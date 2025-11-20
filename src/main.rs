#![allow(bad_style, mismatched_lifetime_syntaxes)]

use core::fmt;
use std::{cell::{Cell, RefCell}, collections::{HashMap, VecDeque}, fmt::Formatter, fs::File, io::{BufReader, BufWriter, Read, Seek, SeekFrom, Write}, os::unix::fs::MetadataExt, path::PathBuf, process::exit};
use bincode::{Decode, Encode, config};
use clap::{Parser, Subcommand};
use itertools::Itertools;

static BincodeConfig: config::Configuration<config::LittleEndian, config::Fixint> = bincode::config::standard().with_little_endian().with_fixed_int_encoding();

#[derive(Encode, Decode)]
struct FATBootSector
{
    _pad0 : [u8;3],
    OEMName : [u8;8],
    BytsPerSec : u16,
    SecPerClus : u8,
    RsvdSecCnt : u16,
    NumFATs : u8,
    _pad1 : [u8; 2],
    TotSec16 : u16,
    _pad2 : [u8; 1],
    FATSz16 : u16,
    _pad3 : [u8; 8],
    TotSec32 : u32,

    // FAT32 fields
    FATSz32 : u32,
    _pad4 : [u8;4],
    RootClus : u32,
    FSInfo : u16,
    _pad5 : [u8;16],
    BootSig : u8,
    _pad6 : [u8; 443],
    Sign : u16
    // size 512 bytes
}

const FATBootSectorSize : u64 = 512;

#[derive(Encode, Decode)]
struct FATFileSystemInfo
{
    LeadSig : u32,
    _pad0 : [u8;256],
    _pad1 : [u8;224],
    StrucSig : u32,
    Free_Count : u32,
    Nxt_Free : u32,
    _pad2 : [u8;12],
    TrailSig : u32
    // size 512 bytes
}

const FATFileSystemInfoSize : u64 = 512;

enum FATFileAttribute
{
    //ReadOnly = 0x1,
    //Hidden = 0x2,
    //System = 0x4,
    //VolumeID = 0x8,
    Directory = 0x10,
    //Archive = 0x20,
    LongName = 0x0f
}

#[derive(Encode, Decode)]
struct FATDirEntry
{
    Name : [u8;11],
    Attr : u8,
    _pad0 : [u8;8],
    FstClusHI : u16,
    _pad1 : [u8;4],
    FstClusLO : u16,
    FileSize : u32
}

const FATDirEntrySize : u64 = 32;

impl FATDirEntry
{
    fn GetClusterNumber(&self) -> u32
    {
        return ((self.FstClusHI as u32) << 16) | self.FstClusLO as u32;
    }

    fn SetClusterNumber(&mut self, Cluster : u32)
    {
        self.FstClusHI = ((Cluster & 0xFFFF0000) >> 16) as u16;
        self.FstClusLO = (Cluster & 0x0000FFFF) as u16;
    }

    fn IsDir(&self) -> bool
    {
        let DirBit = FATFileAttribute::Directory as u8;
        return self.Attr & DirBit == DirBit;
    }

    fn IsLFN(&self) -> bool
    {
        let LFNBit = FATFileAttribute::LongName as u8;
        return self.Attr & LFNBit == LFNBit;
    }

    fn IsUnused(&self) -> bool
    {
        let FirstNameByte = self.Name[0];
        return FirstNameByte == 0x0 || FirstNameByte == 0xe5;
    }

    fn IsLast(&self) -> bool
    {
        let FirstNameByte = self.Name[0];
        return FirstNameByte == 0x0;
    }

    fn IsDot(&self) -> bool
    {
        return self.Name == ".          ".as_bytes();
    }

    fn IsDotDot(&self) -> bool
    {
        return self.Name == "..         ".as_bytes();
    }
}

struct FATDirIterator<'a>
{
    FFS : &'a FATFileSystem<'a>,
    ClusterChain : Vec<u32>,
    EntryIndex : u64,
    EndReached : bool
}

impl<'a> Iterator for FATDirIterator<'a>
{
    type Item = (FileSegment<'a, FATDirEntry>, (u32, u64));

    fn next(&mut self) -> Option<Self::Item>
    {
        if self.EndReached {return None;}

        loop
        {
            let ClusterIndex = (self.EntryIndex / self.FFS.DirEntriesPerCluster) as usize;
            let ClusterPostiion = self.FFS.GetClusterStartByte(self.ClusterChain[ClusterIndex]);
            let EntryOffset = (self.EntryIndex % self.FFS.DirEntriesPerCluster) * FATDirEntrySize;

            let NewFileSegment = FileSegment::<FATDirEntry>::new(ClusterPostiion + EntryOffset, FATDirEntrySize, self.FFS.OpenedFile);
            if NewFileSegment.Data.IsLast()
            {
                self.EndReached = true;
                return None;
            }

            self.EntryIndex += 1;

            if !NewFileSegment.Data.IsUnused()
            && !NewFileSegment.Data.IsLFN()
            {
                return Some((NewFileSegment, (self.ClusterChain[0], self.EntryIndex - 1)));
            }
        }
    }
}

struct FATDirIteratorRecursive<'a>
{
    FFS : &'a FATFileSystem<'a>,
    DirQueue : VecDeque<u32>,
    CurrentIterator : FATDirIterator<'a>
}

impl<'a> Iterator for FATDirIteratorRecursive<'a>
{
    type Item = Result<(FileSegment<'a, FATDirEntry>, (u32, u64)), FATInvalidAccessError>;

    fn next(&mut self) -> Option<Self::Item>
    {
        if self.DirQueue.is_empty() && self.CurrentIterator.EndReached {return None;}

        loop
        {
            match self.CurrentIterator.next()
            {
                Some((v,i)) =>
                {
                    if v.Data.IsDir() && !v.Data.IsDot() && !v.Data.IsDotDot()
                    {
                        self.DirQueue.push_back(v.Data.GetClusterNumber());
                    }

                    return Some(Ok((v,i)));
                },
                None =>
                {
                    match self.DirQueue.pop_front()
                    {
                        Some(v) => self.CurrentIterator = match self.FFS.GetDirIterator(v)
                            {
                                Ok(v) => v,
                                Err(e) =>
                                {
                                    self.DirQueue.clear();
                                    return Some(Err(e))
                                }
                            },
                        None => return None
                    }
                }
            }
        }
    }
}

#[derive(Debug)]
enum FATInvalidAccessError
{
    InvalidFATEntry,
    InvalidDirectoryEntryIndex
}

impl fmt::Display for FATInvalidAccessError
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result
    {
        return write!(f, "Attempted to access a FAT entry larger than the maximum");
    }
}

struct FATBuffer<'a>
{
    FFS : &'a FATFileSystem<'a>,
    BufferedFATEntry : Cell<u32>,
    FATSegment : RefCell<FileSegment::<'a, [u32;FATBufferSize]>>
}

impl<'a> FATBuffer<'a>
{
    fn GetFATEntry(&self, FATEntry : u32) -> Result<u32, FATInvalidAccessError>
    {
        return match self.EnsureFATEntryIsBuffered(FATEntry)
        {
            Ok(_) => Ok(self.FATSegment.borrow().Data[(FATEntry - self.BufferedFATEntry.get()) as usize] & 0x0FFFFFFF),
            Err(e) => Err(e)
        }
    }

    fn SetFATEntry(&mut self, FATEntry : u32, Value : u32) -> Result<(), FATInvalidAccessError>
    {
        match self.EnsureFATEntryIsBuffered(FATEntry)
        {
            Ok(_) =>
            {
                let Index = (FATEntry - self.BufferedFATEntry.get()) as usize;
                self.FATSegment.borrow_mut().Data[Index] &= 0xF0000000;
                self.FATSegment.borrow_mut().Data[Index] |= Value & 0x0FFFFFFF;

                return Ok(());
            }
            Err(e) => return Err(e)
        }
    }

    fn EnsureFATEntryIsBuffered(&self, FATEntry : u32) -> Result<(), FATInvalidAccessError>
    {
        if !self.FFS.IsValidCluster(FATEntry)
        {
            return Err(FATInvalidAccessError::InvalidFATEntry);
        }

        if FATEntry >= self.BufferedFATEntry.get() && FATEntry - self.BufferedFATEntry.get() < FATBufferSize as u32
        {
            return Ok(());
        }

        self.BufferedFATEntry.set( FATEntry - (FATEntry % FATBufferSize as u32));
        self.FATSegment.borrow_mut().WriteBack();
        *self.FATSegment.borrow_mut() = FileSegment::<[u32;FATBufferSize]>::new(self.FFS.FATStartByte + self.BufferedFATEntry.get() as u64*4, FATBufferSize as u64 * 4, self.FFS.OpenedFile);

        return Ok(());
    }
}

struct FATIterator<'a>
{
    FB : FATBuffer<'a>,
    CurrentEntry : u32,
    EndReached : bool
}

impl<'a> Iterator for FATIterator<'a>
{
    type Item = Result<u32, FATInvalidAccessError>;

    fn next(&mut self) -> Option<Self::Item>
    {
        if self.EndReached
        {
            return None;
        }

        const InUseEntries : std::ops::RangeInclusive<u32>  = 2u32..=0xFFFFFF6;
        const EndOfChainEntries : std::ops::RangeInclusive<u32>  = 0x0FFFFFF8u32..=0x0FFFFFFF;
        const BadEntries : [u32;3] = [0x0, 0x1, 0x0FFFFFF7];

        let ReturnItem = self.CurrentEntry;

        if EndOfChainEntries.contains(&ReturnItem)
        {
            self.EndReached = true;
            return None;
        }
        else if BadEntries.contains(&ReturnItem) || !InUseEntries.contains(&ReturnItem)
        {
            return Some(Err(FATInvalidAccessError::InvalidFATEntry));
        }

        match self.FB.GetFATEntry(self.CurrentEntry)
        {
            Ok(v) =>
            {
                self.CurrentEntry = v;
                return Some(Ok(ReturnItem));
            }
            Err(e) =>
            {
                self.EndReached = true;
                return Some(Err(e))
            }
        }
    }
}

struct FileSegment<'a, DataType> where DataType: Encode + Decode<()>
{
    OpenedFile : &'a File,

    Data : DataType,
    DataBuffer : Vec<u8>,
    Position : u64
}

impl<'a, DataType: Encode + Decode<()>> FileSegment<'a, DataType>
{
    fn new(Position : u64, Size : u64, OpenedFile : &'a File) -> Self
    {
        let mut DataBuffer = Vec::new();
        DataBuffer.resize(Size as usize, 0);

        let mut R = BufReader::new(OpenedFile);
        R.seek(SeekFrom::Start(Position)).unwrap();
        R.read_exact(&mut DataBuffer).unwrap();

        let Data : DataType = bincode::decode_from_slice(&DataBuffer, BincodeConfig).unwrap().0;

        return FileSegment { OpenedFile, Data, DataBuffer, Position }
    }

    fn WriteBack(&mut self)
    {
        let OriginalDataBuffer = self.DataBuffer.clone();

        bincode::encode_into_slice(&self.Data, &mut self.DataBuffer, BincodeConfig).unwrap();

        if OriginalDataBuffer != self.DataBuffer
        {
            let mut W = BufWriter::new(self.OpenedFile);
            W.seek(SeekFrom::Start(self.Position)).unwrap();
            W.write_all(&self.DataBuffer).unwrap();
        }
    }
}

#[derive(Debug)]
enum FATCreateError
{
    TooSmallToLoadBS,
    TooSmallAccordingToTotSec32,
    InvalidBSSignature,
    InvalidFSISignature,
    NotFAT32,
    NotEnoughClusters
}

impl fmt::Display for FATCreateError
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result
    {
        match *self
        {
            Self::TooSmallToLoadBS => write!(f, "File too small to contain valid boot sector."),
            Self::TooSmallAccordingToTotSec32 => write!(f, "File is too small for the amount of sectors it reports."),
            Self::InvalidBSSignature => write!(f, "Invalid boot sector signature on file system."),
            Self::InvalidFSISignature => write!(f, "Invalid FileSystemInfo signature on file system."),
            Self::NotFAT32 => write!(f, "File system is probably FAT16 or FAT12, but not FAT32."),
            Self::NotEnoughClusters => write!(f, "File system has less than 65526 clusters. Too few for valid FAT32.")
        }
    }
}

struct FATFileSystem<'a>
{
    OpenedFile : &'a File,
    BS : FileSegment<'a, FATBootSector>,
    FSI : FileSegment<'a, FATFileSystemInfo>,

    FATStartByte : u64,
    DataStartByte : u64,

    BytesPerCluster : u64,
    FATEntryCount : u32,
    BiggestFreeCluster : Cell<u32>,

    DirEntriesPerCluster : u64
}

const FATBufferSize : usize = 128;


impl<'a> FATFileSystem<'a>
{
    fn new(OpenedFile : &'a File) -> Result<Self, FATCreateError>
    {
        if OpenedFile.metadata().unwrap().size() < FATBootSectorSize
        {
            return Err(FATCreateError::TooSmallToLoadBS);
        }

        let BS: FileSegment<'_, FATBootSector> = FileSegment::<FATBootSector>::new(0, FATBootSectorSize, &OpenedFile);

        if BS.Data.FATSz16 != 0 || BS.Data.TotSec16 != 0
        {
            return Err(FATCreateError::NotFAT32);
        }

        let BytesPerCluster = (BS.Data.SecPerClus as u16 * BS.Data.BytsPerSec) as u64;
        let FATStartByte = (BS.Data.RsvdSecCnt * BS.Data.BytsPerSec) as u64;
        let DataStartByte = FATStartByte + BS.Data.NumFATs as u64 * BS.Data.FATSz32 as u64 * BS.Data.BytsPerSec as u64;
        let FATEntryCount = (((BS.Data.TotSec32 as u64 * BS.Data.BytsPerSec as u64) - DataStartByte) / BytesPerCluster) as u32;

        if FATEntryCount < 65526
        {
            return Err(FATCreateError::NotEnoughClusters);
        }

        if !(BS.Data.BootSig == 0x29 && BS.Data.Sign == 0xaa55)
        {
            return Err(FATCreateError::InvalidBSSignature);
        }

        if OpenedFile.metadata().unwrap().size() < (BS.Data.TotSec32 as u64 * BS.Data.BytsPerSec as u64)
        {
            return Err(FATCreateError::TooSmallAccordingToTotSec32);
        }

        let FSIAddress = (BS.Data.FSInfo * BS.Data.BytsPerSec) as u64;
        let FSI = FileSegment::<FATFileSystemInfo>::new(FSIAddress, FATFileSystemInfoSize, &OpenedFile);

        if !(FSI.Data.LeadSig == 0x41615252 && FSI.Data.StrucSig == 0x61417272 && FSI.Data.TrailSig == 0xaa550000)
        {
            return Err(FATCreateError::InvalidFSISignature);
        }

        let BiggestFreeCluster = Cell::new(FATEntryCount + 2 - 1);
        let DirEntriesPerCluster = BytesPerCluster / FATDirEntrySize;

        return Ok(FATFileSystem
        {
            OpenedFile,
            BS,
            FSI,
            FATStartByte,
            DataStartByte,
            BytesPerCluster,
            FATEntryCount,
            BiggestFreeCluster,
            DirEntriesPerCluster,
        });
    }

    fn IsValidCluster(&self, Cluster : u32) -> bool
    {
        return Cluster <= self.FATEntryCount + 2 && Cluster >= 2;
    }

    fn GetClusterStartByte(&self, Cluster : u32) -> u64
    {
        return self.DataStartByte + (Cluster as u64 - 2) * self.BytesPerCluster;
    }

    fn GetFatBuffer(&self) -> FATBuffer
    {
        return FATBuffer { FFS : self, BufferedFATEntry: Cell::new(self.BS.Data.RootClus), FATSegment: RefCell::new(FileSegment::<[u32;FATBufferSize]>::new(self.FATStartByte + 2*4, FATBufferSize as u64 * 4, self.OpenedFile)) }
    }

    fn GetFatIterator(&self, StartEntry : u32) -> FATIterator
    {
        return FATIterator { FB: self.GetFatBuffer(), CurrentEntry: StartEntry, EndReached : false };
    }

    fn GetDirEntry(&self, Cluster : u32, EntryIndex : u64) -> Result<FileSegment<FATDirEntry>, FATInvalidAccessError>
    {
        //This is basically the same as the iterator code, except that we don't cache the fat chain
        let ClusterIndex = (EntryIndex / self.DirEntriesPerCluster) as usize;
        let ClusterPostiion = match self.GetFatIterator(Cluster).nth(ClusterIndex)
        {
            Some(Ok(v)) => self.GetClusterStartByte(v),
            Some(Err(e)) => return Err(e),
            None => return Err(FATInvalidAccessError::InvalidDirectoryEntryIndex)
        };

        let EntryOffset = (EntryIndex % self.DirEntriesPerCluster) * FATDirEntrySize;

        return Ok(FileSegment::<FATDirEntry>::new(ClusterPostiion + EntryOffset, FATDirEntrySize, self.OpenedFile));
    }

    fn GetDirIterator(&self, StartCluster : u32) -> Result<FATDirIterator, FATInvalidAccessError>
    {
        match self.GetFatIterator(StartCluster).collect()
        {
            Ok(v) => Ok(FATDirIterator { FFS : self, ClusterChain: v, EntryIndex: 0, EndReached : false}),
            Err(e) => Err(e)
        }
    }

    fn GetRecursiveDirIterator(&self, Cluster : u32) -> Result<FATDirIteratorRecursive, FATInvalidAccessError>
    {
        match self.GetDirIterator(Cluster)
        {
            Ok(v) => Ok(FATDirIteratorRecursive { FFS: self, DirQueue : VecDeque::<u32>::new(), CurrentIterator : v }),
            Err(e) => Err(e)
        }
    }

    fn FindParentDirAndEntryIndex(&self, Cluster : u32) -> Result<Option<(u32,u64)>, FATInvalidAccessError>
    {
        let DirIteratorRecursive = self.GetRecursiveDirIterator(self.BS.Data.RootClus)?;

        let FoundIndices = DirIteratorRecursive
            .filter_ok(|(v,_)| v.Data.GetClusterNumber() == Cluster && !v.Data.IsDot() && !v.Data.IsDotDot())
            .map_ok(|(_,i)| i)
            .collect::<Result<Vec<(u32,u64)>, FATInvalidAccessError>>()?;

        if FoundIndices.len() == 1
        {
            return Ok(Some(FoundIndices[0]));
        }
        else if FoundIndices.len() > 1
        {
            eprintln!("File with cluster {} is listed more than once.", Cluster)
        }

        return Ok(None);
    }

    fn MoveFileToEnd(&mut self, ParentDir : u32, EntryIndex : u64) -> Result<Option<u32>, FATInvalidAccessError>
    {
        let mut MovedFile = self.GetDirEntry(ParentDir, EntryIndex)?;
        let mut FB = self.GetFatBuffer();

        //Figure out the new cluster chain to move the file to
        let CurrentClusterChain = self.GetFatIterator(MovedFile.Data.GetClusterNumber()).collect::<Result<Vec<u32>, FATInvalidAccessError>>()?;

        let FreeClusters : Vec<u32> =
        (2u32..=self.BiggestFreeCluster.get()).rev()
            .filter(|a| FB.GetFATEntry(*a).unwrap() == 0)
            .take(CurrentClusterChain.len())
            .collect();

        if FreeClusters.len() == 0
        {
            return Ok(None);
        }

        //Pick the highest clusters from either set, and put them into one chain
        let mut PickedClusters : Vec<u32> = CurrentClusterChain.iter().chain(FreeClusters.iter()).map(|a| *a).collect();
        PickedClusters.sort();
        PickedClusters = PickedClusters.iter().rev().take(CurrentClusterChain.iter().len()).rev().map(|a| *a).collect();

        let mut NewClusters = PickedClusters.iter().filter(|a| !CurrentClusterChain.contains(a)).map(|a| *a);

        let NewClusterChain : Vec<u32> = (0..CurrentClusterChain.len())
            .map(|i| if PickedClusters.contains(&CurrentClusterChain[i]) {CurrentClusterChain[i]} else {NewClusters.next().unwrap()})
            .collect();

        self.BiggestFreeCluster.set(*NewClusterChain.iter().min().unwrap());

        if NewClusterChain == CurrentClusterChain
        {
            return Ok(None);
        }

        // Copy Data
        let mut DataBuffer = Vec::<u8>::new();
        DataBuffer.resize(self.BytesPerCluster as usize, 0);
        let mut R = BufReader::new(self.OpenedFile);
        let mut W = BufWriter::new(self.OpenedFile);

        (0..CurrentClusterChain.len()).for_each(
            |i|
            {
                if CurrentClusterChain[i] == NewClusterChain[i] {return;}

                R.seek(SeekFrom::Start(self.GetClusterStartByte(CurrentClusterChain[i]))).unwrap();
                R.read(&mut DataBuffer).unwrap();

                W.seek(SeekFrom::Start(self.GetClusterStartByte(NewClusterChain[i]))).unwrap();
                W.write(&DataBuffer).unwrap();
            });

        // Write to FAT
        CurrentClusterChain.iter().for_each(|a|FB.SetFATEntry(*a, 0).unwrap());
        NewClusterChain.iter()
            .zip(NewClusterChain.iter()
                .rev()
                .take(NewClusterChain.len() - 1)
                .rev()
                .chain([0x0FFFFFFF].iter()))
            .for_each(|(This,Next)| FB.SetFATEntry(*This, *Next).unwrap());

        FB.FATSegment.borrow_mut().WriteBack();

        // Set clusters in dir entry right
        let NewCluster = NewClusterChain[0];
        MovedFile.Data.SetClusterNumber(NewCluster);
        MovedFile.WriteBack();

        if MovedFile.Data.IsDir()
        {
            // Set . entry right
            self.GetDirIterator(NewCluster).unwrap().filter(|(a, _)| a.Data.IsDir() && a.Data.IsDot()).for_each(
                |(mut a, _)|
                {
                    a.Data.SetClusterNumber(NewCluster);
                    a.WriteBack();
                });

            // Set .. entries right
            self.GetDirIterator(NewCluster).unwrap().filter(|(a, _)| a.Data.IsDir() && !a.Data.IsDot() && !a.Data.IsDotDot()).for_each(
                |(a, _)|
                {
                    self.GetDirIterator(a.Data.GetClusterNumber()).unwrap().filter(|(a, _)| a.Data.IsDir() && a.Data.IsDotDot()).for_each(
                        |(mut a, _)|
                        {
                            a.Data.SetClusterNumber(NewCluster);
                            a.WriteBack();
                        });
                }
            );
        }

        return Ok(Some(NewCluster))
    }

    fn MoveAllFilesToEnd(&mut self) -> Result<(), FATInvalidAccessError>
    {
        let mut MoveJobs : Vec<(u32, u32, u64)> = self.GetRecursiveDirIterator(self.BS.Data.RootClus).unwrap()
            .filter_ok(|(v, _)| v.Data.GetClusterNumber() != 0 && !v.Data.IsDot() && !v.Data.IsDotDot())
            .map_ok(|(v,(Cluster,EntryIndex))| (v.Data.GetClusterNumber(), Cluster, EntryIndex))
            .collect::<Result<Vec<(u32, u32, u64)>, FATInvalidAccessError>>()?;

        MoveJobs.sort_by_key(|(FileCluster,_,_)| *FileCluster);

        let mut ClusterRedirects = HashMap::<u32, u32>::new();

        MoveJobs.iter().map(
            |(MovedCluster, ParentDir, EntryIndex)| -> Result<(), FATInvalidAccessError>
            {
                let RealParentDir = match ClusterRedirects.get(ParentDir)
                {
                    Some(v) => v,
                    None => ParentDir
                };

                match self.MoveFileToEnd(*RealParentDir, *EntryIndex)
                {
                    Ok(Some(v)) => _ = ClusterRedirects.insert(*MovedCluster, v),
                    Ok(None) => (),
                    Err(e) => return Err(e)
                }

                return Ok(());
            }).collect::<Result<(), FATInvalidAccessError>>()?;

        return Ok(());
    }

}

fn PrintDirEntry(DirEntry : &FileSegment<FATDirEntry>)
{
    let D = &DirEntry.Data;
    println!("{}{:10} {} {}", if D.IsDir() {'D'} else {' '}, D.GetClusterNumber(), str::from_utf8(&D.Name).unwrap(), D.FileSize);
}


#[derive(Debug, Parser)]
#[clap(name = "fatplow", version = "1.0")]
struct fatplowApp
{
    #[clap(subcommand)]
    Command : Command,

    FileName : PathBuf
}

#[derive(Debug, Subcommand)]
enum Command
{
    ///Move the contents of files to the end of the data storage.
    MoveClustersToEnd
    {
        ///Only move the specified file.
        #[clap(long, short = 'f', default_value_t = 0)]
        FileCluster : u32
    },
    ///Print the Nxt_Free hint. It helps find free clusters faster.
    PrintNextFreeCluster,
    ///Set the Nxt_Free hint.
    SetNextFreeCluster
    {
        ///New value for Nxt_Free
        NextFreeCluster : u32
    },
    ///Displays cluster usage. 'O' is a used cluster, '.' a free one.
    PrintClusterUse
    {
        ///Condense multiple clusters into one for display.
        #[clap(long, short = 's', default_value_t = 1)]
        PrintScale : usize,

        ///Show cluster use numerically as a table.
        #[clap(long, short = 'c', default_value_t = false)]
        CompactPrint : bool
    },
    ///Print files in a directory, with its cluster number and size.
    PrintDir
    {
        ///Cluster of directory to print.
        DirCluster : u32,

        ///Print contents of all subdirectories too.
        #[clap(long, short = 'r', default_value_t = false)]
        Recursive : bool
    },
    ///Print the cluster chain used to store a particular file.
    PrintFileClusters
    {
        ///First cluster of the chain to print.
        StartCluster : u32
    }
}

fn GracefulExit(Message: String) -> !
{
    eprintln!("{}", Message);
    exit(1);
}

fn main()
{
    let Args = fatplowApp::parse();

    let OpenedFile = match File::options().read(true).write(true).open(Args.FileName)
    {
        Ok(v) => v,
        Err(e) => GracefulExit(format!("Could not open file system: {}", e))
    };

    let mut FFS = match FATFileSystem::new(&OpenedFile)
    {
        Ok(v) => v,
        Err(e) => GracefulExit(format!("Failed to open file as FAT32: {}", e))
    };

    match Args.Command
    {
        Command::MoveClustersToEnd {FileCluster} =>
        {
            if FileCluster < 2
            {
                match FFS.MoveAllFilesToEnd()
                {
                    Ok(()) => (),
                    Err(e) => GracefulExit(format!("Error while moving clusters: {}", e))
                }
            }
            else
            {
                match FFS.FindParentDirAndEntryIndex(FileCluster)
                {
                    Ok(Some((dir,i))) => match FFS.MoveFileToEnd(dir, i)
                    {
                        Ok(_) => (),
                        Err(e) => GracefulExit(format!("Error while moving clusters: {}", e))
                    },
                    Ok(None) => eprintln!("File with start cluster {} not found.", FileCluster),
                    Err(e) => GracefulExit(format!("Error while searching for cluster {}. {}", FileCluster, e))
                }
            }
        },
        Command::PrintNextFreeCluster => println!("{}", FFS.FSI.Data.Nxt_Free),
        Command::SetNextFreeCluster { NextFreeCluster } =>
        {
            FFS.FSI.Data.Nxt_Free = NextFreeCluster;
            FFS.FSI.WriteBack();
        }
        Command::PrintClusterUse {PrintScale, CompactPrint} =>
        {
            let BoolToChar = |b: bool| if b {'O'} else {'.'};

            let FB = FFS.GetFatBuffer();
            let ClusterUseMap = (2u32..(FFS.FATEntryCount as u32 + 2))
                .map(|a| FB.GetFATEntry(a).unwrap() != 0);

            if CompactPrint
            {
                ClusterUseMap.chunk_by(|a| *a).into_iter().for_each(|(v, i)| println!("{} {}", BoolToChar(v), i.count()));
            }
            else
            {
                let UsageString = ClusterUseMap
                    .chunks(PrintScale)
                    .into_iter().map(|Chunk| BoolToChar(Chunk.map(|v| if v {1} else {-1}).sum::<i64>() > 0)).collect::<String>();

                println!("{}", UsageString);
            }
        },
        Command::PrintDir {DirCluster, Recursive} =>
        {
            if !FFS.IsValidCluster(DirCluster)
            {
                GracefulExit(format!("Invalid Cluster {}.", DirCluster));
            }

            if DirCluster != FFS.BS.Data.RootClus
            {
                match FFS.FindParentDirAndEntryIndex(DirCluster)
                {
                    Ok(Some((dir, i))) =>
                    {
                        if !FFS.GetDirEntry(dir, i).unwrap().Data.IsDir()
                        {
                            eprintln!("File with cluster {} is not a directory.", DirCluster);
                            return;
                        }
                    },
                    Ok(None) =>
                    {
                        eprintln!("Directory with start cluster {} not found.", DirCluster);
                        return;
                    }
                    Err(e) => GracefulExit(format!("Error while searching for cluster {}: {}", DirCluster, e))
                }
            }

            if Recursive
            {
                let DirIteratorRecursive = match FFS.GetRecursiveDirIterator(DirCluster)
                {
                    Ok(v) => v,
                    Err(e) => GracefulExit(format!("Error while initializing iterator: {}", e))
                };

                match DirIteratorRecursive.filter(
                    |v|
                    {
                        match v
                        {
                            Ok((v,_)) => !v.Data.IsDot() && !v.Data.IsDotDot(),
                            Err(_) => true
                        }
                    })
                    .collect::<Result<Vec<(FileSegment<FATDirEntry>, (u32, u64))>, FATInvalidAccessError>>()
                {
                    Ok(v) => v.iter().for_each(|(v,_)| PrintDirEntry(v)),
                    Err(e) => GracefulExit(format!("Error while iterating directories {}", e))
                }
            }
            else
            {
                match FFS.GetDirIterator(DirCluster)
                {
                    Ok(v) => v.for_each(|(v,_)| PrintDirEntry(&v)),
                    Err(e) => GracefulExit(format!("Error while iterating directories {}", e))
                }
            }
        },
        Command::PrintFileClusters {StartCluster} =>
        {
            match FFS.GetFatIterator(StartCluster).collect::<Result<Vec<u32>, FATInvalidAccessError>>()
            {
                Ok(v) => v.iter().for_each(|a| println!("{}", a)),
                Err(e) => GracefulExit(format!("Error while iterating FAT chain: {}", e))
            }
        }
    }
}
