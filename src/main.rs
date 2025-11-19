#![allow(bad_style, mismatched_lifetime_syntaxes)]

use std::{cell::{Cell, RefCell}, collections::{HashMap, VecDeque}, fs::File, io::{BufReader, BufWriter, Read, Seek, SeekFrom, Write}, path::{PathBuf}};
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
    _pad1 : [u8; 15],
    TotSec32 : u32,

    // FAT32 fields
    FATSz32 : u32,
    _pad2 : [u8;4],
    RootClus : u32,
    FSInfo : u16,
    _pad3 : [u8;16],
    BootSig : u8,
    _pad4 : [u8; 443],
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
    ReadOnly = 0x1,
    Hidden = 0x2,
    System = 0x4,
    VolumeID = 0x8,
    Directory = 0x10,
    Archive = 0x20,
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
    type Item = (FileSegment<'a, FATDirEntry>, (u32, u64));

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

                    return Some((v,i));
                },
                None =>
                {
                    match self.DirQueue.pop_front()
                    {
                        Some(v) => self.CurrentIterator = self.FFS.GetDirIterator(v),
                        None => return None
                    }
                }
            }
        }
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
    fn GetFATEntry(&self, FATEntry : u32) -> u32
    {
        self.EnsureFATEntryIsBuffered(FATEntry);
        return self.FATSegment.borrow().Data[(FATEntry - self.BufferedFATEntry.get()) as usize] & 0x0FFFFFFF;
    }

    fn SetFATEntry(&mut self, FATEntry : u32, Value : u32)
    {
        self.EnsureFATEntryIsBuffered(FATEntry);
        let Index = (FATEntry - self.BufferedFATEntry.get()) as usize;
        self.FATSegment.borrow_mut().Data[Index] &= 0xF0000000;
        self.FATSegment.borrow_mut().Data[Index] |= Value & 0x0FFFFFFF;
    }

    fn EnsureFATEntryIsBuffered(&self, FATEntry : u32)
    {
        if FATEntry >= self.BufferedFATEntry.get() && FATEntry - self.BufferedFATEntry.get() < FATBufferSize as u32
        {
            return;
        }

        self.BufferedFATEntry.set( FATEntry - (FATEntry % FATBufferSize as u32));
        self.FATSegment.borrow_mut().WriteBack();
        *self.FATSegment.borrow_mut() = FileSegment::<[u32;FATBufferSize]>::new(self.FFS.FATStartByte + self.BufferedFATEntry.get() as u64*4, FATBufferSize as u64 * 4, self.FFS.OpenedFile);
    }
}

struct FATIterator<'a>
{
    FB : FATBuffer<'a>,
    StartEntry : u32,
    CurrentEntry : u32,
    EndReached : bool
}

impl<'a> Iterator for FATIterator<'a>
{
    type Item = u32;

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
            eprintln!("While iterating FAT chain {} encountered an invalid entry: {:x?}", self.StartEntry, self.CurrentEntry);
            self.EndReached = true;
            return None;
        }

        self.CurrentEntry = self.FB.GetFATEntry(self.CurrentEntry);
        return Some(ReturnItem);
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

struct FATFileSystem<'a>
{
    OpenedFile : &'a File,
    BS : FileSegment<'a, FATBootSector>,
    FSI : FileSegment<'a, FATFileSystemInfo>,

    FATStartByte : u64,
    DataStartByte : u64,

    BytesPerCluster : u64,
    FATEntryCount : u32,
    BiggestFreeCluster : u32,

    DirEntriesPerCluster : u64
}

const FATBufferSize : usize = 128;

impl<'a> FATFileSystem<'a>
{
    fn new(OpenedFile : &'a File) -> Self
    {
        let BS: FileSegment<'_, FATBootSector> = FileSegment::<FATBootSector>::new(0, FATBootSectorSize, &OpenedFile);
        let FSIAddress = (BS.Data.FSInfo * BS.Data.BytsPerSec) as u64;
        let FSI = FileSegment::<FATFileSystemInfo>::new(FSIAddress, FATFileSystemInfoSize, &OpenedFile);

        let BytesPerCluster = (BS.Data.SecPerClus as u16 * BS.Data.BytsPerSec) as u64;
        let FATStartByte = (BS.Data.RsvdSecCnt * BS.Data.BytsPerSec) as u64;
        let DataStartByte = FATStartByte + BS.Data.NumFATs as u64 * BS.Data.FATSz32 as u64 * BS.Data.BytsPerSec as u64;

        let FATEntryCount = (((BS.Data.TotSec32 as u64 * BS.Data.BytsPerSec as u64) - DataStartByte) / BytesPerCluster) as u32;
        let BiggestFreeCluster = FATEntryCount + 2 - 1;

        let DirEntriesPerCluster = BytesPerCluster / FATDirEntrySize;

        return FATFileSystem
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
        };
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
        return FATIterator { FB: self.GetFatBuffer(), StartEntry, CurrentEntry: StartEntry, EndReached : false };
    }

    fn GetDirEntry(&self, Cluster : u32, EntryIndex : u64) -> FileSegment<FATDirEntry>
    {
        //This is basically the same as the iterator code, except that we don't cache the fat chain
        let ClusterIndex = (EntryIndex / self.DirEntriesPerCluster) as usize;
        let ClusterPostiion = self.GetClusterStartByte(self.GetFatIterator(Cluster).nth(ClusterIndex).unwrap());
        let EntryOffset = (EntryIndex % self.DirEntriesPerCluster) * FATDirEntrySize;

        return FileSegment::<FATDirEntry>::new(ClusterPostiion + EntryOffset, FATDirEntrySize, self.OpenedFile);
    }

    fn GetDirIterator(&self, StartCluster : u32) -> FATDirIterator
    {
        return FATDirIterator { FFS : self, ClusterChain: self.GetFatIterator(StartCluster).collect(), EntryIndex: 0, EndReached : false}
    }

    fn GetRecursiveDirIterator(&self, Cluster : u32) -> FATDirIteratorRecursive
    {
        return FATDirIteratorRecursive { FFS: self, DirQueue : VecDeque::<u32>::new(), CurrentIterator : self.GetDirIterator(Cluster) };
    }

    fn MoveFileToEnd(&mut self, ParentDir : u32, EntryIndex : u64) -> Option<u32>
    {
        // cant modify this while other things are immutably borrowing self,
        // because rust is being shitty about the whole struct being borrowed.
        // This is the least worst way of working around it for now.
        // TODO: wrap it in Cell<>
        let mut BiggestFreeCluster = self.BiggestFreeCluster;
        let Result = (|| -> Option<u32>
        {
            let mut MovedFile = self.GetDirEntry(ParentDir, EntryIndex);

            let mut FB = self.GetFatBuffer();

            //Figure out the new cluster chain to move the file to
            let CurrentClusterChain : Vec<u32> = self.GetFatIterator(MovedFile.Data.GetClusterNumber()).collect();
            let FreeClusters : Vec<u32> =
            (2u32..=self.BiggestFreeCluster).rev()
                .filter(|a| FB.GetFATEntry(*a) == 0)
                .take(CurrentClusterChain.len())
                .collect();

            if FreeClusters.len() == 0
            {
                return None;
            }

            //Pick the highest clusters from either set, and put them into one chain
            let mut PickedClusters : Vec<u32> = CurrentClusterChain.iter().chain(FreeClusters.iter()).map(|a| *a).collect();
            PickedClusters.sort();
            PickedClusters = PickedClusters.iter().rev().take(CurrentClusterChain.iter().len()).rev().map(|a| *a).collect();

            let mut NewClusters = PickedClusters.iter().filter(|a| !CurrentClusterChain.contains(a)).map(|a| *a);

            let NewClusterChain : Vec<u32> = (0..CurrentClusterChain.len())
                .map(|i|
                    {
                        if PickedClusters.contains(&CurrentClusterChain[i])
                        {
                            return CurrentClusterChain[i];
                        }
                        else
                        {
                            return NewClusters.next().unwrap();
                        }
                    })
                .collect();

            BiggestFreeCluster = *NewClusterChain.iter().min().unwrap();

            if NewClusterChain == CurrentClusterChain
            {
                return None;
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

                    R.seek(SeekFrom::Start(self.GetClusterStartByte(CurrentClusterChain[i])));
                    R.read(&mut DataBuffer);

                    W.seek(SeekFrom::Start(self.GetClusterStartByte(NewClusterChain[i])));
                    W.write(&DataBuffer);
                });

            // Write to FAT
            CurrentClusterChain.iter().for_each(|a|FB.SetFATEntry(*a, 0));
            NewClusterChain.iter().zip(NewClusterChain.iter().rev().take(NewClusterChain.len() - 1).rev().chain([0x0FFFFFFF].iter())).for_each(|(This,Next)| FB.SetFATEntry(*This, *Next));
            FB.FATSegment.borrow_mut().WriteBack();

            // Set clusters in dir entry right
            let NewCluster = NewClusterChain[0];
            MovedFile.Data.SetClusterNumber(NewCluster);
            MovedFile.WriteBack();

            if MovedFile.Data.IsDir()
            {
                // Set . entry right
                self.GetDirIterator(NewCluster).filter(|(a, _)| a.Data.IsDir() && a.Data.IsDot()).for_each(
                    |(mut a, _)|
                    {
                        a.Data.SetClusterNumber(NewCluster);
                        a.WriteBack();
                    });

                // Set .. entries right
                self.GetDirIterator(NewCluster).filter(|(a, _)| a.Data.IsDir() && !a.Data.IsDot() && !a.Data.IsDotDot()).for_each(
                    |(a, _)|
                    {
                        self.GetDirIterator(a.Data.GetClusterNumber()).filter(|(a, _)| a.Data.IsDir() && a.Data.IsDotDot()).for_each(
                            |(mut a, _)|
                            {
                                a.Data.SetClusterNumber(NewCluster);
                                a.WriteBack();
                            });
                    }
                );
            }

            return Some(NewCluster)
        })();

        self.BiggestFreeCluster = BiggestFreeCluster;
        return Result
    }

    fn MoveAllFilesToEnd(&mut self)
    {
        let mut MoveJobs : Vec<(u32, u32, u64)> = self.GetRecursiveDirIterator(self.BS.Data.RootClus)
            .filter(|(v, _)| v.Data.GetClusterNumber() != 0 && !v.Data.IsDot() && !v.Data.IsDotDot())
            .map(|(v,(Cluster,EntryIndex))| (v.Data.GetClusterNumber(), Cluster, EntryIndex))
            .collect();

        MoveJobs.sort_by_key(|(FileCluster,_,_)| *FileCluster);
        MoveJobs.iter().for_each(|a| println!("{:?}", a));

        let mut ClusterRedirects = HashMap::<u32, u32>::new();

        MoveJobs.iter().for_each(
            |(MovedCluster, ParentDir, EntryIndex)|
            {
                let RealParentDir = match ClusterRedirects.get(ParentDir)
                {
                    Some(v) => v,
                    None => ParentDir
                };

                match self.MoveFileToEnd(*RealParentDir, *EntryIndex)
                {
                    Some(v) => _ = ClusterRedirects.insert(*MovedCluster, v),
                    None => ()
                }
            });
    }

}

fn PrintDirEntry(DirEntry : FileSegment<FATDirEntry>)
{
    let D = &DirEntry.Data;
    println!("{:10} {} {}", D.GetClusterNumber(), str::from_utf8(&D.Name).unwrap(), D.FileSize);
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
    MoveAllClustersToEnd,
    MoveFileClustersToEnd
    {
        Cluster : u32
    },
    PrintClusterUse
    {
        PrintScale : usize
    },
    PrintDir
    {
        Cluster : u32
    },
    PrintAllFiles,
    PrintFileClusters
    {
        Cluster : u32
    },
    PrintFilesizeSum
}

fn main()
{
    let Args = fatplowApp::parse();

    let OpenedFile = File::options().read(true).write(true).open(Args.FileName).unwrap();
    let mut FFS = FATFileSystem::new(&OpenedFile);


    match Args.Command
    {
        Command::MoveAllClustersToEnd => FFS.MoveAllFilesToEnd(),
        Command::MoveFileClustersToEnd {Cluster} =>
        {
            let FoundFiles : Vec<(u32,u64)> = FFS.GetRecursiveDirIterator(FFS.BS.Data.RootClus)
                .filter(|(v,i)| v.Data.GetClusterNumber() == Cluster)
                .map(|(_,i)| i)
                .collect();

            if FoundFiles.is_empty()
            {
                eprintln!("File with start cluster {} not found.", Cluster);
                return;
            }

            FoundFiles.iter().for_each(|(dir,i)| _ = FFS.MoveFileToEnd(*dir, *i));
        },
        Command::PrintClusterUse {PrintScale} =>
        {
            let FB = FFS.GetFatBuffer();
            let UsageString = (2u32..(FFS.FATEntryCount as u32 + 2))
                .map(|a| FB.GetFATEntry(a) != 0)
                .chunks(PrintScale)
                .into_iter().map(|Chunk| if Chunk.map(|v| if v {1} else {-1}).sum::<i64>() > 0 {'O'} else {'.'}).collect::<String>();

            print!("{}", UsageString);
        },
        Command::PrintDir {Cluster} => FFS.GetDirIterator(Cluster).for_each(|(v,_)| PrintDirEntry(v)),
        Command::PrintAllFiles => FFS.GetRecursiveDirIterator(FFS.BS.Data.RootClus)
            .filter(|(v,_)| !v.Data.IsDot() && !v.Data.IsDotDot())
            .for_each(|(v,_)| PrintDirEntry(v)),
        Command::PrintFileClusters {Cluster} => FFS.GetFatIterator(Cluster).for_each(|a| println!("{}", a)),
        Command::PrintFilesizeSum =>
        {
            let Sum : u64 = FFS.GetRecursiveDirIterator(FFS.BS.Data.RootClus)
                .filter(|(v,_)| !v.Data.IsDir())
                .map(|(v,_)|v.Data.FileSize as u64)
                .sum();

            println!("{}", Sum);
        }
    }
}
