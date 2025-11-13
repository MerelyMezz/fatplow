// Using https://elm-chan.org/docs/fat_e.html as reference

#include <algorithm>
#include <functional>
#include <iostream>
#include <cstdint>
#include <fstream>
#include <queue>
#include <vector>
#include <iomanip>
#include <cmath>

uint64_t GetSectorStartByte(int32_t Sector);
uint64_t GetDataStartSector(int32_t ClusterNumber);
int32_t GetNthCluster(int32_t Start, int32_t n);
std::vector<int32_t> GetClusterChain(int32_t StartCluster);
uint32_t MoveFileToEnd(uint32_t ParentDirCluster, uint32_t DirEntryIndex, uint32_t FileCluster);

struct BootSector
{
    int8_t _pad0[3];
    char OEMName[8];
    int16_t BytesPerSector;         //should be 512
    int8_t SectorsPerCluster;       //Should be power of 2
    int16_t ReservedSectorCount;
    int8_t NumberOfFATs;            //Should be 2
    int8_t _pad1[15];
    int32_t TotalSectors;

    //The following fields are only valid for FAT32,
    //so before using them, we have to verify
    //that we aren't using anything else
    int32_t FATSectorCount;
    int16_t ActiveFATFlags;
    int8_t _pad2[2];
    int32_t RootDirCluster;
    int16_t FileSystemInfoSector;
    int16_t BackupBootSector;
    int8_t _pad3[14];
    int8_t BootSignature;           //Should be 0x29
    int32_t VolumeID;
    char VolumeLabel[11];
    int8_t _pad4[430];
} __attribute__((packed));

struct FSInfo
{
    int8_t _pad0[488];
    int32_t FreeClusterCount;
    int32_t NextFreeCluster;
    int8_t _pad1[16];
} __attribute__((packed));

struct LFNEntry
{
    int8_t OrderByte;
    char NamePart1[10];
    int8_t DirectoryAttributes;
    int8_t _pad0[2];
    char NamePart2[12];
    int8_t _pad1[2];
    char NamePart3[4];
} __attribute__((packed));

enum DirAttribute
{
    DA_ReadOnly = 0x1,
    DA_Hidden = 0x2,
    DA_System = 0x4,
    DA_VolumeID = 0x8,
    DA_Directory = 0x10,
    DA_Archive = 0x20,
    DA_LongFileName = 0xF
};

std::string Dot = ".          ";
std::string DotDot = "..         ";

struct DirectoryEntry
{
    char ShortFileName[11];
    int8_t DirectoryAttributes;
    int8_t _pad0[8];
    uint16_t ClusterNumberHigh;
    int8_t _pad1[4];
    uint16_t ClusterNumberLow;
    int32_t FileSize;

    int32_t GetClusterNumber()
    {
        return ((int32_t)ClusterNumberHigh) << 16 | ClusterNumberLow;
    }

    void SetClusterNumber(int32_t Cluster)
    {
        ClusterNumberHigh = (Cluster & 0xFFFF0000) >> 16;
        ClusterNumberLow = (Cluster & 0x0000FFFF);
    }

    bool IsDirectory()
    {
        return DirectoryAttributes & DA_Directory;
    }

    bool IsLFN()
    {
        return DirectoryAttributes & DA_LongFileName;
    }

    bool IsUnusedEntry()
    {
        uint8_t FirstNameByte = ShortFileName[0];
        return FirstNameByte == 0x0 || FirstNameByte == 0xe5;
    }

    bool IsLastEntry()
    {
        uint8_t FirstNameByte = ShortFileName[0];
        return FirstNameByte == 0x0;
    }

    bool IsDotOrDoubleDotDir()
    {
        std::string SFN = std::string(ShortFileName, sizeof(ShortFileName));

        return SFN == Dot
            || SFN == DotDot;
    }

} __attribute__((packed));

std::fstream FatFilesystem;
BootSector BS;
FSInfo FSI;

int32_t FATStartSector;
int32_t FATEntryCount;
int32_t BiggestFreeCluster;

int32_t DataStartSector;

int32_t BytesPerCluster;

struct FatEditor
{
    std::vector<int32_t> FatEntries;
    uint32_t CurrentLoadedSector;
    bool Dirty;

    void SaveAllChanges()
    {
        if (CurrentLoadedSector != -1 && Dirty)
        {
            FatFilesystem.seekp(GetSectorStartByte(CurrentLoadedSector));
            FatFilesystem.write((char*)FatEntries.data(), BS.BytesPerSector);
            Dirty = false;
        }
    }

    void EnsureSectorLoaded(int32_t FATNumber)
    {
        int32_t FatSector = FATStartSector + ((FATNumber * 4) / BS.BytesPerSector);

        if (CurrentLoadedSector != FatSector)
        {
            SaveAllChanges();

            // Load new sector up
            FatFilesystem.seekg(GetSectorStartByte(FatSector));
            FatFilesystem.read((char*)FatEntries.data(), BS.BytesPerSector);
            CurrentLoadedSector = FatSector;
        }
    }

    int32_t GetFatEntryOffsetWithinSector(int32_t FATNumber)
    {
        return FATNumber % (BS.BytesPerSector / 4);
    }


    int32_t GetFatEntry(int32_t FATNumber)
    {
        EnsureSectorLoaded(FATNumber);
        return FatEntries[GetFatEntryOffsetWithinSector(FATNumber)] & 0x0FFFFFFF;
    }

    void SetFatEntry(int32_t FATNumber, int32_t Entry)
    {
        EnsureSectorLoaded(FATNumber);

        int32_t Index = GetFatEntryOffsetWithinSector(FATNumber);
        FatEntries[Index] = (Entry & 0x0FFFFFFF) | (FatEntries[Index] & 0xF0000000);
        Dirty = true;
    }

    FatEditor()
    {
        FatEntries.resize(BS.BytesPerSector / 4);
        CurrentLoadedSector = -1;
        Dirty = false;
    }
};

struct DirEntryEditor
{
    std::vector<int32_t> DirClusters;
    std::vector<uint8_t> DirEntries;
    uint32_t CurrentLoadedSector;

    int32_t CurrentLoadedCluster;
    int32_t DirStartCluster;
    int32_t DirEntryIndex;
    bool IgnoreDotAndDotDot;
    bool IgnoreClusterZero;
    bool ReachedEnd;

    void SaveAllChanges()
    {
        if (CurrentLoadedSector != -1)
        {
            FatFilesystem.seekp(GetSectorStartByte(CurrentLoadedSector));
            FatFilesystem.write((char*)DirEntries.data(), BS.BytesPerSector);
        }
    }

    void EnsureSectorLoaded(int32_t Cluster, int32_t EntryIndex)
    {
        if (CurrentLoadedCluster != Cluster)
        {
            DirClusters = GetClusterChain(DirStartCluster);
        }

        DirStartCluster = Cluster;
        CurrentLoadedCluster = Cluster;
        DirEntryIndex = EntryIndex;

        int64_t DirEntryByteOffset = DirEntryIndex * sizeof(DirectoryEntry);
        int32_t RealDirCluster = DirClusters[DirEntryByteOffset / BytesPerCluster];

        uint64_t DirEntrySector = GetDataStartSector(RealDirCluster) + (DirEntryByteOffset % BytesPerCluster) / BS.BytesPerSector;

        if (CurrentLoadedSector != DirEntrySector)
        {
            // Load new sector up
            FatFilesystem.seekg(GetSectorStartByte(DirEntrySector));
            FatFilesystem.read((char*)DirEntries.data(), BS.BytesPerSector);
            CurrentLoadedSector = DirEntrySector;
        }
    }

    void InitializeIterator(int32_t Cluster)
    {
        DirStartCluster = Cluster;
        DirEntryIndex = -1;
        ReachedEnd = false;
    }

    DirectoryEntry* GetDirEntry(int32_t Cluster, int32_t EntryIndex)
    {
        DirStartCluster = Cluster;
        DirEntryIndex = EntryIndex;

        EnsureSectorLoaded(Cluster, EntryIndex);
        return &((DirectoryEntry*)DirEntries.data())[EntryIndex % (BS.BytesPerSector / sizeof(DirectoryEntry))];
    }

    DirectoryEntry* GetNextEntry()
    {
        while (true)
        {
            DirEntryIndex++;
            DirectoryEntry* NextEntry = GetDirEntry(DirStartCluster, DirEntryIndex);

            if (NextEntry->IsLastEntry())
            {
                ReachedEnd = true;
                return nullptr;
            }

            if (   NextEntry->IsUnusedEntry()
                || NextEntry->IsLFN()
                || (NextEntry->GetClusterNumber() == 0 && IgnoreClusterZero)
                || (NextEntry->IsDotOrDoubleDotDir() && IgnoreDotAndDotDot))
            {
                continue;
            }

            return NextEntry;
        }
    }

    DirectoryEntry* GetDirEntryByName(int32_t DirCluster, std::string FileName)
    {
        InitializeIterator(DirCluster);
        ResetIgnoreSettings();
        IgnoreClusterZero = false;
        IgnoreDotAndDotDot = false;

        while (!ReachedEnd)
        {
            DirectoryEntry* DirEntry = GetNextEntry();

            if (!DirEntry)
            {
                return nullptr;
            }

            if (std::string(DirEntry->ShortFileName, sizeof(DirEntry->ShortFileName)) == FileName)
            {
                return DirEntry;
            }
        }

        return nullptr;
    }

    void ResetIgnoreSettings()
    {
        IgnoreDotAndDotDot = true;
        IgnoreClusterZero = true;
    }

    DirEntryEditor()
    {
        DirEntries.resize(BS.BytesPerSector);
        CurrentLoadedSector = -1;

        CurrentLoadedCluster = -1;
        DirStartCluster = -1;
        DirEntryIndex = -1;
        ReachedEnd = false;

        ResetIgnoreSettings();
    }
};

uint64_t GetDataStartSector(int32_t ClusterNumber)
{
    return DataStartSector + (static_cast<uint64_t>(ClusterNumber) - 2) * BS.SectorsPerCluster;
}

uint64_t GetDataStartByte(int32_t ClusterNumber)
{
    return GetDataStartSector(ClusterNumber) * BS.BytesPerSector;
}

uint64_t GetSectorStartByte(int32_t Sector)
{
    return static_cast<uint64_t>(Sector) * BS.BytesPerSector;
}

std::vector<int32_t> GetClusterChain(int32_t StartCluster)
{
    FatEditor FE;
    std::vector<int32_t> Clusters;
    int32_t CurrentCluster = StartCluster;

    do
    {
        Clusters.push_back(CurrentCluster);
        CurrentCluster = FE.GetFatEntry(CurrentCluster);
    } while (CurrentCluster < 0x0ffffff8);

    return Clusters;
}

void PrintFilesInDir(int32_t DirCluster, bool Recursive = false, bool IgnoreDots = false)
{
    DirEntryEditor DE;
    DE.ResetIgnoreSettings();
    DE.IgnoreDotAndDotDot = IgnoreDots;
    DE.IgnoreClusterZero = false;

    std::queue<uint32_t> DirQueue;
    DirQueue.push(DirCluster);

    while (!DirQueue.empty())
    {
        uint32_t CurrentDirCluster = DirQueue.front();
        DirQueue.pop();

        DE.InitializeIterator(CurrentDirCluster);
        while (true)
        {
            DirectoryEntry* DirEntry = DE.GetNextEntry();

            if (!DirEntry)
            {
                break;
            }

            if (Recursive && DirEntry->IsDirectory())
            {
                DirQueue.push(DirEntry->GetClusterNumber());
            }

            std::cout << (DirEntry->IsDirectory() ? "D " : "  ") << std::setw(10) << DirEntry->GetClusterNumber() << ": " << DirEntry->ShortFileName << " " << DirEntry->FileSize << "\n";
        }
    }
}

void MoveAllFilesToEnd()
{
    DirEntryEditor DE;

    // First, we discover all files and sort them by their starting cluster
    struct MoveFileJob
    {
        uint32_t ParentDirCluster;
        uint32_t DirEntryIndex;
        uint32_t Cluster;
    };

    std::vector<MoveFileJob> MoveFileJobs;
    std::vector<uint32_t> ClusterRemapping;
    ClusterRemapping.resize(FATEntryCount, 0);
    for (int i = 0; i < FATEntryCount; i++)
    {
        ClusterRemapping[i] = i + 2;
    }

    std::queue<int32_t> DirQueue;
    DirQueue.push(BS.RootDirCluster);

    while (!DirQueue.empty())
    {
        int32_t CurrentDirCluster = DirQueue.front();
        DirQueue.pop();

        DE.InitializeIterator(CurrentDirCluster);
        DE.ResetIgnoreSettings();

        while (true)
        {
            DirectoryEntry* DirEntry = DE.GetNextEntry();

            if (!DirEntry)
            {
                break;
            }

            if (DirEntry->IsDirectory())
            {
                DirQueue.push(DirEntry->GetClusterNumber());
            }

            MoveFileJob MFJ;
            MFJ.ParentDirCluster = CurrentDirCluster;
            MFJ.DirEntryIndex = DE.DirEntryIndex;
            MFJ.Cluster = DirEntry->GetClusterNumber();

            MoveFileJobs.push_back(MFJ);
        }
    }

    std::sort(MoveFileJobs.begin(), MoveFileJobs.end(), [](MoveFileJob A, MoveFileJob B){ return A.Cluster < B.Cluster;});

    for (int i = 0; i < MoveFileJobs.size(); i++)
    {
        MoveFileJob MFJ = MoveFileJobs[i];
        ClusterRemapping[MFJ.Cluster - 2] = MoveFileToEnd(ClusterRemapping[MFJ.ParentDirCluster - 2], MFJ.DirEntryIndex, MFJ.Cluster);
        std::cout << "\r" << std::setw(std::log10(MoveFileJobs.size())) << i << " / " << MoveFileJobs.size();
    }
    std::cout << "\n";
}

uint32_t MoveFileToEnd(uint32_t ParentDirCluster, uint32_t DirEntryIndex, uint32_t FileCluster)
{
    DirEntryEditor DE;
    DirEntryEditor SubDE;
    DirEntryEditor SubDE2;
    FatEditor FE;

    DirectoryEntry* DirEntry = DE.GetDirEntry(ParentDirCluster, DirEntryIndex);

    if (DirEntry->GetClusterNumber() != FileCluster)
    {
        std::cerr << "specified directory entry doesnt match file cluster number";
        exit(1);
    }

    // Start moving the file to the end

    // Find clusters to transfer between
    std::vector<int32_t> ClusterChain = GetClusterChain(DirEntry->GetClusterNumber());
    std::vector<int32_t> FreeClusters;

    int32_t ClustersFound = 0;

    for (int i = BiggestFreeCluster; i >= 2; i--)
    {
        if (FE.GetFatEntry(i) == 0)
        {
            FreeClusters.push_back(i);
            ClustersFound++;

            if (ClustersFound == ClusterChain.size())
            {
                break;
            }
        }
    }

    if (FreeClusters.size() == 0)
    {
        return FileCluster;
    }

    // Pick the highest clusters from the two sets we have.
    std::vector<int32_t> SortedClusters;
    SortedClusters.reserve(ClusterChain.size() + FreeClusters.size());
    SortedClusters.insert(SortedClusters.end(), ClusterChain.begin(), ClusterChain.end());
    SortedClusters.insert(SortedClusters.end(), FreeClusters.begin(), FreeClusters.end());
    std::sort(SortedClusters.begin(), SortedClusters.end());

    std::vector<int32_t> NewClusters;
    NewClusters.resize(ClusterChain.size(), -1);

    // insert recycled Clusters first
    for (int i = 0; i < ClusterChain.size(); i++)
    {
        int32_t Cluster = SortedClusters[SortedClusters.size() - 1 - i];
        auto It = std::find(ClusterChain.begin(), ClusterChain.end(), Cluster);

        // Keep old clusters in the same place in the chain
        if (It != ClusterChain.end())
        {
            NewClusters[std::distance(ClusterChain.begin(), It)] = Cluster;
            continue;
        }
    }

    // insert new Clusters where there is space
    for (int i = 0; i < ClusterChain.size(); i++)
    {
        int32_t Cluster = SortedClusters[SortedClusters.size() - 1 - i];
        auto It = std::find(ClusterChain.begin(), ClusterChain.end(), Cluster);

        // Keep old clusters in the same place in the chain
        if (It == ClusterChain.end())
        {
            int32_t InsertPosition = std::distance(NewClusters.begin(), std::find(NewClusters.begin(), NewClusters.end(), -1));
            NewClusters[InsertPosition] = Cluster;
        }
    }

    BiggestFreeCluster = *std::min_element(NewClusters.begin(), NewClusters.end());

    if (std::find(NewClusters.begin(), NewClusters.end(), -1) != NewClusters.end())
    {
        std::cerr << "New Clusters not completely filled\n";
        std::cerr << "Directory: " << ParentDirCluster << ", Entry: " << DE.DirEntryIndex;
        exit(1);
    }

    // Copy Data
    if (ClusterChain == NewClusters)
    {
        return FileCluster;
    }

    std::vector<int8_t> ReadBuffer;
    ReadBuffer.resize(BytesPerCluster);

    for (int i = 0; i < ClusterChain.size(); i++)
    {
        if (ClusterChain[i] == NewClusters[i])
        {
            continue;
        }

        FatFilesystem.seekg(GetDataStartByte(ClusterChain[i]));
        FatFilesystem.read((char*)ReadBuffer.data(), BytesPerCluster);

        FatFilesystem.seekp(GetDataStartByte(NewClusters[i]));
        FatFilesystem.write((char*)ReadBuffer.data(), BytesPerCluster);
    }

    // Write to FAT
    for (int i = 0; i < ClusterChain.size(); i++)
    {
        FE.SetFatEntry(ClusterChain[i], 0);
    }

    for (int i = 0; i < NewClusters.size(); i++)
    {
        int32_t NewEntry = i == NewClusters.size() - 1 ? 0x0FFFFFFF : NewClusters[i+1];
        FE.SetFatEntry(NewClusters[i], NewEntry);
    }

    FE.SaveAllChanges();

    // Set new initial cluster in dir entry
    uint32_t NewDirCluster = NewClusters[0];
    DirEntry->SetClusterNumber(NewDirCluster);
    DE.SaveAllChanges();

    if (DirEntry->IsDirectory())
    {
        // Correct . entry
        SubDE.GetDirEntryByName(NewDirCluster, Dot)->SetClusterNumber(NewDirCluster);
        SubDE.SaveAllChanges();

        // .. entries too
        SubDE.InitializeIterator(NewDirCluster);
        SubDE.ResetIgnoreSettings();
        SubDE.IgnoreClusterZero = false;

        while (true)
        {
            DirectoryEntry* SubDirEntry = SubDE.GetNextEntry();
            if (!SubDirEntry || !SubDirEntry->IsDirectory())
            {
                break;
            }

            SubDE2.GetDirEntryByName(SubDirEntry->GetClusterNumber(), DotDot)->SetClusterNumber(NewDirCluster == 2 ? 0 : NewDirCluster);
            SubDE2.SaveAllChanges();
        }
    }

    return NewDirCluster;
}

void PrintFATOccupancy(int64_t Scale = 1)
{
    FatEditor FE;

    int FullCount = 0;

    for (int i = 0; i < FATEntryCount; i++)
    {
        bool IsFree = FE.GetFatEntry(i+2) == 0;
        FullCount += IsFree ? 0 : 1;

        if (i % Scale == 0)
        {
            std::cout << (FullCount > Scale / 2 ? 'O' : '.');
            FullCount = 0;
        }
    }

    std::cout << "\n";
}

int32_t main(int32_t argc, char* argv[])
{
    /*if (argc != 3)
    {
        std::cerr << "bad arguments" << "\n";
        exit(1);
    }*/

    FatFilesystem.open(argv[2], std::ios::in | std::ios::out);

    FatFilesystem.read((char*)&BS, sizeof(BS));

    FatFilesystem.seekg(GetSectorStartByte(BS.FileSystemInfoSector));
    FatFilesystem.read((char*)&FSI, sizeof(FSI));

    FATStartSector = BS.ReservedSectorCount;
    DataStartSector = FATStartSector + BS.FATSectorCount * BS.NumberOfFATs;

    FATEntryCount = (BS.TotalSectors - DataStartSector) / BS.SectorsPerCluster;
    BiggestFreeCluster = FATEntryCount + 2 - 1;

    BytesPerCluster = BS.SectorsPerCluster * BS.BytesPerSector;

    int32_t DataClusterCount = (BS.TotalSectors - DataStartSector) / BS.SectorsPerCluster;
    if (DataClusterCount < 65526)
    {
        std::cerr << "File system is not FAT32 or has less than 65526 clusters." << "\n";
        exit(1);
    }

    //////

    if (argv[1] == std::string("printclusters"))
    {
        PrintFATOccupancy(std::stoi(argv[3]));
    }
    else if (argv[1] == std::string("moveclusters"))
    {
        MoveAllFilesToEnd();
    }
    else if (argv[1] == std::string("movefiletoend"))
    {
        MoveFileToEnd(std::stoi(argv[3]), std::stoi(argv[4]), std::stoi(argv[5]));
    }
    else if (argv[1] == std::string("printdir"))
    {
        PrintFilesInDir(std::stoi(argv[3]));
    }
    else if (argv[1] == std::string("printallfiles"))
    {
        PrintFilesInDir(BS.RootDirCluster, true, true);
    }
    else if (argv[1] == std::string("printfileclusters"))
    {
        std::vector<int32_t> Clusters = GetClusterChain(std::stoi(argv[3]));
        for (int i = 0; i < Clusters.size(); i++)
        {
            std::cout << Clusters[i] << "\n";
        }
    }
    else if (argv[1] == std::string("printnextfreecluster"))
    {
        std::cout << FSI.NextFreeCluster << "\n";
    }
    else if (argv[1] == std::string("setnextfreecluster"))
    {
        FSI.NextFreeCluster = std::stoi(argv[3]);
        FatFilesystem.seekp(GetSectorStartByte(BS.FileSystemInfoSector));
        FatFilesystem.write((char*)&FSI, sizeof(FSI));
    }
    else
    {
        std::cerr << "don't know that command" << "\n";
    }

    return 0;
}
