#!/usr/bin/env python3
"""AmigaDisk — Linux GUI tool for Amiga RDB (Rigid Disk Block) partitioning."""

import tkinter as tk
from tkinter import ttk, messagebox
import subprocess, struct, os, math, json
from typing import List, Optional

# ─── Constants ─────────────────────────────────────────────────────────────────
RDSK_ID      = 0x5244534B   # "RDSK"
PART_ID      = 0x50415254   # "PART"
END_MARK     = 0xFFFFFFFF
RDB_SCAN_LIMIT = 16

FS_TYPES = {
    0x444F5300: "OFS",        0x444F5301: "FFS",
    0x444F5302: "OFS+Intl",   0x444F5303: "FFS+Intl",
    0x444F5304: "OFS+DC+Intl",0x444F5305: "FFS+DC+Intl",
    0x53465300: "SFS\\0",
}
FS_MENU = [
    ("FFS — Fast File System",        0x444F5301),
    ("OFS — Original File System",    0x444F5300),
    ("FFS+Intl",                       0x444F5303),
    ("OFS+Intl",                       0x444F5302),
    ("FFS+DC+Intl",                    0x444F5305),
    ("SFS — Smart File System",        0x53465300),
]
COLORS = ["#4A90D9","#E67E22","#27AE60","#8E44AD","#E74C3C","#16A085","#F39C12","#2980B9"]


# ─── Data classes ──────────────────────────────────────────────────────────────

class PartitionInfo:
    def __init__(self):
        self.block_num    = -1
        self.next_part    = END_MARK
        self.flags        = 0          # 0 = bootable/normal
        self.drive_name   = "DH0"
        self.low_cyl      = 0
        self.high_cyl     = 0
        self.surfaces     = 1          # heads
        self.blk_per_trk  = 1          # sectors per track
        self.secs_per_blk = 1          # sectors per filesystem block (usually 1)
        self.reserved     = 2
        self.prealloc     = 0
        self.interleave   = 0
        self.num_buffer   = 30
        self.buf_mem_type = 1          # chip RAM
        self.max_transfer = 0x7FFFFFFF
        self.mask         = 0xFFFFFFFE
        self.boot_pri     = 0
        self.dos_type     = 0x444F5301 # FFS
        self.boot_blocks  = 2

    @property
    def size_bytes(self):
        cyls = max(0, self.high_cyl - self.low_cyl + 1)
        return cyls * self.surfaces * self.blk_per_trk * 512

    @property
    def fs_name(self):
        return FS_TYPES.get(self.dos_type, f"0x{self.dos_type:08X}")


class RDBInfo:
    def __init__(self):
        self.block_num      = -1
        self.hostid         = 7
        self.flags          = 0x12
        self.cylinders      = 0
        self.sectors        = 0   # sectors per track
        self.heads          = 0
        self.rdbblock_lo    = 0
        self.rdbblock_hi    = 15
        self.locyl          = 0   # first usable partition cylinder
        self.hicyl          = 0   # last cylinder
        self.disk_vendor    = ""
        self.disk_product   = ""
        self.disk_revision  = ""
        self.part_list_blk  = END_MARK
        self.fshdr_list     = END_MARK
        self.bad_block      = END_MARK
        self.partitions: List[PartitionInfo] = []


# ─── Binary helpers ────────────────────────────────────────────────────────────

def _fix_checksum(data: bytearray, offset: int = 8) -> bytearray:
    struct.pack_into(">I", data, offset, 0)
    total = sum(struct.unpack_from(">I", data, i)[0] for i in range(0, len(data), 4))
    struct.pack_into(">I", data, offset, (-total) & 0xFFFFFFFF)
    return data


def _read_block(dev: str, block: int) -> Optional[bytes]:
    try:
        with open(dev, "rb") as f:
            f.seek(block * 512)
            return f.read(512)
    except OSError:
        return None


def _write_block(dev: str, block: int, data: bytes) -> bool:
    try:
        with open(dev, "r+b") as f:
            f.seek(block * 512)
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        return True
    except OSError:
        return False


# ─── RDB read ──────────────────────────────────────────────────────────────────

def read_rdb(dev: str) -> Optional[RDBInfo]:
    rdb = RDBInfo()

    # Find RDSK block in first 16 blocks
    for blk in range(RDB_SCAN_LIMIT):
        data = _read_block(dev, blk)
        if data is None:
            return None
        if len(data) < 256:
            continue
        if struct.unpack_from(">I", data, 0)[0] != RDSK_ID:
            continue

        rdb.block_num = blk

        # Offsets per NDK RigidDiskBlock struct
        rdb.hostid          = struct.unpack_from(">I", data, 12)[0]
        rdb.flags           = struct.unpack_from(">I", data, 20)[0]
        rdb.bad_block       = struct.unpack_from(">I", data, 24)[0]
        rdb.part_list_blk   = struct.unpack_from(">I", data, 28)[0]
        rdb.fshdr_list      = struct.unpack_from(">I", data, 32)[0]

        # Physical geometry: offsets 64, 68, 72
        rdb.cylinders = struct.unpack_from(">I", data, 64)[0]
        rdb.sectors   = struct.unpack_from(">I", data, 68)[0]
        rdb.heads     = struct.unpack_from(">I", data, 72)[0]

        # Logical block range + partition cylinder range: offsets 128-144
        rdb.rdbblock_lo = struct.unpack_from(">I", data, 128)[0]
        rdb.rdbblock_hi = struct.unpack_from(">I", data, 132)[0]
        rdb.locyl       = struct.unpack_from(">I", data, 136)[0]
        rdb.hicyl       = struct.unpack_from(">I", data, 140)[0]

        # Drive ID strings
        rdb.disk_vendor   = data[160:168].rstrip(b'\x00').decode('ascii', errors='replace')
        rdb.disk_product  = data[168:184].rstrip(b'\x00').decode('ascii', errors='replace')
        rdb.disk_revision = data[184:188].rstrip(b'\x00').decode('ascii', errors='replace')
        break
    else:
        return None

    # Walk partition linked list
    next_blk = rdb.part_list_blk
    seen = set()
    while next_blk != END_MARK and next_blk not in seen and len(rdb.partitions) < 64:
        seen.add(next_blk)
        data = _read_block(dev, next_blk)
        if data is None or len(data) < 256:
            break
        if struct.unpack_from(">I", data, 0)[0] != PART_ID:
            break

        p             = PartitionInfo()
        p.block_num   = next_blk
        p.next_part   = struct.unpack_from(">I", data, 16)[0]
        p.flags       = struct.unpack_from(">I", data, 20)[0]

        # BCPL drive name at offset 36 (byte 0 = length)
        name_len = min(data[36], 31)
        p.drive_name = data[37:37+name_len].decode('ascii', errors='replace')

        # DosEnvec at offset 128
        e = 128
        # e+0:  TableSize
        # e+4:  SizeBlock   = 128
        # e+8:  SecOrg      = 0
        # e+12: Surfaces    = heads
        # e+16: SectorsPerBlock = 1
        # e+20: BlocksPerTrack  = sectors/track
        # e+24: Reserved    = 2
        # e+28: PreAlloc    = 0
        # e+32: Interleave  = 0
        # e+36: LowCyl
        # e+40: HighCyl
        # e+44: NumBuffer
        # e+48: BufMemType
        # e+52: MaxTransfer
        # e+56: Mask
        # e+60: BootPri  (signed)
        # e+64: DosType
        # e+68: Baud
        # e+72: Control
        # e+76: BootBlocks
        p.surfaces     = struct.unpack_from(">I", data, e+12)[0]
        p.secs_per_blk = struct.unpack_from(">I", data, e+16)[0]
        p.blk_per_trk  = struct.unpack_from(">I", data, e+20)[0]
        p.reserved     = struct.unpack_from(">I", data, e+24)[0]
        p.prealloc     = struct.unpack_from(">I", data, e+28)[0]
        p.interleave   = struct.unpack_from(">I", data, e+32)[0]
        p.low_cyl      = struct.unpack_from(">I", data, e+36)[0]
        p.high_cyl     = struct.unpack_from(">I", data, e+40)[0]
        p.num_buffer   = struct.unpack_from(">I", data, e+44)[0]
        p.buf_mem_type = struct.unpack_from(">I", data, e+48)[0]
        p.max_transfer = struct.unpack_from(">I", data, e+52)[0]
        p.mask         = struct.unpack_from(">I", data, e+56)[0]
        p.boot_pri     = struct.unpack_from(">i", data, e+60)[0]  # signed
        p.dos_type     = struct.unpack_from(">I", data, e+64)[0]
        if len(data) >= e + 80:
            p.boot_blocks = struct.unpack_from(">I", data, e+76)[0]

        rdb.partitions.append(p)
        next_blk = p.next_part

    return rdb


# ─── RDB write ─────────────────────────────────────────────────────────────────

def build_rdsk_block(rdb: RDBInfo) -> bytes:
    d = bytearray(512)
    struct.pack_into(">I", d,   0, RDSK_ID)
    struct.pack_into(">I", d,   4, 128)            # SummedLongs = 512/4
    struct.pack_into(">I", d,   8, 0)              # checksum (filled below)
    struct.pack_into(">I", d,  12, rdb.hostid)
    struct.pack_into(">I", d,  16, 512)            # BlockBytes
    struct.pack_into(">I", d,  20, rdb.flags)
    struct.pack_into(">I", d,  24, END_MARK)       # BadBlockList
    struct.pack_into(">I", d,  28, rdb.part_list_blk)
    struct.pack_into(">I", d,  32, END_MARK)       # FileSysHeaderList
    struct.pack_into(">I", d,  36, END_MARK)       # DriveInit
    struct.pack_into(">I", d,  40, END_MARK)       # BootBlockList
    for i in range(5):                              # Reserved1[5]
        struct.pack_into(">I", d, 44+i*4, END_MARK)

    # Physical geometry
    struct.pack_into(">I", d,  64, rdb.cylinders)
    struct.pack_into(">I", d,  68, rdb.sectors)
    struct.pack_into(">I", d,  72, rdb.heads)
    struct.pack_into(">I", d,  76, 0)             # Interleave
    struct.pack_into(">I", d,  80, rdb.cylinders-1) # Park

    # WritePreComp, ReducedWrite, StepRate (96, 100, 104)
    struct.pack_into(">I", d,  96, 0)
    struct.pack_into(">I", d, 100, 0)
    struct.pack_into(">I", d, 104, 3)

    # Logical block range
    struct.pack_into(">I", d, 128, rdb.rdbblock_lo)
    struct.pack_into(">I", d, 132, rdb.rdbblock_hi)
    struct.pack_into(">I", d, 136, rdb.locyl)
    struct.pack_into(">I", d, 140, rdb.hicyl)
    struct.pack_into(">I", d, 144, rdb.heads * rdb.sectors)  # CylBlocks
    struct.pack_into(">I", d, 148, 0)                        # AutoParkSeconds
    struct.pack_into(">I", d, 152, rdb.rdbblock_hi)          # HighRDSKBlock

    # Drive ID strings
    d[160:168] = rdb.disk_vendor.encode('ascii','replace')[:8].ljust(8, b'\x00')
    d[168:184] = rdb.disk_product.encode('ascii','replace')[:16].ljust(16, b'\x00')
    d[184:188] = rdb.disk_revision.encode('ascii','replace')[:4].ljust(4, b'\x00')

    _fix_checksum(d, 8)
    return bytes(d)


def build_part_block(p: PartitionInfo, rdb_heads: int, rdb_sectors: int) -> bytes:
    d = bytearray(512)
    surfs = p.surfaces or rdb_heads
    spt   = p.blk_per_trk or rdb_sectors

    struct.pack_into(">I", d,  0, PART_ID)
    struct.pack_into(">I", d,  4, 128)         # SummedLongs
    struct.pack_into(">I", d,  8, 0)           # checksum
    struct.pack_into(">I", d, 12, 7)           # HostID
    struct.pack_into(">I", d, 16, p.next_part)
    struct.pack_into(">I", d, 20, p.flags)

    # BCPL drive name at offset 36
    name_b = p.drive_name.encode('ascii','replace')[:31]
    d[36] = len(name_b)
    d[37:37+len(name_b)] = name_b

    # DosEnvec at offset 128
    e = 128
    struct.pack_into(">I", d, e+ 0, 20)            # TableSize (20 longs = through BootBlocks)
    struct.pack_into(">I", d, e+ 4, 128)           # SizeBlock = 512/4
    struct.pack_into(">I", d, e+ 8, 0)             # SecOrg
    struct.pack_into(">I", d, e+12, surfs)         # Surfaces
    struct.pack_into(">I", d, e+16, 1)             # SectorsPerBlock
    struct.pack_into(">I", d, e+20, spt)           # BlocksPerTrack
    struct.pack_into(">I", d, e+24, p.reserved)    # Reserved
    struct.pack_into(">I", d, e+28, p.prealloc)    # PreAlloc
    struct.pack_into(">I", d, e+32, p.interleave)  # Interleave
    struct.pack_into(">I", d, e+36, p.low_cyl)     # LowCyl
    struct.pack_into(">I", d, e+40, p.high_cyl)    # HighCyl
    struct.pack_into(">I", d, e+44, p.num_buffer)  # NumBuffer
    struct.pack_into(">I", d, e+48, p.buf_mem_type)# BufMemType
    struct.pack_into(">I", d, e+52, p.max_transfer)# MaxTransfer
    struct.pack_into(">I", d, e+56, p.mask)        # Mask
    struct.pack_into(">i", d, e+60, p.boot_pri)    # BootPri (signed)
    struct.pack_into(">I", d, e+64, p.dos_type)    # DosType
    struct.pack_into(">I", d, e+68, 0)             # Baud
    struct.pack_into(">I", d, e+72, 0)             # Control
    struct.pack_into(">I", d, e+76, p.boot_blocks) # BootBlocks

    _fix_checksum(d, 8)
    return bytes(d)


# ─── Disk enumeration ──────────────────────────────────────────────────────────

def get_disks() -> list:
    try:
        r = subprocess.run(
            ["lsblk", "-b", "-d", "-o", "NAME,SIZE,MODEL,TYPE", "--json"],
            capture_output=True, text=True, timeout=10)
        data = json.loads(r.stdout)
        result = []
        for dev in data.get("blockdevices", []):
            if dev.get("type") != "disk":
                continue
            name = dev.get("name", "")
            size = int(dev.get("size") or 0)
            model = (dev.get("model") or "").strip()
            result.append({"name": name, "path": f"/dev/{name}",
                            "size": size, "model": model})
        return result
    except Exception:
        return []


def fmt_size(b: int) -> str:
    for unit in ("B","KB","MB","GB","TB"):
        if b < 1024:
            return f"{b:.1f} {unit}"
        b /= 1024
    return f"{b:.1f} PB"


# ─── Dialogs ───────────────────────────────────────────────────────────────────

class InitRDBDialog(tk.Toplevel):
    def __init__(self, parent, disk: dict):
        super().__init__(parent)
        self.title("Initialize Amiga RDB")
        self.resizable(False, False)
        self.grab_set()
        self.result: Optional[RDBInfo] = None
        self._disk = disk
        self._build()
        self.transient(parent)
        self.wait_window()

    def _build(self):
        f = tk.Frame(self, padx=12, pady=10)
        f.pack(fill="both", expand=True)
        row = 0

        tk.Label(f, text=f"Disk: {self._disk['path']}",
                 font=("",10,"bold")).grid(row=row, columnspan=2, sticky="w"); row+=1
        tk.Label(f, text=f"Size: {fmt_size(self._disk['size'])}",
                 fg="gray").grid(row=row, columnspan=2, sticky="w"); row+=1

        total_secs = self._disk["size"] // 512
        def_heads, def_spt = 16, 63
        def_cyls = total_secs // (def_heads * def_spt)

        fields = [
            ("Heads:",         str(def_heads), "_h"),
            ("Sectors/track:", str(def_spt),   "_s"),
            ("Cylinders:",     str(def_cyls),  "_c"),
            ("RDB reserve\n(block 0–N):", "15", "_rhi"),
        ]
        self._vars = {}
        for label, default, key in fields:
            tk.Label(f, text=label, justify="right").grid(row=row, column=0, sticky="e", pady=3)
            v = tk.StringVar(value=default)
            self._vars[key] = v
            tk.Entry(f, textvariable=v, width=10).grid(row=row, column=1, sticky="w", pady=3)
            row += 1

        tk.Label(f, text="Partitions start after the RDB reserved area.",
                 fg="gray", font=("",8)).grid(row=row, columnspan=2, sticky="w"); row+=1

        bf = tk.Frame(f)
        bf.grid(row=row, columnspan=2, pady=(8,0))
        tk.Button(bf, text="Initialize", width=12, command=self._ok).pack(side="left", padx=4)
        tk.Button(bf, text="Cancel",     width=10, command=self.destroy).pack(side="left", padx=4)

    def _ok(self):
        try:
            heads = int(self._vars["_h"].get())
            spt   = int(self._vars["_s"].get())
            cyls  = int(self._vars["_c"].get())
            rdbhi = int(self._vars["_rhi"].get())
        except ValueError:
            messagebox.showerror("Error", "All values must be integers.", parent=self); return
        if heads < 1 or spt < 1 or cyls < 1 or rdbhi < 0:
            messagebox.showerror("Error", "Values must be positive.", parent=self); return

        locyl = math.ceil((rdbhi + 1) / (heads * spt))

        rdb = RDBInfo()
        rdb.block_num    = 0
        rdb.cylinders    = cyls
        rdb.sectors      = spt
        rdb.heads        = heads
        rdb.rdbblock_lo  = 0
        rdb.rdbblock_hi  = rdbhi
        rdb.locyl        = locyl
        rdb.hicyl        = cyls - 1
        rdb.disk_vendor  = self._disk["model"][:8]
        rdb.disk_product = self._disk["model"][8:24] if len(self._disk["model"]) > 8 else ""
        self.result = rdb
        self.destroy()


class AddPartitionDialog(tk.Toplevel):
    def __init__(self, parent, rdb: RDBInfo,
                 preset_lo: int = None, preset_hi: int = None):
        super().__init__(parent)
        self.title("Add Partition")
        self.resizable(False, False)
        self.grab_set()
        self.result: Optional[PartitionInfo] = None
        self._rdb = rdb
        self._preset_lo = preset_lo
        self._preset_hi = preset_hi
        self._build()
        self.transient(parent)
        self.wait_window()

    def _suggest_name(self):
        used = {p.drive_name for p in self._rdb.partitions}
        for i in range(20):
            n = f"DH{i}"
            if n not in used:
                return n
        return "DH0"

    def _find_free(self):
        if self._preset_lo is not None:
            return self._preset_lo, self._preset_hi if self._preset_hi is not None else self._rdb.hicyl
        used = sorted((p.low_cyl, p.high_cyl) for p in self._rdb.partitions)
        candidate = self._rdb.locyl
        for lo, hi in used:
            if candidate < lo:
                return candidate, lo - 1
            candidate = max(candidate, hi + 1)
        return candidate, self._rdb.hicyl

    def _build(self):
        f = tk.Frame(self, padx=12, pady=10)
        f.pack(fill="both", expand=True)
        row = 0

        free_lo, free_hi = self._find_free()

        def lbl_entry(label, val, key, width=12):
            nonlocal row
            tk.Label(f, text=label, justify="right").grid(row=row, column=0, sticky="e", pady=3)
            v = tk.StringVar(value=val)
            self._vars[key] = v
            tk.Entry(f, textvariable=v, width=width).grid(row=row, column=1, sticky="w", pady=3)
            row += 1

        self._vars = {}
        lbl_entry("Drive name:",    self._suggest_name(), "name", 10)
        lbl_entry("Low cylinder:",  str(free_lo),         "lo",   10)
        lbl_entry("High cylinder:", str(free_hi),         "hi",   10)

        tk.Label(f, text=f"(usable: {self._rdb.locyl}–{self._rdb.hicyl})",
                 fg="gray", font=("",8)).grid(row=row, columnspan=2, sticky="w"); row+=1

        tk.Label(f, text="Filesystem:").grid(row=row, column=0, sticky="e", pady=3)
        self._fs_var = tk.StringVar(value=FS_MENU[0][0])
        ttk.Combobox(f, textvariable=self._fs_var,
                     values=[x[0] for x in FS_MENU],
                     state="readonly", width=30).grid(row=row, column=1, sticky="w", pady=3)
        row += 1

        lbl_entry("Boot priority:", "0", "bootpri", 6)

        self._bootable_var = tk.BooleanVar(value=True)
        tk.Checkbutton(f, text="Bootable", variable=self._bootable_var).grid(
            row=row, columnspan=2, sticky="w"); row+=1

        self._size_lbl = tk.Label(f, text="", fg="#336699")
        self._size_lbl.grid(row=row, columnspan=2, sticky="w"); row+=1

        for key in ("lo","hi"):
            self._vars[key].trace_add("write", self._upd_size)
        self._upd_size()

        bf = tk.Frame(f)
        bf.grid(row=row, columnspan=2, pady=(8,0))
        tk.Button(bf, text="Add",    width=10, command=self._ok).pack(side="left", padx=4)
        tk.Button(bf, text="Cancel", width=10, command=self.destroy).pack(side="left", padx=4)

    def _upd_size(self, *_):
        try:
            lo = int(self._vars["lo"].get())
            hi = int(self._vars["hi"].get())
            cyls = hi - lo + 1
            sz = cyls * self._rdb.heads * self._rdb.sectors * 512
            self._size_lbl.config(text=f"Size: {fmt_size(sz)}  ({cyls} cylinders)")
        except ValueError:
            self._size_lbl.config(text="")

    def _ok(self):
        name = self._vars["name"].get().strip()
        if not name:
            messagebox.showerror("Error", "Drive name is required.", parent=self); return
        try:
            lo = int(self._vars["lo"].get())
            hi = int(self._vars["hi"].get())
            bp = int(self._vars["bootpri"].get())
        except ValueError:
            messagebox.showerror("Error", "Numeric fields must be integers.", parent=self); return
        if lo < self._rdb.locyl or hi > self._rdb.hicyl or lo > hi:
            messagebox.showerror("Error",
                f"Cylinder range must be within {self._rdb.locyl}–{self._rdb.hicyl}.", parent=self)
            return
        for p in self._rdb.partitions:
            if lo <= p.high_cyl and hi >= p.low_cyl:
                messagebox.showerror("Error",
                    f"Overlaps with existing partition {p.drive_name}.", parent=self)
                return

        dos_type = next(v for n,v in FS_MENU if n == self._fs_var.get())

        p = PartitionInfo()
        p.drive_name   = name
        p.low_cyl      = lo
        p.high_cyl     = hi
        p.dos_type     = dos_type
        p.boot_pri     = bp
        p.flags        = 0 if self._bootable_var.get() else 2
        p.surfaces     = self._rdb.heads
        p.blk_per_trk  = self._rdb.sectors
        self.result = p
        self.destroy()


# ─── Edit partition dialog ─────────────────────────────────────────────────────

class EditPartitionDialog(tk.Toplevel):
    def __init__(self, parent, rdb: RDBInfo, part_idx: int):
        super().__init__(parent)
        self.transient(parent)
        self.title("Edit Partition")
        self.resizable(False, False)
        self.result: Optional[PartitionInfo] = None
        self._rdb      = rdb
        self._idx      = part_idx
        self._orig     = rdb.partitions[part_idx]
        self._min_lo, self._max_hi = self._calc_window()
        self._build()
        self.update_idletasks()
        pw = parent.winfo_width();  ph = parent.winfo_height()
        px = parent.winfo_rootx(); py = parent.winfo_rooty()
        dw = self.winfo_reqwidth(); dh = self.winfo_reqheight()
        self.geometry(f"+{px + (pw - dw)//2}+{py + (ph - dh)//2}")
        self.wait_visibility()
        self.grab_set()
        self.wait_window()

    def _calc_window(self) -> tuple:
        """Return (min_lo, max_hi) — the cylinder range this partition can expand into."""
        others = [p for i, p in enumerate(self._rdb.partitions) if i != self._idx]
        others_sorted = sorted(others, key=lambda p: p.low_cyl)
        min_lo = self._rdb.locyl
        max_hi = self._rdb.hicyl
        for p in others_sorted:
            if p.high_cyl < self._orig.low_cyl:
                min_lo = max(min_lo, p.high_cyl + 1)
            if p.low_cyl > self._orig.high_cyl:
                max_hi = min(max_hi, p.low_cyl - 1)
        return min_lo, max_hi

    def _build(self):
        f = tk.Frame(self, padx=12, pady=10)
        f.pack(fill="both", expand=True)
        row = 0

        p = self._orig
        cyls = p.high_cyl - p.low_cyl + 1
        sz = fmt_size(cyls * self._rdb.heads * self._rdb.sectors * 512)
        tk.Label(f, text=f"Partition:  {p.drive_name}  ({sz})",
                 font=("", 10, "bold")).grid(row=row, columnspan=2, sticky="w"); row += 1
        tk.Label(f, text=f"Cylinder window: {self._min_lo}–{self._max_hi}",
                 fg="gray", font=("", 8)).grid(row=row, columnspan=2, sticky="w"); row += 1

        def lbl_entry(label, val, key, width=12):
            nonlocal row
            tk.Label(f, text=label, justify="right").grid(
                row=row, column=0, sticky="e", pady=3)
            v = tk.StringVar(value=val)
            self._vars[key] = v
            tk.Entry(f, textvariable=v, width=width).grid(
                row=row, column=1, sticky="w", pady=3)
            row += 1

        self._vars = {}
        lbl_entry("Drive name:",    p.drive_name,    "name", 10)
        lbl_entry("Low cylinder:",  str(p.low_cyl),  "lo",   10)
        lbl_entry("High cylinder:", str(p.high_cyl), "hi",   10)

        tk.Label(f, text="Filesystem:").grid(row=row, column=0, sticky="e", pady=3)
        self._fs_var = tk.StringVar(
            value=next((n for n, v in FS_MENU if v == p.dos_type), FS_MENU[0][0]))
        ttk.Combobox(f, textvariable=self._fs_var,
                     values=[x[0] for x in FS_MENU],
                     state="readonly", width=30).grid(row=row, column=1, sticky="w", pady=3)
        row += 1

        lbl_entry("Boot priority:", str(p.boot_pri), "bootpri", 6)

        self._bootable_var = tk.BooleanVar(value=(p.flags == 0))
        tk.Checkbutton(f, text="Bootable",
                       variable=self._bootable_var).grid(row=row, columnspan=2, sticky="w")
        row += 1

        self._size_lbl = tk.Label(f, text="", fg="#336699")
        self._size_lbl.grid(row=row, columnspan=2, sticky="w"); row += 1

        for key in ("lo", "hi"):
            self._vars[key].trace_add("write", self._upd_size)
        self._upd_size()

        bf = tk.Frame(f)
        bf.grid(row=row, columnspan=2, pady=(8, 0))
        tk.Button(bf, text="Save",   width=10, command=self._ok).pack(side="left", padx=4)
        tk.Button(bf, text="Cancel", width=10, command=self.destroy).pack(side="left", padx=4)

    def _upd_size(self, *_):
        try:
            lo = int(self._vars["lo"].get())
            hi = int(self._vars["hi"].get())
            cyls = hi - lo + 1
            sz = cyls * self._rdb.heads * self._rdb.sectors * 512
            self._size_lbl.config(text=f"Size: {fmt_size(sz)}  ({cyls} cylinders)")
        except ValueError:
            self._size_lbl.config(text="")

    def _ok(self):
        name = self._vars["name"].get().strip()
        if not name:
            messagebox.showerror("Error", "Drive name is required.", parent=self); return
        try:
            lo = int(self._vars["lo"].get())
            hi = int(self._vars["hi"].get())
            bp = int(self._vars["bootpri"].get())
        except ValueError:
            messagebox.showerror("Error", "Numeric fields must be integers.", parent=self); return

        if lo < self._min_lo or hi > self._max_hi or lo > hi:
            messagebox.showerror("Error",
                f"Cylinder range must be within {self._min_lo}–{self._max_hi} "
                f"and low ≤ high.", parent=self); return

        # Warn if cylinder range changed (data loss risk)
        resized = (lo != self._orig.low_cyl or hi != self._orig.high_cyl)
        if resized:
            if not messagebox.askyesno("Data Loss Warning",
                    f"You changed the cylinder range from "
                    f"{self._orig.low_cyl}–{self._orig.high_cyl} to {lo}–{hi}.\n\n"
                    "Resizing a partition WILL corrupt or lose the data on it.\n\n"
                    "Continue?", icon="warning", parent=self):
                return

        p = PartitionInfo()
        p.block_num    = self._orig.block_num
        p.drive_name   = name
        p.low_cyl      = lo
        p.high_cyl     = hi
        p.dos_type     = next(v for n, v in FS_MENU if n == self._fs_var.get())
        p.boot_pri     = bp
        p.flags        = 0 if self._bootable_var.get() else 2
        p.surfaces     = self._orig.surfaces
        p.blk_per_trk  = self._orig.blk_per_trk
        p.reserved     = self._orig.reserved
        p.prealloc     = self._orig.prealloc
        p.interleave   = self._orig.interleave
        p.num_buffer   = self._orig.num_buffer
        p.buf_mem_type = self._orig.buf_mem_type
        p.max_transfer = self._orig.max_transfer
        p.mask         = self._orig.mask
        p.boot_blocks  = self._orig.boot_blocks
        self.result = p
        self.destroy()


# ─── Main window ───────────────────────────────────────────────────────────────

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Amiga RDB Disk Partitioner")
        self.geometry("1020x700")
        self.minsize(800, 520)
        self._disks   = []
        self._cur_disk = None
        self._rdb: Optional[RDBInfo] = None
        self._drag: Optional[dict] = None   # {"start": cyl, "end": cyl}
        self._build_menu()
        self._build_ui()
        self.after(100, self._refresh_disks)

    # ── Menu ──────────────────────────────────────────────────────────────────
    def _build_menu(self):
        mb = tk.Menu(self)
        self.config(menu=mb)
        fm = tk.Menu(mb, tearoff=0)
        fm.add_command(label="Refresh Disks", command=self._refresh_disks, accelerator="F5")
        fm.add_separator()
        fm.add_command(label="Quit", command=self.quit)
        mb.add_cascade(label="File", menu=fm)
        hm = tk.Menu(mb, tearoff=0)
        hm.add_command(label="About", command=self._about)
        mb.add_cascade(label="Help", menu=hm)
        self.bind("<F5>", lambda _: self._refresh_disks())

    # ── UI layout ─────────────────────────────────────────────────────────────
    def _build_ui(self):
        style = ttk.Style(self)
        style.configure("Treeview", rowheight=34)
        style.configure("Treeview.Heading", font=("", 9, "bold"))
        style.map("Treeview",
                  background=[("selected", "#1a6aad")],
                  foreground=[("selected", "white")])

        pw = ttk.PanedWindow(self, orient="horizontal")
        pw.pack(fill="both", expand=True, padx=4, pady=4)

        # ── Left panel: disk list ────────────────────────────────────────────
        left = ttk.Frame(pw, width=230)
        pw.add(left, weight=0)

        ttk.Label(left, text="Physical Disks", font=("",10,"bold")).pack(
            anchor="w", padx=6, pady=(4,2))

        # Wrap tree + scrollbar together so the button can sit below both
        tree_frame = ttk.Frame(left)
        tree_frame.pack(fill="both", expand=True, padx=4, pady=(0,4))

        cols = ("device","size","model")
        self._dtree = ttk.Treeview(tree_frame, columns=cols, show="headings",
                                   selectmode="browse", height=26)
        self._dtree.heading("device", text="Device")
        self._dtree.heading("size",   text="Size")
        self._dtree.heading("model",  text="Model")
        self._dtree.column("device", width=70,  minwidth=60,  anchor="w")
        self._dtree.column("size",   width=80,  minwidth=60,  anchor="e")
        self._dtree.column("model",  width=110, minwidth=80,  anchor="w")
        sb = ttk.Scrollbar(tree_frame, orient="vertical", command=self._dtree.yview)
        self._dtree.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self._dtree.pack(side="left", fill="both", expand=True)
        self._dtree.bind("<<TreeviewSelect>>", self._on_disk_sel)

        ttk.Button(left, text="⟳  Refresh", command=self._refresh_disks).pack(
            fill="x", padx=4, pady=(0,4))

        # ── Right panel ──────────────────────────────────────────────────────
        right = ttk.Frame(pw)
        pw.add(right, weight=1)

        # Disk info
        info_lf = ttk.LabelFrame(right, text="Disk Information")
        info_lf.pack(fill="x", padx=4, pady=(4,2))

        self._info = {}
        # 2 fields per row: (Device, Model), (Size, Geometry), (RDB Status)
        pairs = [
            [("Device","device"), ("Model","model")],
            [("Size","size"),     ("Geometry","geo")],
            [("RDB Status","rdb", 3)],   # spans remaining columns
        ]
        for r, row_items in enumerate(pairs):
            c = 0
            for item in row_items:
                key  = item[1]
                lbl  = item[0]
                span = item[2] if len(item) > 2 else 1
                ttk.Label(info_lf, text=lbl+":", font=("",9,"bold")).grid(
                    row=r, column=c, sticky="e", padx=(8,2), pady=3)
                v = ttk.Label(info_lf, text="—", foreground="#666666")
                v.grid(row=r, column=c+1, sticky="w", padx=(0,16), pady=3,
                       columnspan=span)
                self._info[key] = v
                c += 2
        info_lf.columnconfigure(1, weight=1)
        info_lf.columnconfigure(3, weight=1)

        # Disk map canvas
        map_lf = ttk.LabelFrame(right, text="Disk Map")
        map_lf.pack(fill="x", padx=4, pady=2)

        self._canvas = tk.Canvas(map_lf, height=66, bg="#1a1a2e", highlightthickness=0)
        self._canvas.pack(fill="x", padx=6, pady=6)
        self._canvas.bind("<Configure>",       lambda _: self._draw_map())
        self._canvas.bind("<Motion>",          self._on_map_hover)
        self._canvas.bind("<Button-1>",        self._on_map_press)
        self._canvas.bind("<B1-Motion>",       self._on_map_drag)
        self._canvas.bind("<ButtonRelease-1>", self._on_map_release)
        self._canvas.bind("<Double-1>",        self._on_map_double_click)

        # Partition list
        part_lf = ttk.LabelFrame(right, text="Partitions")
        part_lf.pack(fill="both", expand=True, padx=4, pady=2)

        pcols = ("name","lo","hi","fs","size","pri","flags")
        self._ptree = ttk.Treeview(part_lf, columns=pcols, show="headings",
                                   selectmode="browse", height=8)
        heads = [("Drive",70),("Lo Cyl",72),("Hi Cyl",72),
                 ("Filesystem",135),("Size",88),("Boot Pri",72),("Flags",60)]
        for (h, w), c in zip(heads, pcols):
            self._ptree.heading(c, text=h)
            self._ptree.column(c, width=w, minwidth=w,
                               anchor="center" if c == "flags" else
                               "w"    if c in ("name","fs") else "e")
        psb = ttk.Scrollbar(part_lf, orient="vertical", command=self._ptree.yview)
        self._ptree.configure(yscrollcommand=psb.set)
        self._ptree.pack(side="left", fill="both", expand=True, padx=(6,0), pady=4)
        psb.pack(side="left", fill="y", pady=4, padx=(0,4))
        self._ptree.bind("<<TreeviewSelect>>", self._on_part_sel)
        self._ptree.bind("<Double-1>",         lambda _: self.after(0, self._do_edit))

        # Action buttons
        bf = ttk.Frame(right)
        bf.pack(fill="x", padx=4, pady=4)

        self._btn_init  = ttk.Button(bf, text="Initialize RDB",  command=self._do_init,
                                      state="disabled")
        self._btn_add   = ttk.Button(bf, text="Add Partition",    command=self._do_add,
                                      state="disabled")
        self._btn_edit  = ttk.Button(bf, text="Edit Partition",   command=self._do_edit,
                                      state="disabled")
        self._btn_del   = ttk.Button(bf, text="Delete Partition", command=self._do_del,
                                      state="disabled")
        self._btn_write = ttk.Button(bf, text="✔  Write to Disk", command=self._do_write,
                                      state="disabled")
        self._btn_init.pack(side="left", padx=2)
        self._btn_add.pack(side="left",  padx=2)
        self._btn_edit.pack(side="left", padx=2)
        self._btn_del.pack(side="left",  padx=2)
        self._btn_write.pack(side="right", padx=2)

        # Status bar
        self._status = tk.StringVar(value="Select a disk to begin.")
        ttk.Label(right, textvariable=self._status, relief="sunken",
                  anchor="w").pack(fill="x", padx=4, pady=(0,2))

    # ── Disk list ─────────────────────────────────────────────────────────────
    def _refresh_disks(self):
        self._disks = get_disks()
        for row in self._dtree.get_children():
            self._dtree.delete(row)
        for d in self._disks:
            self._dtree.insert("", "end", iid=d["path"],
                               values=(d["name"], fmt_size(d["size"]), d["model"]))
        if not self._disks:
            self._status.set("No disks found. Try running as root (sudo).")
        else:
            self._status.set(f"{len(self._disks)} disk(s) found. Select one.")

    def _on_disk_sel(self, _=None):
        sel = self._dtree.selection()
        if not sel:
            return
        self._cur_disk = next((d for d in self._disks if d["path"]==sel[0]), None)
        if not self._cur_disk:
            return
        dev = self._cur_disk["path"]
        self._status.set(f"Reading {dev}…")
        self.update_idletasks()

        self._rdb = read_rdb(dev)
        self._info["device"].config(text=dev, foreground="black")
        self._info["model"].config(text=self._cur_disk["model"] or "Unknown", foreground="black")
        self._info["size"].config(text=fmt_size(self._cur_disk["size"]), foreground="black")

        if self._rdb:
            geo = f"{self._rdb.cylinders}C × {self._rdb.heads}H × {self._rdb.sectors}S"
            self._info["geo"].config(text=geo, foreground="black")
            self._info["rdb"].config(
                text=f"RDB found (block {self._rdb.block_num})", foreground="#007700")
            self._btn_init.config(state="normal")
            self._btn_add.config(state="normal")
            self._btn_write.config(state="normal")
            self._status.set(
                f"{dev}: RDB found — {len(self._rdb.partitions)} partition(s)")
        else:
            self._info["geo"].config(text="No RDB", foreground="#888888")
            self._info["rdb"].config(text="No Amiga RDB found", foreground="#cc0000")
            self._btn_init.config(state="normal")
            self._btn_add.config(state="disabled")
            self._btn_write.config(state="disabled")
            self._status.set(f"{dev}: No RDB — use 'Initialize RDB' first.")

        self._btn_edit.config(state="disabled")
        self._btn_del.config(state="disabled")
        self._refresh_parts()
        self._draw_map()

    # ── Partition list ────────────────────────────────────────────────────────
    def _refresh_parts(self):
        # Remember current selection index so we can restore it
        cur = self._ptree.selection()
        prev_idx = int(cur[0]) if cur else None

        for row in self._ptree.get_children():
            self._ptree.delete(row)
        if not self._rdb:
            self._on_part_sel()
            return
        for i, p in enumerate(self._rdb.partitions):
            flags = "Boot" if p.flags == 0 else f"0x{p.flags:02X}"
            self._ptree.insert("", "end", iid=str(i),
                               values=(p.drive_name, p.low_cyl, p.high_cyl,
                                       p.fs_name, fmt_size(p.size_bytes),
                                       p.boot_pri, flags),
                               tags=(f"c{i%len(COLORS)}",))
        for i, c in enumerate(COLORS):
            r,g,b = int(c[1:3],16),int(c[3:5],16),int(c[5:7],16)
            bg = f"#{min(r+160,255):02x}{min(g+160,255):02x}{min(b+160,255):02x}"
            self._ptree.tag_configure(f"c{i}", background=bg)

        # Restore selection (or pick first row) so delete button stays correct
        kids = self._ptree.get_children()
        if kids:
            target = str(min(prev_idx, len(kids) - 1)) if prev_idx is not None else kids[0]
            self._ptree.selection_set(target)
            self._ptree.focus(target)
            self._ptree.see(target)
        self._on_part_sel()

    def _on_part_sel(self, _=None):
        has_sel = bool(self._ptree.selection())
        self._btn_edit.config(state="normal" if has_sel else "disabled")
        self._btn_del.config(state="normal"  if has_sel else "disabled")
        self._draw_map()

    # ── Disk map ──────────────────────────────────────────────────────────────
    def _draw_map(self):
        c = self._canvas
        c.delete("all")
        W = c.winfo_width()
        H = c.winfo_height()
        if W < 10:
            return

        M = 6       # margin
        y1, y2 = M, H - 18
        bw = W - 2*M

        if not self._rdb:
            c.create_rectangle(M, y1, W-M, y2, fill="#333355", outline="#555577")
            c.create_text(W//2, (y1+y2)//2, text="No RDB",
                          fill="#8888aa", font=("",10,"bold"))
            return

        total = self._rdb.hicyl - self._rdb.locyl + 1
        if total <= 0:
            return

        def x_of(cyl):
            t = max(0.0, min(1.0, (cyl - self._rdb.locyl) / total))
            return M + t * bw

        # Free space background
        c.create_rectangle(M, y1, W-M, y2, fill="#2a2a3a", outline="#444466")

        # RDB reserved area (before locyl)
        if self._rdb.locyl > 0:
            x2 = x_of(self._rdb.locyl)
            if x2 > M + 2:
                c.create_rectangle(M, y1, x2, y2, fill="#555566", outline="")
                if x2 - M > 30:
                    c.create_text((M+x2)/2, (y1+y2)/2,
                                  text="RDB", fill="#ccccdd", font=("",8))

        # Partitions
        for i, p in enumerate(self._rdb.partitions):
            px1 = x_of(p.low_cyl)
            px2 = x_of(p.high_cyl + 1)
            if px2 <= px1 + 1:
                px2 = px1 + 2
            col = COLORS[i % len(COLORS)]
            c.create_rectangle(px1, y1, px2, y2, fill=col, outline="#111122", width=1)
            pw = px2 - px1
            if pw > 18:
                max_chars = max(1, int((pw - 8) / 6))
                label = p.drive_name if len(p.drive_name) <= max_chars else p.drive_name[:max_chars]
                c.create_text((px1+px2)/2, (y1+y2)/2,
                              text=label, fill="white",
                              font=("",8,"bold"))

        # Highlight selected partition
        sel = self._ptree.selection()
        if sel:
            sel_idx = int(sel[0])
            if 0 <= sel_idx < len(self._rdb.partitions):
                sp = self._rdb.partitions[sel_idx]
                sx1 = x_of(sp.low_cyl)
                sx2 = x_of(sp.high_cyl + 1)
                if sx2 < sx1 + 2:
                    sx2 = sx1 + 2
                # Outer glow
                c.create_rectangle(sx1 - 2, y1 - 2, sx2 + 2, y2 + 2,
                                    fill="", outline="#ffffff", width=1)
                # Inner bright border
                c.create_rectangle(sx1, y1, sx2, y2,
                                    fill="", outline="white", width=3)

        # Ghost partition (drag-to-create)
        if self._drag is not None:
            lo = min(self._drag["start"], self._drag["end"])
            hi = max(self._drag["start"], self._drag["end"])
            gx1 = x_of(lo)
            gx2 = x_of(hi + 1)
            if gx2 < gx1 + 2:
                gx2 = gx1 + 2
            c.create_rectangle(gx1, y1, gx2, y2,
                                fill="#334466", outline="white", dash=(4, 2), width=2)
            gpw = gx2 - gx1
            if gpw > 28:
                cyls = hi - lo + 1
                sz_str = fmt_size(cyls * self._rdb.heads * self._rdb.sectors * 512)
                c.create_text((gx1 + gx2) / 2, (y1 + y2) / 2,
                               text=sz_str, fill="white", font=("", 8, "bold"))

        # Axis labels
        c.create_text(M,   H-2, text=f"Cyl {self._rdb.locyl}",
                      fill="#8888aa", font=("",7), anchor="sw")
        c.create_text(W-M, H-2, text=f"Cyl {self._rdb.hicyl}",
                      fill="#8888aa", font=("",7), anchor="se")

        # Legend: free space
        free_cyls = total
        for p in self._rdb.partitions:
            free_cyls -= (p.high_cyl - p.low_cyl + 1)
        free_mb = free_cyls * self._rdb.heads * self._rdb.sectors * 512
        c.create_text(W//2, H-2, text=f"Free: {fmt_size(free_mb)}",
                      fill="#8888aa", font=("",7), anchor="s")

    # ── Canvas drag-to-create ─────────────────────────────────────────────────
    def _map_x_to_cyl(self, x: int) -> int:
        M = 6
        bw = self._canvas.winfo_width() - 2 * M
        total = self._rdb.hicyl - self._rdb.locyl + 1
        if bw <= 0 or total <= 0:
            return self._rdb.locyl
        cyl = self._rdb.locyl + int((x - M) / bw * total)
        return max(self._rdb.locyl, min(self._rdb.hicyl, cyl))

    def _cyl_is_free(self, cyl: int) -> bool:
        for p in self._rdb.partitions:
            if p.low_cyl <= cyl <= p.high_cyl:
                return False
        return True

    def _on_map_hover(self, event):
        if not self._rdb:
            self._canvas.config(cursor=""); return
        H = self._canvas.winfo_height()
        if not (6 <= event.y <= H - 18):
            self._canvas.config(cursor=""); return
        self._canvas.config(
            cursor="crosshair" if self._cyl_is_free(self._map_x_to_cyl(event.x)) else "")

    def _on_map_press(self, event):
        if not self._rdb:
            return
        H = self._canvas.winfo_height()
        if not (6 <= event.y <= H - 18):
            return
        cyl = self._map_x_to_cyl(event.x)
        if not self._cyl_is_free(cyl):
            return
        # Snap start to the left edge of this free block
        snap = self._rdb.locyl
        for p in self._rdb.partitions:
            if p.high_cyl < cyl:
                snap = max(snap, p.high_cyl + 1)
        self._drag = {"start": snap, "end": snap}
        self._draw_map()

    def _clamp_drag_end(self, start: int, raw_end: int) -> int:
        """Clamp raw_end so the range [start, end] stays entirely in free space."""
        if raw_end >= start:
            limit = self._rdb.hicyl
            for p in self._rdb.partitions:
                if p.low_cyl > start:
                    limit = min(limit, p.low_cyl - 1)
            return min(raw_end, limit)
        else:
            limit = self._rdb.locyl
            for p in self._rdb.partitions:
                if p.high_cyl < start:
                    limit = max(limit, p.high_cyl + 1)
            return max(raw_end, limit)

    def _on_map_drag(self, event):
        if self._drag is None:
            return
        raw = self._map_x_to_cyl(event.x)
        self._drag["end"] = self._clamp_drag_end(self._drag["start"], raw)
        lo = min(self._drag["start"], self._drag["end"])
        hi = max(self._drag["start"], self._drag["end"])
        cyls = hi - lo + 1
        sz = cyls * self._rdb.heads * self._rdb.sectors * 512
        self._status.set(f"New partition: cyls {lo}–{hi}  ({cyls} cylinder{'s' if cyls != 1 else ''}, {fmt_size(sz)})")
        self._draw_map()

    def _on_map_double_click(self, event):
        if not self._rdb:
            return
        H = self._canvas.winfo_height()
        if not (6 <= event.y <= H - 18):
            return
        cyl = self._map_x_to_cyl(event.x)
        for i, p in enumerate(self._rdb.partitions):
            if p.low_cyl <= cyl <= p.high_cyl:
                self._ptree.selection_set(str(i))
                self._ptree.focus(str(i))
                self._ptree.see(str(i))
                self._do_edit()
                return

    def _on_map_release(self, event):
        if self._drag is None:
            return
        raw = self._map_x_to_cyl(event.x)
        clamped = self._clamp_drag_end(self._drag["start"], raw)
        lo = min(self._drag["start"], clamped)
        hi = max(self._drag["start"], clamped)
        self._drag = None
        self._draw_map()
        if not self._rdb:
            return
        dlg = AddPartitionDialog(self, self._rdb, preset_lo=lo, preset_hi=hi)
        if dlg.result:
            self._rdb.partitions.append(dlg.result)
            self._refresh_parts()
            self._draw_map()
            self._status.set(
                f"Partition '{dlg.result.drive_name}' added. Write to disk to save changes.")
        else:
            self._status.set("Partition add cancelled.")

    # ── Actions ───────────────────────────────────────────────────────────────
    def _do_init(self):
        if not self._cur_disk:
            return
        if self._rdb:
            if not messagebox.askyesno("Overwrite RDB",
                    "This disk already has an Amiga RDB.\n"
                    "Reinitializing will ERASE all partition information.\n\n"
                    "Continue?", icon="warning"):
                return
        dlg = InitRDBDialog(self, self._cur_disk)
        if not dlg.result:
            return
        self._rdb = dlg.result
        geo = f"{self._rdb.cylinders}C × {self._rdb.heads}H × {self._rdb.sectors}S"
        self._info["geo"].config(text=geo, foreground="black")
        self._info["rdb"].config(text="RDB initialized (not written yet)",
                                  foreground="#0055cc")
        self._btn_add.config(state="normal")
        self._btn_write.config(state="normal")
        self._refresh_parts()
        self._draw_map()
        self._status.set("RDB initialized. Add partitions, then write to disk.")

    def _do_add(self):
        if not self._rdb:
            return
        dlg = AddPartitionDialog(self, self._rdb)
        if not dlg.result:
            return
        self._rdb.partitions.append(dlg.result)
        self._refresh_parts()
        self._draw_map()
        self._status.set(
            f"Partition '{dlg.result.drive_name}' added. Write to disk to save changes.")

    def _do_edit(self):
        sel = self._ptree.selection()
        if not sel or not self._rdb:
            return
        idx = int(sel[0])
        dlg = EditPartitionDialog(self, self._rdb, idx)
        if dlg.result:
            self._rdb.partitions[idx] = dlg.result
            self._refresh_parts()
            self._draw_map()
            self._status.set(
                f"Partition '{dlg.result.drive_name}' updated. Write to disk to save changes.")

    def _do_del(self):
        sel = self._ptree.selection()
        if not sel or not self._rdb:
            return
        idx = int(sel[0])
        p = self._rdb.partitions[idx]
        if not messagebox.askyesno("Delete Partition",
                f"Remove partition '{p.drive_name}' (cyls {p.low_cyl}–{p.high_cyl})?\n\n"
                "Write to disk afterwards to make this permanent."):
            return
        self._rdb.partitions.pop(idx)
        self._btn_edit.config(state="disabled")
        self._btn_del.config(state="disabled")
        self._refresh_parts()
        self._draw_map()
        self._status.set(f"Partition '{p.drive_name}' removed. Write to disk to save.")

    def _do_write(self):
        if not self._cur_disk or not self._rdb:
            return
        dev = self._cur_disk["path"]
        n = len(self._rdb.partitions)

        msg = (
            f"⚠  WARNING  ⚠\n\n"
            f"This will OVERWRITE the partition table on:\n\n"
            f"  {dev}   ({fmt_size(self._cur_disk['size'])})\n"
            f"  {self._cur_disk['model'] or 'Unknown model'}\n\n"
            f"  {n} partition(s) will be written.\n\n"
            f"Existing data on this disk may be LOST.\n\n"
            f"Are you absolutely sure?"
        )
        if not messagebox.askyesno("Confirm Write to Disk", msg, icon="warning"):
            return

        if not os.access(dev, os.W_OK):
            messagebox.showerror("Permission Denied",
                f"Cannot write to {dev}.\n\nRun this program with sudo.")
            return

        rdb = self._rdb
        n_parts = len(rdb.partitions)

        # Block layout: RDSK at 0, PART at 1, 2, 3, …
        rdsk_blk   = 0
        part_blks  = list(range(1, 1 + n_parts))
        rdb.rdbblock_hi  = max(15, n_parts + 1)
        rdb.part_list_blk = part_blks[0] if part_blks else END_MARK

        errors = []

        if not _write_block(dev, rdsk_blk, build_rdsk_block(rdb)):
            errors.append(f"Failed to write RDSK block at block {rdsk_blk}")

        for i, (p, blk) in enumerate(zip(rdb.partitions, part_blks)):
            p.block_num = blk
            p.next_part = part_blks[i+1] if i+1 < n_parts else END_MARK
            if not _write_block(dev, blk, build_part_block(p, rdb.heads, rdb.sectors)):
                errors.append(f"Failed to write PART block for {p.drive_name}")

        if errors:
            messagebox.showerror("Write Errors", "\n".join(errors))
        else:
            part_info = ", ".join(str(b) for b in part_blks) or "none"
            messagebox.showinfo("Success",
                f"Amiga RDB written to {dev}!\n\n"
                f"  RDSK block: {rdsk_blk}\n"
                f"  PART block(s): {part_info}\n\n"
                f"Use HDInstTools or HDToolBox on the Amiga to format.")
            self._info["rdb"].config(
                text=f"RDB written to disk ({n_parts} partition(s))",
                foreground="#007700")
            self._status.set(f"RDB successfully written to {dev}.")

    def _about(self):
        messagebox.showinfo("About AmigaDisk",
            "AmigaDisk  —  Amiga RDB Partition Tool\n\n"
            "Creates and manages Amiga Rigid Disk Block (RDB)\n"
            "partition tables on physical drives or disk images\n"
            "for use with real Amiga hardware or emulators.\n\n"
            "Supported filesystems:\n"
            "  OFS, FFS, FFS+Intl, FFS+DC+Intl, SFS\n\n"
            "Run with sudo to write to physical drives.\n\n"
            "RDB spec: Amiga NDK 3.9 / RDB v1.0")


# ─── Entry point ───────────────────────────────────────────────────────────────

if __name__ == "__main__":
    if os.geteuid() != 0:
        print("Warning: not running as root — disk writes will likely fail.")
        print("Tip: sudo python3 amigadisk.py")
    App().mainloop()
