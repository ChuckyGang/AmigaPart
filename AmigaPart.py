#!/usr/bin/env python3
"""AmigaDisk — GUI tool for Amiga RDB (Rigid Disk Block) partitioning."""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import subprocess, struct, os, math, json, re, threading, queue, signal, sys
from typing import List, Optional

_IS_MACOS = sys.platform == "darwin"

# ─── Constants ─────────────────────────────────────────────────────────────────
RDSK_ID      = 0x5244534B   # "RDSK"
PART_ID      = 0x50415254   # "PART"
FSHD_ID      = 0x46534844   # "FSHD"
LSEG_ID      = 0x4C534547   # "LSEG"
END_MARK     = 0xFFFFFFFF
RDB_SCAN_LIMIT = 16
LSEG_DATA    = 492          # payload bytes per LSEG block (512 − 5 longs)

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

# BufMemType options: (display label, numeric value)
# Values are Exec AllocMem() flags used when allocating filesystem buffers.
BUFMEMTYPE_OPTS = [
    ("Any (0)",       0),
    ("Public (1)",    1),
    ("Chip RAM (2)",  2),
    ("Fast RAM (4)",  4),
]

# SizeBlock: filesystem block size in longwords (bytes / 4)
SIZEBLOCK_OPTS = [
    ("512 B",   128),
    ("1 KB",    256),
    ("2 KB",    512),
    ("4 KB",   1024),
    ("8 KB",   2048),
    ("16 KB",  4096),
    ("32 KB",  8192),
]


# ─── Data classes ──────────────────────────────────────────────────────────────

class PartitionInfo:
    def __init__(self):
        self.block_num    = -1
        self.next_part    = END_MARK
        self.flags        = 0          # 0 = bootable/normal
        self.drive_name   = "DH0"
        self.low_cyl      = 0
        self.high_cyl     = 0
        self.size_block   = 128        # filesystem block size in longwords (128 = 512 B)
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
        return _dostype_label(self.dos_type)


def _rdb_fs_menu(rdb) -> list:
    """Return FS_MENU extended with any custom filesystems stored in this RDB."""
    known = {v for _, v in FS_MENU}
    extra = [(f"{fs.label} — External", fs.dos_type)
             for fs in (rdb.filesystems if rdb else [])
             if fs.dos_type not in known]
    return FS_MENU + extra


def _dostype_label(dos_type: int) -> str:
    """Return a human-readable label for an arbitrary DosType, e.g. 0x50465303 → 'PFS\\3'."""
    known = FS_TYPES.get(dos_type)
    if known:
        return known
    chars = []
    for i in range(3):
        b = (dos_type >> (24 - i * 8)) & 0xFF
        chars.append(chr(b) if 32 <= b < 127 else '?')
    ver = dos_type & 0xFF
    return f"{''.join(chars)}\\{ver}"


class FilesystemInfo:
    def __init__(self):
        self.block_num    = -1
        self.dos_type     = 0
        self.version      = 0        # hi word = major, lo word = minor
        self.patch_flags  = 0x180    # SegListBlk + GlobalVec valid
        self.stack_size   = 4096
        self.priority     = 0
        self.startup      = 0
        self.global_vec   = 0xFFFFFFFF
        self.data         = b""      # raw filesystem binary (LSEG payload)

    @property
    def label(self) -> str:
        return _dostype_label(self.dos_type)

    @property
    def version_str(self) -> str:
        major = (self.version >> 16) & 0xFFFF
        minor = self.version & 0xFFFF
        return f"{major}.{minor}"


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
        self.partitions:  List[PartitionInfo]  = []
        self.filesystems: List[FilesystemInfo] = []


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


def _has_pc_partitioning(dev: str) -> bool:
    """Return True if the disk has a PC-style MBR signature (0x55AA at offset 510)."""
    data = _read_block(dev, 0)
    if data is None or len(data) < 512:
        return False
    return data[510] == 0x55 and data[511] == 0xAA


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


# ─── Partition Move / Grow ─────────────────────────────────────────────────────

_MOVE_CHUNK = 128   # sectors per read/write pass (64 KB)

# ── SFS helpers ────────────────────────────────────────────────────────────────

def _sfs_is_type(dos_type: int) -> bool:
    return (dos_type & 0xFFFFFF00) == 0x53465300

def _sfs_verify_chk(data: bytes, block_size: int) -> bool:
    """SFS CALCCHECKSUM: acc=1 + sum all ULONGs; block is valid when result == 0."""
    acc = 1
    for i in range(0, block_size, 4):
        acc = (acc + struct.unpack_from(">I", data, i)[0]) & 0xFFFFFFFF
    return acc == 0

def _sfs_fix_chk(buf: bytearray, block_size: int):
    """Set SFS checksum (byte offset 4) so the block passes _sfs_verify_chk."""
    struct.pack_into(">I", buf, 4, 0)
    acc = 1
    for i in range(0, block_size, 4):
        acc = (acc + struct.unpack_from(">I", buf, i)[0]) & 0xFFFFFFFF
    struct.pack_into(">I", buf, 4, (-acc) & 0xFFFFFFFF)

# ── FFS helpers ────────────────────────────────────────────────────────────────

def _ffs_is_type(dos_type: int) -> bool:
    return (dos_type & 0xFFFFFF00) == 0x444F5300 and (dos_type & 0xFF) <= 7

def _ffs_checksum(buf: bytes, nlongs: int) -> int:
    """FFS block checksum value: -(sum of all longs) & 0xFFFFFFFF."""
    s = 0
    for i in range(nlongs):
        s = (s + struct.unpack_from(">I", buf, i * 4)[0]) & 0xFFFFFFFF
    return (-s) & 0xFFFFFFFF

def _bm_setfree(buf: bytearray, off: int):
    """Mark FFS bitmap bit 'off' as free (1)."""
    idx = (1 + off // 32) * 4
    v = struct.unpack_from(">I", buf, idx)[0]
    struct.pack_into(">I", buf, idx, v | (1 << (31 - off % 32)))

def _bm_setused(buf: bytearray, off: int):
    """Mark FFS bitmap bit 'off' as used (0)."""
    idx = (1 + off // 32) * 4
    v = struct.unpack_from(">I", buf, idx)[0]
    struct.pack_into(">I", buf, idx, v & ~(1 << (31 - off % 32)) & 0xFFFFFFFF)

# ── PFS helpers ────────────────────────────────────────────────────────────────

def _pfs_is_type(dos_type: int) -> bool:
    prefix = dos_type >> 8
    ver    = dos_type & 0xFF
    return prefix in (0x504653, 0x504453) and ver <= 3

# ── Move validation ─────────────────────────────────────────────────────────────

def _part_can_move(rdb, pi, new_lo: int):
    """Returns (True, new_hi) or (False, err_str)."""
    if pi.high_cyl < pi.low_cyl:
        return False, f"Invalid cylinder range ({pi.low_cyl}–{pi.high_cyl})."
    cyl_count = pi.high_cyl - pi.low_cyl + 1
    new_hi    = new_lo + cyl_count - 1
    if new_lo == pi.low_cyl:
        return False, f"Partition is already at cylinder {new_lo}."
    if new_lo < rdb.locyl:
        return False, f"Start cylinder {new_lo} is below the first usable cylinder ({rdb.locyl})."
    if new_hi > rdb.hicyl:
        return False, f"End cylinder {new_hi} exceeds the disk limit ({rdb.hicyl})."
    for other in rdb.partitions:
        if other is pi:
            continue
        if new_lo <= other.high_cyl and new_hi >= other.low_cyl:
            return False, (f"New position (cyl {new_lo}–{new_hi}) overlaps "
                           f"partition {other.drive_name} (cyl {other.low_cyl}–{other.high_cyl}).")
    return True, new_hi

# ── Move data ──────────────────────────────────────────────────────────────────

_DD_CHUNK = 2048   # sectors per dd invocation (~1 MB)

def _part_move_data(dev: str, rdb, pi, new_lo: int,
                    progress_cb=None, use_dd: bool = False) -> tuple:
    """Copy all partition blocks from pi's current location to new_lo.
    Returns (True, msg) or (False, err_str).
    Direction-safe: front-to-back when moving lower, back-to-front when moving higher.
    SFS firstbyte/lastbyte metadata is updated in both root copies after the copy.
    Does NOT update pi or write the RDB — caller must do that on success."""

    heads    = pi.surfaces    or rdb.heads
    sectors  = pi.blk_per_trk or rdb.sectors
    if not heads or not sectors:
        return False, f"Invalid geometry (heads={heads}, sectors={sectors})."

    cyl_count  = pi.high_cyl - pi.low_cyl + 1
    new_hi     = new_lo + cyl_count - 1
    phys_old   = pi.low_cyl * heads * sectors
    phys_new   = new_lo     * heads * sectors
    phys_total = cyl_count  * heads * sectors

    def prog(done, total, phase):
        if progress_cb:
            progress_cb(done, total, phase)

    prog(0, phys_total, "Copying blocks...")
    done = 0

    if use_dd:
        # Overlapping-higher: source and destination overlap AND dest > src.
        # Must copy back-to-front. All other cases: single dd is safe.
        overlapping_higher = (phys_new > phys_old) and (phys_new < phys_old + phys_total)

        # Use byte-based skip/seek/count (GNU dd iflag/oflag) so dd can use
        # large 1 MB blocks internally regardless of sector size.
        def dd_copy(src_sec, dst_sec, sec_count):
            subprocess.run(
                ["dd", f"if={dev}", f"of={dev}", "bs=1M",
                 f"skip={src_sec * 512}", f"seek={dst_sec * 512}",
                 f"count={sec_count * 512}",
                 "iflag=skip_bytes,count_bytes", "oflag=seek_bytes",
                 "conv=notrunc"],
                check=True, capture_output=True)

        if not overlapping_higher:
            # One dd call for the whole partition — fastest path.
            prog(0, phys_total, "Copying blocks (dd)...")
            try:
                dd_copy(phys_old, phys_new, phys_total)
            except subprocess.CalledProcessError as e:
                return False, ("dd failed: "
                               f"{e.stderr.decode(errors='replace').strip()}")
            prog(phys_total, phys_total, "Copying blocks (dd)...")
        else:
            # Overlapping higher: reverse with 128 MB chunks.
            chunk_sz = 262144  # 128 MB in 512-byte sectors
            i = phys_total
            while i > 0:
                cnt = min(chunk_sz, i)
                i  -= cnt
                try:
                    dd_copy(phys_old + i, phys_new + i, cnt)
                except subprocess.CalledProcessError as e:
                    return False, (f"dd error at block {phys_old + i}: "
                                   f"{e.stderr.decode(errors='replace').strip()}")
                done += cnt
                prog(done, phys_total, "Copying blocks (dd)...")
    else:
        def read_secs(start, count):
            try:
                with open(dev, "rb") as f:
                    f.seek(start * 512)
                    data = f.read(count * 512)
                return data if len(data) == count * 512 else None
            except OSError:
                return None

        def write_secs(start, data):
            try:
                with open(dev, "r+b") as f:
                    f.seek(start * 512)
                    f.write(data)
                    f.flush()
                    os.fsync(f.fileno())
                return True
            except OSError:
                return False

        if phys_new < phys_old:
            # Moving to lower address: copy front-to-back (destination precedes source)
            i = 0
            while i < phys_total:
                chunk = min(_MOVE_CHUNK, phys_total - i)
                buf = read_secs(phys_old + i, chunk)
                if buf is None:
                    return False, f"Read error at block {phys_old + i} (after {done} blocks copied)."
                if not write_secs(phys_new + i, buf):
                    return False, f"Write error at block {phys_new + i} (after {done} blocks copied)."
                done += chunk
                i += chunk
                prog(done, phys_total, "Copying blocks...")
        else:
            # Moving to higher address: copy back-to-front (destination follows source)
            i = phys_total
            while i > 0:
                chunk = min(_MOVE_CHUNK, i)
                i -= chunk
                buf = read_secs(phys_old + i, chunk)
                if buf is None:
                    return False, f"Read error at block {phys_old + i} (after {done} blocks copied)."
                if not write_secs(phys_new + i, buf):
                    return False, f"Write error at block {phys_new + i} (after {done} blocks copied)."
                done += chunk
                prog(done, phys_total, "Copying blocks...")

    prog(phys_total, phys_total, "Copying blocks...")

    ok, sfs_msg = _sfs_fixup_after_move(dev, rdb, pi, new_lo)
    if not ok:
        return False, sfs_msg

    msg = (f"Moved {cyl_count} cylinders of data.\n"
           f"cyl {pi.low_cyl}–{pi.high_cyl}  →  {new_lo}–{new_hi}\n"
           f"phys blocks: {phys_old} → {phys_new} ({phys_total} blocks)")
    return True, msg


def _sfs_fixup_after_move(dev: str, rdb, pi, new_lo: int) -> tuple:
    """Update SFS firstbyte/lastbyte in both root copies after a partition move.
    Returns (True, "") on success or if not an SFS partition, (False, err) on failure."""
    if not _sfs_is_type(pi.dos_type):
        return True, ""

    _SFS_ROOT_ID    = 0x53465300
    _OFF_BLOCKSIZE  = 52
    _OFF_FIRSTBYTEH = 32
    _OFF_FIRSTBYTE  = 36
    _OFF_LASTBYTEH  = 40
    _OFF_LASTBYTE   = 44
    _OFF_TOTALBLKS  = 48

    heads    = pi.surfaces    or rdb.heads
    sectors  = pi.blk_per_trk or rdb.sectors
    phys_new = new_lo * heads * sectors

    scratch = _read_block(dev, phys_new)
    if scratch is None:
        return False, "SFS: cannot read new root block 0."
    if struct.unpack_from(">I", scratch, 0)[0] != _SFS_ROOT_ID:
        return False, ("SFS: root ID mismatch after copy — "
                       "metadata not updated.  Run SFScheck after reboot.")
    sfs_bs = struct.unpack_from(">I", scratch, _OFF_BLOCKSIZE)[0]
    if sfs_bs < 512 or (sfs_bs & (sfs_bs - 1)) or sfs_bs % 512:
        return False, f"SFS: invalid blocksize {sfs_bs}."
    sfs_phys = sfs_bs // 512

    def read_sfs_rb(sfs_blk):
        out = bytearray()
        base = phys_new + sfs_blk * sfs_phys
        for k in range(sfs_phys):
            b = _read_block(dev, base + k)
            if b is None:
                return None
            out.extend(b)
        return out

    def write_sfs_rb(sfs_blk, buf):
        base = phys_new + sfs_blk * sfs_phys
        for k in range(sfs_phys):
            if not _write_block(dev, base + k, bytes(buf[k * 512:(k + 1) * 512])):
                return False
        return True

    rb0 = read_sfs_rb(0)
    if rb0 is None or not _sfs_verify_chk(bytes(rb0), sfs_bs):
        return False, "SFS: root block 0 read/checksum error after copy."

    totalblks = struct.unpack_from(">I", rb0, _OFF_TOTALBLKS)[0]
    old_fb = ((struct.unpack_from(">I", rb0, _OFF_FIRSTBYTEH)[0] << 32) |
               struct.unpack_from(">I", rb0, _OFF_FIRSTBYTE)[0])
    old_lb = ((struct.unpack_from(">I", rb0, _OFF_LASTBYTEH)[0] << 32) |
               struct.unpack_from(">I", rb0, _OFF_LASTBYTE)[0])
    new_fb = phys_new * 512
    new_lb = new_fb + (old_lb - old_fb)

    for sfs_blk in (0, totalblks - 1):
        rb = read_sfs_rb(sfs_blk)
        if rb is None:
            continue
        if not _sfs_verify_chk(bytes(rb), sfs_bs):
            continue
        if struct.unpack_from(">I", rb, 0)[0] != _SFS_ROOT_ID:
            continue
        struct.pack_into(">I", rb, _OFF_FIRSTBYTEH, (new_fb >> 32) & 0xFFFFFFFF)
        struct.pack_into(">I", rb, _OFF_FIRSTBYTE,   new_fb         & 0xFFFFFFFF)
        struct.pack_into(">I", rb, _OFF_LASTBYTEH,  (new_lb >> 32) & 0xFFFFFFFF)
        struct.pack_into(">I", rb, _OFF_LASTBYTE,    new_lb         & 0xFFFFFFFF)
        _sfs_fix_chk(rb, sfs_bs)
        if not write_sfs_rb(sfs_blk, rb) and sfs_blk == 0:
            return False, ("SFS: failed to write primary root block after move.\n"
                           "Data was copied but location metadata not updated.\n"
                           "Run SFScheck after reboot.")
    return True, ""

# ── Grow validation ─────────────────────────────────────────────────────────────

def _part_can_grow(rdb, pi, new_hi: int):
    """Returns (True,) or (False, err_str)."""
    if new_hi <= pi.high_cyl:
        return False, f"New high cylinder {new_hi} must be greater than current ({pi.high_cyl})."
    if new_hi > rdb.hicyl:
        return False, f"New high cylinder {new_hi} exceeds the disk limit ({rdb.hicyl})."
    for other in rdb.partitions:
        if other is pi:
            continue
        if pi.low_cyl <= other.high_cyl and new_hi >= other.low_cyl:
            return False, (f"Extended range (cyl {pi.low_cyl}–{new_hi}) overlaps "
                           f"partition {other.drive_name} "
                           f"(cyl {other.low_cyl}–{other.high_cyl}).")
    return (True,)

# ── FFS filesystem grow ─────────────────────────────────────────────────────────

_FFS_ROOT_BM_MAX   = 25
_FFS_EXT_BM_MAX    = 127
_FFS_MAX_EXT_CHAIN = 32
_FFS_RL_CHKSUM     = 5
_FFS_RL_BM_FLAG    = 78
_FFS_RL_BM_PAGES   = 79   # root_buf[79..103] = 25 bitmap block pointers
_FFS_RL_BM_EXT     = 104
_FFS_T_SHORT       = 2
_FFS_ST_ROOT       = 1
_FFS_BM_VALID      = 0xFFFFFFFF


def _ffs_grow(dev: str, rdb, pi, old_hi: int, progress_cb=None) -> tuple:
    """Grow an FFS/OFS filesystem to match pi.high_cyl (already updated).
    Ports DiskPart ffsresize.c algorithm faithfully.
    Returns (True, msg) or (False, err_str)."""

    heads   = pi.surfaces    or rdb.heads
    sectors = pi.blk_per_trk or rdb.sectors
    nlongs  = 128   # 512 bytes / 4
    eff_bsz = 512

    if not heads or not sectors:
        return False, f"Invalid geometry (heads={heads}, sectors={sectors})."

    part_abs   = pi.low_cyl  * heads * sectors
    old_blocks = (old_hi      - pi.low_cyl + 1) * heads * sectors
    new_blocks = (pi.high_cyl - pi.low_cyl + 1) * heads * sectors
    reserved   = pi.reserved if pi.reserved > 0 else 2
    bpbm       = (nlongs - 1) * 32   # 127 * 32 = 4064 blocks per bitmap block

    def prog(msg):
        if progress_cb:
            progress_cb(msg)

    def read_blk(abs_blk):
        d = _read_block(dev, abs_blk)
        return bytearray(d) if d else None

    def write_blk(abs_blk, buf):
        return _write_block(dev, abs_blk, bytes(buf) if isinstance(buf, bytearray) else buf)

    if old_blocks <= reserved or new_blocks <= reserved:
        return False, (f"Partition too small (old_blocks={old_blocks}, "
                       f"new_blocks={new_blocks}, reserved={reserved}).")

    # FFS BitmapCount formula (from init.asm):
    # BitmapCount = (bpbm - 2 + HighestBlock - reserved) / bpbm
    old_bm_need = (bpbm - 2 + old_blocks - reserved) // bpbm
    new_bm_need = (bpbm - 2 + new_blocks - reserved) // bpbm
    num_new_bm  = new_bm_need - old_bm_need

    # Phase 1: read + validate boot block
    prog("Reading boot block...")
    boot_buf = read_blk(part_abs)
    if not boot_buf:
        return False, f"Cannot read boot block (abs {part_abs})."
    if (struct.unpack_from(">I", boot_buf, 0)[0] & 0xFFFFFF00) != 0x444F5300:
        return False, "Boot block DosType mismatch."
    root_blk_stored = struct.unpack_from(">I", boot_buf, 8)[0]   # L[2] = bb[2]
    root_blk = root_blk_stored
    if root_blk == 0 or root_blk >= old_blocks:
        root_blk = old_blocks // 2

    # Phase 2: read + validate root block
    prog("Reading root block...")
    root_buf = read_blk(part_abs + root_blk)
    if not root_buf:
        return False, f"Cannot read root block (abs {part_abs + root_blk}, rel {root_blk})."
    if (struct.unpack_from(">I", root_buf, 0)[0] != _FFS_T_SHORT or
            struct.unpack_from(">I", root_buf, (nlongs - 1) * 4)[0] != _FFS_ST_ROOT):
        return False, (f"Root block wrong type/sec_type "
                       f"({struct.unpack_from('>I', root_buf, 0)[0]:#010x}/"
                       f"{struct.unpack_from('>I', root_buf, (nlongs-1)*4)[0]:#010x}).")
    save_cs = struct.unpack_from(">I", root_buf, _FFS_RL_CHKSUM * 4)[0]
    struct.pack_into(">I", root_buf, _FFS_RL_CHKSUM * 4, 0)
    calc_cs = _ffs_checksum(bytes(root_buf), nlongs)
    struct.pack_into(">I", root_buf, _FFS_RL_CHKSUM * 4, save_cs)
    if calc_cs != save_cs:
        return False, f"Root block checksum invalid (stored {save_cs:#010x}, calc {calc_cs:#010x})."
    if struct.unpack_from(">I", root_buf, _FFS_RL_BM_FLAG * 4)[0] != _FFS_BM_VALID:
        return False, "Bitmap not valid in root block (filesystem may need DiskSalv)."

    # Phase 3: collect existing bitmap block numbers from root + ext chain
    prog("Reading bitmap chain...")
    bm_blknums = []
    ext_chain  = []   # list of (relblk, used_count)

    for i in range(_FFS_ROOT_BM_MAX):
        v = struct.unpack_from(">I", root_buf, (_FFS_RL_BM_PAGES + i) * 4)[0]
        if v == 0:
            break
        bm_blknums.append(v)

    ext_blk = struct.unpack_from(">I", root_buf, _FFS_RL_BM_EXT * 4)[0]
    while ext_blk != 0 and len(ext_chain) < _FFS_MAX_EXT_CHAIN:
        eb = read_blk(part_abs + ext_blk)
        if not eb:
            break
        used = 0
        for i in range(_FFS_EXT_BM_MAX):
            v = struct.unpack_from(">I", eb, i * 4)[0]
            if v == 0:
                break
            used += 1
            bm_blknums.append(v)
        ext_chain.append((ext_blk, used))
        ext_blk = struct.unpack_from(">I", eb, (nlongs - 1) * 4)[0]

    if len(bm_blknums) < old_bm_need:
        return False, (f"Bitmap chain has {len(bm_blknums)} blocks, "
                       f"expected at least {old_bm_need}.")

    # Phase 4: check available chain capacity for new bm pointers
    root_free     = max(0, _FFS_ROOT_BM_MAX - len(bm_blknums))
    last_ext_free = (_FFS_EXT_BM_MAX - ext_chain[-1][1]) if ext_chain else 0
    avail_slots   = root_free + last_ext_free

    new_ext_relblks = []
    if num_new_bm > avail_slots:
        overflow    = num_new_bm - avail_slots
        num_new_ext = (overflow + _FFS_EXT_BM_MAX - 1) // _FFS_EXT_BM_MAX
        if num_new_ext > _FFS_MAX_EXT_CHAIN:
            return False, (f"Grow requires {num_new_ext} new ext blocks "
                           f"(max {_FFS_MAX_EXT_CHAIN}).")
        for ei in range(num_new_ext):
            pos = reserved + (new_bm_need - 1) * bpbm + 1 + ei
            if pos >= new_blocks:
                return False, f"No room in new partition space for ext block {ei}."
            new_ext_relblks.append(pos)

    # Phase 5: update last existing bitmap block to cover newly-available blocks
    prog("Extending last bitmap block...")
    if old_bm_need > 0:
        bm_idx    = old_bm_need - 1
        range_end = reserved + old_bm_need * bpbm
        free_end  = min(range_end, new_blocks)
        if old_blocks < free_end:
            bm_buf = read_blk(part_abs + bm_blknums[bm_idx])
            if not bm_buf:
                return False, f"Cannot read last bm block {bm_blknums[bm_idx]}."
            for b in range(old_blocks, free_end):
                _bm_setfree(bm_buf, b - reserved - bm_idx * bpbm)
            struct.pack_into(">I", bm_buf, 0, 0)
            struct.pack_into(">I", bm_buf, 0, _ffs_checksum(bytes(bm_buf), nlongs))
            if not write_blk(part_abs + bm_blknums[bm_idx], bm_buf):
                return False, f"Failed to write updated bm block {bm_blknums[bm_idx]}."

    # Phase 6: create new bitmap blocks for the extended range
    prog("Writing new bitmap blocks...")
    for k in range(num_new_bm):
        bm_idx  = old_bm_need + k
        abs_blk = reserved + bm_idx * bpbm
        b_start = reserved + bm_idx * bpbm
        b_end   = min(reserved + (bm_idx + 1) * bpbm, new_blocks)
        bm_blknums.append(abs_blk)

        bm_buf = bytearray(eff_bsz)
        for b in range(b_start, b_end):
            _bm_setfree(bm_buf, b - b_start)
        _bm_setused(bm_buf, 0)   # the bm block itself is at abs_blk = b_start
        for ep in new_ext_relblks:
            if b_start <= ep < b_end:
                _bm_setused(bm_buf, ep - b_start)
        struct.pack_into(">I", bm_buf, 0, 0)
        struct.pack_into(">I", bm_buf, 0, _ffs_checksum(bytes(bm_buf), nlongs))
        if not write_blk(part_abs + abs_blk, bm_buf):
            return False, f"Failed to write new bm block {abs_blk} (abs {part_abs + abs_blk})."

    # Phase 7: add new bm block numbers to the pointer chain
    prog("Updating bitmap chain in root...")
    src_idx = old_bm_need
    added   = 0

    i = old_bm_need
    while i < _FFS_ROOT_BM_MAX and added < num_new_bm:
        struct.pack_into(">I", root_buf, (_FFS_RL_BM_PAGES + i) * 4, bm_blknums[src_idx])
        i += 1; added += 1; src_idx += 1

    if added < num_new_bm and ext_chain:
        last_ext_blk, last_ext_used = ext_chain[-1]
        eb = read_blk(part_abs + last_ext_blk)
        if not eb:
            return False, f"Cannot re-read last ext block {last_ext_blk}."
        slot = last_ext_used
        while slot < _FFS_EXT_BM_MAX and added < num_new_bm:
            struct.pack_into(">I", eb, slot * 4, bm_blknums[src_idx])
            slot += 1; added += 1; src_idx += 1
        struct.pack_into(">I", eb, (nlongs - 1) * 4,
                         new_ext_relblks[0] if new_ext_relblks else 0)
        if not write_blk(part_abs + last_ext_blk, eb):
            return False, f"Failed to write updated ext block {last_ext_blk}."

    for ei, ep in enumerate(new_ext_relblks):
        eb   = bytearray(eff_bsz)
        slot = 0
        while slot < _FFS_EXT_BM_MAX and added < num_new_bm:
            struct.pack_into(">I", eb, slot * 4, bm_blknums[src_idx])
            slot += 1; added += 1; src_idx += 1
        next_ep = new_ext_relblks[ei + 1] if ei + 1 < len(new_ext_relblks) else 0
        struct.pack_into(">I", eb, (nlongs - 1) * 4, next_ep)
        if not write_blk(part_abs + ep, eb):
            return False, f"Failed to write new ext block {ep} (abs {part_abs + ep})."

    if new_ext_relblks and not ext_chain:
        struct.pack_into(">I", root_buf, _FFS_RL_BM_EXT * 4, new_ext_relblks[0])
    elif not new_ext_relblks and not ext_chain:
        struct.pack_into(">I", root_buf, _FFS_RL_BM_EXT * 4, 0)

    # Phase 8: relocate root block to (reserved + new_blocks - 1) / 2
    prog("Relocating root block...")
    new_root  = (reserved + new_blocks - 1) // 2
    if new_root < reserved:
        return False, f"new_root {new_root} < reserved {reserved} — impossible geometry."

    bm_idx_nr = (new_root  - reserved) // bpbm
    bm_idx_or = ((root_blk - reserved) // bpbm) if root_blk >= reserved else 0

    if bm_idx_nr >= len(bm_blknums):
        return False, (f"new_root bm index {bm_idx_nr} out of range "
                       f"(bm_count={len(bm_blknums)}).")

    nr_bm_buf = read_blk(part_abs + bm_blknums[bm_idx_nr])
    if not nr_bm_buf:
        return False, "Cannot read bm block for root relocation."
    off_nr = (new_root - reserved) % bpbm
    _bm_setused(nr_bm_buf, off_nr)
    if new_root != root_blk and bm_idx_or == bm_idx_nr and root_blk >= reserved:
        _bm_setfree(nr_bm_buf, (root_blk - reserved) % bpbm)
    struct.pack_into(">I", nr_bm_buf, 0, 0)
    struct.pack_into(">I", nr_bm_buf, 0, _ffs_checksum(bytes(nr_bm_buf), nlongs))
    if not write_blk(part_abs + bm_blknums[bm_idx_nr], nr_bm_buf):
        return False, "Failed to write bm block for root relocation."

    if new_root != root_blk and bm_idx_or != bm_idx_nr and root_blk >= reserved:
        if bm_idx_or < len(bm_blknums):
            or_bm_buf = read_blk(part_abs + bm_blknums[bm_idx_or])
            if or_bm_buf:
                _bm_setfree(or_bm_buf, (root_blk - reserved) % bpbm)
                struct.pack_into(">I", or_bm_buf, 0, 0)
                struct.pack_into(">I", or_bm_buf, 0, _ffs_checksum(bytes(or_bm_buf), nlongs))
                write_blk(part_abs + bm_blknums[bm_idx_or], or_bm_buf)

    # Write root at new position; clear fields FFS validates; bm_flag=0 → FFS rebuilds
    struct.pack_into(">I", root_buf,   4,   0)    # rb_OwnKey  = 0
    struct.pack_into(">I", root_buf,   8,   0)    # rb_SeqNum  = 0
    struct.pack_into(">I", root_buf,  12,  72)    # rb_HTSize  = 72
    struct.pack_into(">I", root_buf,  16,   0)    # rb_Nothing1 = 0
    struct.pack_into(">I", root_buf, 500,   0)    # rb_Parent  = 0  (L[125])
    struct.pack_into(">I", root_buf, _FFS_RL_BM_FLAG * 4, 0)
    struct.pack_into(">I", root_buf, _FFS_RL_CHKSUM  * 4, 0)
    struct.pack_into(">I", root_buf, _FFS_RL_CHKSUM  * 4, _ffs_checksum(bytes(root_buf), nlongs))
    if not write_blk(part_abs + new_root, root_buf):
        return False, f"Failed to write root at new position {new_root} (abs {part_abs + new_root})."

    # Phase 9b: update fhb_Parent in root's direct children (hash table entries)
    prog("Updating file/directory parent pointers...")
    FHB_PARENT    = nlongs - 3   # L[125] = vfhb_Parent
    FHB_HASHCHAIN = nlongs - 4   # L[124] = vfhb_HashChain
    if new_root != root_blk:
        for ht_i in range(72):
            blkno = struct.unpack_from(">I", root_buf, (6 + ht_i) * 4)[0]
            depth = 0
            while blkno and depth < 512:
                depth += 1
                fhb = read_blk(part_abs + blkno)
                if not fhb:
                    break
                if (struct.unpack_from(">I", fhb, 0)[0] != _FFS_T_SHORT or
                        struct.unpack_from(">I", fhb, 4)[0] != blkno):
                    break
                next_blkno = struct.unpack_from(">I", fhb, FHB_HASHCHAIN * 4)[0]
                struct.pack_into(">I", fhb, FHB_PARENT   * 4, new_root)
                struct.pack_into(">I", fhb, _FFS_RL_CHKSUM * 4, 0)
                struct.pack_into(">I", fhb, _FFS_RL_CHKSUM * 4, _ffs_checksum(bytes(fhb), nlongs))
                write_blk(part_abs + blkno, fhb)
                blkno = next_blkno

    # Phase 9: update boot block bb[2] to new_root
    prog("Updating boot block...")
    struct.pack_into(">I", boot_buf, 8, new_root)   # L[2]
    struct.pack_into(">I", boot_buf, 4, 0)           # L[1] = checksum field
    bbsum = 0
    for i in range(nlongs):
        prev  = bbsum
        bbsum = (bbsum + struct.unpack_from(">I", boot_buf, i * 4)[0]) & 0xFFFFFFFF
        if bbsum < prev:
            bbsum = (bbsum + 1) & 0xFFFFFFFF
    struct.pack_into(">I", boot_buf, 4, (~bbsum) & 0xFFFFFFFF)
    if not write_blk(part_abs, boot_buf):
        return False, "Failed to update boot block."

    # Phase 9c: stamp bm_flag=VALID on old root so FFS doesn't run its validator
    if new_root != root_blk:
        old_root_buf = read_blk(part_abs + root_blk)
        if (old_root_buf and
                struct.unpack_from(">I", old_root_buf, 0)[0] == _FFS_T_SHORT and
                struct.unpack_from(">I", old_root_buf, (nlongs - 1) * 4)[0] == _FFS_ST_ROOT and
                struct.unpack_from(">I", old_root_buf, _FFS_RL_BM_FLAG * 4)[0] != _FFS_BM_VALID):
            struct.pack_into(">I", old_root_buf, _FFS_RL_BM_FLAG * 4, _FFS_BM_VALID)
            struct.pack_into(">I", old_root_buf, _FFS_RL_CHKSUM  * 4, 0)
            struct.pack_into(">I", old_root_buf, _FFS_RL_CHKSUM  * 4,
                             _ffs_checksum(bytes(old_root_buf), nlongs))
            write_blk(part_abs + root_blk, old_root_buf)   # non-fatal if fails

    msg = (f"FFS filesystem grown.\n"
           f"old_hi={old_hi}  new_hi={pi.high_cyl}\n"
           f"old_blocks={old_blocks}  new_blocks={new_blocks}\n"
           f"new_bm_need={new_bm_need}  num_new_bm={num_new_bm}\n"
           f"Root: rel {root_blk} → rel {new_root}")
    return True, msg

# ── PFS filesystem grow ─────────────────────────────────────────────────────────

_PFS_OFF_OPTIONS      =  4
_PFS_OFF_RBLKCLUSTER  = 66   # UWORD
_PFS_OFF_RESERVED_BSZ = 64   # UWORD
_PFS_OFF_BLOCKSFREE   = 68
_PFS_OFF_LASTRESERVED = 52
_PFS_OFF_RESERVED_FREE = 60
_PFS_OFF_DISKSIZE     = 84
_PFS_MODE_SIZEFIELD   = 16
_PFS_MODE_SUPERINDEX  = 128
_PFS_ID_PFS1          = 0x50465301
_PFS_ID_PFS2          = 0x50465302


def _pfs_grow(dev: str, rdb, pi, old_hi: int, progress_cb=None) -> tuple:
    """Grow a PFS2/PFS3 filesystem to match pi.high_cyl (already updated).
    Ports DiskPart pfsresize.c algorithm faithfully.
    Returns (True, msg) or (False, err_str)."""

    heads   = pi.surfaces    or rdb.heads
    sectors = pi.blk_per_trk or rdb.sectors
    if not heads or not sectors:
        return False, f"Invalid geometry (heads={heads}, sectors={sectors})."

    phys_per_lb = (pi.size_block * 4 // 512) if pi.size_block * 4 >= 1024 else 1
    rb_lblock   = pi.reserved if pi.reserved > 0 else 2
    part_abs    = (pi.low_cyl * heads * sectors + rb_lblock) * phys_per_lb

    def prog(msg):
        if progress_cb:
            progress_cb(msg)

    def read_cluster(start, count):
        out = bytearray()
        for k in range(count):
            b = _read_block(dev, start + k)
            if b is None:
                return None
            out.extend(b)
        return out

    def write_cluster(start, data):
        for k in range(len(data) // 512):
            if not _write_block(dev, start + k, bytes(data[k * 512:(k + 1) * 512])):
                return False
        return True

    # Phase 1/2: read + validate rootblock
    prog("Reading PFS rootblock...")
    first = _read_block(dev, part_abs)
    if first is None:
        return False, f"Cannot read PFS rootblock (abs {part_abs})."
    disktype = struct.unpack_from(">I", first, 0)[0]
    if disktype not in (_PFS_ID_PFS1, _PFS_ID_PFS2):
        return False, (f"Not a PFS rootblock (disktype=0x{disktype:08X}).\n"
                       f"Expected 0x{_PFS_ID_PFS1:08X} (PFS\\1) or "
                       f"0x{_PFS_ID_PFS2:08X} (PFS\\2).")
    rblkcluster  = struct.unpack_from(">H", first, _PFS_OFF_RBLKCLUSTER)[0]
    reserved_bsz = struct.unpack_from(">H", first, _PFS_OFF_RESERVED_BSZ)[0]
    if rblkcluster == 0:
        return False, "PFS rootblock has rblkcluster=0."
    if reserved_bsz < 512 or reserved_bsz & 3:
        return False, f"Unexpected reserved_blksize={reserved_bsz}."
    cluster_phys = rblkcluster * phys_per_lb

    # Phase 3: read full rootblock cluster
    prog("Reading rootblock cluster...")
    cluster_buf = read_cluster(part_abs, cluster_phys)
    if cluster_buf is None:
        return False, f"Cannot read rootblock cluster ({cluster_phys} sectors at abs {part_abs})."

    # Phase 4: read fields and compute delta
    options       = struct.unpack_from(">I", cluster_buf, _PFS_OFF_OPTIONS)[0]
    lastreserved  = struct.unpack_from(">I", cluster_buf, _PFS_OFF_LASTRESERVED)[0]
    reserved_free = struct.unpack_from(">I", cluster_buf, _PFS_OFF_RESERVED_FREE)[0]
    blocksfree    = struct.unpack_from(">I", cluster_buf, _PFS_OFF_BLOCKSFREE)[0]
    cur_disksize  = struct.unpack_from(">I", cluster_buf, _PFS_OFF_DISKSIZE)[0]

    if options & _PFS_MODE_SUPERINDEX:
        return False, "PFS partition uses SUPERINDEX — not supported by this tool."

    # Derive delta from PFS3's own disksize to avoid DosEnvec geometry mismatch
    old_ncyl     = max(1, old_hi - pi.low_cyl + 1)
    cyl_diff     = pi.high_cyl - old_hi
    bpc          = (cur_disksize // old_ncyl) if (old_ncyl > 0 and cur_disksize > 0) \
                   else (heads * sectors)
    delta_blocks = cyl_diff * bpc
    new_disksize = cur_disksize + delta_blocks

    longsperbmb = reserved_bsz // 4 - 3
    bm_coverage = longsperbmb * 32 if longsperbmb else 1
    bitmapstart = lastreserved + 1
    old_user    = max(0, cur_disksize - bitmapstart)
    new_user    = max(0, new_disksize - bitmapstart)
    old_num_bmb = (old_user + bm_coverage - 1) // bm_coverage
    new_num_bmb = (new_user + bm_coverage - 1) // bm_coverage
    num_new_bmb = max(0, new_num_bmb - old_num_bmb)
    idxperblk   = longsperbmb if longsperbmb else 1
    old_num_idx = (old_num_bmb + idxperblk - 1) // idxperblk if old_num_bmb else 0
    new_num_idx = (new_num_bmb + idxperblk - 1) // idxperblk if new_num_bmb else 0
    num_new_idx = max(0, new_num_idx - old_num_idx)
    reserved_needed = num_new_bmb + num_new_idx

    if reserved_needed > reserved_free:
        return False, (f"PFS reserved area is too full.\n"
                       f"Need {reserved_needed} free reserved blocks "
                       f"({num_new_bmb} bitmap + {num_new_idx} index),\n"
                       f"but only {reserved_free} are available.\n"
                       f"Reformat with a larger reserved area to proceed.")
    if cur_disksize > 0 and blocksfree > cur_disksize:
        return False, (f"PFS metadata corrupted "
                       f"(blocksfree={blocksfree} > disksize={cur_disksize}).\n"
                       f"Run PFSDoctor before growing.")

    # Phase 5: update fields in cluster buffer
    if options & _PFS_MODE_SIZEFIELD:
        struct.pack_into(">I", cluster_buf, _PFS_OFF_DISKSIZE, new_disksize)
    struct.pack_into(">I", cluster_buf, _PFS_OFF_BLOCKSFREE, blocksfree + delta_blocks)

    # Phase 6: write updated cluster
    prog("Writing PFS rootblock cluster...")
    if not write_cluster(part_abs, cluster_buf):
        return False, "Cannot write PFS rootblock cluster."

    # Phase 7: clear MODE_SIZEFIELD (second write, non-fatal if it fails)
    if options & _PFS_MODE_SIZEFIELD:
        struct.pack_into(">I", cluster_buf, _PFS_OFF_OPTIONS, options & ~_PFS_MODE_SIZEFIELD)
        write_cluster(part_abs, cluster_buf)

    msg = (f"PFS filesystem grown.\n"
           f"cyl+{cyl_diff}  bpc={bpc}  delta={delta_blocks}\n"
           f"blocksfree: {blocksfree} → {blocksfree + delta_blocks}\n"
           f"disksize:   {cur_disksize} → {new_disksize}")
    return True, msg


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
        p.size_block   = struct.unpack_from(">I", data, e+ 4)[0]
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

    # Walk filesystem header linked list
    next_blk = rdb.fshdr_list
    seen = set()
    while next_blk != END_MARK and next_blk not in seen:
        seen.add(next_blk)
        data = _read_block(dev, next_blk)
        if data is None or len(data) < 128:
            break
        if struct.unpack_from(">I", data, 0)[0] != FSHD_ID:
            break

        fs               = FilesystemInfo()
        fs.block_num     = next_blk
        next_fshd        = struct.unpack_from(">I", data, 16)[0]
        fs.dos_type      = struct.unpack_from(">I", data, 32)[0]
        fs.version       = struct.unpack_from(">I", data, 36)[0]
        fs.patch_flags   = struct.unpack_from(">I", data, 40)[0]
        fs.stack_size    = struct.unpack_from(">I", data, 60)[0]
        fs.priority      = struct.unpack_from(">I", data, 64)[0]
        fs.startup       = struct.unpack_from(">I", data, 68)[0]
        first_lseg       = struct.unpack_from(">I", data, 72)[0]
        fs.global_vec    = struct.unpack_from(">I", data, 76)[0]

        # Reassemble binary from LSEG chain
        lseg_data = bytearray()
        lseg_blk  = first_lseg
        lseg_seen = set()
        while lseg_blk != END_MARK and lseg_blk not in lseg_seen:
            lseg_seen.add(lseg_blk)
            ldata = _read_block(dev, lseg_blk)
            if ldata is None or struct.unpack_from(">I", ldata, 0)[0] != LSEG_ID:
                break
            lseg_data.extend(ldata[20:512])
            lseg_blk = struct.unpack_from(">I", ldata, 16)[0]
        fs.data = bytes(lseg_data)

        rdb.filesystems.append(fs)
        next_blk = next_fshd

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
    struct.pack_into(">I", d,  32, rdb.fshdr_list)  # FileSysHeaderList
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
    struct.pack_into(">I", d, e+ 4, p.size_block)  # SizeBlock
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


def build_fshd_block(fs: FilesystemInfo, next_fshd: int, first_lseg: int) -> bytes:
    d = bytearray(512)
    struct.pack_into(">I", d,  0, FSHD_ID)
    struct.pack_into(">I", d,  4, 128)
    struct.pack_into(">I", d,  8, 0)
    struct.pack_into(">I", d, 12, 7)              # HostID
    struct.pack_into(">I", d, 16, next_fshd)
    struct.pack_into(">I", d, 20, 0)              # Flags
    struct.pack_into(">I", d, 24, END_MARK)       # Reserved[0]
    struct.pack_into(">I", d, 28, END_MARK)       # Reserved[1]
    struct.pack_into(">I", d, 32, fs.dos_type)
    struct.pack_into(">I", d, 36, fs.version)
    struct.pack_into(">I", d, 40, fs.patch_flags)
    # DevNode
    struct.pack_into(">I", d, 44, 0)              # Type
    struct.pack_into(">I", d, 48, 0)              # Task
    struct.pack_into(">I", d, 52, 0)              # Lock
    struct.pack_into(">I", d, 56, 0)              # Handler
    struct.pack_into(">I", d, 60, fs.stack_size)
    struct.pack_into(">I", d, 64, fs.priority)
    struct.pack_into(">I", d, 68, fs.startup)
    struct.pack_into(">I", d, 72, first_lseg)     # SegListBlk
    struct.pack_into(">I", d, 76, fs.global_vec)
    _fix_checksum(d, 8)
    return bytes(d)


def build_lseg_blocks(fs: FilesystemInfo, first_block: int) -> list:
    """Return list of (block_num, bytes) for the LSEG chain."""
    data   = fs.data or b""
    n      = max(1, math.ceil(len(data) / LSEG_DATA)) if data else 0
    result = []
    for i in range(n):
        blk      = first_block + i
        next_blk = first_block + i + 1 if i + 1 < n else END_MARK
        chunk    = data[i * LSEG_DATA:(i + 1) * LSEG_DATA]
        d = bytearray(512)
        struct.pack_into(">I", d,  0, LSEG_ID)
        struct.pack_into(">I", d,  4, 128)
        struct.pack_into(">I", d,  8, 0)
        struct.pack_into(">I", d, 12, 7)
        struct.pack_into(">I", d, 16, next_blk)
        d[20:20 + len(chunk)] = chunk
        _fix_checksum(d, 8)
        result.append((blk, bytes(d)))
    return result


# ─── Disk enumeration ──────────────────────────────────────────────────────────

def get_disks() -> list:
    if _IS_MACOS:
        return _get_disks_macos()
    return _get_disks_linux()


def _get_disks_linux() -> list:
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


def _get_disks_macos() -> list:
    import plistlib
    try:
        r = subprocess.run(
            ["diskutil", "list", "-plist"],
            capture_output=True, timeout=10)
        data = plistlib.loads(r.stdout)
        result = []
        for disk in data.get("AllDisksAndPartitions", []):
            identifier = disk.get("DeviceIdentifier", "")
            if not identifier:
                continue
            try:
                ri = subprocess.run(
                    ["diskutil", "info", "-plist", identifier],
                    capture_output=True, timeout=10)
                info = plistlib.loads(ri.stdout)
            except Exception:
                info = {}
            size  = int(info.get("TotalSize") or info.get("Size") or 0)
            model = (info.get("MediaName") or info.get("IORegistryEntryName") or "").strip()
            result.append({"name": identifier,
                           "path": f"/dev/r{identifier}",
                           "size": size, "model": model})
        return result
    except Exception:
        return []


def _parse_intval(s: str) -> int:
    s = s.strip()
    return int(s, 16) if s.lower().startswith("0x") else int(s)


def fmt_size(b: int) -> str:
    for unit in ("B","KB","MB","GB","TB"):
        if b < 1024:
            return f"{b:.1f} {unit}"
        b /= 1024
    return f"{b:.1f} PB"


# ─── Dialogs ───────────────────────────────────────────────────────────────────

class CreateImageDialog(tk.Toplevel):
    """Ask for a file path and size, then create a zero-filled disk image."""

    _UNITS = [("KB", 1024), ("MB", 1024**2), ("GB", 1024**3)]
    _PRESETS = [
        ("Custom", 0),
        ("10 MB",  10 * 1024**2),
        ("20 MB",  20 * 1024**2),
        ("50 MB",  50 * 1024**2),
        ("100 MB", 100 * 1024**2),
        ("128 MB", 128 * 1024**2),
        ("256 MB", 256 * 1024**2),
        ("504 MB", 504 * 1024**2),
        ("1 GB",   1024**3),
        ("2 GB",   2 * 1024**3),
        ("4 GB",   4 * 1024**3),
    ]

    def __init__(self, parent):
        super().__init__(parent)
        self.title("Create Blank Disk Image")
        self.resizable(False, False)
        self.grab_set()
        self.result = None   # set to path on success
        self._build()
        self.transient(parent)
        self.wait_window()

    def _build(self):
        f = tk.Frame(self, padx=14, pady=12)
        f.pack(fill="both", expand=True)
        row = 0

        # ── File path ──────────────────────────────────────────────────────
        tk.Label(f, text="Image file:").grid(row=row, column=0, sticky="e", pady=4)
        self._path_var = tk.StringVar()
        path_entry = tk.Entry(f, textvariable=self._path_var, width=36)
        path_entry.grid(row=row, column=1, sticky="w", pady=4)
        tk.Button(f, text="Browse…", command=self._browse).grid(
            row=row, column=2, padx=(4, 0), pady=4)
        row += 1

        # ── Preset sizes ───────────────────────────────────────────────────
        tk.Label(f, text="Preset size:").grid(row=row, column=0, sticky="e", pady=4)
        self._preset_var = tk.StringVar(value=self._PRESETS[0][0])
        ttk.Combobox(f, textvariable=self._preset_var,
                     values=[p[0] for p in self._PRESETS],
                     state="readonly", width=12).grid(row=row, column=1, sticky="w", pady=4)
        self._preset_var.trace_add("write", self._on_preset)
        row += 1

        # ── Manual size entry ──────────────────────────────────────────────
        tk.Label(f, text="Size:").grid(row=row, column=0, sticky="e", pady=4)
        size_frame = tk.Frame(f)
        size_frame.grid(row=row, column=1, columnspan=2, sticky="w", pady=4)
        self._size_var = tk.StringVar(value="100")
        self._size_var.trace_add("write", self._upd_preview)
        tk.Entry(size_frame, textvariable=self._size_var, width=10).pack(side="left")
        self._unit_var = tk.StringVar(value="MB")
        ttk.Combobox(size_frame, textvariable=self._unit_var,
                     values=[u[0] for u in self._UNITS],
                     state="readonly", width=5).pack(side="left", padx=(4, 0))
        self._unit_var.trace_add("write", self._upd_preview)
        row += 1

        # ── Size preview ───────────────────────────────────────────────────
        self._preview_var = tk.StringVar()
        tk.Label(f, textvariable=self._preview_var,
                 fg="gray", font=("", 8)).grid(
            row=row, column=1, columnspan=2, sticky="w"); row += 1
        self._upd_preview()

        # ── Buttons ────────────────────────────────────────────────────────
        bf = tk.Frame(f)
        bf.grid(row=row, columnspan=3, pady=(10, 0))
        tk.Button(bf, text="Create",  width=12, command=self._ok).pack(side="left", padx=4)
        tk.Button(bf, text="Cancel",  width=10, command=self.destroy).pack(side="left", padx=4)

    def _browse(self):
        path = filedialog.asksaveasfilename(
            title="New Disk Image",
            defaultextension=".img",
            filetypes=[("Disk image", "*.img *.hdf"),
                       ("All files", "*.*")])
        if path:
            self._path_var.set(path)

    def _on_preset(self, *_):
        label = self._preset_var.get()
        if label == "Custom":
            return
        size = next(b for n, b in self._PRESETS if n == label)
        # express in the largest clean unit
        for unit_name, unit_mult in reversed(self._UNITS):
            if size % unit_mult == 0:
                self._unit_var.set(unit_name)
                self._size_var.set(str(size // unit_mult))
                return

    def _upd_preview(self, *_):
        try:
            mult = next(m for n, m in self._UNITS if n == self._unit_var.get())
            total = int(self._size_var.get()) * mult
            self._preview_var.set(f"= {fmt_size(total)}  ({total:,} bytes)")
        except (ValueError, StopIteration):
            self._preview_var.set("")

    def _ok(self):
        path = self._path_var.get().strip()
        if not path:
            messagebox.showerror("Error", "Choose a file path first.", parent=self)
            return
        try:
            mult = next(m for n, m in self._UNITS if n == self._unit_var.get())
            total = int(self._size_var.get()) * mult
        except (ValueError, StopIteration):
            messagebox.showerror("Error", "Enter a valid numeric size.", parent=self)
            return
        if total <= 0:
            messagebox.showerror("Error", "Size must be greater than zero.", parent=self)
            return
        if total % 512 != 0:
            # Round up to nearest 512-byte sector boundary
            total = ((total + 511) // 512) * 512
        self.result = (path, total)
        self.destroy()


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

        fs_menu = _rdb_fs_menu(self._rdb)
        tk.Label(f, text="Filesystem:").grid(row=row, column=0, sticky="e", pady=3)
        self._fs_var = tk.StringVar(value=fs_menu[0][0])
        ttk.Combobox(f, textvariable=self._fs_var,
                     values=[x[0] for x in fs_menu],
                     state="readonly", width=30).grid(row=row, column=1, sticky="w", pady=3)
        row += 1

        lbl_entry("Boot priority:", "0", "bootpri", 6)

        flag_frame = tk.Frame(f, relief="groove", bd=2)
        flag_frame.grid(row=row, columnspan=2, sticky="ew", pady=(4, 2)); row += 1
        self._bootable_var   = tk.BooleanVar(value=len(rdb.partitions) == 0)
        self._automount_var  = tk.BooleanVar(value=True)
        self._directscsi_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(flag_frame, text=" Bootable ",
                        variable=self._bootable_var,
                        style='Big.TCheckbutton').pack(side="left", padx=8, pady=5)
        ttk.Checkbutton(flag_frame, text=" Auto-mount ",
                        variable=self._automount_var,
                        style='Big.TCheckbutton').pack(side="left", padx=8, pady=5)
        ttk.Checkbutton(flag_frame, text=" Direct SCSI transfer ",
                        variable=self._directscsi_var,
                        style='Big.TCheckbutton').pack(side="left", padx=8, pady=5)

        self._size_lbl = tk.Label(f, text="", fg="#336699")
        self._size_lbl.grid(row=row, columnspan=2, sticky="w"); row+=1

        for key in ("lo","hi"):
            self._vars[key].trace_add("write", self._upd_size)
        self._upd_size()

        def fill_frame(parent, fields):
            for i, (lbl, val, key, w) in enumerate(fields):
                c = (i % 2) * 3
                r = i // 2
                tk.Label(parent, text=lbl, justify="right").grid(
                    row=r, column=c, sticky="e", padx=(8, 2), pady=2)
                v = tk.StringVar(value=val)
                self._vars[key] = v
                tk.Entry(parent, textvariable=v, width=w).grid(
                    row=r, column=c+1, sticky="w", padx=(0, 12), pady=2)

        # ── Advanced toggle ────────────────────────────────────────────────────
        self._adv_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(f, text="Show advanced settings",
                        variable=self._adv_var,
                        command=self._toggle_adv).grid(
            row=row, columnspan=2, sticky="w", pady=(6, 0)); row += 1

        # ── Advanced ──────────────────────────────────────────────────────────
        self._adv_frame = ttk.LabelFrame(f, text="Advanced")
        self._adv_frame.grid(row=row, columnspan=2, sticky="ew", pady=(4, 2)); row += 1
        fill_frame(self._adv_frame, [
            ("Surfaces:",   str(self._rdb.heads),   "surfaces",   8),
            ("Secs/track:", str(self._rdb.sectors), "blkpertrk",  8),
            ("Secs/block:", "1",                    "secsperblk", 8),
            ("Reserved:",   "2",                    "reserved",   8),
            ("PreAlloc:",   "0",                    "prealloc",   8),
            ("Interleave:", "0",                    "interleave", 8),
            ("BootBlocks:", "2",                    "bootblocks", 8),
        ])

        # ── Parameters ────────────────────────────────────────────────────────
        prm = ttk.LabelFrame(f, text="Parameters")
        prm.grid(row=row, columnspan=2, sticky="ew", pady=(2, 4)); row += 1
        fill_frame(prm, [
            ("NumBuffer:",   "30",          "numbuffer",   8),
            ("MaxTransfer:", "0x7FFFFFFF",  "maxtransfer", 12),
            ("Mask:",        "0xFFFFFFFE",  "mask",        12),
        ])
        # BufMemType dropdown (row 1, col 3 — alongside Mask)
        tk.Label(prm, text="BufMemType:", justify="right").grid(
            row=1, column=3, sticky="e", padx=(8, 2), pady=2)
        self._bufmemtype_var = tk.StringVar(value=BUFMEMTYPE_OPTS[1][0])
        ttk.Combobox(prm, textvariable=self._bufmemtype_var,
                     values=[lbl for lbl, _ in BUFMEMTYPE_OPTS],
                     state="readonly", width=14).grid(
            row=1, column=4, sticky="w", padx=(0, 12), pady=2)
        # Block Size dropdown (row 2, col 0)
        tk.Label(prm, text="Block size:", justify="right").grid(
            row=2, column=0, sticky="e", padx=(8, 2), pady=2)
        self._sizeblock_var = tk.StringVar(value=SIZEBLOCK_OPTS[0][0])
        ttk.Combobox(prm, textvariable=self._sizeblock_var,
                     values=[lbl for lbl, _ in SIZEBLOCK_OPTS],
                     state="readonly", width=14).grid(
            row=2, column=1, sticky="w", padx=(0, 12), pady=2)

        self._adv_frame.grid_remove()

        bf = tk.Frame(f)
        bf.grid(row=row, columnspan=2, pady=(8,0))
        tk.Button(bf, text="Add",    width=10, command=self._ok).pack(side="left", padx=4)
        tk.Button(bf, text="Cancel", width=10, command=self.destroy).pack(side="left", padx=4)

    def _toggle_adv(self):
        if self._adv_var.get():
            self._adv_frame.grid()
        else:
            self._adv_frame.grid_remove()
        self.update_idletasks()
        self.geometry("")

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
            lo          = int(self._vars["lo"].get())
            hi          = int(self._vars["hi"].get())
            bp          = int(self._vars["bootpri"].get())
            surfaces    = _parse_intval(self._vars["surfaces"].get())
            blkpertrk   = _parse_intval(self._vars["blkpertrk"].get())
            secsperblk  = _parse_intval(self._vars["secsperblk"].get())
            reserved    = _parse_intval(self._vars["reserved"].get())
            prealloc    = _parse_intval(self._vars["prealloc"].get())
            interleave  = _parse_intval(self._vars["interleave"].get())
            numbuffer   = _parse_intval(self._vars["numbuffer"].get())
            maxtransfer = _parse_intval(self._vars["maxtransfer"].get())
            mask        = _parse_intval(self._vars["mask"].get())
            bootblocks  = _parse_intval(self._vars["bootblocks"].get())
        except ValueError:
            messagebox.showerror("Error", "Numeric fields must be integers.", parent=self); return
        bufmemtype = next(v for lbl, v in BUFMEMTYPE_OPTS if lbl == self._bufmemtype_var.get())
        size_block = next(v for lbl, v in SIZEBLOCK_OPTS if lbl == self._sizeblock_var.get())
        if lo < self._rdb.locyl or hi > self._rdb.hicyl or lo > hi:
            messagebox.showerror("Error",
                f"Cylinder range must be within {self._rdb.locyl}–{self._rdb.hicyl}.", parent=self)
            return
        for p in self._rdb.partitions:
            if lo <= p.high_cyl and hi >= p.low_cyl:
                messagebox.showerror("Error",
                    f"Overlaps with existing partition {p.drive_name}.", parent=self)
                return

        dos_type = next(v for n,v in _rdb_fs_menu(self._rdb) if n == self._fs_var.get())

        p = PartitionInfo()
        p.drive_name   = name
        p.low_cyl      = lo
        p.high_cyl     = hi
        p.dos_type     = dos_type
        p.boot_pri     = bp
        p.flags        = (0 if self._bootable_var.get()   else 2) | \
                         (0 if self._automount_var.get()  else 4) | \
                         (8 if self._directscsi_var.get() else 0)
        p.size_block   = size_block
        p.surfaces     = surfaces
        p.blk_per_trk  = blkpertrk
        p.secs_per_blk = secsperblk
        p.reserved     = reserved
        p.prealloc     = prealloc
        p.interleave   = interleave
        p.num_buffer   = numbuffer
        p.buf_mem_type = bufmemtype
        p.max_transfer = maxtransfer
        p.mask         = mask
        p.boot_blocks  = bootblocks
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

        fs_menu = _rdb_fs_menu(self._rdb)
        tk.Label(f, text="Filesystem:").grid(row=row, column=0, sticky="e", pady=3)
        self._fs_var = tk.StringVar(
            value=next((n for n, v in fs_menu if v == p.dos_type), fs_menu[0][0]))
        ttk.Combobox(f, textvariable=self._fs_var,
                     values=[x[0] for x in fs_menu],
                     state="readonly", width=30).grid(row=row, column=1, sticky="w", pady=3)
        row += 1

        lbl_entry("Boot priority:", str(p.boot_pri), "bootpri", 6)

        flag_frame = tk.Frame(f, relief="groove", bd=2)
        flag_frame.grid(row=row, columnspan=2, sticky="ew", pady=(4, 2)); row += 1
        self._bootable_var   = tk.BooleanVar(value=not (p.flags & 2))
        self._automount_var  = tk.BooleanVar(value=not (p.flags & 4))
        self._directscsi_var = tk.BooleanVar(value=bool(p.flags & 8))
        ttk.Checkbutton(flag_frame, text=" Bootable ",
                        variable=self._bootable_var,
                        style='Big.TCheckbutton').pack(side="left", padx=8, pady=5)
        ttk.Checkbutton(flag_frame, text=" Auto-mount ",
                        variable=self._automount_var,
                        style='Big.TCheckbutton').pack(side="left", padx=8, pady=5)
        ttk.Checkbutton(flag_frame, text=" Direct SCSI transfer ",
                        variable=self._directscsi_var,
                        style='Big.TCheckbutton').pack(side="left", padx=8, pady=5)

        self._size_lbl = tk.Label(f, text="", fg="#336699")
        self._size_lbl.grid(row=row, columnspan=2, sticky="w"); row += 1

        # ── Resize slider ──────────────────────────────────────────────────────
        self._slider_busy = False
        self._snap_active = False
        orig_cyls = p.high_cyl - p.low_cyl + 1
        self._prev_slider_cyls = orig_cyls
        max_cyls  = max(1, self._max_hi - p.low_cyl + 1)
        rsz = ttk.LabelFrame(f, text="Resize  (WARNING: any resize will cause data loss!)")
        rsz.grid(row=row, columnspan=2, sticky="ew", pady=(4, 2)); row += 1
        self._slider_var = tk.IntVar(value=orig_cyls)
        tk.Scale(rsz, variable=self._slider_var, from_=1, to=max_cyls,
                 orient="horizontal", showvalue=False, length=400,
                 command=self._on_slider).pack(fill="x", padx=8, pady=6)

        for key in ("lo", "hi"):
            self._vars[key].trace_add("write", self._upd_size)
        self._upd_size()

        def fill_frame(parent, fields):
            for i, (lbl, val, key, w) in enumerate(fields):
                c = (i % 2) * 3
                r = i // 2
                tk.Label(parent, text=lbl, justify="right").grid(
                    row=r, column=c, sticky="e", padx=(8, 2), pady=2)
                v = tk.StringVar(value=val)
                self._vars[key] = v
                tk.Entry(parent, textvariable=v, width=w).grid(
                    row=r, column=c+1, sticky="w", padx=(0, 12), pady=2)

        # ── Advanced toggle ────────────────────────────────────────────────────
        self._adv_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(f, text="Show advanced settings",
                        variable=self._adv_var,
                        command=self._toggle_adv).grid(
            row=row, columnspan=2, sticky="w", pady=(6, 0)); row += 1

        # ── Advanced ──────────────────────────────────────────────────────────
        self._adv_frame = ttk.LabelFrame(f, text="Advanced")
        self._adv_frame.grid(row=row, columnspan=2, sticky="ew", pady=(4, 2)); row += 1
        fill_frame(self._adv_frame, [
            ("Surfaces:",   str(p.surfaces),     "surfaces",   8),
            ("Secs/track:", str(p.blk_per_trk),  "blkpertrk",  8),
            ("Secs/block:", str(p.secs_per_blk), "secsperblk", 8),
            ("Reserved:",   str(p.reserved),     "reserved",   8),
            ("PreAlloc:",   str(p.prealloc),     "prealloc",   8),
            ("Interleave:", str(p.interleave),   "interleave", 8),
            ("BootBlocks:", str(p.boot_blocks),  "bootblocks", 8),
        ])
        # ── Parameters ────────────────────────────────────────────────────────
        prm = ttk.LabelFrame(f, text="Parameters")
        prm.grid(row=row, columnspan=2, sticky="ew", pady=(2, 4)); row += 1
        fill_frame(prm, [
            ("NumBuffer:",   str(p.num_buffer),          "numbuffer",   8),
            ("MaxTransfer:", f"0x{p.max_transfer:08X}",  "maxtransfer", 12),
            ("Mask:",        f"0x{p.mask:08X}",          "mask",        12),
        ])
        # BufMemType dropdown (row 1, col 3 — alongside Mask)
        tk.Label(prm, text="BufMemType:", justify="right").grid(
            row=1, column=3, sticky="e", padx=(8, 2), pady=2)
        _bmt_default = next((lbl for lbl, v in BUFMEMTYPE_OPTS if v == p.buf_mem_type),
                            f"Custom ({p.buf_mem_type})")
        self._bufmemtype_var = tk.StringVar(value=_bmt_default)
        _bmt_values = [lbl for lbl, _ in BUFMEMTYPE_OPTS]
        if _bmt_default not in _bmt_values:
            _bmt_values = [_bmt_default] + _bmt_values
        ttk.Combobox(prm, textvariable=self._bufmemtype_var,
                     values=_bmt_values,
                     state="readonly", width=14).grid(
            row=1, column=4, sticky="w", padx=(0, 12), pady=2)
        # Block Size dropdown (row 2, col 0)
        tk.Label(prm, text="Block size:", justify="right").grid(
            row=2, column=0, sticky="e", padx=(8, 2), pady=2)
        _sb_default = next((lbl for lbl, v in SIZEBLOCK_OPTS if v == p.size_block),
                           f"Custom ({p.size_block})")
        self._sizeblock_var = tk.StringVar(value=_sb_default)
        _sb_values = [lbl for lbl, _ in SIZEBLOCK_OPTS]
        if _sb_default not in _sb_values:
            _sb_values = [_sb_default] + _sb_values
        ttk.Combobox(prm, textvariable=self._sizeblock_var,
                     values=_sb_values,
                     state="readonly", width=14).grid(
            row=2, column=1, sticky="w", padx=(0, 12), pady=2)

        self._adv_frame.grid_remove()

        bf = tk.Frame(f)
        bf.grid(row=row, columnspan=2, pady=(8, 0))
        tk.Button(bf, text="Save",   width=10, command=self._ok).pack(side="left", padx=4)
        tk.Button(bf, text="Cancel", width=10, command=self.destroy).pack(side="left", padx=4)

    def _toggle_adv(self):
        if self._adv_var.get():
            self._adv_frame.grid()
        else:
            self._adv_frame.grid_remove()
        self.update_idletasks()
        self.geometry("")

    def _upd_size(self, *_):
        try:
            lo = int(self._vars["lo"].get())
            hi = int(self._vars["hi"].get())
            cyls = hi - lo + 1
            sz = cyls * self._rdb.heads * self._rdb.sectors * 512
            self._size_lbl.config(text=f"Size: {fmt_size(sz)}  ({cyls} cylinders)")
            orig_cyls = self._orig.high_cyl - self._orig.low_cyl + 1
            self._size_lbl.config(fg="red" if cyls != orig_cyls else "#336699")
            if not self._slider_busy:
                self._slider_busy = True
                try:
                    max_cyls = max(1, self._max_hi - lo + 1)
                    self._slider_var.set(max(1, min(cyls, max_cyls)))
                finally:
                    self._slider_busy = False
        except ValueError:
            self._size_lbl.config(text="")

    def _on_slider(self, val):
        if self._slider_busy:
            return
        cyls = int(float(val))
        orig_cyls = self._orig.high_cyl - self._orig.low_cyl + 1
        # Snap/sticky detent when crossing the original size position
        if self._snap_active:
            self._slider_busy = True
            try:
                self._slider_var.set(orig_cyls)
            finally:
                self._slider_busy = False
            return
        prev = self._prev_slider_cyls
        if (prev < orig_cyls < cyls) or (prev > orig_cyls > cyls):
            self._snap_active = True
            cyls = orig_cyls
            self.after(350, self._release_snap)
        self._prev_slider_cyls = cyls
        self._slider_busy = True
        try:
            self._slider_var.set(cyls)
            try:
                lo = int(self._vars["lo"].get())
            except ValueError:
                lo = self._orig.low_cyl
            self._vars["hi"].set(str(lo + cyls - 1))
        finally:
            self._slider_busy = False

    def _release_snap(self):
        self._snap_active = False

    def _ok(self):
        name = self._vars["name"].get().strip()
        if not name:
            messagebox.showerror("Error", "Drive name is required.", parent=self); return
        try:
            lo          = int(self._vars["lo"].get())
            hi          = int(self._vars["hi"].get())
            bp          = int(self._vars["bootpri"].get())
            surfaces    = _parse_intval(self._vars["surfaces"].get())
            blkpertrk   = _parse_intval(self._vars["blkpertrk"].get())
            secsperblk  = _parse_intval(self._vars["secsperblk"].get())
            reserved    = _parse_intval(self._vars["reserved"].get())
            prealloc    = _parse_intval(self._vars["prealloc"].get())
            interleave  = _parse_intval(self._vars["interleave"].get())
            numbuffer   = _parse_intval(self._vars["numbuffer"].get())
            maxtransfer = _parse_intval(self._vars["maxtransfer"].get())
            mask        = _parse_intval(self._vars["mask"].get())
            bootblocks  = _parse_intval(self._vars["bootblocks"].get())
        except ValueError:
            messagebox.showerror("Error", "Numeric fields must be integers.", parent=self); return
        sel = self._bufmemtype_var.get()
        bufmemtype = next((v for lbl, v in BUFMEMTYPE_OPTS if lbl == sel),
                          int(sel.split("(")[1].rstrip(")")))
        sel_sb = self._sizeblock_var.get()
        size_block = next((v for lbl, v in SIZEBLOCK_OPTS if lbl == sel_sb), None)
        if size_block is None:
            size_block = int(sel_sb.split("(")[1].rstrip(")"))

        if lo < self._min_lo or hi > self._max_hi or lo > hi:
            messagebox.showerror("Error",
                f"Cylinder range must be within {self._min_lo}–{self._max_hi} "
                f"and low ≤ high.", parent=self); return

        if lo < self._orig.low_cyl:
            messagebox.showerror("Cannot Resize From Start",
                "Filesystem resize is only possible when the start cylinder is left "
                "unchanged.\n\nTo grow a partition, drag the right edge or use the "
                "Grow Partition button instead.", parent=self); return

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
        p.dos_type     = next(v for n, v in _rdb_fs_menu(self._rdb) if n == self._fs_var.get())
        p.boot_pri     = bp
        p.flags        = (0 if self._bootable_var.get()   else 2) | \
                         (0 if self._automount_var.get()  else 4) | \
                         (8 if self._directscsi_var.get() else 0)
        p.size_block   = size_block
        p.surfaces     = surfaces
        p.blk_per_trk  = blkpertrk
        p.secs_per_blk = secsperblk
        p.reserved     = reserved
        p.prealloc     = prealloc
        p.interleave   = interleave
        p.num_buffer   = numbuffer
        p.buf_mem_type = bufmemtype
        p.max_transfer = maxtransfer
        p.mask         = mask
        p.boot_blocks  = bootblocks
        self.result = p
        self.destroy()


# ─── Add filesystem dialog ─────────────────────────────────────────────────────

# Common external filesystem DosTypes offered as presets
_FS_PRESETS = [
    ("PFS\\3  — Professional File System 3", 0x50465303),
    ("PFS\\2  — Professional File System 2", 0x50465302),
    ("PFS\\1  — Professional File System 1", 0x50465301),
    ("SFS\\0  — Smart File System",           0x53465300),
    ("SFS\\2  — Smart File System 2",         0x53465302),
    ("FAT\\0  — FAT95",                       0x46415400),
    ("Custom (enter DosType below)",          0),
]

class AddFilesystemDialog(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Add Filesystem to RDB")
        self.resizable(False, False)
        self.grab_set()
        self.transient(parent)
        self.result: Optional[FilesystemInfo] = None
        self._build()
        self.wait_window()

    def _build(self):
        f = tk.Frame(self, padx=14, pady=12)
        f.pack(fill="both", expand=True)
        row = 0

        # Filesystem binary
        tk.Label(f, text="Filesystem binary:", justify="right").grid(
            row=row, column=0, sticky="e", pady=3)
        self._path_var = tk.StringVar()
        tk.Entry(f, textvariable=self._path_var, width=36).grid(
            row=row, column=1, sticky="ew", pady=3)
        tk.Button(f, text="Browse…", command=self._browse).grid(
            row=row, column=2, padx=(4,0), pady=3)
        row += 1

        # Preset selector
        tk.Label(f, text="Filesystem type:", justify="right").grid(
            row=row, column=0, sticky="e", pady=3)
        self._preset_var = tk.StringVar(value=_FS_PRESETS[0][0])
        cb = ttk.Combobox(f, textvariable=self._preset_var,
                          values=[x[0] for x in _FS_PRESETS],
                          state="readonly", width=38)
        cb.grid(row=row, column=1, columnspan=2, sticky="w", pady=3)
        cb.bind("<<ComboboxSelected>>", self._on_preset)
        row += 1

        # DosType hex entry + ASCII preview
        tk.Label(f, text="DosType (hex):", justify="right").grid(
            row=row, column=0, sticky="e", pady=3)
        self._dostype_var = tk.StringVar(value=f"0x{_FS_PRESETS[0][1]:08X}")
        tk.Entry(f, textvariable=self._dostype_var, width=14).grid(
            row=row, column=1, sticky="w", pady=3)
        self._dostype_preview = tk.Label(f, text="", fg="#336699", font=("Monospace", 10))
        self._dostype_preview.grid(row=row, column=2, sticky="w", padx=(6, 0))
        self._dostype_var.trace_add("write", self._upd_dostype_preview)
        self._upd_dostype_preview()
        row += 1

        # Version
        tk.Label(f, text="Version (major.minor):", justify="right").grid(
            row=row, column=0, sticky="e", pady=3)
        self._version_var = tk.StringVar(value="0.0")
        tk.Entry(f, textvariable=self._version_var, width=10).grid(
            row=row, column=1, sticky="w", pady=3)
        row += 1

        # Stack size
        tk.Label(f, text="Stack size:", justify="right").grid(
            row=row, column=0, sticky="e", pady=3)
        self._stack_var = tk.StringVar(value="4096")
        tk.Entry(f, textvariable=self._stack_var, width=10).grid(
            row=row, column=1, sticky="w", pady=3)
        row += 1

        # File info label
        self._info_lbl = tk.Label(f, text="", fg="#336699", anchor="w")
        self._info_lbl.grid(row=row, column=0, columnspan=3, sticky="w"); row += 1

        f.columnconfigure(1, weight=1)

        bf = tk.Frame(f)
        bf.grid(row=row, columnspan=3, pady=(8, 0))
        tk.Button(bf, text="Add",    width=10, command=self._ok).pack(side="left", padx=4)
        tk.Button(bf, text="Cancel", width=10, command=self.destroy).pack(side="left", padx=4)

    def _upd_dostype_preview(self, *_):
        try:
            dt = _parse_intval(self._dostype_var.get())
            chars = []
            for i in range(4):
                b = (dt >> (24 - i * 8)) & 0xFF
                chars.append(chr(b) if 32 <= b < 127 else f"\\{b}")
            self._dostype_preview.config(text="".join(chars), fg="#336699")
        except (ValueError, AttributeError):
            self._dostype_preview.config(text="", fg="#336699")

    def _browse(self):
        path = filedialog.askopenfilename(
            title="Select Filesystem Binary",
            filetypes=[("All files", "*")])
        if not path:
            return
        self._path_var.set(path)
        try:
            size = os.path.getsize(path)
            n_lseg = math.ceil(size / LSEG_DATA)
            self._info_lbl.config(
                text=f"{fmt_size(size)}  ({n_lseg} LSEG block{'s' if n_lseg != 1 else ''})")
        except OSError:
            self._info_lbl.config(text="")

    def _on_preset(self, _=None):
        label = self._preset_var.get()
        dt = next((v for n, v in _FS_PRESETS if n == label), 0)
        if dt:
            self._dostype_var.set(f"0x{dt:08X}")

    def _ok(self):
        path = self._path_var.get().strip()
        if not path:
            messagebox.showerror("Error", "Select a filesystem binary.", parent=self)
            return
        try:
            with open(path, "rb") as fh:
                data = fh.read()
        except OSError as e:
            messagebox.showerror("Error", str(e), parent=self)
            return
        if not data:
            messagebox.showerror("Error", "File is empty.", parent=self)
            return
        try:
            dos_type = _parse_intval(self._dostype_var.get())
        except ValueError:
            messagebox.showerror("Error", "Invalid DosType.", parent=self)
            return
        try:
            parts = self._version_var.get().strip().split(".")
            major = int(parts[0])
            minor = int(parts[1]) if len(parts) > 1 else 0
            version = (major << 16) | (minor & 0xFFFF)
        except (ValueError, IndexError):
            messagebox.showerror("Error", "Version must be major.minor (e.g. 47.16).",
                                 parent=self)
            return
        try:
            stack = int(self._stack_var.get())
        except ValueError:
            messagebox.showerror("Error", "Stack size must be an integer.", parent=self)
            return

        fs            = FilesystemInfo()
        fs.dos_type   = dos_type
        fs.version    = version
        fs.stack_size = stack
        fs.data       = data
        self.result   = fs
        self.destroy()


# ─── dd progress dialog ────────────────────────────────────────────────────────

class _DDProgressDialog(tk.Toplevel):
    """Modal progress dialog that runs a dd command and shows live progress."""

    def __init__(self, parent, title: str, cmd: list, total_bytes: int):
        super().__init__(parent)
        self.title(title)
        self.resizable(False, False)
        self.protocol("WM_DELETE_WINDOW", self._cancel)
        self.transient(parent)
        self._total     = total_bytes
        self._proc      = None
        self._done      = False
        self._error     = None
        self._cancelled = False
        self._bytes     = 0
        self._speed     = ""
        self._build()
        self.grab_set()
        self._thread = threading.Thread(target=self._run, args=(cmd,), daemon=True)
        self._thread.start()
        self._poll()
        self.wait_window()

    @property
    def success(self):
        return self._done and not self._cancelled and self._error is None

    def _build(self):
        f = tk.Frame(self, padx=16, pady=12)
        f.pack(fill="both", expand=True)
        self._lbl = tk.Label(f, text="Starting…", width=52, anchor="w")
        self._lbl.pack(fill="x", pady=(0, 6))
        self._bar = ttk.Progressbar(f, length=420, mode="determinate", maximum=1000)
        self._bar.pack(fill="x", pady=(0, 6))
        self._speed_lbl = tk.Label(f, text="", fg="#336699", anchor="w")
        self._speed_lbl.pack(fill="x", pady=(0, 8))
        tk.Button(f, text="Cancel", width=10, command=self._cancel).pack()

    def _run(self, cmd):
        try:
            self._proc = subprocess.Popen(cmd, stderr=subprocess.PIPE,
                                          stdout=subprocess.DEVNULL)
            if _IS_MACOS:
                # Send SIGINFO every second so BSD dd reports progress to stderr
                def _siginfo_sender():
                    while self._proc and self._proc.poll() is None:
                        try:
                            self._proc.send_signal(signal.SIGINFO)
                        except (ProcessLookupError, OSError):
                            break
                        import time; time.sleep(1)
                threading.Thread(target=_siginfo_sender, daemon=True).start()
            buf = b""
            while True:
                ch = self._proc.stderr.read(1)
                if not ch:
                    break
                if ch in (b'\r', b'\n'):
                    line = buf.decode('utf-8', errors='replace').strip()
                    buf = b""
                    if line:
                        # Linux GNU dd:  "1073741824 bytes (1.1 GB) copied, 5.0 s, 215 MB/s"
                        m = re.match(
                            r'(\d+)\s+bytes.*?,\s+[\d.]+\s+s,\s+([\d.]+\s*\S+)', line)
                        if m:
                            self._bytes = int(m.group(1))
                            self._speed = m.group(2)
                        else:
                            # macOS BSD dd:  "1073741824 bytes transferred in 5.001 secs (214697... bytes/sec)"
                            m2 = re.match(
                                r'(\d+)\s+bytes\s+transferred\s+in\s+[\d.]+\s+secs\s+\(([\d.]+)\s+bytes/sec\)',
                                line)
                            if m2:
                                self._bytes = int(m2.group(1))
                                speed_bps = float(m2.group(2))
                                self._speed = fmt_size(int(speed_bps)) + "/s"
                            else:
                                m3 = re.match(r'(\d+)\s+bytes', line)
                                if m3:
                                    self._bytes = int(m3.group(1))
                else:
                    buf += ch
            rc = self._proc.wait()
            if rc != 0 and not self._cancelled:
                self._error = f"dd exited with code {rc}"
        except Exception as e:
            if not self._cancelled:
                self._error = str(e)
        self._done = True

    def _poll(self):
        if self._done:
            if self._error:
                messagebox.showerror("dd Error", self._error, parent=self)
            self.destroy()
            return
        if self._total > 0 and self._bytes > 0:
            pct = min(self._bytes / self._total, 1.0)
            self._bar["value"] = int(pct * 1000)
            self._lbl.config(
                text=f"{fmt_size(self._bytes)} / {fmt_size(self._total)}"
                     f"  ({pct*100:.1f}%)")
        elif self._bytes > 0:
            self._lbl.config(text=fmt_size(self._bytes))
        if self._speed:
            self._speed_lbl.config(text=f"Speed: {self._speed}")
        self.after(300, self._poll)

    def _cancel(self):
        self._cancelled = True
        if self._proc:
            self._proc.terminate()
        self.destroy()


# ─── Move / Grow dialogs ───────────────────────────────────────────────────────

class MovePartitionDialog(tk.Toplevel):
    """Warning + progress dialog for a physical partition move (block copy)."""

    def __init__(self, parent, dev: str, rdb, pi, preset_lo: int = None):
        super().__init__(parent)
        self.title("WARNING: Move Partition — Data Hazard")
        self.resizable(False, False)
        self.grab_set()
        self.transient(parent)
        self._dev       = dev
        self._rdb       = rdb
        self._pi        = pi
        self._preset_lo = preset_lo if preset_lo is not None else pi.low_cyl
        self.result = None      # set to new_lo (int) on success
        self._q: queue.Queue = queue.Queue()
        self._build()
        self.wait_window()

    def _build(self):
        f = tk.Frame(self, padx=14, pady=10)
        f.pack(fill="both", expand=True)

        tk.Label(f, justify="left", fg="#cc2200", font=("", 0, "bold"),
                 text=(
                     "WARNING:  MOVING A PARTITION COPIES ALL DATA ON DISK.\n\n"
                     f"Partition {self._pi.drive_name} "
                     f"(cyl {self._pi.low_cyl}\u2013{self._pi.high_cyl}) "
                     "will be physically copied to the\n"
                     "cylinder you enter below.\n\n"
                     "POWER LOSS OR CRASH DURING THIS PROCESS WILL\n"
                     "PERMANENTLY DESTROY YOUR DATA.  No rollback."
                 )).pack(anchor="w", pady=(0, 8))

        row = tk.Frame(f)
        row.pack(fill="x", pady=4)
        tk.Label(row, text="New start cylinder:").pack(side="left")
        self._cyl_var = tk.StringVar(value=str(self._preset_lo))
        self._cyl_entry = ttk.Entry(row, textvariable=self._cyl_var, width=10)
        self._cyl_entry.pack(side="left", padx=6)

        self._range_lbl = tk.Label(f, fg="#555555", justify="left", text="")
        self._range_lbl.pack(anchor="w")
        self._cyl_var.trace_add("write", self._upd_range)
        self._upd_range()

        self._backup_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(f, text=f"I have a current backup of {self._pi.drive_name}",
                        variable=self._backup_var).pack(anchor="w", pady=(8, 2))

        self._dd_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(f, text="Use dd (faster — large kernel-buffered transfers)",
                        variable=self._dd_var).pack(anchor="w", pady=(0, 4))

        self._prog_frame = tk.Frame(f)
        self._prog_bar   = ttk.Progressbar(self._prog_frame, mode="determinate",
                                           length=400, maximum=100)
        self._prog_bar.pack(fill="x")
        self._prog_lbl = tk.Label(self._prog_frame, text="", fg="#333333")
        self._prog_lbl.pack(anchor="w")

        bf = tk.Frame(f)
        bf.pack(fill="x", pady=(10, 0))
        self._btn_move   = ttk.Button(bf, text="Move Partition", width=16,
                                      command=self._on_move)
        self._btn_cancel = ttk.Button(bf, text="Cancel", width=10,
                                      command=self.destroy)
        self._btn_move.pack(side="left", padx=4)
        self._btn_cancel.pack(side="left", padx=4)

    def _upd_range(self, *_):
        try:
            new_lo = int(self._cyl_var.get())
        except ValueError:
            self._range_lbl.config(text="")
            return
        ok, result = _part_can_move(self._rdb, self._pi, new_lo)
        if ok:
            heads   = self._pi.surfaces    or self._rdb.heads
            sectors = self._pi.blk_per_trk or self._rdb.sectors
            cyl_cnt = self._pi.high_cyl - self._pi.low_cyl + 1
            phys    = cyl_cnt * heads * sectors
            self._range_lbl.config(
                text=f"New range: cyl {new_lo}\u2013{result}  ({phys} blocks)",
                fg="#006600")
        else:
            self._range_lbl.config(text=result, fg="#cc2200")

    def _on_move(self):
        if not self._backup_var.get():
            messagebox.showwarning("Backup Required",
                "Tick the backup confirmation checkbox before proceeding.",
                parent=self)
            return
        try:
            new_lo = int(self._cyl_var.get())
        except ValueError:
            messagebox.showerror("Invalid Input", "Enter a valid cylinder number.", parent=self)
            return
        ok, result = _part_can_move(self._rdb, self._pi, new_lo)
        if not ok:
            messagebox.showerror("Cannot Move", result, parent=self)
            return

        heads   = self._pi.surfaces    or self._rdb.heads
        sectors = self._pi.blk_per_trk or self._rdb.sectors
        phys    = (self._pi.high_cyl - self._pi.low_cyl + 1) * heads * sectors
        if not messagebox.askyesno("Confirm Move",
                f"Move {self._pi.drive_name} from cyl {self._pi.low_cyl}\u2013"
                f"{self._pi.high_cyl} to cyl {new_lo}\u2013{result}?\n\n"
                f"This will copy {phys} physical blocks.\n"
                "There is NO UNDO.  Continue?",
                parent=self, icon="warning"):
            return

        use_dd = self._dd_var.get()

        if use_dd:
            phys_old   = self._pi.low_cyl * heads * sectors
            phys_new   = new_lo           * heads * sectors
            phys_total = (self._pi.high_cyl - self._pi.low_cyl + 1) * heads * sectors
            overlapping = (phys_new > phys_old) and (phys_new < phys_old + phys_total)

            if not overlapping:
                # Use _DDProgressDialog for live progress via dd status=progress.
                cmd = ["dd", f"if={self._dev}", f"of={self._dev}", "bs=1M",
                       f"skip={phys_old * 512}", f"seek={phys_new * 512}",
                       f"count={phys_total * 512}",
                       "iflag=skip_bytes,count_bytes", "oflag=seek_bytes",
                       "conv=notrunc", "status=progress"]
                dlg = _DDProgressDialog(self, "Moving Partition…",
                                        cmd, phys_total * 512)
                if not dlg.success:
                    return
                # SFS metadata fixup (tiny — synchronous is fine)
                sfs_ok, sfs_msg = _sfs_fixup_after_move(
                    self._dev, self._rdb, self._pi, new_lo)
                if not sfs_ok:
                    messagebox.showwarning("SFS Fixup Warning", sfs_msg, parent=self)
                self.result = new_lo
                messagebox.showinfo("Partition Moved",
                    f"Partition {self._pi.drive_name} moved successfully.\n\n"
                    "Write RDB to disk to update the partition table, then reboot.",
                    parent=self)
                self.destroy()
                return

        # Python path (or overlapping-higher dd fallback): thread + poll progress.
        self._new_lo = new_lo
        self._use_dd = use_dd
        self._btn_move.config(state="disabled")
        self._btn_cancel.config(state="disabled")
        self._cyl_entry.config(state="disabled")
        self._prog_frame.pack(fill="x", pady=4)
        threading.Thread(target=self._run_move, daemon=True).start()
        self.after(100, self._poll)

    def _run_move(self):
        def cb(done, total, phase):
            self._q.put(("progress", done, total, phase))
        ok, msg = _part_move_data(self._dev, self._rdb, self._pi, self._new_lo, cb,
                                  use_dd=self._use_dd)
        self._q.put(("done", ok, msg))

    def _poll(self):
        while not self._q.empty():
            item = self._q.get_nowait()
            if item[0] == "progress":
                _, done, total, phase = item
                pct = int(done * 100 / total) if total else 0
                self._prog_bar["value"] = pct
                self._prog_lbl.config(text=f"{phase}  {pct}%")
            elif item[0] == "done":
                _, ok, msg = item
                self._prog_bar.config(mode="determinate", value=100 if ok else 0)
                if ok:
                    self.result = self._new_lo
                    messagebox.showinfo("Partition Moved",
                        f"Partition {self._pi.drive_name} moved successfully.\n\n"
                        f"{msg}\n\n"
                        "Write RDB to disk to update the partition table, then reboot.",
                        parent=self)
                else:
                    messagebox.showerror("Move Failed",
                        f"Move FAILED:\n{msg}\n\n"
                        "Data may be partially written.\n"
                        "Restore from backup before rebooting.",
                        parent=self)
                self.destroy()
                return
        self.after(100, self._poll)


class GrowPartitionDialog(tk.Toplevel):
    """Dialog for extending a partition's high cylinder."""

    def __init__(self, parent, rdb, pi):
        super().__init__(parent)
        self.title(f"Grow Partition \u2014 {pi.drive_name}")
        self.resizable(False, False)
        self.grab_set()
        self.transient(parent)
        self._rdb = rdb
        self._pi  = pi
        self.result = None   # set to new_hi (int) on OK
        self._build()
        self.wait_window()

    def _build(self):
        f = tk.Frame(self, padx=14, pady=12)
        f.pack(fill="both", expand=True)

        heads   = self._pi.surfaces    or self._rdb.heads
        sectors = self._pi.blk_per_trk or self._rdb.sectors
        cur_sz  = fmt_size(self._pi.size_bytes)
        tk.Label(f, justify="left",
                 text=f"Current range: cyl {self._pi.low_cyl}\u2013{self._pi.high_cyl}  ({cur_sz})"
                 ).pack(anchor="w", pady=(0, 4))

        max_hi = self._rdb.hicyl
        for other in self._rdb.partitions:
            if other is self._pi:
                continue
            if other.low_cyl > self._pi.high_cyl:
                max_hi = min(max_hi, other.low_cyl - 1)
        tk.Label(f, text=f"Maximum available: cyl {max_hi}",
                 fg="#333333").pack(anchor="w", pady=(0, 8))

        row = tk.Frame(f)
        row.pack(fill="x", pady=4)
        tk.Label(row, text="New high cylinder:").pack(side="left")
        self._hi_var = tk.StringVar(value=str(min(self._pi.high_cyl + 1, max_hi)))
        ttk.Entry(row, textvariable=self._hi_var, width=10).pack(side="left", padx=6)

        self._size_lbl = tk.Label(f, fg="#333333", text="")
        self._size_lbl.pack(anchor="w")
        self._hi_var.trace_add("write", self._upd_size)
        self._upd_size()

        if _ffs_is_type(self._pi.dos_type):
            notice = "FFS filesystem grow will be offered after confirmation."
        elif _pfs_is_type(self._pi.dos_type):
            notice = "PFS filesystem grow will be offered after confirmation."
        elif _sfs_is_type(self._pi.dos_type):
            notice = ("SFS: only the RDB entry will be updated.\n"
                      "Run SFScheck after reboot to expand the filesystem.")
        else:
            notice = "Only the RDB partition entry will be updated."
        tk.Label(f, text=notice, fg="#555577", justify="left",
                 wraplength=360).pack(anchor="w", pady=(6, 0))

        bf = tk.Frame(f)
        bf.pack(fill="x", pady=(12, 0))
        ttk.Button(bf, text="Grow",   width=10, command=self._ok).pack(side="left", padx=4)
        ttk.Button(bf, text="Cancel", width=10, command=self.destroy).pack(side="left", padx=4)

    def _upd_size(self, *_):
        try:
            new_hi = int(self._hi_var.get())
        except ValueError:
            self._size_lbl.config(text="")
            return
        ok_r = _part_can_grow(self._rdb, self._pi, new_hi)
        if ok_r[0]:
            heads   = self._pi.surfaces    or self._rdb.heads
            sectors = self._pi.blk_per_trk or self._rdb.sectors
            cyls    = new_hi - self._pi.low_cyl + 1
            new_sz  = fmt_size(cyls * heads * sectors * 512)
            self._size_lbl.config(
                text=f"New range: cyl {self._pi.low_cyl}\u2013{new_hi}  ({new_sz})",
                fg="#006600")
        else:
            self._size_lbl.config(text=ok_r[1], fg="#cc2200")

    def _ok(self):
        try:
            new_hi = int(self._hi_var.get())
        except ValueError:
            messagebox.showerror("Invalid Input", "Enter a valid cylinder number.", parent=self)
            return
        ok_r = _part_can_grow(self._rdb, self._pi, new_hi)
        if not ok_r[0]:
            messagebox.showerror("Cannot Grow", ok_r[1], parent=self)
            return
        self.result = new_hi
        self.destroy()


# ─── Main window ───────────────────────────────────────────────────────────────

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Amiga RDB Disk Partitioner")
        style = ttk.Style()
        style.configure('Big.TCheckbutton', indicatorsize=28)
        self.geometry("1100x700")
        self.minsize(900, 540)
        self._disks       = []
        self._image_files = []   # user-opened .img files treated as disks
        self._cur_disk = None
        self._rdb: Optional[RDBInfo] = None
        self._drag: Optional[dict] = None       # create drag  {"start": cyl, "end": cyl}
        self._part_drag: Optional[dict] = None  # move/grow drag
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
        fm.add_command(label="Open Image as Disk…",  command=self._do_open_image)
        fm.add_command(label="Create Blank Image…",  command=self._do_create_image)
        fm.add_separator()
        fm.add_command(label="Quit", command=self.quit)
        mb.add_cascade(label="File", menu=fm)
        tm = tk.Menu(mb, tearoff=0)
        tm.add_command(label="Backup RDB Blocks…",          command=self._do_backup_rdb)
        tm.add_command(label="Restore RDB Blocks…",         command=self._do_restore_rdb)
        tm.add_command(label="Backup RDB Extended…",        command=self._do_backup_rdb_extended)
        tm.add_command(label="Restore RDB Extended…",       command=self._do_restore_rdb_extended)
        tm.add_separator()
        tm.add_command(label="Image Disk to File…", command=self._do_image_disk)
        tm.add_command(label="Restore Disk from Image…", command=self._do_restore_image)
        tm.add_separator()
        tm.add_command(label="Add Filesystem to RDB…",    command=self._do_add_filesystem)
        tm.add_command(label="Remove Selected Filesystem", command=self._do_remove_filesystem)
        mb.add_cascade(label="Tools", menu=tm)
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

        # Status bar + buttons packed BEFORE the expanding partition list
        # so they are always visible regardless of window height
        self._status = tk.StringVar(value="Select a disk to begin.")
        ttk.Label(right, textvariable=self._status, relief="sunken",
                  anchor="w").pack(side="bottom", fill="x", padx=4, pady=(0,2))

        bf = ttk.Frame(right)
        bf.pack(side="bottom", fill="x", padx=4, pady=4)
        for col in range(5):
            bf.columnconfigure(col, weight=1)

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
        self._btn_move  = ttk.Button(bf, text="Move Partition",   command=self._do_move,
                                      state="disabled")
        self._btn_grow  = ttk.Button(bf, text="Grow Partition",   command=self._do_grow,
                                      state="disabled")
        self._btn_init.grid( row=0, column=0, sticky="ew", padx=2)
        self._btn_add.grid(  row=0, column=1, sticky="ew", padx=2)
        self._btn_edit.grid( row=0, column=2, sticky="ew", padx=2)
        self._btn_del.grid(  row=0, column=3, sticky="ew", padx=2)
        self._btn_write.grid(row=0, column=4, sticky="ew", padx=2)
        self._btn_move.grid( row=1, column=0, columnspan=2, sticky="ew", padx=2, pady=(2, 0))
        self._btn_grow.grid( row=1, column=2, columnspan=3, sticky="ew", padx=2, pady=(2, 0))

        # Filesystem list — packed before partition list (above it, below buttons)
        fs_lf = ttk.LabelFrame(right, text="Filesystems")
        fs_lf.pack(side="bottom", fill="x", padx=4, pady=2)

        fscols = ("dostype", "name", "version", "size")
        self._fstree = ttk.Treeview(fs_lf, columns=fscols, show="headings",
                                    selectmode="browse", height=3)
        for col, hdr, w in [("dostype","DosType",90), ("name","Name",110),
                             ("version","Version",70), ("size","Binary",80)]:
            self._fstree.heading(col, text=hdr)
            self._fstree.column(col, width=w, minwidth=w, anchor="w")
        fssb = ttk.Scrollbar(fs_lf, orient="vertical", command=self._fstree.yview)
        self._fstree.configure(yscrollcommand=fssb.set)
        self._fstree.pack(side="left", fill="x", expand=True, padx=(6,0), pady=4)
        fssb.pack(side="left", fill="y", pady=4, padx=(0,4))

        # Partition list — packed last so expand=True only claims leftover space
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

    # ── Disk list ─────────────────────────────────────────────────────────────
    def _refresh_disks(self):
        self._disks = get_disks()
        # Drop image files that have disappeared from disk
        self._image_files = [d for d in self._image_files if os.path.exists(d["path"])]
        for row in self._dtree.get_children():
            self._dtree.delete(row)
        for d in self._disks:
            self._dtree.insert("", "end", iid=d["path"],
                               values=(d["name"], fmt_size(d["size"]), d["model"]))
        for d in self._image_files:
            self._dtree.insert("", "end", iid=d["path"],
                               values=(d["name"], fmt_size(d["size"]), d["model"]),
                               tags=("imgfile",))
        self._dtree.tag_configure("imgfile", foreground="#0055cc")
        total = len(self._disks) + len(self._image_files)
        if not total:
            self._status.set("No disks found. Try running as root (sudo).")
        else:
            self._status.set(f"{len(self._disks)} disk(s) found. Select one.")

    def _on_disk_sel(self, _=None):
        sel = self._dtree.selection()
        if not sel:
            return
        self._cur_disk = next(
            (d for d in self._disks + self._image_files if d["path"] == sel[0]), None)
        if not self._cur_disk:
            return
        dev = self._cur_disk["path"]
        self._status.set(f"Reading {dev}…")
        self.update_idletasks()

        self._rdb = read_rdb(dev)

        if _has_pc_partitioning(dev):
            messagebox.showwarning(
                "PC Partitioning Detected",
                f"{dev} contains a PC-style (MBR) partition table.\n\n"
                "Writing an Amiga RDB to this disk will DESTROY all existing "
                "partitions and data on it.\n\n"
                "Make sure you have a backup before proceeding.")

        self._info["device"].config(text=dev, foreground="black")
        self._info["model"].config(text=self._cur_disk["model"] or "Unknown", foreground="black")
        self._info["size"].config(text=fmt_size(self._cur_disk["size"]), foreground="black")

        if self._rdb:
            # Check if physical disk is larger than RDB geometry describes
            cyl_bytes = self._rdb.heads * self._rdb.sectors * 512
            if cyl_bytes > 0:
                phys_cyls = self._cur_disk["size"] // cyl_bytes
                if phys_cyls > self._rdb.cylinders:
                    rdb_size  = fmt_size(self._rdb.cylinders * cyl_bytes)
                    phys_size = fmt_size(self._cur_disk["size"])
                    ans = messagebox.askyesno(
                        "Disk Larger Than RDB",
                        f"The physical disk ({phys_size}) is larger than the RDB geometry describes ({rdb_size}).\n\n"
                        f"RDB cylinder count: {self._rdb.cylinders}  →  physical: {phys_cyls}\n\n"
                        f"Expand RDB geometry to use the full disk?\n"
                        f"(You can then add a new partition in the free space.)")
                    if ans:
                        self._rdb.cylinders = phys_cyls
                        self._rdb.hicyl     = phys_cyls - 1

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
        self._btn_move.config(state="disabled")
        self._btn_grow.config(state="disabled")
        self._refresh_parts()
        self._refresh_filesystems()
        self._draw_map()

    # ── Partition list ────────────────────────────────────────────────────────
    def _refresh_parts(self):
        if self._rdb:
            self._rdb.partitions.sort(key=lambda p: p.low_cyl)

        # Remember current selection index so we can restore it
        cur = self._ptree.selection()
        prev_idx = int(cur[0]) if cur else None

        for row in self._ptree.get_children():
            self._ptree.delete(row)
        if not self._rdb:
            self._on_part_sel()
            return
        for i, p in enumerate(self._rdb.partitions):
            flag_parts = []
            if not (p.flags & 2): flag_parts.append("Boot")
            if not (p.flags & 4): flag_parts.append("AM")
            if p.flags & 8:       flag_parts.append("SCSI")
            flags = ",".join(flag_parts) if flag_parts else f"0x{p.flags:02X}"
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
        has_dev = bool(self._cur_disk)
        self._btn_edit.config(state="normal" if has_sel else "disabled")
        self._btn_del.config( state="normal" if has_sel else "disabled")
        self._btn_move.config(state="normal" if (has_sel and has_dev) else "disabled")
        self._btn_grow.config(state="normal" if (has_sel and has_dev) else "disabled")
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

        # Ghost for move/grow drag
        if self._part_drag is not None:
            pd   = self._part_drag
            glo  = pd["ghost_lo"]
            ghi  = pd["ghost_hi"]
            gx1  = x_of(glo)
            gx2  = x_of(ghi + 1)
            if gx2 < gx1 + 2:
                gx2 = gx1 + 2
            # Dim original position
            ox1 = x_of(pd["orig_lo"])
            ox2 = x_of(pd["orig_hi"] + 1)
            if ox2 < ox1 + 2: ox2 = ox1 + 2
            c.create_rectangle(ox1, y1, ox2, y2,
                                fill="#223344", outline="#556677", dash=(3, 3), width=1)
            # Ghost at new position
            ghost_col = "#ff9900" if pd["mode"] == "move" else "#00cc88"
            c.create_rectangle(gx1, y1, gx2, y2,
                                fill="", outline=ghost_col, dash=(4, 2), width=2)
            gpw = gx2 - gx1
            if gpw > 28:
                cyls = ghi - glo + 1
                sz_str = fmt_size(cyls * self._rdb.heads * self._rdb.sectors * 512)
                lbl = f"{glo}\u2013{ghi}  {sz_str}"
                c.create_text((gx1 + gx2) / 2, (y1 + y2) / 2,
                               text=lbl, fill=ghost_col, font=("", 8, "bold"))

        # Draw resize handle on selected partition's right edge
        sel = self._ptree.selection()
        if sel and not self._part_drag:
            si = int(sel[0])
            if 0 <= si < len(self._rdb.partitions):
                sp   = self._rdb.partitions[si]
                ex   = int(x_of(sp.high_cyl + 1))
                hmid = (y1 + y2) // 2
                hw   = 5
                c.create_rectangle(ex - hw, hmid - 8, ex + hw, hmid + 8,
                                    fill="#00cc88", outline="white", width=1)

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

    def _map_hit_test(self, x: int) -> tuple:
        """Return (kind, idx) where kind is 'free'|'body'|'edge', idx is partition index.
        'edge' means within 8px of a partition's right edge (grow handle)."""
        if not self._rdb:
            return ("free", -1)
        M  = 6
        bw = self._canvas.winfo_width() - 2 * M
        total = self._rdb.hicyl - self._rdb.locyl + 1
        EDGE_PX = 8

        def x_of(cyl):
            t = max(0.0, min(1.0, (cyl - self._rdb.locyl) / total))
            return M + t * bw

        for i, p in enumerate(self._rdb.partitions):
            ex  = x_of(p.high_cyl + 1)
            sx  = x_of(p.low_cyl)
            if abs(x - ex) <= EDGE_PX:
                return ("edge", i)
            if abs(x - sx) <= EDGE_PX:
                return ("left_edge", i)
            if sx <= x <= ex:
                return ("body", i)
        return ("free", -1)

    def _on_map_hover(self, event):
        if not self._rdb:
            self._canvas.config(cursor=""); return
        H = self._canvas.winfo_height()
        if not (6 <= event.y <= H - 18):
            self._canvas.config(cursor=""); return
        kind, _ = self._map_hit_test(event.x)
        if kind == "free":
            self._canvas.config(cursor="crosshair")
        elif kind == "edge":
            self._canvas.config(cursor="sb_h_double_arrow")
        elif kind == "left_edge":
            self._canvas.config(cursor="X_cursor")
        else:
            self._canvas.config(cursor="fleur")

    def _on_map_press(self, event):
        if not self._rdb:
            return
        H = self._canvas.winfo_height()
        if not (6 <= event.y <= H - 18):
            return
        kind, idx = self._map_hit_test(event.x)
        if kind == "free":
            cyl = self._map_x_to_cyl(event.x)
            snap = self._rdb.locyl
            for p in self._rdb.partitions:
                if p.high_cyl < cyl:
                    snap = max(snap, p.high_cyl + 1)
            self._drag = {"start": snap, "end": snap}
            self._draw_map()
            return
        # Select the partition
        self._ptree.selection_set(str(idx))
        self._ptree.focus(str(idx))
        self._ptree.see(str(idx))
        self._on_part_sel()
        p = self._rdb.partitions[idx]
        if kind == "left_edge":
            messagebox.showinfo(
                "Cannot Resize From Start",
                "Filesystem resize is only possible when the start cylinder is left "
                "unchanged.\n\nTo grow a partition, drag the right edge instead.",
                parent=self)
            return
        if kind == "edge":
            self._part_drag = {
                "mode":     "grow",
                "idx":      idx,
                "orig_lo":  p.low_cyl,
                "orig_hi":  p.high_cyl,
                "ghost_lo": p.low_cyl,
                "ghost_hi": p.high_cyl,
            }
        else:
            self._part_drag = {
                "mode":       "move",
                "idx":        idx,
                "orig_lo":    p.low_cyl,
                "orig_hi":    p.high_cyl,
                "ghost_lo":   p.low_cyl,
                "ghost_hi":   p.high_cyl,
                "press_cyl":  self._map_x_to_cyl(event.x),
            }
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
        if self._part_drag is not None:
            pd  = self._part_drag
            idx = pd["idx"]
            p   = self._rdb.partitions[idx]
            raw = self._map_x_to_cyl(event.x)

            if pd["mode"] == "grow":
                # Only the right edge moves; must stay > low_cyl
                lo    = pd["orig_lo"]
                min_hi = lo   # keep at least 1 cylinder
                max_hi = self._rdb.hicyl
                for other in self._rdb.partitions:
                    if other is p: continue
                    if other.low_cyl > lo:
                        max_hi = min(max_hi, other.low_cyl - 1)
                pd["ghost_hi"] = max(min_hi, min(max_hi, raw))
                cyls = pd["ghost_hi"] - lo + 1
                sz   = cyls * self._rdb.heads * self._rdb.sectors * 512
                self._status.set(
                    f"Grow {p.drive_name}: cyl {lo}\u2013{pd['ghost_hi']}  "
                    f"({cyls} cyl, {fmt_size(sz)})")

            else:  # move
                cyl_count = pd["orig_hi"] - pd["orig_lo"] + 1
                offset    = raw - pd["press_cyl"]
                new_lo    = pd["orig_lo"] + offset
                new_hi    = new_lo + cyl_count - 1
                # Clamp within disk bounds
                if new_lo < self._rdb.locyl:
                    new_lo = self._rdb.locyl
                    new_hi = new_lo + cyl_count - 1
                if new_hi > self._rdb.hicyl:
                    new_hi = self._rdb.hicyl
                    new_lo = new_hi - cyl_count + 1
                # Clamp to avoid overlapping other partitions
                for other in self._rdb.partitions:
                    if other is p: continue
                    if other.high_cyl < pd["orig_lo"] and other.high_cyl >= new_lo:
                        new_lo = other.high_cyl + 1
                        new_hi = new_lo + cyl_count - 1
                    if other.low_cyl > pd["orig_hi"] and other.low_cyl <= new_hi:
                        new_hi = other.low_cyl - 1
                        new_lo = new_hi - cyl_count + 1
                new_lo = max(self._rdb.locyl, new_lo)
                new_hi = new_lo + cyl_count - 1
                pd["ghost_lo"] = new_lo
                pd["ghost_hi"] = new_hi
                sz = cyl_count * self._rdb.heads * self._rdb.sectors * 512
                self._status.set(
                    f"Move {p.drive_name}: cyl {new_lo}\u2013{new_hi}  ({fmt_size(sz)})")

            self._draw_map()
            return

        if self._drag is None:
            return
        raw = self._map_x_to_cyl(event.x)
        self._drag["end"] = self._clamp_drag_end(self._drag["start"], raw)
        lo = min(self._drag["start"], self._drag["end"])
        hi = max(self._drag["start"], self._drag["end"])
        cyls = hi - lo + 1
        sz = cyls * self._rdb.heads * self._rdb.sectors * 512
        self._status.set(
            f"New partition: cyls {lo}\u2013{hi}  "
            f"({cyls} cylinder{'s' if cyls != 1 else ''}, {fmt_size(sz)})")
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
        # ── move/grow drag released ────────────────────────────────────────────
        if self._part_drag is not None:
            pd      = self._part_drag
            idx     = pd["idx"]
            pi      = self._rdb.partitions[idx]
            mode    = pd["mode"]
            glo     = pd["ghost_lo"]
            ghi     = pd["ghost_hi"]
            orig_lo = pd["orig_lo"]
            orig_hi = pd["orig_hi"]
            self._part_drag = None
            self._draw_map()

            if mode == "grow" and ghi != orig_hi:
                ok_r = _part_can_grow(self._rdb, pi, ghi)
                if not ok_r[0]:
                    messagebox.showerror("Cannot Grow", ok_r[1], parent=self)
                    return
                pi.high_cyl = ghi
                self._refresh_parts()
                self._draw_map()
                dev = self._cur_disk["path"] if self._cur_disk else None
                if dev:
                    if _ffs_is_type(pi.dos_type):
                        if messagebox.askyesno("Grow FFS Filesystem",
                                f"Partition {pi.drive_name} extended to cyl {ghi}.\n\n"
                                "EXPERIMENTAL: Grow the FFS filesystem to match?\n\n"
                                "This writes FFS bitmap blocks directly to disk.\n"
                                "Always have a backup before proceeding.",
                                parent=self, icon="warning"):
                            ok, msg = _ffs_grow(dev, self._rdb, pi, orig_hi)
                            if ok:
                                messagebox.showinfo("FFS Grown",
                                    f"FFS filesystem grown.\n\n{msg}\n\n"
                                    "Write RDB, then reboot.", parent=self)
                            else:
                                messagebox.showerror("FFS Grow Failed", msg, parent=self)
                    elif _pfs_is_type(pi.dos_type):
                        if messagebox.askyesno("Grow PFS Filesystem",
                                f"Partition {pi.drive_name} extended to cyl {ghi}.\n\n"
                                "EXPERIMENTAL: Grow the PFS filesystem to match?\n\n"
                                "This updates PFS rootblock metadata on disk.",
                                parent=self, icon="warning"):
                            ok, msg = _pfs_grow(dev, self._rdb, pi, orig_hi)
                            if ok:
                                messagebox.showinfo("PFS Grown",
                                    f"PFS filesystem grown.\n\n{msg}\n\n"
                                    "Write RDB, then reboot.", parent=self)
                            else:
                                messagebox.showerror("PFS Grow Failed", msg, parent=self)
                self._status.set(
                    f"Partition '{pi.drive_name}' grown to cyl {ghi}. "
                    "Write to disk to save.")

            elif mode == "move" and glo != orig_lo:
                if not self._cur_disk:
                    messagebox.showwarning("No Device",
                        "Open a disk image or device first to move partitions.", parent=self)
                    return
                dev = self._cur_disk["path"]
                dlg = MovePartitionDialog(self, dev, self._rdb, pi, preset_lo=glo)
                if dlg.result is not None:
                    cyl_cnt     = pi.high_cyl - pi.low_cyl + 1
                    pi.low_cyl  = dlg.result
                    pi.high_cyl = dlg.result + cyl_cnt - 1
                    self._status.set(
                        f"Partition '{pi.drive_name}' moved to cyl "
                        f"{pi.low_cyl}\u2013{pi.high_cyl}. Write to disk to update RDB.")
                self._refresh_parts()
                self._draw_map()
            return

        # ── create drag released ───────────────────────────────────────────────
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
        self._btn_del.config( state="disabled")
        self._btn_move.config(state="disabled")
        self._btn_grow.config(state="disabled")
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
        n_fs    = len(rdb.filesystems)

        # Block layout: RDSK@0, PART@1…, FSHD+LSEG after
        rdsk_blk  = 0
        part_blks = list(range(1, 1 + n_parts))
        next_blk  = 1 + n_parts

        # Pre-calculate FSHD and LSEG block numbers
        fshd_blks      = []
        lseg_runs      = []   # list of (first_lseg_blk, n_lseg)
        for fs in rdb.filesystems:
            fshd_blks.append(next_blk); next_blk += 1
            n_lseg = max(1, math.ceil(len(fs.data) / LSEG_DATA)) if fs.data else 0
            lseg_runs.append((next_blk, n_lseg))
            next_blk += n_lseg

        rdb.rdbblock_hi   = max(15, next_blk - 1)
        rdb.part_list_blk = part_blks[0] if part_blks else END_MARK
        rdb.fshdr_list    = fshd_blks[0] if fshd_blks else END_MARK

        errors = []

        # Open once, write all RDB blocks, fsync once at the end.
        try:
            with open(dev, "r+b") as fh:
                def write_at(blk, data):
                    try:
                        fh.seek(blk * 512)
                        fh.write(data)
                        return True
                    except OSError:
                        return False

                if not write_at(rdsk_blk, build_rdsk_block(rdb)):
                    errors.append(f"Failed to write RDSK block at block {rdsk_blk}")

                for i, (p, blk) in enumerate(zip(rdb.partitions, part_blks)):
                    p.block_num = blk
                    p.next_part = part_blks[i+1] if i+1 < n_parts else END_MARK
                    if not write_at(blk, build_part_block(p, rdb.heads, rdb.sectors)):
                        errors.append(f"Failed to write PART block for {p.drive_name}")

                for i, (fs, fshd_blk, (first_lseg, n_lseg)) in enumerate(
                        zip(rdb.filesystems, fshd_blks, lseg_runs)):
                    next_fshd = fshd_blks[i+1] if i+1 < n_fs else END_MARK
                    first_lseg_or_end = first_lseg if n_lseg > 0 else END_MARK
                    if not write_at(fshd_blk,
                                    build_fshd_block(fs, next_fshd, first_lseg_or_end)):
                        errors.append(f"Failed to write FSHD block for {fs.label}")
                    for blk_num, blk_data in build_lseg_blocks(fs, first_lseg):
                        if not write_at(blk_num, blk_data):
                            errors.append(f"Failed to write LSEG block {blk_num} for {fs.label}")

                fh.flush()
        except OSError as e:
            errors.append(f"Cannot open {dev} for writing: {e}")

        if errors:
            messagebox.showerror("Write Errors", "\n".join(errors), parent=self)
        else:
            part_info = ", ".join(str(b) for b in part_blks) or "none"
            fs_info   = ", ".join(str(b) for b in fshd_blks) or "none"
            messagebox.showinfo("Success",
                f"Amiga RDB written to {dev}!\n\n"
                f"  RDSK block: {rdsk_blk}\n"
                f"  PART block(s): {part_info}\n"
                f"  FSHD block(s): {fs_info}\n\n"
                f"Reboot the Amiga, then format each partition from AmigaOS.",
                parent=self)
            self._info["rdb"].config(
                text=f"RDB written to disk ({n_parts} partition(s))",
                foreground="#007700")
            self._status.set(f"RDB successfully written to {dev}.")

    # ── Filesystem list ───────────────────────────────────────────────────────
    def _refresh_filesystems(self):
        for row in self._fstree.get_children():
            self._fstree.delete(row)
        if not self._rdb:
            return
        for i, fs in enumerate(self._rdb.filesystems):
            self._fstree.insert("", "end", iid=str(i),
                                values=(f"0x{fs.dos_type:08X}",
                                        fs.label,
                                        fs.version_str,
                                        fmt_size(len(fs.data))))

    def _do_add_filesystem(self):
        if not self._rdb:
            messagebox.showerror("No RDB", "Load or initialize an RDB first.")
            return
        dlg = AddFilesystemDialog(self)
        if not dlg.result:
            return
        fs = dlg.result
        # Replace if same DosType already loaded
        self._rdb.filesystems = [x for x in self._rdb.filesystems
                                  if x.dos_type != fs.dos_type]
        self._rdb.filesystems.append(fs)
        self._refresh_filesystems()
        self._status.set(
            f"Filesystem {fs.label} added ({fmt_size(len(fs.data))}). "
            f"Write to disk to save.")

    def _do_remove_filesystem(self):
        sel = self._fstree.selection()
        if not sel or not self._rdb:
            messagebox.showinfo("No Selection", "Select a filesystem in the list first.")
            return
        idx = int(sel[0])
        fs  = self._rdb.filesystems[idx]
        if not messagebox.askyesno("Remove Filesystem",
                f"Remove filesystem {fs.label} from the RDB?\n\n"
                "Write to disk afterwards to make this permanent."):
            return
        self._rdb.filesystems.pop(idx)
        self._refresh_filesystems()
        self._status.set(f"Filesystem {fs.label} removed. Write to disk to save.")

    def _do_open_image(self):
        path = filedialog.askopenfilename(
            title="Open Disk Image as Drive",
            filetypes=[("Disk image", "*.img *.hdf *.bin"),
                       ("All files", "*.*")])
        if not path:
            return
        try:
            size = os.path.getsize(path)
        except OSError as e:
            messagebox.showerror("Error", str(e))
            return
        if size == 0:
            messagebox.showerror("Error", "Image file is empty.")
            return
        name = os.path.basename(path)
        d = {"name": name, "path": path, "size": size, "model": path}
        # Replace if already open
        self._image_files = [x for x in self._image_files if x["path"] != path]
        self._image_files.append(d)
        if self._dtree.exists(path):
            self._dtree.delete(path)
        self._dtree.insert("", "end", iid=path,
                           values=(name, fmt_size(size), path),
                           tags=("imgfile",))
        self._dtree.tag_configure("imgfile", foreground="#0055cc")
        self._dtree.selection_set(path)
        self._dtree.see(path)
        self._on_disk_sel()

    def _do_create_image(self):
        dlg = CreateImageDialog(self)
        if dlg.result is None:
            return
        path, total = dlg.result
        # Write zeros in 1 MB chunks with a simple progress window
        CHUNK = 1024 * 1024
        written = 0
        try:
            with open(path, "wb") as fh:
                while written < total:
                    chunk = min(CHUNK, total - written)
                    fh.write(b"\x00" * chunk)
                    written += chunk
        except OSError as e:
            messagebox.showerror("Error", f"Could not create image:\n{e}")
            try:
                os.remove(path)
            except OSError:
                pass
            return
        # Add to device list exactly like _do_open_image
        name = os.path.basename(path)
        d = {"name": name, "path": path, "size": total, "model": path}
        self._image_files = [x for x in self._image_files if x["path"] != path]
        self._image_files.append(d)
        if self._dtree.exists(path):
            self._dtree.delete(path)
        self._dtree.insert("", "end", iid=path,
                           values=(name, fmt_size(total), path),
                           tags=("imgfile",))
        self._dtree.tag_configure("imgfile", foreground="#0055cc")
        self._dtree.selection_set(path)
        self._dtree.see(path)
        self._on_disk_sel()

    def _do_backup_rdb(self):
        if not self._cur_disk:
            messagebox.showerror("No Disk Selected", "Select a disk first.")
            return
        dev = self._cur_disk["path"]
        hi = self._rdb.rdbblock_hi if self._rdb else RDB_SCAN_LIMIT - 1
        path = filedialog.asksaveasfilename(
            title="Save RDB Backup",
            defaultextension=".rdb",
            filetypes=[("RDB backup", "*.rdb"), ("Binary", "*.bin"), ("All files", "*.*")])
        if not path:
            return
        blocks = []
        for blk in range(hi + 1):
            data = _read_block(dev, blk)
            if data is None:
                messagebox.showerror("Read Error", f"Failed to read block {blk} from {dev}.")
                return
            blocks.append(data)
        try:
            with open(path, "wb") as f:
                for b in blocks:
                    f.write(b)
        except OSError as e:
            messagebox.showerror("Save Error", str(e))
            return
        messagebox.showinfo("Backup Complete",
            f"Saved {hi + 1} block(s) (blocks 0–{hi}) to:\n{path}")
        self._status.set(f"RDB backup saved: {os.path.basename(path)}")

    def _do_restore_rdb(self):
        if not self._cur_disk:
            messagebox.showerror("No Disk Selected", "Select a disk first.")
            return
        dev = self._cur_disk["path"]
        path = filedialog.askopenfilename(
            title="Open RDB Backup",
            filetypes=[("RDB backup", "*.rdb"), ("Binary", "*.bin"), ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, "rb") as f:
                raw = f.read()
        except OSError as e:
            messagebox.showerror("Open Error", str(e))
            return
        if len(raw) < 512 or len(raw) % 512 != 0:
            messagebox.showerror("Invalid File", "File size is not a multiple of 512 bytes.")
            return
        if struct.unpack_from(">I", raw, 0)[0] != RDSK_ID:
            messagebox.showerror("Invalid File",
                "First block is not an Amiga RDSK block.\n"
                "This does not appear to be a valid RDB backup.")
            return
        n_blocks = len(raw) // 512
        if not messagebox.askyesno("Confirm Restore",
                f"⚠  WARNING  ⚠\n\n"
                f"This will restore {n_blocks} block(s) to:\n\n"
                f"  {dev}   ({fmt_size(self._cur_disk['size'])})\n\n"
                f"This overwrites the existing RDB area on the disk.\n\n"
                f"Continue?", icon="warning"):
            return
        if not os.access(dev, os.W_OK):
            messagebox.showerror("Permission Denied",
                f"Cannot write to {dev}.\n\nRun this program with sudo.")
            return
        for i in range(n_blocks):
            if not _write_block(dev, i, raw[i*512:(i+1)*512]):
                messagebox.showerror("Write Error", f"Failed to write block {i} to {dev}.")
                return
        messagebox.showinfo("Restore Complete",
            f"Restored {n_blocks} block(s) to {dev}.\n\n"
            f"Re-select the disk to reload the RDB.")
        self._status.set(f"RDB restored from {os.path.basename(path)}. Re-select disk to refresh.")

    # ── ERDB extended backup / restore ──────────────────────────────────────────
    # Format (compatible with DiskPart):
    #   32-byte header: 8 × big-endian uint32
    #     [0] magic  = 0x45524442 ('ERDB')
    #     [1] version = 1
    #     [2] block_lo
    #     [3] block_size (512)
    #     [4] num_blocks
    #     [5..7] reserved (0)
    #   Then num_blocks × 512 bytes of raw block data.

    _ERDB_MAGIC   = 0x45524442
    _ERDB_VERSION = 1
    _ERDB_HDR_SZ  = 32

    def _do_backup_rdb_extended(self):
        if not self._rdb or not self._rdb.valid:
            messagebox.showerror("No RDB", "Load a disk with a valid RDB first.",
                                 parent=self); return
        if not self._cur_disk:
            messagebox.showerror("No Disk Selected", "Select a disk first.",
                                 parent=self); return
        dev      = self._cur_disk["path"]
        block_lo = self._rdb.rdbblock_lo
        block_hi = self._rdb.rdbblock_hi
        num_blocks = block_hi - block_lo + 1

        model = (self._cur_disk.get("model") or "disk").strip()
        safe  = re.sub(r"[^A-Za-z0-9_-]", "_", model).strip("_") or "disk"
        suggested = f"RDB_extended_{safe}.backup"

        path = filedialog.asksaveasfilename(
            title="Save Extended RDB Backup",
            defaultextension=".backup",
            initialfile=suggested,
            filetypes=[("ERDB backup", "*.backup"), ("All files", "*.*")],
            parent=self)
        if not path:
            return

        hdr = struct.pack(">8I",
            self._ERDB_MAGIC, self._ERDB_VERSION,
            block_lo, 512, num_blocks, 0, 0, 0)
        try:
            with open(path, "wb") as f:
                f.write(hdr)
                for blk in range(block_lo, block_hi + 1):
                    data = _read_block(dev, blk)
                    if data is None:
                        messagebox.showerror("Read Error",
                            f"Failed to read block {blk} from {dev}.", parent=self)
                        return
                    f.write(data)
        except OSError as e:
            messagebox.showerror("Save Error", str(e), parent=self); return

        messagebox.showinfo("Extended Backup Complete",
            f"Extended RDB backup saved.\n"
            f"{num_blocks} blocks (blocks {block_lo}–{block_hi})\n\n"
            f"{path}", parent=self)
        self._status.set(f"Extended RDB backup saved: {os.path.basename(path)}")

    def _do_restore_rdb_extended(self):
        if not self._cur_disk:
            messagebox.showerror("No Disk Selected", "Select a disk first.",
                                 parent=self); return
        dev = self._cur_disk["path"]

        if not messagebox.askyesno("Extended Restore — WARNING",
                "WARNING: This will overwrite multiple blocks\n"
                "(RDB, partitions, filesystems) on the disk!\n\n"
                "An incorrect backup WILL destroy the disk layout.\n"
                "Ensure the backup matches THIS disk.\n\n"
                "Are you absolutely sure?",
                icon="warning", parent=self):
            return

        path = filedialog.askopenfilename(
            title="Select Extended RDB Backup File",
            filetypes=[("ERDB backup", "*.backup"), ("All files", "*.*")],
            parent=self)
        if not path:
            return

        try:
            with open(path, "rb") as f:
                raw = f.read()
        except OSError as e:
            messagebox.showerror("Open Error", str(e), parent=self); return

        if len(raw) < self._ERDB_HDR_SZ:
            messagebox.showerror("Invalid File",
                "File too small — not a valid extended backup.", parent=self); return

        magic, version, block_lo, block_size, num_blocks = struct.unpack_from(">5I", raw)
        if magic != self._ERDB_MAGIC or version != self._ERDB_VERSION:
            messagebox.showerror("Invalid File",
                "Not a valid extended RDB backup.\n(Bad magic or unsupported version.)",
                parent=self); return
        if block_size != 512:
            messagebox.showerror("Invalid File",
                f"Block size mismatch: backup uses {block_size}-byte blocks, "
                "this tool requires 512.", parent=self); return
        expected = self._ERDB_HDR_SZ + num_blocks * 512
        if len(raw) != expected:
            messagebox.showerror("Invalid File",
                "File size does not match header — backup may be corrupt.",
                parent=self); return

        if not messagebox.askyesno("LAST CHANCE",
                f"Write {num_blocks} block(s) "
                f"(blocks {block_lo}–{block_lo + num_blocks - 1}) to:\n\n"
                f"  {dev}   ({fmt_size(self._cur_disk['size'])})\n\n"
                "This CANNOT be undone.",
                icon="warning", parent=self):
            return

        if not os.access(dev, os.W_OK):
            messagebox.showerror("Permission Denied",
                f"Cannot write to {dev}.\n\nRun this program with sudo.",
                parent=self); return

        offset = self._ERDB_HDR_SZ
        for i in range(num_blocks):
            blk_data = raw[offset + i * 512 : offset + i * 512 + 512]
            if not _write_block(dev, block_lo + i, blk_data):
                messagebox.showerror("Write Error",
                    f"Failed to write block {block_lo + i} to {dev}.", parent=self)
                return

        messagebox.showinfo("Extended Restore Complete",
            "Extended RDB restored successfully.\n\n"
            "Re-select the disk to reload the RDB.", parent=self)
        self._status.set(
            f"Extended RDB restored from {os.path.basename(path)}. Re-select disk to refresh.")

    def _do_image_disk(self):
        if not self._cur_disk:
            messagebox.showerror("No Disk Selected", "Select a disk first.")
            return
        dev  = self._cur_disk["path"]
        size = self._cur_disk["size"]
        path = filedialog.asksaveasfilename(
            title="Save Disk Image",
            defaultextension=".img",
            filetypes=[("Disk image", "*.img"), ("All files", "*.*")])
        if not path:
            return
        cmd = ["dd", f"if={dev}", f"of={path}", "bs=4m" if _IS_MACOS else "bs=4M"]
        if not _IS_MACOS:
            cmd.append("status=progress")
        dlg = _DDProgressDialog(self, f"Imaging {dev}…", cmd, size)
        if dlg.success:
            messagebox.showinfo("Image Complete",
                f"Disk image saved to:\n{path}\n\n{fmt_size(size)}")
            self._status.set(f"Disk image saved: {os.path.basename(path)}")

    def _do_restore_image(self):
        if not self._cur_disk:
            messagebox.showerror("No Disk Selected", "Select a disk first.")
            return
        dev  = self._cur_disk["path"]
        path = filedialog.askopenfilename(
            title="Open Disk Image",
            filetypes=[("Disk image", "*.img"), ("All files", "*.*")])
        if not path:
            return
        try:
            img_size = os.path.getsize(path)
        except OSError as e:
            messagebox.showerror("Error", str(e))
            return
        if not messagebox.askyesno("Confirm Restore",
                f"⚠  WARNING  ⚠\n\n"
                f"This will overwrite ALL data on:\n\n"
                f"  {dev}   ({fmt_size(self._cur_disk['size'])})\n\n"
                f"Image size: {fmt_size(img_size)}\n\n"
                f"THIS CANNOT BE UNDONE.\n\nContinue?", icon="warning"):
            return
        if not os.access(dev, os.W_OK):
            messagebox.showerror("Permission Denied",
                f"Cannot write to {dev}.\n\nRun this program with sudo.")
            return
        cmd = ["dd", f"if={path}", f"of={dev}", "bs=4m" if _IS_MACOS else "bs=4M"]
        if _IS_MACOS:
            cmd.append("conv=sync")
        else:
            cmd += ["status=progress", "oflag=dsync"]
        dlg = _DDProgressDialog(self, f"Restoring to {dev}…", cmd, img_size)
        if dlg.success:
            messagebox.showinfo("Restore Complete",
                f"Image restored to {dev}.\n\nRe-select the disk to reload.")
            self._status.set(f"Image restored to {dev}. Re-select disk to refresh.")

    def _do_move(self):
        sel = self._ptree.selection()
        if not sel or not self._rdb or not self._cur_disk:
            return
        idx = int(sel[0])
        pi  = self._rdb.partitions[idx]
        dev = self._cur_disk["path"]
        dlg = MovePartitionDialog(self, dev, self._rdb, pi)
        if dlg.result is not None:
            new_lo  = dlg.result
            cyl_cnt = pi.high_cyl - pi.low_cyl + 1
            pi.low_cyl  = new_lo
            pi.high_cyl = new_lo + cyl_cnt - 1
            self._refresh_parts()
            self._draw_map()
            self._status.set(
                f"Partition '{pi.drive_name}' moved to cyl {pi.low_cyl}\u2013{pi.high_cyl}. "
                "Write to disk to update the RDB.")

    def _do_grow(self):
        sel = self._ptree.selection()
        if not sel or not self._rdb or not self._cur_disk:
            return
        idx = int(sel[0])
        pi  = self._rdb.partitions[idx]
        dev = self._cur_disk["path"]
        dlg = GrowPartitionDialog(self, self._rdb, pi)
        if dlg.result is None:
            return
        new_hi = dlg.result
        old_hi = pi.high_cyl
        pi.high_cyl = new_hi
        self._refresh_parts()
        self._draw_map()

        if _ffs_is_type(pi.dos_type):
            if messagebox.askyesno("Grow FFS Filesystem",
                    f"Partition {pi.drive_name} extended to cyl {new_hi}.\n\n"
                    "EXPERIMENTAL: Grow the FFS filesystem to match?\n\n"
                    "This writes FFS bitmap blocks directly to disk.\n"
                    "Always have a backup before proceeding.",
                    parent=self, icon="warning"):
                ok, msg = _ffs_grow(dev, self._rdb, pi, old_hi)
                if ok:
                    messagebox.showinfo("FFS Grown",
                        f"FFS filesystem grown successfully.\n\n{msg}\n\n"
                        "Write RDB to disk, then reboot.", parent=self)
                else:
                    messagebox.showerror("FFS Grow Failed",
                        f"FFS grow failed:\n{msg}", parent=self)

        elif _pfs_is_type(pi.dos_type):
            if messagebox.askyesno("Grow PFS Filesystem",
                    f"Partition {pi.drive_name} extended to cyl {new_hi}.\n\n"
                    "EXPERIMENTAL: Grow the PFS filesystem to match?\n\n"
                    "This updates PFS rootblock metadata on disk.",
                    parent=self, icon="warning"):
                ok, msg = _pfs_grow(dev, self._rdb, pi, old_hi)
                if ok:
                    messagebox.showinfo("PFS Grown",
                        f"PFS filesystem grown successfully.\n\n{msg}\n\n"
                        "Write RDB to disk, then reboot.", parent=self)
                else:
                    messagebox.showerror("PFS Grow Failed",
                        f"PFS grow failed:\n{msg}", parent=self)

        self._status.set(
            f"Partition '{pi.drive_name}' grown to cyl {new_hi}. "
            "Write to disk to save.")

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
