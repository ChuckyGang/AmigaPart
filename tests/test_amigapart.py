import struct
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

import AmigaPart as ap


class AmigaPartTests(unittest.TestCase):
    def test_build_part_block_preserves_secs_per_blk(self):
        part = ap.PartitionInfo()
        part.secs_per_blk = 4
        block = ap.build_part_block(part, rdb_heads=16, rdb_sectors=63)
        self.assertEqual(struct.unpack_from(">I", block, 128 + 16)[0], 4)

    def test_validate_partition_settings_rejects_long_names(self):
        err = ap._validate_partition_settings(
            "D" * 32, 128, 16, 63, 1, 2, 0, 0, 30, 0x7FFFFFFF, 0xFFFFFFFE, 2)
        self.assertIn("31 ASCII characters", err)

    def test_validate_rdb_layout_accepts_simple_layout(self):
        rdb = ap.RDBInfo()
        rdb.cylinders = 100
        rdb.heads = 16
        rdb.sectors = 63
        rdb.locyl = 1
        rdb.hicyl = 99

        part = ap.PartitionInfo()
        part.drive_name = "DH0"
        part.low_cyl = 1
        part.high_cyl = 10
        part.surfaces = 16
        part.blk_per_trk = 63
        rdb.partitions = [part]

        disk_size = rdb.cylinders * rdb.heads * rdb.sectors * 512
        self.assertIsNone(ap._validate_rdb_layout(rdb, disk_size))

    def test_validate_rdb_layout_rejects_metadata_overflow(self):
        rdb = ap.RDBInfo()
        rdb.cylinders = 100
        rdb.heads = 16
        rdb.sectors = 63
        rdb.locyl = 1
        rdb.hicyl = 99

        fs = ap.FilesystemInfo()
        fs.data = b"x" * (ap.LSEG_DATA * 1008)
        rdb.filesystems = [fs]

        disk_size = rdb.cylinders * rdb.heads * rdb.sectors * 512
        err = ap._validate_rdb_layout(rdb, disk_size)
        self.assertIn("metadata needs", err)

    def make_app(self, path, size):
        rdb = ap.RDBInfo()
        rdb.cylinders, rdb.heads, rdb.sectors = 100, 1, 16
        rdb.locyl, rdb.hicyl = 1, 99
        part = ap.PartitionInfo()
        part.low_cyl, part.high_cyl = 1, 10
        part.blk_per_trk = 16
        rdb.partitions = [part]
        fs = ap.FilesystemInfo()
        fs.data = b"filesystem" * 100
        rdb.filesystems = [fs]
        return SimpleNamespace(
            _rdb=rdb, _cur_disk={"path": str(path), "size": size, "model": "test"},
            _info={"rdb": Mock()}, _status=Mock())

    def test_write_orders_metadata_before_rdsk_and_round_trips(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "disk.img"
            path.write_bytes(bytes(100 * 16 * 512))
            app = self.make_app(path, path.stat().st_size)
            offsets = []
            real_open = open

            def recording_open(*args, **kwargs):
                fh = real_open(*args, **kwargs)
                wrapper = Mock(wraps=fh)
                wrapper.__enter__ = Mock(return_value=wrapper)
                wrapper.__exit__ = Mock(side_effect=fh.__exit__)

                def write(data):
                    offsets.append(fh.tell())
                    return fh.write(data)

                wrapper.write.side_effect = write
                return wrapper

            with patch.object(ap, "open", recording_open, create=True), \
                    patch.object(ap, "messagebox") as dialogs:
                ap.App._do_write(app)
            dialogs.showerror.assert_not_called()
            self.assertEqual(offsets, [512, 1024, 1536, 2048, 2560, 0])
            parsed = ap.read_rdb(str(path))
            self.assertEqual(parsed.partitions[0].high_cyl, 10)
            self.assertEqual(parsed.filesystems[0].data[:1000],
                             app._rdb.filesystems[0].data)

    def test_write_failure_stops_before_rdsk(self):
        app = self.make_app("unused.img", 100 * 16 * 512)
        fh = Mock()
        fh.__enter__ = Mock(return_value=fh)
        fh.__exit__ = Mock(return_value=False)
        fh.write.side_effect = OSError("injected write failure")
        with patch.object(ap, "open", return_value=fh, create=True), \
                patch.object(ap.os, "access", return_value=True), \
                patch.object(ap, "messagebox") as dialogs:
            ap.App._do_write(app)
        self.assertEqual(fh.seek.call_args_list[0].args, (512,))
        fh.write.assert_called_once()
        dialogs.showerror.assert_called_once()
        dialogs.showinfo.assert_not_called()

    def test_invalid_layout_does_not_open_disk_for_writing(self):
        app = self.make_app("unused.img", 100 * 16 * 512)
        app._rdb.partitions[0].low_cyl = 0
        with patch.object(ap, "open", create=True) as disk_open, \
                patch.object(ap.os, "access", return_value=True), \
                patch.object(ap, "messagebox") as dialogs:
            ap.App._do_write(app)
        disk_open.assert_not_called()
        dialogs.showerror.assert_called_once()

    def test_oversized_restores_do_not_write(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "backup.rdb"
            raw = struct.pack(">I", ap.RDSK_ID) + bytes(1024 - 4)
            path.write_bytes(raw)
            app = self.make_app("unused.img", 512)
            for method in (ap.App._do_restore_rdb, ap.App._do_restore_image):
                with self.subTest(method=method.__name__), \
                        patch.object(ap.filedialog, "askopenfilename", return_value=str(path)), \
                        patch.object(ap, "messagebox") as dialogs, \
                        patch.object(ap, "_write_block") as write_block, \
                        patch.object(ap, "_DDProgressDialog") as dd:
                    method(app)
                    dialogs.showerror.assert_called_once()
                    dialogs.askyesno.assert_not_called()
                    write_block.assert_not_called()
                    dd.assert_not_called()


if __name__ == "__main__":
    unittest.main()
