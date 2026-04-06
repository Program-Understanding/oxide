"""Binary reading helpers for DWARF parsing."""

import struct

from . import leb128


class BinaryReader:
    def __init__(self, data: bytes, little_endian: bool = True, offset: int = 0):
        self.data = data
        self.offset = offset
        self.endian = "<" if little_endian else ">"

    def tell(self) -> int:
        return self.offset

    def seek(self, offset: int) -> None:
        self.offset = offset

    def read_u8(self) -> int:
        v = self.data[self.offset]
        self.offset += 1
        return v

    def read_u16(self) -> int:
        v = struct.unpack_from(self.endian + "H", self.data, self.offset)[0]
        self.offset += 2
        return v

    def read_u32(self) -> int:
        v = struct.unpack_from(self.endian + "I", self.data, self.offset)[0]
        self.offset += 4
        return v

    def read_u64(self) -> int:
        v = struct.unpack_from(self.endian + "Q", self.data, self.offset)[0]
        self.offset += 8
        return v

    def read_bytes(self, size: int) -> bytes:
        v = self.data[self.offset : self.offset + size]
        self.offset += size
        return v

    def read_cstring(self) -> str:
        start = self.offset
        while self.data[self.offset] != 0:
            self.offset += 1
        out = self.data[start : self.offset].decode("utf-8", errors="replace")
        self.offset += 1
        return out

    def read_uleb128(self) -> int:
        v, self.offset = leb128.decode_uleb128(self.data, self.offset)
        return v

    def read_sleb128(self) -> int:
        v, self.offset = leb128.decode_sleb128(self.data, self.offset)
        return v
