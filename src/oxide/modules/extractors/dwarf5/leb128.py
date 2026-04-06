"""LEB128 signed/unsigned decoding utilities."""


def decode_uleb128(data: bytes, offset: int) -> tuple[int, int]:
    value = 0
    shift = 0
    while True:
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if (byte & 0x80) == 0:
            return value, offset
        shift += 7


def decode_sleb128(data: bytes, offset: int) -> tuple[int, int]:
    byte = 0
    value = 0
    shift = 0
    while True:
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if (byte & 0x80) == 0:
            if shift < 64 and (byte & 0x40):
                value |= -(1 << shift)
            return value, offset
