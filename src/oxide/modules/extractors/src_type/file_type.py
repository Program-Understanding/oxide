"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

import struct

from typing import Set


def isPE(stream: bytes) -> bool:
	return stream[:2] == b"MZ"


def isZM(stream: bytes) -> bool:
    return stream[:2] == b"ZM"


def isELF(stream: bytes) -> bool:
    return stream[:4] == b"\x7fELF"


def isELF32(stream: bytes) -> bool:
    return isELF(stream) and stream[5] == b"\x01"


def isELF64(stream: bytes) -> bool:
    return isELF(stream) and stream[5] == b"\x02"


def isELF32_intel(stream: bytes) -> bool:
    return isELF32(stream) and stream[18] == b"\x03"


def isELF32_arm(stream: bytes) -> bool:
    return isELF32(stream) and stream[18] == b"\x40"


def isScript(stream: bytes) -> bool:
    return stream[:2] == b"#!"


def isPDF(stream: bytes) -> bool:
    return stream[:4] == b"%PDF"


def isGIF(stream: bytes) -> bool:
    return stream[:4] == b"GIF8"


def isJPG(stream: bytes) -> bool:
    return stream[:2] == b"\xFF\xD8"


def isPNG(stream: bytes) -> bool:
    return stream[:8] == b"\x89\x50\x4E\x47\x0D\x0A\x1A\x0A"

def isSVG(stream: bytes) -> bool:
    print(stream[:10])
    return stream[:] == b""

def isBMP(stream: bytes) -> bool:
    return stream[:2] == b"BM"

def isTIFF(stream: bytes) -> bool:
    """ TrID TIF=TIFF
    """
    return (stream[:4] == b"\x49\x49\x2A\x00" or
           stream[:4] == b"\x4D\x4D\x00\x2A")

def isPS(stream: bytes) -> bool:
    return stream[:2] == b"%!"

def isMP3(stream: bytes) -> bool:
    print(stream[:12])
    return stream[:12] == b"\x49\x44\x33\x03\x00\x00\x00"

def isMP4(stream: bytes) -> bool:
    print(stream[:12])
    return (stream[:12] == b"\x00\x00\x00\x14ftyp3gp5" or
            stream[:12] == b"\x00\x00\x00\x14ftypisom" or
            stream[:12] == b"\x00\x00\x00\x1cftypisom" or
            stream[:12] == b"\x00\x00\x00\x20ftyp3gp5" or
            stream[:12] == b"\x00\x00\x00\x20ftypisom")

def isWAV(stream: bytes) -> bool:
    return (stream[:4] == b"\x52\x49\x46\x46" or
            stream[:5] == b"\x57\x41\x56\x43\x56" or
            stream[:5] == b"\x52\x46\x36\x34\xFF")

def isOGG(stream: bytes) -> bool:
    """ TrID: OGG=OGV
    """
    return stream[:4] == b"\x4F\x67\x67\x53"

def isM4A(stream: bytes) -> bool:
    return stream[:12] == b"\x00\x00\x00\x20ftypM4A\x20"


def isZIP(stream: bytes) -> bool:
    return stream[:4] == b"PK\x03\x04"

def isXZ(stream: bytes) -> bool:
    print(stream[:4])
    return stream[:4] == b"\de\ca"

def isCompress(stream: bytes) -> bool:
    return stream[:2] == b"\x1f\x9d"


def isBZ2(stream: bytes) -> bool:
    return stream[:2] == b"BZ"


def isGZip(stream: bytes) -> bool:
    return stream[:2] == b"\x1f\x8b"


def isFITS(stream: bytes) -> bool:
    return stream[:6] == b"SIMPLE"


def isTAR(stream: bytes) -> bool:
    return (len(stream) > 265 and stream[257:257+5] == b"ustar")


def isCAB(stream: bytes) -> bool:
    return stream[:4] == b"MSCF"


def isMSOffice(stream: bytes) -> bool:
    return stream[:8] == b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1"


def isJava(stream: bytes) -> bool:
    # Java Class file
    return stream[:8] == b"\xCA\xFE\xD0\x0D"


def isVmem(stream: bytes) -> bool:
    return stream[:6] == b"\x53\xff\x00\xf0\x53\xff"


def isXML(stream: bytes) -> bool:
    return (stream[:5] == b"<?xml" or stream[:5] == b"<?XML")

def isTTF(stream: bytes) -> bool:
    return (stream[:5] == b"\x00\x01\x00\x00\x00" or
            stream[:5] == b"\x74\x72\x75\x65\x00")

def isMachO(stream: bytes) -> bool:
    return (stream[:4] == b"\xce\xfa\xed\xfe" or stream[:4] == b"\xfe\xed\xfa\xce" or
            stream[:4] == b"\xcf\xfa\xed\xfe")


def isDEX(stream: bytes) -> bool:
    return stream[:4] == b"dex\n"


def isFatBinary(stream: bytes) -> bool:
    return stream[:4] == b"\xca\xfe\xba\xbe"


def file_type(stream: bytes) -> Set[str]:
    """ go through set of possible file types, checking file header for matches.
    """
    type = set()
    if isPE(stream):
        type.add("PE")
    if isZM(stream):
        type.add("ZM")
    if isELF(stream):
        type.add("ELF")
    if isScript(stream):
        type.add("Script")
    if isPDF(stream):
        type.add("PDF")
    if isGIF(stream):
        type.add("GIF")
    if isJPG(stream):
        type.add("JPG")
    if isPNG(stream):
        type.add("PNG")
    if isBMP(stream):
        type.add("BMP")
    if isTIFF(stream):
        type.add("TIFF")
    if isPS(stream):
        type.add("PS")
    if isMP3(stream):
        type.add("MP3")
    if isMP4(stream):
        type.add("MP4")
    if isWAV(stream):
        type.add("WAV")
    if isOGG(stream):
        type.add("OGG")
    if isM4A(stream):
        type.add("M4A")
    if isZIP(stream):
        type.add("ZIP")
    if isXZ(stream):
        type.add("XZ")
    if isCompress(stream):
        type.add("Compress")
    if isBZ2(stream):
        type.add("BZ2")
    if isGZip(stream):
        type.add("GZIP")
    if isFITS(stream):
        type.add("FITS")
    if isTAR(stream):
        type.add("TAR")
    if isCAB(stream):
        type.add("Microsoft CAB File")
    if isMSOffice(stream):
        type.add("Microsoft Office File")
    if isJava(stream):
        type.add("JAVA Bytecode")
    if isVmem(stream):
        type.add("VMEM")
    if isXML(stream):
        type.add("XML")
    if isTTF(stream):
        type.add("TTF")
    if isMachO(stream):
        type.add("MACHO")
    if isDEX(stream):
        type.add("DEX")
    if isFatBinary(stream):
        type.add("OSX Universal Binary")

    if not type:
        type.add("Unknown")
    return type
