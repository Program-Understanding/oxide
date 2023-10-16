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

import unittest, shutil, logging
import os
import _path_magic
from core.sys_utils import (ensure_dir_exists, get_contents_of_file, get_file_stat, import_file,
                            delete_file, read_object_from_file, write_object_to_file,
                            get_files_from_directory, pack, unpack, pack_file, unpack_file)
import core.oxide as oxide
test_data = b"abcdefghijklmnopqrstuvwxyz0123456789!@#$%^&*()" * 1024 * 256
size = len(test_data)/1048576.
test_fname = "test_file"
test_dname = "test_dir"

class SysUtilsTest(unittest.TestCase):
    def test_file_utils(self):
        if os.path.isdir(test_dname):
            shutil.rmtree(test_dname)

        fd = open(test_fname, "wb")
        fd.write(test_data)
        fd.close()

        stat = get_file_stat(test_fname)
        self.assertNotEqual(stat, None)
        data = get_contents_of_file(test_fname)
        self.assertEqual(data, test_data)

        oxide.set_verbosity_level(logging.FATAL)
        oxide.set_logging_level(logging.FATAL)

        self.assertEqual(import_file(test_fname, max_file_size=1), None)
        oxide.set_verbosity_level(logging.ERROR)
        oxide.set_logging_level(logging.ERROR)

        file_data = import_file(test_fname, max_file_size=25)
        self.assertEqual(file_data["file_stat"]["ctime"], stat["ctime"])
        self.assertEqual(file_data["file_stat"]["mtime"], stat["mtime"])
        self.assertEqual(file_data["data"], test_data)
        self.assertEqual(file_data["size"], size)

        self.assertEqual(delete_file(test_fname), True)

        oxide.set_verbosity_level(logging.FATAL)
        oxide.set_logging_level(logging.FATAL)
        self.assertEqual(delete_file(test_fname), False)
        oxide.set_verbosity_level(logging.ERROR)
        oxide.set_logging_level(logging.ERROR)

        self.assertFalse(os.path.isdir(test_dname))
        self.assertTrue(ensure_dir_exists(test_dname))
        self.assertTrue(os.path.isdir(test_dname))
        self.assertTrue(ensure_dir_exists(test_dname))

        long_name = os.path.join(test_dname, test_fname)
        self.assertEqual(write_object_to_file(long_name, test_data), True)
        self.assertEqual(read_object_from_file(long_name), test_data)
        self.assertTrue(os.path.join(test_dname, test_fname) in get_files_from_directory(test_dname))
        shutil.rmtree(test_dname)

    def test_network_utils(self):

        new_data = pack(test_data)
        self.assertNotEqual(new_data, None)
        old_data = unpack(new_data)
        self.assertEqual(old_data, test_data)

        new_data = pack_file(test_data)
        self.assertNotEqual(new_data, None)
        old_data = unpack_file(new_data)
        self.assertEqual(old_data, test_data)


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(SysUtilsTest)
    unittest.TextTestRunner().run(suite)
