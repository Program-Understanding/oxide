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

import unittest
import os

# This file needs to be named test.py and reside in the same folder as the module itself.
# Class name must be <modulename>_test and must inherit from unittest.TestCase
# Function names must start with test_

class file_meta_test(unittest.TestCase):
    def test_file_meta(self):
        sample_files = os.listdir(self.oxide.config.dir_sample_dataset)
        for sample_file in sample_files:
            fp = os.path.join(self.oxide.config.dir_sample_dataset, sample_file)
            oid,newfile = self.oxide.import_file(fp)
            if oid: # Some files will not be imported
                ds = self.oxide.retrieve("file_meta", oid)
                file_stat = os.stat(fp)
                fs_dict = {}
                fs_dict["atime"] = file_stat.st_atime
                fs_dict["mtime"] = file_stat.st_mtime
                fs_dict["ctime"] = file_stat.st_ctime
                fs_dict["size"]  = file_stat.st_size
                name = os.path.basename(fp)
                for t in ds["metadata"]:
                    if name in ds["metadata"][t]:
                        stat = ds["metadata"][t][name]
                self.assertEqual(stat['size'], fs_dict['size'], "File size does not match.")
                self.assertEqual(stat['mtime'], fs_dict['mtime'], "File mtime does not match.")
                self.assertEqual(stat['ctime'], fs_dict['ctime'], "File ctime does not match.")
