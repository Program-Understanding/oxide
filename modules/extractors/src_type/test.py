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


class src_type_test(unittest.TestCase):
    def test_src_type(self):
        sample_files = os.listdir(self.oxide.config.dir_sample_dataset)
        for sample_file in sample_files:
            fp = os.path.join(self.oxide.config.dir_sample_dataset, sample_file)
            oid, already = self.oxide.import_file(fp)
            if oid: # Some files will not be imported
                """result = os.popen("file " + fp).read().upper()
                cut = len(fp) + 2
                result = result[cut:] #remove the '<filename>: ' from the beginning"""
                src_type = self.oxide.get_field("src_type", oid, "type")
                self.assertNotEqual(src_type, None)

                """
                # Validate the src_type modules label of the file
                if src_type == "PE":
                    self.assertEqual(result[:2], "PE")
                elif src_type == "ELF":
                    self.assertEqual(result[:3], "ELF")
                elif src_type == "Script":
                    self.assertNotEqual(result.find("SHELL SCRIPT"), -1)
                elif src_type == "ZIP":
                    self.assertEqual(result[:3], "ZIP")

                # Make sure the module didn't miss a file it should have labeled
                if result[:2] == "PE":
                    self.assertEqual(src_type, "PE")
                elif result[:3] == "ELF":
                    self.assertEqual(src_type, "ELF")
                elif result.find("SHELL SCRIPT") >= 0:
                    self.assertEqual(src_type, "Script")
                elif result[:3] == "ZIP":
                    self.assertEqual(src_type, "ZIP")"""
