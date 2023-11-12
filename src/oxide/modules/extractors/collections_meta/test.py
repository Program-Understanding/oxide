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

class collections_meta_test(unittest.TestCase):
    def test_collections_meta(self):
        sample_files = os.listdir(self.oxide.config.dir_sample_dataset)
        oid_list = []
        for sample_file in sample_files:
            fp = os.path.join(self.oxide.config.dir_sample_dataset, sample_file)
            oid, new_fie = self.oxide.import_file(fp)
            if oid: oid_list.append(oid)
        cid = self.oxide.get_cid_from_oid_list(oid_list)
        col_name = "test_collections_meta"
        col_note = "Test notes ...."
        self.assertTrue(self.oxide.create_collection(col_name, oid_list, col_note))
        data = self.oxide.retrieve("collections_meta", cid, {})
        self.assertEqual(data['name'], col_name, "Collection name not equal")
        self.assertEqual(data['notes'], col_note, "Collection notes not equal")
        self.assertEqual(data['num_oids'], len(oid_list), "Collection size not correct")
        self.oxide.delete_collection_by_name(col_name)
