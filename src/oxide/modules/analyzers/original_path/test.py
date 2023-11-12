import unittest
import os

# This file needs to be named test.py and reside in the same folder as the module itself.
# Class name must be <modulename>_test and must inherit from unittest.TestCase
# Function names must start with test_

class original_path_test(unittest.TestCase):
    def test_original_path(self) -> None:
        sample_files = os.listdir(self.oxide.config.dir_sample_dataset)
        oid_list = []
        for sample_file in sample_files:
            fp = os.path.join(self.oxide.config.dir_sample_dataset, sample_file)
            oid, newfile = self.oxide.import_file(fp)
            if not oid: continue
            oid_list.append(oid)
        for oid in oid_list:
            src_type = self.oxide.get_field("src_type", oid, "type")
            if  'PE' in src_type or 'ELF' in src_type or 'MACHO' in src_type:
                self.assertTrue(self.oxide.process("original_path", [oid], {}),
                                "original_path not able to process a PE, ELF, MACHO file")
            else:
                self.assertFalse(self.oxide.process("original_path", [oid], {}),
                                 "original_path able to process a not-PE/ELF/MACHO file")