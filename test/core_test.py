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

import os, sys, shutil, unittest, _path_magic
import core.oxide as oxide

mod_types = os.listdir(oxide.config.dir_modules)


class CoreTest(unittest.TestCase):
    def setUp(self):
        """ Set up test environment
        """
        # Move the datastore to the scratch dir
        oxide.datastore.datastore_dir = os.path.join(oxide.config.dir_scratch, "db")
        oxide.config.dir_datastore = oxide.datastore.datastore_dir
        if os.path.isdir(oxide.datastore.datastore_dir):
            shutil.rmtree(oxide.datastore.datastore_dir)
        oxide.sys_utils.ensure_dir_exists(oxide.datastore.datastore_dir)
        # self.assertTrue(oxide.get_set_names() == {}, "Collection dict is not empty.")

    def tearDown(self):
        """ Clean up test environment """
        shutil.rmtree(oxide.datastore.datastore_dir)

    def test_modules_imported(self):
        """ Assert that all of the modules imported correctly """
        fail = False
        for mod_type in mod_types:
            mod_type_path = os.path.join(oxide.config.dir_modules,mod_type)
            if not os.path.isdir(mod_type_path): continue
            mod_dirs = os.listdir(mod_type_path)
            base_type = mod_type
            if base_type[-4:] == "_dev":
                base_type = base_type[:-4]
            mods = oxide.modules_list(mod_type=base_type)
            for mod_dir in mod_dirs:
                if not os.path.isdir(os.path.join(mod_type_path,mod_dir)): continue
                fail_msg = "\n * A directory for module %s of type %s exists but it did not import." % (mod_dir, mod_type)
                if not mod_dir in mods:
                    fail = True
                    print(fail_msg)
        self.assertFalse(fail, "Some modules were not imported.")

    def test_import_file(self):
        """ Assert that a file can be imported """
        f = os.path.join(oxide.config.dir_datasets, "sample_dataset", "bash")
        fail_msg = "Not able to import file", f
        self.assertNotEqual(oxide.import_file(f), (None, False), fail_msg)

    def test_import_directory(self):
        """ Assert that a directory can be imported """
        d = os.path.join(oxide.config.dir_datasets, "sample_dataset")
        fail_msg = "Not able to import directory", d
        self.assertNotEqual(oxide.import_directory(d), (None, 0), fail_msg)

    def test_create_collection(self):
        """ Assert that a collection can be created """
        oid_list = ["abc"]
        data = {"xyz":"lmn"}
        opts = {}
        oxide.store("files", oid_list[0], data, opts)
        col_name = "test"
        self.assertTrue(oxide.create_collection(col_name, oid_list, "notes"), "Collection creation failed.")
        cid_l = oxide.get_cid_from_oid_list(oid_list)
        cid_n = oxide.get_cid_from_name(col_name)
        self.assertEqual(cid_l, cid_n, "cid collection name mismatch.")

    def test_documentation(self):
        """  Assert that documentation can be retrieved for each imported module """
        mods = oxide.modules_list()
        for mod in mods:
            fail_msg = "Not able to retrieve documentation for " + mod
            doc = oxide.documentation(mod)
            self.assertNotEqual(doc, None, fail_msg)

    def test_opts_doc(self):
        """ Assert that each module that has an opts_doc also has the required fields """
        mods = oxide.modules_list()
        for mod in mods:
            opts_doc = doc = oxide.documentation(mod)["opts_doc"]
            for opt in opts_doc:
                opts_keys = ["type", "mangle", "default"]
                for opts_key in opts_keys:
                    fail_msg = "opts_doc for module %s missing key %s." % (mod, opts_key)
                    self.assertTrue(opts_key in opts_doc[opt], fail_msg)

    def test_store_exists_retrieve_delete(self):
        """ Exercise the oxide functions store, exists, retrieve and delete_data """
        mod_name = "files"
        oid = "abc"
        data = {"xyz":"lmn"}
        opts = {}
        self.assertNotEqual(oxide.store(mod_name, oid, data, opts), False, "Store attempt failed.")
        self.assertNotEqual(oxide.exists(mod_name, oid, opts), False, "Test for data exists failed.")
        self.assertNotEqual(oxide.retrieve(mod_name, oid, opts, lock=False), False, "Retrieve attempt failed.")
        #self.assertNotEqual(oxide.delete_data(mod_name, oid, opts), False, "Delete data attempt failed."

if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(CoreTest)
    unittest.TextTestRunner().run(suite)
