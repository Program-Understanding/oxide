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

import unittest, os, shutil
import _path_magic
import core.oshell as oshell
s = oshell.OxideShell()

class ShellTest(unittest.TestCase):
    def setUp(self):
        """ Set up test environment """
        # Move the datastore to the scratch dir
        s.oxide.datastore.datastore_dir = os.path.join(s.oxide.config.dir_scratch, "db")
        s.oxide.config.dir_datastore = s.oxide.datastore.datastore_dir
        if os.path.isdir(s.oxide.datastore.datastore_dir):
            shutil.rmtree(s.oxide.datastore.datastore_dir)
        s.oxide.sys_utils.ensure_dir_exists(s.oxide.datastore.datastore_dir)
        self.assertTrue(s.oxide.get_set_names() == {}, "Collection dict is not empty.")

    def tearDown(self):
        """ Clean up test environment """
        shutil.rmtree(s.oxide.datastore.datastore_dir)

    def test_shell(self):
        test_collection = "test_collection"
        test_var = "test_var"
        test_var_s = "@" + test_var

        test_context = os.path.join(s.oxide.config.dir_scratch,"test_context.save")
        s.config["context_file"] = test_context
        if os.path.isfile(test_context):
            os.remove(test_context)

        test_history = os.path.join(s.oxide.config.dir_scratch,"test_history.txt")
        s.config["history_file"] = test_history
        if os.path.isfile(test_history):
            os.remove(test_history)

        s.onecmd("import datasets/sample_dataset | " + test_var_s)
        self.assertIn(test_var, s.vars)
        sample_len = len(s.vars[test_var])

        s.onecmd(test_var_s + " | collection create " + "_"+test_collection)
        self.assertIn("_"+test_collection, s.oxide.collection_names())

        s.onecmd("collection rename " + "_"+test_collection + " " + test_collection)
        self.assertNotIn("_"+test_collection, s.oxide.collection_names())
        self.assertIn(test_collection, s.oxide.collection_names())

        s.onecmd("context set &" + test_collection)
        self.assertEqual(sample_len, len(s.context))

        s.onecmd("$0 | " + test_var_s)
        s.onecmd("collection remove " + test_collection + " " + test_var_s)
        s.onecmd("context set &" + test_collection)
        self.assertEqual(sample_len-1, len(s.context))

        s.onecmd("collection delete " + test_collection)
        self.assertNotIn(test_collection, s.oxide.collection_names())

        s.onecmd("context remove " + test_var_s)
        self.assertEqual(sample_len-1, len(s.context))

        s.onecmd("context save ")

        s.onecmd("context clear")
        self.assertEqual(len(s.context), 0)

        s.onecmd("context load ")
        self.assertEqual(sample_len-1, len(s.context))

        if os.path.isfile(test_context):
            os.remove(test_context)

        s.onecmd("history clear")
        self.assertEqual(oshell.readline.get_current_history_length(), 0)
        if os.path.isfile(test_history):
            os.remove(test_history)


if __name__ == "__main__":
    suite = unittest.TestLoader().loadTestsFromTestCase(ShellTest)
    unittest.TextTestRunner().run(suite)
