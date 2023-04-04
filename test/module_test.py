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

import _path_magic
import os
import sys
import unittest
import shutil
import core.oxide as oxide

def module_test(singlemodule=None):
    # Move the datastore to the scratch dir
    oxide.datastore.datastore_dir = os.path.join(oxide.config.dir_scratch, "db")
    oxide.config.dir_datastore = oxide.datastore.datastore_dir
    if os.path.isdir(oxide.datastore.datastore_dir):
        shutil.rmtree(oxide.datastore.datastore_dir)
    oxide.sys_utils.ensure_dir_exists(oxide.datastore.datastore_dir)

    # Add module directories to path
    modulesdir = os.listdir(oxide.config.dir_modules)
    for moduletype in modulesdir:
        moduletypepath = os.path.join(oxide.config.dir_modules,moduletype)
        if os.path.isdir(moduletypepath):
            modules = os.listdir(moduletypepath)
            for module in modules:
                if singlemodule and module != singlemodule: # Check if we are only testing one module
                    continue
                testpath = os.path.join(moduletypepath,module,"test.py")
                if os.path.exists(testpath):
                    print("Running the %s module test." % (module))
                    sys.path.insert(0,os.path.join(moduletypepath,module)) # Prepend the path
                    class_str = str(module) + ".test"
                    try:
                        mod = __import__(class_str, globals(), locals(), [str(module) + "_test"])
                        try:
                            test_class = getattr(mod, str(module) + "_test")
                        except AttributeError:
                            print(" - AttributeError trying to run module %s test" % module)
                            continue
                        suite = unittest.TestLoader().loadTestsFromTestCase(test_class)
                        for test in suite: # Set the test's version of oxide to be the same as ours
                            test.oxide = oxide
                        testSuite = unittest.TestSuite([suite])
                        text_runner = unittest.TextTestRunner()
                        text_runner.run(testSuite)
                    except ImportError:
                        print("Warning: Not able to import %s. Skipping this test!" % (module))
                    sys.path.remove(os.path.join(moduletypepath,module)) # Remove the path prepend

    # Remove the datastore in the scratch dir
    shutil.rmtree(oxide.datastore.datastore_dir)

if __name__ == "__main__":
    module_test()
