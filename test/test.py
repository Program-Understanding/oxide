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

""" test.py

Unit test harness
"""
import argparse
import unittest
from module_test import module_test
from sys_utils_test import SysUtilsTest
from core_test import CoreTest
from shell_test import ShellTest

parser = argparse.ArgumentParser()
parser.add_argument("-c", "--core", action="store_true", dest="core",
                    help="Run the core tests")

parser.add_argument("-a", "--all", action="store_true", dest="all",
                    help="Run all of the tests")

parser.add_argument("-i", "--interactive", action="store_true", dest="interactive",
                    help="Run interactive tests")

parser.add_argument("-v", "--verbose", action="count", dest="verbose",
                    help="Verbose test output")

parser.add_argument("-m", "--modules", action="store_true", dest="modules",
                    help="Run module tests")

parser.add_argument("-o", "--onemodule", action="store", dest="onemodule",
                    help="Test single module")

parser.add_argument("-s", "--shell", action="store_true", dest="shell",
                    help="Test the shell")

ARGS = parser.parse_args()


def main():
    """ Unit test harness
    """
    if ARGS.all or (not ARGS.core and not ARGS.modules and not ARGS.onemodule and not ARGS.shell):
        ARGS.core = True
        ARGS.modules = True
        ARGS.shell = True

    if ARGS.onemodule:
        print("Testing the " + ARGS.onemodule + " module")
        module_test(singlemodule=ARGS.onemodule)

    if ARGS.modules:
        print("Running module tests.")
        module_test()
    else:
        print("Skipping module tests.")

    if ARGS.core:
        print("Running sys_utils tests.")
        suite = unittest.TestLoader().loadTestsFromTestCase(SysUtilsTest)
        unittest.TextTestRunner().run(suite)

        print("Running core tests.")
        suite = unittest.TestLoader().loadTestsFromTestCase(CoreTest)
        unittest.TextTestRunner(verbosity=50).run(suite)
    else:
        print("Skipping core tests.")

    if ARGS.shell:
        print("Running shell tests.")
        suite = unittest.TestLoader().loadTestsFromTestCase(ShellTest)
        unittest.TextTestRunner(verbosity=50).run(suite)


if __name__ == "__main__":
    main()
