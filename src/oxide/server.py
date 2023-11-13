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

""" server.py

Utility script to start Oxide server
"""
import argparse
import sys
import os

# Hack to import sister module
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from oxide.core import oxide_server

parser = argparse.ArgumentParser()
parser.add_argument("-l", "--listen", action="store", type=str, dest="listen", nargs='?',
                    metavar="HOST:PORT", help="The host:port I'm listening on")
ARGS = parser.parse_args()


def main() -> None:
    """ Server utility entry point.
    """
    if not isinstance(ARGS.listen, str):
        parser.print_help()
        sys.exit(1)

    elif len(ARGS.listen.split(":")) != 2:
        parser.print_help()
        sys.exit(1)

    host, port = ARGS.listen.split(":")
    sys.argv = sys.argv[:1]
    oxide_server.main(host, int(port))


if __name__ == "__main__":
    main()
