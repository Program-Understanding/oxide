#!/usr/bin/env python3
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

""" shell.py

Oxide CLI entrypoint module
"""
import argparse
import sys

from core import rshell
from core import oshell

def main() -> None:
    """ Oxide CLI entry point, initiating remote or commandline shell.
    """
    parser = argparse.ArgumentParser()
    parser.add_argument('-r', '--remote', action='store', type=str, dest='remote',
                        metavar='HOST:PORT', help="The server ip:port I'm connecting to")
    args = parser.parse_args()

    if args.remote:
        if len(args.remote.split(":")) != 2:
            parser.print_help()
            sys.exit(1)

        host, port_str = args.remote.split(":")
        print(' - Connecting to remote server {}:{}'.format(host, port_str))
        sys.argv = sys.argv[:1]
        remote_shell = rshell.RemoteOxideShell(host, int(port_str))
        remote_shell.cmdloop()

    else:
        oshell.OxideShell().cmdloop()

# --- Do not read below, this is strictly to support one liner support
try:
    HAS_CLICK = True
    import click
except ImportError:
    HAS_CLICK = False

if not HAS_CLICK:
    if __name__ == '__main__':
        main()
else:
    @click.group(invoke_without_command=True)
    @click.pass_context
    def cli(ctx):
        if ctx.invoked_subcommand is None:
            main()


    @cli.command()
    @click.argument('arguments', nargs=-1)
    def run(arguments) -> None:
        """ One shot run analysis
                expected command:
                    shell.py run [cmd] [cmd_arguments] [oid]
                Do not include `| show`, show will post-pend to command by default.
        """
        arg_string = " ".join(arguments)
        oshell.OxideShell().onecmd(f"run {arg_string} | show")

    @cli.command('import')
    @click.argument('arguments', nargs=-1)
    def imp(arguments) -> None:
        """ One shot import
                expected command:
                    shell.py import [oid]+
        """
        arg_string = " ".join(arguments)
        oshell.OxideShell().onecmd(f"import {arg_string} | show")

    if __name__ == '__main__':
        cli()