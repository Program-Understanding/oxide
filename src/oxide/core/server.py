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
"""
from xmlrpc.server import SimpleXMLRPCServer
import logging
import socketserver

from typing import List, Callable

NAME = "server"
logger = logging.getLogger(NAME)
server = None


class ForkingServer(socketserver.ForkingMixIn, SimpleXMLRPCServer):
    pass


def init(host: str, port: str, functions: List[Callable]) -> bool:
    """ Initialize server and register function list.
    """
    global server
    global logger

    if not isinstance(functions, list):
        logger.error("functions must be of list type")
        return False

    server = ForkingServer((host, int(port)), allow_none=True)
    server.register_introspection_functions()
    server.register_function(alive)
    for function in functions:
        server.register_function(function)

    logger.debug("Server init %s:%s", host, port)
    return True


def start_listen() -> None:
    """ Start server always listening.
    """
    global server
    global logger
    logger.debug("Server listening")
    server.serve_forever()


def close() -> None:
    global server
    global logger
    # TODO:: Is this a compile time choice?
    # SERVER.close()  # Use this for non forking server
    server.server_close()  # Use this for forking server
    logger.debug("Server close")


def alive() -> bool:
    """ Always return true, to allow endless listening server.
    """
    return True
