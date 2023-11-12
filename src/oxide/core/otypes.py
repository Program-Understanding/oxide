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

""" otypes.py
Handles oxide defined types/exceptions and logging levels
"""

import logging

from typing import Optional, Any

LOG_LEVELS = ["DEBUG", "INFO", "WARN", "WARNING", "ERROR", "CRITICAL", "FATAL"]


class OxideError(Exception):
    """ Oxide Error base class
    """


class BadOIDList(OxideError):
    pass


class UnrecognizedModule(OxideError):
    pass


class AnalysisModuleError(OxideError):
    pass


class InvalidOIDList(AnalysisModuleError):
    pass


def cast_string(string: str) -> Any:
    """ Casts string to any detectable type
    """
    if not isinstance(string, str) or string == "":
        res = string
    elif string.lower() == "true":
        res = True
    elif string.lower() == "false":
        res = False
    elif string.upper() in LOG_LEVELS:
        res = convert_logging_level(string)
    else:
        try:
            # integer
            res = int(string)
        except ValueError:
            try:
                # hex
                res = int(string, 16)
            except ValueError:
                try:
                    # float
                    res = float(string)
                except ValueError:
                    logging.debug("Not able to cast(%s)", string)
                    res = string

    return res


def convert_logging_level(level: str) -> Optional[int]:
    """ Given a string corresponding to a loggging level return the logging
        level enum value or None if a match is not found
    """
    level = level.upper()
    if level == "DEBUG":
        res = logging.DEBUG
    elif level == "INFO":
        res = logging.INFO
    elif level in ["WARN", "WARNING"]:
        res = logging.WARNING
    elif level == "ERROR":
        res = logging.ERROR
    elif level in ["CRITICAL", "FATAL"]:
        res = logging.CRITICAL
    else:
        res = None

    return res
