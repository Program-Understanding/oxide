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

""" tags.py
"""
import logging

from oxide.core import api

from typing import List, Optional


NAME = "tags"
logger = logging.getLogger(NAME)


def apply_tags(oid_list: List[str], new_tags: List[str]) -> None:
    if isinstance(oid_list, list):
        for oid in oid_list:
            apply_tags(oid, new_tags)
    else:
        oid = oid_list
        if not api.exists("tags", oid):
            tags = {}
        else:
            tags = api.retrieve("tags", oid, {}, True)
        for tag in new_tags:
            tags[tag] = new_tags[tag]
        api.store("tags", oid, tags)


def get_tags(oid: str) -> Optional[List[str]]:
    if not isinstance(oid, str):
        logger.error("get_tags must be called with a single OID")
        return None

    if api.exists("tags", oid):
        return api.retrieve("tags", oid)

    return None


def tag_filter(oid_list: List[str], tag: str, value: str = "<empty>") -> Optional[List[str]]:
    filtered_oids = []
    if not oid_list:
        oid_list = api.retrieve_all_keys("files")
        if not oid_list:
            logger.error("No files exist")
            return None
        cids = api.retrieve_all_keys("collections")
        if cids:
            oid_list.extend(cids)

    for oid in oid_list:
        tags_list = get_tags(oid)
        if tags_list and tag in tags_list:
            if (tags_list[tag] == "<empty>" or value == "<empty>" or value == tags_list[tag] or value in tags_list[tag]):
                filtered_oids.append(oid)

    return filtered_oids
