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

import logging
import traceback
from multiprocessing import Pool, Queue, Manager
from multiprocessing.managers import BaseManager

from oxide.core import oxide, config
from oxide.core.progress import Progress
from oxide.core.client import get_proxy

from typing import List, Callable, Tuple, Any


NAME = "multiproc"
logger = logging.getLogger(NAME)

class MyManager(BaseManager):
    pass

MyManager.register('Progress', Progress)
MyManager.register('Queue', Queue)


max_processes = config.multiproc_max
results_q = Queue()


def _process_map(job: Tuple[Callable, str, dict, Progress]) -> None:
    (func, mod_name, oid, opts, p) = job
    try:
        config.multiproc_on = False
        func(mod_name, oid, opts)
        p.tick()
    except:
        print('-'*60)
        traceback.print_exc()
        print('-'*60)


def process_map(func: Callable, mod_name: str, oid_list: List[str], opts: dict = {},
                blocking: bool = False) -> bool:
    num_oids = len(oid_list)
    if num_oids == 0:
        return True

    nprocs = min(num_oids, max_processes)
    with Pool(processes=nprocs) as pool:
        manager = MyManager()
        manager.start()
        p = manager.Progress(num_oids)
        try:
            pool.map(_process_map, [(func, mod_name, i, opts, p) for i in oid_list])
        except:
            print('-'*60)
            traceback.print_exc()
            print('-'*60)
        manager.shutdown()

    return True


def multi_map(func: Callable, oid_list: List[str], opts: dict, blocking: bool = False) -> bool:
    num_oids = len(oid_list)
    if num_oids == 0:
        return True
    nprocs = min(num_oids, max_processes)
    with Pool(processes=nprocs) as pool:
        manager = MyManager()
        manager.start()
        p = manager.Progress(num_oids)
        try:
            pool.map(_map_wrapper, [(func, i, opts, p) for i in oid_list])
        except:
            print('-'*60)
            traceback.print_exc()
            print('-'*60)
        manager.shutdown()
    return True


def expand_oids(mod_name: str, oid_list: List[str]) -> List[str]:
    mod_type = oxide.get_mod_type(mod_name)
    if mod_type in ["analyzers", "map_reducers", "source"]:
        return oid_list
    return oxide.expand_oids(oid_list)


def multi_map_callable(func: Callable, oid_list: List[str], opts: dict, blocking: bool = False):
    try:
        num_oids = len(oid_list)
        if num_oids == 0:
            return [], 0
        
        with MyManager() as manager:
            # quit()
    
            p = manager.Progress(num_oids)
            results_q = manager.Queue()
            
            print(max_processes)
            nprocs = min(num_oids, max_processes)
            
            with Pool(processes=nprocs) as pool:
                # print('qsize before', results_q.qsize())
                
                pool.map(_map_reduce_wrapper, [(func, i, opts, p, results_q) for i in oid_list])
                pool.close()
                pool.join()
            results = []
            # print('qsize after', results_q.qsize())
            for _ in range(num_oids):
                result_queue = results_q.get(timeout=1)
                if result_queue[0] == "ERROR":
                    continue
                results.append(result_queue)

        print(dir(results_q))
        manager.shutdown()
        del results_q
        return results, len(results)
    except ValueError:  # FIXME:: This is the wrong exception to be catching
        print('-'*60)
        traceback.print_exc()
        print('-'*60)
    # Exception occurred
    if manager:
        manager.shutdown()
    return [], 0


def multi_map_distrib(proxy_list: List[str], mod_name: str, oid_list: List[str], opts: dict = {},
                      blocking: bool = False, force: bool = False) -> bool:
    if not isinstance(oid_list, list):
        oid_list = [oid_list]

    num_oids = len(oid_list)
    if num_oids == 0:
        return True

    if num_oids == 1:
        proxy = get_proxy(proxy_list[0][0], proxy_list[0][1], True)
        proxy.process(mod_name, oid_list[0], opts, force)
        return True

    nprocs = min(num_oids, max_processes)
    with Pool(processes=nprocs) as pool:
        manager = MyManager()
        manager.start()
        p = manager.Progress(num_oids)
        num_partitions = len(proxy_list)
        list_len = len(oid_list)
        chunk_len = list_len / num_partitions
        pool_jobs = []
        for i in range(num_partitions-1):
            j = oid_list[i*chunk_len:i*chunk_len+chunk_len]
            pool_jobs.append( (proxy_list[i], mod_name, j, opts, p, force) )
        j = oid_list[(num_partitions-1)*chunk_len:]
        pool_jobs.append( (proxy_list[-1], mod_name, j, opts, p, force) )

        try:
            pool.map(_multi_map_process_wrapper, pool_jobs)
        except:
            print('-'*60)
            traceback.print_exc()
            print('-'*60)
        manager.shutdown()
    return True


def _multi_map_process_wrapper(remote_job: Tuple[Tuple[str, int], str, str, dict, Progress, bool]) -> None:
    ((server_ip, server_port), mod_name, i, opts, p, force) = remote_job
    try:
        config.multiproc_on = False
        proxy = get_proxy(server_ip, server_port, True)
        if not proxy:
            logger.error("Not able to get proxy")
            raise
        proxy.process(mod_name, i, opts, force)
        p.tick()
    except:
        print('-'*60)
        traceback.print_exc()
        print('-'*60)


def _map_wrapper(job: Tuple[Callable, str, dict, Progress]) -> None:
    """ Called through multi_map """
    (func, i, opts, p) = job
    try:
        config.multiproc_on = False
        func(i, opts)
        p.tick()
    except:
        print('-'*60)
        traceback.print_exc()
        print('-'*60)


def multi_mapreduce(map_func, reduce_func, oid_list, opts, jobid):
    try:
        num_oids = len(oid_list)
        if num_oids == 0:
            return None
        nprocs = min(num_oids, max_processes)
        with Pool(processes=nprocs) as pool:
            manager = MyManager()
            manager.start()
            p = manager.Progress(num_oids)
            pool.map(_map_reduce_wrapper, [(map_func, i, opts, p) for i in oid_list])
        results = []
        for _ in range(num_oids):
            results.append(results_q.get())

        manager.shutdown()
        return reduce_func(results, opts, jobid)
    except:
        print('-'*60)
        traceback.print_exc()
        print('-'*60)


def _map_reduce_wrapper(job: Tuple[Callable, str, dict, Progress, Any]) -> None:
    """ Called through multi_mapreduce """
    (func, i, opts, p, results_q) = job
    try:
        config.multiproc_on = False
        result = func(i, opts)
        p.tick()
        results_q.put(result)
    except Exception as e:
        print('-'*60)
        traceback.print_exc()
        print('-'*60)
        results_q.put(("ERROR", str(e)))
