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

""" progress.py

Utility class to display estimate progress
"""
import sys
import time


class Progress:
    """ Utility class to display estimate progress on some task.
    """
    def __init__(self, total: int = 1, freq: int = 0) -> None:
        self.total = total
        if freq < 1:
            self.freq = 1
            if total > 1000:
                self.freq = total // 1000
        else:
            self.freq = int(freq)

        self.count = 0
        self.time = 0
        self.last_tick = time.time()

    def tick(self) -> None:
        """ Update tick mark and display at interval.
        """
        if self.total == 1:
            return

        self.count += 1

        # update time and last_tick
        now = time.time()
        self.time += now - self.last_tick
        self.last_tick = now

        if not self.count % self.freq:
            if self.time:
                rate = self.count / float(self.time)
                est = (self.total - self.count) / float(rate)
                est /= 60  # Convert to minutes
                est_scale = 'm'  # Default to minutes
                if est > 60:  # Convert to hours if there is more than 1
                    est /= 60
                    est_scale = 'h'

                # Same thing for the total time
                print_time = self.time / float(60)
                time_scale = 'm'
                if print_time > 60:
                    print_time /= 60
                    time_scale = 'h'

                sys.stderr.write("Processed {}/{} ({:.2f}%)   time: {:.2f}{}   est: {:.2f}{}   {:.2f} per/s\r".format(
                                 self.count, self.total, (100 * self.count) / float(self.total),
                                 print_time, time_scale, est, est_scale, rate))

        if self.count == self.total:
            print()
