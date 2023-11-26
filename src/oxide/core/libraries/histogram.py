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

""" histogram.py
"""
import collections
from collections import defaultdict
from math import log

from typing import Tuple, List, Dict, Any

NAME = "histogram"


def build_histo(input_list: List[Any]) -> Dict[Any, int]:
    histo = defaultdict(int)
    for i in input_list:
        histo[i] += 1
    return histo


def build_ngrams(input_list: List[bytes], n: int) -> Dict[str, int]:
    ngrams = defaultdict(int)
    # ngram holds a rotating set of elements constituting the current ngram
    ngram = [str(x) for x in input_list[:n-1]]
    for x in input_list[n-1:]:
        ngram.append(str(x))
        ngram_str = ",".join(ngram)
        ngrams[ngram_str] += 1
        del ngram[0]
    return ngrams


def merge_histo(main_histo: dict, new_histo: dict) -> dict:
    if new_histo:
        for i in new_histo:
            main_histo[i] += new_histo[i]
    return main_histo


def build_ngram_freq(data: bytes, n: int = 1) -> collections.Counter:
    """ Takes a sequence containing data, typically a string of binary data.
        Returns a Counter object that has non-overlapping subsequences of
        length n as keys and the frequency that subsequence occured as the values.
    """
    return collections.Counter(data[i:i + n] for i in range(0, len(data), n))


def calc_entropy(data_sequence: bytes) -> float:
    """
    Calculates the b-ary entropy
    In general the b-ary entropy of a source {S} = (S,P) with source alphabet
    S = {a1, ..., an} and discrete probability distribution P = {p1, ..., pn}
    where pi is the probability of ai (say pi = p(ai)) is defined by:
        H_b({S}) = - sum_(1 >= i <= n) p_i * log_b * p_i
    Note: the b in "b-ary entropy" is the number of different symbols of the
    "ideal alphabet" which is being used as the standard yardstick to measure
    source alphabets. In information theory, two symbols are necessary and
    sufficient for an alphabet to be able to encode information, therefore
    the default is to let b = 2 ("binary entropy"). Thus, the entropy of the
    source alphabet, with its given empiric probability distribution, is a
    number equal to the number (possibly fractional) of symbols of the "ideal
    alphabet", with an optimal probability distribution, necessary to encode
    for each symbol of the source alphabet. Also note that "optimal probability
    distribution" here means a uniform distribution: a source alphabet with
    n symbols has the highest possible entropy (for an alphabet with n symbols)
    when the probability distribution of the alphabet is uniform. This optimal
    entropy turns out to be logb(n).
    """
    entropy = 0
    total = len(data_sequence)
    histogram = collections.Counter(data_sequence)
    for count in histogram.values():
        probability = count / total
        entropy -= probability * log(probability, 256)
    return entropy


def normalize_dict(d: dict) -> Dict[Any, float]:
    """ Takes a dictionary  (or dictionary like object) with numbers as values.
        returns a dictionary with the values normalized.
    """
    ret = {}
    total = sum(d.values())
    for key, value in d.items():
        ret[key] = value / total
    return ret


def harmonize_dicts(d_1: dict, d_2: dict) -> Tuple[list, list]:
    """ Takes two dictionaries  (or dictionary like objects).
        Returns two lists that are the values for the two dictionaries, where
        entries for each index had the same key. Where an entry was in one
        dictionary, but not the other, a value of zero is used to correspond
        to the missing entry.
    """
    l_1 = []
    l_2 = []
    seen_keys = []
    for key, value in d_1.items():
        l_1.append(value)
        l_2.append(d_2.get(key, 0.0))
        seen_keys.append(key)
    for key in d_2:
        if key not in seen_keys:
            l_1.append(0.0)
            l_2.append(d_2[key])
    return l_1, l_2


def pearson(x: List[int], y: List[int]) -> float:
    """ Takes two lists of numerical values.
        Returns a value between 1 and -1.
        The vaue is a "Pearson Correlation Coefficient".
        This coefficient is a measure of how highly correlated two values are.
    """
    n = len(x)
    vals = range(n)
    sum_x = sum([float(x[i]) for i in vals])
    sum_y = sum([float(y[i]) for i in vals])
    sum_sq_x = sum([x[i]**2.0 for i in vals])
    sum_sq_y = sum([y[i]**2.0 for i in vals])
    product_sum = sum([x[i] * y[i] for i in vals])
    num = product_sum - (sum_x * sum_y / n)
    den = ((sum_sq_x - pow(sum_x, 2) / n) * (sum_sq_y - pow(sum_y, 2) / n)) ** 0.5
    if den == 0:  # avoid dividing by 0
        return 1.0
    return num / den
