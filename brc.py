#!/usr/bin/python3
# -*- coding: utf-8 -*-

"Break-Reislient Code"

__author__ = "Canran Wang, PhD Candidate @ WashU"

import bitarray as bt
import bitarray.util as btutil
import itertools
import random
import reedsolo
from functools import reduce
from math import ceil, log2


class BRCodec:
    def __init__(
        self,
        l=0,
        m=0,
        t=0,
        k=None,
    ):
        self.t = t

        if k:
            self.l = 1
            while True:
                self.l = self.l + 1
                self.m = 2 * ceil(log2(self.l)) + 2
                self.k = (self.l - self.t) * self.m - 1
                if self.k >= k:
                    break
        else:
            if m < 2 * ceil(log2(l)) + 2:
                print(f"m should be at least {2*ceil(log2(l))+2} bits")
                return
            self.l = l
            self.m = m
            self.k = (self.l - self.t) * self.m - 1

        self.len_zr = ceil(log2(self.m)) + 1  # maximum zero run
        self.len_mu_cw = self.len_zr + self.m + 3  # MU codeword length

        self.len_rs = (self.m + 1) * 4 + 2 * ceil(4 * (self.m + 1) / (2 ** (self.len_zr - 1) - 1 + (self.len_zr - 1))) - 1  # RS redundancy
        self.n = self.len_mu_cw * self.l + self.t * self.len_rs  # BRC cw lenght

        self.identifiers = [btutil.int2ba(r, self.m) for r in range(self.t)]
        self.rscodec = reedsolo.RSCodec(4 * self.t, c_exp=self.m + 1)

        print(f"[CODEC] {self.t}-break-resilient code with k={self.k} (l={self.l}, m={self.m}),  n={self.n}, and rate={self.k/self.n}")

    def __generate_random_iw(self):
        return btutil.urandom(self.k)

    def __fetch_block(self, data, i):
        return data[(i - 1) * self.m : i * self.m]

    def __delete_block(self, data, i):
        del data[(i - 1) * self.m : i * self.m]
        return data

    def __merge_blocks(self, blocks):
        return reduce(lambda x, y: x + y, blocks)

    def __encode_distinct_blocks(self, data):
        i = 1
        i_end = self.l
        while i < i_end:
            j = i + 1
            while j <= i_end:
                if self.__fetch_block(data, i) == self.__fetch_block(data, j):
                    self.__delete_block(data, j)
                    occupied_indices = list(set([btutil.ba2int(self.__fetch_block(data, r)[: ceil(log2(self.l)) + 1]) for r in range(1, self.l)]))
                    occupied_indices.sort()
                    j0 = 0
                    for _ in range(j):
                        j0 = j0 + 1
                        while j0 in occupied_indices:
                            j0 = j0 + 1

                    new_block = btutil.int2ba(j0, length=ceil(log2(self.l)) + 1) + btutil.int2ba(i, length=ceil(log2(self.l)))
                    while len(new_block) < self.m:
                        new_block.append(0)
                    data = data + new_block
                else:
                    j = j + 1
            i = i + 1
        return data

    def __decode_distinct_blocks(self, data):
        while data[-1] == 0:
            last_block = self.__fetch_block(data, self.l)
            j0 = btutil.ba2int(last_block[: ceil(log2(self.l)) + 1])
            i = btutil.ba2int(last_block[ceil(log2(self.l)) + 1 : 2 * ceil(log2(self.l)) + 1])
            j = j0
            occupied_indices = list(set([btutil.ba2int(self.__fetch_block(data, r)[: ceil(log2(self.l)) + 1]) for r in range(1, self.l)]))
            occupied_indices.sort()
            for s in range(1, j0):
                if s in occupied_indices:
                    j = j - 1

            data = reduce(
                lambda x, y: x + y,
                [self.__fetch_block(data, r) for r in range(1, j)] + [self.__fetch_block(data, i)] + [self.__fetch_block(data, r) for r in range(j, self.l)],
            )

        return data[:-1]

    def __encode_rll(self, w, max_allowence):
        result = bt.bitarray()
        chunk_size = 2**max_allowence - 1 + max_allowence
        for j in range(0, len(w), chunk_size):
            chunk = w[j : j + chunk_size]
            chunk.append(1)
            i, i_end = 0, len(chunk) - 1
            while i <= i_end - max_allowence:
                if all(c == 0 for c in chunk[i : i + max_allowence + 1]):
                    del chunk[i : i + max_allowence + 1]
                    chunk = chunk + btutil.int2ba(i + 1, length=max_allowence)
                    chunk.append(0)
                    i_end = i_end - max_allowence - 1
                else:
                    i = i + 1
            result = result + chunk
            result.append(1)
        result.pop()
        return result

    def __decode_rll(self, w, max_allowence):
        result = bt.bitarray()
        chunk_size = 2**max_allowence - 1 + max_allowence
        for i in range(0, len(w), chunk_size + 2):
            chunk = w[i : i + chunk_size + 1]
            while chunk[-1] != 1:
                chunk.pop()
                index = btutil.ba2int(chunk[-max_allowence:]) - 1
                chunk[index:index] = btutil.zeros(max_allowence + 1)
                del chunk[-max_allowence:]
            chunk.pop()
            result = result + chunk
        return result

    def __encode_mu(self, iw):
        return btutil.zeros(self.len_zr) + bt.bitarray("1") + self.__encode_rll(iw, self.len_zr - 1) + bt.bitarray("1")

    def __decode_mu(self, iw):
        return self.__decode_rll(iw[self.len_zr + 1 : -1], self.len_zr - 1)

    def _is_mu_cw(self, w):
        if (not w[: self.len_zr].any()) and w[self.len_zr] == 1:
            return True
        else:
            return False

    def brc_encode(self, iw):
        if len(iw) > self.k:
            print("[ENCODE] Error: Information word is longer than k.")
            return
        iw1 = iw + "0" * (self.k - len(iw)) + "1"
        # print("data is: ", iw1, " len is ", len(iw1))

        data = self.__encode_distinct_blocks(self.__merge_blocks(self.identifiers) + iw1)
        # create parities
        vec = [i for i in range(2**self.m)]
        for i in range(self.t + 1, self.l):
            vec[btutil.ba2int(self.__fetch_block(data, i))] = btutil.ba2int(self.__fetch_block(data, i + 1))
        parities = [btutil.int2ba(parity, self.m + 1) for parity in self.rscodec.encode(vec)[-4 * self.t :]]

        # insert parities inbetween of identifiers
        components = [self.__encode_mu(self.__fetch_block(data, i)) for i in range(1, self.l + 1)]

        [
            components.insert(
                i + 1,
                self.__encode_rll(
                    reduce(lambda x, y: x + y, parities[4 * i : 4 * i + 4]),
                    self.len_zr - 1,
                ),
            )
            for i in reversed(range(self.t))
        ]

        cw = self.__merge_blocks(components)
        return cw

    def brc_decode(self, fragments, verbose=False):
        rss = [-1] * self.t * 4
        approx_vec = [i for i in range(2**self.m)]
        num_error = self.l - self.t - 1
        for fragment in fragments:
            i = 0
            chunks = []
            while i + self.len_mu_cw <= len(fragment):  # check if the length of remaining part is shorter than a mu code.
                window = fragment[i : i + self.len_mu_cw]  # check for the window
                if self._is_mu_cw(window):  # if it's a MU code
                    i = i + self.len_mu_cw
                    block_int = btutil.ba2int(self.__decode_mu(window))  # decode the mu code and check if it's an identifier
                    if block_int < self.t:  # It is an identifier ...
                        if i + self.len_rs <= len(fragment):  # and is long enough, we try to learn the redundancy.
                            rs = self.__decode_rll(fragment[i : i + self.len_rs], self.len_zr - 1)  # First, decode rll and get true redundancy
                            rss[4 * block_int : 4 * (block_int + 1)] = [btutil.ba2int(rs[j * (self.m + 1) : (j + 1) * (self.m + 1)]) for j in range(4)]  # Second, split the redundancy in four parts
                            i = i + self.len_rs
                        else:  # but is not long enough, nothing we can do with the remaining part of the fragment.
                            break
                    else:  # Ok, not an identifier
                        chunks.append(block_int)
                else:
                    i = i + 1
            for b, b_next in zip(chunks[:-1], chunks[1:]):
                num_error = num_error - 1
                approx_vec[b] = b_next
        to_be_decoded = approx_vec + rss

        vec = self.rscodec.decode(
            to_be_decoded,
            erase_pos=[len(approx_vec) + pos for pos in [i for i in range(self.t * 4) if rss[i] == -1]],
        )[0]

        blockss = [[i, vec[i]] for i in range(len(vec)) if i != vec[i]]

        while len(blockss) > 1:
            for pair in itertools.permutations(range(len(blockss)), 2):
                i, j = pair[0], pair[1]
                if blockss[i] and blockss[j] and blockss[i][-1] == blockss[j][0]:
                    blockss[i] = blockss[i] + blockss[j][1:]
                    blockss[j] = []
            blockss = [block for block in blockss if block]

        iw = reduce(
            lambda x, y: x + y,
            [btutil.int2ba(element, length=self.m + 1)[1:] for element in blockss[0]],
        )

        return self.__decode_distinct_blocks(self.__merge_blocks(self.identifiers + [iw]))[self.t * self.m :]

    def randomly_break_codeword(self, cw):
        fragments = []
        breaks = random.sample(range(len(cw) - 1), self.t)
        breaks.sort()

        fragments.append(cw[0 : breaks[0] + 1])
        for b, b_next in zip(breaks[:-1], breaks[1:]):
            fragments.append(cw[b + 1 : b_next + 1])
        fragments.append(cw[breaks[-1] + 1 :])
        random.shuffle(fragments)
        return fragments

    def break_test(self):
        d = 10000000
        for i in range(10000000):
            if i % 100 == 0:
                print(i, "/", d)
            iw = self.__generate_random_iw()
            cw = self.brc_encode(iw)

            fgs = self.randomly_break_codeword(cw)

            decoded_iw = self.brc_decode(fgs)
            if decoded_iw != iw:
                print(decoded_iw.to01())
                print(iw.to01())
                break


if __name__ == "__main__":

    # k = 120, n=425 (3-break), 353 (2-break), 281 (1-break)
    fc = BRCodec(l=12, m=11, t=1)
    Robert_Heinlein = "010100100110111101100010011001010111001001110100001000000100100001100101011010010110111001101100011001010110100101101110"

    cw = fc.brc_encode(Robert_Heinlein)
    print(cw.to01())
