#!/usr/bin/python3
# -*- coding: utf-8 -*-

"Break-Reislient Code"

__author__ = "Canran Wang, PhD"

# import bitarray as bt
# import bitarray.util as btutil
import itertools
import random
import reedsolo
from functools import reduce
from math import ceil, log2


class BRCodec:

    def br(self, a, length):
        if a < 0:
            raise ValueError("This function only supports non-negative integers.")
        binary = bin(a)[2:]  # Get the binary representation and remove the '0b' prefix
        if len(binary) > length:
            raise ValueError(f"Cannot represent {a} in {length} bits.")
        return binary.zfill(length)

    def __init__(
        self,
        l=0,
        m=0,
        t=0,
        k=None,
    ):
        self.t = t

        if k:
            self.l = self.t
            while True:
                self.l += 1
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

        self.len_rs = (self.m + 2) * 4 + 3  # RS redundancy
        self.n = self.l * self.len_mu_cw + self.t * self.len_rs  # BRC cw lenght
        # print(self.len_mu_cw, self.l, self.t, self.len_rs)
        # exit()

        self.identifiers = [self.br(r, self.m) for r in range(self.t)]
        self.rscodec = reedsolo.RSCodec(4 * self.t, c_exp=self.m + 1)
        # print(f"[CODEC] {self.t}-break-resilient code with k={self.k} (l={self.l}, m={self.m}),  n={self.n}, and rate={self.k/self.n}")

    def __generate_random_iw(self):
        return "".join(random.choice("01") for _ in range(self.k))

    def __encode_distinct_blocks(self, data):
        i = 1
        i_end = self.l
        while i < i_end:
            j = i + 1
            while j <= i_end:
                if data[i - 1] == data[j - 1]:
                    del data[j - 1]
                    occupied_indices = list(set([int(data[r - 1][: ceil(log2(self.l)) + 1], 2) for r in range(1, self.l)]))
                    occupied_indices.sort()
                    j0 = 0
                    for _ in range(j):
                        j0 = j0 + 1
                        while j0 in occupied_indices:
                            j0 = j0 + 1

                    new_block = self.br(j0, ceil(log2(self.l)) + 1) + self.br(i, ceil(log2(self.l)))
                    while len(new_block) < self.m:
                        new_block += "0"
                    data.append(new_block)
                else:
                    j = j + 1
            i = i + 1
        return data

    def __decode_distinct_blocks(self, data):
        while data[-1][-1] == "0":
            last_block = data[-1]
            j0 = int(last_block[: ceil(log2(self.l)) + 1], 2)
            i = int(last_block[ceil(log2(self.l)) + 1 : 2 * ceil(log2(self.l)) + 1], 2)
            j = j0
            occupied_indices = list(set([int(data[r - 1][: ceil(log2(self.l)) + 1], 2) for r in range(1, self.l)]))
            occupied_indices.sort()
            for s in range(1, j0):
                if s in occupied_indices:
                    j = j - 1

            data = reduce(
                lambda x, y: x + y,
                [data[r - 1] for r in range(1, j)] + [data[i - 1]] + [data[r - 1] for r in range(j, self.l)],
            )
        print(data)

        return data[:-1]

    def __encode_rll_single(self, w: str, max_allowence=None) -> str:
        if max_allowence is None:
            max_allowence = self.len_zr - 1

        chunk_size = 2**max_allowence - 1 + max_allowence
        if chunk_size < len(w):
            print("[ERROR] Too small max_allowence.")
            return
        chunk = w + "1"
        i, i_end = 0, len(chunk) - 1
        while i <= i_end - max_allowence:
            if all(c == "0" for c in chunk[i : i + max_allowence + 1]):
                chunk = chunk[:i] + chunk[i + max_allowence + 1 :]
                chunk += self.br(i + 1, length=max_allowence) + "0"
                i_end = i_end - max_allowence - 1
            else:
                i = i + 1
        return chunk

    def __decode_rll_single(self, w: str, max_allowence=None) -> str:
        if max_allowence is None:
            max_allowence = self.len_zr - 1
        chunk_size = 2**max_allowence - 1 + max_allowence
        if len(w) > chunk_size + 1:
            print("[ERROR] Too long cannot decode")
            return
        chunk = w
        while chunk[-1] != "1":
            chunk = chunk[:-1]
            index = int(chunk[-max_allowence:], 2) - 1
            chunk = chunk[:index] + "0" * (max_allowence + 1) + chunk[index:-max_allowence]
        return chunk[:-1]

    def __encode_mu(self, iw):
        # return btutil.zeros(self.len_zr) + bt.bitarray("1") + self.__encode_rll_single(iw) + bt.bitarray("1")
        return "0" * self.len_zr + "1" + self.__encode_rll_single(iw) + "1"

    def __decode_mu(self, iw):
        # print("trying to decode mu")
        return self.__decode_rll_single(iw[self.len_zr + 1 : -1], self.len_zr - 1)

    def _is_mu_cw(self, w):
        if ("1" not in w[: self.len_zr]) and w[self.len_zr] == "1":
            return True
        else:
            return False

    def brc_encode(self, iw):
        if len(iw) > self.k:
            print("[ENCODE] Error: Information word is longer than k.")
            return
        iw1 = iw + "0" * (self.k - len(iw)) + "1"
        data = self.__encode_distinct_blocks(self.identifiers + [iw1[ll : ll + self.m] for ll in range(self.l - self.t)])
        print(data)
        # create the kv-store \textt{next}
        next_kv = [i for i in range(2**self.m)]
        for i in range(self.t + 1, self.l):
            next_kv[int(data[i - 1], 2)] = int(data[i], 2)

        # create parities from \textt{next}
        parities = [self.br(parity, self.m + 1) for parity in self.rscodec.encode(next_kv)[-4 * self.t :]]
        # encode every makers
        components = [self.__encode_mu(marker) for marker in data]
        # encode parities with RLL and insert them in between of identifiers
        [
            components.insert(
                i + 1,
                self.__encode_rll_single(parities[4 * i])
                + "1"
                + self.__encode_rll_single(parities[4 * i + 1])
                + "1"
                + self.__encode_rll_single(parities[4 * i + 2])
                + "1"
                + self.__encode_rll_single(parities[4 * i + 3]),
            )
            for i in reversed(range(self.t))
        ]
        cw = "".join(component for component in components)
        # print("cw: ", cw)
        # print(f"Parities: parities {self.rscodec.encode(next_kv)[-4 * self.t :]}")

        # print(f"Parities: parities {[self.__encode_rll_single(parity)  for parity in parities   ]  }")

        return cw

    def brc_decode(self, fragments, verbose=False):
        rss = [-1] * self.t * 4  # parties
        approx_next_kv = [i for i in range(2**self.m)]
        num_error = self.l - self.t - 1
        for fragment in fragments:
            # print("Checking: " + fragment)
            i = 0
            chunks = []
            while i + self.len_mu_cw <= len(fragment):  # check if the length of remaining part is shorter than a mu code.
                window = fragment[i : i + self.len_mu_cw]  # check for the window
                if self._is_mu_cw(window):  # if it's a MU code
                    i = i + self.len_mu_cw
                    block_int = int(self.__decode_mu(window), 2)  # decode the mu code and check if it's an identifier
                    if block_int < self.t:  # It is an identifier ...
                        # print(f"Find identifier {block_int}, \nchekcing its back")
                        j = i - self.len_mu_cw - (self.m + 1)
                        for n_pre_chunk in range(3):
                            start = j - (self.m + 2) * n_pre_chunk
                            if start < 0:
                                break
                            rss[block_int - n_pre_chunk - 1] = int(self.__decode_rll_single(fragment[start : start + self.m + 1]))
                        # print("chekcing its next")
                        ip = i
                        for idx in range(4):
                            if ip + self.m + 2 >= len(fragment):
                                break
                            rss[block_int + idx] = int(self.__decode_rll_single(fragment[ip : ip + self.m + 2]), 2)
                            # print(f"data is {fragment[ip : ip + self.m + 2]}, decoded is {rss[block_int + idx]}")
                            ip += self.m + 3
                        # print(f"Done for identifier {block_int}")
                    else:  # Ok, not an identifier
                        chunks.append(block_int)
                        # print(window)
                else:  # if it's not a MU code
                    i = i + 1
            for b, b_next in zip(chunks[:-1], chunks[1:]):
                num_error = num_error - 1
                approx_next_kv[b] = b_next
        to_be_decoded = approx_next_kv + rss

        print("ERR vs RSS:", num_error, rss)

        next_kv = self.rscodec.decode(
            to_be_decoded,
            erase_pos=[len(approx_next_kv) + pos for pos in [i for i in range(self.t * 4) if rss[i] == -1]],
        )[0]

        blockss = [[i, next_kv[i]] for i in range(len(next_kv)) if i != next_kv[i]]

        while len(blockss) > 1:
            for i, j in itertools.permutations(range(len(blockss)), 2):
                if blockss[i] and blockss[j] and blockss[i][-1] == blockss[j][0]:
                    blockss[i] = blockss[i] + blockss[j][1:]
                    blockss[j] = []
            blockss = [block for block in blockss if block]

        # print([self.br(element, self.m + 1) for element in blockss[0]])
        data = self.identifiers + [self.br(element, self.m + 1)[1:] for element in blockss[0]]
        print(data)

        return ("".join(self.__decode_distinct_blocks(data)[self.t :]))[:-1]
        print("".join(self.__decode_distinct_blocks(data)[self.t + 1 :]))

    def randomly_break_codeword(self, cw: str) -> list[str]:
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
        d = 1
        for i in range(d):
            if i % 10 == 0:
                print(i, "/", d)
            iw = self.__generate_random_iw()

            cw = self.brc_encode(iw)

            fgs = self.randomly_break_codeword(cw)
            decoded_iw = self.brc_decode(fgs)

            print(f"     iw: ", iw)
            print(f"decoded: ", decoded_iw)

            # if decoded_iw != iw:
            #     print(decoded_iw.to01())
            #     print(iw.to01())
            #     break


if __name__ == "__main__":

    # k = 120, n=425 (3-break), 353 (2-break), 281 (1-break)
    fc = BRCodec(l=12, m=11, t=1)
    fc.break_test()

    # Robert_Heinlein = "010100100110111101100010011001010111001001110100001000000100100001100101011010010110111001101100011001010110100101101110"

    # cw = fc.brc_encode(Robert_Heinlein)
    # print(cw.to01())
