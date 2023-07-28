import difflib
import re
from copy import copy
from collections.abc import Iterable, Generator
from itertools import combinations, zip_longest, islice

import unicodedata


def strip_accents(s):
    return "".join(
        c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn"
    )


r_del = lambda s, r: re.sub(r, "", s)


def flatten_deep(xs: list | str) -> Generator:
    for x in xs:
        if isinstance(x, Iterable) and not isinstance(x, (str, bytes)):
            yield from flatten_deep(x)
        else:
            yield x


def merge(original, lists, sep="$"):
    ins_aft = []

    for l in lists:
        ins_aft.append([])
        orig_copy = original[:]

        next_ins = -1
        for i, k in enumerate(l):
            if k in orig_copy:
                next_ins = orig_copy.index(k)
                orig_copy[next_ins] = ""
            elif k == sep:
                ins_aft[-1].append(next_ins)

    i_add = 0

    # Remove duplicates
    for i, k in enumerate(ins_aft):
        for j, l in enumerate(ins_aft):
            if j > i:
                for item in k:
                    if item in ins_aft[j] and item != -2:
                        ins_aft[j][ins_aft[j].index(item)] = -2

    ins_aft = [item for sublist in ins_aft for item in sublist]
    for k in sorted(ins_aft):
        if k != -2:
            original.insert(k + 1 + i_add, sep)

            i_add += 1

    return original


def diff_ratio(x: str, y: str, r: str, sep: str) -> float:
    x = r_del(x, r)
    y = r_del(y, r)
    x_parts = x.split("⧽")
    y_parts = y.split("⧽")

    y_parts, x_parts = list(zip(*zip_longest(x.split("⧽"), y.split("⧽"), fillvalue="")))

    y = "⧽".join([x if x or i == 0 else x_parts[i - 1] for i, x in enumerate(x_parts)])
    x = "⧽".join([z if z or i == 0 else y_parts[i - 1] for i, z in enumerate(y_parts)])
    y = strip_accents(y).lower() if y.replace("$", "").replace("⧽", "") else "$"
    x = strip_accents(x).lower() if x.replace("$", "").replace("⧽", "") else "$"
    # print(x, y)
    ratio = difflib.SequenceMatcher(lambda x: x == sep, x, y).ratio() * len(
        min([x, y], key=len)
    )

    shorter = [x, y].pop([x, y].index(min([x, y], key=len)))
    longer = y if shorter == x else x
    longer_made_shorter = longer[: len(shorter)]

    if len(shorter) > 2:
        shorter = "".join(islice(shorter, None, len(shorter) // 2))
        longer_made_shorter = "".join(
            islice(longer_made_shorter, None, len(longer_made_shorter) // 2)
        )

        # print(shorter, longer_made_shorter)

        beginning_ratio = difflib.SequenceMatcher(
            lambda x: x == sep, shorter, longer_made_shorter
        ).ratio()

        ratio += beginning_ratio / 3
    # print(ratio)
    return ratio


def fix_pairs(pairs: list, fixed_pairs: list, i: int = 0) -> tuple:
    y = pairs.pop(i)[0]
    fixed_pairs.append(y)

    for i, sp in enumerate(pairs):
        x = sp[0]
        if (
            (x[0] == y[0] or x[1] == y[1])
            or (x[0] > y[0] and x[1] < y[1])
            or (x[0] < y[0] and x[1] > y[1])
        ):
            pairs[i] = []

    pairs = [x for x in pairs if x]
    return pairs, fixed_pairs


def pad_and_get_ratio(
    longest: list, orig_l: list, fixed_pairs: list, r: str, sep: str
) -> tuple:
    padded_ll = 0
    padded_l = 0
    longest_copy = copy(longest)
    l = copy(orig_l)

    fixed_pairs = sorted(fixed_pairs, key=lambda x: x[0])
    # print(f'inside pad_and_get_ratio. fixed_pairs: {fixed_pairs}')

    # print('IN PADDING')
    # print(f'l: {l}, longest_copy: {longest_copy}')
    # print(fixed_pairs)

    for x in fixed_pairs:
        # print(x)
        pad = (x[0] + padded_ll) - (x[1] + padded_l)
        # print(f'pad: {pad}, padded_l: {padded_l}')

        if pad > 0:
            l.insert(x[1] + padded_l, pad * [sep])
            padded_l += pad
        elif pad < 0:
            longest_copy.insert(x[0] + padded_ll, -pad * [sep])
            padded_ll -= pad

        longest_copy = list(flatten_deep(longest_copy))
        l = list(flatten_deep(l))
    if len(l) > len(longest):
        longest_copy += [sep] * (len(l) - len(longest_copy))
    elif len(longest_copy) > len(l):
        l += [sep] * (len(longest_copy) - len(l))

    # print(f'l: {l}, longest_copy: {longest_copy}')
    zipped_lists = list(zip(l, longest_copy))
    # print(f'zip: {zipped_lists}')

    true_len = sum(
        [1 if not (r_del(x, r) == r_del(y, r) == sep) else 0 for x, y in zipped_lists]
    )

    scores = [diff_ratio(x, y, r, sep) for x, y in zipped_lists]

    for i, x in enumerate(scores):
        if r_del(zipped_lists[i][0], r) == r_del(zipped_lists[i][1], r) == sep:
            scores[i] = 0
    try:
        ratio = sum(scores) / true_len
    except:
        ratio = 0
    return longest_copy, l, ratio


def best_match(lists: list, clean_regex: str, sep: str = "$") -> list:
    list_prefixes = []
    list_suffixes = []

    for x in lists:
        list_prefix = ""
        list_suffix = ""
        included_ids = set()
        for el in re.findall(clean_regex, x[0]):
            if ">" in el and len(el.split(">")[-1].split("[")[0]) > 1:
                included_ids.add(el.split("[")[-1].split("]")[0])
                list_prefix += el
            elif "<" in el:
                if el.split("[")[-1].split("]")[0] in included_ids:
                    list_suffix += el

        list_prefixes.append(list_prefix)
        list_suffixes.append(list_suffix)

    pairs = list(combinations(lists, 2))
    list_vs = [[] for _ in lists]
    versions = []

    for pair in pairs:
        pair = list(pair)
        longer = pair.pop(pair.index(max(pair, key=len)))
        shorter = pair[0]

        possible_word_pairings = [
            (
                (xi, yi),
                diff_ratio(
                    x if x != sep else "°", y if y != sep else "§", clean_regex, sep
                ),
            )
            for xi, x in enumerate(longer)
            for yi, y in enumerate(shorter)
        ]

        sorted_pairs = sorted(possible_word_pairings, key=lambda x: x[1], reverse=True)
        best_pair = []
        best_score = -1

        for pair_i in range(len(sorted_pairs)):
            remaining_pairs, fixed_pairs = fix_pairs(copy(sorted_pairs), [], pair_i)
            while remaining_pairs:
                remaining_pairs, fixed_pairs = fix_pairs(
                    remaining_pairs, fixed_pairs, 0
                )

            new_longer, new_shorter, ratio = pad_and_get_ratio(
                longer, shorter, fixed_pairs, clean_regex, sep
            )

            if ratio > best_score:
                best_score = ratio
                best_pair = [new_longer, new_shorter]

        list_vs[lists.index(longer)].append(best_pair[0])
        list_vs[lists.index(shorter)].append(best_pair[1])

    for i, l in enumerate(lists):
        versions = list_vs[i]
        list_vs[i] = merge(l, versions, sep)

    for i, l in enumerate(list_vs):
        for k, it in enumerate(l):
            if it == "$":
                list_vs[i][k] = list_prefixes[i] + it + list_suffixes[i]
    maxlen = len(max(list_vs, key=len))

    # Pad
    for i, sublist in enumerate(list_vs):
        list_vs[i] = sublist + [list_prefixes[i] + "$" + list_suffixes[i]] * (
            maxlen - len(sublist)
        )

    return list_vs
