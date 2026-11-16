"""Exact finite checks to guide formalization; this is not a Lean proof.

Primary source: Yao--Jafar, arXiv:2206.10049v3, Examples 1,2,4 and Remark 6.1.
The journal-layout author PDF repeats the same examples and assertion:
https://escholarship.org/content/qt44b1c5hm/qt44b1c5hm.pdf
All arithmetic below is exact modulo the indicated prime.
"""
from fractions import Fraction
from itertools import permutations, product
import json


def rank(rows, prime):
    a = [list(row) for row in rows]
    result = 0
    for j in range(3):
        pivot = next((i for i in range(result, len(a)) if a[i][j] % prime), None)
        if pivot is None:
            continue
        a[pivot], a[result] = a[result], a[pivot]
        a[result] = [(v * pow(a[result][j], -1, prime)) % prime for v in a[result]]
        for i in range(len(a)):
            if i != result:
                multiple = a[i][j]
                a[i] = [(v - multiple * w) % prime for v, w in zip(a[i], a[result])]
        result += 1
    return result


def rows(t):
    # Ordered W'_1,W'_2,W'_3,W_1,W_2,W_3.
    return [(1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 1), (1, 0, 1), (1, t, 0)]


def all_subset_ranks(t, prime):
    return [rank([rows(t)[i] for i in range(6) if mask >> i & 1], prime)
            for mask in range(64)]


def span(generators, prime):
    return {tuple(sum(c * x[j] for c, x in zip(cs, generators)) % prime for j in range(3))
            for cs in product(range(prime), repeat=len(generators))}


def join(a, b, prime):
    return {tuple((x + y) % prime for x, y in zip(u, v)) for u in a for v in b}


def dimension(space, prime):
    size, result = len(space), 0
    while size > 1:
        assert size % prime == 0
        size //= prime
        result += 1
    return result


def profile(t, prime):
    side = [span([x], prime) for x in rows(t)[:3]]
    signal = [span([x, y], prime) for x, y in zip(rows(t)[:3], rows(t)[3:])]

    def cr(c, b):
        return dimension(join(c, b, prime), prime) - dimension(b, prime)

    first = [3 - cr(signal[i] & signal[j], side[j])
             - cr(signal[k] & join(signal[i], signal[j], prime), side[k])
             for i, j, k in permutations(range(3))]
    second = []
    for i in range(3):
        j, k = [r for r in range(3) if r != i]
        for ell in range(3):
            subtracted = (cr(signal[0] & signal[1] & signal[2], side[ell])
                          + cr(join(signal[i] & signal[j], signal[i] & signal[k], prime), side[i])
                          + cr(signal[j] & join(signal[i], signal[k], prime), side[j])
                          + cr(signal[k] & join(signal[i], signal[j], prime), side[k]))
            second.append(3 - Fraction(subtracted, 2))
    return {"first": first, "second": list(map(str, second)),
            "maximum": str(max(first + second))}


def binary_example():
    # Exact Example 4: sides A,B,A+B; demands B,A+B,A.
    source = list(product(range(2), repeat=2))
    side = lambda x: (x[0], x[1], x[0] ^ x[1])
    demand = lambda x: (x[1], x[0] ^ x[1], x[0])
    witnesses = []
    for j, x in enumerate(source):
        for y in source[j + 1:]:
            users = [i for i in range(3) if side(x)[i] == side(y)[i]
                     and demand(x)[i] != demand(y)[i]]
            assert users
            witnesses.append({"x": x, "y": y, "user": users[0]})
    # The source prints this two-instance code. Verify all local recoveries
    # by checking that equal (broadcast, own sides) force equal own demands.
    blocks = list(product(source, repeat=2))
    def broadcast(block):
        (a1, b1), (a2, b2) = block
        return a1 ^ a2 ^ b2, a1 ^ b1 ^ b2
    for i in range(3):
        seen = {}
        for block in blocks:
            key = broadcast(block), tuple(side(x)[i] for x in block)
            value = tuple(demand(x)[i] for x in block)
            assert key not in seen or seen[key] == value
            seen[key] = value
    assert len({broadcast(x) for x in blocks}) == 4
    return {"all_six_source_pairs_confusable": witnesses,
            "scalar_broadcast_required_messages": 4,
            "literal_two_instance_broadcast_messages": 4}


if __name__ == "__main__":
    result = {"status": "Exact finite arithmetic evidence; not a Lean certificate.",
              "variable_order": ["W'_1", "W'_2", "W'_3", "W_1", "W_2", "W_3"],
              "coefficient_rows": {"t=1": rows(1), "t=2": rows(2)}, "fields": {}}
    for prime in (3, 5, 7):
        left, right = all_subset_ranks(1, prime), all_subset_ranks(2, prime)
        mismatches = [{"mask": mask, "selected": [i for i in range(6) if mask >> i & 1],
                       "left_rank": left[mask], "right_rank": right[mask]}
                      for mask in range(64) if left[mask] != right[mask]]
        result["fields"][str(prime)] = {
            "left_subset_ranks": left, "right_subset_ranks": right,
            "mismatches": mismatches,
            "left_profile": profile(1, prime), "right_profile": profile(2, prime)}
    assert result["fields"]["3"]["mismatches"] == [
        {"mask": 56, "selected": [3, 4, 5], "left_rank": 3, "right_rank": 2}]
    assert not result["fields"]["5"]["mismatches"]
    assert not result["fields"]["7"]["mismatches"]
    result["binary_example_4"] = binary_example()
    print(json.dumps(result, indent=2))
