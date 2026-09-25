"""unittest suite for the #470 search (run: cd problems/470/scripts && python3 -m unittest -v test_ows)."""
from __future__ import annotations

import random
import unittest

from arith import divisors, factor_small, is_probable_prime, mul_prime, next_prime, sigma, value
from intervals import IntervalSet
from subsetsum import is_pseudoperfect, subset_sums, witness

# OEIS A006037 (weird numbers), all terms < 20000
WEIRD_BELOW_20000 = [70, 836, 4030, 5830, 7192, 7912, 9272, 10430, 10570, 10792, 10990, 11410,
                     11690, 12110, 12530, 12670, 13370, 13510, 13790, 13930, 14770, 15610, 15890,
                     16030, 16310, 16730, 16870, 17272, 17570, 17990, 18410, 18830, 18970, 19390,
                     19670, 19810]


def sieve(n: int) -> list:
    b = bytearray([1]) * (n + 1)
    b[0] = b[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if b[i]:
            b[i * i::i] = bytearray(len(b[i * i::i]))
    return b


def brute_pseudoperfect(n: int) -> bool:
    bits = 1
    for d in range(1, n):
        if n % d == 0:
            bits |= bits << d
    return (bits >> n) & 1 == 1


class TestArith(unittest.TestCase):
    def test_primes(self) -> None:
        b = sieve(100_000)
        for n in range(100_000):
            self.assertEqual(is_probable_prime(n), bool(b[n]), n)
        self.assertEqual(next_prime(2), 3)
        self.assertEqual(next_prime(40), 41)
        self.assertTrue(is_probable_prime(2 ** 61 - 1))
        self.assertFalse(is_probable_prime(3215031751))  # strong pseudoprime to bases 2,3,5,7

    def test_sigma_divisors(self) -> None:
        self.assertEqual(sigma(((2, 2), (3, 1))), 28)
        self.assertEqual(value(((3, 3), (5, 1), (7, 1))), 945)
        self.assertEqual(divisors(((2, 1), (5, 1), (7, 1))), [1, 2, 5, 7, 10, 14, 35, 70])
        self.assertEqual(factor_small(945), ((3, 3), (5, 1), (7, 1)))
        self.assertEqual(mul_prime(((3, 1),), 3), ((3, 2),))
        self.assertEqual(mul_prime(((3, 1),), 5), ((3, 1), (5, 1)))
        for n in range(2, 3000):
            f = factor_small(n)
            self.assertEqual(value(f), n)
            self.assertEqual(sigma(f), sum(divisors(f)))


class TestIntervals(unittest.TestCase):
    def test_basic(self) -> None:
        self.assertEqual(IntervalSet([(3, 5), (0, 1), (2, 2)]).ivs, [(0, 5)])
        self.assertEqual(IntervalSet.normalize([(5, 7), (1, 2), (3, 4)]), [(1, 7)])
        self.assertEqual(IntervalSet([(0, 0)]).union_shift(3).ivs, [(0, 0), (3, 3)])
        A = IntervalSet([(0, 10), (20, 30)])
        self.assertEqual(A.subtract(IntervalSet([(5, 22)])).ivs, [(0, 4), (23, 30)])
        self.assertEqual(A.intersect_range(8, 25).ivs, [(8, 10), (20, 25)])
        self.assertEqual(A.size(), 22)

    def test_random_vs_sets(self) -> None:
        rng = random.Random(1)
        for _ in range(300):
            xs = {rng.randrange(60) for _ in range(rng.randrange(30))}
            ys = {rng.randrange(60) for _ in range(rng.randrange(30))}
            X, Y = IntervalSet([(x, x) for x in xs]), IntervalSet([(y, y) for y in ys])
            d = rng.randrange(20)
            self.assertEqual({v for v in range(100) if X.union_shift(d).contains(v)},
                             xs | {x + d for x in xs})
            self.assertEqual({v for v in range(100) if X.subtract(Y).contains(v)}, xs - ys)


class TestSubsetSum(unittest.TestCase):
    def test_small(self) -> None:
        S = subset_sums([1, 3, 5])
        self.assertEqual([v for v in range(12) if S.contains(v)], [0, 1, 3, 4, 5, 6, 8, 9])
        self.assertFalse(is_pseudoperfect(factor_small(70)))
        self.assertFalse(is_pseudoperfect(factor_small(836)))
        self.assertTrue(is_pseudoperfect(factor_small(12)))
        self.assertTrue(is_pseudoperfect(factor_small(945)))

    def test_weird_list(self) -> None:
        weird = [n for n in range(2, 20000)
                 if sigma(factor_small(n)) > 2 * n and not is_pseudoperfect(factor_small(n))]
        self.assertEqual(weird, WEIRD_BELOW_20000)

    def test_vs_brute(self) -> None:
        for n in range(2, 3000):
            f = factor_small(n)
            if sigma(f) >= 2 * n:
                self.assertEqual(is_pseudoperfect(f), brute_pseudoperfect(n), n)

    def test_witness(self) -> None:
        for n in [12, 945, 1575, 15015, 81081, 20]:
            w = witness(factor_small(n))
            self.assertEqual(sum(w), n)
            self.assertEqual(len(set(w)), len(w))
            self.assertTrue(all(n % d == 0 and d < n for d in w))
        self.assertIsNone(witness(factor_small(70)))


class TestLastPrime(unittest.TestCase):
    def test_placeholder(self) -> None:
        """TODO: settle_prefix agrees with per-n brute force on Ω ≤ 6 prefixes."""
        self.skipTest("not written yet")


if __name__ == "__main__":
    unittest.main()
