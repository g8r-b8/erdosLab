"""unittest suite for the #470 search (run: cd problems/470/scripts && python3 -m unittest -v test_ows)."""
from __future__ import annotations

import unittest


class TestArith(unittest.TestCase):
    def test_placeholder(self) -> None:
        """TODO: primality vs sieve, sigma/divisors on small n."""
        self.skipTest("not written yet")


class TestSubsetSum(unittest.TestCase):
    def test_placeholder(self) -> None:
        """TODO: is_pseudoperfect vs brute force for all abundant n < 10^5 (weird list A006037)."""
        self.skipTest("not written yet")


class TestLastPrime(unittest.TestCase):
    def test_placeholder(self) -> None:
        """TODO: settle_prefix agrees with per-n brute force on Ω ≤ 6 prefixes."""
        self.skipTest("not written yet")


if __name__ == "__main__":
    unittest.main()
