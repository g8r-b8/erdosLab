# Erdős Problem #436: consecutive k-th power residues (triples, k = 5)

**Status (ours):** computational attack on the smallest open case Λ(5,3). No resolution yet.
**Site status:** OPEN (erdosproblems.com/436, rechecked 2026-09-23).

## Statement (erdosproblems.com/436, verbatim in substance)
For a prime p and k, m ≥ 2 let r(k,m,p) be the least r ≥ 1 such that r, r+1, …, r+m−1 are all
k-th power residues mod p, and Λ(k,m) = limsup_{p→∞} r(k,m,p).
Is Λ(k,2) finite for all k? Is Λ(k,3) finite for all odd k? How large are they?

Known (site / OEIS A000445): Λ(k,2) < ∞ for all k (Hildebrand 1991); Λ(2,2)=9, Λ(3,2)=77,
Λ(4,2)=1224, Λ(5,2)=7888, Λ(6,2)=202124, Λ(7,2)=1649375; Λ(3,3)=23532 (Lehmer–Lehmer–Mills–Selfridge
1962, "Machine proof of a theorem on cubic residues"); Λ(k,3)=∞ for even k; Λ(k,l)=∞ for l ≥ 4
(Graham 1964). Open: Λ(k,3) for odd k ≥ 5. Smallest open case: **Λ(5,3)**.
Note: answering "finite for all odd k" needs more than k = 5, but Λ(5,3) = ∞ would disprove it,
and Λ(5,3) < ∞ would be the first new case.

## Openness evidence (copied from NOTES.md triage, rechecked 2026-09-23)
- erdosproblems.com/436: OPEN; forum thread: 3 comments (Adenwalla 24–25 Oct 2025, Bloom 25 Oct
  2025) — notation fix, LLMS 1962 reference, a literature compilation; no claims, no computations.
  No see-also / duplicate links.
- teorth/erdosproblems problems.yaml: 436 open, formal_status "unformalized".
- formal-conjectures: no ErdosProblems/436 file; issue #731 "Erdős Problem 436" open ("up for
  grabs", 0 comments).
- Tao's AI-contributions wiki (clone, last commit 2026-06-30): no mention of 436.
- arXiv/web: Dietzel 1309.7506, 1810.01518 (pairs / Hildebrand) only; nothing on triples for k ≥ 5.
  (Williams 1976 "Explicit criteria for quintic residuacity" is about which small q are quintic
  residues, not runs.)

## Definition ↔ combinatorial model (the reduction)
Λ_comb(k,l) := sup over completely additive f: Z_{>0} → Z/k of the least r with
f(r) = … = f(r+l−1) = 0.

**Upper bound (elementary, what "finite" needs): Λ(k,l) ≤ Λ_comb(k,l).**
Given p, let d = gcd(k, p−1), g a primitive root, and f_p(n) = (k/d)·(ind_g n mod d) ∈ Z/k for
p ∤ n. f_p is a homomorphism (Z/p)^* → Z/k with f_p(n) = 0 ⇔ n is a k-th power residue (for p ∤ n,
n is a k-th power ⇔ d | ind n). Extend to all positive integers by F(q) = f_p(q) for primes q < p,
F(q) = 1 otherwise; then F is completely additive and F(n) = f_p(n) for 1 ≤ n < p. If
Λ_comb = L < ∞, F has a zero run at some r ≤ L, and for p > L+l−1 these are k-th power residues:
r(k,l,p) ≤ L for all p > L+l−1. (This covers all p, not only p ≡ 1 mod k.)
Moreover S(R) := "∃ f with no zero run at r ≤ R" only involves f on primes ≤ R+l−1, so
Λ_comb ≤ R ⇔ the finite SAT instance S(R) is UNSAT. By compactness (König), Λ_comb = ∞ ⇔ some f
has no zero run at all.

**Lower bound (needs Chebotarev; only needed for exact values / for Λ = ∞):** for odd k the primes
q_1 < … < q_m are independent in Q(ζ_k)^*/(Q(ζ_k)^*)^k, so by Chebotarev in
Q(ζ_k, q_1^{1/k}, …, q_m^{1/k}) every assignment of the q_i's k-th power characters (up to a unit of
Z/k) occurs for infinitely many p ≡ 1 mod k. Hence Λ(k,l) = Λ_comb(k,l) for odd k (also a model with
no zero run up to R gives Λ(k,l) ≥ R). For even k there can be Kummer obstructions (e.g. √2 ∈ Q(ζ_8)),
so the model is only an upper bound there — but it still reproduces the known values for k = 2, 4.

## Results
1. **Validation** (`scripts/lam_sat.py` incremental pysat/CaDiCaL; `scripts/lamenc.c` + kissat via
   `scripts/drive.py`): exact search reproduces Λ_comb = 9, 77, 1224, 7888 for (k,2), k = 2..5, and
   Λ_comb(3,3) = 23532 (kissat 2 s; final UNSAT DRAT proof checked by drat-trim, 1.2 MB LRAT).
   So the model matches all literature values tested.
2. **k = 5, l = 3 — full instance** (see Log below).
3. **k = 5, l = 3 — smooth weakening F_y(X)** (see Log below).

## Files
- `scripts/lam_sat.py` — reference incremental encoder + exact search (pysat Cadical153).
- `scripts/lamenc.c` — compact DIMACS encoder (dominance for primes > N/2; z-only composites) and
  model decoder; `scripts/drive.py` — exact / geometric search with kissat.
- `scripts/smoothruns.c` — segmented sieve listing runs of l consecutive y-smooth numbers ≤ X.
- `scripts/smooth_sat.py` — weakened instance F_y(X) (only primes ≤ y, only smooth runs).
- `logs/` — solver logs.

## Log
(see below)

## Next steps
(see below)
