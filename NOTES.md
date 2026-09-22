# erdosLab notes

## Status (iteration 1, 2026-09-22)
- Lean: elan installed (~/.elan/bin), Lean v4.35.0-rc2. Mathlib project `Erdos/` works
  (`import Mathlib` test compiles, ~78s cold). Run with `cd Erdos && lake env lean <file>`.
- Data: cloned teorth/erdosproblems (data/problems.yaml, updated 2026-09-22) and
  google-deepmind/formal-conjectures into the session scratchpad.
- Site stats: 1221 problems; 593 with status exactly "open".

## Observations
- "decidable" status (19, 475, 506, 551, 556, 580, 742, 848) = proven for large n with
  ineffective/huge thresholds → finite check not feasible. Skip.
- erdosproblems.com pages show community "looks tractable" votes and proof-claim counts —
  use these to rank candidates.
- Recent problems (1050–1221) have had less attention → triage there first.

## ★ ACTIVE TARGET: #468 — DISPROOF of "f(N)=o(N) (for almost all N)"
Statement: D_n = {d1, d1+d2, ...} (1<d1<d2<... divisors of n); f(N) = min n with N ∈ D_n.
Is f(N)=o(N)? Perhaps for almost all N?
Open evidence (checked 2026-09-22): erdosproblems.com/468 OPEN, 0 proof claims, 1 comment
(Vjeko_Kovac 14 Sep 2025: data suggests o(N) false; only trivial liminf f(N)/N=0 known).
Not on Tao's AI-contributions wiki. formal-conjectures: only open PR #4076 (statement, May 2026).
Web search: nothing else.

THEOREM (ours): for all K≥1, X: #{N ≤ X : ∃ n, Kn ≤ N, N ∈ D_n} ≤ S·X/K², S ≤ ζ(2)·2ζ(3) ≈ 3.95.
So f(N) > N/3 for ≥ 56% of N ≤ X (every X). Answer: NO, even for almost all N.
Proof: N = prefix sum at divisor d=n/e, N ≤ Σ_{d'|n,d'≤d} d' = n·T_e(n), T_e(n)=Σ_{e'|n,e'≥e} 1/e'.
So Kn ≤ N ⇒ T_e(n) ≥ K. Count ≤ Σ_{n≤X/K} #{e|n : T_e ≥ K} ≤ (1/K) Σ_{n≤X/K} Σ_{e|n} T_e(n).
Σ_{n≤Y} Σ_{e|n} T_e(n) = Σ_{e≤e'} (1/e')·#{n≤Y: lcm(e,e')|n} ≤ Y·Σ_{e≤e'} gcd(e,e')/(e·e'^2)
≤ Y·Σ_{e'} (1/e'^2)Σ_{g|e'} H(e'/g) = Y·ζ(2)·Σ_b H_b/b² = Y·ζ(2)·2ζ(3).
Numerics (scratchpad/e468/check.py, X=2e5): covered fraction K=1 .319, K=2 .046, K=3 .004;
pairs/X ≤ bound in all cases.
Lean status (iter ~10): Erdos/Erdos/E468.lean — ALL lemmas proved except `sum_T_le`
(DONE — merged; whole file sorry-free, axioms: propext, Classical.choice, Quot.sound). Final theorem `not_erdos468AlmostAll`.
Lean plan: prove ∃K, ∀X, covered(K,X) ≤ X/2 via summability (no explicit constants needed),
then ¬(almost-all o(N)) as in PR #4076's Erdos468MinimalPreimageLittleOAlmostAll.

## Candidates (ranked; each needs open-verification evidence before work)
- 1210 — pairwise coprime A ⊆ [1,n), is Σ 1/(n−a) ≤ Σ_{p<n} 1/p + O(1)? 3 "looks tractable"
  votes. Open per site (checked 2026-09-22, last update 2026-04-08). Concern: needs sharp
  constant 1 on loglog n → sieve/parity issues. Not yet in Lean.
  Own analysis (iter 3): write b = n−a. gcd(n−b, n−b') | (b−b'), so CRT constructions
  (n ≡ c_q mod small q) reduce to: S ⊆ [1,k] missing one residue class mod each prime q<k;
  best Σ1/b ≈ loglog k while n ≳ e^k, so constructions only give ~logloglog-scale vs loglog n
  → no easy counterexample. Upper bound via dyadic blocks (π(2B) small-factor elements +
  Brun–Titchmarsh count of rough ones) gives O(loglog n) but constant ≈ 2/log 2-ish, not 1.
  Getting constant 1 looks like genuine sieve work → probably NOT an ASAP target.
- 1209 — mostly resolved (counterexamples); only residual variants left. Low priority.

## Triage batch 1052–1088 (agent, iter 4) — nothing quick
- Region heavily worked by AI-assisted groups in 2026: 8/25 have proof claims.
- Proof claims / solved-ish: 1054 (Principia Math, Lean, Jul 2026), 1059 (J. Land, Sep 2026),
  1061 (E. Li, arXiv Li26), 1070 pt2 (Dúcz–Varga 2026), 1075 (Q. Gu disproof claim Sep 2026),
  1083 d=3 (Tidor–Yu–Zakharov Aug 2026).
- 1087 (0 votes/claims): reduction f(n) = Θ(n·I(n)) + O(n³ log n) where I(n) = max #isosceles
  triangles ⇒ f(n) ≪ n^{3.137} via Pach–Tardos, and #1087 ⇔ Erdős–Purdy isosceles question.
  Nice forum contribution, NOT a resolution (needs Guth–Katz; not in Mathlib).
- 1088, 1084: only partial/estimate improvements. Rest deep.

## Triage batch 1093–1139 (agent, iter 7) — nothing quick
- Claimed/resolved in 2026: 1112 (J. Land sorry-free Lean, Bloom confirmed 13 Jul), 1117 (Gu,
  GPT-6 Astra, 5 Sep), 1122 (Gu, 8 Sep), 1133 (Chojecki/Yang), 1139 (GPT Pro, Jun), 1120 (→∞
  proved, arXiv 2606.19178), 1101 Q2 (lipet2k, Apr).
- 1110 weak candidate: density of representable ints for (p,q)=(5,2),(7,2),(9,2),(5,3) open.
  Antichain-count exponent c>1 in those cases (1.263/1.127/1.045/1.034) so counting can't give
  density 0. Bitset computation to 1.024e6: (5,2) fraction 0.79 rising; (7,2) ~0.22 flat;
  (9,2) 0.11 falling; (5,3) 0.087 falling. Research-level. Scripts: scratchpad/e1110/.
- 1100, 1101 Q1: hard growth questions. Rest deep (Collatz, Brocard-type, χ-boundedness...).

## Triage batch 1142–1188 (agent, iter 7) — nothing quick
- KEY RESOURCE: Tao's wiki github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdős-problems
  lists AI full/partial solutions per problem — check it for every candidate (site status lags!).
- 1151: site says OPEN but effectively SOLVED (Chojecki + GPT-5.5 Pro, 30 Apr 2026, checked by
  N. Sothanaphan; wiki "Full solution"). Partial Lean by AllenGrahamHart (Thm 1.1(a)); part (b)
  needs Erdős 1941 divergence. Formalization-only opportunity, NOT an open problem.
- 1183 (Erdős–Ulam union-closed): upper half done (subexponential, Mar 2026); lower bound
  F(n) ≥ n^{ω(n)} open — tried grid/chain constructions, only polylog/O(m). Hard.
- 1145 (Erdős–Sárközy a_n/b_n→1 bases): digit tilings can't give ratio→1; no counterexample.
- 1188: estimate question. Rest deep (BES conjecture, box problem, ultraflat polys...).

## Triage 950–1049 (agent, iter 8) — nothing quick
- 968 secondary Q (u_n=p_n/n monotone triples infinitely often): answered YES by known results
  (Maier 1981 chains of large gaps; Maynard/GPY small gaps) — literature note, main Q open.
  Lean would need Maier/Maynard as axioms → not axiom-clean.
- 985 (prime primitive root < p): GRH-level. 963: essentially solved (1−o(1))log2 n.

## Site-wide scrape (agent): scratchpad/all.tsv + probs/<N>.html (all 1225 pages)
- Format: (num, votes, voters, ?, STATUS, (comments, proof_claims)).
- 590 OPEN; 461 open w/ 0 claims; 176 open w/ 0 claims & ≤1 comment → scratchpad/lowattn.txt.
- Top tractable-voted: 689(5,claimed) 1038(5,3 claims) 1139 142 1210(3, no claim) 521 848.

## #197 (partition N into 2 sets each permutable w/o monotone 3-AP) — iter 8
- OPEN (checked 2026-09-22): 0 claims, 1 comment (wkasel 26 Aug 2026: SAT-assisted partial
  result, dyadic-blocks partition can't work; github.com/Wkasel/erdos197). Formal stmt exists.
- Literature: Geneson arXiv 1803.06334; LeSaulnier–Vijay 2011: α(3) ≥ 1/2, β(3) ≥ 1/4
  (upper/lower density sup of permutable sets), conjectured tight → would give NO since need
  α+β ≥ 1. No nontrivial upper bounds known.
- Own: first element a forces chain a+2^k(b−a) to exit A (infinite descent) — only a
  density-0 obstruction. Research-level. Dropped as ASAP target.

## Tried / dropped
- 19, 475, 506, 551: decidable-but-infeasible finite checks.
- 1218, 1220: large-cardinal set theory, not Mathlib-friendly.
- 1221: asymptotic analysis on circle, no obvious handle.

## Next step
- Parallel triage of open problems 1050–1221 for tractability + open-status evidence.

## Short-formal-statement older problems (iter 6, own check) — all dropped
826, 943, 849, 383, 431, 396, 371, 479: short Lean statements but famous analytic-NT
questions (divisor tails, powerful-number reps, binomial multiplicities, prime tuples,
2^n ≡ k mod n). Short statement ≠ tractable. No quick handle.

## Prize problems (user request, 2026-09-22)
- Prizes now paid by the Combinatorics Foundation (Steve Butler). Require publication in a
  reputable peer-reviewed journal + documentation that Erdős offered the amount. (erdosproblems.com/faq)
- #468 has NO prize.
- Open prize problems, smallest first (from all.tsv + problems.yaml): 470 $10 (odd weird),
  1052 $10 (unitary perfect), 634 $25 (2 claims), 661 $50, then $100: 78 86 99 101 104 120
  132(“any nontrivial result”, 1 claim) 241 588 708(1 claim) 1029; $250: 50 52 77 165 595 671...
- Agent triaging 132, 634, 708, 104, 661, 99, 101, 588, 470, 86, 241, 120.

## Submission requirements (checked 2026-09-22)
erdosproblems.com forum rules:
- AI assistance allowed but MUST be disclosed.
- Poster must understand/verify the math themselves, OR provide a sorry-free, bug-free Lean formalisation.
- Long proofs → external PDF (not inline). Short proofs must be detailed; harder problem = higher bar.
- Status updates: comment under the problem, or email Bloom (site owner). Needs a forum account.
- Prizes (not applicable to 468): journal publication + proof of Erdős's offer; Combinatorics
  Foundation / Steve Butler.
Plan for 468: (1) finish sorry-free Lean (sum_T_le pending), public repo with E468.lean;
(2) PDF/markdown write-up (WRITEUP_468.md) incl. all-N via Romanov (agent working);
(3) user posts a proof claim on forum/thread/468 with AI disclosure + links;
(4) optionally comment on formal-conjectures PR #4076 offering the disproof; optional arXiv note.
