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
- 885 k=5: parked 2026-09-23, UN-PARKED 2026-09-25 (user) → see problems/885/README.md.

## Iteration 8 (2026-09-23)
- Agents running: 132 novelty audit (A2, B2), 132 A2 write-up, 132 convex n=7 (angle_B3),
  triage 700–949, triage 400–699. Loop paused until they report (hook pause file).
- Own: C1 greedy evidence (problems/132/angle_C.md): max μ(Δ₂)−n = +1 up to n=21.

## Iteration 8 results (2026-09-23)
- 132: 54/37 audited NEW + rigorous write-up (~90%); convex n=11,13 k≥3 certified (drat-trim+lrat); convex
  n≤8 k≥3 follows from Erdős–Fishburn 1995 (user-supplied PDFs); C1 greedy evidence.
- 436: Λ(5,3) finiteness unresolved; new lower bound Λ(5,3) ≥ 5,062,794 (needs novelty check + Chebotarev
  direction written up); brute-force certificate ~1e18 nodes → needs structural idea.
- Triage 400–699 (→436) and 700–949 (→885 k=5, competitor active) found nothing quick.

## Iteration 9 (2026-09-23)
- Agents: novelty audit (convex n=11/13 → 132 NOVELTY Audit 4; Λ(5,3) → problems/436/NOVELTY.md),
  second independent referee of WRITEUP_A2 (→ REFEREE2_A2.md), Lean scoping of convex n=7/11
  (→ Erdos/Erdos/E132Convex.lean, problems/132/lean/README.md). Loop paused while they run.

## Iteration 9 results so far
- 54/37: second independent referee CORRECT (REFEREE2_A2.md). Only the original Ve87 paper remains unread.
- Audit 4: convex n=11,13 k≥3 NEW (the Marchetto/Rafik/Beller forum claims are ≥2 rare distances for general sets,
  so they don't cover this). Q-ORD method: prior art Morić–Pritchard arXiv:1103.0412 (abstract convex polygons
  + quadrilateral inequality), which must be cited. Related: lyfar/rare-distance-fields (GitHub).
- 436: Λ(5,3) ≥ 5,062,794 NEW (no table for k≥5, l=3). The reduction is KNOWN (Lehmer–Lehmer–Mills case vectors;
  Brillhart–Lehmer–Lehmer 1964). Unread: Lehmer "Mechanized mathematics" (BAMS 1966), Lehmer–Lehmer
  "On runs of residues" (Proc AMS 1962), Mills' 1965 survey.

## Research round R1–R5 (2026-09-23/24): beyond Clemen–Dumitrescu–Liu
- R1 (angle_R1.md, a0a2fdf): convex ⇒ ≥3 rare distances for every 6 ≤ n ≤ 18 (n = 15, 17 SAT-certified by
  drat-trim). Odd n ≥ 19 is open: B1b closed; A1/B2 are conditional on Fishburn L6 / Thm 2 / the E–F conjecture;
  A2, B1a and B2 (3 ≤ a ≤ m) remain open.
- R2 (angle_R2.md, 2f1f194): Conjecture C1 is FALSE. There are convex no-4-concyclic sets with μ(Δ₂) = 5n/4 (proof needs a
  referee). Local lemmas P0–P6 are proved. New question: μ(Δ₂) ≤ 5n/4 + O(1)? The paper is corrected (70fe7e8).
- R3 (angle_R3.md, ce1b53b): Hit Lemma (≤ 21–23 chord hits, via Beukers–Smyth). Theorem AC: an almost-cocircular
  convex set has k ≥ (n−3w+1)/4. The general case reduces to Erdős–Fishburn's f(n), plus stability off a circle.
- R4 (angle_R4.md, c2f61e8): **L ≤ 15/11** for CDL Problem 1.6, down from 54/37 (18/13 refereed twice, the N1 lemma refereed
  once). Region II alone gives 4/3. Theorem G would give 9/7 conditionally (it needs a gap lemma).
- R5 (angle_R5.md, fecabb2): the #132(a) case map. "Δ₂ or Δ₃ is rare" is false (exact n = 8; odd rings → 6/5). Conjecture
  R5.4: min(μ₂, μ₃, μ₄) ≤ n. Charge Lemma conjectured (0 violations in ~205k sets).
- The paper and Lean proof still state 54/37. The upgrade to 15/11 awaits the user's decision.

## ★ R6 result (2026-09-24): L ≤ 4/3 (refereed twice); 9/7 for τ > 1 (matches the global lower bound; not "sharp" — the 9/7 constructions have t < 1)
- Theorem N3: average weight (deg y + m_y) ≤ 8 ⇒ L ≤ 4/3 for all τ (refereed; six wording fixes applied).
- 21/16 in Region I and for τ > 1 (refereed). Theorem E′ (global shell/Euler) ⇒ 9n/7 + O(n^{2/3}) for τ > 1, matching
  the global lower bound (refereed twice; the full corrected proof of E′ still needs to be written — REF2 G1–G6). Commits 9508181 and 8ed366d; see problems/132/angle_R6.md.
- Unrefereed: Region II e(S) ≤ s + ½|Q′| + C; Region III outside the window. Conjectured: 9/7 in Region I (average ≤ 6).
- Correction to R4: the deg+m = 10 fan does not occur throughout Region I (pinning ⇒ t ≈ √3/2).

## ★ Lean milestone 3 (2026-09-24): 15/11 fully formalised
- Erdos132Main.erdos132_main15: min{μ(Δ₂),μ(δ)} ≤ 15/11·n + C₀, sorry-free, axioms = propext, Classical.choice,
  Quot.sound; leanchecker passes on all 6 E132Main15* modules (5,251 lines, 141 theorems; commit 1619776).
  N2 (4/3 in Region II) is not formalised. The blog (post 15/11) and the public repo get updated once the Lean files are pushed.
- The 9/7 research (R6) continues: 21/16 in Region I (unrefereed); Theorem E + Lemma F nearly give 9/7 for τ > 1
  (the general-fat-K step is sketched); a pair-gap obstruction and Theorem 2L conditional on H1.

## ★ Lean milestone 2 (2026-09-23): #132 54/37 bound fully formalised
- Erdos132Main.erdos132_main (CDL Problem 1.6: min{μ(Δ₂),μ(δ)} ≤ 54/37·n + C₀) sorry-free, axioms = propext,
  Classical.choice, Quot.sound. Also Vesztergombi 1987, Hopf–Pannwitz, Cor A1 (E132Layer). Full lake build OK.
- This is a Lean-verified NEW partial result on open problem #132 (improves the 3/2 upper bound in CDL's Problem 1.6).
  It does NOT resolve #132, so ERDOS_DONE is not met.

## Lean milestone (2026-09-23)
- #132 convex n=7, n=11 (≥3 rare distances) proved in Lean without sorry: Erdos/Erdos/E132Convex.lean. Axioms:
  propext, Classical.choice, Quot.sound + bv_decide certificate axiom (disclose, like native_decide). This is a
  partial result on an open problem, not a resolution, so it does NOT meet the ERDOS_DONE criterion.

## Next step
- 132: novelty audit of convex n=11/13 result; independent read of WRITEUP_A2 §7.2 and §8 Step 4;
  scope a Lean formalisation of convex n=11 (quadrilateral lemma + verified encoder + LRAT).
- 436: novelty check of Λ(5,3) ≥ 5,062,794 (Lehmer–Mills-type tables); structural lemmas on small primes.
- (old) Parallel triage of open problems 1050–1221 for tractability + open-status evidence.

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
Prize triage result (agent, 2026-09-22): nothing quick.
- #132 ($100 "any nontrivial result"): claims for small n (Beller n=8 Lean conditional; Marche 7–13;
  Chojecki n=8 flawed); ienjoymath lower bound (9/7)n for CDL Problem 1.6 (upper 3/2). Realistic
  line: stability version of Altman/Fishburn for convex position. Unproved.
- #634 ($25): n=19 claimed impossible by George (Jul 2026) and Harries (Jul 2026), unaccepted;
  full "find all N" far off. Beeson arXiv 2607.19572.
- #708 ($100): Chen claim O(n log log n) unaccepted; prize needs (2+o(1))n.
- 104, 661, 99, 101, 588, 470, 86, 241, 120: deep.

## Layout (from 2026-09-22): one folder per attempted problem
problems/<N>/README.md = status, prior work, results, files, next steps. All assets live there.
- problems/468 — DONE (almost-all: Lean sorry-free; literal: Lean conditional on Romanov density).
- problems/132 — IN PROGRESS (iter 8: novelty audit A2/B2, A2 write-up, convex n=7 agents running).

## ⚠ 2026-09-22: #468 result is NOT NEW
Tao proved the δ² density bound on 2025-11-01 (comment moved from #468 to #1054 thread); #1054
is the same f shifted by one. Later improvements (Kovač, Price), every n≥6 representable (jif),
limsup=∞ fully Lean-formalised (Principia Math, Jul 2026). Our first triage agent even noted
"1054: Tao handled the density part" but I failed to connect 1054 ↔ 468. Lesson baked into
PROMPT.md rule 4: check all cross-referenced/sibling problems and their threads.

## Triage batch 400–699 (agent, iter 8) — one real candidate (#436), not quick
- 146/300 have status open (problems.yaml 2026-09-22); pages fetched 2026-09-23 → scratchpad/e400/
  (open.txt, summary.tsv = num/status/comments/claims/statement, p/<N>.html, f/<N>.html threads).
- Heavily worked / not new: 404 (KitaKen1 Jul 2026: f(2,2)=254 exact + Lean, f(a,2) a≤256 table;
  Tao lemma), 677 (Aristotle formalisations, qrdl/Sothanaphan Mar 2026), 614 (Tang–Ma Jan 2026:
  finite-family Turán reformulation), 668 (2nd Q false at n=4; AMP25 tables n≤21), 644 (known r≤6).
- 430 ≡ first part of 385 (Adenwalla) — open, prime-gap flavour. 662: statement garbled per site.
- Rest deep (Ramsey/Turán asymptotics, analytic NT, set theory, random polys, distances).
- ★ #436 (Lehmer–Lehmer consecutive k-th power residues) — OPEN sub-question explicitly on page:
  "is Λ(k,3) finite for odd k≥5?" (Λ(k,2) finite: Hildebrand 1991; Λ(3,3)=23532 LLMS 1962;
  even k: Λ(k,3)=∞; Λ(k,l)=∞ for l≥4). Smallest open case Λ(5,3).
  Openness (checked 2026-09-23): erdosproblems.com/436 OPEN, 3 comments (Adenwalla/Bloom Oct 2025,
  refs only), 0 claims, no see-also; formal-conjectures: no 436 file/PR (grep + gh pr search);
  not on Tao's AI-contributions wiki (wiki clone grep); OEIS A000445 (Λ(k,2) only; Reble a(8) bounds;
  last hist edit Oct 2025); arXiv/web: only Dietzel 1309.7506, 1810.01518 (pairs/IP-sets) — nothing on triples.
  Reformulation: Λ(5,3) = max over completely additive f: N→Z/5 of first r with f(r)=f(r+1)=f(r+2)=0
  (⇔ every index-5 subgroup of Q+ contains 3 consecutive ints). Since χ(−1)=1 for odd order,
  character-mod-M constructions fail (±1 both in kernel ⇒ triple around multiples of M) → finiteness plausible.
  Lean fit: UPPER bound Λ(5,3) ≤ R (⇒ "finite", answers the Q for k=5) is purely elementary:
  kth-power char on (Z/p)^* + finite certificate over primes ≤ R+2. Exact value needs Chebotarev
  (lower bound) — not needed for "finite".
  Tried: naive DFS scratchpad/e400/l53/dfs.c reproduces Λ(2,2)=9, Λ(3,2)=77 but blows up already
  on Λ(4,2), Λ(3,3) (2e8 nodes, depth ~190). Needs CDCL/SAT (one-hot F5 vars per prime, triple
  clauses; no SAT solver installed — pip/brew needs user OK) or lazy domain-propagation (primes
  >R/2 never forced). Risk: Λ(5,3) may be ∞ or ≫1e7 (Λ(7,2)=1.6e6). Verdict: best 400–699 lead,
  a genuine computation project, NOT quick; certificate size for Lean (decide) may be the bottleneck.

## Triage batch 700–949 (agent, iter 8) — nothing quick; best finite lead #885 k=5
- problems.yaml (clone 2026-09-23): 118/250 status open. Pages + forum threads fetched 2026-09-23
  → scratchpad/probs/<N>.html, thr/<N>.html; summary.txt (num, comments, claims, statement).
  Only 25 open w/ 0 claims & ≤1 comment, all famous/deep (712 714 724 738 761 766 782 802 805
  809 812 813 830 837 840 849 857 859 893 901 919 929 930 938 706).
- Region is HEAVILY worked in 2026 (KitaKen1 Lean PRs, GPT-5.x/6 claims, SAT exact values):
  944 k=4,r=1 Dirac case Lean-claimed (Kitamura, FC PR #5467, 10 Sep 2026); 768 claimed resolved
  (arXiv 2606.24872 + Aristotle Lean); 731 (Li26 claim); 776 n0(r)~2r (He–Tang, Bloom minded to
  mark solved; n0(11)=27 Thiim); 836 Q2 (GPT-5.5 Pro, Price Apr 2026); 873 neg. answer Lean (Sep);
  878, 879, 889 (V-variant) Lean claims Sep 2026; 872 game near-resolution; 906, 749(upper) done.
- Small-exact-value threads already occupied: 827 n4=7 (sallerk, 22 Sep 2026; n5 in [9,37]),
  831 small h(n), 857 M(n,3) Lean-certified small values, 817 g3(7)≤474 (23 Sep), 902 f(1),f(2)
  Lean (f(3)=19 known; f(4) open but big tournament SAT), 719 (3,6) exhaustively OK (Feb 2026).
- ★ #885 (factor-difference sets, D(n)={|a−b|: n=ab}; ∀k ∃N1<…<Nk with |∩D(Ni)|≥k?) — OPEN.
  Known k≤4 (ErRo97, Ji99, Bremner IJNT 2019). Finite, Lean-decidable witness for k=5 would be a
  genuinely new case (NOT a full resolution). Reformulation: d∈D(N) ⇔ 4N+d² square ⇔ a (k+1)×k
  sumset-of-squares {u_i+v_j} with u_0=0; k=5 needs (6,5); Choudhry arXiv 2508.07806 (Aug 2025)
  only has (3,3),(5,3),(4,4) families.
  Openness (checked 2026-09-23): erdosproblems.com/885 OPEN, 0 claims, 3 comments: sammausberg
  19 Apr 2026 (3-way intersection {36,468,692,1028}, Lean via Aristotle); **Aleksanndr_NFA
  23 Sep 2026 04:05 (TODAY)**: elliptic-curve search d_j≤40, many k=4, NO k=5; k=4 Lean in FC PR
  #6509. No see-also links. formal-conjectures 885.lean (main @ 2026-09-23): main thm `research
  open`, variants k=2,3,4 solved (k=4 = Bremner {65984625,508032000,1578963456,2505664000},
  d={5040,27720,68880,164976}). Not on Tao's AI wiki. Web: JSP awards PR #297 (Lean k=2,3); no k=5.
  Own search (scratchpad/e885/s885.c, s885l.c): pivot N1, columns D(N1), rows N=b(b+d), b≤B,
  128-bit masks. Validated (recovers both k=4 examples). N1≤2e6 with |D|≥10, B=2e4 (rows ≤~4e10):
  15 k=4 configs, 0 k=5. 1600 smooth N1∈[5e7,1.4e9] with τ≥640, 128 smallest d, B=2e4: 0 k=5.
  Verdict: live competition (someone searching today), and the full ∀k question needs Bombieri–Lang-
  type ideas (probably false/unknowable). Worth it only as a "k=5 witness" side result; better tool
  = rational points on the genus-1 quartics (needs PARI/gp: not installed).
- Drops (one line): 700/726/727/731/768/770/820/821/824/826/828/829/830/849/850/852–855/859/886–
  893/912/913/928–933/935–943/945 analytic/multiplicative NT, conjecture-level (Dickson/abc/prime
  gaps/Singmaster); 704/706/712–714/724/725/738/740/761/766/802/805/809–813/836–838/857/901/911/
  917/918/919/934/944 extremal graph/hypergraph asymptotics or set theory; 708–711/860 covering-
  interval asymptotics (claims exist); 749/757/773/774/786–792/796/817/819/839/840/856/864/866/
  870/873/875/876/881/883/949 additive-comb. asymptotics, most with 2026 AI/partial work;
  734 PBD construction for all n (Erdős: "probably not very difficult") — no finite core, open
  but not quick; 719 Erdős–Sauer needs Turán K4^3 values; 778 game for all n; 782 squares.

## #436 PARKED (2026-09-23, user's call; recorded from the #436 session)
- Best bound: **Λ(5,3) ≥ 2,000,028,671**, from a warm-start local search plus a small-prime smooth fix. The witness is in
  problems/436/logs/warmstart/ and was verified by 4 independent checkers (commits ee53d03..ba31de7).
- It is not a resolution. The site says the problem "cannot be resolved with a finite computation". The witness analysis shows
  f ≈ Ω(n) mod 5 (Liouville-like), so if Λ(5,3) is finite it is likely astronomically large. Finiteness reduces to
  3-point log-Elliott correlations with exponent sum ≡ 0 mod 5 (problems/436/THEORY.md).
- F_100(∞) is SAT: the Luca–Najman triple bound is 407,498,958, plus the erratum's extra triple 43,184,400.
- There is no prize. Effort moves to #132 (the $100 prize for "any nontrivial result"). Full details: problems/436/README.md.
- The earlier lines above quoting Λ(5,3) ≥ 5,062,794 are superseded.

## #436 SAT attack (agent, 2026-09-23) — see problems/436/README.md
- Reduction pinned: Λ(k,l) ≤ Λ_comb(k,l) := max over completely additive f: N→Z/k of first zero
  l-run (elementary: k-th power character mod p, all p); equality for odd k via Kummer/Chebotarev.
  Λ_comb ≤ R ⇔ finite CNF S(R) UNSAT.
- Validation: SAT search reproduces Λ(2..5,2) = 9, 77, 1224, 7888 and Λ(3,3) = 23532 (kissat 2 s,
  DRAT checked by drat-trim).
- k=5: full S(R) SAT up to R = 5,062,500 ⇒ **Λ(5,3) ≥ 5,062,794** (new lower bound); R = 7.59e6
  kissat > 80 min (still running). Models: f(2)=0, f(3)=1, f=0 on most small primes.
- Weakening F_y(X) (primes ≤ y, runs of y-smooth numbers; sound for UNSAT): k=3 refuted at y=300
  (31k-node DFS); k=5 SAT up to y=500 (X=1e9); y=1000 open. Knuth estimate of the refutation tree
  ≈ 1e18 nodes for k=5 (vs 3e4 for k=3): ~1e14 surviving assignments of primes ≤ 100 alone.
- Verdict: brute-force finiteness certificate for Λ(5,3) infeasible; would need a structural idea.
  Openness rechecked 2026-09-23 (site, thread, fc issue #731 open/no file, Tao wiki, arXiv): open.

## Triage batch 1–399 (agent, iter 9) — nothing quick; best lead #261(iii) (research-level)
- problems.yaml (clone 2026-09-22): 187 status open + falsifiable 23/64/97/107/114/128/167/242/287/375/
  398, verifiable 7/307/364/366, open(Lean) 390, decidable 19. Pages + threads fetched 2026-09-23 →
  scratchpad/e001/ (p/<N>.html, f/<N>.html, summary.tsv = num/comments/claims/tractable/edited/stmt).
- Region is the most famous + most worked: nearly every open item is a named conjecture (Sidon/B_h
  asymptotics, Ramsey/Turán, prime gaps, irrationality, distinct distances, Erdős–Gyárfás 64, Grimm 375,
  Erdős–Straus 242, powerful triples 364/366 = abc-level). 0-comment threads (39 40 41 50 60 62 70 84
  87 89 99 101–103 111 112 131 159 172 177 187 195 200 201 212 222 247 295 319 340) all deep.
- Occupied / done-ish: 117 (Lecomte claims h(n)^{1/n}→√2, Zenodo, Aug 2026); 389 (Kitamura/Jack
  exact k(n) n≤29, Sep 2026); 393 (Turturean abc-conditional); 348 (m,n)=(2,3) actively searched
  (SSD117/Sprite144/Woett); 341 ({1,4,9,16,25} period 224, Kitamura Jul 2026 — general Q open);
  156 (cyclic data, veljjanoski Sep 2026); 160 (ruizshi N^{1/4} via arXiv 2607.20752); 272 (Szabo
  conj., StijnC data N≤14); 273 (ideal_ombrer: needs p>877, Jul 2026); 302/361/357 bound-tweaking
  threads; 354 Q2 Lean (Kitamura, Sep 2026); 260 claimed (Wang–Grau Ribas + Lean, Jul 2026, disputed).
  112 k(n,m): k(2,m) = tournament TT_m Ramsey no. (m=7 open) → "determine" hopeless.
- ★ #261(iii): is there rational x with ≥2^ℵ0 representations x=Σ_{a∈A} a/2^a (A infinite)?
  Openness (checked 2026-09-23): site OPEN, last edited 1 Dec 2025, 0 proof claims; thread: Kovač
  12 Aug 2025 "both questions still open", Rafik 27 Apr 2026 (two reps of 7/4 — trivial weak version),
  Kovač 5 May 2026 ("2" believed misprint for 2^ℵ0); formal-conjectures 261.lean (main @ 2026-09-23):
  parts.iii + two_representations tagged `research open`; not on Tao's AI wiki (frozen 30 Jun 2026);
  see-also only #260 (checked thread); no OEIS link. BoLo90 abstract: "some numbers have a unique
  representation, others have uncountably many" (not rationals); TUZ20 (arXiv 2008.01501) is about the
  FINITE equation n/2^n=Σ_{i≤k}a_i/2^{a_i} (≥5 solutions for k in an infinite set) — it does NOT count
  infinite reps of rationals (earlier note '≥3 reps, ≥9' was WRONG; corrected on blog 2026-09-25).
  Own reduction (scratchpad/e001/e261/): s_a := 2^a·(remaining target before a) must stay in
  [0,2a+2]; include a iff s≥a, exclude iff s≤a+2 ⇒ choice ONLY in window s∈[a,a+2]; map commutes
  with s↦2a+2−s. BL identity n/2^n=Σ_{n<k≤n+m}k/2^k (n=2^{m+1}−m−2) = a diamond at ANY window
  offset. For dyadic x: canonical e_{L+1}=min(2e_L, L+2−2e_L); #infinite non-cofinite reps =
  2^{#{L: e_L=1}} ⇒ x has continuum reps ⇔ this integer orbit returns to 1 infinitely often.
  x=1: returns at L=2,4,80,236,432,1504,2944,6060,6620,18912,54224,302467996,1772665632,
  2148845168,5145362668 (none more to 2e10); orbits from many starts merge into this trunk.
  Non-dyadic x (1/3,1/5,3/7,5/7): ≤10 live states, branches ~ c·log a, paths grow — heuristically
  YES (hit rate ~1/a, Σ diverges) but a proof = controlling a non-autonomous tent-map orbit. Any
  rational-x construction must fight rationality ⇒ gaps ≤ log₂a+O(1) (260 claim) vs gadget runs ≈ log₂a.
  Lean fit would be excellent (FC statement exists; certificate = infinite family), but no proof idea.
  Verdict: genuinely open + elementary, NOT quick. Record reformulation; revisit only with a new idea.
  Re-check 2026-09-24: exact DP over all partial reps of x=1 to a=1600 → live-branch count doubles at
  exactly a=2,4,80,236,432,1504 (matches orbit); orbit returns to 2e10 reproduced (identical list).
  Reduction itself still only a sketch (no rigorous proof that live branches never die).
  Blog post published 2026-09-24 by user: g8r-b8.github.io/erdos-lab/2026/09/erdos-261-iii-integer-orbit/
  2026-09-25: reduction PROVED (elementary). u_a=min(s,2a+2−s), v_a=a+1−u_a ⇒ every live branch follows
  v_{a+1}=|a−2v_a|; v=0 (centre) splits into 2 mirror live branches; u=a spawns only a finite/cofinite
  branch; u≥1 ⇒ u'≥2 so no live branch dies ⇒ #inf non-cofinite reps = 2^{#{a: v_a=0}}. x=1: v_1=0,
  zeros at a=L−1 (to 2e10). Old e_L = min(v_{L−1}+1, L−v_{L−1}) (proved by case t=a−2v ≥/< 0).
  General dyadic m/2^k: several orbits (one per integer state at a=k). Post updated (dated) in blog
  repo, pushed 2026-09-25 (7862f15). Open problem itself: still need ∞ zeros of v.
  2026-09-25: v-search to 1e12 → two more zeros a=129465909327, 212089391807 (L=a+1) ⇒ 1 has ≥2^17
  inf non-cofinite reps. Mirror branches take opposite choices at EVERY later a (reps differ infinitely
  often; cf. Rafik's cofinite 7/4 pair). FC file also has variants.two_representations tagged `research
  open` (≥2 infinite reps of some rational) — literally answered by Rafik's cofinite 7/4 pair (forum,
  27 Apr 2026); a Lean proof of that variant for x=1 via our orbit (a=1 split) is a possible small FC PR.
  Blog post corrected + updated (daa99d8).
- Drops (one line): 3/5/9/10/11/14/15/17/18/20/25/28/30/32/33/36/39–41/44/50–52/60–62/65/66/68/
  70/75/77/78/80–82/84–87/89/91/96–104/107/108/111/114/120/122/124/128–131/137/138/141–143/145/148/
  149/151/153/155/158/159/161/162/165/167–170/172–174/176/177/181/184/187/188/195–197/200/201/203/
  208/212/213/217/218/222/233/234/236/238/241–244/247/249/251/252/254/256/257/263–265/267/269/271/
  274/276/278/279/282/287–289/291/293/295/301/304/306/307/311–313/317/319/322–327/329/332/334–336/
  338/340/342/345/349/352/359/364–368/371/373–377/382/383/385/386/388/390/394/396/398: deep
  (asymptotic/conjecture-level), heavily worked in 2026, or need abc/Chebotarev-type input.
