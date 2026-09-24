# Erdős #132, angle R2: Conjecture C1 (general position ⇒ μ(Δ₂) ≤ n + O(1)) — REFUTED

Date: 2026-09-23. Coordinator plus three sub-agents: local structure, convex case, and construction search.
Scripts: `scripts/r2_*.py`. Run them with `.venv/bin/python`, which has mpmath, sympy and pysat.

## Verdict

**Conjecture C1 is FALSE, in both its weak and its strong form, even for convex sets.**

Two independent families, both with no four points concyclic (NFC):
- a convex family, proved for every n ≡ 0 (mod 4), n ≥ 12, with μ(Δ₂) = 5n/4;
- a non-convex family with m₃ = 0 and μ(Δ₂) = 5n/4 − 3/2, certified numerically up to n = 62.

In both, the number t of degree-3 hull vertices in the 2-core G′ is linear in n.

Positive results:
- exact local lemmas P0–P6 for degree-3 hull vertices under NFC (§2);
- a computer-assisted matching upper bound 5n/4 + C in convex position (§4; its SAT encoding has not been audited).

So the NFC route to #132(a) through Δ₂ is closed. Under NFC, the right constant for μ(Δ₂)/n lies in [5/4, 3/2], and it is 5/4 for convex sets.

## 0. What was needed for #132(a)

- (a) needs a second rare distance besides the diameter Δ, and μ(Δ₂) ≤ n suffices.
- A bound μ(Δ₂) ≤ n + O(1) does not give (a) by itself. Only the strong form would feed into Theorem A (angle_C):
  μ(Δ₂) ≤ |V(G)| + t/2 ≤ n − m₃ + t/2,
  where m₃ is the number of points of depth ≥ 3. Under NFC, every point has at most 3 Δ₂-neighbours, so deg_{G′} ≤ 3.
- So the strong form (t ≤ c) would have given (a) for NFC sets with m₃ ≥ c/2.
- The families below have t ≍ n. In the non-convex family m₃ = 0, so they refute exactly that hope.

## 1. Counterexamples to C1

### 1a. Convex family (convex sub-agent; independently re-verified)

Let n = 4m, k = n/2, θ = 2π/n.

**Symmetric seed.**
- Even points: a_{2y} = ½·e(2yθ).
- Odd points: a_{2y+1} = R₂·e((2y+1)θ), where R₂² + R₂ cos θ = 3/4.

**Prescribed equalities.**
- Δ₂ = 1 on the n pairs a_x a_{x+k±1}, and on the n/4 antipodal even pairs a_{2y} a_{2y+k}.
- Δ = 2R₂ > 1 on the n/4 antipodal odd pairs.

**Counts.** μ(Δ₂) = 5n/4 and μ(Δ) = n/4.
- Every even point has Δ₂-degree 3.
- Each even point and its antipode are each other's middle neighbour ("3↔3 pairs").
- So t = n/2.

**Why Lemma T is avoided.** The Δ-edges join odd points only, and there are no odd–odd Δ₂-edges. So no alternating 4-cycle exists.

**Removing concyclicity.**
- The seed is concyclic.
- The Jacobian of the 3n/2 equations has full rank there, so the solution set is a manifold of dimension n/2 + 1 (before quotienting by isometries).
- A random point on it near the seed has no 4 concyclic points.

**Certification.**
- The sub-agent certified n = 12, 16, 20, 24, 32, 40 with a Krawczyk interval-Newton box of radius 1e-40 at 60 digits. On that box it did interval checks of: all equalities; D > 1; every other distance < 1; strict convexity; all C(n,4) concyclicity determinants ≠ 0.
- **Independent re-check** (`r2_verify.py`: own hull code, own concyclicity determinant, 50 digits) on n = 12, 20, 40:

| n | μ(Δ₂) | μ(Δ) | t | μ(Δ₂) − n | max eq. error | gap 1 − max(other) | min normalised concyclic det |
|---|---|---|---|---|---|---|---|
| 12 | 15 | 3 | 6 | 3 | 5e-51 | 0.109 | 1.0e-7 |
| 20 | 25 | 5 | 10 | 5 | 5e-51 | 0.032 | 2.0e-6 |
| 40 | 50 | 10 | 20 | 10 | 5e-51 | 0.0082 | 1.8e-8 |

All points are hull vertices. The minimum |orientation| is ≥ 3e-4, so no 3 points are collinear either.

**Theorem R2.1 (proved for every m ≥ 3; convex sub-agent; I re-checked only parts).** For every n = 4m ≥ 12 there is a strictly convex n-set with no 4 concyclic points, μ(Δ₂) = 5n/4 and μ(Δ) = n/4.

The proof has three parts.

*(i) Seed inequalities (by hand).*
- Write R = ½ + u. Then u = (1−c)/(2(1+c+u)) with c = cos θ, so 0 < u < tan²(θ/2)/2.
- R < 1/(2cos θ), because f(R) = R² + R cos θ is increasing and f(1/(2cos θ)) > 3/4.
- Hence D = 2R > 1.
- Even–even non-antipodal distances are sin(dθ) < 1.
- The largest odd–odd non-antipodal distance is 2R cos θ < 1.
- Even–odd squared distances are ¼ + R² + R cos φ, with φ ∈ {θ, 3θ, …}. This equals 1 exactly at φ = θ (the edges) and is < 1 for φ ≥ 3θ.
- Strict convexity follows from ½ > R cos θ and R > ½cos θ.

*(ii) Full rank 3n/2 at the seed.*
- Self-stresses split into Fourier modes under the rotation by 2θ.
- The block determinants are:
  - −4R² sin²θ(ω−1) for ω^m = 1, ω ≠ 1;
  - a 3×3 minor −i(4R sin θ + sin 2θ)/2 for ω = 1;
  - 2iR sin θ(1 + 2R cos θ) for ω^m = −1.
- All are nonzero (`r2_convex_jac_fourier.py`).
- The kernel consists of the global rotation plus "pair translations": v(a_y) = v(a_{y+k}) = V_y, with V_{y+1} − V_y ∥ (a_y + a_{y+1})^⊥.
- So the solution set M is a real-analytic manifold germ at the seed.

*(iii) No concyclicity determinant c_Q vanishes identically on M.* The 4-sets split into three groups:
- non-local 4-sets are excluded by a first-order argument, using the bounds on R;
- 58 local types are handled by a first-order check that is exact for all θ ≤ arccos(433/500) ⊃ (0, π/6]. It uses sympy resultants and Sturm counts (`r2_convex_localtypes.py`);
- pairs of equal-length diameters are the only first-order failures. For them c″ is a nonzero quadratic form in the pair translation (`r2_convex_typeI.py`).

Since c_Q ≢ 0 on a connected analytic germ, a generic point of M near the seed avoids all concyclicities, and the open conditions of (i) persist there.

**Independent checks by me.**
- Float rank = 3n/2 at the seed for m = 3, 4, 5, 8, 13, 25. σ_min decays like ~1/m².
- Max non-edge distance < 1 at the seed for the same m.
- The 50-digit verification of n = 12, 20, 40 above.

**Points for a referee.** The first-order "wrap-gap" bookkeeping in (iii), and the analytic-genericity step. Rigour: I rate this high, not certain, because only the sub-agent has done the full proof.

### 1b. Non-convex family with m₃ = 0 (search sub-agent; independently re-verified)

Let m = 2k+1 be odd, n = 2m.

**Points.**
- Hull vertices p₀,…,p_{m−1} form a Reuleaux-type polygon: |p_i p_{i+k}| = Δ for all i.
- One server per hull edge: |s_i p_i| = |s_i p_{i+1}| = 1.
- A consecutive block of unit chords: |p_i p_{i+k−1}| = 1 for i = 0,…,k−2.

**Why Lemma T is avoided.** An alternating 4-cycle would need two chords whose indices differ by ±k. A block of k − 1 consecutive indices contains no such pair.

**Counts.** μ(Δ₂) = 2m + k − 1 = 5n/4 − 3/2 and μ(Δ) = m. The excess is (m − 3)/2 and t = m − 3.
- L₁ is the hull, L₂ is the servers, and m₃ = 0.
- Theorem A holds with equality.

**Structure of each degree-3 hull vertex p_i.**
- Its outer neighbours are its chord partner and one server.
- Its middle neighbour is the other server. That server is interior and has G-degree 2.
- The forced Δ-edge is a Reuleaux chord.

**Independent re-check.** Each configuration was re-polished from the agent's data with our own Gauss–Newton (`r2_polish.py`, 80 digits) and then run through `r2_verify.py` (70 digits):

| m | n | μ(Δ₂) | μ(Δ) | t | excess | residual | σ_min(J) | gap | min concyclic det |
|---|---|---|---|---|---|---|---|---|---|
| 7 | 14 | 16 | 7 | 4 | 2 | 9e-81 | 0.53 | 0.025 | 5.7e-5 |
| 11 | 22 | 26 | 11 | 8 | 4 | 7e-81 | 0.14 | 0.020 | 5.0e-7 |
| 21 | 42 | 51 | 21 | 18 | 9 | 1e-80 | 0.039 | 0.0017 | 4.6e-10 |

The agent also reports m = 9, 13, 15, 17, 19 and 31 (n = 62, excess 14).

**Rigour.** σ_min(J) ≫ residual, so Newton–Kantorovich puts an exact solution within ~1e-79 of each polished point. That is far below every margin. The Kantorovich constants were not written out.

**All m.** The heuristic reason the family works for all m is the sub-agent's chord identity. Take a Δ-edge (i−1, i+k), and let α_j be the angle at p_j between its two Δ-neighbours. Then
  |p_i p_{i+k−1}|² = Δ²(1 − 8 sin a sin b cos(a+b)), with a = α_{i−1}/2 and b = α_{i+k}/2.
This identity was checked numerically to 1e-15 and is not proved. The margins shrink polynomially, e.g. Δ − 1 ~ 1/m². A full proof needs an implicit-function argument on the angle system.

**#132(a) for these families.** Both families satisfy (a):
- the diameter is rare: μ(Δ) = n/4 or n/2;
- the convex family has a second rare distance by CDL Thm 1.2 (convex position);
- in family 1b, every distance other than 1 and Δ has multiplicity 1. This was checked at 40 digits for n = 14, 18, 26, 42 (`r2_search_rare.py`); the smallest gap between distinct values was ≥ 6e-12, against a matching tolerance of 1e-20.

**Chord blocks of size k (numerical, search sub-agent).** Take the hull-only angle model and use a block of k matched chords instead of k − 1.
- The best achievable margin is exactly 0, for m = 7, 9, 11, 13.
- At the optimum, every offset-(k−1) chord is forced to length 1. That is the full Ve87 structure, which Lemma T makes concyclic.
- This suggests a provable rigidity identity over the Δ-cycle.

**Trying to beat 5/4 (search sub-agent).** 850 chord/server types with 4μ₂ > 5n (offsets k−1 and k−2, servers of offset 1–2), for m = 7, 9, 11. **0 valid.** Every realisation degenerated in one of two ways:
- a server collapsed onto a hull vertex, by the Lemma M mechanism;
- adjacent hull vertices merged.

(`r2_search_anglefeas.py`, `r2_search_beat54.py`.)

So these are counterexamples to C1, not to #132.

## 2. Local structure around a degree-3 hull vertex (proved; local sub-agent, checked by coordinator)

**Frame.**
- Δ₂ = 1 and NFC.
- p = 0 is extreme with exactly three Δ₂-neighbours: w₂ = (1,0), w₁ = e(−α), w₃ = e(β), with α, β > 0 and α + β < 180°.
- P1–P4 and P6 need only this; they do not need core membership.
- Lemma M, Lemma T and Prop 1 are as in angle_C / VERIFY_A1c.
- Identities are checked in sympy (`r2_local_lemmas.py`, all True).

**P0.** t is even.
- Under NFC every G′-degree is 2 or 3.
- Degree-3 vertices of G′ are extreme (Prop 3, VERIFY_A1b).
- By the handshake lemma, t = 2(e(G′) − |V(G′)|).

**P1.** α, β ≤ 60°, and |w₁w₂|, |w₂w₃| ≤ 1.
- Chord length is strictly increasing on (0°, 180°), so |w₁w₂| = 2 sin(α/2) < |w₁w₃| ≤ Δ.
- Hence |w₁w₂| ≤ 1, so α ≤ 60°. The same argument gives β ≤ 60°.

**P2 (middle neighbour).** Every r ∈ N(w₂)∖{p} lies strictly off the line pw₂. If r is strictly on the w₃-side, then |rw₁| = Δ (so r is extreme) and |rw₃| ≤ 1. The w₁-side is symmetric.
- The first claim is Lemma M.
- r on the line means r = (2,0), so Δ = 2. But |rw₁|² = 5 − 4cos α ≤ 3, a contradiction.
- Suppose |rw₃| = Δ too. Then r lies on the bisector of w₁w₃, so r = 2cos θ·e(θ) with θ = (β−α)/2 ∈ (0°, 30°).
  - Then |pr| > √3, so |pr| = Δ.
  - But |r − w₁|² − |r|² = 1 − 2(cos α + cos β) ≤ −1 ≠ 0.

**P3.** deg_G(w₂) ≤ 3: there is at most one r on each side. This is exactly the Lean-proved `Erdos132Ve87.mid_pair_real`, applied with w = w₂ and b = w₁.

**P4 (outer neighbours).** Every r₁ ∈ N(w₁)∖{p} lies strictly on the w₂/w₃ side of the line pw₁.
- Otherwise Lemma M, applied twice, gives |r₁w₂| = |r₁w₃| = Δ.
- So r₁ = t·e(γ) with γ = a + b/2 ≤ 90° (frame w₁ = (1,0), w₂ = e(a), w₃ = e(a+b), using P1).
- Then t(t − 2cos γ) = 0, so r₁ = p or r₁ lies strictly inside. Either way this is a contradiction.
- This refutes the "case B" that the coordinator had anticipated.

**P5 (distinct middle neighbours).**
- Statement: let p ≠ p′ be extreme points with a common Δ₂-neighbour w. Suppose each has Δ₂-neighbours strictly on both sides of its line to w. Then X contains 4 concyclic points.
- Proof:
  - p′ is not strictly on one side of pw. Take a ∈ N(p) strictly on the other side. Lemma M gives |ap′| = Δ.
  - Symmetrically there is b ∈ N(p′) with |pb| = Δ.
  - Now |pb| = |ap′| = Δ and |pa| = |bp′| = 1, so Lemma T applies. Distinctness is immediate from the distances.
- **Under NFC, distinct degree-3 hull vertices have distinct middle neighbours.** This is what destroys the CDL alternate-servers configuration.

**P6 (dichotomy).** Take r on the w₃-side.
- The case (|pr|, |w₁w₃|) = (Δ, Δ) is impossible.
- If |pr| ≤ 1, the Δ-segment [w₁r] crosses the open segment (p, w₂), and {p, w₁, w₂, r} is in convex position.
- If |pr| = Δ, then α + β ≤ 60°.
- So every degree-3 hull vertex either has a Δ-partner in N(N(p)), or has a Δ-edge through an outer neighbour crossing its middle Δ₂-segment.

**Adversarial check.** P1–P4 and P6 were tested on 1,180 hull vertices with 3 neighbours from greedy sets, in floating point: 0 violations.

**Why no local argument could bound t.**
- The 5-point configuration (p, w₁, w₂, w₃, r) is realisable on an open 3-parameter set.
- An ear of length ℓ has 2(ℓ−1) degrees of freedom against ℓ + 2 equations.

The families in §1 confirm this globally. The sub-agent's conjecture t ≤ 2, drawn from myopic greedy data (n ≤ 26), is **false** (§1).

## 3. What the counterexamples teach

- In both families every degree-3 hull vertex p has the P6 structure. In 1a, the middle neighbour is itself degree 3 (3↔3 pairs). In 1b, it is an interior server.
- The NFC hypothesis only removes Lemma-T 4-cycles and shared middle neighbours (P5). Both constraints cost a constant factor, not the linear excess:
  - general sets: 3n/2 (Ve87) and 4n/3 (convex, Ve85);
  - NFC sets: at least 5n/4 − O(1) in both cases.
- In 1a the excess equals μ(Δ) = n/4. This matches Vesztergombi's convex inequality n₂ ≤ n + n₁ with equality.

## 4. Convex position: upper bound 5n/4 + C (computer-assisted; convex sub-agent; encoding not re-audited by me)

**Statement.** There is an absolute constant C such that every strictly convex n-set with no alternating 4-cycle (|ab| = |cd| = Δ, |ac| = |bd| = Δ₂) satisfies μ(Δ₂) ≤ 5n/4 + C. In particular this covers all NFC convex sets. Together with Theorem R2.1:

  **max{μ(Δ₂) : X convex, NFC, |X| = n} = 5n/4 + O(1).**

**Method.**
- Morić–Pritchard (arXiv 1103.0412) proved the 4/3 bound with a level/windowing framework (their Prop 4.1). The sub-agent recast their Lemma 4.2 as a SAT instance (`r2_convex_levels.py`).
- The grid has t_i for |i| ≤ 10 and b_j for |j−1| ≤ 10, so MP Lemma 1.5 is used with l = 22.
- Clauses come from:
  - MP Fact 3.1, via its consequences: no two non-crossing Δ-edges; Δ₂ + Δ₂ non-crossing forces a crossing Δ; Δ + Δ₂ non-crossing forces both crossing diagonals to be Δ;
  - MP Fact 3.2;
  - MP Fact 3.3 with (i, j) = (2,2) and (2,1);
  - Lemma T.
- MP Fact 3.4 is not used. The degree ≤ 3 and same-side clauses turn out to be unnecessary (ablation).

**Result.**
- At α = 5/4, L = 5 the instance is UNSAT. It has 3.1M clauses, and its core has 776 clauses.
- The CaDiCaL DRAT proof was checked by drat-trim.

**Controls.**
- Without Lemma T the encoding reproduces MP's 4/3 (UNSAT at L = 4).
- Dropping Lemma T or Fact 3.2 makes α = 5/4 satisfiable.
- The certified n = 32 set violates no clause (`r2_convex_soundtest.py`).

**Dependencies.**
- MP Lemma 1.5 and Prop 4.1 (published). C is their constant, which is not made explicit.
- The soundness of each clause encoding. Only the sub-agent has checked this. **Audit it before citing.**

## 5. Summary

**PROVED.**
- Exact, high confidence:
  - P0–P6 (§2), in particular P5: under NFC, distinct degree-3 hull vertices have distinct middle neighbours.
- High confidence (proof by the convex sub-agent, exact symbolic computations; partly re-checked by me):
  - **Theorem R2.1.** For every n ≡ 0 (mod 4), n ≥ 12, there is a convex NFC set with μ(Δ₂) = 5n/4 and μ(Δ) = n/4.
  - **So Conjecture C1 is false**, in weak and strong form, even for convex sets. Here t = n/2.
- Certified numerically (70–80-digit Newton with σ_min ≫ residual; no written Kantorovich constants):
  - The non-convex family 1b with m₃ = 0 and μ(Δ₂) = 5n/4 − 3/2, for n = 14, 18, …, 42, 62.
  - All its other distances are simple.

**Computer-assisted, pending an audit.** Convex + no alternating 4-cycle ⇒ μ(Δ₂) ≤ 5n/4 + C. This is sharp.

**Conjecture R2 (new).** Under NFC, for all finite X, μ(Δ₂) ≤ 5n/4 + O(1). Evidence:
- the two unrelated constructions both stop at 5/4;
- 850 searched types above 5/4 all degenerate;
- the convex case is settled (conditionally, §4).

For comparison, Theorem A gives (3/2)|L₁| + |L₂| and Ve87 gives 3n/2 without NFC.

**Obstruction for #132(a).**
- Under NFC, Δ₂ can occur 5n/4 times. So a proof of (a) for general-position sets must use some distance other than Δ₂ as the second rare one.
- In all our examples, rare distances are abundant: the diameter has μ(Δ) ≤ n/2, and generic distances are simple. So the families do not threaten (a).
- In both families the excess μ(Δ₂) − n is at most μ(Δ). Every degree-3 hull vertex forces a Δ-edge (P6). A plausible target is μ(Δ₂) ≤ n + μ(Δ) + O(1) under NFC; Vesztergombi's convex inequality n₂ ≤ n + n₁ holds with equality in family 1a.
- Such a bound would not by itself give (a).

**Next steps.**
1. Referee Theorem R2.1, especially the first-order wrap-gap argument and the analytic genericity step.
2. Audit the SAT encoding in §4.
3. Prove the block-k rigidity identity: a Reuleaux polygon with k matched offset-(k−1) unit chords forces all of them tight, which is Ve87 and therefore concyclic. Use it toward Conjecture R2 in the Reuleaux-plus-servers class.
4. Test μ(Δ₂) ≤ n + μ(Δ) + O(1) under NFC, and in general.
