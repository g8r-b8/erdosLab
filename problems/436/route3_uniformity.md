# Erdős #436, Λ(5,3), route 3: higher-order and local Fourier uniformity (2026-09-25)

Question. What local uniformity statement for μ_5-valued non-pretentious g would kill the 12
three-point terms in T (THEORY §7.0, §7.4)? What is proved in the literature? How far apart are the two?

Labels (as in THEORY §7):
- **PROOF**: a full argument is given here.
- **CITED**: arXiv id and theorem number, checked in the PDF text extracted with pypdf, 2026-09-25.
- **HEURISTIC**.
- **OPEN**.

Notation follows THEORY §7.0. Throughout:
- g: N → μ_5 is completely multiplicative and in **case C**: it weakly pretends to no χ.
- e = (e_0, e_1, e_2) ∈ T means e_i ≠ 0 and e_0 + e_1 + e_2 ≡ 0 mod 5.
- C_e(x) := E^log_{n≤x} g^{e_0}(n) g^{e_1}(n+1) g^{e_2}(n+2).
- For an interval I of length H, ‖f‖_{U^2(I)} is Tao's normalised local Gowers norm (1605.04628, just
  before Conj. 1.6).
- ‖f‖_{u^2(I)} := sup_α |E_{n∈I} f(n) e(−αn)| is the local Fourier norm. For 1-bounded f, u^2 and
  U^2 control each other polynomially: ‖f‖_{u^2} ≤ ‖f‖_{U^2} ≤ ‖f‖_{u^2}^{1/2}, up to absolute
  constants, via Parseval on Z/NZ with N ≍ H. So "local U^2 uniformity" and "local Fourier
  uniformity" are the same hypothesis.

---------------------------------------------------------------------------------------------------

## 0. Verdict (short)

1. **The right norm is U^2 (local Fourier uniformity), not U^3.** [PROOF, §2]
   - After dilation (entropy decrement, or Tao–Teräväinen isotopy), a three-point term becomes a
     local 3-term progression average. U^2 controls that average.
   - Prop 9.6's process is not genuinely quadratic. Its quadratic coefficient κ ∈ {1/5, 4/5} is
     rational, so e(κh^2) is 5-periodic. The process is a 1-step (Kronecker) object: a rotation on
     T × Z/5, as Prop 9.6(f) already says.
   - Its local Fourier bias is ≈ 0.418 on almost every window, both computed and measured. So local
     U^2 uniformity excludes it.
2. **Conditional theorems [PROOF, §3].** For a case-C g, local U^2 uniformity of g alone (or of g^2
   alone) forces all 12 terms of T to vanish. Then the zero-run log density is 1/125. Two versions:
   - **R3.1 [PROOF, complete modulo TT 1708.02610 Thm 1.2]:** log-averaged uniformity at bounded H
     (H → ∞ after x → ∞).
   - **R3.2 [PROOF sketch, adapting MRTTZ 2007.15644 Prop 1.7]:** uniformity only at polylog scales
     (log x)^η ≤ H ≤ (log x)^{1/10}, for every η > 0.
   Each version is needed along a single sequence of scales only.
   - The obstruction Tao flags for Elliott-type extensions (1605.04628 Rem. 1.10 / 3.5: the weight
     Λ·g_1⋯g_k needs a "higher order restriction theorem") **is absent for T**, because
     g^{e_0+e_1+e_2} ≡ 1. For T terms the λ proof goes through verbatim.
3. **What is known [CITED, §4].**
   - Local Fourier uniformity (sup inside the average) holds for arbitrary 1-bounded multiplicative
     functions that are non-pretentious in the MRT sense, which covers our case-C g.
   - The best range is H ≥ exp((log X)^{2/5+ε}): Pilatte, arXiv 2604.26564, Thm 1.3, April 2026.
   - Local U^k for all k holds at H ≥ X^θ (MRTTZ 2007.15644 Thm 1.5).
   - Under GRH: H ≥ (log X)^{K(η)} (Walsh 2310.07873 Thm 1.1).
   - Fixed-frequency (sup outside) and small frequency sets: MRT, KLRT.
4. **The gap [§5].**
   - Needed: log H ≍ η log log x.
   - Known unconditionally: log H ≥ (log x)^{2/5+ε}. That is an exponential gap in log H.
   - Known under GRH: H ≥ (log x)^{K}, against a needed H ≤ (log x)^{c} with c ≈ 1/10. That is a
     gap of exponents only.
   - MRTTZ state that the window H ∈ [(log X)^η, (log X)^{1/η}] "would likely necessitate an
     entirely new idea".
   - **Distance to the frontier:** this route needs the U^2 case of Tao's logarithmic local
     uniformity conjecture (1605.04628 Conj. 1.6, d = 2), transplanted to a μ_5-valued case-C g.
     That case is open even for λ. (For λ its three-point *consequence* happens to be known by the
     parity trick of Tao–Teräväinen 1710.02112. That trick is unavailable for T, where the product
     is trivial.) **It is out of reach, not a near miss.**
5. **Special features of G_5 do not lower the requirement in any known way [PROOF + HEURISTIC, §6].**
   - Only one of g, g^2 is needed. Only one sequence of scales is needed.
   - Positivity turns o(1) into "below an ineffective absolute threshold c_0".
   - But the obstruction model has local frequencies spread over all of T (Haar).
     - KLRT 2310.05528 Thm 1.2 / Thm 4.1: excluding local Fourier bias on any positive-measure
       frequency set is as hard as full local Fourier uniformity (for λ).
     - "No local correlation with the specific phase e(θh + κh^2), κ ∈ {±1/5}, θ free" is
       literally equivalent to local Fourier uniformity.
   - One genuinely new direction [HEURISTIC, §6.5]: Helfgott–Radziwiłł's conjectured 3-tensor
     decoupling (2103.06853 (9.2), k = 3) would move the needed scale up to
     H ≤ exp((log x)^{1/2−ε}). There local Fourier uniformity for non-pretentious f **is now
     known** (Pilatte 2604.26564 Thm 1.3, exponent 2/5 < 1/2).
     - So G_5 would follow from a divisor-hypergraph expansion statement that does not involve g
       at all.
     - That statement is open. Neither we nor HR know how to prove it.

---------------------------------------------------------------------------------------------------

## 1. The reduction chain (what Tao's equivalence says, and its Elliott analogue)

**Tao 1605.04628 [CITED].**
- Conj. 1.6 (log local Gowers uniformity of λ):
  Σ_{X/ω≤n≤X} ‖λ‖_{U^d([n,n+H])}/n = o_{H→∞}(log ω), for 2 ≤ H ≤ ω ≤ X.
- Conj. 1.7 is the nilsequence form, with the sup over g **inside** the n-sum.
- Thm 1.8: Conjectures 1.3–1.7 (log Chowla, log Sarnak, local U^d, local nilsequences) are
  equivalent. Rem. 1.9: one may take ω = X.
- **Rem. 3.4 (verified):** "if one wishes to establish Conjecture 1.3 for a specific choice of k ≥ 3,
  then it would suffice to establish Conjecture 1.6 for d = k − 1. In particular, the first open
  case k = 3 … would follow from a non-trivial bound on the local U^2 norms." So **three-point
  correlations need U^2.**
- §3 is the mechanism, Prop 3.1 → Prop 3.3 → generalised von Neumann:
  - λ(p)^k from dilation n ↦ pn;
  - entropy decrement at a scale H_- ≤ H ≤ H_+;
  - W-trick removes the Λ weight;
  - the local k-AP average is bounded by ‖λ‖_{U^{k−1}}.
- Rem. 1.10 and Rem. 3.5: for general multiplicative g_1,…,g_k the weight becomes Λ·g_1⋯g_k, and
  one would need a "higher order restriction theorem for the primes" or a transference principle;
  "possibly after increasing d to k".

**For our 12 terms that obstruction disappears [PROOF].**
- For e ∈ T, the dilation identity reads
  Π_i g^{e_i}(pn + pi) = g(p)^{e_0+e_1+e_2} Π_i g^{e_i}(n+i) = Π_i g^{e_i}(n+i).
- The weight is exactly Λ, as for λ. Every step of Tao §3 then uses only three facts:
  - |g| = 1;
  - g takes finitely many values, so the entropy bound H(X_H) ≤ H log 5;
  - complete multiplicativity.
- So Tao's Rem. 3.4 transfers to T **with d = 2**. No increase to d = k is needed.
- Sections 3.1 and 3.2 give two rigorous forms.

**The 112 other terms** need nothing new (THEORY §7.4):
- TT 1708.02610 Cor 1.6 covers every term with non-trivial product;
- Tao 1509.05422 Cor 1.5 covers the two-point terms with trivial product.

**Why the two-point trivial-product case needed less.**
- Tao's two-point theorem uses only the *sup-outside* estimate of MRT 1501.04585 ("sup_α ∫ …").
  1812.01224 §1 says so explicitly: "(4) along with the entropy decrement argument was used by [31]
  to establish a logarithmically averaged version".
- After dilation, a two-point term is E_n E_p f_0(n) f_1(n+p). This is a correlation with a fixed
  structure, not a 3-AP.
- At three points the 3-AP average appears, and the sup must be **inside**.
- This is the exact jump from "known" to "open".

## 2. Which norm: U^2, and why Prop 9.6 does not contradict it

**Lemma R3.0 (one power suffices) [PROOF + check].** Every e ∈ T has a coordinate in {1,4} and a
coordinate in {2,3}.
*Proof.*
- If all three coordinates lie in {±1}: the sums of three elements of {1,4} are 3, 1, 4, 2 mod 5,
  never 0.
- If all lie in {±2}: the sums of three elements of {2,3} are 1, 2, 3, 4 mod 5, never 0.
∎
Checked by enumeration in `scripts/route3_checks.py`. Since ‖g^{−j}‖ = ‖\bar{g^j}‖ = ‖g^j‖, local
U^2 uniformity of **g alone**, or of **g^2 alone**, controls all 12 terms in the generalised von
Neumann step, which can bound by the norm of any chosen coordinate (§3.1, step 4).

**Prop 9.6's model is 1-step [PROOF].** Recall u_h = y + hθ − κ(s+h)^2, κ ∈ {1/5, 4/5}, and
X_h = ⌊5u_h⌋.
1. Put F(u) := ζ^{⌊5u⌋} on T. Then F(u + 1/5) = ζF(u), so F̂(m) = 0 unless m ≡ 1 mod 5.
   F̂(1) = 5(1 − e(−1/5))/(2πi), so |F̂(1)| = 5 sin(π/5)/π ≈ 0.9355.
2. e(−mκ(s+h)^2) is 5-periodic in h, because 5κm^2 ∈ Z. Its discrete Fourier coefficients are
   normalised quadratic Gauss sums, of modulus 5^{−1/2} each.
3. Hence ζ^{X_h} = Σ_m F̂(m) e(my − mκ(s+h)^2 + mhθ) is a Bohr-almost-periodic sequence. Its
   spectrum is {mθ + r/5}. On every window,
   sup_α |E_{h<H} ζ^{X_h} e(−αh)| → |F̂(1)|·5^{−1/2} ≈ 0.418 as H → ∞, for θ irrational.
   - Measured (`route3_checks.py`, H = 4000, 200 samples): min 0.416, median 0.418.
   - An i.i.d. control gives 0.051.
4. So in any log-Furstenberg system realising the model, E^log ‖g‖_{u^2[n,n+H]} ≳ 0.418 for all
   large H. **Local U^2 uniformity excludes the model.** The task's premise "the process is
   quadratic, so U^2 is not enough" does not hold: the quadratic phase has a rational coefficient.
   This is the same as Prop 9.6(f) (components are rotations of T × Z/5) and THEORY §9.6
   "candidate 3".
5. [HEURISTIC, from THEORY §9.6, not re-proved] Genuinely 2-step twists (κ irrational, or
   cubic/generalised-polynomial phases) are *not* controlled by U^2. §9.6 argues that irrational κ
   gives constant triples positive mass anyway. So U^3 structure is not the danger; the torsion
   (Z/5) part of 1-step structure is.

Where exactly the obstruction sits:
- After the W-trick (§3.2), differences d run over d ≡ r mod W with (r, W) = 1 and 5 | W. So the
  Z/5-coordinate of the local rotation moves by r ≢ 0 at every step.
- Pure irrational Bohr structure cannot avoid constant triples: for small dθ, the three points are
  close. The rational part of the local spectrum, combined with a random irrational part, can.
- Local Fourier uniformity removes both parts.

## 3. Conditional theorems

### 3.1 Theorem R3.1 (bounded-H local U^2 ⇒ T vanishes) [PROOF, modulo TT 1708.02610 Thm 1.2]

**Theorem R3.1.** Let g be in case C. Let x_m → ∞ and 2 ≤ ω_m ≤ x_m with ω_m → ∞; ω_m = x_m is
allowed. Write E^log_m for the average over x_m/ω_m ≤ n ≤ x_m. Suppose that for j = 1 or j = 2:

 (LU²_j)  lim_{H→∞} limsup_{m→∞} E^log_m ‖g^j‖_{U^2([n+1, n+H])} = 0.

Then:
- C_e(x_m) → 0 for every e ∈ T;
- E^log_m 1[g(n) = g(n+1) = g(n+2) = 1] → 1/125;
- in particular g has zero runs.

If (LU²_1) holds for every case-C g (along x_m = m, say), then G_5 holds, and so Λ(5,3) < ∞
(THEORY Thm 7.5).

*Proof.*

**Step 1 (set-up).**
- Fix e ∈ T and, by Lemma R3.0, an index i ∈ {0,1,2} with e_i ∈ {±j}.
- Put h_k := k − i for k = 0, 1, 2, so h_i = 0 and the other two h_k are distinct and nonzero.
- Fix a generalised limit functional ~lim, as in TT 1708.02610 §1, and define for a ∈ Z
  f(a) := ~lim_m E^log_m Π_k g^{e_k}(n + a h_k).
- Log averages over [x/ω, x] are invariant under a fixed shift of n, up to O_a(1/log ω). So
  f(1) = ~lim_m C_e(x_m).

**Step 2 (isotopy) [CITED: TT 1708.02610 Thm 1.2 (i), (iii)].**
- The product g^{e_0}g^{e_1}g^{e_2} ≡ 1 weakly pretends to the principal character. So for every
  ε > 0 there is a q-periodic F_ε with sup_a |f(a) − F_ε(a)| ≤ ε and F_ε(ab) = F_ε(a) for all b
  coprime to q.
- Hence |f(b) − f(1)| ≤ 2ε for every b with (b, q) = 1.

**Step 3 (average over b).** For any B ≥ 1,
f(1) = E_{b≤B, (b,q)=1} f(b) + O(ε) = ~lim_m E^log_m A_B(n) + O(ε), where
A_B(n) := E_{b≤B,(b,q)=1} Π_k g^{e_k}(n + b h_k).
By shift invariance again, E^log_m A_B(n) = E^log_m E_{1≤t≤B} A_B(n+t) + O_B(1/log ω_m).

**Step 4 (local generalised von Neumann).** Fix n. Put F_k(y) := g^{e_k}(n+y). Then

 E_{t≤B} A_B(n+t) = (q/φ(q) + o_B(1)) · E_{t≤B} E_{b≤B} 1_{(b,q)=1} F_i(t) Π_{k≠i} F_k(t + b h_k).

Three reductions put this in standard form.
- Coprimality weight: write 1_{(b,q)=1} = Σ_{s mod q} c_s e(sb/q), with |c_s| ≤ 1. Let k ≠ l be
  the two indices other than i. Since b = ((t + bh_k) − (t + bh_l))/(h_k − h_l), each phase
  e(sb/q) factors as a function of t + bh_k times a function of t + bh_l, and can be absorbed into
  F_k and F_l.
- Cutoff 1_{[1,B]}(b): approximate it in L^1(Z/N) to within δ by a trigonometric polynomial with
  O_δ(1) terms, with N a prime ≍ B. Absorb each term in the same way.
- What remains is Σ_{t,b∈Z/N} F_i1_{[1,B]}(t) G_k(t + bh_k) G_l(t + bh_l) with 1-bounded G's.
  Since h_k ≠ h_l are nonzero and N > 2 max|h|, Fourier expansion bounds it by
  N^2 max_ξ |(F_i1_{[1,B]})^(ξ)| ≤ N^2 ‖F_i1_{[1,B]}‖_{U^2(Z/N)}.

Normalising (N ≍ B):

 |E_{t≤B} A_B(n+t)| ≤ C(q, δ) ‖g^{e_i}‖_{U^2([n+1,n+B])} + C δ + o_{B→∞}(1).

**Step 5 (limits).**
- ‖g^{e_i}‖_{U^2} = ‖g^j‖_{U^2}, because e_i = ±j and conjugation preserves U^2.
- Averaging and applying (LU²_j) as B → ∞ gives |f(1)| ≤ O(ε) + Cδ.
- Let δ → 0, then ε → 0. (q depends on ε only; fix ε, then q, then δ, then B.)
- So f(1) = 0 for every generalised limit, hence C_e(x_m) → 0.
- With the 112 other terms (THEORY §7.4, valid along any x_m, ω_m), THEORY Lemma 7.3 and Prop 9.5
  give zero-run density → 1/125.
∎

Remarks.
- (a) **Where (LU²) comes from.** It follows from the 4-point logarithmic Elliott conjecture for g
  [PROOF sketch]:
  E^log ‖g‖^4_{U^2[n+1,n+H]} is a weighted average over |h_1|, |h_2| ≤ H of
  E^log g(n)\bar g(n+h_1)\bar g(n+h_2) g(n+h_1+h_2).
  - Degenerate pairs (h_1 h_2 = 0) contribute O(1/H).
  - The other pairs → 0 under 4-point log Elliott, since case-C g satisfies (1.8) by Lemma 7.2.
  - This is the analogue of Tao 1605.04628 Rem. 1.12.
  So the hypothesis sits between the 3-point (T) and 4-point log Elliott conjectures for g.
- (b) (LU²) at bounded H implies the same at every larger H(x) → ∞. For u^2: cut [n, n+H(x)] into
  blocks of length H_0. So R3.1's hypothesis is the *stronger* of the two in this section.

### 3.2 Theorem R3.2 (polylog-scale local U^2 suffices) [PROOF sketch: an adaptation of MRTTZ 2007.15644 Prop 1.7]

**Theorem R3.2.** Let g be in case C, j ∈ {1, 2}, and x_m → ∞. Suppose that for every η ∈ (0, 1/10]
and every choice (log x)^η ≤ H(x) ≤ (log x)^{1/10}:

 E^log_{n≤x_m} ‖g^j‖_{U^2([n, n+H(x_m)])} → 0 as m → ∞.

Then C_e(x_m) → 0 for all e ∈ T, and the conclusion of R3.1 holds.

*Proof sketch.* This follows the proof of MRTTZ 2007.15644 **Prop 1.7** (§5.3; verified: it is
stated and proved for λ).

1. **Approximate functional equation at one scale.**
   - Set f_x(d) := E^log_{n≤x} Π_k g^{e_k}(n + d h_k), with h_k = k − i as in §3.1.
   - Claim: |f_x(1) − E_{2^m<p≤2^{m+1}} f_x(p)| ≪ ε for all m ≤ log log x outside an exceptional
     set M with Σ_{m∈M} 1/m ≪ ε^{−3}.
   - This is TT 1710.02112 **Thm 3.1** with (−1)^k replaced by g(p)^{e_0+e_1+e_2} = 1. We read the
     proof (§4 of that paper). It uses λ only through the identity λ(n) = −λ(pn) and the finite
     alphabet of X_m ∈ {±1}^{C2^m}.
   - For us the identity is g^{e}(pn + ph) = g(p)^{e} g^{e}(n+h), with product 1, and
     X_m ∈ μ_5^{C2^m}, so H(X_1) = O(a log 5). The signs c_p become unit complex numbers; split
     into real and imaginary parts for the concentration step.
   - The general-g form of this statement, with generalised limits and the same Σ 1/m bound, is
     TT 1708.02610 **Thm 3.6 + Rem. 3.7** (CITED).
2. **Choose the scale.** Choose m ∈ [ε′ log log x, (1/10) log log x] ∖ M, where ε′ = exp(−ε^{−10}).
   This is possible because Σ 1/m over that range is ≍ ε^{−10} ≫ ε^{−3}. Then
   P := 2^m ∈ [(log x)^{η}, (log x)^{1/10}] with η = ε′ log 2.
3. **W-trick** (TT 1710.02112 **Thm 3.2** and **Lemma 5.2**; the proof in §5 is deterministic in
   the functions φ_j):
   E_p f_x(p) = (W/φ(W)) E_{P≤d≤2P, (d,W)=1} f_x(d) + O(ε), with W = Π_{p≤w} p and w large
   depending on ε. This uses the Gowers uniformity of W-tricked Λ, with P → ∞.
4. **Local von Neumann**, exactly as in Step 4 of §3.1, with q replaced by W and B by P:
   |f_x(1)| ≤ C(W, δ) E^log_{n≤x} ‖g^j‖_{U^2[n, n+3P]} + Cδ + O(ε).
   The hypothesis at H(x) = 3P kills the first term.
∎

Status:
- This is a sketch. Each step is a cited argument, and the changes are listed above. We did not
  write out the entropy computation in full for μ_5.
- **Refinement [HEURISTIC; constants not tracked].** In R3.2, W depends only on ε, not on g. So
  the argument should give: *there is an absolute (ineffective) c_0 > 0 such that*
  limsup E^log ‖g‖_{U^2} ≤ c_0 *at the scales in step 2 ⇒ |Σ_T C_e| < 1 ⇒ zero runs.*
  - For G_5, positivity suffices (THEORY §7.5 item 2).
  - In R3.1 this fails as stated, because q = q(ε, g) depends on g.

### 3.3 What R3.1 and R3.2 do and do not say

- They are *conditional*. The hypothesis is a local Fourier uniformity statement for a single
  μ_5-valued case-C function. It is not known for any case-C g, not even for λ_1 = ζ^{Ω(n)}
  (§4, §5).
- They need no hypothesis on nilsequences of step ≥ 2 (U^2 suffices), and none on g^3, g^4
  (g or g^2 suffices).
- Folklore status [HEURISTIC]: the implication is Tao's Rem. 3.4 plus the observation that T has
  trivial product. It is presumably known to experts. Present it as "recorded", not as new
  (cf. THEORY §8 item 12).

## 4. What is proved: literature table [CITED unless noted]

"Sup inside" means sup_α (or sup over nilsequences) inside the x-average; this is what the
reduction needs. "Sup outside" means a fixed phase. "NP" means the stated non-pretentiousness
hypothesis. Its form is M(f; X^{k+1}/H^{k+1}, Q) → ∞, or inf over |t| ≤ X^2/H^{2−o(1)} and
q ≤ Q of D(f, χ n^{it}; X) → ∞.
**For case-C μ_5-valued g these hold.** The Vinogradov–Korobov argument of THEORY Lemma 7.2 gives
this, uniformly over |t| ≤ X^{O(1)} and bounded conductor. Its regime 1 covers 1 ≤ |kt| ≤ x^{O(1)}
with the same (F1). [PROOF: same as Lemma 7.2; also MRT 1812.01224 remark after Thm 1.4 and
MRTTZ "(1.12) of [25]".]

| source | functions | norm / object | H range | averaging | reference |
|---|---|---|---|---|---|
| Matomäki–Radziwiłł (via MRT 1501.04585) | real / general NP multiplicative | U^1 (short sums), and fixed α (sup **outside**) | any H → ∞ | almost all x | quoted in 1812.01224 §1 eq. (3)–(4), 1605.04628 after Conj. 1.7 |
| Tao 1509.05422 | g_1 with (1.8) | two-point log Elliott | — | log | Thm 1.3, Cor 1.5 (THEORY §7) |
| MRT 1812.01224 | λ; any 1-bounded multiplicative f | u^2, sup inside | H = X^θ, θ > 0 | ∫_X^{2X} dx (almost all) | **Thm 1.2** (λ), **Thm 1.4** (f: bias ⇒ D(f; X^2/H^{2−ρ}; Q) ≪ 1), Cor 1.5 (f(n)a(n+h)b(n+2h) with sieve-majorised a, b) |
| MRTTZ 2007.15644 | λ; any 1-bounded multiplicative f | u^{k+1} (poly phases), U^{k+1}, nilsequences | X^θ ≤ H ≤ X^{1−θ} (all k); u^{k+1} down to exp((log X)^{5/8+ε}) | almost all x | **Thm 1.3, Thm 1.5** (general f), **Cor 1.1, 1.6** (λ), **Thm 1.8** (short H, u^{k+1} only), **Prop 1.7** (λ: U^k at H = (log X)^η for all η, k ⇒ log Chowla) |
| Walsh 2102.05564 | any 1-bounded multiplicative g | u^2 | H = X^δ | almost all x | **Thm 1.1** (simpler proof of MRT) |
| Walsh 2304.09792 | any 1-bounded multiplicative g | u^2 | exp(C(log X)^{1/2}(log log X)^{1/2}) ≤ H ≤ X^{1/2} | almost all x | **Thm 1.1** |
| Walsh 2310.07873 | any 1-bounded multiplicative g | u^2 | H ≥ (log X)^{K(η)} | almost all x | **Thm 1.1, conditional on GRH** |
| **Pilatte 2604.26564** (Apr 2026) | λ; any 1-bounded multiplicative f | u^2 | **H ≥ exp((log X)^{2/5+ε})**, bias δ ≥ C(log log X)^{−1/2} | almost all x | **Thm 1.2** (λ), **Thm 1.3** (f: bias ⇒ Σ_p (1−Re f(p)χ(p)p^{it})/p ≪ log δ^{−1}, cond(χ) = O(δ^{−O(1)}), \|t\| ≤ X^2/H^{2−o(1)}). The author says 2/5 is "the natural limit of our unconditional methods". |
| Pilatte 2310.19357 | λ | two-point log Chowla, rate (log x)^{−c} | (uses MRT at H = exp((log X)^{1/2−c})) | log | **Thm 1.1**; λ only; says it "should generalise" |
| Helfgott–Radziwiłł 2103.06853 | λ (k = 2) | expander / trace method | — | log | Main thm; **§9.5 (9.2)** conjectures k-tensor decoupling [OPEN] |
| Matomäki–Shao–Tao–Teräväinen 2204.03754 | μ, Λ, d_k only | nilsequences, U^s | **all** intervals, H ≥ X^{5/8+ε} (μ, Λ, d_k) | every x | Thm 1.1 (abstract checked) |
| MRSTT 2411.05770 | μ, Λ, d_k only | nilsequences, U^s | almost all x; μ: H ≥ X^{1/3+ε} (Thm 1.1(i)) | almost all x | Thm 1.1 |
| Tao–Teräväinen 1708.02610 | any 1-bounded multiplicative | structure of log correlation sequences | — | log | **Thm 1.2** (periodic, χ-isotypic), **Cor 1.6**, **Thm 3.6 + Rem 3.7** |
| Tao–Teräväinen 1710.02112 | λ | odd-order log Chowla (parity trick; no Fourier uniformity) | — | log | Thm 1.1, **Thm 3.1, 3.2, Lemma 5.2** |
| Tao–Teräväinen 1809.02518 | general | Cesàro correlations at almost all scales | — | Cesàro, almost all X | Thm 1.7 (no new information for T) |
| Kanigowski–Lemańczyk–Richter–Teräväinen 2310.05528 | λ | u^2 with α restricted to a closed set C | **any H → ∞** | log | **Cor 1.1** (Leb C = 0 ⇒ uniform), **Thm 2.4** (bias on C ≪ Leb(C)^{1/4}), **Thm 1.2 / 4.1** (C with interior, or positive measure with all character twists ⇒ full conjecture), Thm 1.5, 1.6, Cor 1.7 (e(αh^t), α in small or countable irrational sets) |

Notes on the table.
- No result handles μ_k-valued g *specifically*. All general results are for arbitrary 1-bounded
  multiplicative f under non-pretentiousness, and they apply to case-C g as noted above.
- No result gives local U^2 (sup inside) at any H ≤ exp((log X)^{2/5}) unconditionally, for any
  non-pretentious function, λ included.
- The only local uniformity at H → ∞ arbitrarily slowly is:
  - U^1 (MR);
  - fixed frequencies (MRT; He–Wang for polynomial phases, quoted in MRTTZ);
  - small frequency sets (KLRT, λ).

## 5. Needed vs known

| ingredient | needed for T (hence G_5) | best known unconditional | best known under GRH | gap |
|---|---|---|---|---|
| norm | U^2 (local Fourier), sup inside [§2, §3] | U^2 and U^k (all k), sup inside | same | none in the *norm* |
| function class | one fixed case-C μ_5-valued g (or g^2) | any 1-bounded NP f | any 1-bounded NP f | none |
| averaging over x | log-averaged, almost all n, along one sequence of scales | Cesàro almost all x (stronger) | same | none |
| scale H (entropy route, R3.2) | H ∈ [(log x)^η, (log x)^{1/10}], all η > 0 (or η ≤ η_0 for positivity only) | H ≥ exp((log x)^{2/5+ε}) (Pilatte Thm 1.3) | H ≥ (log x)^{K(η)} (Walsh 2310.07873) | unconditional: log H from η log log x to (log x)^{2/5}. GRH: exponent K(c_0) > 1 vs ≤ 1/10 |
| scale H (bounded, R3.1) | H = O(1) → ∞ | same as above | same | larger |
| scale H (expander route, §6.5) | H ≤ exp((log x)^{1/2−ε}) | **H ≥ exp((log x)^{2/5+ε}): available** | — | none in H; instead needs HR (9.2) for k = 3 [OPEN] |
| bias size | o(1) (R3.1/R3.2), or < c_0 (positivity, heuristic) | o(1) and even δ ≥ C(log log X)^{−1/2} | — | — |

The obstruction in the H-column is structural, not technical.
- MRTTZ 2007.15644 p. 8–9 [CITED, verified]: "Handling the regime H ∈ [(log X)^η, (log X)^{η^{-1}}],
  at the very least, would likely necessitate an entirely new idea". The reasons given:
  - even under GRH, cancellation in Σ_{H^ε≤p≤2H^ε} χ(p)p^{it} is known only for
    H ≫ (log X)^{(2+κ)ε^{−1}};
  - "approximate functional equation" arguments need Π_{H^ε≤p≤2H^ε} p ≫ X;
  - the entropy decrement is confined to H ≤ (log X)^η.
- Walsh 2310.07873 §1 lists the same three obstacles ("mixing", "iterative losses", "lack of
  enough primes in the range H ≤ log X"). His GRH theorem clears the second and third, but only
  down to (log X)^{K}.

## 6. Special features of G_5: do they lower the requirement?

1. **One power, one sequence of scales** [PROOF, R3.0, R3.1].
   - G_5 needs U^2 uniformity of g *or* of g^2, along one sequence x_m.
   - This is weaker than the full conjecture's "all powers, all scales", but no known theorem
     distinguishes these cases at small H.
2. **Positivity instead of vanishing** [HEURISTIC, §3.2 refinement].
   - We need only limsup (P_1+P_2+P_3) > 2/5 (THEORY Prop 9.5), i.e. |Σ_T C_e| < 1 at some scales.
   - So a *non-trivial but not o(1)* local U^2 bound, below an ineffective absolute c_0, would do.
   - The model has bias 0.418 (§2), so any such c_0 is < 0.42.
   - No unconditional bound of the form "E^log ‖g‖_{u^2[n,n+H]} ≤ 1 − δ at H = (log x)^η" is known
     either. Pilatte's Thm 1.3 allows bias δ ≥ C(log log X)^{−1/2}, but only at
     H ≥ exp((log X)^{2/5+ε}).
3. **Only the specific quadratic form of Prop 9.6?** [PROOF of the equivalence below.]
   - The model's local structure is e(θh)·ψ(h), where ψ(h) = e(−κ(s+h)^2) is 5-periodic and θ is
     free. For any α, e(αh) = e((α − 1/5)h)·e(h/5).
   - Therefore sup_{θ, ψ 5-periodic, nonconstant} |E_h g(n+h) e(θh)ψ(h)| ≥ ‖g‖_{u^2[n,n+H]}.
     Conversely it is ≤ 5^{1/2} ‖g‖_{u^2}, by Cauchy–Schwarz on the ≤ 5 Fourier coefficients of ψ.
   - So **"no local correlation with rational-quadratic phases e(θh − κh^2), κ ∈ {±1/5}" is
     equivalent to local Fourier uniformity.** It is not a special case.
   - KLRT 2310.05528 make the same point for λ in their §1.4. If their (1.15) holds for some
     infinite closed C containing a rational, then the degree t−1 statement holds on all of T.
     KLRT Cor 1.7 (irrational countable C) does not apply, because 1/5 is rational.
   - **Status of "g does not correlate locally with quadratic phases" for NP μ_k-valued g at the
     relevant scale: not known.**
     - Known at H ≥ X^θ (MRTTZ Thm 1.3/1.5, general f) and, for polynomial phases (u^3), at
       H ≥ exp((log X)^{5/8+ε}) (MRTTZ Thm 1.8, general f).
     - At H → ∞ slowly, it is known for λ only with the leading coefficient in a set of box
       dimension < 1/2, or countable and irrational (KLRT Thm 1.5, Cor 1.7), and with no free
       linear part in Thm 1.5.
     - None of these reaches (log x)^η for the rational leading coefficient ±1/5 with a free
       linear term.
4. **Frequency spreading lemma (adaptation of KLRT Thm 2.4 to case C, log averages) [PROOF].**
   For a case-C g and any closed C ⊂ T:
   limsup_{H→∞} limsup_{x→∞} E^log_{n≤x} sup_{α∈C} |E_{h≤H} g(n+h) e(hα)| ≪ Leb(C)^{1/4}.
   *Proof.* Follow KLRT's proof of Thm 2.4 (verified).
   - Let ε = Leb(C). Their Lemma 2.3 covers C by J ≤ 2ε^{3/4}H intervals of length ε^{1/4}/H
     (H large), with centres α_j.
   - On each interval, the sup is within O(ε^{1/4}) of the value at α_j.
   - Chebyshev: P^log(|E_h g(n+h)e(α_j h)| ≥ ε^{1/4}) ≤ ε^{−1/2} H^{−2} Σ_{h_1,h_2≤H}
     |E^log g(n+h_1)\bar g(n+h_2)| ≤ ε^{−1/2}(1/H + o_{x→∞}(1)). The off-diagonal terms vanish
     for case-C g by Tao 1509.05422 Cor 1.5 plus THEORY Lemma 7.2.
   - Union over j: ≤ 2ε^{1/4}.
   ∎
   Consequence: any local Fourier bias of a case-C g must be carried by frequency sets of positive
   measure.
   - The Prop 9.6 model is consistent with this: θ is Haar distributed.
   - KLRT Thm 1.2 / Thm 4.1 (for λ) show that going beyond measure 0 is equivalent to the full
     conjecture.
   - **So the small-set literature cannot touch the model. The model sits exactly in the regime
     that is as hard as the whole conjecture.**
5. **Expander route (Helfgott–Radziwiłł; Pilatte) [HEURISTIC; the key open input is combinatorial].**
   - HR 2103.06853 §9.5 conjecture (9.2) [CITED as a conjecture, verified]: for N = (N, 2N],
     a set P of primes, L = Σ_{p∈P} 1/p, and f_i with suitable ℓ^{r_i} bounds,
     (1/NL)|Σ_n Σ_{p∈P, p|n} f_1(n+a_1p)⋯f_k(n+a_kp) − Σ_n Σ_{p∈P} f_1(n+a_1p)⋯f_k(n+a_kp)/p| ≪ L^{−1/2}.
     HR note that the second sum "might be within reach, due to the broad range we are allowing
     for H, namely, H ≤ exp((log x)^{1/2−ε})".
   - Pilatte 2604.26564 §1.2 [verified] says Theorem 1.2 "would now provide the necessary
     number-theoretic ingredient, at least for linear phases".
   - **For our T-terms (k = 3), linear phases are all that is needed (§2).**
     - For e ∈ T, g^{e_i}(n + a_i p) with p | n equals g(p)^{e_i} g^{e_i}(n/p + a_i), and the
       product of the g(p) factors is 1. So the first sum in (9.2) is ≈ L·C_e(x) after log
       averaging.
     - The second sum is the local 3-AP with prime differences at scale H, which the W-trick and
       §3.1 step 4 bound by local U^2.
     - The needed U^2 input at H ≤ exp((log x)^{1/2−ε}) is supplied for case-C g by Pilatte
       **Thm 1.3** (exponent 2/5 + ε). Its hypothesis holds by the VK remark in §4.
   - **Conditional statement [HEURISTIC; bookkeeping of P-ranges, Cesàro-vs-log and the r_i-norm
     conditions not checked]:** HR (9.2) with k = 3 for P ⊂ [exp((log x)^{2/5+2ε}),
     exp((log x)^{1/2−ε})] ⇒ C_e → 0 for e ∈ T ⇒ G_5.
   - (9.2) is a statement about the divisibility hypergraph. It does not involve g, and it is
     **OPEN**. HR explain why their trace method does not extend: tensors have no clear analogue
     of the trace.
   - This is the only formulation we found in which the *number-theoretic* input for G_5 is
     already a theorem.

## 7. Honest verdict

- **Exactly what is needed.** Local U^2 = local Fourier uniformity, with the sup inside the
  average. It is needed for one μ_5-valued case-C function (g or g^2), log-averaged, at polylog
  scales H = (log x)^η for every η > 0 (Thm R3.2), or at bounded H (Thm R3.1). Positivity
  (heuristically) lowers "→ 0" to "< c_0". Nothing about U^3 or higher-step nilsequences is needed.
  Prop 9.6's "quadratic" model is 1-step and is excluded by U^2.
- **What is known.** The same norm, for the same class of functions (arbitrary 1-bounded
  non-pretentious multiplicative f, which includes every case-C g), but only at
  H ≥ exp((log x)^{2/5+ε}) (Pilatte 2026). Under GRH, H ≥ (log x)^{K} (Walsh).
- **Distance.** The gap is the full "small H" regime that experts (MRTTZ, Walsh, Pilatte) describe
  as requiring a new idea. It is the same gap that separates the known cases of logarithmic
  Chowla (k = 2 and odd k) from the first open one. The route reduces G_5 to a problem at least as
  hard as the U^2 case of Tao's local uniformity conjecture for μ_5-valued functions.
  **This route does not bring Λ(5,3) < ∞ within reach. We see no special feature of G_5 that
  shortcuts it.**
- **Proved here.**
  - Thm R3.1 [PROOF], and Thm R3.2 [PROOF sketch]: the conditional implications
    "local U^2 of g or g^2 ⇒ T vanishes ⇒ G_5 ⇒ Λ(5,3) < ∞" (with THEORY Thm 7.5).
  - Lemma R3.0 (one power suffices).
  - The identification of Prop 9.6 as 1-step, with bias ≈ 0.418.
  - The equivalence "rational-quadratic twist ⇔ full Fourier uniformity" (§6.3).
  - The case-C frequency-spreading lemma (§6.4).
- **Most promising lead [HEURISTIC].** §6.5. With Pilatte's 2026 exponent 2/5 < 1/2, a 3-tensor
  version of the Helfgott–Radziwiłł decoupling (a combinatorial statement about divisibility by
  primes, independent of g) would give G_5, and with it the 3-point trivial-product log Elliott
  conjecture for every case-C μ_5-valued g. This is a research problem (HR §9.5 explain the
  obstacle), not a near-term step.

## 8. Reproducibility

- `scripts/route3_checks.py` (well under 1 s CPU, < 50 MB) covers:
  - the enumeration in Lemma R3.0;
  - the Monte Carlo of the model's local Fourier bias (H = 4000, 200 samples, FFT with 8× zero
    padding), against the prediction 5^{1/2} sin(π/5)/π ≈ 0.418.
- PDFs and pypdf text extracts are in the session scratchpad `lit/`, not in the repo:
  1605.04628, 1812.01224, 2007.15644, 2204.03754, 2411.05770, 2102.05564, 2304.09792, 2310.07873,
  2604.26564, 2310.19357, 2310.05528, 2103.06853, 1708.02610, 1710.02112, 1809.02518.
- Theorem numbers quoted above were read in those extracts. Two abstracts only:
  - 2204.03754: we checked the abstract, not the theorem statement.
  - 1501.04585: quoted through 1812.01224 and 1605.04628, not read directly.
- arXiv searches (API, 2026-09-25) found nothing after Pilatte 2604.26564 on local Fourier
  uniformity, and no three-point trivial-product log Elliott result. Recent "Chowla" titles
  through 2609 are two-point or averaged variants: 2608.23500, 2609.28526, 2608.16108,
  2609.14492.
