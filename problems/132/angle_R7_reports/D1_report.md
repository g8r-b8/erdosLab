# D1r report: reconstruction and repair of Theorem G (average R-weight at most 6 off the fan zone)

Branch D1r of angle R7 (Erdős #132 / CDL Problem 1.6), 2026-09-25. It reconstructs branch D1, whose full report was lost in the
scratchpad wipe. Sources: angle_R7.md §5, D1_excerpt.md (§0–§1), the scripts `r7_D1_*.py` and paper v3 (`paper/paper.tex`).
New scripts: `scripts/r7_D1r_lemmaS.py` and `scripts/r7_D1r_global.py`.

STATUS: IN PROGRESS (written incrementally)

## 0. Summary of what is proved here

- **Theorem G (proved below, unrefereed).** Work in the nondegenerate regime. For every η > 0 and every κ > 0 there are
  constants Δ₀(η,κ) and C(η,κ) with the following property. If |t − √3/2| ≥ κ, then Σ_{y∈𝓡} v(y) ≤ (6 + η)|𝓡| + C(η,κ)
  (and trivially ≤ 6r + ηn + C). D1's statement with κ = κ₁ = 2.1·10⁻³ is the special case θ_s = 10⁻³, ε₀ = 10⁻⁶.
  The rigorous value at those parameters (Δ₂ ≥ 10⁴) is κ₁ < 1.56·10⁻³ (`r7_D1r_lemmaS.py`).
- **Corollary 6.1 (proved).** For all t: Σ_𝓡 v ≤ 6r + 2|F*| + ηr + C_η. Here F* is the set of good points y (depth ≤ 1) that have
  S∩D-neighbours near both ±30° and a K-neighbour near +90° or −90°. At such a point own(y) = 4 exactly.
- The proof below is new in its details. It follows D1's design: orientation, Lemma O, sector frames and random cuts. It differs from
  D1's scripts in three repairs, listed in §7:
  1. Edges at 𝓡∩D points are owned by the 𝓡∩D end.
  2. The deep zone gets its own global frame, with a random depth threshold.
  3. Lemma S is proved directly from the frame lemma, (G5) and Lemma DN, without P4's δ₀-flat model.
- All three D1 referee flags are resolved (§8).

## 1. Set-up, exact facts, and the bookkeeping lemma

Notation follows paper v3 §2 and §7:
- δ = 1, R = Δ₂, Δ = Δ₂ + t, K = ∩_{w∈X} D(w, Δ₂);
- D = endpoints of diametral pairs, S = points with a Δ₂-partner, 𝓡 = X∖S, r = |𝓡|;
- v(y) = deg y + m_y, where m_y = #neighbours in S;
- d(y) = dist(y, ∂K) for y ∈ K (the *depth*), and h = d(y) in the paper's notation.

We work in the nondegenerate regime Δ ≤ 1.94Δ₂. In the degenerate regime, min ≤ n + 1 (paper Prop. 8.1).

**Fact 1.1** (paper Lemma 2.1 and §7(b)):
- X∖D ⊂ K;
- S∖D ⊂ ∂K and 𝓡∖D ⊂ int K;
- dist(z, K) ≥ t for z ∈ D.

Every neighbour of a point of X therefore lies in int K (and then in 𝓡∖D), in S∖D ⊂ ∂K, or in D (disjoint from K).

**Fact 1.2 (exact).** Σ_{y∈𝓡} v(y) = 2E_𝓡, where E_𝓡 is the number of unit edges with at least one end in 𝓡.
Proof: an 𝓡–𝓡 edge contributes 1 to deg at each end. An 𝓡–S edge contributes 1 to deg and 1 to m at its 𝓡-end.

**Fact 1.3** (paper §7(a)). A point z ∈ D has deg z ≤ 3. This is because X∖{z} lies in an open half-plane bounded by a line through z.

**Fact 1.4** (paper §7(c)). If y ∈ 𝓡∖D has d(y) > 1, then every neighbour of y lies in int K. In particular y has no neighbour in S and none in D.
Proof: if q ∉ int K, the segment [y,q] meets ∂K, so d(y) ≤ 1.

**Separation.** Distinct neighbours of any point are at least 60° apart as seen from it, since |q − q'| ≥ 1 = |q − y| = |q' − y|.

**Lemma O.** If U is a set of neighbours of y whose directions lie in a half-open arc of length π, then |U| ≤ 3.
Proof: four such directions, sorted, would have span at least 3·60° = 180° inside a half-open arc of length 180°. That is impossible.

**Ownership and Lemma E (bookkeeping).** An *ownership* assigns each edge with an end in 𝓡 to exactly one of its 𝓡-ends. Then
E_𝓡 = Σ_{y∈𝓡} own(y). Let Exc ⊂ 𝓡 be any set with own(y) ≤ 3 for y ∉ Exc. Since own(y) ≤ deg y ≤ 6,
E_𝓡 ≤ 3r + 3|Exc|, and so **Σ_𝓡 v ≤ 6r + 6|Exc|**.

## 2. Theorem F (flat model): exactly Σv ≤ 6r

*Flat model* (an idealisation, not a configuration):
- ∂K is the line z = 0 and K lies below it;
- points of S∖D are on z = 0;
- points of D (in S or in 𝓡) are at z ≥ t > 0;
- points of 𝓡∖D are at z < 0.

*Ownership.* An edge with an end in 𝓡∩D is owned by that end (by either end if both qualify). A spoke y–q with y ∈ 𝓡∖D and
q ∈ S is owned by y. An edge between two points of 𝓡∖D is owned by the lower end; if the heights are equal, it is owned by the end that sees the other on its right.

**Theorem F.** In the flat model own(y) ≤ 3 for every y ∈ 𝓡, so Σ_𝓡 v ≤ 6r exactly, for every t > 0.

*Proof.* If y ∈ 𝓡∩D, then own(y) ≤ deg y ≤ 3 by Fact 1.3. If y ∈ 𝓡∖D, it sits at height −h < 0. Every S-neighbour sits at height ≥ 0 > −h, so it is strictly
higher. An 𝓡∖D-neighbour owned by y is higher, or at equal height and to the right. So all owned directions lie in the half-open
half-plane {Δz > 0} ∪ {Δz = 0, Δx > 0}, and Lemma O gives own(y) ≤ 3. ∎

The bound is tight on B1's A-row stack E1 and on the cap lattice E2: both have average weight exactly 6 (`r7_D1_flat_orient.py`, rerun below).
There, radius-1 discharging is stuck at 7 (paper Remark 10.1(a)).

*Why fans are the only obstruction.* In the real geometry, ∂K near y is a concave graph with |f| ≤ ε|x|. So a K-neighbour has
c = cos ψ ∈ [h − ε, h] rather than c = h. When h ≤ ε, a K-neighbour can sit slightly *below* the horizontal (|ψ| up to 90° + ε₀).
Together with S∩D-neighbours at ±30°, this makes the fan configuration with four S-neighbours. The flat_orient stress test
reproduces exactly this. Lemma S below shows that it is the only way to exceed 3, and that it pins t to √3/2.

## 3. Lemma S (tilted frames): exact statement and proof

**Standing parameters.**
- 0 < ε₀ ≤ 1/50 and ε = tan ε₀;
- Λ ≥ 100 with Λ(1 − cos ε₀) < 1, and ρ = 1;
- Δ₂ ≥ 10⁴.

A point y ∈ 𝓡∖D with h = d(y) ≤ 1 is **good** if all of the following hold:
- perimeter(K) > 2Λ;
- turn(γ^Λ_y) ≤ ε₀;
- ∂K ∩ D(y,1) ⊂ γ^Λ_y.

Then the frame lemma (paper Lemma 9.2, properties G1–G5, with ρ = 1) and Lemma DN (paper Lemma 9.3, with ξ = ζ = 1) apply at y.
Use y's frame: origin p₀ (the nearest boundary point), axes t₀ and n₀, so y = (0, −h). Write a neighbour as q = y + (sin ψ, cos ψ) and
c(q) = cos ψ. By G1–G4 every neighbour is one of three kinds:
- a **K-neighbour** (S∖D): c ∈ [h − ε|sin ψ|, h];
- a **D-neighbour** (in S or 𝓡): c ≥ h + t − ε;
- an **interior** neighbour (𝓡∖D): c < h.

Every non-interior neighbour has |ψ| < 90° + ε₀ (G1, as in F1).

**Definition.** For a unit vector n, let O_n(y) be the set of S-neighbours of y together with the 𝓡∖D-neighbours u such that
(u − y)·n > 0, or (u − y)·n = 0 and (u − y)·n^⊥ > 0. This is exactly the set of edges y owns under the ownership of §4 when y is not
exceptional and its sector frame is n. (𝓡∩D-neighbours are never in O_n(y): those edges belong to the 𝓡∩D end.)

**Lemma S.** Let y be good, and let n be a unit vector with ∠(n, n₀) ≤ θ. Put a := max(θ, ε₀) and assume a ≤ 10⁻².
1. |O_n(y)| ≤ 4.
2. If |O_n(y)| = 4, the four directions are within a of −90°, −30°, 30°, 90°. One of the two extreme ones is a K-neighbour, and
   both middle ones are S∩D-neighbours.
3. If |O_n(y)| = 4, then t ∈ [t_lo, t_hi], where
   - L_c := cos(30° + a) − sin a,
   - U_c := cos(30° − a) + ε,
   - t_lo := L_c cos ε₀ − 2 sin ε₀ − 1/(2Δ₂),
   - t_hi := U_c + 2 sin ε₀ + 2/Δ₂.
   
   Hence **|O_n(y)| ≤ 3 whenever |t − √3/2| > κ(θ) := max{√3/2 − t_lo, t_hi − √3/2}**.

For D1's parameters (θ = 10⁻³, ε₀ = 10⁻⁶, Λ = 10⁹, Δ₂ ≥ 10⁴), `r7_D1r_lemmaS.py` gives in 60-digit interval arithmetic
t ∈ [0.8644729, 0.8667280] and **κ₁ = κ(10⁻³) < 1.553·10⁻³ < 2.1·10⁻³**. So D1's κ₁ is correct, with room to spare.
In general κ(θ) ≈ 1.5θ + 3ε₀ + O(1/Δ₂), so κ(θ) → 0 as θ, ε₀ → 0 and Δ₂ → ∞.

*Proof.*
(a) *Directions.*
- S-neighbours have |ψ| < 90° + ε₀.
- An 𝓡∖D-neighbour u ∈ O_n(y) has ψ − α in a half-open arc of length 180° centred at 0, where α is the signed angle from n₀ to n
  and |α| ≤ θ. (Here (u − y)·n = cos(ψ − α), and the tie rule keeps exactly one of ψ − α = ±90°.)

So every direction in O_n(y) lies in [−90° − a, 90° + a], an arc of length 180° + 2a < 240°. By separation this arc holds at most 4
points, which proves (1). Suppose |O_n(y)| = 4 with directions ψ₁ < ψ₂ < ψ₃ < ψ₄. Consecutive gaps are ≥ 60°, so ψ₄ − ψ₁ ≥ 180°.
This forces:
- ψ₁ ∈ (−90° − a, −90° + a] and ψ₄ ∈ [90° − a, 90° + a];
- ψ₂ ∈ [ψ₁ + 60°, ψ₄ − 120°] ⊂ [−30° − a, −30° + a], and similarly ψ₃ ∈ [30° − a, 30° + a].

(b) *Some extreme is in S.* Suppose both extremes were 𝓡∖D-neighbours. Then ψ₁ − α and ψ₄ − α would lie in one half-open arc of
length 180°, so ψ₄ − ψ₁ < 180°. That is a contradiction. So let e ∈ {ψ₁, ψ₄} be an S-neighbour. Since |ψ_e| ≥ 90° − a, we have c_e ≤ sin a.

(c) *e is not a D-neighbour, and the middles are S∩D.* We have c_e ≥ h − ε if e is a K-neighbour, and c_e ≥ h + t − ε if e is a D-neighbour.
Either way h ≤ sin a + ε. Each middle neighbour m has c_m ≥ cos(30° + a) > sin a + ε ≥ h. So m is neither interior (that needs c < h)
nor a K-neighbour (that needs c ≤ h), and m is a D-neighbour. Since m ∈ O_n(y) and m ∉ 𝓡∖D, we get m ∈ S∩D.

Now suppose e were a D-neighbour. Then e and m would be two points of D ∩ D(y,1) whose levels (c − h) differ by c_m − c_e ≥ L_c.
Lemma DN (ξ = ζ = 1) bounds that difference by κ_D|Δx| ≤ 2κ_D, with κ_D = ((Λ − 1)ε + 1)/(Λ − 2). But L_c > 2κ_D (check (S2); it holds even
in the worst case Λ = 100, ε₀ = θ = 1/50, where 0.0608 < 0.8359). This is a contradiction, so e is a K-neighbour. This proves (2).

(d) *Pinning.* Let k := e (a K-neighbour) and z := m ∈ S∩D.
- In y's frame, z − k = (Δx, Δc) with |Δx| ≤ 2 and Δc = c_m − c_e ∈ [L_c, U_c]. (Use c_m ∈ [cos(30° + a), cos(30° − a)] and c_e ∈ [−ε, sin a],
  the latter because c_e ≥ h − ε > −ε.)
- Since k ∈ ∂K ∩ D(y,1) ⊂ γ^Λ_y, property G5 shows that the inward normal u_k = (w_k − k)/Δ₂ equals (sin β', −cos β') with |β'| ≤ ε₀.
- Then (z − k)·u_k = Δx sin β' − Δc cos β' ≤ 2 sin ε₀ − L_c cos ε₀ < 0 (check (S1)). So z is not normal for k, and by paper Lemma 2.2(b) we get
  |z − w_k| = Δ.
- Expanding |z − w_k|² = |z − k|² − 2Δ₂(z − k)·u_k + Δ₂² = (Δ₂ + t)² gives exactly
  t = Δc cos β' − Δx sin β' + (d² − t²)/(2Δ₂), where d = |z − k| ≤ 2.
- Hence t ≤ U_c + 2 sin ε₀ + 2/Δ₂ = t_hi, and t_hi < 1 (check (S3)). With t² < 1 we also get t ≥ L_c cos ε₀ − 2 sin ε₀ − 1/(2Δ₂) = t_lo. ∎

*Remarks.*
- The proof uses only paper v3's frame lemma, (G5), Lemma DN and Lemma 2.2(b), all of them refereed as part of Theorem N3.
  It does **not** use P4's δ₀-flat model. D1's constant κ₁ = a + a₀ + ε + δ₀ (in `r7_D1_tilt.py`) had a δ₀ = 10⁻⁴ term from that model.
  That term is unnecessary, and the resulting κ₁ is smaller.
- Lemma S is sharp in form: exact fans (F6, F5, HF2 with h ≤ ε) realise |O_n(y)| = 4 at t ≈ √3/2. The `r7_D1_tilt.py` screen finds
  212 witnesses, all within 10⁻⁴ of √3/2, and none outside κ.
- The screen of `r7_D1_tilt.py` counts owned 𝓡∩D-neighbours too (kind 'd'). That is a superset of O_n(y), so its passing also covers the
  present rule.
