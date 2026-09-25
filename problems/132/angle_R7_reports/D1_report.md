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

## 4. Global ownership: sector frames, the deep zone, random cuts

This section builds one ownership (in the sense of Lemma E, §1) of all edges incident to 𝓡. Every point of 𝓡 outside an
exceptional set Exc owns only edges pointing into a half-open half-plane of directions, as seen in a frame that is within θ of its
boundary normal. It then bounds |Exc| by ηr + C. The design differs from D1's scripts in one respect beyond the three repairs of §7.
The sectors are cut in the **Gauss map** (by the direction of the boundary normal), not by arc length. This makes the corners of K
harmless: the cost of the boundary turning (total 2π) is O(1), independent of n (§4.5).

### 4.1 Parameters

Fix η ∈ (0,1] and κ > 0. Put:
- a := min{κ/8, 10⁻²};
- ε₀ := a, ε := tan ε₀;
- Λ := 231;
- N_s := ⌈π/a⌉, θ_s := 2π/N_s ≤ 2a (the sector width), θ := θ_s/2 ≤ a;
- M := ⌈36/η⌉, ℓ := 2M + 3, Λ₁ := 116ℓ;
- Δ₂* := max{10⁴, 5/κ, 100ℓ}.

Then:
- Λ ≥ 100;
- Λ(1 − cos ε₀) ≤ 231·(1 − cos 10⁻²) < 0.012 < 1;
- ρ = 1 ≤ Λ/2.

So the frame lemma (paper Lemma 9.2) and Lemma DN (paper Lemma 9.3) apply at good points. Lemma S applies with this θ and ε₀, since
max(θ, ε₀) = a ≤ 10⁻².

**Lemma 4.0 (size of κ(θ)).** For a := max(θ, ε₀) ≤ 10⁻² and Δ₂ ≥ 10⁴, **κ(θ) ≤ 1.51a + 3.01ε₀ + 2/Δ₂**. With the parameters above,
κ(θ) ≤ 4.52a + 2/Δ₂ ≤ 0.565κ + 0.4κ < κ whenever Δ₂ ≥ Δ₂*.

*Proof.* Upper end:
- t_hi − √3/2 = [cos(30° − a) − cos 30°] + tan ε₀ + 2 sin ε₀ + 2/Δ₂;
- cos(30° − a) − cos 30° = cos 30°(cos a − 1) + ½ sin a ≤ a/2;
- tan ε₀ ≤ 1.0001ε₀ and sin ε₀ ≤ ε₀ for ε₀ ≤ 10⁻².

So t_hi − √3/2 ≤ a/2 + 3.0001ε₀ + 2/Δ₂.

Lower end:
- L_c = (√3/2)cos a − (3/2)sin a ≥ √3/2 − (√3/4)a² − 1.5a;
- since 0 < L_c ≤ 1, L_c cos ε₀ ≥ L_c − ε₀²/2.

So √3/2 − t_lo ≤ 1.5a + 0.434a² + 0.5ε₀² + 2ε₀ + 1/(2Δ₂) ≤ 1.51a + 3.01ε₀ + 1/(2Δ₂), using a, ε₀ ≤ 10⁻². ∎
(At D1's parameters θ = 10⁻³, ε₀ = 10⁻⁶ the bound gives 1.71·10⁻³, against the exact interval value 1.553·10⁻³ of §3. The script
`r7_D1r_global.py` Part B compares the bound with the interval value on a grid.)

### 4.2 Zones, frames and the ownership rule

All objects below are defined for y ∈ 𝓡∖D ⊂ int K (Fact 1.1).
- **Foot and normal.** h(y) = dist(y, ∂K) > 0. Fix a nearest point p₀(y) ∈ ∂K and put ν(y) := (p₀(y) − y)/h(y). The disc D(y, h(y)) lies in
  K and touches ∂K at p₀(y). Every supporting line of K at p₀ therefore supports this disc at p₀. So K has the **unique** outer normal ν(y) at
  p₀(y) (p₀ is a smooth point), and ν(y) is the vector n₀ of the frame lemma at y.
- **Lipschitz.** h(y) = dist(y, ℝ²∖int K) is 1-Lipschitz, so |h(y) − h(u)| ≤ 1 for every edge yu.
- **Random choices.** φ₀ is uniform in [0, θ_s) and T is uniform in [1, 1 + M], independently.
- **Zones.**
  - y is *deep* if h(y) > T and *shallow* if h(y) ≤ T.
  - The deep zone has the single frame e := (0, 1), a fixed direction.
  - A shallow y lies in sector j(y) ∈ {0, …, N_s − 1}, defined by ν(y) ∈ I_j := [φ₀ + jθ_s, φ₀ + (j+1)θ_s) (angles mod 2π). The frame of
    sector j is n_j := the unit vector at angle φ₀ + (j + ½)θ_s.
  - Hence **∠(n_{j(y)}, ν(y)) ≤ θ_s/2 = θ for every shallow y.** Every point with h ≤ 1 is shallow, since T ≥ 1.
  - The *zone* of y is "deep" or "sector j(y)"; its *frame* n(y) is e or n_{j(y)}.
- **Upward.** For a unit vector n, write n^⊥ for n rotated by −90°. Call a vector w ≠ 0 *n-upward* if w·n > 0, or if w·n = 0 and w·n^⊥ > 0.
  Exactly one of w and −w is n-upward.

**Definition 4.1 (ownership).** Every unit edge with at least one end in 𝓡 falls under exactly one of the following rules.
- (O1) *Spoke:* y ∈ 𝓡, q ∈ S. Owned by y, its only 𝓡-end.
- (O2) *D-edge:* at least one end is in 𝓡∩D. Owned by an 𝓡∩D end (if both ends are in 𝓡∩D, by the lexicographically smaller one).
- (O3) *Zone edge:* y, u ∈ 𝓡∖D in the same zone, with frame n. Owned by y iff u − y is n-upward (otherwise by u).
- (O4) *Crossing edge:* y, u ∈ 𝓡∖D in different zones (deep/shallow, or two different sectors). Owned by the lexicographically smaller end.
  **Both ends are put in Exc_cr.**

The cases are disjoint and exhaustive: an edge with an 𝓡-end has its other end in S, in 𝓡∩D or in 𝓡∖D. Exactly one end owns each edge;
for (O3) this is because exactly one of u − y and y − u is n-upward. Hence E_𝓡 = Σ_{y∈𝓡} own(y).

**Exceptional set.**
- Exc_ng := the points y ∈ 𝓡∖D with h(y) ≤ 1 that are not good (§3; with Λ = 231, ρ = 1).
- Exc_thin := 𝓡∖D if K is *ℓ-thin*, i.e. if there are p, b ∈ ∂K with |pb| ≤ ℓ such that both arcs of ∂K between p and b are longer
  than Λ₁. Otherwise Exc_thin := ∅.
- Exc := Exc_ng ∪ Exc_cr ∪ Exc_thin.

### 4.3 The half-open half-plane condition off Exc

**Proposition 4.2.** Let y ∈ 𝓡∖Exc.
- (a) If y ∈ 𝓡∩D, then own(y) ≤ deg y ≤ 3 (Fact 1.3).
- (b) If y ∈ 𝓡∖D and h(y) > 1, then every edge at y is a zone edge (O3), and own(y) ≤ 3.
- (c) If y ∈ 𝓡∖D and h(y) ≤ 1, then own(y) = |O_n(y)| with n = n_{j(y)} and ∠(n, n₀(y)) ≤ θ. Hence own(y) ≤ 4, and **own(y) ≤ 3 if
  |t − √3/2| > κ(θ)** (Lemma S). If own(y) = 4, then y has S∩D-neighbours within a of ±30° and a K-neighbour within a of +90° or −90°.

*Proof.*
(a) y owns at most all its edges, and deg y ≤ 3 by Fact 1.3.

(b) By Fact 1.4 every neighbour of y lies in int K. Points of X in int K are in 𝓡∖D, because S∖D ⊂ ∂K and D ∩ K = ∅. So there are no spokes
and no D-edges at y. Since y ∉ Exc_cr, there are no crossing edges either, so every edge at y is (O3) in y's zone frame n(y). The owned
neighbours u have u − y n(y)-upward. The n-upward unit vectors form a half-open semicircle, so Lemma O gives own(y) ≤ 3.

(c) Since y ∉ Exc_ng, y is good. Since h ≤ 1 ≤ T, y is shallow with frame n = n_{j(y)}, and ∠(n, ν(y)) ≤ θ with ν(y) = n₀(y). Since
y ∉ Exc_cr, all 𝓡∖D-neighbours of y are in y's sector. y owns:
- all its S-neighbours (O1);
- none of its 𝓡∩D-neighbours (O2);
- exactly the 𝓡∖D-neighbours u with u − y n-upward (O3).

This is the set O_n(y) of §3. Lemma S(1)–(3) gives the rest. ∎

(The condition "∠(n, n₀) ≤ θ" of Lemma S is used only at points with h ≤ 1. Deep points and shallow points with h > 1 need no condition on
their frame, only that their neighbours use the same one.)

### 4.4 Counting Exc

**Lemma 4.3 (non-good points).** Assume Δ₂ ≥ 10⁴. Then |Exc_ng| ≤ N_ng := 463² + 2π·465²/ε₀ + 7600. The bound does not depend on the
weights v (this resolves D1 flag 2, §8).

*Proof.* This is paper Lemma 9.4 (lem:fewbad) with Λ = 231, ρ = 1. A point y ∈ 𝓡∖D with h ≤ 1 fails to be good for one of three reasons.
- (i) perimeter(K) ≤ 2Λ = 462. Then diam K ≤ 231, and the 1-separated set X∖D ⊂ K has at most (2·231 + 1)² = 463² points.
- (ii) turn(γ^Λ_y) > ε₀. Paper §9.1 (the proof of Lemma 8.5 with 232 replaced by Λ) bounds the number of such y by 2π(2Λ + 3)²/ε₀.
- (iii) Some b ∈ ∂K ∩ D(y, 1) is not on γ^Λ_y. Then |p₀b| ≤ 2 and both arcs from p₀ to b are longer than Λ = 231 > 115·2. Paper
  Lemma 9.1 (lem:Tstar) with ℓ = 2 ≤ Δ₂/100 gives |X∖D| < (501)(11.8)(4/π) < 7528.

None of the three cases uses v(y). ∎

**Lemma 4.4 (the deep/shallow interface).** For every fixed φ₀, the expected number (over T) of crossing edges with one deep and one shallow
end is at most e(𝓡∖D)/M ≤ 3r/M.

*Proof.* An edge yu inside 𝓡∖D, with h(y) ≤ h(u), is deep/shallow iff T ∈ [h(y), h(u)). This has probability ≤ (h(u) − h(y))/M ≤ 1/M,
because T has density 1/M and h is 1-Lipschitz. Also e(𝓡∖D) ≤ 3|𝓡∖D| ≤ 3r, since degrees are ≤ 6. ∎

The level curve {h = T} with a **fixed** T could carry Θ(r) crossing edges: put almost all of 𝓡 in a band of width 2 around depth T.
Randomising T is what makes the interface cost ≤ 3r/M. (This is repair 2, §7.)

**Lemma 4.5 (seams).** Suppose K is not ℓ-thin, and fix T ∈ [1, 1 + M]. For every edge yu with y, u ∈ 𝓡∖D shallow, let γ_{yu} be a
shortest arc of ∂K from p₀(y) to p₀(u). Then:
1. length(γ_{yu}) ≤ Λ₁, and ∠(ν(y), ν(u)) ≤ turn(γ_{yu});
2. Σ_{yu} ∠(ν(y), ν(u)) ≤ 2π·M_seam, where M_seam := 6(2Λ₁ + 2M + 3)²;
3. over φ₀, the expected number of edges yu whose ends lie in different sectors is ≤ 2πM_seam/θ_s.

*Proof.*
(1) |p₀(y) − p₀(u)| ≤ h(y) + 1 + h(u) ≤ 2T + 1 ≤ ℓ. If both arcs between the feet were longer than Λ₁, K would be ℓ-thin. So the shorter
arc has length ≤ Λ₁ (if the feet coincide, γ_{yu} is a point). The normal image N(γ_{yu}) ⊂ S¹ is a connected arc of length turn(γ_{yu}).
It contains ν(y) and ν(u), the (unique) outer normals at the end points. So the angular distance between them is ≤ turn(γ_{yu}).

(2) If b ∈ γ_{yu}, then |b − y| ≤ |b − p₀(y)| + h(y) ≤ Λ₁ + T, because a chord is at most the arc. The discs of radius ½ about the points
of X within Λ₁ + T of b are disjoint and lie in D(b, Λ₁ + T + ½). So there are at most (2Λ₁ + 2T + 1)² ≤ (2Λ₁ + 2M + 3)² such points,
and at most 6 times as many edges have an end among them. Hence every b ∈ ∂K lies on at most M_seam of the arcs γ_{yu}. Paper Lemma 2.4
(multiplicity) gives Σ turn(γ_{yu}) ≤ 2πM_seam, and (1) finishes the proof.

(3) The cut set {φ₀ + jθ_s} is a uniformly random translate of the lattice θ_sℤ/2πℤ. Two directions at angular distance α lie in different
sectors only if a cut point lies in the short arc between them. The expected number of cut points in an arc of length α is exactly α/θ_s,
so by Markov the probability is ≤ α/θ_s. Now sum over edges and use (2). ∎

**Lemma 4.6 (thin K).** If K is ℓ-thin, then |Exc_thin| ≤ |X∖D| < N_thin := (250ℓ + 1)(5.4ℓ + 1)·4/π.

*Proof.* Apply paper Lemma 9.1 with this ℓ and Λ₁ > 115ℓ, using 1 ≤ ℓ ≤ Δ₂/100 since Δ₂ ≥ Δ₂*. ∎

### 4.5 Why corners and curvature cost O(1): the sanity check

**Flat hexagon.** Take the triangular lattice hexagon H_k of side k. It is a toy, not a configuration: S is the 6k boundary points and 𝓡
the 3k² − 3k + 1 interior points. Then E_𝓡 = 9k² − 3k, so **E_𝓡 = 3r + 6k − 3** and Σ_𝓡 v = 6r + 12k − 6. For a band of the k rows next to
the boundary of a larger hexagon, E_𝓡 − 3r = 6k exactly. Both are checked in exact integer arithmetic for sides up to 24 in
`r7_D1r_global.py` Part A.

The excess is **not** a local defect. Every interior point has own ≤ 3 in a frame normal to its nearest side, as in Theorem F. The
excess comes from the global impossibility of one consistent frame:
- The six sides need six frames, 60° apart. Along each corner bisector (a *seam* of length ≍ k) the frame jumps by 60°, and the Θ(k) edges
  crossing the seams cannot all be owned by an end with a compatible frame.
- Equivalently, Theorem F's "bottom deficit" of a flat strip, where the lowest row has degree 4, never occurs: the six strips meet in the
  centre.

So E_𝓡 − 3r = Θ(k) = Θ(√r). This is o(r), but it is **not** O(1), and any valid scheme must pay for it. The question the coordinator
raised is whether a real K could force Θ(r).

**How the proof pays, quantitatively.** In Theorem G the geometry of K enters only through three counts. For each, the table gives the
bound and what it is for H_k and for a real ball polygon (arcs of radius Δ₂, total turning 2π).

| cost | bound | H_k (toy) | real K |
|---|---|---|---|
| non-good points (h ≤ 1, turning > ε₀ near the foot) | N_ng ≤ 463² + 2π·465²/ε₀ + 7600 (Lemma 4.3) | ≍ Λ per corner | O(1/ε₀): only total turning 2π is used |
| seams: shallow edges in different Gauss sectors | E ≤ 2πM_seam/θ_s = O(M²/θ_s) (Lemma 4.5) | ≍ T per corner (seams cut off at depth T) | O(M²/θ_s), independent of n and of Δ₂ |
| interface {h = T} | E ≤ 3r/M (Lemma 4.4) | ≍ 6k (length of the level hexagon), averaged over T | ≤ 3r/M, using only that h is 1-Lipschitz |

So the seams do **not** cost "turning × depth of K". The deep zone has one global frame, so a seam only runs to depth T ≤ M + 1. The
**sum of the turning over all seams is 2π, however many corners K has** (Lemma 4.5(2) is the multiplicity lemma, the same tool as paper
Lemma 8.5). The remaining cost moves to the level curve {h = T}, and randomising T in a window of width M makes it ≤ 3r/M.

For H_k this gives: E_𝓡 − 3r ≤ 18r/M + O(M²/θ_s) + O(Λ²/ε₀). That is consistent with the true value 6k − 3 ≍ √r, and at best
M ≍ r^{1/3} it gives O(r^{2/3}).

In short, the flat-hexagon excess is paid by the interface, not by the corners. Curvature (arcs of radius Δ₂) plays no role in the count
except through "total turning 2π" and "turning ≤ ε₀ over arcs of length 2Λ at good points". The random-configuration test on curved ball
polygons (Part C of `r7_D1r_global.py`) measures the three costs directly; see §4.6.
