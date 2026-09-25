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

We work in the nondegenerate regime Δ ≤ 1.94Δ₂. In the degenerate regime, min ≤ n + 1 (paper Prop. 7.1).

**Fact 1.1** (paper Lemma 2.1 and §6.1(b)):
- X∖D ⊂ K;
- S∖D ⊂ ∂K and 𝓡∖D ⊂ int K;
- dist(z, K) ≥ t for z ∈ D.

Every neighbour of a point of X therefore lies in int K (and then in 𝓡∖D), in S∖D ⊂ ∂K, or in D (disjoint from K).

**Fact 1.2 (exact).** Σ_{y∈𝓡} v(y) = 2E_𝓡, where E_𝓡 is the number of unit edges with at least one end in 𝓡.
Proof: an 𝓡–𝓡 edge contributes 1 to deg at each end. An 𝓡–S edge contributes 1 to deg and 1 to m at its 𝓡-end.

**Fact 1.3** (paper §6.1(a)). A point z ∈ D has deg z ≤ 3. This is because X∖{z} lies in an open half-plane bounded by a line through z.

**Fact 1.4** (paper §6.1(c)). If y ∈ 𝓡∖D has d(y) > 1, then every neighbour of y lies in int K. In particular y has no neighbour in S and none in D.
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

Then the frame lemma (paper Lemma 9.3, properties G1–G5, with ρ = 1) and Lemma DN (paper Lemma 9.4, with ξ = ζ = 1) apply at y.
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

So the frame lemma (paper Lemma 9.3) and Lemma DN (paper Lemma 9.4) apply at good points. Lemma S applies with this θ and ε₀, since
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

*Proof.* This is paper Lemma 9.5 (lem:fewbad) with Λ = 231, ρ = 1. A point y ∈ 𝓡∖D with h ≤ 1 fails to be good for one of three reasons.
- (i) perimeter(K) ≤ 2Λ = 462. Then diam K ≤ 231, and the 1-separated set X∖D ⊂ K has at most (2·231 + 1)² = 463² points.
- (ii) turn(γ^Λ_y) > ε₀. Paper §9.1 (the variant of Lemma 6.4 stated after Lemma 9.2, with 232 replaced by Λ) bounds the number of such y by 2π(2Λ + 3)²/ε₀.
- (iii) Some b ∈ ∂K ∩ D(y, 1) is not on γ^Λ_y. Then |p₀b| ≤ 2 and both arcs from p₀ to b are longer than Λ = 231 > 115·2. Paper
  Lemma 9.2 (lem:Tstar) with ℓ = 2 ≤ Δ₂/100 gives |X∖D| < (501)(11.8)(4/π) < 7528.

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
and at most 6 times as many edges have an end among them. Hence every b ∈ ∂K lies on at most M_seam of the arcs γ_{yu}. Paper Lemma 2.5
(multiplicity) gives Σ turn(γ_{yu}) ≤ 2πM_seam, and (1) finishes the proof.

(3) The cut set {φ₀ + jθ_s} is a uniformly random translate of the lattice θ_sℤ/2πℤ. Two directions at angular distance α lie in different
sectors only if a cut point lies in the short arc between them. The expected number of cut points in an arc of length α is exactly α/θ_s,
so by Markov the probability is ≤ α/θ_s. Now sum over edges and use (2). ∎

**Lemma 4.6 (thin K).** If K is ℓ-thin, then |Exc_thin| ≤ |X∖D| < N_thin := (250ℓ + 1)(5.4ℓ + 1)·4/π.

*Proof.* Apply paper Lemma 9.2 (lem:Tstar) with this ℓ and Λ₁ > 115ℓ, using 1 ≤ ℓ ≤ Δ₂/100 since Δ₂ ≥ Δ₂*. ∎

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
Lemma 6.4). The remaining cost moves to the level curve {h = T}, and randomising T in a window of width M makes it ≤ 3r/M.

For H_k this gives: E_𝓡 − 3r ≤ 18r/M + O(M²/θ_s) + O(Λ²/ε₀). That is consistent with the true value 6k − 3 ≍ √r, and at best
M ≍ r^{1/3} it gives O(r^{2/3}).

In short, the flat-hexagon excess is paid by the interface, not by the corners. Curvature (arcs of radius Δ₂) plays no role in the count
except through "total turning 2π" and "turning ≤ ε₀ over arcs of length 2Λ at good points". The random-configuration test on curved ball
polygons (Part C of `r7_D1r_global.py`) measures the three costs directly; see §4.6.

### 4.6 The random-configuration test (`r7_D1r_global.py` Part C)

The test uses toy "curved K": K = ∩ D(c_i, R) with 3–40 arcs, R between 10² and 10⁷ (R = 10⁷ is a flat hexagon-like polygon), and
inradius scale w up to 48. It is filled with a randomly rotated, randomly thinned triangular lattice (exact unit adjacency):
- 𝓡 = the lattice points in int K;
- toy S = the lattice points in a band of width 1.2 just outside int K;
- there is no D, and t plays no role.

The rule of §4.2 is applied with random (φ₀, T). The test checks:
- each edge incident to 𝓡 is owned exactly once, and Σv = 2E_𝓡;
- own ≤ 3 off Exc at h > 1 (Lemma O);
- at toy-good points with h ≤ 1 (foot more than 4 from every corner), own ≤ 4, and own = 4 only in the Lemma S(1)–(2) pattern;
- Σv ≤ 6r + 2#{own = 4} + 6|Exc|.

It also computes, exactly, the three costs of §4.5: the seam measure Σ∠(ν(y), ν(u)), E_{φ₀}[#sector crossings] and E_T[#deep crossings].
Results are in §5.4.

## 5. Theorem G assembled

**Theorem G.** Assume the nondegenerate regime Δ ≤ 1.94Δ₂. For every η ∈ (0,1] and κ > 0, every X with |t − √3/2| ≥ κ satisfies

  Σ_{y∈𝓡} v(y) ≤ (6 + η)·r + C(η,κ),   with C(η,κ) := max{6N_ng + 24πM_seam/θ_s, 6N_thin, 6(3.88Δ₂* + 1)²},

where the constants are those of §4.1 and §4.4.

*Proof.*
1. *Small Δ₂.* If Δ₂ < Δ₂*, then diam X = Δ ≤ 1.94Δ₂, and the discs of radius ½ about the points of X are disjoint and lie in a disc of
   radius Δ + ½. So n ≤ (2Δ + 1)² ≤ (3.88Δ₂* + 1)². Since v ≤ 12 (paper Lemma 3.3), Σv ≤ 12r ≤ 6r + 6n.
2. *Thin K.* If K is ℓ-thin, then Exc ⊇ 𝓡∖D. Points of 𝓡∩D own ≤ 3 edges (Proposition 4.2(a)), and |𝓡∖D| < N_thin (Lemma 4.6).
   Lemma E gives Σv ≤ 6r + 6N_thin.
3. *General case.* Now Δ₂ ≥ Δ₂* and K is not ℓ-thin.
   - Averaging over (φ₀, T), Lemmas 4.4 and 4.5 give E|Exc_cr| ≤ 2(3r/M) + 2(2πM_seam/θ_s). Fix a pair (φ₀, T) at which
     |Exc_cr| is at most its mean.
   - By Lemma 4.0 (Δ₂ ≥ Δ₂*), κ(θ) < κ ≤ |t − √3/2|. So Proposition 4.2 gives own(y) ≤ 3 for every y ∉ Exc.
   - Lemma E (§1) and Lemma 4.3 then give
     Σv ≤ 6r + 6|Exc| ≤ 6r + 6N_ng + 36r/M + 24πM_seam/θ_s ≤ (6 + η)r + C(η,κ), since M ≥ 36/η. ∎

Sample values of the constant: C(0.1, 0.02) < 2.6·10¹⁵ and C(0.01, 10⁻³) < 5.1·10¹⁸ (script Part B3). As functions of the parameters:
- N_ng = O(1/κ);
- M_seam/θ_s = O(M²/θ_s) = O(η⁻²κ⁻¹);
- N_thin = O(η⁻²).

No effort was made to optimise them.

**Remark 5.1 (what is used from paper v3).**
- Lemma 2.1 (ball polygon), Lemma 2.2(b) (exceptions) and Lemma 2.5 (multiplicity);
- §6.1(a)–(c) (structure of R);
- the variant of Lemma 6.4 in §9.1 (big turning), Lemma 9.2 (packing in thin K), Lemma 9.3 (frame, G1–G5) and Lemma 9.4 (DN);
- Lemma 3.3 (v ≤ 12).

All of these are in the part of paper v3 that was refereed with Theorem N3. **Nothing from §10 (P4, the δ₀-flat model) is used, and no
assumption on τ is made.**

**Remark 5.2 (an o(r) form with a rate).** Fix κ, and choose M := ⌈r^{1/3}⌉ instead of ⌈36/η⌉ (T is then uniform in [1, 1 + M]).
- The interface costs ≤ 36r/M ≤ 36r^{2/3}.
- The seams cost 24πM_seam/θ_s = O_κ(M²) = O_κ(r^{2/3}).
- N_thin = O(M²) = O(r^{2/3}).
- If Δ₂ < 100ℓ = O(r^{1/3}), then n = O(r^{2/3}), so r = O(1).

Hence **Σ_{𝓡} v ≤ 6r + O_κ(r^{2/3})** whenever |t − √3/2| ≥ κ. This is the same shape as paper Theorem 12.1 (τ > 1: deficit
2|A| − O(n^{2/3})), and it is not a coincidence. Both are "local orientation + a global interface of size O(n^{2/3})".

**Remark 5.3 (Theorem G does not need Δ₂ ≥ 2·10¹⁵ or Region I).** D1's version inherited the hypotheses of paper §10 through P4's flat
model. The present proof needs only Δ₂ ≥ Δ₂* (small Δ₂ is absorbed into C) and the nondegenerate regime.

### 5.4 Test results (`r7_D1r_global.py`)

Run with `tools/memcap.sh 4000 .venv/bin/python problems/132/scripts/r7_D1r_global.py` (4 s). All assertions pass.
- **Part A (exact).** E_𝓡 − 3r = 6k − 3 for the hexagon of side k ∈ {3, 6, 12, 24}, and = 6k for every band of depth k.
- **Part B (60-digit intervals).**
  - (S1)–(S5) hold at the §4.1 worst case (Λ = 231, a = ε₀ = 10⁻², Δ₂ = 10⁴): 2κ_D < 0.0288 < L_c, and t_hi < 0.902.
  - Lemma 4.0's bound holds on a 7 × 5 × 3 grid of (θ, ε₀, Δ₂); the maximal ratio of κ(θ) to the bound is 0.996.
  - Constants: C(0.1, 0.02) < 2.6·10¹⁵ and C(0.01, 10⁻³) < 5.1·10¹⁸.
- **Part C (curved toy K, θ_s = 2°, M = 6).** 160 ball polygons and 510 random (φ₀, T). No violation of:
  - one owner per edge;
  - Σv = 2E_𝓡;
  - own ≤ 3 off Exc at h > 1;
  - own ≤ 4 and the fan pattern at own = 4 for toy-good h ≤ 1 (10 toy fans occurred, all in the pattern);
  - Σv ≤ 6r + 2#fans + 6|Exc|.

  The costs of §4.5 for families of growing size:

| K | r | Σ_𝓡 v − 6r (true toy excess) | seam measure Σ∠ (T = 3) | E_{φ₀}[#sector crossings] | E_T[#deep crossings] | 3r/M |
|---|---|---|---|---|---|---|
| 3 arcs, R = 400, w = 12/24/48 | 1110 / 4042 / 13041 | 314 / 530 / 1012 | 63.7 / 66.0 / 43.9 | 76 / 133 / 183 | 225 / 454 / 939 | 555 / 2021 / 6521 |
| 6 arcs, R = 10⁷ (flat hexagon-like), w = 12/24/48 | 541 / 2349 / 8205 | 170 / 374 / 678 | 39.2 / 44.4 / 36.1 | 37 / 41 / 34 | 112 / 312 / 618 | 271 / 1175 / 4103 |
| 12 arcs, R = 300; 40 arcs, R = 150 (w = 24) | 1800; 1624 | 322; 292 | 38.6; 34.9 | 123; 196 | 262; 236 | 900; 812 |

What the table shows:
- The **seam measure stays bounded** (25–66) while r grows twelvefold, whether K has 3 sharp corners, 6 corners (flat sides) or 40
  shallow ones. This is Lemma 4.5: it is controlled by the total turning 2π times T, not by the size of K.
- The sector crossings are ≤ Σ∠/θ_s and do not grow with r for the flat polygon. For curved arcs they grow only while the smooth part
  of the turning increases, and they stay below the fixed bound Σ∠/θ_s.
- The deep-interface crossings grow like the perimeter (∝ w, i.e. ∝ √r), well below 3r/M.
- The true toy excess Σv − 6r also grows like the perimeter (≍ √r).
- For thinned lattices (density 0.8–0.9) the toy excess is negative, since missing points lower degrees.

## 6. Corollary 6.1: all t, and the exact cost of each fan type

Fix a₀ ∈ (0, 10⁻²] and use the parameters of §4.1 with a := a₀. The condition Δ₂ ≥ 5/κ is dropped from Δ₂*, and η ∈ (0,1] is arbitrary.

**Definition.** F* = F*(a₀) is the set of good points y ∈ 𝓡∖D (h ≤ 1) that have:
- S∩D-neighbours within a₀ of −30° and of +30°, and
- a K-neighbour within a₀ of +90° or of −90°.

Here ψ is measured from n₀(y) as in §3. Let F*₄ := {y ∈ F*∖Exc : own(y) = 4}.

**Corollary 6.1.** Assume the nondegenerate regime. Then for all t:
1. Σ_{y∈𝓡} v(y) ≤ 6r + 2|F*₄| + ηr + C(η, a₀) ≤ 6r + 2|F*| + ηr + C(η, a₀).
2. **F* ≠ ∅ implies |t − √3/2| ≤ κ(θ) ≤ 1.51a₀ + 3.01a₀ + 2/Δ₂.** So Theorem G is the special case F* = ∅.
3. 2|F*| ≤ 3|S∩D|.

*Proof.*
(1) Run the proof of Theorem G (§5, steps 1–3) without using |t − √3/2| ≥ κ. By Proposition 4.2(c) and Lemma S(2), a point y ∉ Exc
with h ≤ 1 has own(y) ≤ 4, with equality only if its four owned directions are within a of −90°, −30°, 30°, 90°, both middle ones are
S∩D and one extreme one is a K-neighbour. Such a y is in F*. So own(y) ≤ 3 + 1[y ∈ F*₄], and Lemma E becomes
Σv ≤ 6r + 2|F*₄| + 6|Exc|.

(2) Let y ∈ F*. Take its K-neighbour k near ±90° and an S∩D-neighbour z near +30°. Part (d) of the proof of Lemma S uses only these two
points and the bounds
- c(k) ∈ [h − ε, sin a₀] ⊂ [−ε, sin a₀], and
- c(z) ∈ [cos(30° + a₀), cos(30° − a₀)].

So it gives t ∈ [t_lo, t_hi]. The final bound is Lemma 4.0.

(3) Every y ∈ F* has two S∩D-neighbours. Every z ∈ D has deg z ≤ 3 (Fact 1.3), so z is a neighbour of at most 3 points of F*. Double
counting gives the bound. ∎

**The exact cost of each fan type.** Measure cost as the contribution to Σv − 6r, which is 2(own(y) − 3) at a non-exceptional point.
Let y ∉ Exc be good with h ≤ 1, and assume |t − √3/2| ≤ κ(θ) (otherwise every cost below is 0 by Theorem G). Use the types of paper
Lemma 9.7 (F6, F5, HF1, HF2, cap), which were classified there for ε₀ = 1/50. At smaller ε₀ the same types arise with tolerance a.

| type (deg, m) | v | neighbours (ψ from n₀) | owned by y | own(y) | cost |
|---|---|---|---|---|---|
| **F6** (6,4) | 10 | K ±90°, S∩D ±30°, interior ±150° | the 4 S-neighbours; the interior ones have cos(ψ − α) < 0 | 4 | **2** |
| **F5** (5,4) | 9 | K ±90°, S∩D ±30°, one interior in (150° − ε₀, 210° + ε₀) | the 4 S-neighbours | 4 | **2** |
| bare fan (4,4) | 8 | K ±90°, S∩D ±30° | the 4 S-neighbours | 4 | **2** |
| **HF2** (6,3) | 9 | S∩D ±30°, K at +90° (say), 𝓡∖D-neighbour u near −90°, interior ±150° | 3 S-neighbours, plus u iff u − y is n-upward | 3 or 4 | **0 or 2** |
| HF2 relatives (5,3), (4,3) | 8, 7 | as HF2 without one or both of ±150° | as HF2 | 3 or 4 | 0 or 2 |
| **HF1** (6,3) | 9 | K ±90°, S∩D at +30° (say), the neighbour near −30° is in 𝓡∩D | 3 S-neighbours; the 𝓡∩D edge belongs to the D-end (O2) | 3 | **0** |
| **cap** (6,3) | 9 | K ±60°, S∩D at 0°, interior ±120°, 180° | 3 S-neighbours | 3 | **0** (and caps pin t ≈ ½, off the fan zone) |

*Why the entries hold.*
- In F6, F5 and the bare fan, all four S-neighbours are owned (O1). The 4 of Lemma S is attained, and the interior neighbours lie below
  the frame line.
- In HF2, the neighbour u near −90° is not in S (m = 3). It is not in D, since c(u) ≤ sin(a + 2.81°) < h + t − ε. So it is in 𝓡∖D, and
  y owns it iff it is n-upward. This depends on the side on which u sits relative to the tilted frame line; both happen.
- If two HF2 points y, y' are each other's ±90° neighbours (the situation of paper Lemma 9.10(b)), the edge yy' is owned by exactly one
  of them. So **at most one of the pair pays** for it.
- In HF1, the neighbour near −30° has c > h, so it is not interior. It is not in S (m = 3), so it lies in 𝓡∩D, and that edge belongs to
  the D-end.

Summary: **each F6, F5 or bare-fan point costs exactly 2; each HF2-type point costs 2 or 0 (2 iff its horizontal 𝓡∖D-neighbour is
upward in its sector frame); HF1 and caps cost 0.** Compare Theorem N3, where F6 carries 10 − 8 = 2 over 8 and needs two receivers.
In the orientation accounting every fan type costs at most 2 over 6, because its interior neighbours below own their edges to it.

*Consequences for branch E (fan zone).* With φ := |F*₄|/r ≤ 1, the average weight is 2c ≤ 6 + 2φ + η.
- φ ≤ 1 recovers Theorem N3's 8 (up to η).
- Any bound φ ≤ 1 − δ gives c < 4, hence a bound below 4/3 in the fan zone, by Theorem W's LP (§9).
- φ ≤ ½ gives 21/16.

By (3), |F*| ≤ 1.5|S∩D|, so the fan term is controlled by the number of diametral points in S.

## 7. The three repairs, relative to D1 as recoverable

D1's own write-up is lost. What survives is the summary in angle_R7.md §5, the excerpt D1_excerpt.md and the scripts `r7_D1_*.py`. The
repairs below are measured against those. Each one closes a gap that is visible in what survives. I cannot certify that D1's lost text
had these gaps, only that the surviving design does.

**Repair 1: edges at 𝓡∩D points are owned by the 𝓡∩D end (rule O2).**
- *Gap.* D1's rule ("an edge between two 𝓡-points is owned by the lower end in the zone frame") needs both ends to have a zone and a
  frame. A point z ∈ 𝓡∩D lies outside K, at distance ≥ t (Fact 1.1). It has no foot, no depth and no sector, so the rule is undefined
  for edges at z. `r7_D1_global_hex.py` has no D-row, and `r7_D1_tilt.py` simply counts 𝓡∩D-neighbours (kind 'd') as owned by y when
  they are upward.
- *Repair.* z owns all its edges. This is harmless, because own(z) ≤ deg z ≤ 3 by Fact 1.3, so z is never exceptional.
- *Side benefit.* O_n(y) contains no 𝓡∩D-neighbours. So the middle neighbours of a 4-point in Lemma S are in **S**∩D, and the fan set
  F* of Corollary 6.1 shrinks accordingly: HF1 costs 0. The tilt screen counts a superset of O_n(y), so its passing still covers the
  new rule.

**Repair 2: the deep zone gets one global frame, with a random depth threshold T (Lemma 4.4).**
- *Gap.* `r7_D1_global_hex.py` uses a deep zone with a fixed direction, but its threshold D_int is a fixed parameter of each run. The
  surviving summary says "averaging over random cut positions", which refers to the sector cuts.
- For a **fixed** threshold, the edges crossing the level curve {h = D_int} are not o(r) in general: a configuration may put almost all of
  𝓡 in a band of width 2 around that depth.
- *Repair.* Take T uniform in [1, 1 + M]. Since h is 1-Lipschitz, each edge crosses with probability ≤ 1/M, so the interface costs
  ≤ 3r/M.
- Also, the deep zone has **one** frame, not sector frames continued inwards. Continued sectors would have foot maps that are
  discontinuous across the medial axis of K at every depth, and so an unbounded number of seams.

**Repair 3: Lemma S is proved directly from the frame lemma, (G5), Lemma DN and Lemma 2.2(b), without paper §10's δ₀-flat model.**
- *Gap.* D1's κ₁ = a + a₀ + ε + δ₀ (see `r7_D1_tilt.py`, Part 1) uses the flat model of paper Lemma 10.3, with δ₀ = 10⁻⁴ and the
  parameters of §10 (Λ = 10⁹, ρ = 6, good′ points).
- Paper §10 is stated under "τ ≤ √3/2 − 2β or τ > 1, and Δ₂ ≥ 2·10¹⁵". The flat model's proof does not visibly use the τ-hypothesis, but
  as written it is not available in Regions II and III. Theorem G is applied in Region III off the fan zone.
- *Repair.* §3 proves Lemma S from paper Lemmas 9.3 and 9.4 (stated with no τ-hypothesis and Δ₂ ≥ 10⁴) and Lemma 2.2(b). The constant
  improves to κ(10⁻³) < 1.553·10⁻³ at D1's parameters, and κ(θ) ≤ 1.51a + 3.01ε₀ + 2/Δ₂ in general (Lemma 4.0).

**A further change (a simplification, not a repair).**
- *Change.* The sectors are cut in the **Gauss map**, by the normal direction ν(y), instead of by arc length along ∂K.
- *What arc-length sectors needed.* Their frames are the normal at the start of the sector. Sectors containing turning > θ ("bad
  sectors", e.g. at the corners of K) then have to be exceptional, and the cut crossings cost O(r·T/L_s). That also works, with one more
  ηr term.
- *What Gauss-map sectors give.* Every shallow point is automatically within θ of its sector frame, so there are no bad sectors. The seam
  cost is O(1) by the multiplicity lemma (Lemma 4.5).

## 8. D1's three referee flags, resolved

**Flag 1: "Lemma T* rescaled to |pb| ≤ 4D₁ + 1 is not rewritten line by line."**
- *Resolution.* No rescaling is needed. Paper Lemma 9.2 (packing in thin K) is stated and proved for every 1 ≤ ℓ ≤ Δ₂/100 and
  Λ > 115ℓ.
- *Where it is used.*
  - Lemma 4.3(iii): ℓ = 2, Λ = 231.
  - Lemma 4.6: ℓ = 2M + 3 ≥ 2T + 1 (the analogue of D1's "4D₁ + 1"), Λ₁ = 116ℓ. The hypothesis ℓ ≤ Δ₂/100 is part of Δ₂ ≥ Δ₂*.
- *Checks on the proof.* The lemma's proof uses:
  - the nondegenerate regime, through |w_bot − w_top| ≤ Δ ≤ 1.94Δ₂;
  - the numerical bound 1.998 − 0.035 − 0.011 > 1.94, in which ℓ enters only through w₀/Δ₂ ≤ 1.0001ℓ/Δ₂ ≤ 0.0101 (the "0.011").

  Both hold uniformly in ℓ ≤ Δ₂/100. **Resolved.**

**Flag 2: "the count of non-good points in B1 P0.1 is independent of v".**
- *Resolution.* Correct, and this is exactly what is needed. Paper Lemma 9.5 is stated for points with v ≥ 7, but that restriction is
  used only to discard 𝓡∩D and h > 1.
- The three cases of its proof bound **all** non-good h ≤ 1 points of 𝓡∖D: perimeter ≤ 2Λ, turning > ε₀ (the multiplicity count), and
  thin K. None of them uses v. Lemma 4.3 restates the count in this form: N_ng = 463² + 2π·465²/ε₀ + 7600 at Λ = 231, ρ = 1.
- Theorem G needs all non-good points to be exceptional, whatever their weight, because a non-good point of weight ≤ 6 can still own 4
  or more edges. **Resolved.**

**Flag 3: "the expected cut count ℓ/Λ_s for perimeters that are not multiples of Λ_s".**
- *Resolution.* Gauss-map sectors have width θ_s = 2π/N_s, so 2π is an exact multiple. The cut set is a uniformly random translate of
  θ_sℤ/2πℤ, and the expected number of cuts in an arc of length α is exactly α/θ_s (Lemma 4.5(3); Markov turns this into a probability
  bound).
- For the arc-length variant, use L' := P/⌈P/L_s⌉ ∈ [L_s/2, L_s] and equally spaced cuts σ + jL', σ ∼ U[0, L'). The expected count is
  again exactly α/L' ≤ 2α/L_s.
- In the deep direction the analogous count is Lemma 4.4 (T ∼ U[1, 1 + M], density 1/M). **Resolved.**
