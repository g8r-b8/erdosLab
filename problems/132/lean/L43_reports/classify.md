# L43 report: `E132Main43Classify.lean` (Lemmas P, M, H, Pin)

**Status: the file has no `sorry`.** `#print axioms` for `lemmaH`, `lemmaM`, `fanShape_of_m4`,
`hexagon_exact`, `heavy_type` and `heavy_low` gives only `[propext, Classical.choice, Quot.sound]`,
so the whole upstream chain (Defs, Frame) is sorry-free as far as these results use it.
No statement was changed. There is no `native_decide`/`bv_decide` and no new axiom.

## Commits (this phase)

| commit | content |
|---|---|
| 1d420c0, 18ceba5 | (earlier session) `mS_le_four_of_frame`, `pair_sym`, `pair_K`, `pair_D`, `pin_cap`, `pin_fan` |
| cfcb974 | `lemmaM`, `fanShape_of_m4` (+ angle helpers `c43_angle`, `c43_chord`, `c43_dot_slot`, `c43_slot_of_angle`, `c43_arc4`) |
| c90d571 | `hexagon_exact` (+ `c43_count`, `c43_rot_eq`, `c43_eq_of_coords`) |
| e7ad7b1 | lemmaH helpers: hexagon enumeration, pinning, three-of-a-kind |
| 688aa8e | `lemmaH` (six pair cases + dispatch); docstrings set to "TODO: none — proved." |

## Proof routes (differences from the paper)

* **`c43_arc4` (used by Lemma M).** This lemma needs no sorting. Give each `S`-neighbour its angle
  `ψ ∈ (−π, π]`. `|ψ| < π/2 + 0.021` because `sin 0.021 > 1/49`. Let `k(q)` be the number of
  angles below `ψ_q`. Counting the angles `≤ ψ_q` and `≥ ψ_q` (`card_le_of_sep_real`) gives
  `|ψ_q − (−π/2 + kπ/3)| ≤ 0.021`. So `k` is injective, and `surjOn_of_injOn_of_card_le` then
  fills all four slots.
* **`lemmaM`.** The 4 slot points have chord error `≤ 0.021 < 1/40`. Assigning their kinds is
  linear arithmetic: `c43_KD` (K height `≤ h`, D height `> h − 1/49`) plus `pair_K`/`pair_D`
  height differences.
* **`fanShape_of_m4`.** This proof does not need `hexagon_exact`. With `c43_dot_slot` (a neighbour
  `≠ q'` has `⟨q − y, dirF ψ⟩ ≤ 1/2 + η` when `q'` is in slot `ψ`):
  * Every neighbour other than `p₁, p₂` has `|X| ≤ 21/40`, so if its height is `≤ −2/3` it is
    `≤ −4/5`.
  * A non-`S` neighbour also has `√3·Z ≤ 21/20` (from `z₁, z₂`), so `Z ≤ −4/5`.
  * The count is `v = deg + 4 ≤ 8 + #(non-S)`. The hypothesis `5 ≤ deg` turned out to be unused
    (linter warning only).
* **`hexagon_exact`.** Take the frame `n = q − y`. The other 5 neighbours have angles in
  `[π/3, 5π/3]` and are pairwise `π/3`-separated (`c43_count`). So the minimal one is exactly at
  `π/3`, and equal coordinates give `rot(π/3)(q − y)`.
* **`lemmaH`.**
  * **Hexagon.** `c43g y x = y + rot(π/3)(x − y)`. `c43_hex_enum` shows the neighbours are
    `a, g a, …, g⁵ a`, using the angle of `x` relative to `a − y`. `c43g3` gives `g³x = 2y − x`.
  * **Setup.** The 3 `S`-points come from `card_eq_three`. All 8 kind patterns are checked:
    KKK and DDD are impossible by `c43_three_K`/`c43_three_D`. Each other pattern has a pair `a, b`
    of the same kind with `b = gʲ a`. The cases `j = 4, 5` are swapped to `j = 2, 1`.
  * **Pinning (`c43_pin`).** The mirror bound is exactly the component orthogonal to the slot. It
    puts `a` within `η` of the slot or of its antipode. The algebra (`P² + Q² = 1`) has no
    `arcsin`.
  * **Propagation.** `c43g_slot` rotates the slot to every vertex with the same error, so all later
    steps are linear arithmetic on exact values `cos, sin (mπ/6)`.
  * **The six pair cases.** Each case's `j` is the step from `a` to `b` in `b = gʲ a`:

    | case | pin `(δ, η)` | outcome |
    |---|---|---|
    | K, `j=1` (`±30°`) | `(1/49, 0.03)` | impossible |
    | K, `j=2` (`±60°`) | `(0.012, 0.02)`, using `Z_a − Z_b = √3·Q` | **cap** (`σ = −1`, `z` at `0°`, `b` at `180°`) |
    | K, `j=3` (`±90°`) | `(1/98, 0.02)`, both orientations | **HF1** |
    | D, `j=1` (`±30°`) | `(9/400, 1/30)`, via `dd_heights` and `\|X_a − X_b\| ≤ 1` (adjacent) | **HF2** (`dist z₁ z₂ = 1` by `c43g_dist`) |
    | D, `j=2` | `(0.026, 0.037)` | impossible |
    | D, `j=3` | `(9/400, 1/30)` | impossible |

    All slot errors are `≤ 1/30 < 1/20`.
  * **Height margins.** The fan lower points have height `≤ −√3/2 + 1/30 ≈ −0.833 ≤ −4/5`. For the
    cap, the points at `±120°` have height `≥ −0.52 > −2/3`, and the point at `180°` is within
    `0.02` of `y − n`.

## Issues / notes

* Linter warnings only: unused `hy` in `lemmaM`/`lemmaH`, unused `hd` in `fanShape_of_m4`, and
  two `<;>` style hints.
* `c43_arc4` has its own copy of the counting helper. This duplicates `c43_count`, but it is
  harmless and could be refactored.
* The file is now about 1740 lines and compiles in about 1–2 min under `leanslot`.
