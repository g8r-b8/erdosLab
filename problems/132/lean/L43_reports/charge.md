# L43 report: `E132Main43Charge.lean` and `degδ_le_three_of_D` (Defs)

**Status: the whole `4/3` chain is sorry-free.** `E132Main43.lean` compiles, and
`#print axioms Erdos132Main.erdos132_main43` prints

```
'Erdos132Main.erdos132_main43' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No statement was changed. There is no `native_decide`/`bv_decide` and no new axiom. The only
edits are the one proof body in `E132Main43Defs.lean` and the four proof bodies in
`E132Main43Charge.lean`, plus private helper lemmas `ch_*` in Charge. The docstrings now say
"TODO: none — proved."
The oleans were rebuilt through the semaphore in this order: Defs, Frame, Good, Classify,
Charge, Main43.

## Commits

| commit | content |
|---|---|
| aed49a6 | `degδ_le_three_of_D` (Defs) |
| f04fbca | `cap_disjoint` |
| 75bf548 | `mS_le_one_of_Low` |
| 906b3cb | `fan_common_low_slot` (+ helpers `ch_np`, `ch_pn`, `ch_sq`, `ch_dirF_n/p`, `ch_abs`, `ch_dirF_sub`, `ch_slotX`, `ch_sin2`, `ch_cos2`, `ch_sin6`, `ch_hex`, `ch_fan_hf2`, `ch_num`, `ch_num_d`) |
| c092bf4 | `fan_disjoint` |
| 6ed60c1 | docstrings in Charge/Defs changed to "proved" |

## Proof routes

* **`degδ_le_three_of_D`.** A proved copy already existed as `degδ_le_three_of_D97` in
  `E132Main97DPart.lean`, but that file sits downstream of Main15 and is not imported by Defs.
  I could change only this proof body, so the open-half-circle packing lemma
  (`card_sep_arc_le_three`) is inlined as a local `have key`. The cone is
  `(q − z)·(w − z)/Δ ≥ 1/(2Δ)`, which follows from `|q − w| ≤ Δ`.
* **`cap_disjoint`.** `y′ − y = (b − y + n) − (b − y′ + n′) + (n′ − n)`, so
  `‖y′ − y‖ ≤ 1/20 + 1/20 + 1/50 < 1`. This contradicts `one_le_dist`.
* **`mS_le_one_of_Low`.** Apply `card_cone_le_two` at `a` to `insert y (S-neighbours of a)`. For
  `y`, `⟨y − a, n⟩ ≥ 2/3` (`Low_Z`). For an `S`-neighbour `q`, `frame_outside` with
  `|⟨q − y, perp n⟩| ≤ ‖q − y‖ ≤ 2` gives `⟨q − y, n⟩ ≥ −2/49`, so
  `⟨q − a, n⟩ ≥ 2/3 − 2/49 > 1/2`. Since `y ∉ S`, `card = 1 + m_a ≤ 2`.
* **`fan_common_low_slot`.** Work in the coordinates `c = ⟨e, n⟩`, `x = ⟨e, perp n⟩` with
  `e = y − a` and `e′ = y′ − a`. The inputs are `c ≥ 4/5`, `c′ ≥ 4/5 − 1/50` (from
  `⟨e′, n′⟩ ≥ 4/5` and `frame_normal_close`), `c² + x² = c′² + x′² = 1` and
  `(c′ − c)² + (x′ − x)² ≥ 1`.
  * The first step is pure numerics, isolated in the lemma `ch_num`: `|c′ − c| ≤ 0.22`,
    `|x| ≤ 0.6` and `|x′| ≤ 0.63`, so `|x′ − x| ∈ [0.97, 1.23]`.
  * The second step takes `σ = sign(x′ − x)` and bounds the squared distance by
    `0.0484 + 0.0529 = 0.1013 ≤ (7/20)² = 0.1225`.
  * `nlinarith` timed out while the full context was present. It works once the numerics sit in
    separate small lemmas.
* **`fan_disjoint`.** The argument follows the refereed plan.
  * `ch_fan_hf2` is the slot argument, used twice. If `y′ ∈ R` lies within `7/20` of `y`'s
    `σ′·90°` direction, then the slot point `q` (when `σ′ = σ`) or `p` (when `σ′ = −σ`) is within
    `0.4 < 1` of `y′`. It therefore equals `y′`. The point `p` is impossible because `p ∈ S`, so
    `y′ = q ∉ S`, and `y` falls in the HF2 branch.
  * The same argument with the roles swapped gives `τ`. The case `τ = σ` fails on the abscissae,
    because `⟨y′ − y, perp n⟩ ≈ σ ± 0.05` and `⟨y − y′, perp n⟩ ≈ τ ± 0.09`. So `τ = −σ`.
  * The hexagon identity `dirF(σ30°) = dirF(σ90°) + dirF(−σ30°)` (`ch_hex`, proved by
    `module`) combines with `‖dirF n ψ − dirF n′ ψ‖ ≤ 2‖n − n′‖` (`ch_dirF_sub`). Together
    they give `‖z₁ − z₁′‖ ≤ 3/20 + 1/25 < 1`, so `z₁ = z₁′`.
  * The points `y, y′, z₂, z₂′` are all `δ`-neighbours of `z₁`. Their abscissae relative to
    `(y, n)` are `0`, `σ ± 0.05`, `−σ/2 ± 0.05` and `3σ/2 ± 0.14`, so the four points are
    distinct. This gives `degδ z₁ ≥ 4`, which contradicts `degδ_le_three_of_D`.

## Remaining sorries

None in `E132Main43*.lean`.
