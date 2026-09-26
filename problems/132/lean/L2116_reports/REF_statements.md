# Statement referee: Lean skeleton of Theorem 1(b) (21/16)

Date: 2026-09-25.  Scope: the 37 `sorry`'d statements in `Erdos/Erdos/E132Main2116{Good,Frame,
ClassI,RegionIIw,DischI,RegionIIe}.lean`, judged **as written in Lean** (not as intended), plus
the question whether the proved wiring rests on constructible interfaces.  No Lean edited or
compiled.  Verdicts: TRUE / FALSE / UNCLEAR.  Scripts: `ref_scripts/`.

Conventions used throughout (from the base files): `dirF n ψ = sin ψ·perp n + cos ψ·n`, so
`ψ = 0` points along the outer normal ("up", towards `∂K`), `ψ > 0` towards `perp n`
(`perp` = rotation by `+90°`); height `Z q = ⟨q − y, n⟩`, abscissa `⟨q − y, perp n⟩`;
`h = depth X y`, level `= Z − h`; `t = tgap X = Δ − Δ₂`; `δ = 1`.

## 1. Good (`E132Main2116Good.lean`)

| lemma | line | verdict | key estimate / margin |
|---|---|---|---|
| `far_pointsP` | 84 | TRUE | `κ = 1.01·10⁻⁶`: `‖d − n‖ = 1.00999·10⁻⁶ > ε₀` (1% margin); `A ≤ Λ−1 ⇒ A² + C² ≤ Λ² − 2.0·10⁹`; height loss `κ(Λ−1) = 1010.0 ≤ 1011` |
| `thin_boxP` | 130 | TRUE | box `4·10¹¹ × 10¹⁰`: `W ≤ 2.1·10⁹ + 4·10¹¹/69 = 7.9·10⁹`; fatness needs `W < 0.058Δ₂`, have `≤ 0.029Δ₂ + 2.1·10⁹`, `Δ₂ ≥ 2·10¹⁵` |
| `turning_geP` | 172 | TRUE | scale-invariant copy of `turning_ge43` (`|ν₁·ν₂| ≤ 1 − 10⁻⁴` ⇒ support points within `150Λ`) |
| `card_bigTurning_leP` | 190 | TRUE | multiplicity `(4·1.5·10¹¹ + 1)²`, total turning `2π` |

Notes.
* `thin_boxP` docstring: "if `L ≥ 3.3·10¹¹` then `W ≤ L/48`" is off by a hair with
  `W ≤ 2.1·10⁹ + L/69` (needs `L ≥ 3.312·10¹¹`; with the honest `W ≤ 2Λ·(1+o(1)) + L/69`,
  `3.16·10¹¹` suffices).  Proof-internal only: any threshold `≤ 4·10¹¹` works, the statement is
  unaffected.
* `far_pointsP`: the hypothesis `0 ≤ h` (not `0 < h`) is harmless; the proof never divides by `h`.
* Wiring `frameP_of_good`, `thin_card_leP` (`(8·10¹¹+1)(2·10¹⁰+1) = 1.6·10²² ≤ 10²³`),
  `card_EP_le` (`2.26·10³⁰ + 10²³ ≤ 10³²`) checked: consistent.

