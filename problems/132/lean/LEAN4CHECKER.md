# Independent kernel re-check of the E132 Lean development

Date: 2026-09-23. Project: `Erdos/` (toolchain `leanprover/lean4:v4.35.0-rc2`, Mathlib `v4.35.0-rc2`),
checked at repo HEAD `4c8e7a9`. `lake build --no-build` gave "All targets up-to-date (2718 jobs)",
so the `.olean` files checked below match the committed sources. No project files were modified.

## Tools

- **lean4checker**: the standalone repo (github.com/leanprover/lean4checker, last tag `v4.29.0-rc8`)
  is deprecated. Its README says it "has been merged into the Lean 4 repository itself" and ships as
  **`leanchecker`** with every toolchain from v4.28.0 on. So the check used the `leanchecker`
  that ships with v4.35.0-rc2 (`~/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/leanchecker`,
  source `src/lean/LeanChecker.lean`). There was no need to build the old repo.
- **nanoda_bin 0.4.17**: an external type checker written in Rust (ammkrn/nanoda_lib), also shipped
  with the toolchain. It is a kernel implementation independent of Lean's C++ kernel.
- **leanexport** (lean4export 3.1.0, also shipped): dumps a declaration's full dependency closure
  in the NDJSON export format.
- (The bundled `lean4lean` binary could not read these `.olean` files: "incompatible header".
  It was not used.)

## Commands and results (all run from `Erdos/`)

| # | Command | Result |
|---|---|---|
| 1 | `lake env leanchecker Erdos.<M>` for each M in E132Convex, E132ConvexFinset, E132Layer, E132Ve87, E132ConvexCurve, E132MainDefs, E132MainLocal, E132MainRegions, E132MainDegen, E132Main | all exit 0, no errors (10–23 s each, ~2.2 GB RSS) |
| 2 | `lake env leanchecker -v Erdos` (all 12 `Erdos.*` modules, in parallel) | exit 0, every module replayed |
| 3 | `lake env leanchecker --fresh -v Erdos.E132Main` (replays **every** constant in the import closure, including Lean core and all imported Mathlib, into an empty environment) | exit 0; 345 s wall, 3.2 GB max RSS |
| 4 | `lake env leanexport Erdos.E132Main -- Erdos132Main.erdos132_main > e132main.ndjson` | 287 MB, 5.39 M lines |
| 5 | `nanoda_bin nanoda.json` with `permitted_axioms = [propext, Classical.choice, Quot.sound]`, `unpermitted_axiom_hard_error = true`, Nat and String extensions on | **"Checked 41754 declarations with no errors"**. The export has exactly 3 axioms: propext, Quot.sound, Classical.choice |
| 6 | `lake env leanchecker --from-export e132main.ndjson` | "Lean default kernel accepts the solution" |
| 7 | `lake env lean AxCheck.lean` (scratch file: `import Erdos`, `#print axioms`, then a scan of every constant from an `Erdos.*` module) | see below |

nanoda pretty-printed the checked statement (proofs hidden) as:

```
theorem Erdos132Main.erdos132_main :
  ∃ C₀ : ℝ, ∀ X : Finset Erdos132Convex.Pt, 2 ≤ X.card →
    ((min (mult X (dist2 X)) (mult X (minDist X)) : ℕ) : ℝ) ≤ 54 / 37 * X.card + C₀
```

## Axioms

- `Erdos132Main.erdos132_main` depends on `[propext, Classical.choice, Quot.sound]` only. Both
  `#print axioms` and the nanoda strict allow-list (run 5) confirm this.
- Scan of all 981 constants in `Erdos.*` modules:
  - 0 constants depend on `sorryAx`.
  - The only `axiom` declarations are the two `bv_decide` certificates in E132Convex:
    `Erdos132Convex.bvNoCE7._native.bv_decide.ax_1_14` and `…bvNoCE11._native.bv_decide.ax_1_14`.
    These are expected and already disclosed. They appear only under `erdos132_convex7/11(_finset)`,
    not in the `erdos132_main` chain.
- `vesztergombi87` ([Ve87]) is a proved theorem, not an axiom. It is not in the axiom list.

## Verdict

**PASS.** The 54/37 main theorem `Erdos132Main.erdos132_main` was re-checked in three ways:
- Lean's kernel, module by module.
- Lean's kernel in `--fresh` mode, from an empty environment through all of Mathlib.
- nanoda, an independent external kernel, run on the exported closure (41,754 declarations).

All three accept it, with only the three standard axioms. None of the E132 modules shows any
sign of environment hacking.

Side notes (no action taken):
- The module docstring of `Erdos/E132Main.lean` (lines 6–9 and the theorem docstring) still says
  `sorry`s remain and that `#print axioms` includes `sorryAx`. That text is stale.
- `Erdos/E132Convex13.lean` exists but is not imported by `Erdos.lean`, so it was not checked.
