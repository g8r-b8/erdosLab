# Erdős #132 paper: submission checklist

Status: the draft `paper.tex` / `paper.pdf` builds cleanly. **Nothing has been posted or submitted.**

## 1. Before anything is public

- [ ] **Human expert read.** A human expert in discrete geometry reads the whole proof. At minimum:
  - Theorem 1 (§§2–7). The least standard parts are the ownership/pairing count (§5.2, Region II) and the incidence count (§6, Step 4).
  - The layer bound (§8: Prop. 8.2, Lemma 8.4, Thms 8.5–8.6).

  All checks so far are AI-driven: two adversarial referee passes plus scripts.
- [ ] **Author's own verification statement.** Fill in the red placeholder under "Statement on AI assistance" in `paper.tex`, plus the author, affiliation and email placeholders.
- [ ] **Re-check priority / novelty (same day as posting).**
  - [ ] ienjoymath's announced "LP analysis" companion note: https://github.com/mathematiclover1337/erdos-132-note. At our last check (2026-09-23) `RESULT3-upper-bound-program.md` and `NOTES.md` returned 404, and the repo was last pushed 2026-07-25. If it has appeared, compare it with Theorem 1 and cite it.
  - [ ] #132 forum thread (new comments after post-8100, 25 Jul 2026) and the proof-claims page.
  - [ ] arXiv listings for Clemen, Dumitrescu, D. Liu, and a search for "second largest distance" / "Problem 1.6".
  - [ ] Lean Pool / lyfar repos (very active) for convex-position rare-distance results.
- [ ] **Bibliography details.**
  - [ ] Confirm the exact reference behind erdosproblems.com's key [Er97e] (Erdős's \$100 offer), and cite it directly. It is currently cited via the website.
  - [ ] Confirm the CDL journal details (Acta Math. Hungar. 177 (2025) 231–245) against the published version.
  - [ ] Check Altman 1963/1972 statements against the originals (currently quoted via Fishburn 1995, Thm 1).
- [ ] **Repository link.** Make the repo, or a trimmed copy with `problems/132/scripts/` and `Erdos/Erdos/E132Convex.lean`, public, and replace `[REPOSITORY URL]` in the paper and the forum draft. Do not publish the paywalled PDFs in `novelty_sources/`; they are gitignored.
- [ ] **Reproducibility.** Optionally archive the DRUP/LRAT certificates (~120 MB for (13,7,5)) on Zenodo, since they are regenerated rather than stored.

## 2. arXiv

- [ ] Primary class math.CO, cross-list math.MG.
- [ ] Put the AI-assistance statement in the paper (already present) and in the arXiv comments field.
- [ ] License: default arXiv licence or CC BY.

## 3. Forum post (erdosproblems.com, thread 132)

- [ ] Only after the arXiv version exists and the human read is done. Use `FORUM_POST_DRAFT.md`.
- [ ] Mandatory AI-use disclosure, which is in the draft. The poster must understand and verify the math personally; there is no Lean proof of the main theorem.
- [ ] Long proof, so link the PDF rather than pasting it.

## 4. Journal (needed for the prize)

Suitable venues for a discrete-geometry result of this size (~20 pages, one main theorem plus two side results):
- *Discrete & Computational Geometry*
- *Combinatorica* (a stretch)
- *European Journal of Combinatorics*
- *Electronic Journal of Combinatorics* (open access)
- *Computational Geometry: Theory and Applications*
- *Acta Mathematica Hungarica* (where CDL appeared)
- *Discrete Mathematics*
- *Periodica Mathematica Hungarica*

The computer-assisted convex part might alternatively be split off to a journal that welcomes certified computation (e.g. *Experimental Mathematics*), or dropped from the main submission if a referee objects.

- [ ] Choose a venue. Check its policy on AI-assisted work and disclose accordingly.
- [ ] Suggested referees: authors of related work (e.g. CDL authors, Vesztergombi, Swanepoel, Pach). Avoid conflicts.

## 5. Prize (\$100, "any nontrivial result", [Er97e])

- [ ] Prize payment requires **publication in a reputable journal**. The site owner has no say in this.
- [ ] Prizes are handled by the **Combinatorics Foundation / Steve Butler**. Contact them with:
  - the journal reference;
  - documentation of Erdős's offer, i.e. the [Er97e] source as cited on erdosproblems.com/132.
- [ ] Be realistic. Whether 54/37 (a bound for CDL's Problem 1.6), the layer-bound class, or the convex n ≤ 13 results count as a "nontrivial result" on #132 is for the prize administrators to judge. Problem 1.6 is related to #132, but it does not by itself answer either question of #132.

## 6. Known limitations to keep stated (do not upgrade)

- Theorem 1: hand proof, not formalised. The constant C₀ = 3·1.51·10⁹ + 10⁸ is not optimised.
- Cor. 8.7 (the A1 class) needs hypothesis (H3). The sharpness examples were checked only in floating point.
- Convex position:
  - n = 6, 7, 8 are literature corollaries (r₂ values from Fishburn's DIMACS report 92-17, as quoted in Erdős–Fishburn 1995).
  - Even n ≥ 10 is a parity-sharp corollary of CDL's proof.
  - n = 11, 13 trust the Python CNF encoder on the drat-trim route. The Lean route (n = 7, 11 only) trusts the compiled `bv_decide` checker and is stated for ordered polygons.
  - n = 15 is open.
