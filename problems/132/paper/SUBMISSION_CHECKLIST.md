# Erdős #132 paper: submission checklist

Status (2026-09-23):
- The draft `paper.tex` / `paper.pdf` builds cleanly (21 pp.).
- The main 54/37 theorem is **fully formalised in Lean**: sorry-free, standard axioms only (see `../lean/README.md`).
- **Nothing has been posted, sent or submitted.**

Legend:
- [x] done or prepared
- [ ] to do by the author
- (P) a draft is prepared in this directory

## 0. Prepared artefacts

- [x] `PREFLIGHT.md`: novelty re-check of 2026-09-23. No red flags.
- [x] `arxiv/`: clean arXiv source (`paper.tex`, `paper.bbl`, `refs.bib`) and `arxiv/arxiv-source.tar.gz`, verified to compile from a clean extract. The repository URL is still a TODO: `https://github.com/g8r-b8/erdos132-lean`.
- [x] `ARXIV_METADATA.md`: title, abstract (1368 chars), categories, comments, MSC, endorsement notes.
- [x] `FORUM_POST_DRAFT.md`, updated for the full Lean formalisation.
- [x] `EMAILS_DRAFT.md`: emails to Clemen / Dumitrescu / Dingyuan Liu and to T. Bloom.

## 1. Ordered checklist

1. [ ] **Independent kernel re-check of the Lean proofs.**
   - Run `lean4checker` (built for the same toolchain, `v4.35.0-rc2`) on the modules `Erdos.E132Main`, `Erdos.E132Layer`, `Erdos.E132ConvexFinset` and `Erdos.E132Convex13`. For example, from `Erdos/`: `lake env lean4checker Erdos.E132Main`.
   - Re-run `#print axioms Erdos132Main.erdos132_main` and confirm `[propext, Classical.choice, Quot.sound]`.
   - Record the results (date, commit hash) in `../lean/README.md` and in the paper's appendix.
2. [ ] **Human check of the Lean statement.**
   - Read `E132MainDefs.lean` and confirm that `mult`, `dist2` and `minDist` mean what the paper says. In particular, check the behaviour for sets with fewer than 3 distinct distances, where `dist2` must be defined somehow.
   - The formal proof is only as good as the statement.
3. [ ] **Human expert read (strongly recommended, and required before journal submission).**
   - Theorem 1, §§2–7: the ownership/pairing count (§5.2, Region II) and the incidence count (§6, Step 4). The Lean proof now covers the logic, but the exposition should still be readable and correct.
   - The layer bound in §8.
   - All checks so far are AI-driven: referee passes, scripts and Lean.
4. [ ] **Fix small inconsistencies in `paper.tex`, then mirror them into `arxiv/paper.tex`:**
   - The appendix item "*Lean 4.* The statements for n=7 and n=11 are formalised" should say n = 7, 11, 13.
   - "Limitations of the formalisation (iii) … the main theorem is treated in the next paragraph": the main-theorem paragraph comes *before* it.
   - The "*Lean.*" reproduction paragraph at the very end lists only the convex files. Add `lake build` for `E132Main*` / `E132Layer`, with timings.
   - Optionally add "The main theorem is formalised in Lean 4" to the abstract (the arXiv abstract in `ARXIV_METADATA.md` already has it).
   - Optionally add `\address` / `\email` (a public contact address) to the paper.
5. [ ] **Bibliography details.**
   - Confirm the source behind [Er97e] (Erdős's \$100 offer).
   - Confirm the CDL journal details (Acta Math. Hungar. 177 (2025) 231–245; https://link.springer.com/article/10.1007/s10474-025-01562-y).
   - Check the Altman 1963/1972 statements against the originals.
6. [ ] **Publish the repository.**
   - Make public a repo (or a trimmed copy) with `problems/132/scripts/`, `Erdos/` (the E132 files plus the lakefile/manifest) and `problems/132/lean/README.md`.
   - Do **not** include the paywalled PDFs in `novelty_sources/`.
   - Replace `https://github.com/g8r-b8/erdos132-lean` in `arxiv/paper.tex` (and replace `\placeholder{REPOSITORY URL}` in `paper.tex`), `ARXIV_METADATA.md`, `FORUM_POST_DRAFT.md` and `EMAILS_DRAFT.md`.
   - Rebuild the `.bbl` and tarball (commands in `ARXIV_METADATA.md`).
   - Optionally put the DRUP/LRAT certificates (about 120 MB for (13,7,5)) on Zenodo.
7. [ ] **Same-day novelty re-check.** Repeat the "Still to do" list in `PREFLIGHT.md`: the forum thread, ienjoymath's repo (the `RESULT3-upper-bound-program.md` / `NOTES.md` 404s), CDL citations, and the arXiv author listings.
8. [ ] **arXiv endorsement and submission.**
   - Get a math.CO endorsement (see `ARXIV_METADATA.md`).
   - Upload `arxiv/arxiv-source.tar.gz`.
   - Primary math.CO, cross-list math.MG, MSC 52C10 (68V20, 52A10), comments line as drafted.
   - Check the arXiv PDF preview.
9. [ ] **Forum post** (erdosproblems.com, thread 132).
   - Only after the arXiv version exists and steps 1–2 are done.
   - Use `FORUM_POST_DRAFT.md`, which includes the AI disclosure. The poster must be able to vouch for the post.
   - Link the PDF; don't paste the proof.
10. [ ] **Emails** (`EMAILS_DRAFT.md`).
    - (a) CDL authors, after arXiv. Take the addresses from their public pages.
    - (b) T. Bloom, after the forum post is live.
    - Do not ask for an endorsement or mention the prize in the first emails.
11. [ ] **Journal choice and submission.**
    - Natural fit: *Acta Mathematica Hungarica*, where CDL appeared.
    - Alternatives: *Discrete & Computational Geometry*, *European J. Combin.*, *Electronic J. Combin.* (open access), *Discrete Mathematics*, *Comput. Geom. Theory Appl.*, *Periodica Math. Hungarica*.
    - Check the venue's policy on AI-assisted work and disclose accordingly.
    - Possible referees: Vesztergombi, Swanepoel, Pach, or the CDL authors (if they have not collaborated with you). Avoid conflicts.
    - The computer-assisted convex part could be split off, e.g. to *Experimental Mathematics*, if a referee objects.
12. [ ] **Prize contact, only after journal publication.**
    - Erdős offered \$100 for "any nontrivial result" [Er97e].
    - Payment needs publication in a reputable journal, and it is handled by the **Combinatorics Foundation / Steve Butler**, not by erdosproblems.com.
    - Send the journal reference and the [Er97e] documentation.
    - Be realistic: 54/37 bounds CDL's Problem 1.6, which is related to #132 but does not answer either question of #132. Whether it counts is for the administrators to decide.

## 2. Known limitations to keep stated (do not upgrade)

- **Theorem 1.**
  - Hand proof, **and fully formalised in Lean** (sorry-free, standard axioms).
  - The formal proof deviates from the text in three places (Ve87 via the 2-core; direction-counting instead of arc length, so Lemma 5.2 is unused; a weaker mixed-T bound, 1200 instead of 71, which only changes C₀).
  - C₀ is not optimised, and the gap to 9/7 is open.
- **Cor. 8.7 (the A1 class)** needs hypothesis (H3). The sharpness examples were checked only in floating point. It is formalised in `E132Layer.lean` with standard axioms.
- **Convex position.**
  - n = 6, 7, 8 are literature corollaries.
  - Even n ≥ 10 is a parity-sharp corollary of CDL's proof.
  - n = 9 comes from Erdős–Fishburn.
  - n = 11, 13 are SAT-certified (drat-trim/lrat-check, trusting the Python encoder) and in Lean via `bv_decide` (trusting compiled code). n = 7 is also in Lean.
  - n = 15 is open.
