# Paper v3: branches considered (2026-09-25)

Paper v3 changes the main theorem from L ≤ 15/11 to L ≤ 4/3 (Theorem N3 of angle_R6, refereed twice). It adds
21n/16 + C in Region I and for τ > 1 (Theorem P4, refereed twice, CORRECT WITH GAPS, all repairs applied) and
9n/7 + O(n^{2/3}) for τ > 1 (Theorem E′, refereed three times, the last time on the complete corrected proof).
15/11 stays as the formalised backbone (Theorem 8.1).

## Crossroad 1: where the new material goes (no genuine choice; one draft)
The brief asked for a minimal restructuring, so there was only one draft:
- §§2–7 are unchanged, and are still the proof of 15/11.
- §8 becomes "Assembly: the formalised bound 15/11" (Theorem 8.1).
- New §9 (N3 ⇒ Theorem 1(a)), §10 (P4 ⇒ Theorem 1(b) in Region I and τ > 1), §11 (Region II part of 1(b)) and §12 (E′ ⇒ Theorem 1(c)) are added on top.

Two alternatives were set aside without drafting:
- Moving 15/11 to an appendix would have broken the Lean section's cross-references to §§2–8 and contradicted "restructure minimally".
- Presenting 4/3 as a self-contained proof would have duplicated §§2–6.

## Crossroad 2: add Region II to Theorem 1(b)? (genuine choice; branch drafted by an agent)
| branch | file | outcome |
|---|---|---|
| exclude | (earlier state of `paper.tex`) | Theorem 1(b) would cover only Region I and τ > 1. |
| **include** (chosen) | `v3_branches/paper_v3_regionII_fragment.tex`, report `v3_branches/REGIONII_BRANCH_REPORT.md` | Becomes §11 (Region II). Theorem 1(b) then holds for τ ≤ √3/2 − 1/50 or τ ≥ √3/2 + 3/100. |

Including Region II needs two new inputs, each refereed only once:
- e(S) ≤ s + ½|Q′| + C (angle_R7 §1, A2 fixes F1–F4);
- the average weight ≤ 7 in Region II (angle_R7 §3, REF_B fixes).

**Decision: include**, on the coordinator's call. The paper labels this part honestly:
- the intro status paragraph, the §11 status paragraph and the appendix all say that each Region II input had **one** referee pass;
- they also say that the text of §11 itself has not been refereed.

What adoption required:
- The drafter's recommended follow-on edits (abstract, intro, rem:bottleneck(b), rem:N3(b), the opening of §10, open problems).
- Copying `r6_below_classify_B1copy.py`, `r6_below_rule_check_B1copy.py` and `r7_refB_{margins,classify,search,exact}.py` into `scripts/`. `r7_B_classify.py` and `r7_refB_margins.py` / `r7_refB_classify.py` were re-run from `scripts/` and pass.

Two further changes to the text:
- Open problems now say that only Region III stays at 4/3.
- A new remark (rem:regionIII) mentions R7's Theorem W as work in progress. Theorem W had one referee pass; it gives e(S) ≤ s + ⅔|Q| + C in Region III, which would leave only the average weight there as the obstacle. The remark claims no new bound.

## Constraints applied throughout
- The two false statements in angle_R6 §4 flagged by REFEREE2_R6 are not in the paper:
  - B's range is the half-open [t, √3/2);
  - the paper makes no claim about forwarding targets also receiving directly. The load lemma covers every receiver.
- The τ > 1 result is described as "matches the global lower bound 9/7", never "sharp" (the 9/7 constructions have τ → 0).
- There is one AI-disclosure line in each document. Checks are described neutrally ("independent referee passes").
