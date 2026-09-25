# REF_E: hostile referee report on branch E (R7) — fan window, Theorem G′, Proposition F, Theorem E (81/61)

Referee REF_E of angle R7 (Erdős #132 / CDL Problem 1.6), 2026-09-25. Written incrementally; committed per section.
Object: `angle_R7_reports/E_report.md` (STATUS FINAL) and `scripts/r7_E_{window,structure,lp,reuleaux}.py`.
Inputs read: angle_R7.md (all), D1_report.md (+ Errata), REF_D1_report.md, paper/paper.tex v3 (§2 setup, Lemma 2.2, Lemma VS/VSQ,
Lemma 9.3 frame incl. (G5), Lemma 9.4 DN, Lemma pin, Remark rem:sharp), WRITEUP_A2.md (Lemma 4.2), scripts r7_C_*, r7_refC_*.
New scripts: `scripts/r7_refE7_*.py` (run as `tools/memcap.sh 4000 .venv/bin/python problems/132/scripts/<name>`).

E's own scripts rerun under memcap: `r7_E_window.py`, `r7_E_lp.py`, `r7_E_structure.py` all pass (outputs as in E §5.5).

## 0. Plan of the audit

1. Definitions: is Q in VSQ, Q′ in Theorem W, and Q_K in Proposition F one consistent family? (flag 4)
2. Lemma EW and its applicability to every F* point (flags 1, 5), exactly.
3. Theorem G′ uniformity (flag 2).
4. Lemma U, C2(a) (flag 3), Proposition F.
5. The LP: exact vertex enumeration and certificates; what survives if an input fails.
6. X1, C2(b), ORD (flag 6), §4.
7. Consistency with ienjoymath (9/7). Verdict.
