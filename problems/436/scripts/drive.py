"""Driver: exact search for Lambda_comb(k,l) or geometric probing, using lamenc + kissat/cadical.

  python drive.py k l [--R0 R] [--grow G] [--solver kissat] [--work DIR]
Exact mode (grow=1): R <- first run of the model f (so S(R-1) SAT); stop at first UNSAT R => Lambda = R.
Geometric (grow>1): R <- max(first_run, ceil(grow*R)); at UNSAT only the bound Lambda <= R is certified.
"""
import argparse, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ENC = os.path.join(HERE, "lamenc")


def solve(k, l, R, work, solver, extra=()):
    cnf, mp, md = (os.path.join(work, f"k{k}l{l}R{R}.{e}") for e in ("cnf", "map", "model"))
    e = subprocess.run([ENC, "enc", str(k), str(l), str(R), cnf, mp], capture_output=True, text=True)
    info = e.stderr.strip()
    t0 = time.time()
    with open(md, "w") as fh:
        p = subprocess.run([solver, "-q", *extra, cnf] if solver == "kissat" else [solver, "-q", *extra, cnf],
                           stdout=fh)
    dt = time.time() - t0
    if p.returncode == 20:
        os.remove(md)
        return "UNSAT", None, info, dt, cnf
    assert p.returncode == 10, p.returncode
    lim = 2 * R + 100
    while True:
        r = subprocess.run([ENC, "run", str(k), str(l), str(lim), mp, md], capture_output=True, text=True)
        o = r.stdout.strip()
        if not o.startswith("NONE"):
            t = int(o); break
        lim *= 2
    os.remove(cnf)
    return "SAT", t, info, dt, md


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("k", type=int); ap.add_argument("l", type=int)
    ap.add_argument("--R0", type=int, default=1)
    ap.add_argument("--grow", type=float, default=1.0)
    ap.add_argument("--solver", default="kissat")
    ap.add_argument("--work", default=".")
    a = ap.parse_args()
    os.makedirs(a.work, exist_ok=True)
    R, T0 = a.R0, time.time()
    while True:
        st, t, info, dt, f = solve(a.k, a.l, R, a.work, a.solver)
        print(f"[{time.time()-T0:8.1f}s] R={R} {st} solve={dt:.1f}s first_run={t}  ({info})", flush=True)
        if st == "UNSAT":
            print(f"RESULT k={a.k} l={a.l}: S({R}) UNSAT => Lambda_comb <= {R}"
                  + (f" (exact: = {R})" if a.grow == 1.0 else ""), flush=True)
            return R
        assert t > R
        R = max(t, int(a.grow * R + 0.999)) if a.grow > 1 else t


if __name__ == "__main__":
    main()
