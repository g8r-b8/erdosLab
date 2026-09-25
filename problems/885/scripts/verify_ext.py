#!/usr/bin/env python3
"""Exactly verify ext.c survivors with PARI/gp. Prints any GENUINE extension (5th column or 5th row)."""
import glob, re, subprocess, sys
cfg = [list(map(int, l.split())) for l in open('data/k44.tsv')]
prog = []
for f in sorted(glob.glob('logs/ext/c*_Q*.txt')):
    i = int(re.search(r'/c(\d+)_', f).group(1)); xs, ds = cfg[i][:4], cfg[i][4:]
    for l in open(f):
        m = re.match(r'(COL|ROW) q=(\d+) (?:p|s1)=(\d+)', l)
        if not m: continue
        t, q, v = m.group(1), int(m.group(2)), int(m.group(3))
        if t == 'COL':
            prog.append(f'if(vecmin(vector(4,i,issquare({q}^2*{xs}[i]+{v}^2))),print("GENUINE COL cfg {i} d=",{v}/{q}),print("false COL cfg {i} q={q}"))')
        else:
            prog.append(f'X={v}^2-{q}^2*{ds[0]}^2; if(vecmin(vector(4,j,issquare(X+{q}^2*{ds}[j]^2))),print("GENUINE ROW cfg {i} x=",X/{q}^2),print("false ROW cfg {i} q={q}"))')
out = subprocess.run(['gp', '-q'], input='\n'.join(prog) + '\n', capture_output=True, text=True).stdout
print(out, end='')
print(f'# checked {len(prog)} survivors; genuine: {out.count("GENUINE")}', file=sys.stderr)
