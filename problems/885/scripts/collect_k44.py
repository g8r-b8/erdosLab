#!/usr/bin/env python3
"""Collect distinct (up to rational scaling) 4x4 configurations from dpair/dpair2 logs -> data/k44.tsv
columns: x1..x4 (x = 4N form, integers)  d1..d4"""
import re, sys, glob
from fractions import Fraction as Fr
seen, out = set(), []
for f in sorted(glob.glob('logs/**/*.txt', recursive=True)):
    for l in open(f):
        if not l.startswith('K4 '): continue
        g = int(re.search(r'g=(\d+)', l).group(1))
        ms = list(map(int, re.search(r'm=\{([\d,]+)\}', l).group(1).split(',')))
        xs = sorted(map(int, l.split('x:')[1].split()))[:4]
        ds = sorted(g * m for m in ms)[:4]
        key = (tuple(Fr(x, ds[0]**2) for x in xs), tuple(Fr(d, ds[0]) for d in ds))
        if key in seen: continue
        seen.add(key); out.append(xs + ds)
import os; os.makedirs('data', exist_ok=True)
with open('data/k44.tsv', 'w') as fh:
    for r in out: fh.write('\t'.join(map(str, r)) + '\n')
print(len(out), 'distinct configurations')
