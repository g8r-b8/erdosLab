#!/bin/bash
# rational sweeps: d = g*m, m <= M
cd "$(dirname "$0")/.." && mkdir -p logs/rat
while read g M; do
  ./scripts/dpair $g $M 0 1 1 > logs/rat/g${g}_M${M}.txt 2> logs/rat/g${g}_M${M}.err &
done
wait
