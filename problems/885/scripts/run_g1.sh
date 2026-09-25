#!/bin/bash
# Complete g=1 search to M, 8 parts, at most $2 concurrent jobs (default 2), RSS watchdog, no auto-restart.
M=${1:-50000}; J=${2:-2}
cd "$(dirname "$0")/.." && mkdir -p logs/g1
export DPAIR_MEMCAP_MB=800
for p in 0 1 2 3 4 5 6 7; do
  while [ $(pgrep -f "dpair2 1 $M" | wc -l) -ge $J ]; do sleep 5; done
  nice -n 10 ./scripts/dpair2 1 $M $p 8 1 > logs/g1/v2_M${M}_$p.txt 2> logs/g1/v2_M${M}_$p.err &
  sleep 1; [ $p -eq 0 ] && (./scripts/watchdog.sh 1000 >> logs/g1/watchdog.log 2>&1 &)
done
wait
