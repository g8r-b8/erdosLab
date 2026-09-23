#!/bin/bash
# warmchain.sh WORK START_MAP START_MODEL R1 R2 ... : chain warmls runs, each warm-started from the
# previous result; after each run verify with `lamenc run` and checkf.py, and append to status.tsv.
# Env: SCRIPTS (dir with lamenc, checkf.py), STATUS (status.tsv path), PMIN (30) SEED (1) MAXSTEPS (50000000) NOISE (0).  Stops at the first R not solved.
set -u
W=$1; map=$2; model=$3; shift 3
HERE=${SCRIPTS:-$(cd "$(dirname "$0")"; pwd)}; ST=${STATUS:-$HERE/../logs/probes/status.tsv}
PMIN=${PMIN:-30}; SEED=${SEED:-1}; MAXSTEPS=${MAXSTEPS:-50000000}; NOISE=${NOISE:-0}
ts() { date '+%Y-%m-%d %H:%M:%S'; }
for R in "$@"; do
  tag=ws_R$R; log=$W/$tag.log
  t0=$(date +%s)
  "$W/warmls" 5 3 "$R" "$map" "$model" "$W/$tag.map" "$W/$tag.model" "$PMIN" "$SEED" "$MAXSTEPS" "$NOISE" > "$log" 2>&1
  rc=$?; dt=$(( $(date +%s) - t0 ))
  lim=$((R + 1000000))
  # decoder A: lamenc run (the original decoder, ~5 bytes per n) up to LAMENC_MAX, else segcheck (O(segment))
  if [ "$R" -le "${LAMENC_MAX:-500000000}" ]; then dec=lamenc; else dec=segcheck; fi
  while :; do
    if [ $dec = lamenc ]; then a=$("$HERE/lamenc" run 5 3 $lim "$W/$tag.map" "$W/$tag.model"); else a=$("$HERE/segcheck" 5 3 $lim "$W/$tag.map" "$W/$tag.model"); fi
    case $a in NONE*) lim=$((lim * 2));; *) break;; esac
  done
  b=$(python3 "$HERE/checkf.py" 5 3 $lim "$W/$tag.map" "$W/$tag.model")
  end=$(grep '^END' "$log")
  if [ $rc = 0 ]; then st=SAT; else st=UNSOLVED; fi
  printf "%s\tR=%s warmls\t%s\t%ss from %s; %s_first_run=%s checkf_first_run=%s; %s\n" "$(ts)" "$R" "$st" "$dt" "$(basename "$map")" "$dec" "$a" "$b" "$end" >> "$ST"
  echo "$(ts) R=$R $st ${dt}s $dec=$a checkf=$b | $end"
  [ $rc = 0 ] || exit 1
  map=$W/$tag.map; model=$W/$tag.model
done
