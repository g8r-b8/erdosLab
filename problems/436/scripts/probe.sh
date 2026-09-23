#!/bin/bash
# probe.sh R WORK LOGDIR [k l] : one verbose kissat run on S(R) for Lambda_comb(k,l), with file-only logging.
#   LOGDIR/k{k}l{l}R{R}.log    kissat progress (all "c" lines, verbose=1 periodic reports), plus our own
#                              '### ' header/footer lines (start time, instance size, result, first_run).
#   LOGDIR/status.tsv          one line per event: time  R  state  detail   (cheap to tail)
#   WORK/k{k}l{l}R{R}.model    satisfying assignment ("v" lines) if SAT
# Nothing is written to stdout. Reuses an existing CNF/map in WORK.
set -u
R=$1; W=$2; L=$3; k=${4:-5}; l=${5:-3}
HERE=$(cd "$(dirname "$0")"; pwd); ENC=$HERE/lamenc
tag=k${k}l${l}R${R}; cnf=$W/$tag.cnf; map=$W/$tag.map; model=$W/$tag.model; log=$L/$tag.log; st=$L/status.tsv
mkdir -p "$W" "$L"
ts() { date '+%Y-%m-%d %H:%M:%S'; }
note() { echo "$(ts)	R=$R	$1	$2" >> "$st"; echo "### $(ts) $1 $2" >> "$log"; }
exec >/dev/null 2>>"$log"
if [ ! -s "$cnf" ] || [ ! -s "$map" ]; then
  note ENCODE start; info=$("$ENC" enc $k $l $R "$cnf" "$map" 2>&1 >/dev/null); note ENCODED "$info"
else note REUSE "$(du -h "$cnf" | cut -f1) cnf"; fi
note SOLVE "kissat -v pid=$$"
t0=$(date +%s)
kissat -v "$cnf" | awk -v M="$model" -v G="$log" '/^v /{print > M; next} {print >> G; fflush(G)}'
rc=${PIPESTATUS[0]}; dt=$(( $(date +%s) - t0 ))
if [ $rc = 10 ]; then
  lim=$((2*R+100)); while :; do o=$("$ENC" run $k $l $lim "$map" "$model"); case $o in NONE*) lim=$((lim*2));; *) break;; esac; done
  note SAT "solve=${dt}s first_run=$o (Lambda_comb >= $o)"; rm -f "$cnf"
elif [ $rc = 20 ]; then note UNSAT "solve=${dt}s => Lambda_comb($k,$l) <= $R  (no proof logged: re-run with proof for a certificate)"
else note EXIT "rc=$rc after ${dt}s"; fi
