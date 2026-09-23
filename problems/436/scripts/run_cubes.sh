#!/bin/bash
# run_cubes.sh k y runs.txt workdir logfile NPAR : cube-and-conquer on f(2),f(3),f(5) with kissat
k=$1; y=$2; runs=$3; W=$4; LOG=$5; NP=${6:-4}
HERE=$(cd $(dirname $0); pwd); PY=/Users/wingatejones/Projects/erdosLab/.venv/bin/python
mkdir -p $W
cubes=$($PY -c "
import itertools
k=$k
for v in itertools.product(range(k),repeat=3):
    nz=[x for x in v if x]
    if nz and k%nz[0]: continue
    print('2=%d,3=%d,5=%d'%v)")
one() { c=$1; f=$W/cube_${c//[=,]/_}.cnf
  info=$($PY $HERE/smooth_cnf.py $k 3 $y $runs $f --cube $c | cut -d' ' -f6-7)
  s=$(date +%s); kissat -q $f > $f.out; rc=$?; e=$(date +%s)
  echo "cube $c rc=$rc $([ $rc = 20 ] && echo UNSAT || ([ $rc = 10 ] && echo SAT || echo UNKNOWN)) $((e-s))s $info" >> $LOG
  [ $rc = 20 ] && rm -f $f $f.out; }
export -f one; export k y runs W LOG HERE PY
echo "$cubes" | xargs -P $NP -I{} bash -c 'one {}'
echo "ALL DONE" >> $LOG
