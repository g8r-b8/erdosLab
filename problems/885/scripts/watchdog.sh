#!/bin/bash
# kill any dpair* process whose RSS exceeds $1 MB (default 2000); also stop everything if free memory is low
CAP=${1:-2000}
while pgrep -q dpair; do
  ps -axo pid=,rss=,comm= | awk -v cap=$((CAP*1024)) '$3 ~ /dpair/ && $2 > cap {print $1}' | while read p; do
    echo "$(date) watchdog: killing $p (RSS over ${CAP} MB)"; kill -9 $p; done
  sleep 2
done
