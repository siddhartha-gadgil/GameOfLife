#!/bin/sh
# R-31: all exact runs in parallel (results/p3_*.txt)
cd "$(dirname "$0")"
for a in r0=0 r0=1 r0=2 r0=3; do python3 p3_run.py add $a > /dev/null 2>&1 & done
for a in r0=0 r0=1 r0=2; do python3 p3_run.py share $a > /dev/null 2>&1 & done
for a in r0=0,r1=0,r2=0 r0=1,r1=0,r2=0 r0=2,r1=1,r2=0 r0=1,r1=2,r2=1; do python3 p3_run.py rand $a > /dev/null 2>&1 & done
wait
