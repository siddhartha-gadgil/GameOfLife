#!/bin/sh
# coarse scans of g2_reuse.py (R-29); output results/g2_coarse.txt
cd "$(dirname "$0")"
OUT=results/g2_coarse.txt
: > $OUT
for k in 2 3 40 1; do python3 g2_reuse.py DD $k 100 400 5 >> $OUT; done
python3 g2_reuse.py DD 0 400 1000 10 >> $OUT
for k in 0 1 2 3 40; do python3 g2_reuse.py II $k 0 30 1 >> $OUT; done
for k in 1 2 3 40; do python3 g2_reuse.py DI $k 200 500 5 >> $OUT; done
python3 g2_reuse.py DI 0 400 1000 10 >> $OUT
for k in 0 1 2 3 40; do python3 g2_reuse.py ID $k -60 60 2 >> $OUT; done
echo done >> $OUT
