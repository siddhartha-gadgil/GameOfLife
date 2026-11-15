#!/bin/sh
# refinement scans of g2_reuse.py (R-29); output results/g2_fine.txt
cd "$(dirname "$0")"
OUT=results/g2_fine.txt
: > $OUT
for k in 1 2 3 40; do python3 g2_reuse.py DD $k 0 100 1 >> $OUT; done
python3 g2_reuse.py DD 0 630 645 1 >> $OUT
for k in 1 2 3 40; do python3 g2_reuse.py DI $k 60 200 1 >> $OUT; done
python3 g2_reuse.py DI 0 830 845 1 >> $OUT
for k in 0 1 2 3 40; do python3 g2_reuse.py ID $k 20 60 1 >> $OUT; done
echo done >> $OUT
