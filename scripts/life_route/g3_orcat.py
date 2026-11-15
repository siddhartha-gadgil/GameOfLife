#!/usr/bin/env python3
"""G3 (R-29): OR gates from the catalogue of blockedStream (scripts/life_gates s3/s4, read-only).
For the released stream glider A = (SE, 14, .) (gate coordinates), list the repeatable control
records from infinity grouped by direction and lane, with the residues tau (mod 30) that release A
and the output tau.  'Relay' records: control SE (same direction as A) -> chainable by translation."""
from gcommon import *
from machine import load_catalog
from collections import defaultdict

recs = load_catalog()
by = defaultdict(list)
for r in recs:
    if r['kind'] != 'gate' or not r['from_infinity'] or len(r['outs']) != 1:
        continue
    o = r['outs'][0][0]
    if not (o[0] == SE and o[1] == 14):
        continue
    by[(r['d'], r['lane'])].append((r['tau'], o[2], bool(r['repeat']), r['duration']))
for key in sorted(by, key=lambda k: (DIRNAME[k[0]], k[1])):
    v = sorted(by[key])
    print('%s lane %4d: ' % (DIRNAME[key[0]], key[1]) + ' '.join('%d->%d%s' % (t, o, '' if rp else '?') for t, o, rp, du in v))
