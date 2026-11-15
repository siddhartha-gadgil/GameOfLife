#!/usr/bin/env python3
"""F0 (R-28): the frozen data of DZ2 (R-27), world frame of REG1 (R-24).  Imported by f*.py.

Frozen (k >= 1 part, under Lean certification): REG1, F_A, RF_a, RF_b, G_N.  RF_R (Z part) as in R-27.
"""
import json
import os
from dcat import *
from net import env_cells, glider_path

REGF = os.path.join(HERE, '..', 'life_machine', 'results', 'register.json')
F_A = [('asm', 6, -560, -587, 22), ('asm', 6, -498, -552, 17)]
RF_A = ('rf', 2, -252, -796, 17)
RF_B = ('rf', 3, 461, -47, 10)
G_N = ('asm', 3, -29, 440, 4)
RF_R = ('rf', 4, 50, 374, 24)
C = (SE, -13, 2446)              # the one control glider
C0 = (SE, 41, 2422)              # REG1's DEC control as released by F_A (natural (SE, 41, 22) + 2400)
Y_A = (NE, 1071, 2851)           # F_A's second output
W1 = (SE, 530, 2846)             # after RF_a
D = (SW, 397, 6549)              # detector (local (SW, 9, 1825))
N1 = (SE, -391, 6589)            # NZ output
N2 = (SE, -391, 6619)
R_IN0 = (SE, -345, 5430)         # RF_R input giving R = (NE, -408, 5425); may be delayed by 30 m
R0 = (NE, -408, 5425)
CI0 = (SE, 314, -2222)           # REG1's INC control (natural); may be delayed by 30 m
SHIFT = (148, 240, 4132)         # local (SlidingBlock) -> world: translate (148, 240), time + 4132


def reg1_pieces():
    d = json.load(open(REGF))
    return [tuple(p) for p in d['pieces']]


def frozen_pieces():
    return reg1_pieces() + F_A + [RF_A, RF_B, G_N]


def envelope(pieces):
    e = set()
    for p in pieces:
        e |= env_cells(p)
    return e


def blocks(k0=-1, k1=80):
    b = set()
    for kk in range(k0, k1 + 1):
        b |= translate(set(counter(kk)), 148, 240)
    return b
