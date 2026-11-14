# R-21: Fan-out, reflector and a pull-salvo generator from Gosper guns (own search)

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** The data were produced on 2026-11-14 by the untrusted oracle
[`scripts/life_machine/`](../../../scripts/life_machine/README.md). Inputs: the gun of
`Guns.lean`, the glider and eater 1 of `Patterns.lean`, `blockedStream` and the gate of
`Gates.lean`, the salvos of `SlidingBlock.lean`, their symmetric images, translates and time
shifts, and the catalogue of gate reactions of `R-20` (`scripts/life_gates`, read-only). No
pattern file, placement or collision table from the literature was used. Three *ideas* were taken
from general knowledge and from the coordinator's guidance, and every geometry was then found by
our own search: that a kickback returns a glider; that half of the gun (a queen bee shuttle) can
turn a glider by a right angle; that a salvo can be assembled from gliders of several streams.

Conventions as in `R-20`: cells `(x, y)`, `y` downward; windows `ofRows x0 y0 [rows]`;
symmetries `sym_k`; a glider world line is `(direction, lane, tau)` with `lane = dy x - dx y`,
`tau = t - 4 dx x` for the canonical box origin `(x, y)`; directions SE `(1, 1)`, SW `(-1, 1)`,
NW `(-1, -1)`, NE `(1, -1)`. An *assembly* `(k, vx, vy, s)` is `blockedStream` transformed by
`sym_k`, translated by `(vx, vy)` and delayed by `s` generations; a *reflector* `(k, p, q, s)`
is the same for the oscillator `RF0` of section 3.1.

## Summary

| Goal | Result |
| --- | --- |
| (a) fan-out | **Achieved.** One control glider into the certified gate `S = blockedStream`, a second assembly `K`: two gliders out, both assemblies back in their cycle. 77 verified placements, all reusable; recommended `F1` (`K = (0, 35, 62, 25)`, 810 generations, reuse spacing 450) and `F2` (`K = (7, 90, 132, 25)`, 690 generations, reuse spacing 330) |
| (b) pull-salvo generator | **Achieved, from one control glider**: `PG1` = `S`, `K`, a third gate `Gb` and three reflectors (6 guns, 3 queen bee shuttles with eaters; envelope 177 × 133, period 30). `evolve 1170 (R ∪ C) = R ∪ translate (51, 143) pullSalvo`; with the block `counter k` in place (`k = 0 .. 3`) the block ends at `k - 1` and everything else is restored; reuse spacing 330 generations (82 cells between salvos). 46 placements verified |
| (c) push-salvo generator | **Not achieved.** It needs a third glider (same lane as the second, 25 generations later), hence one more fan-out stage; the method of `PG1` applies (section 5) |
| (d) continue glider | **Not achieved** in `PG1`; same remark. The fan-out alone provides it for components with one output |
| new component | **Reflector `RF0`** (period 30, 27 cells, 23 × 9): `evolve 30 (RF0 ∪ ofRows 20 0 [1, 5, 3]) = RF0 ∪ ofRows 11 (-4) [2, 3, 5]`, a right-angle turn; works for inputs 30 generations apart |

Obstructions found (section 2), each of which changed the design:

1. **A gun shadows 48 parallel lanes.** No glider can pass a gun on a lane within `-23 .. +24`
   of its stream. The salvo lanes are 6 apart (or equal), so at most one glider of a salvo can
   come straight from a gun: "one gate per salvo glider" (the approach suggested for D1) is
   impossible.
2. **A period-30 stream is opaque.** A glider crossing it at a right angle interacts for every
   lane and phase (60 classes: 33 clean deletions of one stream glider, 1 kickback, 26 dirty).
   Signals cannot cross a live stream; a layout is a planar routing problem, and a glider
   returned by a kickback can only act on the gate it came from.
3. **No right-angle turn or insertion by collisions of 2 – 5 gliders** from gate-suppliable
   lanes, **and parity**: kickbacks keep the parity of `tau`, a reflection changes the parities
   of lane and `tau` together, and the two gliders of the pull salvo differ by `(6, 29)`. The
   two outputs of the fan-out can never be brought to such a pair by reflectors alone; one of
   them has to be re-timed by a gate.

## 1. Method and cross-checks

* `python3 common.py`: the simulator of `scripts/life_gates` reproduces `blockedStream_start`,
  least period 30 of `blockedStream`, the gate
  `evolve 90 (blockedStream ∪ ofRows 47 6 [2, 4, 7]) = blockedStream ∪ ofRows 45 32 [5, 6, 2]`,
  and `pull`, `push` for `k = 0 .. 5`. The salvos as world lines:
  `pullSalvo = {(SE, -5, 0), (SE, 1, -29)}`, `pushSalvo = pullSalvo ∪ {(SE, 1, -4)}`.
  So the second glider is 6 lanes to the right of the first and 29 generations ahead; the third
  one is on the lane of the second, 25 generations behind it (not 30).
* Composites are run on a bit-parallel board (`machine.run_scheduled`): control gliders are
  inserted when they are 4 cells outside the bounding box of the whole composite, gliders flying
  away are removed 13 cells outside it, and success means that the configuration is exactly the
  periodic cycle again. Every accepted run is repeated with the set simulator on the unbounded
  plane (`machine.verify_scheduled`): cycle at a time `≡ 0 (mod 30)` plus the control gliders
  evolves to the cycle plus exactly the stated gliders in free flight.
* "Envelope" of a piece = all its cells over a cycle. Distances are Chebyshev distances.

## 2. Obstructions

### 2.1 The shadow of a gun (`r0_obstruction.py`)

A glider flying SE or NW on the lanes `x - y = -40 .. 70`, all 30 phases, past the free gun
(stream lane 14): it passes unchanged for all phases on the lanes `≤ -11` and `≥ 39` (SE) and
`≤ -12`, `≥ 38` (NW); for 25 of 30 phases on lane `-10` (SE), `-11` (NW); for **no** phase on
the lanes `-9 .. 38` (SE), `-10 .. 37` (NW). Hence two guns firing in the same direction have
stream lanes at least 24 apart (25 for all phases), whichever is in front, and a glider can be
put on a lane within 23 of a stream only by a reaction in front of that gun. Salvo lanes: `-5`,
`1`, `1`.

### 2.2 A period-30 stream cannot be crossed (`r4_stream.py one`)

One glider against a stream `(SW, 0, 30 j)`. Up to the symmetry of the stream there are 60
classes of an SE glider (2 lane parities × 30 phases): 33 delete exactly one stream glider and
vanish (the gate), 1 is the kickback, 18 leave permanent debris, 8 do not settle; **none
passes**. (Head-on, lane offsets `-12 .. 12` × 2 parities: 19 clean deletions, 24 pass — the
lanes with offset `≤ -8` or `≥ 6` —, 7 dirty.) Consequences observed:

* `f1_fanout.py`: a kickback returns the control glider on the line on which it came (2 lanes
  off). A second assembly on that line would have to let the control glider through first:
  40 981 placements, 2 173 world lines of the control glider in the frame of the second
  assembly, **0 pass**.
* `s1_shifter.py`: a "permanent lane shifter" from two terminated guns (two kickbacks) does not
  exist in the range searched (1 020 placements, 0 work): the glider cannot cross the second
  stream on its way in.
* For the layout: a signal path may cross only the dead part of a blocked stream. The assemblies
  of `PG1` are therefore placed so that every path goes around the guns.

### 2.3 What collisions of few gliders can do

Gates can supply, at one place, SE gliders on one lane (30 n generations apart), gliders from
the two sides (SW and NE, one lane each), and nothing from the side of the register (NW).

* Two gliders (`R-19`; the roots of `r1_recipes.py` agree): exactly two collisions leave one
  glider, the kickback `SE (0, 0) + SW (6, 7) → NW (2, 12)` and the head-on side step
  `SE (0, 0) + NW (-4, 18) → SE (6, -13)` (the SE glider moves 6 lanes; world lines in the
  convention above, `reactions.py`). No right-angle turn.
* `r1_recipes.py` (slow recipes: each further glider arrives after the debris has settled; one
  lane per direction; up to 5 gliders, 51 511 runs): the only recipes ending with one SE glider
  are lane shifts of an SE glider by `±12` (SE + SW leave a traffic light and an SE glider 12
  lanes over; a third glider removes the traffic light) and by `±13` (4 gliders). From the two
  sides alone (SW and NE, up to 9 gliders): nothing.
* `r3_headon.py` (two head-on gated streams, all subsets of 4 + 4 consecutive gliders, lane
  offsets `-12 .. 12`, 8 phases; 41 800 runs): never a glider at a right angle.
* `r2_three.py` (all collisions SE + SW + NE, 2 650 252 runs, 707 575 with gliders only):
  single SE gliders come out with lane shifts from `-16` to `+7` and beyond (`±12` as above); for
  the shift `+6` the `tau` shifts are `-20, -15, -7, -4, 16, 18, 26, 43, 200`, for `-6`:
  `4, 17, 20, 40, 42, 50, 67`. A second salvo glider made from a glider of the same gun would
  need `+6` with `tau ≡ 1` or `-6` with `tau ≡ 29 (mod 30)`: not available. No outcome with two
  SE gliders.
* `b1_single_lane.py`: salvos on a single lane (what one gate emits; spacings 30 .. 180, up to
  16 gliders, all lanes): the block is never moved diagonally; the only single-block outcomes
  are the knight's moves `(-2, -1)`, `(-1, -2)` by one glider.

### 2.4 Parity

For a glider let `(λ, τ) = (lane mod 2, tau mod 2)`.

* A kickback keeps `τ` of the glider that comes back; two kickbacks move an SE glider by `0` or
  `±2` lanes with an even delay `≡ 40 + 8 j`. The side step moves by `±6` lanes and changes `τ`
  (`tau` shifts `-13` and `+11`).
* A reflection by `RF0` (any of its 8 images) changes both: `(λ, τ) → (1 - λ, 1 - τ)`.
* `pullSalvo`: the two gliders have equal `λ` and different `τ`.
* Guns that are translates of each other and run synchronously give streams with equal `τ`
  (`tau ≡ 29 - 4 vx`); so even without obstruction 2.1 the two salvo gliders need guns with an
  odd relative delay (or of different orientation).
* The fan-out gives `G1` with `(λ, τ) = (1, 0)` and `G2 = (SW, 75, ·)` with `(1, 1)`. `G2`
  needs an odd number of reflections to fly SE, `G1` an even number: the results are `(0, 0)`
  and `(1, 0)`, never equal `λ`. `g2_pull.py` confirms: no solution for any of the 77 fan-outs
  with up to 3 reflectors. A gate in one of the two paths removes the obstruction, because the
  position and the delay of its guns are free.

### 2.5 The salvo from kickbacks alone (`r5_synth.py`): possible, but expensive

A free-glider synthesis that respects 2.1 – 2.4, verified with the block (`counter k` far down
the diagonal, `k = 300 .. 303`, ends as `counter (k - 1)`, nothing else left): three gliders of
one gun lane and seven kicker gliders from the sides.

```text
VERIFIED synthesis (free gliders -> pull salvo -> counter k -> counter (k - 1), k = 300 .. 303):
  parameters j1=4 j2=6 jH=6 j6=-2 j7=8 order=['SW', 'NE']
   e1  SE lane   -5 tau     0 (tau mod 30 =  0)
   k1  NE lane   -9 tau   -17 (tau mod 30 = 13)
   k2  NE lane   27 tau   115 (tau mod 30 = 25)
   k3  NE lane   -9 tau   103 (tau mod 30 = 13)
   k4  NE lane   27 tau   235 (tau mod 30 = 25)
   k5  NE lane   -9 tau   223 (tau mod 30 = 13)
   e2  SE lane   -5 tau   330 (tau mod 30 =  0)
   k6  SW lane    3 tau   316 (tau mod 30 = 16)
   k7  NE lane   27 tau   416 (tau mod 30 = 26)
   a   SE lane   -5 tau   450 (tau mod 30 =  0)
   -> a = SE lane -5 tau 450,  b = SE lane 1 tau 421
```

`e1` is kicked five times (each kick moves it one half-lane to the right) and becomes an NW
glider 5 lanes off; `e2` side-steps against it onto lane 1; two more kicks delay it by the right
amount; `a` is direct. In gates this is 5 glider classes (5 gun pairs; the minimum over the 14 112 parameter
choices tried) and 10 control events for
one decrement; the push salvo would need about twice as many. This is why the reflector was
looked for.

## 3. Components

### 3.1 Reflector `RF0` (`q1_reflector.py`)

Search: the left half of `gosperGun` (cells with `x ≤ 17`: block and queen bee) plus one
stabiliser, a block or eater 1 in its 8 orientations, at 483 positions: 6 oscillators of least
period 30 (4 distinct). Each with every glider world line from infinity (4 directions, all
lanes, 30 phases). Two of them (mirror images of each other) turn a glider by a right angle:

```text
RF0 = ofRows 0 2 [12288, 34816, 66563, 214019, 66560, 1607680, 2633728, 2097152, 6291456]
    = (cells of gosperGun with x ≤ 17) ∪ translate (19, 7) eater1        27 cells, box x 0..22, y 2..10
least period 30; envelope over a cycle x 0..22, y 2..10
evolve 30 (RF0 ∪ ofRows 20 0 [1, 5, 3]) = RF0 ∪ ofRows 11 (-4) [2, 3, 5]
   in  (SW, lane 19, tau 18)   out (NW, lane -14, tau 13)        (times: RF0 at time 0 mod 30)
....................O..        (input glider at the upper right, flying SW)
....................O.O
............OO......OO.
...........O...O.......
OO........O.....O......
OO........O...O.OO.....
..........O.....O......
...........O...O...OO..
............OO.....O.O.
.....................O.
.....................OO
```

* One input lane and one phase (of 30). Inputs 30, 60, 90 generations apart all work (tested 2
  and 3 in a row).
* The 8 images give all 8 right-angle turns (`g2_pull.TURN`): `SW→NW, NW→NE, NE→SE, SE→SW`
  and the mirror images `SE→NE, NW→SW, NE→NW, SW→SE`.
* A copy turning a given glider onto a given outgoing lane is unique if it exists
  (`g2_pull.reflect`): the outgoing lane must have the right parity (2.4), and `tau + 4 lane`
  of the outgoing glider does not depend on the position of the reflector.
* Next to the reflector: a glider parallel to the outgoing one passes for all phases on the
  lanes 4 or more to the far side of the outgoing lane (`x - y ≥ 18` for the output on 14), and
  for no phase on the other side up to 11 lanes off. So the second salvo glider, 6 lanes away,
  passes the reflector that makes the first — on one side only; the mirror image serves the
  other side.
* The same oscillator also returns an SE glider `(SE, 17, 24)` as `(NW, -17, 163)` (a 180° turn
  taking 150 generations), not used.

Proposed Lean statements: `IsOscillator RF0 30`;
`conway.evolve 30 (RF0 ∪ ofRows 20 0 [1, 5, 3]) = RF0 ∪ ofRows 11 (-4) [2, 3, 5]`.

### 3.2 Fan-out by a round trip (`f2_roundtrip.py`)

`S = blockedStream`. The control glider `C = (SE, 41, 22)` is the one of the certified gate; `S`
releases `G0 = (SE, 14, 119)`. `K` is placed so that `G0` is one of its kickback control gliders
(`R-20` §3.4): `K` releases a glider `G1` of its own stream and sends `G0` back as `X`, 2 lanes
off. `X` meets the stream A of `S` head-on, in `S` it is the control glider `(NW, -12, 11)` of
the catalogue: a gate from infinity that releases one glider `G2` of stream B of `S`. (The
phases `8, 10, 26, 28` on that lane would do the same but have the wrong parity; a phase that
releases stream A again would start the round trip anew.)

Enumeration: 47 kickbacks × symmetries × `|vx| ≤ 160`: 521 placements satisfy the lane, phase
and clearance conditions, **77 are verified**, all with a second control glider later. `G2` is
always `(SW, 75, ·)`; `G1` flies SE (`K` a translate or mirror image of `S`) or NW.

**F1** (smallest box; `K` = `blockedStream` translated by `(35, 62)`, delayed by 25). In the data
block the two gliders at the end are listed in the order `G1 = (SW, 75, 891)` (from `S`) and
`G2 = (SE, -13, 214)` (from `K`):

```text
Fan-out: S and K = (k, vx, vy, s) = (0, 35, 62, 25)
 pieces at world time 0 (mod 30):
  S = blockedStream:                 ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744]   -- 102 cells, box x 0..90, y 0..27
  K = assembly (0, 35, 62, 25):      ofRows 35 62 [12582912, 442721857769046016000, 73786976346411374592, 906731366285561930323968, 916176099251249681105667, 1864220319137040770576188291, 1873879956671238777276924672, 7290595979787783828019200, 916139097676711171463168, 906694364710971881029632, 33554432, 36893488147486212096, 18446744073826992128, 129127208515966861312, 0, 0, 0, 0, 8589934592, 144115198813274112, 720575953264181248, 432345564227567616, 0, 0, 0, 1099511627776, 1128098930098176, 566798244118528, 3940649673949184]   -- 118 cells, box x 35..125, y 62..90
  whole periodic configuration R:    ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 432345564227567616, 15211807202739329278712741888000, 2535301202228499366680362745856, 31155052515631083901792585959604224, 31479571069287739739834151082131456, 64054122425858184414746942289465049088, 64386025044262940577691355213564215296, 250502970412300868493281219680665600, 31478299704867392498177240228429824, 31153781151208965771182977975320576, 1152921504606846976, 1267650600230535244505916899328, 633825300118149926014475567104, 4436777100798802905238461218816, 0, 0, 0, 0, 295147905179352825856, 4951760526076402573787529216, 24758801228429463267011723264, 14855280471424563298789490688, 0, 0, 0, 37778931862957161709568, 38761184091394047914016768, 19475039375354416861282304, 135399691796838467567091712]   -- 220 cells, box x 0..125, y 0..90
  period 30 (least), envelope over a cycle: x 0..125, y 0..94 (126 x 95)
 minimum Chebyshev distance between the envelopes (all cells over a cycle) of the pieces:
    S = blockedStream -- K = assembly (0, 35, 62, 25): 30
    minimum: 30
 reaction (set simulator, unbounded plane):  evolve 810 (R ∪ C) = R ∪ G   (world times 150 -> 960, both = 0 mod 30)
  C1 (SE, lane 41, tau 22):          ofRows 32 -9 [2, 4, 7]   -- 5 cells, box x 32..34, y -9..-7
  G1 (SW, lane 75, tau 891):         ofRows -17 93 [5, 3, 2]   -- 5 cells, box x -17..-15, y 93..95
  G2 (SE, lane -13, tau 214):        ofRows 186 200 [4, 5, 6]   -- 5 cells, box x 186..188, y 200..202
  start R ∪ C:                       ofRows 0 -9 [8589934592, 17179869184, 30064771072, 0, 0, 0, 0, 0, 0, 16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 432345564227567616, 15211807202739329278712741888000, 2535301202228499366680362745856, 31155052515631083901792585959604224, 31479571069287739739834151082131456, 64054122425858184414746942289465049088, 64386025044262940577691355213564215296, 250502970412300868493281219680665600, 31478299704867392498177240228429824, 31153781151208965771182977975320576, 1152921504606846976, 1267650600230535244505916899328, 633825300118149926014475567104, 4436777100798802905238461218816, 0, 0, 0, 0, 295147905179352825856, 4951760526076402573787529216, 24758801228429463267011723264, 14855280471424563298789490688, 0, 0, 0, 37778931862957161709568, 38761184091394047914016768, 19475039375354416861282304, 135399691796838467567091712]   -- 225 cells, box x 0..125, y -9..90
  end R ∪ G:                         ofRows -17 0 [2199023255552, 9671406556919782176718848, 48357032791340980356775936, 59653249810170466421958508544, 84412050595871316524661080064, 243550079562684510534682276134912, 243561037266313497532952729354240, 160941876513656352774847201280, 84179922671405858694751059968, 59421121885698254294669590528, 19342813113840663865065472, 14507109835378848631357440, 29014219670751100192948224, 0, 0, 0, 0, 703687441776640, 188894660159210738679808, 113336795870346461839360, 75557863725914323419136, 0, 0, 0, 36028797018963968, 590511983140819435520, 442829944160086130688, 885443715538058477568, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56668397794435742564352, 1993841993677449367219436504743936000, 332306999178493868989528505824837632, 4083555043328797429175757826897244848128, 4126090339193682623179541850637134200832, 8395701934602083947609711219764762914062336, 8439205074601632147399161310552288827277312, 32833925337881099435151356025984201523200, 4125923698916378869521087231220753891328, 4083388403051261561560495289181218537472, 151115727451828646838272, 166153499473416715567879539828719616, 83076749737086147102569341531455488, 581537248155900694395415588872650752, 0, 0, 0, 0, 38685626227668133590597632, 649037155673886238151479029399552, 3245185594612706609333760591659008, 1947111321950560360698936123457536, 0, 0, 0, 4951760157141521099596496896, 5080505921227200648186005815296, 2552632361006454126841994149888, 17747108403195211620953844875264, 0, 0, 5, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51422017416287688817342786954917203280710495801049370729644032, 64277521770359611021678483693646504100888119751311713412055040, 77133026124431533226014180432375804921065743701574056094466048]   -- 230 cells, box x -17..188, y 0..202
 second control glider(s) 420 generations later: FAILS
 second control glider(s) 450 generations later: works (set simulator)
 gun bodies at world time 0 (the streams in flight belong to the assemblies as well):
  S gun A:                           ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  S gun B:                           ofRows 55 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792, 12582912]   -- 36 cells, box x 55..90, y 1..9
  K gun A:                           ofRows 35 62 [12582912, 16777216, 51573168128, 51573299200, 33653507, 17597315, 14615296, 137216, 6144]   -- 44 cells, box x 35..70, y 62..70
  K gun B:                           ofRows 90 63 [12288, 2048, 25166851, 25428995, 51742508032, 52010616832, 202354688, 25427968, 25165824]   -- 44 cells, box x 90..125, y 63..71
```

Picture of the start configuration of F1 (control glider at the top):

```text
.................................O............................................................................................
..................................O...........................................................................................
................................OOO...........................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
........................O.....................................................................................................
......................O.O.........................................O...........................................................
............OO......OO............OO..............................O.O.........................................................
...........O...O....OO............OO...................OO............OO......OO...............................................
OO........O.....O...OO.................................OO............OO....O...O..............................................
OO........O...O.OO....O.O............................................OO...O.....O........OO...................................
..........O.....O.......O.........................................O.O....OO.O...O........OO...................................
...........O...O..................................................O.......O.....O.............................................
............OO.............................................................O...O..............................................
.......................O.....................................................OO...............................................
........................OO.........................................O..........................................................
.......................OO........................................OO...........................................................
..................................................................OO..........................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................O.O.............................................................................................
...............................OO.........................O.O.................................................................
...............................O..........................OO..................................................................
...........................................................O..................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
......................................O.......................................................................................
.......................................OO...........O.........................................................................
......................................OO..........OO..........................................................................
...................................................OO.........................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
.........................................................OO...................................................................
...........................................................O..........................................OO......................
..............................................OO............O........OO..............................O........................
..............................................OO....O.......O........OO...................OO........O............OO...........
...................................OO......OO.....OO........O.............................OO........O.......O....OO...........
...................................OO.....OOO.....O..OO....O........................................O........OO.....OO......OO
...........................................OO......OOOOO.OO..........................................O....OO..O.....OOO.....OO
..............................................OO....O.................................................OO.OOOOO......OO........
..............................................OO............................................................O....OO...........
.................................................................................................................OO...........
............................................................O.................................................................
.............................................................O......................................O.........................
...........................................................OOO.....................................O..........................
...................................................................................................OOO........................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
....................................................................O.........................................................
..................................................................O.O.......................O.................................
...................................................................OO.......................O.O...............................
............................................................................................OO................................
..............................................................................................................................
..............................................................................................................................
..............................................................................................................................
...........................................................................O..................................................
............................................................................O........O........................................
..........................................................................OOO.......O.........................................
....................................................................................OOO.......................................
```

Clearances of F1: the envelopes of `S` and `K` are 30 apart; the glider from `S` passes the
envelope of `K` at distance 11; `C` and the glider from `K` stay more than 40 away from the other
assembly. Reuse: a second `C` 450 generations later works, 420 fails (the returning `X` meets
the next `G0`).

**F2** (`K` = `sym_7 blockedStream` translated by `(90, 132)`, delayed by 25; the glider from
`K` flies NW; used in `PG1`):

```text
Fan-out: S and K = (k, vx, vy, s) = (7, 90, 132, 25)
 pieces at world time 0 (mod 30):
  S = blockedStream:                 ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744]   -- 102 cells, box x 0..90, y 0..27
  K = assembly (7, 90, 132, 25):     ofRows 62 42 [12582912, 12582912, 0, 0, 0, 0, 0, 4194304, 14680064, 14680064, 0, 51904512, 51904512, 0, 0, 12582912, 10485760, 19922944, 6291456, 6291456, 2097152, 0, 136314880, 136314880, 71335936, 58884096, 98304, 0, 0, 0, 0, 256, 128, 896, 50331648, 50331648, 0, 0, 0, 1, 5, 3, 0, 0, 0, 0, 0, 0, 0, 6, 10, 2, 0, 0, 0, 100663296, 100663296, 1792, 256, 512, 0, 0, 0, 0, 196608, 117768192, 142671872, 272629760, 272629760, 0, 4194304, 12582912, 12582912, 39845888, 20971520, 25165824, 0, 0, 103809024, 103809024, 0, 29360128, 29360128, 8388608, 0, 0, 0, 0, 0, 25165824, 25165824]   -- 118 cells, box x 62..90, y 42..132
  whole periodic configuration R:    ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58028439341502200385896448, 58028439341502200385896448, 0, 0, 0, 0, 0, 19342813113834066795298816, 67699845898419233783545856, 67699845898419233783545856, 0, 239367312283696576591822848, 239367312283696576591822848, 0, 0, 58028439341502200385896448, 48357032784585166988247040, 91878362290711817277669376, 29014219670751100192948224, 29014219670751100192948224, 9671406556917033397649408, 0, 628641426199607170847211520, 628641426199607170847211520, 328978938662630964166918144, 271554962230936078368374784, 453347182355485940514816, 0, 0, 0, 0, 1180591620717411303424, 590295810358705651712, 4132070672510939561984, 232113757366008801543585792, 232113757366008801543585792, 0, 0, 0, 4611686018427387904, 23058430092136939520, 13835058055282163712, 0, 0, 0, 0, 0, 0, 0, 27670116110564327424, 46116860184273879040, 9223372036854775808, 0, 0, 0, 464227514732017603087171584, 464227514732017603087171584, 8264141345021879123968, 1180591620717411303424, 2361183241434822606848, 0, 0, 0, 0, 906694364710971881029632, 543109924461872156736749568, 657957877325261928333836288, 1257282852399214341694423040, 1257282852399214341694423040, 0, 19342813113834066795298816, 58028439341502200385896448, 58028439341502200385896448, 183756724581423634555338752, 96714065569170333976494080, 116056878683004400771792896, 0, 0, 478734624567393153183645696, 478734624567393153183645696, 0, 135399691796838467567091712, 135399691796838467567091712, 38685626227668133590597632, 0, 0, 0, 0, 0, 116056878683004400771792896, 116056878683004400771792896]   -- 220 cells, box x 0..90, y 0..132
  period 30 (least), envelope over a cycle: x 0..90, y 0..132 (91 x 133)
 minimum Chebyshev distance between the envelopes (all cells over a cycle) of the pieces:
    S = blockedStream -- K = assembly (7, 90, 132, 25): 23
    minimum: 23
 reaction (set simulator, unbounded plane):  evolve 690 (R ∪ C) = R ∪ G   (world times 150 -> 840, both = 0 mod 30)
  C1 (SE, lane 41, tau 22):          ofRows 32 -9 [2, 4, 7]   -- 5 cells, box x 32..34, y -9..-7
  G1 (NW, lane 29, tau 730):         ofRows -27 1 [3, 5, 1]   -- 5 cells, box x -27..-25, y 1..3
  G2 (SW, lane 75, tau 771):         ofRows -17 93 [5, 3, 2]   -- 5 cells, box x -17..-15, y 93..95
  start R ∪ C:                       ofRows 0 -9 [8589934592, 17179869184, 30064771072, 0, 0, 0, 0, 0, 0, 16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58028439341502200385896448, 58028439341502200385896448, 0, 0, 0, 0, 0, 19342813113834066795298816, 67699845898419233783545856, 67699845898419233783545856, 0, 239367312283696576591822848, 239367312283696576591822848, 0, 0, 58028439341502200385896448, 48357032784585166988247040, 91878362290711817277669376, 29014219670751100192948224, 29014219670751100192948224, 9671406556917033397649408, 0, 628641426199607170847211520, 628641426199607170847211520, 328978938662630964166918144, 271554962230936078368374784, 453347182355485940514816, 0, 0, 0, 0, 1180591620717411303424, 590295810358705651712, 4132070672510939561984, 232113757366008801543585792, 232113757366008801543585792, 0, 0, 0, 4611686018427387904, 23058430092136939520, 13835058055282163712, 0, 0, 0, 0, 0, 0, 0, 27670116110564327424, 46116860184273879040, 9223372036854775808, 0, 0, 0, 464227514732017603087171584, 464227514732017603087171584, 8264141345021879123968, 1180591620717411303424, 2361183241434822606848, 0, 0, 0, 0, 906694364710971881029632, 543109924461872156736749568, 657957877325261928333836288, 1257282852399214341694423040, 1257282852399214341694423040, 0, 19342813113834066795298816, 58028439341502200385896448, 58028439341502200385896448, 183756724581423634555338752, 96714065569170333976494080, 116056878683004400771792896, 0, 0, 478734624567393153183645696, 478734624567393153183645696, 0, 135399691796838467567091712, 135399691796838467567091712, 38685626227668133590597632, 0, 0, 0, 0, 0, 116056878683004400771792896, 116056878683004400771792896]   -- 225 cells, box x 0..90, y -9..132
  end R ∪ G:                         ofRows -27 0 [2251799813685248, 9903520314285856948960100355, 49517601578333163885338558469, 61084927805614557616085512749057, 86437939810172228121252945985536, 249395281472188938787514650762149888, 249406502160705021473743594858741760, 164804481549984105241443534110720, 86200240815519599303425085407232, 60847228810955012397741660700672, 19807040628572839797827043328, 14855280471427940998510018560, 29710560942849126597578981376, 0, 0, 0, 0, 720575940379279360, 193428132003031796408123392, 116056878971234776923504640, 77371252455336267181195264, 0, 0, 0, 36893488147419103232, 604684270736199101972480, 453457862819928197824512, 906694364710971881029632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7788445287802241442795744493830144, 7788445287802241442795744493830144, 0, 0, 0, 0, 0, 2596148429267413814265248164610048, 9086519502435948349928368576135168, 9086519502435948349928368576135168, 0, 32127336812184245951532446037049344, 32127336812184245951532446037049344, 0, 0, 7788445287802241442795744493830144, 6490371073168534535663120411525120, 12331705039020215617759928781897728, 3894222643901120721397872246915072, 3894222643901120721397872246915072, 1298074214633706907132624082305024, 0, 84374823951190948963620565349826560, 84374823951190948963620565349826560, 44154805707149686512933166049656832, 36447490057762051751833210560970752, 60847228810955011271841753858048, 0, 0, 0, 0, 158456325028528675187087900672, 79228162514264337593543950336, 554597137599850363154807652352, 31153781151208965771182977975320576, 31153781151208965771182977975320576, 0, 0, 0, 618970019642690137449562112, 3094850098213450687247810560, 1856910058928070412348686336, 0, 0, 0, 0, 0, 0, 0, 3713820117856140824697372672, 6189700196426901374495621120, 1237940039285380274899129344, 3072, 2048, 0, 62307562302417931542365955950641152, 62307562302417931542365955950641152, 1109194275199700726309615304704, 158456325028528675187087900672, 316912650057057350374175801344, 0, 0, 0, 0, 121694457621910022543683507716096, 72894980115524103503666421121941504, 88309611414299373025866332099313664, 168749647902381897927241130699653120, 168749647902381897927241130699653120, 0, 2596148429267413814265248164610048, 7788445287802241442795744493830144, 7788445287802241442795744493830144, 24663410078040431235519857563795456, 12980742146337069071326240823050240, 15576890575604482885591488987660288, 0, 0, 64254673624368491903064892074098688, 64254673624368491903064892074098688, 0, 18173039004871896699856737152270336, 18173039004871896699856737152270336, 5192296858534827628530496329220096, 0, 0, 0, 0, 0, 15576890575604482885591488987660288, 15576890575604482885591488987660288]   -- 230 cells, box x -27..90, y 0..132
 second control glider(s) 300 generations later: FAILS
 second control glider(s) 330 generations later: works (set simulator)
 gun bodies at world time 0 (the streams in flight belong to the assemblies as well):
  S gun A:                           ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  S gun B:                           ofRows 55 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792, 12582912]   -- 36 cells, box x 55..90, y 1..9
  K gun A:                           ofRows 82 97 [96, 96, 0, 0, 0, 0, 0, 0, 0, 0, 112, 136, 260, 260, 0, 4, 12, 12, 38, 20, 24, 0, 0, 99, 99, 0, 28, 28, 8, 0, 0, 0, 0, 0, 24, 24]   -- 44 cells, box x 82..90, y 97..132
  K gun B:                           ofRows 81 42 [24, 24, 0, 0, 0, 0, 0, 8, 28, 28, 0, 99, 99, 0, 0, 24, 20, 38, 12, 12, 4, 0, 260, 260, 136, 112, 0, 0, 0, 0, 0, 0, 0, 0, 96, 96]   -- 44 cells, box x 81..89, y 42..77
```

Clearances of F2: envelopes 23 apart; the glider from `K` passes the envelope of `S` at distance
11, the glider from `S` that of `K` at 32. Reuse spacing 330 (300 fails).

Proposed Lean statements (F1): with `R` the window "whole periodic configuration",
`IsOscillator R 30` and `conway.evolve 810 (R ∪ ofRows 32 (-9) [2, 4, 7]) = R ∪ G1 ∪ G2`.

### 3.3 Pull-salvo generator `PG1` (`g4_pull3.py`)

```text
C ──► S ──G0──► K ──G1 (NW)──► RF1 ──(SW)──► RF2 ──► a = (SE, -97, 1116)
      ▲         │
      └────X────┘
      S ──G2 (SW)──► Gb ──o (NE)──► RF3 ──► b = (SE, -91, 1087)
```

* `S`, `K`: the fan-out F2.
* Path 1: `G1 = (NW, 29, 730)` is turned by `RF1` onto the SW lane `-2` and by `RF2` onto the SE
  lane `-97`. The length of the NW leg delays the glider as needed (with F1, where `G1` flies
  SE, `G2` is about 500 generations late for every position of the reflectors: no causal
  solution).
* Path 2: `G2 = (SW, 75, 771)` is the control glider `(NE, -46, 14)` of the gate
  `Gb = (2, 4, 121, 29)` (`blockedStream` rotated by 180°, translated by `(4, 121)`, delayed by
  29; a repeatable gate "against stream B" of `R-20` §3.2), which releases `o = (NE, -46, 1092)`;
  `RF3` turns `o` onto the SE lane `-91`.
* Enumeration: the SW lane of path 1 in `-160 .. 130`, final lanes in `-420 .. -91`, all 712
  repeatable gates in the 2 symmetries that fit, `vx` in `-150 .. 39`: 3 821 827 exact solutions
  of the lane and timing equations; of the 254 000 with the smallest boxes, 130 are causal, keep
  every flight segment clear of the pieces it does not use and have pieces at least 4 apart;
  the logged run (`results/g4_pull3.txt`) was stopped after 45 of these 130 had been simulated,
  **all 45 verified**; `PG1` is a 46th of the 130 (verified in an earlier run of the same search,
  which had checked 41, and again by `report_data.py`). The remaining simulations are slow for
  a reason that was not investigated.

```text
Pull-salvo generator: fan-out (S, K), gate Gb, three reflectors
 pieces at world time 0 (mod 30):
  S = blockedStream:                 ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744]   -- 102 cells, box x 0..90, y 0..27
  K = assembly (7, 90, 132, 25):     ofRows 62 42 [12582912, 12582912, 0, 0, 0, 0, 0, 4194304, 14680064, 14680064, 0, 51904512, 51904512, 0, 0, 12582912, 10485760, 19922944, 6291456, 6291456, 2097152, 0, 136314880, 136314880, 71335936, 58884096, 98304, 0, 0, 0, 0, 256, 128, 896, 50331648, 50331648, 0, 0, 0, 1, 5, 3, 0, 0, 0, 0, 0, 0, 0, 6, 10, 2, 0, 0, 0, 100663296, 100663296, 1792, 256, 512, 0, 0, 0, 0, 196608, 117768192, 142671872, 272629760, 272629760, 0, 4194304, 12582912, 12582912, 39845888, 20971520, 25165824, 0, 0, 103809024, 103809024, 0, 29360128, 29360128, 8388608, 0, 0, 0, 0, 0, 25165824, 25165824]   -- 118 cells, box x 62..90, y 42..132
  Gb = assembly (2, 4, 121, 29):     ofRows -86 94 [1924145348608, 7882398859526144, 1126449662656512, 2251799813685248, 0, 0, 0, 6442450944, 864691133823844352, 1441151885053526016, 288230376151711744, 0, 0, 0, 0, 58720256, 258254417031967277056, 36893488147435880448, 73786976294838210560, 302231454903657293682688, 906694364710971889617920, 1841870502271751320440323, 1861170371365381780718947331, 1858753257595915522290489344, 909350803944028658208768, 303707302515945125183488, 737869762948390453248, 147573952589676412928]   -- 108 cells, box x -86..4, y 94..121
  RF1 = reflector (5, -32, 18, 0):   ofRows -32 8 [6291456, 2097152, 2633728, 1607680, 66560, 214019, 66563, 34816, 12288]   -- 27 cells, box x -32..-10, y 8..16
  RF2 = reflector (7, -45, 67, 13):  ofRows -55 45 [1, 7, 8, 12, 0, 0, 0, 0, 0, 0, 112, 136, 260, 428, 0, 0, 32, 80, 80, 32, 0, 96, 96]   -- 29 cells, box x -55..-47, y 45..67
  RF3 = reflector (2, -4, 73, 0):    ofRows -26 63 [3, 2, 1546, 2188, 4160, 6295904, 6295616, 2176, 1536]   -- 27 cells, box x -26..-4, y 63..71
  whole periodic configuration R:    ofRows -86 0 [1298074214633706907132624082305024, 5708990770825462117001436011431896325633867776, 28544953858107125948173660998918462398038802432, 35213063437224879564523737031076040234699040227328, 49828079810529921065029535762319719484278930669568, 143766591578382088934566006591292483758549153395769344, 143773059864925432344411035102131790713101812110458880, 95003315417279513525457504795921181736361640591360, 49691055669250699219876022375861590308295718993920, 35076039295941670685925543339823177901011583893504, 11417981541651573271110236321343116544275644416, 8563486156237706397671695338445865478415974400, 17126972312471518572699432832432306427713814528, 3855423554600824733696, 1199092407986649300992, 627189298506124754944, 221360928884514619392, 415383748682786210282439706337607680, 111503726491113614127022043702169455135031296, 66902235761745368897721638930920967052984320, 44601490397061246283071436545296723011960832, 0, 0, 0, 21267647932558653966460912964485513216, 348576749614636338510294363487917561610240, 261400660739078415901771081246491442937856, 522673715590561479879743397015195972796416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4489733029880533764721719806104421436383024772022272, 4489733029880533764721719806104421436383024772022272, 0, 2147483648, 15032385536, 17179869184, 25769803776, 1496577676626844588240573268701473812127674924007424, 5238021868193956058842006440455158342446862234025984, 5238021868193956058842006440455158342446862234025984, 0, 18520148748257201779477094200180738425079977184591872, 18520148748257201779477094200180738425079977184591872, 240518168576, 292057776128, 4489733029880533764721719806104421436383583117770752, 3741444191567111470601433171753684530320106433019904, 7108743963977511794142723026332000607606455889035264, 2244866514940266882360859903052210718191512386011136, 2244866514940266882360859903052210718191581105487872, 748288838313422294120286634350736906064009260695552, 3458764685619232768, 48638774490372449117818631232797901199992512963411968, 48638774490372449117818631232799681310795557215666176, 25453512515755005223435375046589307662580007108083712, 21010547538269060352096173155134080844033056879673344, 35076039295941670036888443243873905012008684617728, 7258351071146939531657216, 2508757194024499019776, 1770887431076116955136, 0, 91343852333181432387730302044767688728495783936, 45671926166590716193865151022383844364247891968, 319703483166135013357056057156686910549735243776, 17958932119522135058886879224417685745532099088089088, 17958932119522135058886879224417685745532099088089088, 0, 0, 0, 356811923176489970264571492362373784095686656, 1784059615882449851322857461811868920478433280, 1070435769529469910793714477087121352287059968, 0, 0, 0, 0, 0, 0, 0, 2140871539058939821587428954174242704574119936, 3568119231764899702645714923623737840956866560, 713623846352979940529142984724747568191373312, 1924145348608, 7882398859526144, 1126449662656512, 35917864239044270117773758448835371493315997989863424, 35917864239044270117773758448835371491064198176178176, 639406966332270026714112114313373821099470487552, 91343852333181432387730302044767688728495783936, 182687704666362864775460604089535377463434018816, 864691133823844352, 1441151885053526016, 288230376151711744, 0, 70152078591883340073776871970381584943484762062848, 42021095076538120704192346310258569381147372475645952, 50907025031510010446870750093173570140655442336940032, 97277548980744898235637262465595797788298870119202816, 97277548980744898235637262465596056042715902027759616, 36893488147435880448, 1496577676626844588240573268701547599103969762217984, 4489733029880533764721719806406652891286682065704960, 4489733029880533764721719807011115801093996661640192, 14217487927955023588285446054505871717484663098510851, 7482888383134222941202868204677740426020155338984451, 8979466059761067529443441470962100468681571834533888, 909350803944028658208768, 303707302515945125183488, 37040297496514403558954188400362214719922902759636992, 37040297496514403558954188400361624424112544045596672, 0, 10476043736387912117684012880910316684893724468051968, 10476043736387912117684012880910316684893724468051968, 2993155353253689176481146537402947624255349848014848, 0, 0, 0, 0, 0, 8979466059761067529443439612208842872766049544044544, 8979466059761067529443439612208842872766049544044544]   -- 411 cells, box x -86..90, y 0..132
  period 30 (least), envelope over a cycle: x -86..90, y 0..132 (177 x 133)
 minimum Chebyshev distance between the envelopes (all cells over a cycle) of the pieces:
    S = blockedStream -- K = assembly (7, 90, 132, 25): 23
    S = blockedStream -- Gb = assembly (2, 4, 121, 29): 71
    K = assembly (7, 90, 132, 25) -- Gb = assembly (2, 4, 121, 29): 54
    S = blockedStream -- RF1 = reflector (5, -32, 18, 0): 10
    K = assembly (7, 90, 132, 25) -- RF1 = reflector (5, -32, 18, 0): 72
    Gb = assembly (2, 4, 121, 29) -- RF1 = reflector (5, -32, 18, 0): 73
    S = blockedStream -- RF2 = reflector (7, -45, 67, 13): 48
    K = assembly (7, 90, 132, 25) -- RF2 = reflector (7, -45, 67, 13): 105
    Gb = assembly (2, 4, 121, 29) -- RF2 = reflector (7, -45, 67, 13): 22
    RF1 = reflector (5, -32, 18, 0) -- RF2 = reflector (7, -45, 67, 13): 30
    S = blockedStream -- RF3 = reflector (2, -4, 73, 0): 42
    K = assembly (7, 90, 132, 25) -- RF3 = reflector (2, -4, 73, 0): 62
    Gb = assembly (2, 4, 121, 29) -- RF3 = reflector (2, -4, 73, 0): 20
    RF1 = reflector (5, -32, 18, 0) -- RF3 = reflector (2, -4, 73, 0): 47
    RF2 = reflector (7, -45, 67, 13) -- RF3 = reflector (2, -4, 73, 0): 21
    minimum: 10
 reaction (set simulator, unbounded plane):  evolve 1170 (R ∪ C) = R ∪ G   (world times 150 -> 1320, both = 0 mod 30)
  C1 (SE, lane 41, tau 22):          ofRows 32 -9 [2, 4, 7]   -- 5 cells, box x 32..34, y -9..-7
  G1 (SE, lane -97, tau 1116):       ofRows 51 148 [2, 4, 7]   -- 5 cells, box x 51..53, y 148..150
  G2 (SE, lane -91, tau 1087):       ofRows 58 150 [5, 6, 2]   -- 5 cells, box x 58..60, y 150..152
  start R ∪ C:                       ofRows -86 -9 [664613997892457936451903530140172288, 1329227995784915872903807060280344576, 2326148992623602777581662355490603008, 0, 0, 0, 0, 0, 0, 1298074214633706907132624082305024, 5708990770825462117001436011431896325633867776, 28544953858107125948173660998918462398038802432, 35213063437224879564523737031076040234699040227328, 49828079810529921065029535762319719484278930669568, 143766591578382088934566006591292483758549153395769344, 143773059864925432344411035102131790713101812110458880, 95003315417279513525457504795921181736361640591360, 49691055669250699219876022375861590308295718993920, 35076039295941670685925543339823177901011583893504, 11417981541651573271110236321343116544275644416, 8563486156237706397671695338445865478415974400, 17126972312471518572699432832432306427713814528, 3855423554600824733696, 1199092407986649300992, 627189298506124754944, 221360928884514619392, 415383748682786210282439706337607680, 111503726491113614127022043702169455135031296, 66902235761745368897721638930920967052984320, 44601490397061246283071436545296723011960832, 0, 0, 0, 21267647932558653966460912964485513216, 348576749614636338510294363487917561610240, 261400660739078415901771081246491442937856, 522673715590561479879743397015195972796416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4489733029880533764721719806104421436383024772022272, 4489733029880533764721719806104421436383024772022272, 0, 2147483648, 15032385536, 17179869184, 25769803776, 1496577676626844588240573268701473812127674924007424, 5238021868193956058842006440455158342446862234025984, 5238021868193956058842006440455158342446862234025984, 0, 18520148748257201779477094200180738425079977184591872, 18520148748257201779477094200180738425079977184591872, 240518168576, 292057776128, 4489733029880533764721719806104421436383583117770752, 3741444191567111470601433171753684530320106433019904, 7108743963977511794142723026332000607606455889035264, 2244866514940266882360859903052210718191512386011136, 2244866514940266882360859903052210718191581105487872, 748288838313422294120286634350736906064009260695552, 3458764685619232768, 48638774490372449117818631232797901199992512963411968, 48638774490372449117818631232799681310795557215666176, 25453512515755005223435375046589307662580007108083712, 21010547538269060352096173155134080844033056879673344, 35076039295941670036888443243873905012008684617728, 7258351071146939531657216, 2508757194024499019776, 1770887431076116955136, 0, 91343852333181432387730302044767688728495783936, 45671926166590716193865151022383844364247891968, 319703483166135013357056057156686910549735243776, 17958932119522135058886879224417685745532099088089088, 17958932119522135058886879224417685745532099088089088, 0, 0, 0, 356811923176489970264571492362373784095686656, 1784059615882449851322857461811868920478433280, 1070435769529469910793714477087121352287059968, 0, 0, 0, 0, 0, 0, 0, 2140871539058939821587428954174242704574119936, 3568119231764899702645714923623737840956866560, 713623846352979940529142984724747568191373312, 1924145348608, 7882398859526144, 1126449662656512, 35917864239044270117773758448835371493315997989863424, 35917864239044270117773758448835371491064198176178176, 639406966332270026714112114313373821099470487552, 91343852333181432387730302044767688728495783936, 182687704666362864775460604089535377463434018816, 864691133823844352, 1441151885053526016, 288230376151711744, 0, 70152078591883340073776871970381584943484762062848, 42021095076538120704192346310258569381147372475645952, 50907025031510010446870750093173570140655442336940032, 97277548980744898235637262465595797788298870119202816, 97277548980744898235637262465596056042715902027759616, 36893488147435880448, 1496577676626844588240573268701547599103969762217984, 4489733029880533764721719806406652891286682065704960, 4489733029880533764721719807011115801093996661640192, 14217487927955023588285446054505871717484663098510851, 7482888383134222941202868204677740426020155338984451, 8979466059761067529443441470962100468681571834533888, 909350803944028658208768, 303707302515945125183488, 37040297496514403558954188400362214719922902759636992, 37040297496514403558954188400361624424112544045596672, 0, 10476043736387912117684012880910316684893724468051968, 10476043736387912117684012880910316684893724468051968, 2993155353253689176481146537402947624255349848014848, 0, 0, 0, 0, 0, 8979466059761067529443439612208842872766049544044544, 8979466059761067529443439612208842872766049544044544]   -- 416 cells, box x -86..90, y -9..132
  end R ∪ G:                         ofRows -86 0 [1298074214633706907132624082305024, 5708990770825462117001436011431896325633867776, 28544953858107125948173660998918462398038802432, 35213063437224879564523737031076040234699040227328, 49828079810529921065029535762319719484278930669568, 143766591578382088934566006591292483758549153395769344, 143773059864925432344411035102131790713101812110458880, 95003315417279513525457504795921181736361640591360, 49691055669250699219876022375861590308295718993920, 35076039295941670685925543339823177901011583893504, 11417981541651573271110236321343116544275644416, 8563486156237706397671695338445865478415974400, 17126972312471518572699432832432306427713814528, 3855423554600824733696, 1199092407986649300992, 627189298506124754944, 221360928884514619392, 415383748682786210282439706337607680, 111503726491113614127022043702169455135031296, 66902235761745368897721638930920967052984320, 44601490397061246283071436545296723011960832, 0, 0, 0, 21267647932558653966460912964485513216, 348576749614636338510294363487917561610240, 261400660739078415901771081246491442937856, 522673715590561479879743397015195972796416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4489733029880533764721719806104421436383024772022272, 4489733029880533764721719806104421436383024772022272, 0, 2147483648, 15032385536, 17179869184, 25769803776, 1496577676626844588240573268701473812127674924007424, 5238021868193956058842006440455158342446862234025984, 5238021868193956058842006440455158342446862234025984, 0, 18520148748257201779477094200180738425079977184591872, 18520148748257201779477094200180738425079977184591872, 240518168576, 292057776128, 4489733029880533764721719806104421436383583117770752, 3741444191567111470601433171753684530320106433019904, 7108743963977511794142723026332000607606455889035264, 2244866514940266882360859903052210718191512386011136, 2244866514940266882360859903052210718191581105487872, 748288838313422294120286634350736906064009260695552, 3458764685619232768, 48638774490372449117818631232797901199992512963411968, 48638774490372449117818631232799681310795557215666176, 25453512515755005223435375046589307662580007108083712, 21010547538269060352096173155134080844033056879673344, 35076039295941670036888443243873905012008684617728, 7258351071146939531657216, 2508757194024499019776, 1770887431076116955136, 0, 91343852333181432387730302044767688728495783936, 45671926166590716193865151022383844364247891968, 319703483166135013357056057156686910549735243776, 17958932119522135058886879224417685745532099088089088, 17958932119522135058886879224417685745532099088089088, 0, 0, 0, 356811923176489970264571492362373784095686656, 1784059615882449851322857461811868920478433280, 1070435769529469910793714477087121352287059968, 0, 0, 0, 0, 0, 0, 0, 2140871539058939821587428954174242704574119936, 3568119231764899702645714923623737840956866560, 713623846352979940529142984724747568191373312, 1924145348608, 7882398859526144, 1126449662656512, 35917864239044270117773758448835371493315997989863424, 35917864239044270117773758448835371491064198176178176, 639406966332270026714112114313373821099470487552, 91343852333181432387730302044767688728495783936, 182687704666362864775460604089535377463434018816, 864691133823844352, 1441151885053526016, 288230376151711744, 0, 70152078591883340073776871970381584943484762062848, 42021095076538120704192346310258569381147372475645952, 50907025031510010446870750093173570140655442336940032, 97277548980744898235637262465595797788298870119202816, 97277548980744898235637262465596056042715902027759616, 36893488147435880448, 1496577676626844588240573268701547599103969762217984, 4489733029880533764721719806406652891286682065704960, 4489733029880533764721719807011115801093996661640192, 14217487927955023588285446054505871717484663098510851, 7482888383134222941202868204677740426020155338984451, 8979466059761067529443441470962100468681571834533888, 909350803944028658208768, 303707302515945125183488, 37040297496514403558954188400362214719922902759636992, 37040297496514403558954188400361624424112544045596672, 0, 10476043736387912117684012880910316684893724468051968, 10476043736387912117684012880910316684893724468051968, 2993155353253689176481146537402947624255349848014848, 0, 0, 0, 0, 0, 8979466059761067529443439612208842872766049544044544, 8979466059761067529443439612208842872766049544044544, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 348449143727040986586495598010130648530944, 696898287454081973172991196020261297061888, 112723297995697759160731325956277264799760384, 133804471191183738849214309635890169035882496, 44601490397061246283071436545296723011960832]   -- 421 cells, box x -86..90, y 0..152
 second control glider(s) 300 generations later: FAILS
 second control glider(s) 330 generations later: works (set simulator)
 second control glider(s) 360 generations later: works (set simulator)
 with the block: pullSalvo translated by (100, 192) is reached at world time 1516;
    k = 0: evolve 1410 (R ∪ C ∪ translate (100, 192) (counter 0)) = R ∪ translate (100, 192) (counter -1): checked
    k = 1: evolve 1410 (R ∪ C ∪ translate (100, 192) (counter 1)) = R ∪ translate (100, 192) (counter 0): checked
    k = 2: evolve 1410 (R ∪ C ∪ translate (100, 192) (counter 2)) = R ∪ translate (100, 192) (counter 1): checked
    k = 3: evolve 1410 (R ∪ C ∪ translate (100, 192) (counter 3)) = R ∪ translate (100, 192) (counter 2): checked
```

The two gliders at the end are `ofRows 51 148 [2, 4, 7]` and `ofRows 58 150 [5, 6, 2]`, that is
exactly `translate (51, 143) pullSalvo`. Proposed Lean statements, `R` the window "whole periodic
configuration" and `C = ofRows 32 (-9) [2, 4, 7] = translate (32, -9) Pattern.glider`:

```lean
theorem pullGenerator_isOscillator : IsOscillator R 30
theorem pullGenerator : conway.evolve 1170 (R ∪ C) = R ∪ translate (51, 143) pullSalvo
-- with the block (checked for k = 0 .. 3; translate (100, 192) (counter k) = translate (51, 143) (counter (k + 49))):
--   conway.evolve 1410 (R ∪ C ∪ translate (100, 192) (counter k)) = R ∪ translate (100, 192) (counter (k - 1))
```

Checks made, in the order of the task:

1. without control glider: least period 30, bounded (envelope `x -86 .. 90`, `y 0 .. 132`);
2. with `C`: after 1170 generations the same periodic state plus exactly the two salvo gliders;
3. with the block `translate (100, 192) (counter k)`, `k = 0, 1, 2, 3` (its upper left cell is
   `(107 + k, 203 + k)`, 70 rows below the envelope, so the salvo flies freely for more than 50
   cells): after 1410 generations the periodic state and the block at `k - 1`, nothing else;
4. reuse: a second `C` 330 generations later works as well (two salvos, 82.5 cells apart, far
   more than the 13 that `pipeline` needs); 360 works; 300 fails (limit: the round trip of F2).

Clearances. Between the envelopes of different pieces the minimum is 10 (`S` – `RF1`), all other
pairs are 19 or more apart (table above). Flight segments against the envelopes of the pieces
they do not use (`g5_clearance.py`):

```text
world lines: G0 ((1, 1), 14, 119), G1 ((-1, -1), 29, 730), leg ((-1, 1), -2, 725), G2 ((-1, 1), 75, 771), o ((1, -1), -46, 1092), P1 ((1, 1), -97, 1116), P2 ((1, 1), -91, 1087)
  C0 (control, before S)   SE lane 41: K 28, Gb 84, RF1 29, RF2 69, RF3 55
  G0 (S to K)              SE lane 14: Gb 62, RF1 55, RF2 92, RF3 49
  G1 (K to RF1)            NW lane 29: S 11, Gb 41, RF2 36, RF3 21
  leg (RF1 to RF2)         SW lane -2: S 26, K 84, Gb 42, RF3 18
  P1 (RF2 onwards)         SE lane -97: S 54, K 24, Gb 6, RF1 46, RF3 3
  G2 (S to Gb)             SW lane 75: K 32, RF1 39, RF2 35, RF3 6
  o (Gb to RF3)            NE lane -46: S 54, K 82, RF1 56, RF2 19
  P2 (RF3 onwards)         SE lane -91: S 52, K 21, Gb 9, RF1 66, RF2 38
minimum over all segments: 3
```

The three small values are inherent or nearly so: `a` (P1) passes `RF3` at distance 3 (the
second salvo glider is 6 lanes from the output lane of the reflector, section 3.1), `G2` passes
`RF3` at 6 and `a` passes `Gb` at 6. Everything else is 9 or more.

Phases: `K` is delayed by 25 and `Gb` by 29 generations relative to `S`, `RF2` by 13; the odd
delays are forced by the parity conditions (2.4). The windows above are the pieces at world time
0 (mod 30); `S` is `blockedStream` itself.

## 4. Lanes and phases: what is reachable

* Output of a gate `(k, vx, vy, s)`: any lane; `tau ≡ 29 - 4 vx + s` (for `k = 0`). With `s`
  free every `(lane, tau mod 30)` is reachable; with all guns synchronous only odd `tau`
  (15 residues).
* Input of a gate: 12 or 4 of 30 phases per lane (`R-20`); of a kickback: 1 phase per lane; of
  the reflector: 1 lane, 1 phase. All are met by sliding the piece along the lane of the glider
  and choosing its delay; what remains fixed is the class `(λ, τ)` of 2.4 and, for a reflector,
  `tau + 4 lane` of the outgoing glider.
* Exact times (not only mod 30): the glider released by a gate is the one whose partner the
  control glider deleted, so a path determines the release time exactly. In `PG1` the two exact
  conditions (lane difference 6, `tau` difference 29) are solved by the three reflector
  positions and the position of `Gb`.
* A period-60 or period-120 clock is **not needed** for the pull salvo. It would help in one
  respect only: thinned streams could presumably be crossed (2.2), which would free the layout.
  Not searched: thinning of a period-30 stream.

## 5. Open

* **Push salvo**: third glider `(SE, L + 6, t - 4)`. One more fan-out stage is needed (for
  example `G2` as the control glider of a second pair `S′`, `K′`, giving two gliders in place of
  `o`), then one or two reflectors per path; the search of `g4_pull3.py` extends to this with
  one more exact condition. Estimated size: 10 guns, 5 or 6 reflectors.
* **Continue glider**: the same (one more fan-out stage), or a component "fan-out, then
  generator" in series. A cheaper way was not found: no control glider of the catalogue releases
  one glider of each stream.
* **Zero test** in this style (a detector glider across the diagonal, `R-19` §6 and
  `zeroTestGlider`): not started.
* **Certification**: `PG1` is one evolution certificate of 1170 generations on a window of
  177 × 133 with about 400 live cells, or modular: the certified gate (twice more, as `K` and
  `Gb`, each with a different control glider: kickback `(NW, -55, 8)` and gate `(NE, -46, 14)`
  in their own coordinates), the return of `X` into `S` (control glider `(NW, -12, 11)`), the
  reflector (three times), and free flights; the separations above show which pieces are far
  apart, but `a` passes `RF3` at distance 3 only, so that step needs its own certificate.
* Smaller designs: the verified placements all have boxes of about 177 × 133; a search with
  `G1` and `G2` of other fan-outs, or with two reflectors on path 2, was not made. Reuse spacing
  330 is that of F2.
* Not searched: other reflectors (other stabilisers, two shuttles), thinning to period 60,
  alternative block-moving salvos adapted to the generators.

## 6. Search ranges and run times

Python 3.12, standard library, up to 20 processes on a shared 22-thread machine (wall times).

| Script | Range | Runs | Time |
| --- | --- | --- | --- |
| `common.py` | cross-checks | | 1 s |
| `r0_obstruction.py` | SE and NW, lanes -40 .. 70, 30 phases, 1000 generations | 6 660 | 203 s |
| `r1_recipes.py 5`, `r1_recipes.py 9 sides` | slow recipes, ≤ 5 gliders (3 directions), ≤ 9 (2 sides) | 51 511; 1 040 | 64 s; 1 s |
| `r2_three.py` | SE + SW + NE, all timings within 130 generations | 2 650 252 | 2 504 s |
| `r3_headon.py 4` | 4 + 4 head-on gliders, 25 offsets, 8 phases | 41 800 | 47 s |
| `r4_stream.py one` | glider against stream, 110 classes | 110 | 2 s |
| `r5_synth.py` | kick positions, 1 380 candidates, 40 verified with the block | | about 4 min (1 process) |
| `b1_single_lane.py` | 20 lanes × 6 spacings × 16 gliders | 120 | 1 min |
| `q1_reflector.py` | 4 347 stabiliser placements; 6 oscillators × all world lines | | 19 s |
| `s1_shifter.py 24` | 17 × 60 kick positions | 1 020 | 6 s |
| `f1_fanout.py 41 24` | kickback K1, all repeatable gates, `|vx| ≤ 220`, box area ≤ 30 000 | 40 981 placements | 218 s |
| `f2_roundtrip.py` | 47 kickbacks, `|vx| ≤ 160` | 521 simulated | 34 s |
| `g2_pull.py` | 77 fan-outs, ≤ 3 reflectors | 0 solutions | 7 s |
| `g4_pull3.py 130` | see 3.3 | 130 candidates, 45 simulated | 30 s + 60 s; first 45 simulations 80 s; then stopped |

Limits: settling of free-glider collisions is cut at 700 – 1 500 generations, population 120 –
400 (unsettled runs are counted as failures: 3 – 16 % of the runs of `r1`, `r3`); composites are
cut 3 000 – 6 000 generations after the last control glider; only assemblies that are copies of
`blockedStream` and only the reflector `RF0` were used; the catalogue of control gliders is that
of `R-20` (one control glider from infinity at a time).

## 7. Files

`scripts/life_machine/` (see its `README.md` for the commands): `common.py`, `recipes.py`,
`reactions.py`, `machine.py`, the searches `r0` – `r5`, `b1`, `q1`, `s1`, `f1`, `f2`, `g1`, `g2`,
`g4`, `g5_clearance.py`, `report_data.py`, and `results/`. The data blocks of this report are
`results/report_reflector.txt`, `report_fanout.txt`, `report_fanout_k7.txt`,
`report_generator.txt` (printed by `report_data.py`, which asserts every statement with the set
simulator) and `results/g5_clearance.txt`; the recommended generator is `results/pg1.json`.
