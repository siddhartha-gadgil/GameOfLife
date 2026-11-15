# N-20: The diagonal of a register: a block with a queue of salvos

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-20` |
| Title | Register diagonal dynamics: a block and a queue of salvos in flight |
| Kind | formalization plan |
| Addresses | `G-7` (step theorem of `N-19`) |
| Depends on | `N-19`; Lean: `salvo_world_all`, `salvo_world_end`, `trajectory_reaction`, `dz2gAll`, `dz2jAll` |
| Dependency requirement | compiled salvo-and-block processes with sharp footprints |
| Produces | the register part of the configuration encoding and its dynamics |
| Difficulty | hard (induction over a queue with times depending on the register value) |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-15: created |

## Purpose and scope

An instruction step of the machine (`N-19`, layout `R-31`) ends when the control glider enters the
next unit; the answer of a register operation leaves the module at a time independent of the
register value `k`. But the salvo that moves the block needs about `4 k` generations to reach it
(`dz2gAll`, `dz2jAll`: the tail of `4 k` generations). So at a step boundary a register is in
general **a block with salvos still in flight** towards it along its diagonal; a loop of `inc r`
can leave several in flight.

## The encoding

Register `r` at a step boundary: the block at position `k` (counting the salvos still in flight as
not yet arrived) and a queue `q = [(type₁, m₁), …]` of salvos in flight, type pull or push, each
at a stage `m` of its trajectory (generations since it became free), ordered front to back. Its
cells: the block and the salvos at their places (`evolve m (PullX …)` decomposed: the front salvo
with the block as one generic process, the others as free flights).

## Claims to prove

1. **Queue lemma.** If consecutive salvos are at least `G` cells apart along the diagonal (`G`
   from the reuse spacings of `R-29`, about 100 cells), the diagonal evolves, for every number of
   generations, into the block moved by the salvos that have arrived and the remaining queue
   advanced; footprint inside the diagonal strip of the register. Proof: induction over the queue;
   the front salvo and the block are one process (`salvo_world_all`), the others are flights far
   behind it; when the front salvo is done, the next becomes the front.
2. **Probe lemma (zero test).** The detector of `DZ2` probes only near the start of the diagonal: it
   finds the block at `-1` iff the effective value (block plus salvos in flight) is `0`. If the value
   is `0` the queue is short and arrives fast (the block is near the start); otherwise the block is
   far, or a pull leaves it at `≥ 0`.
3. **Separation.** The strip is far from every other part of the machine (`R-31`, inequalities
   14–17), so the diagonals run in parallel with the rest.

## Barriers

* The times at which salvos arrive depend on `k`; segment boundaries of the network method must be
  symbolic. The generic processes of `Network.lean` (`trajectory_reaction`) handle this for one
  salvo; the queue needs an induction with symbolic times.
* The minimum gap `G` must follow from the timing rules of the layout (`R-31` §4.3), as an
  inequality.
