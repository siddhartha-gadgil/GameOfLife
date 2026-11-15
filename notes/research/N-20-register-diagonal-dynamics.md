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
| Implementation status | in progress |
| Implementation evidence | `Theory/Life/Diagonal.lean` |
| Lean evidence | `diag_strip`, `flights_reaction`, `flights_evolve_mul`, `Salvo.front_end` |
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

## Refined approach (2026-11-15): the isolated diagonal with virtual salvos

Treat the diagonal of register `r` as an isolated system `C_r`: the initial block `counter k₀` and
every salvo sent into it so far, each placed back along the diagonal at its *virtual* start (its
position at time `0` if it had always been flying). In the isolated system nothing else is there,
so a virtual salvo flies untouched until the time it is really emitted, and then it is exactly the
real salvo. Hence the diagonal of the machine at time `t` is `conway.evolve t C_r`, and an operation
adds one salvo: `evolve n (evolve t C_r ∪ S) = evolve (t + n) (C_r ∪ S_virtual)` by locality (the
virtual salvo stays behind the others). The encoding of a register is this one trajectory. Needed:

1. **Queue footprint**: for consecutive gaps `≥ G`, every `evolve t C_r` lies in the diagonal strip
   (induction over the salvos; the front one and the block as the generic process
   `salvo_track_all`, the others as flights).
2. **Value**: after all salvos have arrived the block is at `k₀ + Σ dⱼ`; a salvo arrives within
   `4 (k + e) + n` generations, so if the value is small the queue is empty by the next operation.
3. **Probe**: when the detector of a `decJz` passes, near the start of the diagonal there is only
   the block (if its position is small) or nothing; `dz2Detector_pass` and the `k = 0, 1`
   certificates cover the interaction.

## Progress

* 2026-11-15: claim 1 (queue footprint) compiled: `diag_strip` (`Theory/Life/Diagonal.lean`), by
  induction over the queue with symbolic arrival times. Claim 2 compiled: `diag_step`, `diag_end`
  (after `diagTime K q` generations the block is at `K + qMove q`). Next: the instances for the pull
  and push salvos (`DiagParams`, the reaction of the pull extended to a multiple of 4), then the
  probe lemma and the addition of a salvo (virtual start).
* 2026-11-15: compiled: moving strip bounds, `diag_add` (adding a salvo = virtual start),
  `diag_near` (probe: if every salvo is `L` cells along, the near part is the final block),
  instances `regPull`, `regPush` (`Salvos.lean`).

## Barriers

* The times at which salvos arrive depend on `k`; segment boundaries of the network method must be
  symbolic. The generic processes of `Network.lean` (`trajectory_reaction`) handle this for one
  salvo; the queue needs an induction with symbolic times.
* The minimum gap `G` must follow from the timing rules of the layout (`R-31` §4.3), as an
  inequality.
