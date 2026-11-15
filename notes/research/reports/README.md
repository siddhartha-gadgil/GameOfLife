# notes/research/reports/

Reports written by sub-agents. They are inputs to the notes, not evidence: source reports
summarize what external sources say, search reports record numerical observations of the
project's untrusted oracles. A claim becomes established only through a compiled Lean
declaration.

- [`R-18-source-report.md`](R-18-source-report.md): primary sources for the register-machine
  route (book chapter, Chapman, Hickerson, Durand–Róka), with locators and cell-exact data as
  found in the sources.
- [`R-19-elementary-reactions.md`](R-19-elementary-reactions.md): own exhaustive search of
  two-glider collisions, the eater, salvos against a block and zero tests
  (`scripts/life_search`). Certified in `LeanTheory/Theory/Life/Collisions.lean`.
- [`R-20-gun-gates.md`](R-20-gun-gates.md): own search of terminated guns, blocked streams and
  gates (`scripts/life_gates`). Certified in `LeanTheory/Theory/Life/Gates.lean`.
- [`R-21-salvo-generators.md`](R-21-salvo-generators.md): own search for a fan-out, a
  reflector and salvo generators (`scripts/life_machine`); obstructions (gun shadow, uncrossable
  streams, parity). Reflector and pull-salvo generator certified in
  `LeanTheory/Theory/Life/SalvoGenerator.lean`.
- [`R-22-push-and-continue.md`](R-22-push-and-continue.md): continue glider (`CG1`), the failed
  push-generator search with its obstructions, and the decision part of the zero test.
- [`R-23-push-generator.md`](R-23-push-generator.md): the push-salvo generator `PSG1` (and
  `PSG1C` with a continue glider); certified in `LeanTheory/Theory/Life/Increment.lean`.
- [`R-25-zero-supply.md`](R-25-zero-supply.md): why the zero-test inputs cannot be supplied by the
  current components, and a partly designed replacement logic (`scripts/life_zero`).
- [`R-24-register.md`](R-24-register.md): the joint register `REG1` (one block, DEC and INC
  inputs, a shared glider through an OR gate); `scripts/life_machine`.
- [`R-26-decjz.md`](R-26-decjz.md): the decrement-from-zero decision `DZ1` (free gliders) and
  the supply obstruction `O3`; `scripts/life_zero`.
- [`R-27-decjz-inc.md`](R-27-decjz-inc.md): the decJz design `DZ2` (restore via `REG1`'s INC
  input), verified by simulation for k = 0, 1, 2, 3, 40; supply of `O` open (`O4`).
- [`R-28-dz2-supply.md`](R-28-dz2-supply.md): `DZ2` complete from one control glider (supply
  of `O` by a re-timing gate, Z branch); simulated for k = 0, 1, 2, 3, 40, 100.
- [`R-29-sharing.md`](R-29-sharing.md): sharing a register: OR-gate merge chains, dispatch
  stations, INC continue, reuse spacings; a modified `DZ2` (gate `G_I`); `scripts/life_route`.
- [`R-30-layout.md`](R-30-layout.md): the program layout rule (register modules, instruction and
  merge units, band routing with hairpin delays, timing rules) and exact simulations of whole
  machines to halting (addition, register sharing); `scripts/life_layout`.
