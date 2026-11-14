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
