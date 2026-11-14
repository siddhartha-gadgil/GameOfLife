# N-17: Self-replication

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-17` |
| Title | Definitions of self-replication, survey of known constructions, feasibility |
| Kind | source synthesis / definition / research approach |
| Addresses | `G-8`; `Q-10` |
| Depends on | `N-01` (types), `N-04` (separation notions); sources `S-02`, `S-11` ch. 10–12, `S-15`, `S-16` |
| Dependency requirement | kernel types for stating definitions; the sources actually read |
| Produces | candidate formal definitions with sanity instances; a feasibility assessment; a precise activation rule for `G-8`; possibly new notes on construction arms |
| Difficulty | research: the definitional part is moderate; a Lean proof for any known replicator in Life is beyond what direct simulation can reach |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

User scope: Life "is rich enough to … have self-replication. This should be proved." This note
makes the claim precise and assesses whether and how it can be proved in Lean.

## Dependencies

None verified. Sources are at snippet level only.

## Sources and prior work

- Conway's argument in `S-02` (not retrieved): described by `S-04` as proving that the
  necessary components exist without giving an explicit machine.
- Gemini (`S-16`): a self-constructing *spaceship*; the parent is destroyed; not a replicator.
- Linear propagator (`S-16`): 290 096 cells, period 237 228 617; called "arguably the first
  explicit example of a replicator … depending on the exact definition"; other sources say it is
  not a replicator because the parent is destroyed.
- 0E0P metacell (`S-15`; `S-11` ch. 12 by title): a metacell with an empty off state, said to
  allow a genuine replicator in Life by emulating a small replicator of another rule.

## Theory development

Candidate definitions (to be refined):

- **Copying step**: `evolve T P = P ∪ (v +ᵥ P)` with `v ≠ 0` and the two copies disjoint.
- **Replicator**: the number of disjoint translated copies of `P` contained in `evolve n P` is
  unbounded in `n`. Variants allow debris, or copies in other phases or orientations.
- A definition that excludes spaceships (one copy, parent gone) and guns emitting gliders
  (the gun does not copy itself), and decides the disputed linear-propagator case explicitly.

Sanity instances for the definition: if the kernel is rule-generic (`Q-2`), a rule with a small
replicator gives a non-vacuity check (the HighLife rule is reported to have one; **recalled, not
sourced this session**). Negative instances: glider, Gosper gun.

Feasibility: direct kernel simulation of ≈ 3 × 10⁵ cells for ≈ 2 × 10⁸ generations is out of
reach of `N-03` by many orders of magnitude. A proof would have to be compositional: a verified
construction arm (glider salvos building still lifes), a verified tape reader, and a copy
theorem by induction over the tape. That is a second project of at least the size of `G-7`.

Proposed activation rule for `G-8`: activate when (i) `G-7` is achieved or its component theory
(`N-08`–`N-11`) is verified, and (ii) a specific explicit pattern with retrievable data and a
written decomposition into verified-size components has been identified, or the user decides to
prioritize it earlier. Until then only this note's definitional and survey work proceeds.

## Update from the source report `R-18` (2026-11-14)

Source: [`reports/R-18-source-report.md`](reports/R-18-source-report.md), written by a sub-agent
that read the primary sources (book `S-11` ch. 9 and parts of ch. 2, 6–8, 11, 12; Chapman's
archived pages `S-10`; Hickerson's 1990 description; Durand–Róka's research report `S-14`).
Its numerical observations are simulations, not proofs.

- No source gives a definition of replicator precise enough to state a theorem; the LifeWiki
  says so explicitly.
- Sizes: linear propagator 290 096 cells (the wiki gives two different periods, 237 228 617 and
  237 228 340); the 0E0P metacell is 2¹⁸ × 2¹⁸ cells per metacell with 2³⁶ generations per
  metageneration, and the book's replicator is twelve such metacells emulating the HighLife
  rule's replicator.
- Terminology trap: Durand–Róka's "construction-universal" means surjectivity of the global
  map and is false for Life; the Life community's "universal constructor" is a different,
  informal notion.
- The assessment below (postponed; infeasible by direct simulation) stands.

## Claims and evidence

| Claim | Status |
| --- | --- |
| Self-replicating patterns exist in Life | sourced claim with disputed definitions; no Lean evidence |
| Direct simulation of known replicators in the Lean kernel is infeasible | expectation from sizes; not measured |

## Difficulty, barriers and readiness

The survey and definitions are ready to start (reading `S-11` ch. 10–12 first). The formal goal
is postponed.

## Outputs and next dependencies

Updates `G-8` and `Q-10`; may request the rule-generic kernel in `N-01`.
