# Kernel/

The domain model. A kernel file defines the objects of the domain and states each law as a
**typeclass** (a hypothesis that an object satisfies), never as an `axiom`. Theorems take the law
as an instance argument, so they hold for every object satisfying it.

- [`Example.lean`](Example.lean): the one-dimensional harmonic oscillator. `OscParams` (mass,
  stiffness), `energy`, the law `OscillatorLaw p x v` (`x' = v`, `m v' = -k x`),
  `energy_conserved`, `potential_le_energy`.
- [`Life.lean`](Life.lean): Conway's Game of Life on finite configurations. `Cell` (`ℤ × ℤ`, `x`
  to the right, `y` downward), `nbrs`, `liveNbrs`, `Rule` (birth and survival counts, no birth
  at zero neighbours), `conway` (B3/S23), `Rule.step`, `Rule.evolve`, the set-level specification
  `Rule.stepSet`, and the cell-by-cell rule `Rule.mem_step`. A model given by definitions: there
  is no law typeclass, and the specification plays the role of the independent check.

Keep the kernel small, state in each module docstring that it is a kernel file, and give every
law its sanity triad in `Sanity/`. See `notes/domain-libraries.md`.
