# Sanity/

Checks that kernel definitions and laws mean what they should: for every law a **degenerate
case**, a **concrete instance** (the law is satisfiable, so theorems about it are not vacuous) and
a **counterexample** (the law excludes something).

- [`Example.lean`](Example.lean): for `Kernel/Example`, the free particle
  (`free_velocity_const`), the instance `cos`/`-sin` (`instOscillatorLawCos`, `cos_energy`) and
  the non-instance `exp` (`exp_energy_not_conserved`, `not_oscillatorLaw_exp`).
- [`Life.lean`](Life.lean): for `Kernel/Life`, the neighbourhood (`mem_nbrs_iff_max`, `nbrs_eq`,
  `card_nbrs`), the step against its specification (`Rule.coe_step`, `conway_stepSet_univ`,
  `not_finite_stepSetCore_birth_zero`), degenerate cases (`Rule.step_empty`,
  `conway_step_eq_empty_of_card_lt_three`), instances (`conway_step_block`, the blinker of period
  two), counterexamples (`not_monotone_conway_step`, `not_injective_conway_step`,
  `not_additive_conway_step`), symmetry (`Rule.step_map` and its instances) and the speed of
  light (`Rule.exists_near_of_mem_evolve`).
- [`QuasisymmetryNotSymmetry.lean`](QuasisymmetryNotSymmetry.lean): a local counterexample showing
  that a symmetry of a scalar field need not be a symmetry of the vector-field equations built
  from it (uses `Theory/Fields/LieGradient`).
