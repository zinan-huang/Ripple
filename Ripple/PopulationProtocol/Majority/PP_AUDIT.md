# Population Protocol Libraries Audit

This note records what was integrated under `Ripple.PopulationProtocol.Majority` and what each
library currently proves. It is intentionally conservative: theorem wrappers
that take the target estimate/correctness statement as an input are not counted
as completed proofs.

## Integrated Libraries

- `PopProtoCommon`: shared counting/probability helpers for population
  protocols.
- `PopProto`: approximate majority protocol proof material from `PP-Proof`.
- `ExactMajority`: Doty et al. nonuniform exact majority formalization scaffold
  from `PP-ExactMajority`.
- `SSExactMajority` is intentionally not integrated in this tree right now.
  It is being finished in a separate working copy and should be merged later.

## PP-Proof / PopProto

The approximate-majority development is substantial. It contains real
one-step drift calculations, Markov kernels, corner-region convergence bounds,
central-region augmented-state supermartingale bounds, and explicit geometric
decay theorems, including:

- `nonconsensus_mem_activeRegion`
- `allX_stepDist_eq_pure`
- `allY_stepDist_eq_pure`
- `allB_stepDist_eq_pure`
- `allX_transitionKernel_eq_dirac`
- `allY_transitionKernel_eq_dirac`
- `allB_transitionKernel_eq_dirac`
- `allX_transitionKernel_pow_eq_dirac`
- `allY_transitionKernel_pow_eq_dirac`
- `allB_transitionKernel_pow_eq_dirac`
- `consensus_transitionKernel_eq_dirac`
- `consensus_transitionKernel_pow_eq_dirac`
- `hasOpinion_stepOrSelf`
- `hasOpinion_of_stepDist_support`
- `stepDist_not_hasOpinion_eq_zero_of_hasOpinion`
- `transitionKernel_not_hasOpinion_eq_zero_of_hasOpinion`
- `ae_hasOpinion_transitionKernel_pow`
- `transitionKernel_pow_not_hasOpinion_eq_zero`
- `not_allB_of_opinionated_stepDist_support`
- `stepDist_allB_eq_zero_of_hasOpinion`
- `transitionKernel_allB_eq_zero_of_hasOpinion`
- `transitionKernel_pow_allB_eq_zero_of_hasOpinion`
- `activeRegion`
- `nonconsensus_mem_activeRegion_set`
- `nonconsensus_opinionated_event_subset_activeRegion`
- `measure_activeRegion_le_sum`
- `measure_nonconsensus_opinionated_le_region_sum`
- `prob_in_activeLargeX_le`
- `prob_in_activeLargeY_le`
- `prob_in_activeLargeB_le`
- `convergence_time_largeX`
- `convergence_time_largeY`
- `convergence_time_largeB`
- `prob_in_activeCentral_le`
- `convergence_time_central`

There is currently no exported theorem named as the full global
high-probability convergence statement. The old placeholder
`PopProto.Convergence.Supermartingale.convergence_time_bound : True` has been
removed. This library should be treated as strong component proofs plus regional
time bounds, not yet as a single formal statement of the full high-probability
global theorem.

## PP-ExactMajority / ExactMajority

This is not yet a full formalization of the Doty et al. exact-majority paper.
It does formalize important infrastructure:

- agent roles, states, outputs, and transitions;
- the nonuniform protocol definition;
- state-count bounds for the flat Lean encoding;
- invariants such as small-bias preservation and well-formedness preservation,
  including one-step and reachable preservation for `well_formed_config` and
  the valid-initial reachable wrapper;
- preservation of the initial input gap under one-step and reachable protocol
  evolution, proved by reducing the `filter.card` definition to an additive
  `+1/-1` input-bias sum;
- deterministic bridges from the sign of `initialGap` to the concrete
  `majorityVerdict` output triple for A, B, and tie;
- preservation of `majorityVerdict` itself along reachable protocol executions,
  derived from input-gap preservation and the sign-to-verdict bridges;
- bidirectional bridge between `doutPartition` output triples and concrete
  unanimous `Output` fields, including the reverse direction from the generic
  partition output back to agent-level unanimity;
- Phase-10 majority witness bridges: if a Phase-10 unanimous A/B/T
  configuration matches the sign of the initial input gap, it gives both the
  required `majorityVerdict` partition output and a `Protocol.IsStable`
  witness;
- a reduction from the remaining phase-reachability obligation to the generic
  `Protocol.StablyComputes` wrapper: once every valid-initial reachable
  configuration is shown to reach a matching `phase10MajorityWitness`,
  `stable_majority_correct_target` and
  `nonuniform_majority_correctness_target` follow from the deterministic
  Phase-10 witness lemmas;
- a second Phase-10 endpoint interface for phase analyses that produce
  `doutPartition` output directly: a Phase-10 configuration with partition
  output `majorityVerdict init` is converted into the concrete
  `phase10MajorityWitness`, and the same stable-computation reductions are
  exported for this partition-output reachability form;
- Phase 10 deterministic stable-backup output preservation for unanimous
  interacting pairs, both for `Phase10Transition` and the full `Transition`
  dispatcher when both agents are already in Phase 10, plus one-step closure
  and reachable closure for configurations whose agents are all in Phase 10
  with unanimous output; these configurations are now proved stable in the
  generic `Protocol.IsStable` sense;
- reusable concentration/epidemic/Janson-style hooks.

The theorem names that previously wrapped supplied assumptions have been
demoted to target propositions or removed:

- `stable_majority_correct_target`
- `nonuniform_majority_correctness_target`
- the Section 5--7 milestone targets in `Analysis/Invariants.lean`

These targets should not be counted as discharged paper proofs. They record the
remaining probability-coupling obligations without exporting fake theorems.
The correctness wrapper itself is now separated from the probability work:
`stable_majority_correct_of_phase10MajorityWitness_reachability` proves that
the only missing correctness-side input is the actual Phase-10 endpoint
reachability theorem.

The Janson and epidemic-time concentration files still contain useful proved
union-bound/Chernoff steps, but their names now make the dependencies explicit:

- `janson_geom_upper_tail_of_mgf_bound`
- `janson_geom_lower_tail_of_mgf_bound`
- `janson_geom_upper_tail_of_individual_mgf_bound`
- `janson_geom_lower_tail_of_individual_mgf_bound`
- `janson_geom_concentration_of_tail_bounds`
- `epidemic_concentration_of_tail_bounds`
- `epidemicTime_concentration_of_tail_bounds`

The `*_of_individual_mgf_bound` lemmas use `iIndepFun.mgf_sum₀` to derive the
MGF of the sum from the product of individual MGFs.

The shifted-geometric MGF is now proved for Mathlib's geometric measure:

- `shifted_geometric_exp_series_hasSum`
- `shifted_geometric_exp_pmf_hasSum`
- `shifted_geometric_exp_pmf_tsum`
- `shifted_geometric_exp_integral_geometricMeasure`
- `shifted_geometric_mgf_geometricMeasure`
- `shifted_geometric_mgf_converges_of_nonpos`
- `shifted_geometric_mgf_geometricMeasure_of_nonpos`
- `shifted_geometric_mgf_of_identDistrib`
- `shifted_geometric_mgf_of_identDistrib_of_nonpos`
- `shifted_geometric_product_mgf_of_identDistrib`
- `shifted_geometric_product_mgf_of_identDistrib_of_nonpos`
- `shifted_geometric_mgf_closedForm_denom_pos`
- `shifted_geometric_mgf_closedForm_pos`
- `shifted_geometric_integrable_exp_sum_of_identDistrib`
- `shifted_geometric_mgf_closedForm_log_eq`
- `shifted_geometric_mgf_closedForm_eq_expNeg`
- `shifted_geometric_mgf_closedForm_le_upper_crude`
- `shifted_geometric_mgf_closedForm_log_le_upper_crude`
- `shifted_geometric_mgf_closedForm_le_lower_crude`
- `shifted_geometric_mgf_closedForm_log_le_lower_crude`
- `neg_log_one_sub_mul_le_mul_neg_log_one_sub`
- `neg_log_one_add_mul_le_mul_neg_log_one_add`
- `shifted_geometric_mgf_closedForm_log_le_upper_scaled`
- `shifted_geometric_mgf_closedForm_log_le_lower_scaled`
- `shifted_geometric_mgf_converges_of_nonneg_lt`
- `shifted_geometric_mgf_closedForm_log_le_upper_janson_point`
- `shifted_geometric_mgf_closedForm_log_le_lower_janson_point`
- `shifted_geometric_product_mgf_closedForm_log_eq`
- `shifted_geometric_product_mgf_closedForm_mul_le_exp_of_log_bound`
- `janson_geom_log_chernoff_of_pointwise_bound`
- `janson_pmin_le_of_iInf`
- `janson_pmin_nonneg_of_iInf`
- `janson_geom_upper_tail_of_shifted_geometric_bound`
- `janson_geom_lower_tail_of_shifted_geometric_bound`
- `janson_geom_upper_tail_of_shifted_geometric_log_bound`
- `janson_geom_lower_tail_of_shifted_geometric_log_bound`
- `janson_geom_upper_tail_of_shifted_geometric_pointwise_bound`
- `janson_geom_lower_tail_of_shifted_geometric_pointwise_bound`
- `janson_geom_upper_tail_of_shifted_geometric_janson_parameter`
- `janson_geom_lower_tail_of_shifted_geometric_janson_parameter`
- `janson_geom_upper_tail_of_shifted_geometric_iInf_parameter`
- `janson_geom_lower_tail_of_shifted_geometric_iInf_parameter`
- `janson_geom_concentration_of_shifted_geometric_iInf_parameters`
- `two_mul_exp_neg_eighth_le_exp_neg_sixteenth`
- `janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic`
- `janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic_of_convergent`
- `janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic_auto`
- `janson_log_rate_nonneg`
- `janson_log_rate_pos_of_ne_one`
- `janson_log_rate_upper_quadratic`
- `janson_log_rate_lower_quadratic`

The optimized one-sided Janson exponent inequalities are now instantiated for
the shifted-geometric variables. The `iInf` wrappers derive the local facts
`0 ≤ p_min` and `∀ i ∈ range k, p_min ≤ p_i` from the finite `p_min`
definition used by the caller. The two-sided wrapper now feeds the one-sided
bounds into the concentration corollary with `λ = 1 ± ε`, assuming only the
union-bound `1/2` slack. The quadratic lower bounds for the two Janson rates
at `λ = 1 ± ε` are proved separately. A second two-sided wrapper,
`janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic`,
uses those quadratic bounds directly and absorbs the two one-sided tails under
the quantitative scale condition `16 log 2 ≤ ε² p_min μ_X`. The
`_of_convergent` variant derives the two Chernoff integrability facts from the
finite shifted-geometric MGF convergence conditions, instead of taking
`Integrable` assumptions directly. The `_auto` variant uses the optimized
Janson parameter choices and derives those MGF convergence conditions
internally from the finite `p_min` facts and the same scale condition.

The source has no executable `sorry`/`axiom` commands in the imported tree, but
these target propositions are still mathematical placeholders.

## SSExactMajority

`SSExactMajority` is excluded from this branch. Another working copy is handling
its time-bound and final cleanup work, and this Ripple tree should merge that
version later instead of carrying an old duplicate under `Kurtz`.
