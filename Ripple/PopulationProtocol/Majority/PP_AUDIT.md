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
- `initial_hasOpinion`
- `initial_not_allB`
- `initial_isConsensus_iff`
- `initial_not_isConsensus_of_pos_lt`
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
- `initial_transitionKernel_pow_allB_eq_zero`
- `initial_transitionKernel_pow_not_hasOpinion_eq_zero`
- `supportTrace`, `supportTraceEndpoint`,
  `ae_of_stepDist_support_preserved`,
  `transitionKernel_pow_not_pred_eq_zero_of_stepDist_support_preserved`,
  `transitionKernel_pow_eq_zero_of_forall_not_pred`,
  `supportTraceEndpoint_hasOpinion`, `supportTraceEndpoint_not_allB`,
  `initial_supportTraceEndpoint_not_allB`,
  `gap_stepOrSelf_bounded`, `gap_of_stepDist_support_bounded`,
  `supportTraceEndpoint_gap_bounded`,
  `transitionKernel_pow_gap_natAbs_sub_gt_eq_zero`, and
  `transitionKernel_pow_eq_zero_of_forall_gap_natAbs_sub_gt`, plus generic
  finite-time core-invariant packages
  `transitionKernel_pow_core_invariants`,
  `transitionKernel_pow_core_invariants_fail_eq_zero`, and
  `transitionKernel_pow_eq_zero_of_forall_core_invariants_fail`, with
  initial-state wrappers `initial_supportTraceEndpoint_gap_bounded`,
  `initial_transitionKernel_pow_gap_natAbs_sub_gt_eq_zero`, and
  `initial_transitionKernel_pow_eq_zero_of_forall_gap_natAbs_sub_gt`, plus
  combined initial core-invariant packages
  `initial_supportTraceEndpoint_core_invariants`,
  `initial_transitionKernel_pow_core_invariants`,
  `initial_transitionKernel_pow_core_invariants_fail_eq_zero`, and
  `initial_transitionKernel_pow_eq_zero_of_forall_core_invariants_fail`
- `activeRegion`
- `nonconsensus_mem_activeRegion_set`
- `nonconsensus_opinionated_event_subset_activeRegion`
- `measure_activeRegion_le_sum`
- `measure_nonconsensus_opinionated_le_region_sum`
- `transitionKernel_pow_nonconsensus_le_region_sum`
- `initial_mem_activeRegion_of_pos_lt`
- `initial_transitionKernel_pow_nonconsensus_le_region_sum`
- `initial_transitionKernel_pow_nonconsensus_le_region_sum_all`
- `initial_consensus_transitionKernel_pow_eq_dirac`
- `initial_consensus_transitionKernel_pow_nonconsensus_eq_zero`
- `absorbedKernelLargeX_pow_eq_dirac_of_not_mem`
- `absorbedKernelLargeY_pow_eq_dirac_of_not_mem`
- `absorbedKernelLargeB_pow_eq_dirac_of_not_mem`
- `absorbedKernelCentral_pow_eq_dirac_of_not_mem`
- `absorbedKernelLargeX_active_eq_zero_of_not_mem`
- `absorbedKernelLargeY_active_eq_zero_of_not_mem`
- `absorbedKernelLargeB_active_eq_zero_of_not_mem`
- `absorbedKernelCentral_active_eq_zero_of_not_mem`
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
- generic population-size preservation for one-step and reachable protocol
  executions (`stepRel_card_eq`, `reachable_card_eq`, `stepRel_size_eq`,
  `reachable_size_eq`);
- generic additive-observable preservation for one-step and reachable protocol
  executions (`Config.sumOf`, `stepRel_sumOf_eq`, `reachable_sumOf_eq`);
- deterministic chosen-pair update infrastructure (`stepOrSelf`,
  `stepRel_stepOrSelf_of_applicable`, `stepOrSelf_card_eq`,
  `reachable_stepOrSelf`, `stepOrSelf_sumOf_eq`);
- a generic ExactMajority uniform random scheduler over ordered state pairs:
  `Config.interactionCount`, `Config.sum_interactionCount`,
  `Config.interactionPMF`, `Protocol.stepDist`, and support-to-reachability /
  support-size preservation bridges (`stepDist_support_reachable`,
  `stepDist_support_card_eq`);
- a generic ExactMajority Markov kernel interface:
  `Protocol.stepDistOrSelf`, `Protocol.transitionKernel`, and support
  preservation facts (`stepDistOrSelf_support_reachable`,
  `stepDistOrSelf_support_card_eq`) using the scheduler for populations of
  size at least two and a point-mass fallback otherwise; one-step
  support-closed predicates are lifted to finite Markov-chain executions by
  `Protocol.ae_of_stepDistOrSelf_support_preserved` and
  `Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved`,
  and finite Markov-chain executions are almost surely deterministic
  reachable executions via `Protocol.ae_reachable_transitionKernel_pow` and
  `Protocol.transitionKernel_pow_not_reachable_eq_zero`; consequently, every
  event disjoint from the deterministic reachability closure has finite-time
  probability zero by
  `Protocol.transitionKernel_pow_eq_zero_of_forall_not_reachable`;
- a concrete nonuniform exact-majority Markov-chain interface:
  `nonuniformStepDistOrSelf`, `nonuniformTransitionKernel`, and the inherited
  support-to-reachability / support-size facts for `NonuniformMajority L K`,
  plus concrete finite-time reachability wrappers
  `ae_nonuniformReachable_transitionKernel_pow` and
  `nonuniformTransitionKernel_pow_not_reachable_eq_zero`, with the concrete
  event form `nonuniformTransitionKernel_pow_eq_zero_of_forall_not_reachable`;
- stochastic-support forms of the deterministic invariants:
  `nonuniformStepDistOrSelf_support_initialGap_eq`,
  `nonuniformStepDistOrSelf_support_majorityVerdict_eq`,
  `nonuniformStepDistOrSelf_support_well_formed_config`, plus valid-initial
  wrappers for well-formedness and majority-verdict preservation; these are
  now also lifted to finite Markov-chain powers by
  `nonuniformTransitionKernel_pow_initialGap_eq`,
  `nonuniformTransitionKernel_pow_majorityVerdict_eq`,
  `nonuniformTransitionKernel_pow_well_formed_config`, and the corresponding
  valid-initial wrappers; the complements of these invariant events are also
  proved null by
  `nonuniformTransitionKernel_pow_initialGap_ne_eq_zero`,
  `nonuniformTransitionKernel_pow_majorityVerdict_ne_eq_zero`,
  `nonuniformTransitionKernel_pow_not_well_formed_config_eq_zero`, with
  reusable event-subset forms for each invariant and direct valid-initial
  variants, plus the simultaneous core-invariant package
  `validInitial_nonuniformTransitionKernel_pow_core_invariants`,
  `validInitial_nonuniformTransitionKernel_pow_core_invariants_fail_eq_zero`,
  and
  `validInitial_nonuniformTransitionKernel_pow_eq_zero_of_forall_core_invariants_fail`;
  Phase-0/1 small-bias preservation is also lifted to finite Markov-chain
  time by
  `validInitial_nonuniformTransitionKernel_pow_phase_le_one_smallBias_eq_initialGap`
  and the corresponding zero-probability bad-event form
  `validInitial_nonuniformTransitionKernel_pow_phase_le_one_smallBias_ne_eq_zero`;
- finite stochastic support traces:
  `Protocol.supportTrace`, `Protocol.supportTraceEndpoint`, and concrete
  `nonuniformSupportTrace` wrappers proving that every finite support path is
  protocol-reachable and preserves population size, `initialGap`,
  `majorityVerdict`, and `well_formed_config`; finite support-trace Phase-10
  endpoints are bridged to stable-output witnesses and to the two correctness
  targets, in both concrete `phase10MajorityWitness` and generic
  `doutPartition` endpoint forms; direct endpoint packages
  `stable_output_of_nonuniformSupportTrace_phase10MajorityWitness` and
  `stable_output_of_nonuniformSupportTrace_phase10_partition_output` avoid
  adding reachability assumptions when only endpoint stability is needed;
  support-trace endpoints also export the combined valid-initial core
  invariant `validInitial_nonuniformSupportTrace_core_invariants`, plus
  `validInitial_nonuniformSupportTrace_smallBiasSum_eq_initialGap` for
  Phase-0/1 endpoints;
- finite realized-schedule traces:
  `Protocol.runPairs`, `Protocol.reachable_runPairs`, generic size/additive
  invariant preservation along traces, and concrete `nonuniformRunPairs`
  preservation of reachability, population size, `initialGap`,
  `majorityVerdict`, and `well_formed_config`; finite scheduled Phase-10
  endpoints are bridged directly to stable-output witnesses via
  `stable_witness_of_nonuniformRunPairs_phase10MajorityWitness` and
  `stable_witness_of_nonuniformRunPairs_phase10_partition_output`, with
  endpoint-only packages
  `stable_output_of_nonuniformRunPairs_phase10MajorityWitness` and
  `stable_output_of_nonuniformRunPairs_phase10_partition_output`; scheduled
  endpoints also export the combined valid-initial core invariant
  `validInitial_nonuniformRunPairs_core_invariants`, plus
  `validInitial_nonuniformRunPairs_smallBiasSum_eq_initialGap` for Phase-0/1
  endpoints;
- state-count bounds for the flat Lean encoding;
- invariants such as small-bias preservation and well-formedness preservation,
  including one-step and reachable preservation for `well_formed_config` and
  the valid-initial reachable wrapper;
- the Phase-0 small-bias/input-gap bridge
  `validInitial_smallBiasSum_initialGap`, plus the Phase ≤ 1 reachable
  corollary `reachable_smallBiasSum_eq_initialGap`;
- preservation of the initial input gap under one-step and reachable protocol
  evolution, proved by reducing the `filter.card` definition to an additive
  `+1/-1` input-bias sum;
- deterministic bridges from the sign of `initialGap` to the concrete
  `majorityVerdict` output triple for A, B, and tie, including the reverse
  `majorityVerdict_eq_A/B/T_iff_initialGap_*` characterizations;
- preservation of `majorityVerdict` itself along reachable protocol executions,
  derived from input-gap preservation and the sign-to-verdict bridges;
- bidirectional bridge between `doutPartition` output triples and concrete
  unanimous `Output` fields, including the reverse direction from the generic
  partition output back to agent-level unanimity;
- Phase-10 majority witness bridges: if a Phase-10 unanimous A/B/T
  configuration matches the sign of the initial input gap, it gives both the
  required `majorityVerdict` partition output and a `Protocol.IsStable`
  witness; `stable_output_of_phase10MajorityWitness` packages this endpoint
  conclusion without an extra reachability argument, and
  `phase10MajorityWitness_iff_phase10_partition_output` identifies this
  concrete witness with the generic Phase-10 partition-output endpoint;
- a reduction from the remaining phase-reachability obligation to the generic
  `Protocol.StablyComputes` wrapper: once every valid-initial reachable
  configuration is shown to reach a matching `phase10MajorityWitness`,
  `stable_majority_correct_target` and
  `nonuniform_majority_correctness_target` follow from the deterministic
  Phase-10 witness lemmas;
- a second Phase-10 endpoint interface for phase analyses that produce
  `doutPartition` output directly: a Phase-10 configuration with partition
  output `majorityVerdict init` is converted into the concrete
  `phase10MajorityWitness`; `phase10_partition_output_majority_isStable`
  and `stable_output_of_phase10_partition_output` also package the endpoint
  itself as a stable majority output, and the same stable-computation
  reductions are exported for this partition-output reachability form;
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

- `chernoff_upper`
- `chernoff_lower`
- `chernoff_two_sided_hoeffding`
- `geometric_drift_tail_kernel`
- `geometric_drift_tail`
- `measure_real_le_of_le_ofReal`
- `geometric_drift_tail_random_variable`
- `geometric_drift_tail_random_variable_real_bound`
- `geometric_drift_tail_random_variable_ge_one`
- `geometric_drift_tail_random_variable_ge_one_real_bound`
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
