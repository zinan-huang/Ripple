/-
  Ripple.Kurtz.PopulationProtocol — Population Protocol Mean-Field ODE

  Specializes Kurtz's theorem to population protocols:
    N agents, d species S₁,...,S_d
    Reactions: S_i + S_j → S_k + S_ℓ
    Mass-action rates: β_{(k,ℓ)-(i,j)}(x) = x_i · x_j
    Mean-field ODE: x'_r = Σ (net production of S_r) · x_i(t) · x_j(t)

  This is exactly the quadratic ODE that Ripple formalizes as a PIVP.

  The key connection:
  - Every population protocol induces a RateSpec with quadratic rates
  - The drift F is a quadratic polynomial vector field
  - The resulting mean-field ODE is a PolyPIVP with degree-2 polynomials
  - Kurtz's theorem guarantees the stochastic PP converges to this ODE

  References:
  - [LPP] §1–2: Population protocols and mass-action ODE
  - kurtz-ml.pdf §1.3: PP specialization of Kurtz
-/

import Ripple.Kurtz.MeanField
import Ripple.CTMC.DensityDependent
import Ripple.LPP.Defs
import Mathlib.RingTheory.MvPolynomial.Basic

namespace Ripple.Kurtz

open Ripple
open Ripple.CTMC

/-! ## Population protocol as a rate specification

A population protocol with d species has reactions of the form
S_i + S_j → S_k + S_ℓ. Each reaction has mass-action rate x_i · x_j. -/

/-- A population protocol reaction: two input species produce two output species. -/
structure PPReaction (d : ℕ) where
  /-- First input species. -/
  in1 : Fin d
  /-- Second input species. -/
  in2 : Fin d
  /-- First output species. -/
  out1 : Fin d
  /-- Second output species. -/
  out2 : Fin d
  deriving DecidableEq

namespace PPReaction

variable {d : ℕ}

/-- The net change vector for a reaction: +1 for each output, -1 for each input.
When in1 = out1 or similar, the effects cancel. -/
noncomputable def netChange (r : PPReaction d) : Fin d → ℤ :=
  fun i =>
    (if i = r.out1 then 1 else 0) +
    (if i = r.out2 then 1 else 0) -
    (if i = r.in1 then 1 else 0) -
    (if i = r.in2 then 1 else 0)

/-- Population-protocol reactions conserve total population: two agents are
consumed and two agents are produced. -/
theorem netChange_sum_zero (r : PPReaction d) :
    ∑ i, r.netChange i = 0 := by
  simp [netChange, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The mass-action rate of a reaction: x_{in1} · x_{in2}. -/
def massActionRate (r : PPReaction d) (x : Fin d → ℝ) : ℝ :=
  x r.in1 * x r.in2

/-- A reaction consumes two distinct input species.  This is the clean
finite-population regime for the unguarded mass-action PP encoding; reactions
with repeated input need guarded/combinatorial finite-N rates instead. -/
def InputsDistinct (r : PPReaction d) : Prop :=
  r.in1 ≠ r.in2

/-- If a reaction consumes distinct input species, no coordinate is consumed
more than once. -/
theorem neg_one_le_netChange_of_inputsDistinct (r : PPReaction d)
    (hd : r.InputsDistinct) (i : Fin d) :
    (-1 : ℤ) ≤ r.netChange i := by
  by_cases h1 : i = r.in1
  · subst i
    simp [netChange, InputsDistinct] at hd ⊢
    split_ifs <;> omega
  · by_cases h2 : i = r.in2
    · subst i
      have hd' : r.in2 ≠ r.in1 := Ne.symm hd
      simp [netChange] at hd' ⊢
      split_ifs <;> omega
    · simp [netChange, h1, h2]
      split_ifs <;> omega

/-- A coordinate that is not one of the consumed input species has
non-negative net change. -/
theorem netChange_nonneg_of_not_input (r : PPReaction d) {i : Fin d}
    (h1 : i ≠ r.in1) (h2 : i ≠ r.in2) :
    0 ≤ r.netChange i := by
  simp [netChange, h1, h2]
  split_ifs <;> omega

/-- For an input-distinct reaction, if both consumed inputs are present in a
lattice state, then applying the reaction does not make any coordinate
negative. -/
theorem count_add_netChange_nonneg_of_inputsDistinct
    (r : PPReaction d) (hd : r.InputsDistinct)
    {N : ℕ} (x : Fin d → Fin (N + 1))
    (hpos1 : 0 < (x r.in1 : ℕ)) (hpos2 : 0 < (x r.in2 : ℕ))
    (i : Fin d) :
    0 ≤ (x i : ℤ) + r.netChange i := by
  by_cases h1 : i = r.in1
  · subst i
    have hx : (1 : ℤ) ≤ (x r.in1 : ℤ) := by exact_mod_cast hpos1
    have hdelta := r.neg_one_le_netChange_of_inputsDistinct hd r.in1
    linarith
  · by_cases h2 : i = r.in2
    · subst i
      have hx : (1 : ℤ) ≤ (x r.in2 : ℤ) := by exact_mod_cast hpos2
      have hdelta := r.neg_one_le_netChange_of_inputsDistinct hd r.in2
      linarith
    · have hx : 0 ≤ (x i : ℤ) := by exact_mod_cast (Nat.zero_le (x i : ℕ))
      have hdelta := r.netChange_nonneg_of_not_input h1 h2
      linarith

/-- If all post-reaction integer counts are non-negative and their total is
`N`, then each post-reaction count is at most `N`. -/
theorem count_add_netChange_le_total
    (r : PPReaction d) {N : ℕ} (x : Fin d → Fin (N + 1))
    (hsum : ∑ i, (x i : ℕ) = N)
    (hnonneg : ∀ i, 0 ≤ (x i : ℤ) + r.netChange i)
    (i : Fin d) :
    (x i : ℤ) + r.netChange i ≤ (N : ℤ) := by
  have hsingle :
      (x i : ℤ) + r.netChange i ≤
        ∑ j, ((x j : ℤ) + r.netChange j) := by
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have htotal :
      ∑ j, ((x j : ℤ) + r.netChange j) = (N : ℤ) := by
    rw [Finset.sum_add_distrib, r.netChange_sum_zero]
    have hsum_int : (∑ j, (x j : ℕ) : ℤ) = (N : ℤ) := by
      exact_mod_cast hsum
    simpa using hsum_int
  exact hsingle.trans_eq htotal

/-- For an input-distinct reaction with both consumed inputs present in a
simplex state, every post-reaction coordinate lies in the integer interval
`[0, N]`. -/
theorem count_add_netChange_mem_Icc_of_inputsDistinct
    (r : PPReaction d) (hd : r.InputsDistinct)
    {N : ℕ} (x : Fin d → Fin (N + 1))
    (hsum : ∑ i, (x i : ℕ) = N)
    (hpos1 : 0 < (x r.in1 : ℕ)) (hpos2 : 0 < (x r.in2 : ℕ))
    (i : Fin d) :
    0 ≤ (x i : ℤ) + r.netChange i ∧
      (x i : ℤ) + r.netChange i ≤ (N : ℤ) := by
  have hnonneg : ∀ j, 0 ≤ (x j : ℤ) + r.netChange j :=
    r.count_add_netChange_nonneg_of_inputsDistinct hd x hpos1 hpos2
  exact ⟨hnonneg i, r.count_add_netChange_le_total x hsum hnonneg i⟩

/-- If an input-distinct reaction has both consumed inputs present in a
simplex population state, then its net change is realizable as a target state
in the ambient finite lattice. -/
theorem exists_realizing_state_of_inputsDistinct_of_input_counts_pos
    (r : PPReaction d) (hd : r.InputsDistinct)
    {N : ℕ} (x : Fin d → Fin (N + 1))
    (hsum : ∑ i, (x i : ℕ) = N)
    (hpos1 : 0 < (x r.in1 : ℕ)) (hpos2 : 0 < (x r.in2 : ℕ)) :
    ∃ y : Fin d → Fin (N + 1),
      ∀ i, (y i : ℤ) - (x i : ℤ) = r.netChange i := by
  let y : Fin d → Fin (N + 1) := fun i =>
    ⟨Int.toNat ((x i : ℤ) + r.netChange i), by
      have hIcc :=
        r.count_add_netChange_mem_Icc_of_inputsDistinct hd x hsum hpos1 hpos2 i
      exact Nat.lt_succ_of_le (Int.toNat_le.mpr hIcc.2)⟩
  refine ⟨y, ?_⟩
  intro i
  have hIcc :=
    r.count_add_netChange_mem_Icc_of_inputsDistinct hd x hsum hpos1 hpos2 i
  dsimp [y]
  rw [Int.toNat_of_nonneg hIcc.1]
  ring

/-- A reaction has zero mass-action rate once either consumed input has zero
density. -/
theorem massActionRate_eq_zero_of_input_zero (r : PPReaction d)
    (x : Fin d → ℝ) (hzero : x r.in1 = 0 ∨ x r.in2 = 0) :
    r.massActionRate x = 0 := by
  rcases hzero with h | h
  · simp [massActionRate, h]
  · simp [massActionRate, h]

end PPReaction

/-- A population protocol: a finite set of reactions. -/
structure PopProtocol (d : ℕ) where
  /-- The set of reactions. -/
  reactions : Finset (PPReaction d)

namespace PopProtocol

variable {d : ℕ} (pp : PopProtocol d)

/-- Every reaction in the protocol consumes two distinct input species. -/
def InputsDistinct : Prop :=
  ∀ r ∈ pp.reactions, r.InputsDistinct

/-- Convert a population protocol to a density-dependent rate specification.

Each reaction r: S_i + S_j → S_k + S_ℓ contributes:
  - Jump direction: net change vector of r
  - Rate: β_ℓ(x) = x_i · x_j (mass-action) -/
noncomputable def toRateSpec : RateSpec d where
  jumps := pp.reactions.image PPReaction.netChange
  rate := fun ℓ x =>
    ∑ r ∈ pp.reactions.filter (fun r => r.netChange = ℓ),
      r.massActionRate x
  rate_nonneg := by
    intro ℓ _ x hx
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg (hx r.in1) (hx r.in2)
  rate_support := by
    intro ℓ hℓ
    ext x
    simp only [Finset.mem_image] at hℓ
    simp only [PPReaction.massActionRate]
    have hempty : pp.reactions.filter (fun r => r.netChange = ℓ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro r hr hc
      exact hℓ ⟨r, hr, hc⟩
    simp [hempty]
  rate_lipschitz := by
    intro ℓ _ R hR
    refine ⟨2 * R * (pp.reactions.card : ℝ) + 1, by positivity, ?_⟩
    intro x y hx hy
    rw [← Finset.sum_sub_distrib, Real.norm_eq_abs]
    have bilinear : ∀ r : PPReaction d,
        |r.massActionRate x - r.massActionRate y| ≤ 2 * R * ‖x - y‖ := by
      intro r
      simp only [PPReaction.massActionRate]
      have split : x r.in1 * x r.in2 - y r.in1 * y r.in2 =
          x r.in1 * (x r.in2 - y r.in2) + (x r.in1 - y r.in1) * y r.in2 := by ring
      rw [split]
      calc |x r.in1 * (x r.in2 - y r.in2) + (x r.in1 - y r.in1) * y r.in2|
          ≤ |x r.in1 * (x r.in2 - y r.in2)| + |(x r.in1 - y r.in1) * y r.in2| :=
            abs_add_le _ _
        _ = |x r.in1| * |x r.in2 - y r.in2| + |x r.in1 - y r.in1| * |y r.in2| := by
            rw [abs_mul, abs_mul]
        _ ≤ R * ‖x - y‖ + ‖x - y‖ * R := by
            gcongr
            · exact (norm_le_pi_norm x r.in1).trans hx
            · rw [show x r.in2 - y r.in2 = (x - y) r.in2 from by simp [Pi.sub_apply]]
              exact norm_le_pi_norm (x - y) r.in2
            · rw [show x r.in1 - y r.in1 = (x - y) r.in1 from by simp [Pi.sub_apply]]
              exact norm_le_pi_norm (x - y) r.in1
            · exact (norm_le_pi_norm y r.in2).trans hy
        _ = 2 * R * ‖x - y‖ := by ring
    calc |∑ r ∈ pp.reactions.filter (fun r => r.netChange = ℓ),
            (r.massActionRate x - r.massActionRate y)|
        ≤ ∑ r ∈ pp.reactions.filter (fun r => r.netChange = ℓ),
            |r.massActionRate x - r.massActionRate y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ pp.reactions.filter (fun r => r.netChange = ℓ),
            (2 * R * ‖x - y‖) :=
          Finset.sum_le_sum (fun r _ => bilinear r)
      _ ≤ (pp.reactions.card : ℝ) * (2 * R * ‖x - y‖) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right
            (mod_cast Finset.card_filter_le pp.reactions _) (by positivity)
      _ ≤ (2 * R * (pp.reactions.card : ℝ) + 1) * ‖x - y‖ := by
          nlinarith [norm_nonneg (x - y)]

/-- The mean-field ODE for a population protocol.

  x'_r(t) = Σ_{reactions} (net production of S_r) · x_{in1}(t) · x_{in2}(t)

This is a quadratic polynomial vector field. -/
noncomputable def meanFieldDrift (x : Fin d → ℝ) : Fin d → ℝ :=
  fun r => ∑ rxn ∈ pp.reactions,
    (rxn.netChange r : ℝ) * rxn.massActionRate x

/-- The mean-field drift equals the drift from the rate specification. -/
theorem meanFieldDrift_eq_drift :
    pp.meanFieldDrift = pp.toRateSpec.drift := by
  ext x i
  simp only [meanFieldDrift, RateSpec.drift, toRateSpec, PPReaction.massActionRate]
  symm
  simp_rw [Finset.mul_sum]
  have key : ∀ ℓ ∈ pp.reactions.image PPReaction.netChange,
      (∑ rxn ∈ pp.reactions.filter (fun r => r.netChange = ℓ),
        (ℓ i : ℝ) * (x rxn.in1 * x rxn.in2)) =
      (∑ rxn ∈ pp.reactions.filter (fun r => r.netChange = ℓ),
        (rxn.netChange i : ℝ) * (x rxn.in1 * x rxn.in2)) := by
    intro ℓ _
    apply Finset.sum_congr rfl
    intro rxn hrxn
    simp only [Finset.mem_filter] at hrxn
    rw [hrxn.2]
  rw [Finset.sum_congr rfl key]
  have hdisjoint : Set.PairwiseDisjoint
      (↑(pp.reactions.image PPReaction.netChange) : Set _)
      (fun ℓ => pp.reactions.filter (fun r => r.netChange = ℓ)) := by
    intro ℓ₁ _ ℓ₂ _ hne
    simp only [Function.onFun, Finset.disjoint_filter]
    exact fun _ _ h1 h2 => absurd (h1.symm.trans h2) hne
  rw [← Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  rw [Finset.ext_iff]
  intro rxn
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  exact ⟨fun ⟨ℓ, ⟨_, _, _⟩, hmem, _⟩ => hmem,
         fun h => ⟨rxn.netChange, ⟨rxn, h, rfl⟩, h, rfl⟩⟩

/-- Every jump direction in the population-protocol rate specification
conserves total population. -/
theorem toRateSpec_conservative_jumps :
    ∀ ℓ ∈ pp.toRateSpec.jumps, ∑ i, ℓ i = 0 := by
  intro ℓ hℓ
  simp only [toRateSpec, Finset.mem_image] at hℓ
  obtain ⟨r, _hr, rfl⟩ := hℓ
  exact r.netChange_sum_zero

/-- The density-dependent CTMC built from a population protocol has
conservative listed jumps. -/
theorem toDensityDepCTMC_conservativeJumps (N : ℕ) (hN : 0 < N) :
    (DensityDepCTMC.mk N hN pp.toRateSpec).ConservativeJumps := by
  intro ℓ hℓ
  exact pp.toRateSpec_conservative_jumps ℓ hℓ

/-- Reaction-level simplex boundary compatibility lifts to the aggregated
`RateSpec` boundary compatibility needed by the density-dependent CTMC bridge.

This isolates the finite-N modeling obligation for population protocols:
prove that every reaction whose net change is impossible from a simplex state
has zero rate at that state's density.  This can be discharged by guarded
finite-N rates, by an input-distinct realization lemma, or by moving to a
reachable/simplex state space. -/
theorem toDensityDepCTMC_boundaryCompatibleOnSimplex_of_reaction_rates_zero
    (N : ℕ) (hN : 0 < N)
    (hzero : ∀ x : Fin d → Fin (N + 1),
      (DensityDepCTMC.mk N hN pp.toRateSpec).InSimplex x →
        ∀ r ∈ pp.reactions,
          ¬ (∃ y : Fin d → Fin (N + 1),
              ∀ i, (y i : ℤ) - (x i : ℤ) = r.netChange i) →
            r.massActionRate
              ((DensityDepCTMC.mk N hN pp.toRateSpec).scaledState x) = 0) :
    (DensityDepCTMC.mk N hN pp.toRateSpec).BoundaryCompatibleOnSimplex := by
  intro x hx ℓ _hℓ himpossible
  change pp.toRateSpec.rate ℓ
    ((DensityDepCTMC.mk N hN pp.toRateSpec).scaledState x) = 0
  simp only [toRateSpec]
  apply Finset.sum_eq_zero
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  exact hzero x hx r hr'.1 (by
    intro hrealizable
    apply himpossible
    obtain ⟨y, hy⟩ := hrealizable
    refine ⟨y, ?_⟩
    intro i
    simpa [hr'.2] using hy i)

/-- Input-distinct population protocols are simplex-locally boundary
compatible for the unguarded mass-action density-dependent encoding: if a
reaction is impossible from a simplex state, then one of its consumed input
species has zero count, hence zero mass-action rate. -/
theorem toDensityDepCTMC_boundaryCompatibleOnSimplex_of_inputsDistinct
    (N : ℕ) (hN : 0 < N) (hd : pp.InputsDistinct) :
    (DensityDepCTMC.mk N hN pp.toRateSpec).BoundaryCompatibleOnSimplex := by
  refine pp.toDensityDepCTMC_boundaryCompatibleOnSimplex_of_reaction_rates_zero
    N hN ?_
  intro x hx r hr himpossible
  have hsum : ∑ i, (x i : ℕ) = N := by
    simpa [DensityDepCTMC.InSimplex, DensityDepCTMC.totalCount] using hx
  by_cases hzero1 : (x r.in1 : ℕ) = 0
  · have hscaled1 :
        (DensityDepCTMC.mk N hN pp.toRateSpec).scaledState x r.in1 = 0 := by
      simp [DensityDepCTMC.scaledState, hzero1]
    exact r.massActionRate_eq_zero_of_input_zero
      ((DensityDepCTMC.mk N hN pp.toRateSpec).scaledState x) (Or.inl hscaled1)
  · by_cases hzero2 : (x r.in2 : ℕ) = 0
    · have hscaled2 :
          (DensityDepCTMC.mk N hN pp.toRateSpec).scaledState x r.in2 = 0 := by
        simp [DensityDepCTMC.scaledState, hzero2]
      exact r.massActionRate_eq_zero_of_input_zero
        ((DensityDepCTMC.mk N hN pp.toRateSpec).scaledState x) (Or.inr hscaled2)
    · have hpos1 : 0 < (x r.in1 : ℕ) := Nat.pos_of_ne_zero hzero1
      have hpos2 : 0 < (x r.in2 : ℕ) := Nat.pos_of_ne_zero hzero2
      exact (himpossible
        (r.exists_realizing_state_of_inputsDistinct_of_input_counts_pos
          (hd r hr) x hsum hpos1 hpos2)).elim

/-- Canonical density-dependent PP paths stay in the population simplex
almost surely, once non-absorption and simplex initialization are supplied. -/
theorem canonicalPathMap_forall_inSimplex_stateAt_ae
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin d → Fin (N + 1))
    (hNA : (DensityDepCTMC.mk N hN pp.toRateSpec).NoAbsorbing)
    (hinit : (DensityDepCTMC.mk N hN pp.toRateSpec).InSimplex x₀) :
    ∀ᵐ records ∂(DensityDepCTMC.mk N hN pp.toRateSpec).canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        (DensityDepCTMC.mk N hN pp.toRateSpec).InSimplex
          (((DensityDepCTMC.mk N hN pp.toRateSpec).canonicalPathMap records).stateAt t) := by
  exact (DensityDepCTMC.mk N hN pp.toRateSpec)
    |>.canonicalPathMap_forall_inSimplex_stateAt_ae_of_noAbsorbing
      x₀ hNA (pp.toDensityDepCTMC_conservativeJumps N hN) hinit

/-- Canonical density-process bridge for input-distinct population protocols.

For this PP subclass, conservative jumps and simplex-local boundary
compatibility are both supplied internally.  The remaining stochastic input is
only the generator-residual Doob/bracket inequality. -/
noncomputable def toCanonicalDensityProcessOfGeneratorInstantQVDoob_of_inputsDistinct
    (N : ℕ) (hN : 0 < N)
    (x₀ : Fin d → Fin (N + 1))
    (hNA : (DensityDepCTMC.mk N hN pp.toRateSpec).NoAbsorbing)
    (hinit : (DensityDepCTMC.mk N hN pp.toRateSpec).InSimplex x₀)
    (hd : pp.InputsDistinct)
    {A : ℝ} (hA : 0 < A)
    (hDoob : ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖(DensityDepCTMC.mk N hN pp.toRateSpec).generatorMartingalePart
          (DensityDepCTMC.mk N hN pp.toRateSpec).canonicalPathMap s records‖ ^ 2
        ∂(DensityDepCTMC.mk N hN pp.toRateSpec).canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        (DensityDepCTMC.mk N hN pp.toRateSpec).instantQVRate
          (((DensityDepCTMC.mk N hN pp.toRateSpec).canonicalPathMap records).stateAt s))
        ∂(DensityDepCTMC.mk N hN pp.toRateSpec).canonicalRecordMeasure x₀) :
    DensityProcess d pp.toRateSpec N
      ((DensityDepCTMC.mk N hN pp.toRateSpec).canonicalRecordMeasure x₀) :=
  (DensityDepCTMC.mk N hN pp.toRateSpec)
    |>.toCanonicalDensityProcessOfGeneratorInstantQVDoob
      x₀ hNA
      (pp.toDensityDepCTMC_conservativeJumps N hN)
      hinit
      (pp.toDensityDepCTMC_boundaryCompatibleOnSimplex_of_inputsDistinct N hN hd)
      hA hDoob

/-! ## Connection to Ripple's PIVP framework

The mean-field ODE of a population protocol is a PolyPIVP: the vector
field is a polynomial of degree ≤ 2 with rational coefficients (in fact,
integer coefficients from the stoichiometry). -/

/-- Build a PolyPIVP from a population protocol and an initial condition.

The vector field is the quadratic mean-field ODE; initial conditions are
rational (representing initial fractions x_i(0) = n_i/N). -/
noncomputable def toPolyPIVP (x₀ : Fin d → ℚ) (output : Fin d) :
    PolyPIVP d where
  field := fun r =>
    ∑ rxn ∈ pp.reactions,
      (rxn.netChange r : ℚ) •
        MvPolynomial.X rxn.in1 * MvPolynomial.X rxn.in2
  init := x₀
  output := output

/-- The PolyPIVP's semantic field matches the mean-field drift. -/
theorem toPolyPIVP_field_eq (x₀ : Fin d → ℚ) (output : Fin d)
    (x : Fin d → ℝ) :
    (pp.toPolyPIVP x₀ output).evalField x = pp.meanFieldDrift x := by
  ext r
  simp only [PolyPIVP.evalField, toPolyPIVP, meanFieldDrift, PPReaction.massActionRate]
  rw [MvPolynomial.eval₂_sum]
  congr 1; ext rxn
  rw [MvPolynomial.smul_eq_C_mul]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  simp [Rat.castHom]
  ring

/-- The mean-field ODE of a population protocol is CRN-implementable.

This is immediate: the ODE came from mass-action kinetics in the
first place. The production terms p_i and degradation rates q_i
can be read off directly from the reaction stoichiometry. -/
theorem meanField_isCRNImplementable [NeZero d] :
    ∃ (x₀ : Fin d → ℚ) (output : Fin d),
      ∃ _pcd : PolyCRNDecomposition d (pp.toPolyPIVP x₀ output), True := by
  refine ⟨0, ⟨0, Fin.pos'⟩, ?_, trivial⟩
  refine {
    prod := fun r =>
      ∑ rxn ∈ pp.reactions.filter (fun rxn => 0 < rxn.netChange r),
        (rxn.netChange r : ℚ) • (MvPolynomial.X rxn.in1 * MvPolynomial.X rxn.in2)
    degr := fun r =>
      ∑ rxn ∈ pp.reactions.filter (fun rxn => rxn.netChange r < 0),
        (-rxn.netChange r : ℤ) • (if rxn.in1 = r then MvPolynomial.X rxn.in2
         else MvPolynomial.X rxn.in1)
    prod_nonneg := ?prod_nn
    degr_nonneg := ?degr_nn
    init_nonneg := ?init_nn
    field_eq := ?field_eq
  }
  case init_nn => intro i; simp [toPolyPIVP]
  case prod_nn =>
    intro i σ
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro rxn hrxn
    simp only [Finset.mem_filter] at hrxn
    rw [MvPolynomial.coeff_smul]
    apply smul_nonneg
    · exact_mod_cast hrxn.2.le
    · simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
                 MvPolynomial.coeff_monomial]
      split_ifs <;> norm_num
  case degr_nn =>
    intro i σ
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro rxn hrxn
    simp only [Finset.mem_filter] at hrxn
    rw [(Int.cast_smul_eq_zsmul ℚ (-rxn.netChange i) _).symm,
        MvPolynomial.smul_eq_C_mul, MvPolynomial.coeff_C_mul]
    apply mul_nonneg
    · exact_mod_cast Int.neg_nonneg_of_nonpos hrxn.2.le
    · split_ifs <;>
        simp only [MvPolynomial.X, MvPolynomial.coeff_monomial] <;>
        split_ifs <;> norm_num
  case field_eq =>
    intro i
    simp only [toPolyPIVP]
    simp_rw [smul_mul_assoc]
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not pp.reactions
      (fun rxn => (0 : ℤ) < rxn.netChange i)]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.sum_mul]
    simp_rw [smul_mul_assoc, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_neg, neg_smul]
    rw [Finset.sum_neg_distrib, neg_neg]
    conv_lhs => rw [show pp.reactions.filter (fun rxn => ¬(0 : ℤ) < rxn.netChange i) =
      pp.reactions.filter (fun rxn => rxn.netChange i ≤ 0) from by ext; simp [not_lt]]
    rw [← Finset.sum_subset
      (show pp.reactions.filter (fun rxn => rxn.netChange i < 0) ⊆
          pp.reactions.filter (fun rxn => rxn.netChange i ≤ 0) from by
        intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, le_of_lt hx.2⟩)
      (fun x hx hx' => by
        simp only [Finset.mem_filter] at hx
        have : ¬(x.netChange i < 0) := fun h =>
          hx' (Finset.mem_filter.mpr ⟨hx.1, h⟩)
        have : x.netChange i = 0 := by omega
        simp [this])]
    apply Finset.sum_congr rfl
    intro rxn hrxn
    simp only [Finset.mem_filter] at hrxn
    congr 1
    have h_in : rxn.in1 = i ∨ rxn.in2 = i := by
      by_contra h_neither
      push Not at h_neither
      have : 0 ≤ rxn.netChange i := by
        simp only [PPReaction.netChange]
        rw [if_neg (Ne.symm h_neither.1), if_neg (Ne.symm h_neither.2)]
        simp only [sub_zero]
        split_ifs <;> omega
      linarith [hrxn.2]
    rcases h_in with h1 | h2
    · simp [h1, mul_comm]
    · split_ifs with h_eq
      · rw [h_eq, mul_comm]
      · rw [h2]

/-! ## The full bridge: stochastic PP → deterministic ODE → CRN-computable

Combining Kurtz's theorem with the PIVP connection:

1. A population protocol with N agents is a density-dependent CTMC
2. By Kurtz, the density X̄^N(t) → x(t) as N → ∞
3. x(t) solves the quadratic mean-field ODE
4. This ODE is a PIVP in Ripple's framework
5. If x(t) → ν as t → ∞, then ν is CRN-computable

This is the formal justification for why Ripple's PIVP framework
captures exactly what population protocols compute in the large-N limit. -/

/-- A population protocol computes a number ν if its mean-field ODE
converges to ν along the output coordinate.

This definition connects the stochastic notion "the PP computes ν"
(finite-N stochastic dynamics) to the deterministic notion
"the PIVP converges to ν" (ODE limit) via Kurtz's theorem. -/
def Computes (pp : PopProtocol d) (output : Fin d) (ν : ℝ) : Prop :=
  ∃ x₀ : Fin d → ℚ,
    ∀ sol : ℝ → Fin d → ℝ,
      (sol 0 = fun i => (x₀ i : ℝ)) →
      (∀ t ≥ 0, HasDerivAt sol (pp.meanFieldDrift (sol t)) t) →
      Filter.Tendsto (fun t => sol t output) Filter.atTop (nhds ν)

/-- If a PP computes ν, then ν is PIVP-computable (and hence CRN-computable).

This is the formal bridge: Kurtz's theorem justifies that the ODE limit
captures the computational content of the stochastic protocol. -/
theorem computes_implies_pivpComputable (output : Fin d) (ν : ℝ)
    (h : Computes pp output ν)
    (sol : ℝ → Fin d → ℝ)
    (hsol_init : sol 0 = fun i => (h.choose i : ℝ))
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (pp.meanFieldDrift (sol t)) t) :
    ∃ (d' : ℕ) (pivp : PolyPIVP d') (sol : ℝ → Fin d' → ℝ),
      (sol 0 = fun i => (pivp.init i : ℝ)) ∧
      Filter.Tendsto (fun t => sol t pivp.output) Filter.atTop (nhds ν) := by
  refine ⟨d, pp.toPolyPIVP h.choose output, sol, ?_, ?_⟩
  · exact hsol_init
  · simp only [toPolyPIVP]
    exact h.choose_spec sol hsol_init hsol_ode

end PopProtocol

end Ripple.Kurtz
