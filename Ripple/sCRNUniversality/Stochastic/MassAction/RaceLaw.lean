/-
  Final assembly: MassActionRaceLaw from rawLaw + pathFromOmega + raceBound.
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.Traj
import Ripple.sCRNUniversality.Probability.MeasureBridge

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-! ### Path construction using stateStep from Traj.lean -/

open Classical in
noncomputable def pathState
    (z0 : State S) (omega : (n : Nat) → Option N.I) : Nat → State S
  | 0 => z0
  | t + 1 => stateStep N (pathState z0 omega t) (omega (t + 1))

open Classical in
noncomputable def pathFired
    (z0 : State S) (omega : (n : Nat) → Option N.I) (t : Nat) : Option N.I :=
  let z := pathState N z0 omega t
  if hT : N.Terminal z then none
  else some (fireOptionSanitized N z (omega (t + 1)) hT)

theorem pathFired_valid (z0 : State S) (omega : (n : Nat) → Option N.I) (t : Nat) :
    match pathFired N z0 omega t with
    | some i => N.StepAt i (pathState N z0 omega t) (pathState N z0 omega (t + 1))
    | none => pathState N z0 omega (t + 1) = pathState N z0 omega t ∧
              N.Terminal (pathState N z0 omega t) := by
  open Classical in
  unfold pathFired
  set z := pathState N z0 omega t
  by_cases hT : N.Terminal z
  · simp [dif_pos hT]
    constructor
    · show stateStep N z (omega (t + 1)) = z
      simp [stateStep, dif_pos hT]
    · exact hT
  · simp [dif_neg hT]
    exact ⟨fireOptionSanitized_enabled N z _ hT,
      show stateStep N z (omega (t + 1)) = _ by simp [stateStep, dif_neg hT]⟩

noncomputable def pathFromOmega (hPos : N.hasPositiveRates) (z0 : State S)
    (omega : (n : Nat) → Option N.I) : Network.Path N where
  state := pathState N z0 omega
  fired := pathFired N z0 omega
  valid := pathFired_valid N z0 omega

/-! ### prefixToState = pathState -/

theorem prefixToState_eq_pathState (z0 : State S)
    (omega : (n : Nat) → Option N.I) :
    ∀ t, prefixToState N z0 t (fun k => omega k.val) = pathState N z0 omega t := by
  intro t; induction t with
  | zero => rfl
  | succ t ih =>
    simp only [prefixToState, pathState]; congr 1

theorem prefixToState_const_of_hstate (z0 : State S) (z : State S) (t : Nat)
    (hstate : ∀ omega, pathState N z0 omega t = z)
    (p : (i : Finset.Iic t) → Option N.I) :
    prefixToState N z0 t p = z := by
  let omega : (n : Nat) → Option N.I := fun k =>
    if h : k ≤ t then p ⟨k, Finset.mem_Iic.mpr h⟩ else none
  have : (fun k : Finset.Iic t => omega k.val) = p := by
    funext ⟨k, hk⟩; simp [omega, Finset.mem_Iic.mp hk]
  rw [← this, prefixToState_eq_pathState]; exact hstate omega

/-! ### raceBound proof -/

private theorem pathFired_eq_of_omega_enabled
    (z0 : State S) (omega : (n : Nat) → Option N.I) (t : Nat) (i : N.I)
    (z : State S) (hz : pathState N z0 omega t = z)
    (hEnabled : N.EnabledAt z i) (homega : omega (t + 1) = some i) :
    pathFired N z0 omega t = some i := by
  open Classical in
  simp only [pathFired]
  have hNT : ¬ N.Terminal (pathState N z0 omega t) := by
    rw [hz]; exact fun hT => hT i hEnabled
  simp only [dif_neg hNT, homega]
  congr 1
  exact fireOptionSanitized_of_enabled N _ i hNT (by rwa [hz])

private theorem notFired_subset_notOmega
    (z0 : State S) (t : Nat) (i : N.I) (z : State S)
    (hstate : ∀ omega, pathState N z0 omega t = z)
    (hEnabled : N.EnabledAt z i) :
    {omega : (n : Nat) → Option N.I |
      pathFired N z0 omega t ≠ some i} ⊆
    {omega | omega (t + 1) ≠ some i} := by
  intro omega hne hcontra
  exact hne (pathFired_eq_of_omega_enabled N z0 omega t i z (hstate omega) hEnabled hcontra)

/-! ### Helper: PMF complement bound -/

private theorem massActionPMF_complement_le
    (hPos : N.hasPositiveRates) (z : State S) (i : N.I) :
    (massActionPMF N hPos z).toMeasure {some i}ᶜ ≤
    ENNReal.ofReal (1 - ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat)) := by
  -- Complement in probability measure: μ(Aᶜ) = 1 - μ(A)
  rw [measure_compl (show MeasurableSet ({some i} : Set (Option N.I)) from trivial)
    (measure_ne_top _ _)]
  rw [measure_univ]
  rw [PMF.toMeasure_apply_singleton _ _ (show MeasurableSet ({some i} : Set (Option N.I)) from trivial)]
  -- Goal: 1 - (massActionPMF z)(some i) ≤ ENNReal.ofReal(1 - prop/total)
  -- massActionPMF(some i) = massActionWeight(some i)
  change 1 - massActionWeight N hPos z (some i) ≤ _
  unfold massActionWeight
  classical
  by_cases hT : N.Terminal z
  · -- Terminal: weight = 0, propensity = 0
    simp only [hT, dite_true, tsub_zero]
    have hprop0 : (N.rxn i).propensity z = 0 :=
      Reaction.propensity_eq_zero_of_not_enabled (hT i)
    rw [hprop0]; simp
  · -- Non-terminal: weight = jumpProbAt z i
    simp only [hT, dite_false]
    -- Goal: 1 - (jumpProbAt z i : ENNReal) ≤ ENNReal.ofReal(1 - prop/total)
    -- Strategy: show (jumpProbAt z i : ENNReal) = ENNReal.ofReal(prop/total), then use ofReal_sub
    set q := jumpProbAt N z i
    -- Key fact: (q : ENNReal) = ENNReal.ofReal ((q : NNReal) : ℝ)
    have hq_ennreal : (q : ENNReal) = ((q : NNReal) : ENNReal) := rfl
    -- And ((q : NNReal) : ENNReal) = ENNReal.ofReal ((q : NNReal) : ℝ)
    -- And ((q : NNReal) : ℝ) = ((q : Rat) : ℝ) = (prop/total : Rat : ℝ)
    -- So (q : ENNReal) = ENNReal.ofReal ((prop/total : Rat) : ℝ)
    have hq_ofReal : (q : ENNReal) =
        ENNReal.ofReal ((((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat) : Rat) : ℝ) := by
      rw [hq_ennreal, ← ENNReal.ofReal_coe_nnreal]
      congr 1
    rw [hq_ofReal]
    -- Now: 1 - ENNReal.ofReal(↑(prop/total)) ≤ ENNReal.ofReal(1 - ↑↑prop/↑↑total)
    -- Normalize casts and use ofReal_sub
    have hcast_eq : ((((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat) : Rat) : ℝ) =
        (((N.rxn i).propensity z : Rat) : ℝ) / (((N.totalPropensity z : Rat) : ℝ)) := by
      push_cast; ring
    rw [hcast_eq, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]

/-! ### Helper: rawLaw marginal = PMF -/

private theorem rawLaw_coord_complement
    (hPos : N.hasPositiveRates) (z0 : State S)
    (t : Nat) (i : N.I) (z : State S)
    (hstate : ∀ omega, pathState N z0 omega t = z) :
    (rawLaw N hPos z0)
      {omega | omega (t + 1) ≠ some i} ≤
    ENNReal.ofReal
      (1 - ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat)) := by
  -- It suffices to show the measure equals the PMF complement
  suffices heq : (rawLaw N hPos z0) {omega | omega (t + 1) ≠ some i} =
      (massActionPMF N hPos z).toMeasure {some i}ᶜ by
    rw [heq]; exact massActionPMF_complement_le N hPos z i
  have hms : MeasurableSet ({some i}ᶜ : Set (Option N.I)) := trivial
  -- Rewrite set
  rw [show {omega : (n : Nat) → Option N.I | omega (t + 1) ≠ some i} =
    (fun x => x (t + 1)) ⁻¹' {some i}ᶜ from by ext; simp]
  -- rawLaw (preimage) = rawLaw.map(eval(t+1)) {some i}ᶜ
  rw [← Measure.map_apply (measurable_pi_apply (t + 1)) hms]
  -- Use the marginal lemma
  rw [rawLaw_map_eval_succ N hPos z0 t]
  -- Goal: (stepKernel t ∘ₖ partialTraj ...) x₀ {some i}ᶜ = (massActionPMF z).toMeasure {some i}ᶜ
  rw [Kernel.comp_apply' _ _ _ hms]
  -- Under hstate, stepKernel t p = (massActionPMF z).toMeasure for all p
  have hstep : ∀ p, stepKernel N hPos z0 t p = (massActionPMF N hPos z).toMeasure := by
    intro p
    change (massActionPMF N hPos (prefixToState N z0 t p)).toMeasure = _
    congr 2; exact prefixToState_const_of_hstate N z0 z t hstate p
  simp_rw [hstep]
  rw [MeasureTheory.lintegral_const, measure_univ, mul_one]

theorem raceBound_of_rawLaw
    (hPos : N.hasPositiveRates) (z0 : State S)
    (t : Nat) (i : N.I) (z : State S)
    (hstate : ∀ omega, (pathFromOmega N hPos z0 omega).state t = z)
    (hEnabled : N.EnabledAt z i) :
    (rawLaw N hPos z0)
      {omega | (pathFromOmega N hPos z0 omega).fired t ≠ some i} ≤
    ENNReal.ofReal
      (1 - ((N.rxn i).propensity z : Rat) / (N.totalPropensity z : Rat)) := by
  calc (rawLaw N hPos z0)
        {omega | (pathFromOmega N hPos z0 omega).fired t ≠ some i}
      ≤ (rawLaw N hPos z0) {omega | omega (t + 1) ≠ some i} :=
        measure_mono (notFired_subset_notOmega N z0 t i z hstate hEnabled)
    _ ≤ _ := rawLaw_coord_complement N hPos z0 t i z hstate

noncomputable def massActionRaceLaw
    (hPos : N.hasPositiveRates) (z0 : State S) :
    MassActionRaceLaw N ((n : Nat) → Option N.I) where
  prob := Ripple.sCRNUniversality.Probability.ProbSpec.ofMeasure (rawLaw N hPos z0)
  probAxioms := Ripple.sCRNUniversality.Probability.ProbAxioms.ofMeasure (rawLaw N hPos z0)
  path := pathFromOmega N hPos z0
  raceBound := fun t i z hstate hEnabled _hPos =>
    raceBound_of_rawLaw N hPos z0 t i z hstate hEnabled

end Ripple.sCRNUniversality.Stochastic.MassAction
