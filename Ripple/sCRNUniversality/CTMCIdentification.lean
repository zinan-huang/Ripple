import Ripple.sCRNUniversality.CTMCBridge
import Ripple.CTMC.CanonicalLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# Identification of finite stopped mass-action laws with canonical CTMC records

The finite state includes a molecule-count sublevel, the requested target
counter, an all-reaction counter, and a cemetery.  The extra counter retains
null firings as genuine augmented-state transitions.

The finite record-law theorem is unconditional apart from positive rates.
The CTM exhaustion and first-exit consequences expose global U1 explicitly.
Absorbing record sentinels are interpreted using a stopped absorbing extension.
-/

namespace Ripple.sCRNUniversality.CTMCIdentification

open MeasureTheory ProbabilityTheory Preorder Classical
open Ripple.CTMC
open Stochastic Stochastic.MassAction CTMCBridge
open scoped BigOperators ENNReal

universe u v w

noncomputable section
section FiniteLocalizationDefinition

/-- Finite marked channels whose nonzero-rate destinations differ from their source. -/
structure FiniteChannels (X : Type u) (I : Type v)
    [Fintype X] [DecidableEq X] [Fintype I] where
  channelRate : X → I → Rate
  destination : X → I → X
  noSelf : ∀ x i, channelRate x i ≠ 0 → destination x i ≠ x

namespace FiniteChannels

variable {X : Type u} {I : Type v}
variable [Fintype X] [DecidableEq X] [Fintype I]
variable (D : FiniteChannels X I)

def totalRate (x : X) : Rate := ∑ i, D.channelRate x i

def destinationRate (x y : X) : Rate :=
  ∑ i, if D.destination x i = y then D.channelRate x i else 0

theorem destinationRate_self_eq_zero (x : X) :
    D.destinationRate x x = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hdest : D.destination x i = x
  · have hz : D.channelRate x i = 0 := by
      by_contra hn
      exact D.noSelf x i hn hdest
    simp [hdest, hz]
  · simp [hdest]

theorem sum_destinationRate (x : X) :
    ∑ y, D.destinationRate x y = D.totalRate x := by
  unfold destinationRate totalRate
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem sum_destinationRate_except (x : X) :
    ∑ y ∈ Finset.univ.filter (· ≠ x), D.destinationRate x y =
      D.totalRate x := by
  have h := D.sum_destinationRate x
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x),
    D.destinationRate_self_eq_zero x, zero_add] at h
  simpa only [Finset.filter_ne'] using h

/-- Aggregation is by destination, with the diagonal fixed by the exit rate. -/
def qMatrix : QMatrix X where
  rate x y :=
    if x = y then -(D.totalRate x : ℝ) else (D.destinationRate x y : ℝ)
  rate_nonneg x y hxy := by
    rw [if_neg hxy]
    exact (D.destinationRate x y).cast_nonneg
  rate_diag x := by
    rw [if_pos rfl]
    congr 1
    calc
      (D.totalRate x : ℝ) =
          ((∑ y ∈ Finset.univ.filter (· ≠ x), D.destinationRate x y : Rate) : ℝ) := by
            rw [D.sum_destinationRate_except]
      _ = ∑ y ∈ Finset.univ.filter (· ≠ x),
          if x = y then -(D.totalRate x : ℝ) else (D.destinationRate x y : ℝ) := by
            rw [NNRat.cast_sum]
            apply Finset.sum_congr rfl
            intro y hy
            rw [if_neg (Finset.mem_filter.mp hy).2.symm]

theorem qMatrix_rate_offdiag (x y : X) (hxy : x ≠ y) :
    D.qMatrix.rate x y = (D.destinationRate x y : ℝ) := by
  simp only [qMatrix, hxy, if_false]

theorem qMatrix_exitRate (x : X) :
    D.qMatrix.exitRate x = (D.totalRate x : ℝ) := by
  unfold QMatrix.exitRate
  calc
    (∑ y ∈ Finset.univ.filter (· ≠ x), D.qMatrix.rate x y) =
        ∑ y ∈ Finset.univ.filter (· ≠ x), (D.destinationRate x y : ℝ) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact D.qMatrix_rate_offdiag x y (Finset.mem_filter.mp hy).2.symm
    _ = ((∑ y ∈ Finset.univ.filter (· ≠ x), D.destinationRate x y : Rate) : ℝ) := by
          rw [NNRat.cast_sum]
    _ = (D.totalRate x : ℝ) := by rw [D.sum_destinationRate_except]

theorem qMatrix_isAbsorbing_iff (x : X) :
    D.qMatrix.IsAbsorbing x ↔ D.totalRate x = 0 := by
  rw [QMatrix.IsAbsorbing, D.qMatrix_exitRate]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    rw [h]
    norm_num

@[simp] private theorem rateCast_zero :
    ((0 : Rate) : ENNReal) = 0 := by
  rw [← ENNReal.coe_nnratCast, NNRat.cast_zero, ENNReal.coe_zero]

@[simp] private theorem rateCast_one :
    ((1 : Rate) : ENNReal) = 1 := by
  rw [← ENNReal.coe_nnratCast, NNRat.cast_one, ENNReal.coe_one]

private theorem ofReal_rate (r : Rate) :
    ENNReal.ofReal (r : ℝ) = (r : ENNReal) := by
  change ENNReal.ofReal ((r : NNReal) : ℝ) = ((r : NNReal) : ENNReal)
  exact ENNReal.ofReal_coe_nnreal

private theorem rateCast_sum (f : I → Rate) :
    ((∑ i, f i : Rate) : ENNReal) = ∑ i, (f i : ENNReal) := by
  simp_rw [← ENNReal.coe_nnratCast]
  rw [← ENNReal.coe_finsetSum, NNRat.cast_sum]

theorem qMatrix_jumpProb (x y : X) :
    D.qMatrix.jumpProb x y =
      ((D.destinationRate x y / D.totalRate x : Rate) : ENNReal) := by
  by_cases hxy : x = y
  · subst y
    simp [QMatrix.jumpProb, D.destinationRate_self_eq_zero]
  · rw [QMatrix.jumpProb, if_neg hxy, D.qMatrix_rate_offdiag x y hxy,
      D.qMatrix_exitRate, ← NNRat.cast_div, ofReal_rate]

theorem qMatrix_jumpProb_eq_sum (x y : X) :
    D.qMatrix.jumpProb x y =
      ∑ i, if D.destination x i = y then
        ((D.channelRate x i / D.totalRate x : Rate) : ENNReal) else 0 := by
  rw [D.qMatrix_jumpProb]
  have h : D.destinationRate x y / D.totalRate x =
      ∑ i, if D.destination x i = y then
        D.channelRate x i / D.totalRate x else 0 := by
    unfold destinationRate
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [h, rateCast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

def channelWeight (x : X) (o : Option I) : ENNReal :=
  if D.totalRate x = 0 then
    match o with
    | none => 1
    | some _ => 0
  else
    match o with
    | none => 0
    | some i => ((D.channelRate x i / D.totalRate x : Rate) : ENNReal)

theorem channelWeight_sum_eq_one (x : X) :
    ∑ o, D.channelWeight x o = 1 := by
  classical
  by_cases ht : D.totalRate x = 0
  · simp [channelWeight, ht, Fintype.sum_option]
  · simp only [channelWeight, ht, if_false, Fintype.sum_option, zero_add]
    rw [← rateCast_sum]
    have h : ∑ i, D.channelRate x i / D.totalRate x = 1 := by
      rw [← Finset.sum_div]
      exact div_self ht
    rw [h]
    simp

def channelPMF (x : X) : PMF (Option I) :=
  ⟨D.channelWeight x, by
    rw [ENNReal.summable.hasSum_iff, tsum_fintype]
    exact D.channelWeight_sum_eq_one x⟩

def labelDestination (x : X) : Option I → X
  | none => x
  | some i => D.destination x i

theorem channelPMF_map_labelDestination (x : X) :
    (D.channelPMF x).map (D.labelDestination x) = D.qMatrix.embeddedDTMC.step x := by
  classical
  ext y
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_option]
  change (@ite ENNReal (y = x) (Classical.propDecidable _) (D.channelWeight x none) 0) +
      (∑ i, @ite ENNReal (y = D.destination x i) (Classical.propDecidable _)
        (D.channelWeight x (some i)) 0) =
    D.qMatrix.embeddedDTMC.step x y
  by_cases ht : D.totalRate x = 0
  · rw [D.qMatrix.embeddedDTMC_step_of_absorbing
      ((D.qMatrix_isAbsorbing_iff x).mpr ht) y]
    simp [channelWeight.eq_def, ht]
  · rw [D.qMatrix.embeddedDTMC_step_of_nonabsorbing
      (fun ha => ht ((D.qMatrix_isAbsorbing_iff x).mp ha)) y,
      D.qMatrix_jumpProb_eq_sum]
    simp [channelWeight.eq_def, ht, eq_comm]

end FiniteChannels

variable {S : Type u} [Fintype S] [DecidableEq S]

def populationSize (z : State S) : ℕ := ∑ s, z s

/-- A finite molecule-count sublevel, represented by bounded coordinates. -/
abbrev BoundedPopulation (S : Type u) [Fintype S] (R : ℕ) :=
  {v : S → Fin (R + 1) // ∑ s, (v s).val ≤ R}

/-- The third coordinate counts every reaction, including a null reaction. -/
abbrev LocalState (S : Type u) [Fintype S] (R K J : ℕ) :=
  Option (BoundedPopulation S R × Fin K × Fin J)

instance localStateMeasurableSpace (R K J : ℕ) :
    MeasurableSpace (LocalState S R K J) := ⊤

instance localStateMeasurableSingletonClass (R K J : ℕ) :
    MeasurableSingletonClass (LocalState S R K J) := ⟨fun _ => trivial⟩

def boundedPopulation {R : ℕ} (z : State S)
    (hz : populationSize z ≤ R) : BoundedPopulation S R := by
  classical
  refine ⟨fun s => ⟨z s, ?_⟩, ?_⟩
  · exact Nat.lt_succ_of_le
      ((Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s)).trans hz)
  · exact hz

/-- Leaving any one of the three bounds enters the cemetery. -/
def encode (R K J : ℕ) (z : State S) (k j : ℕ) : LocalState S R K J :=
  if h : populationSize z ≤ R ∧ k < K ∧ j < J then
    some (boundedPopulation z h.1, ⟨k, h.2.1⟩, ⟨j, h.2.2⟩)
  else none

def population {R K J : ℕ} : LocalState S R K J → State S
  | none => 0
  | some x => fun s => (x.1.val s).val

def targetCount {R K J : ℕ} : LocalState S R K J → ℕ
  | none => K
  | some x => x.2.1.val

def reactionCount {R K J : ℕ} : LocalState S R K J → ℕ
  | none => J
  | some x => x.2.2.val

omit [DecidableEq S] in
theorem encode_eq_none_iff (R K J : ℕ) (z : State S) (k j : ℕ) :
    encode R K J z k j = none ↔
      ¬ (populationSize z ≤ R ∧ k < K ∧ j < J) := by
  unfold encode
  split_ifs <;> simp_all

omit [DecidableEq S] in
theorem population_encode (R K J : ℕ) (z : State S) (k j : ℕ)
    (h : populationSize z ≤ R ∧ k < K ∧ j < J) :
    population (encode R K J z k j) = z := by
  simp only [encode, dif_pos h, population, boundedPopulation]

omit [DecidableEq S] in
theorem targetCount_encode (R K J : ℕ) (z : State S) (k j : ℕ)
    (h : populationSize z ≤ R ∧ k < K ∧ j < J) :
    targetCount (encode R K J z k j) = k := by
  simp only [encode, dif_pos h, targetCount]

omit [DecidableEq S] in
theorem reactionCount_encode (R K J : ℕ) (z : State S) (k j : ℕ)
    (h : populationSize z ≤ R ∧ k < K ∧ j < J) :
    reactionCount (encode R K J z k j) = j := by
  simp only [encode, dif_pos h, reactionCount]

omit [DecidableEq S] in
theorem population_encode_of_eq_some (R K J : ℕ) (z : State S) (k j : ℕ)
    {x : BoundedPopulation S R × Fin K × Fin J}
    (h : encode R K J z k j = some x) :
    population (some x : LocalState S R K J) = z := by
  unfold encode at h
  split_ifs at h with hb <;> cases h <;> rfl

omit [DecidableEq S] in
theorem targetCount_encode_of_eq_some (R K J : ℕ) (z : State S) (k j : ℕ)
    {x : BoundedPopulation S R × Fin K × Fin J}
    (h : encode R K J z k j = some x) :
    targetCount (some x : LocalState S R K J) = k := by
  unfold encode at h
  split_ifs at h with hb <;> cases h <;> rfl

omit [DecidableEq S] in
theorem reactionCount_encode_of_eq_some (R K J : ℕ) (z : State S) (k j : ℕ)
    {x : BoundedPopulation S R × Fin K × Fin J}
    (h : encode R K J z k j = some x) :
    reactionCount (some x : LocalState S R K J) = j := by
  unfold encode at h
  split_ifs at h with hb <;> cases h <;> rfl

omit [DecidableEq S] in
theorem populationSize_some_le {R K J : ℕ}
    (x : BoundedPopulation S R × Fin K × Fin J) :
    populationSize (population (some x : LocalState S R K J)) ≤ R :=
  x.1.property

variable (N : Network.{u, v} S) [DecidableEq N.I]
variable (inc : State S → N.I → ℕ)

def advance {R K J : ℕ} : LocalState S R K J → N.I → LocalState S R K J
  | none, _ => none
  | some x, i =>
      encode R K J ((N.rxn i).fire (population (some x : LocalState S R K J)))
        (x.2.1.val + inc (population (some x : LocalState S R K J)) i)
        (x.2.2.val + 1)

omit [DecidableEq N.I] in
theorem population_advance_of_eq_some {R K J : ℕ}
    (x y : BoundedPopulation S R × Fin K × Fin J) (i : N.I)
    (h : advance N inc (some x : LocalState S R K J) i = some y) :
    population (some y : LocalState S R K J) =
      (N.rxn i).fire (population (some x : LocalState S R K J)) := by
  exact population_encode_of_eq_some R K J
    ((N.rxn i).fire (population (some x : LocalState S R K J)))
    (x.2.1.val + inc (population (some x : LocalState S R K J)) i)
    (x.2.2.val + 1) h

theorem advance_some_ne {R K J : ℕ}
    (x : BoundedPopulation S R × Fin K × Fin J) (i : N.I) :
    advance N inc (some x : LocalState S R K J) i ≠ some x := by
  intro heq
  have hc := reactionCount_encode_of_eq_some R K J
    ((N.rxn i).fire (population (some x : LocalState S R K J)))
    (x.2.1.val + inc (population (some x : LocalState S R K J)) i)
    (x.2.2.val + 1) heq
  change x.2.2.val = x.2.2.val + 1 at hc
  omega

/-- The auxiliary firing count makes the finite localization free of self-jumps. -/
def channels (R K J : ℕ) : FiniteChannels (LocalState S R K J) N.I := by
  classical
  refine
    { channelRate := fun x i =>
        match x with
        | none => 0
        | some _ => (N.rxn i).propensity (population x)
      destination := advance N inc
      noSelf := ?_ }
  intro x i hi
  cases x with
  | none => exact False.elim (hi rfl)
  | some x => exact advance_some_ne N inc x i

@[simp] theorem channels_totalRate_none (R K J : ℕ) :
    (channels N inc R K J).totalRate none = 0 := by
  simp [FiniteChannels.totalRate, channels]

@[simp] theorem channels_totalRate_some (R K J : ℕ)
    (x : BoundedPopulation S R × Fin K × Fin J) :
    (channels N inc R K J).totalRate (some x) =
      N.totalPropensity (population (some x : LocalState S R K J)) := rfl

theorem channels_channelPMF_some (hPos : N.hasPositiveRates) (R K J : ℕ)
    (x : BoundedPopulation S R × Fin K × Fin J) :
    (channels N inc R K J).channelPMF (some x) =
      massActionPMF N hPos (population (some x : LocalState S R K J)) := by
  classical
  ext o
  change (channels N inc R K J).channelWeight (some x) o =
    massActionWeight N hPos (population (some x : LocalState S R K J)) o
  unfold FiniteChannels.channelWeight
  rw [channels_totalRate_some]
  unfold massActionWeight
  by_cases ht : N.Terminal (population (some x : LocalState S R K J))
  · have hz := Network.totalPropensity_eq_zero_of_terminal ht
    simp [ht, hz]
    cases o <;> rfl
  · have hz := totalPropensity_ne_zero_of_nonTerminal N hPos ht
    simp only [ht, hz, dite_false, if_false]
    cases o <;> rfl

@[simp] theorem channels_isAbsorbing_none (R K J : ℕ) :
    (channels N inc R K J).qMatrix.IsAbsorbing none := by
  rw [FiniteChannels.qMatrix_isAbsorbing_iff, channels_totalRate_none]

theorem channels_isAbsorbing_some_iff (hPos : N.hasPositiveRates) (R K J : ℕ)
    (x : BoundedPopulation S R × Fin K × Fin J) :
    (channels N inc R K J).qMatrix.IsAbsorbing (some x) ↔
      N.Terminal (population (some x : LocalState S R K J)) := by
  rw [FiniteChannels.qMatrix_isAbsorbing_iff, channels_totalRate_some]
  exact Network.totalPropensity_eq_zero_iff_terminal_of_positive_rates hPos

end FiniteLocalizationDefinition


section ExponentialScaling

theorem unitExponential_div_map (r : ℝ) (hr : 0 < r) :
    (expMeasure 1).map (fun e : ℝ => e / r) = expMeasure r := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  have hm : Measurable (fun e : ℝ => e / r) := by fun_prop
  letI : IsProbabilityMeasure ((expMeasure 1).map (fun e : ℝ => e / r)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.eq_of_cdf
  ext t
  rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
  have hpre : (fun e : ℝ => e / r) ⁻¹' Set.Iic t = Set.Iic (t * r) := by
    ext e
    exact div_le_iff₀ hr
  rw [hpre, ← cdf_eq_real,
    cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1),
    cdf_expMeasure_eq hr]
  by_cases ht : 0 ≤ t
  · rw [if_pos (mul_nonneg ht hr.le), if_pos ht]
    simp only [one_mul, mul_comm t r]
  · have htr : ¬0 ≤ t * r := by
      exact not_le.mpr (mul_neg_of_neg_of_pos (lt_of_not_ge ht) hr)
    simp [ht, htr]

end ExponentialScaling

section PrefixUniqueness

variable {X : Type*} [MeasurableSpace X]

def prefixAppend (n : ℕ) (p : ((i : Finset.Iic n) → X) × X) :
    (i : Finset.Iic (n + 1)) → X :=
  fun i => if hi : i.1 ≤ n
    then p.1 ⟨i.1, Finset.mem_Iic.mpr hi⟩ else p.2

@[fun_prop]
theorem measurable_prefixAppend (n : ℕ) :
    Measurable (prefixAppend (X := X) n) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.1 ≤ n
  · have hm : Measurable
        (fun p : ((j : Finset.Iic n) → X) × X =>
          p.1 (⟨i.1, Finset.mem_Iic.mpr hi⟩ : Finset.Iic n)) :=
        (measurable_pi_apply (X := fun _ : Finset.Iic n => X)
          (⟨i.1, Finset.mem_Iic.mpr hi⟩ : Finset.Iic n)).comp measurable_fst
    simpa [prefixAppend, hi] using hm
  · simpa [prefixAppend, hi] using
      (measurable_snd : Measurable (Prod.snd : ((i : Finset.Iic n) → X) × X → X))

omit [MeasurableSpace X] in
theorem prefixAppend_history_next (n : ℕ) (ω : ℕ → X) :
    prefixAppend n (frestrictLe (π := fun _ : ℕ => X) n ω, ω (n + 1)) = frestrictLe (π := fun _ : ℕ => X) (n + 1) ω := by
  funext i
  by_cases hi : i.1 ≤ n
  · simp [prefixAppend, hi]
  · have hi' : i.1 = n + 1 := by
      have hiBound := Finset.mem_Iic.mp i.2
      omega
    simp [prefixAppend, hi, hi']

theorem measure_eq_of_prefix_map_eq (μ ν : Measure (ℕ → X)) [IsFiniteMeasure μ]
    (hprefix : ∀ n : ℕ,
      μ.map (frestrictLe (π := fun _ => X) n) =
        ν.map (frestrictLe (π := fun _ => X) n))
    (hmass : μ Set.univ = ν Set.univ) :
    μ = ν := by
  refine ext_of_generate_finite (measurableCylinders (fun _ : ℕ => X))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (fun A hA => ?_) hmass
  obtain ⟨n, B, hB, rfl⟩ :
      ∃ n B, MeasurableSet B ∧ A = cylinder (Finset.Iic n) B := by
    simpa [measurableCylinders_nat] using hA
  have hp : Measurable (frestrictLe (π := fun _ : ℕ => X) n) :=
    measurable_frestrictLe (X := fun _ : ℕ => X) n
  have h := congrArg
    (fun ρ : Measure ((i : Finset.Iic n) → X) => ρ B) (hprefix n)
  dsimp only at h
  rw [Measure.map_apply (μ := μ) hp hB,
    Measure.map_apply (μ := ν) hp hB] at h
  simpa only [cylinder, frestrictLe] using h

theorem measure_eq_of_history_next
    (μ ν : Measure (ℕ → X)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X) X)
    (hinitial : μ.map (frestrictLe (π := fun _ => X) 0) =
      ν.map (frestrictLe (π := fun _ => X) 0))
    (hμ : ∀ n : ℕ,
      μ.map (fun ω => (frestrictLe (π := fun _ : ℕ => X) n ω, ω (n + 1))) =
        μ.map (frestrictLe (π := fun _ : ℕ => X) n) ⊗ₘ κ n)
    (hν : ∀ n : ℕ,
      ν.map (fun ω => (frestrictLe (π := fun _ : ℕ => X) n ω, ω (n + 1))) =
        ν.map (frestrictLe (π := fun _ : ℕ => X) n) ⊗ₘ κ n) :
    μ = ν := by
  apply measure_eq_of_prefix_map_eq μ ν
  · intro n
    induction n with
    | zero => exact hinitial
    | succ n ih =>
        have hmap (ρ : Measure (ℕ → X)) :
            (ρ.map (fun ω => (frestrictLe (π := fun _ : ℕ => X) n ω, ω (n + 1)))).map
                (prefixAppend n) =
              ρ.map (frestrictLe (π := fun _ : ℕ => X) (n + 1)) := by
          rw [Measure.map_map (measurable_prefixAppend n) (by fun_prop)]
          congr 1
          funext ω
          exact prefixAppend_history_next n ω
        rw [← hmap μ, ← hmap ν, hμ n, hν n, ih]
  · simp

end PrefixUniqueness

section CanonicalUniqueness

variable {X : Type*} [Fintype X] [DecidableEq X] [Countable X]
  [MeasurableSpace X] [MeasurableSingletonClass X]

theorem eq_canonicalRecordMeasure_of_history_next
    (Q : Ripple.CTMC.QMatrix X) (x₀ : X)
    (μ : Measure (ℕ → ℝ × X)) [IsProbabilityMeasure μ]
    (hinitial : μ.map (frestrictLe (π := fun _ => ℝ × X) 0) =
      (Measure.dirac (0, x₀)).map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ × X)).symm)
    (hnext : ∀ n : ℕ,
      μ.map (fun ω => (frestrictLe (π := fun _ : ℕ => ℝ × X) n ω, ω (n + 1))) =
        μ.map (frestrictLe (π := fun _ : ℕ => ℝ × X) n) ⊗ₘ Q.jumpHoldTrajectoryStepKernel n) :
    μ = Q.canonicalRecordMeasure x₀ := by
  apply measure_eq_of_history_next μ (Q.canonicalRecordMeasure x₀)
    Q.jumpHoldTrajectoryStepKernel
  · exact hinitial.trans (Q.canonicalRecordMeasure_map_frestrictLe_zero x₀).symm
  · exact hnext
  · exact Q.canonicalRecordMeasure_history_next x₀

end CanonicalUniqueness


section FreshClocks

/-- The clocks already used by the first n reaction records. -/
def clockPrefix (n : ℕ) (e : ℕ → ℝ) : Fin n → ℝ :=
  fun j => e j

@[fun_prop]
theorem measurable_clockPrefix (n : ℕ) :
    Measurable (clockPrefix n) := by
  unfold clockPrefix
  fun_prop

theorem unitClockLaw_map_prefix (n : ℕ) :
    unitClockLaw.map (clockPrefix n) =
      Measure.pi (fun _ : Fin n => expMeasure 1) := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  simpa only [unitClockLaw, clockPrefix, Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => expMeasure 1)
      (f := fun j : Fin n => j.val) Fin.val_injective)

theorem clockPrefix_indep_next (n : ℕ) :
    IndepFun (clockPrefix n) (fun e : ℕ → ℝ => e n) unitClockLaw := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hi : iIndepFun (fun i : ℕ => fun e : ℕ → ℝ => e i) unitClockLaw := by
    exact iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1)
      (X := fun (_ : ℕ) (x : ℝ) => x) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) ({n} : Finset ℕ) := by simp
  have h := iIndepFun.indepFun_finset (Finset.range n) ({n} : Finset ℕ)
    hd hi (fun i => measurable_pi_apply i)
  have hc := h.comp
    (φ := fun p : (i : Finset.range n) → ℝ =>
      fun j : Fin n => p ⟨j.val, Finset.mem_range.mpr j.isLt⟩)
    (ψ := fun p : (i : ({n} : Finset ℕ)) → ℝ => p ⟨n, by simp⟩)
    (by
      apply measurable_pi_lambda
      intro j
      exact measurable_pi_apply (X := fun _ : Finset.range n => ℝ)
        (⟨j.val, Finset.mem_range.mpr j.isLt⟩ : Finset.range n))
    (measurable_pi_apply (X := fun _ : ({n} : Finset ℕ) => ℝ)
      (⟨n, by simp⟩ : ({n} : Finset ℕ)))
  simpa only [Function.comp_def, clockPrefix] using hc

/-- The next clock is fresh even after all earlier clocks have been observed. -/
theorem unitClockLaw_map_prefix_next (n : ℕ) :
    unitClockLaw.map (fun e => (clockPrefix n e, e n)) =
      (Measure.pi (fun _ : Fin n => expMeasure 1)).prod (expMeasure 1) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map
    (measurable_clockPrefix n).aemeasurable
    (measurable_pi_apply n).aemeasurable).mp (clockPrefix_indep_next n)]
  rw [unitClockLaw_map_prefix, unitClockLaw_map_eval]

end FreshClocks


section SourceJointLaw

universe uJ vJ
variable {S : Type uJ} [Fintype S] [DecidableEq S]
variable (N : Network.{uJ, vJ} S) [DecidableEq N.I]
variable (hPos : N.hasPositiveRates) (z0 : State S)

/-- The complete finite label history and its next label, with the actual
history-dependent mass-action step kernel. -/
theorem rawLaw_map_history_next (n : ℕ) :
    (rawLaw N hPos z0).map
        (fun ω => (frestrictLe (π := fun _ => Option N.I) n ω, ω (n + 1))) =
      (rawLaw N hPos z0).map (frestrictLe (π := fun _ => Option N.I) n) ⊗ₘ
        stepKernel N hPos z0 n := by
  change
    (Kernel.traj (X := fun _ => Option N.I)
      (fun k => stepKernel N hPos z0 k) 0 (fun _ => none)).map
        (fun ω => (frestrictLe (π := fun _ : ℕ => Option N.I) n ω, ω (n + 1))) =
    (Kernel.traj (X := fun _ => Option N.I)
      (fun k => stepKernel N hPos z0 k) 0 (fun _ => none)).map
        (frestrictLe (π := fun _ : ℕ => Option N.I) n) ⊗ₘ stepKernel N hPos z0 n
  rw [← Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => Option N.I) (Nat.zero_le n),
    Kernel.traj_map_frestrictLe_apply (X := fun _ => Option N.I)]

/-- Simultaneously expose all past labels, all past clocks, and the next
label-clock pair.  The ordering groups the label data and the clock data. -/
theorem timedLaw_map_history_next (n : ℕ) :
    (timedLaw N hPos z0).map
        (fun η =>
          ((frestrictLe (π := fun _ => Option N.I) n η.1, η.1 (n + 1)),
            (clockPrefix n η.2, η.2 n))) =
      ((rawLaw N hPos z0).map (frestrictLe (π := fun _ => Option N.I) n) ⊗ₘ
        stepKernel N hPos z0 n).prod
          ((Measure.pi (fun _ : Fin n => expMeasure 1)).prod (expMeasure 1)) := by
  letI := rawLaw_isProbabilityMeasure N hPos z0
  change
    ((rawLaw N hPos z0).prod unitClockLaw).map
      (Prod.map
        (fun ω => (frestrictLe (π := fun _ => Option N.I) n ω, ω (n + 1)))
        (fun e => (clockPrefix n e, e n))) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    rawLaw_map_history_next N hPos z0 n, unitClockLaw_map_prefix_next n]

end SourceJointLaw


section ChannelRecords

variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]

namespace FiniteChannels

noncomputable def channelRecord (D : FiniteChannels X I) (x : X)
    (u : ℝ × Option I) : ℝ × X :=
  if D.totalRate x = 0 then (0, x)
  else (u.1 / (D.totalRate x : ℝ), D.labelDestination x u.2)

omit [MeasurableSingletonClass X] in
@[fun_prop]
theorem measurable_channelRecord (D : FiniteChannels X I) (x : X) :
    Measurable (D.channelRecord x) := by
  unfold channelRecord
  split_ifs
  · exact measurable_const
  · exact (measurable_fst.div_const _).prodMk
      ((measurable_of_countable (D.labelDestination x)).comp measurable_snd)

theorem channelRecord_map (D : FiniteChannels X I) (x : X) :
    ((expMeasure 1).prod (D.channelPMF x).toMeasure).map
        (D.channelRecord x) =
      D.qMatrix.jumpHoldStepMeasureTotal x := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  by_cases hzero : D.totalRate x = 0
  · have habs : D.qMatrix.IsAbsorbing x :=
      (D.qMatrix_isAbsorbing_iff x).mpr hzero
    rw [D.qMatrix.jumpHoldStepMeasureTotal_of_absorbing habs]
    have hrec : D.channelRecord x = fun _ => (0, x) := by
      funext p
      simp only [channelRecord, if_pos hzero]
    rw [hrec]
    simp
  · have habs : ¬D.qMatrix.IsAbsorbing x := by
      intro hh
      exact hzero ((D.qMatrix_isAbsorbing_iff x).mp hh)
    have hrate : 0 < (D.totalRate x : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hzero : (0 : Rate) < D.totalRate x)
    have hdest : Measurable (D.labelDestination x) :=
      measurable_of_countable _
    rw [D.qMatrix.jumpHoldStepMeasureTotal_of_nonabsorbing habs]
    have hrec : D.channelRecord x =
        Prod.map (fun e : ℝ => e / (D.totalRate x : ℝ))
          (D.labelDestination x) := by
      funext p
      simp only [channelRecord, if_neg hzero, Prod.map]
    rw [hrec]
    change ((expMeasure 1).prod (D.channelPMF x).toMeasure).map
        (Prod.map (fun e : ℝ => e / (D.totalRate x : ℝ))
          (D.labelDestination x)) =
      (expMeasure (D.qMatrix.exitRate x)).prod
        (D.qMatrix.embeddedDTMC.step x).toMeasure
    rw [← Measure.map_prod_map _ _ (by fun_prop) hdest,
      unitExponential_div_map _ hrate,
      PMF.toMeasure_map (D.labelDestination x) (D.channelPMF x) hdest,
      D.channelPMF_map_labelDestination x, D.qMatrix_exitRate x]

end FiniteChannels

end ChannelRecords


section RecordTransducer

variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]

namespace FiniteChannels

noncomputable def labelStep (D : FiniteChannels X I) (x : X) (o : Option I) : X :=
  if D.totalRate x = 0 then x else D.labelDestination x o

noncomputable def labelStatePath (D : FiniteChannels X I) (x₀ : X)
    (ω : ℕ → Option I) : ℕ → X
  | 0 => x₀
  | n + 1 => D.labelStep (D.labelStatePath x₀ ω n) (ω (n + 1))

@[fun_prop]
theorem measurable_labelStatePath (D : FiniteChannels X I) (x₀ : X) (n : ℕ) :
    Measurable (fun ω => D.labelStatePath x₀ ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact (measurable_of_countable
        (fun p : X × Option I => D.labelStep p.1 p.2)).comp
        (ih.prodMk (measurable_pi_apply (n + 1)))

noncomputable def recordMap (D : FiniteChannels X I) (x₀ : X)
    (η : (ℕ → Option I) × (ℕ → ℝ)) : ℕ → ℝ × X
  | 0 => (0, x₀)
  | n + 1 => D.channelRecord (D.labelStatePath x₀ η.1 n)
      (η.2 n, η.1 (n + 1))

omit [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)] in
@[simp]
theorem recordMap_zero (D : FiniteChannels X I) (x₀ : X)
    (η : (ℕ → Option I) × (ℕ → ℝ)) :
    D.recordMap x₀ η 0 = (0, x₀) := rfl

omit [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)] in
@[simp]
theorem recordMap_state (D : FiniteChannels X I) (x₀ : X)
    (η : (ℕ → Option I) × (ℕ → ℝ)) (n : ℕ) :
    (D.recordMap x₀ η n).2 = D.labelStatePath x₀ η.1 n := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [recordMap, labelStatePath, channelRecord, labelStep]
      split_ifs <;> rfl

omit [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)] in
theorem recordMap_of_zero_rate (D : FiniteChannels X I) (x₀ : X)
    (η : (ℕ → Option I) × (ℕ → ℝ)) (n : ℕ)
    (h : D.totalRate (D.labelStatePath x₀ η.1 n) = 0) :
    D.recordMap x₀ η (n + 1) = (0, D.labelStatePath x₀ η.1 n) := by
  simp [recordMap, channelRecord, h]

@[fun_prop]
theorem measurable_recordMap (D : FiniteChannels X I) (x₀ : X) :
    Measurable (D.recordMap x₀) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n =>
      have hs : Measurable (fun η : (ℕ → Option I) × (ℕ → ℝ) =>
          D.labelStatePath x₀ η.1 n) :=
        (D.measurable_labelStatePath x₀ n).comp measurable_fst
      have hz : MeasurableSet {x : X | D.totalRate x = 0} :=
        (Set.to_countable _).measurableSet
      have hm : Measurable (fun p : X × Option I =>
          D.labelDestination p.1 p.2) := measurable_of_countable _
      change Measurable (fun η : (ℕ → Option I) × (ℕ → ℝ) =>
        if D.totalRate (D.labelStatePath x₀ η.1 n) = 0 then
          (0, D.labelStatePath x₀ η.1 n)
        else (η.2 n / (D.totalRate (D.labelStatePath x₀ η.1 n) : ℝ),
          D.labelDestination (D.labelStatePath x₀ η.1 n) (η.1 (n + 1))))
      refine Measurable.ite (hs hz)
        (measurable_const.prodMk hs) ?_
      have hrate : Measurable (fun η : (ℕ → Option I) × (ℕ → ℝ) =>
          (D.totalRate (D.labelStatePath x₀ η.1 n) : ℝ)) :=
        (measurable_of_countable (fun x : X => (D.totalRate x : ℝ))).comp hs
      exact (((measurable_pi_apply n).comp measurable_snd).div hrate).prodMk
        (hm.comp (hs.prodMk ((measurable_pi_apply (n + 1)).comp measurable_fst)))

theorem recordMap_initial
    (D : FiniteChannels X I) (x₀ : X)
    (μ : Measure ((ℕ → Option I) × (ℕ → ℝ))) [IsProbabilityMeasure μ] :
    (μ.map (D.recordMap x₀)).map (frestrictLe (π := fun _ => ℝ × X) 0) =
      (Measure.dirac (0, x₀)).map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ × X)).symm := by
  rw [Measure.map_map (measurable_frestrictLe (X := fun _ : ℕ => ℝ × X) 0) (D.measurable_recordMap x₀)]
  have hc :
      (frestrictLe (π := fun _ => ℝ × X) 0) ∘ D.recordMap x₀ =
        fun _ => (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 => ℝ × X)).symm (0, x₀) := by
    funext η i
    rcases i with ⟨i, hi⟩
    have hi' : i = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hi)
    subst i
    rfl
  rw [hc]
  simp

end FiniteChannels

end RecordTransducer


namespace FiniteChannels

universe uC vC
variable {X : Type uC} {I : Type vC}
variable [Fintype X] [DecidableEq X] [Fintype I]

/-- The localized state at index n uses only labels through n. -/
theorem labelStatePath_congr_prefix (D : FiniteChannels X I) (x0 : X)
    (n : ℕ) {ω ω' : ℕ → Option I}
    (hω : ∀ k, k ≤ n → ω k = ω' k) :
    D.labelStatePath x0 ω n = D.labelStatePath x0 ω' n := by
  revert hω
  induction n with
  | zero =>
      intro _
      rfl
  | succ n ih =>
      intro hω
      simp only [labelStatePath]
      rw [ih (fun k hk => hω k (hk.trans (Nat.le_succ n))),
        hω (n + 1) le_rfl]

end FiniteChannels

section LocalizedSourceConsistency

universe uS vS
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable (N : Network.{uS, vS} S) [DecidableEq N.I]

/-- The cemetery remains absorbing for every raw label. -/
theorem channels_labelStep_cemetery (inc : State S → N.I → ℕ)
    (R K J : ℕ) (o : Option N.I) :
    (channels N inc R K J).labelStep none o = none := by
  simp [FiniteChannels.labelStep, FiniteChannels.totalRate, channels]

/-- Before killing, the localized population equals the source population. -/
theorem labelStatePath_population_of_fired_eq_label
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ)
    (ω : ℕ → Option N.I)
    (hlabels : ∀ n, pathFired N z0 ω n = ω (n + 1)) :
    ∀ n (x : BoundedPopulation S R × Fin K × Fin J),
      (channels N inc R K J).labelStatePath
        (encode R K J z0 k0 0) ω n = some x →
      population (some x) = pathState N z0 ω n := by
  classical
  let D := channels N inc R K J
  let x0 := encode R K J z0 k0 0
  change ∀ n (x : BoundedPopulation S R × Fin K × Fin J),
    D.labelStatePath x0 ω n = some x →
      population (some x) = pathState N z0 ω n
  intro n
  induction n with
  | zero =>
      intro x hx
      exact population_encode_of_eq_some R K J z0 k0 0 hx
  | succ n ih =>
      intro y hy
      cases hprev : D.labelStatePath x0 ω n with
      | none =>
          have hnext : D.labelStatePath x0 ω (n + 1) = none := by
            rw [FiniteChannels.labelStatePath, hprev]
            exact channels_labelStep_cemetery N inc R K J _
          have hbad : (none : LocalState S R K J) = some y := hnext.symm.trans hy
          cases hbad
      | some x =>
          have hpop : population (some x) = pathState N z0 ω n := ih x hprev
          have hvalid := pathFired_valid N z0 ω n
          rw [hlabels n] at hvalid
          cases ho : ω (n + 1) with
          | none =>
              have hterminal : pathState N z0 ω (n + 1) = pathState N z0 ω n ∧
                  N.Terminal (pathState N z0 ω n) := by
                simpa only [ho] using hvalid
              have hstay := hterminal.1
              have hnext : D.labelStatePath x0 ω (n + 1) = some x := by
                rw [FiniteChannels.labelStatePath, hprev, ho]
                simp [FiniteChannels.labelStep, FiniteChannels.labelDestination]
              have hxy : x = y := Option.some.inj (hnext.symm.trans hy)
              subst y
              exact hpop.trans hstay.symm
          | some i =>
              have hstep : N.StepAt i (pathState N z0 ω n)
                  (pathState N z0 ω (n + 1)) := by
                simpa only [ho] using hvalid
              have hNT : ¬ N.Terminal (pathState N z0 ω n) :=
                fun hT => hT i hstep.1
              have hrate : D.totalRate (some x) ≠ 0 := by
                change N.totalPropensity (population (some x)) ≠ 0
                rw [hpop]
                exact totalPropensity_ne_zero_of_nonTerminal N hPos hNT
              have hadvance : advance N inc (some x) i = some y := by
                change D.labelDestination (some x) (some i) = some y
                simpa only [FiniteChannels.labelStatePath, hprev, ho,
                  FiniteChannels.labelStep, if_neg hrate] using hy
              calc
                population (some y) = (N.rxn i).fire (population (some x)) :=
                  population_advance_of_eq_some N inc x y i hadvance
                _ = (N.rxn i).fire (pathState N z0 ω n) := by rw [hpop]
                _ = pathState N z0 ω (n + 1) := hstep.2.symm

end LocalizedSourceConsistency


section FiniteHistories

variable {I : Type*} [MeasurableSpace (Option I)]

def extendLabels (n : ℕ) (p : (i : Finset.Iic n) → Option I) : ℕ → Option I :=
  fun j => if h : j ≤ n then p ⟨j, Finset.mem_Iic.mpr h⟩ else none

def extendClocks (n : ℕ) (c : Fin n → ℝ) : ℕ → ℝ :=
  fun j => if h : j < n then c ⟨j, h⟩ else 0

@[fun_prop]
theorem measurable_extendLabels (n : ℕ) :
    Measurable (extendLabels (I := I) n) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j ≤ n
  · simpa [extendLabels, hj] using
      (measurable_pi_apply
        (X := fun _ : Finset.Iic n => Option I)
        (⟨j, Finset.mem_Iic.mpr hj⟩ : Finset.Iic n))
  · simpa [extendLabels, hj] using
      (measurable_const : Measurable
        (fun _ : ((i : Finset.Iic n) → Option I) => (none : Option I)))

@[fun_prop]
theorem measurable_extendClocks (n : ℕ) :
    Measurable (extendClocks n) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j < n
  · simpa [extendClocks, hj] using
      (measurable_pi_apply
        (X := fun _ : Fin n => ℝ) (⟨j, hj⟩ : Fin n))
  · simpa [extendClocks, hj] using
      (measurable_const : Measurable (fun _ : Fin n → ℝ => (0 : ℝ)))

omit [MeasurableSpace (Option I)] in
@[simp]
theorem extendLabels_restrict_apply (n j : ℕ) (ω : ℕ → Option I) (hj : j ≤ n) :
    extendLabels n (frestrictLe (π := fun _ : ℕ => Option I) n ω) j = ω j := by
  simp [extendLabels, hj]

@[simp]
theorem extendClocks_prefix_apply (n j : ℕ) (e : ℕ → ℝ) (hj : j < n) :
    extendClocks n (clockPrefix n e) j = e j := by
  simp [extendClocks, clockPrefix, hj]

end FiniteHistories

section CausalRecordHistories

variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]

namespace FiniteChannels

noncomputable def recordHistory (D : FiniteChannels X I) (x₀ : X) (n : ℕ)
    (pc : ((i : Finset.Iic n) → Option I) × (Fin n → ℝ)) :
    (i : Finset.Iic n) → ℝ × X :=
  frestrictLe (π := fun _ : ℕ => ℝ × X) n
    (D.recordMap x₀ (extendLabels n pc.1, extendClocks n pc.2))

@[fun_prop]
theorem measurable_recordHistory (D : FiniteChannels X I) (x₀ : X) (n : ℕ) :
    Measurable (D.recordHistory x₀ n) :=
  (measurable_frestrictLe (X := fun _ : ℕ => ℝ × X) n).comp ((D.measurable_recordMap x₀).comp
    (((measurable_extendLabels n).comp measurable_fst).prodMk
      ((measurable_extendClocks n).comp measurable_snd)))

omit [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)] in
theorem recordHistory_currentState (D : FiniteChannels X I) (x₀ : X) (n : ℕ)
    (pc : ((i : Finset.Iic n) → Option I) × (Fin n → ℝ)) :
    Ripple.CTMC.QMatrix.currentStateFromHistory n (D.recordHistory x₀ n pc) =
      D.labelStatePath x₀ (extendLabels n pc.1) n := by
  exact D.recordMap_state x₀
    (extendLabels n pc.1, extendClocks n pc.2) n

omit [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)] in
theorem recordHistory_restrict (D : FiniteChannels X I) (x₀ : X) (n : ℕ)
    (η : (ℕ → Option I) × (ℕ → ℝ)) :
    D.recordHistory x₀ n (frestrictLe (π := fun _ : ℕ => Option I) n η.1, clockPrefix n η.2) =
      frestrictLe (π := fun _ : ℕ => ℝ × X) n (D.recordMap x₀ η) := by
  funext i
  rcases i with ⟨i, hi⟩
  have hin : i ≤ n := Finset.mem_Iic.mp hi
  cases i with
  | zero => rfl
  | succ k =>
      have hk : k < n := by omega
      have hs :
          D.labelStatePath x₀ (extendLabels n (frestrictLe (π := fun _ : ℕ => Option I) n η.1)) k =
            D.labelStatePath x₀ η.1 k := by
        apply D.labelStatePath_congr_prefix x₀ k
        intro j hj
        exact extendLabels_restrict_apply n j η.1 (by omega)
      change D.channelRecord
          (D.labelStatePath x₀ (extendLabels n (frestrictLe (π := fun _ : ℕ => Option I) n η.1)) k)
          (extendClocks n (clockPrefix n η.2) k,
            extendLabels n (frestrictLe (π := fun _ : ℕ => Option I) n η.1) (k + 1)) =
        D.channelRecord (D.labelStatePath x₀ η.1 k) (η.2 k, η.1 (k + 1))
      rw [hs, extendClocks_prefix_apply n k η.2 hk,
        extendLabels_restrict_apply n (k + 1) η.1 hin]

noncomputable def nextRecord (D : FiniteChannels X I) (x₀ : X) (n : ℕ)
    (u : (((i : Finset.Iic n) → Option I) × (Fin n → ℝ)) × (Option I × ℝ)) :
    ℝ × X :=
  D.channelRecord (D.labelStatePath x₀ (extendLabels n u.1.1) n)
    (u.2.2, u.2.1)

@[fun_prop]
theorem measurable_nextRecord (D : FiniteChannels X I) (x₀ : X) (n : ℕ) :
    Measurable (D.nextRecord x₀ n) := by
  have hs : Measurable (fun u :
      (((i : Finset.Iic n) → Option I) × (Fin n → ℝ)) × (Option I × ℝ) =>
      D.labelStatePath x₀ (extendLabels n u.1.1) n) := by
    exact (D.measurable_labelStatePath x₀ n).comp
      ((measurable_extendLabels n).comp (measurable_fst.comp measurable_fst))
  have hm : Measurable (fun p : X × (ℝ × Option I) =>
      D.channelRecord p.1 p.2) := by
    refine measurable_from_prod_countable_right ?_
    intro x
    exact D.measurable_channelRecord x
  exact hm.comp (hs.prodMk ((measurable_snd.comp measurable_snd).prodMk
    (measurable_fst.comp measurable_snd)))

omit [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)] in
theorem nextRecord_restrict (D : FiniteChannels X I) (x₀ : X) (n : ℕ)
    (η : (ℕ → Option I) × (ℕ → ℝ)) :
    D.nextRecord x₀ n
        ((frestrictLe (π := fun _ : ℕ => Option I) n η.1, clockPrefix n η.2), (η.1 (n + 1), η.2 n)) =
      D.recordMap x₀ η (n + 1) := by
  have hs :
      D.labelStatePath x₀ (extendLabels n (frestrictLe (π := fun _ : ℕ => Option I) n η.1)) n =
        D.labelStatePath x₀ η.1 n := by
    apply D.labelStatePath_congr_prefix x₀ n
    intro j hj
    exact extendLabels_restrict_apply n j η.1 hj
  simpa only [nextRecord, recordMap, hs]

end FiniteChannels

end CausalRecordHistories


section LocalizedSourceAlmostSure

universe uA vA
variable {S : Type uA} [Fintype S] [DecidableEq S]
variable (N : Network.{uA, vA} S) [DecidableEq N.I]

/-- The source raw jump law draws its actual enabled labels almost surely. -/
theorem source_fired_eq_label_ae (hPos : N.hasPositiveRates) (z0 : State S) :
    ∀ᵐ ω ∂rawLaw N hPos z0, ∀ n,
      pathFired N z0 ω n = ω (n + 1) := by
  have hprefix (ω : ℕ → Option N.I) (n : ℕ) :
      prefixToState N z0 n (frestrictLe (π := fun _ : ℕ => Option N.I) n ω) = pathState N z0 ω n :=
    prefixToState_eq_pathState N z0 ω n
  have hnonnull : ∀ᵐ ω ∂rawLaw N hPos z0, ¬ ∃ n,
      massActionPMF N hPos (pathState N z0 ω n) (ω (n + 1)) = 0 := by
    rw [ae_iff]
    simpa only [not_not, hprefix] using rawLaw_null_label N hPos z0
  filter_upwards [hnonnull] with ω hω n
  exact pathFired_eq_label_of_mass_ne_zero N hPos z0 ω n
    (fun h => hω ⟨n, h⟩)

/-- All live localized populations agree with the original population on one
conull set of timed paths. -/
theorem labelStatePath_population_ae
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ) :
    ∀ᵐ η ∂timedLaw N hPos z0,
      ∀ n (x : BoundedPopulation S R × Fin K × Fin J),
        (channels N inc R K J).labelStatePath
          (encode R K J z0 k0 0) η.1 n = some x →
        population (some x) = pathState N z0 η.1 n := by
  filter_upwards [timedLaw_fired_eq_label_ae N hPos z0] with η hη
  exact labelStatePath_population_of_fired_eq_label
    N hPos inc R K J z0 k0 η.1 hη

/-- Source/localized population agreement for almost every finite prefix. -/
theorem labelStatePath_population_prefix_ae
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 n : ℕ) :
    ∀ᵐ p ∂(rawLaw N hPos z0).map
        (frestrictLe (π := fun _ : ℕ => Option N.I) n),
      ∀ x : BoundedPopulation S R × Fin K × Fin J,
        (channels N inc R K J).labelStatePath
          (encode R K J z0 k0 0) (extendLabels n p) n = some x →
        population (some x) = prefixToState N z0 n p := by
  apply (ae_map_iff (measurable_frestrictLe (X := fun _ : ℕ => Option N.I) n).aemeasurable
    (measurableSet_prefixSet N n _)).2
  filter_upwards [source_fired_eq_label_ae N hPos z0] with ω hω
  intro x hx
  have hlocal :
      (channels N inc R K J).labelStatePath (encode R K J z0 k0 0)
          (extendLabels n (frestrictLe (π := fun _ : ℕ => Option N.I) n ω)) n =
        (channels N inc R K J).labelStatePath (encode R K J z0 k0 0) ω n := by
    apply FiniteChannels.labelStatePath_congr_prefix
    intro k hk
    simp only [extendLabels, dif_pos hk, frestrictLe_apply]
  have hx' :
      (channels N inc R K J).labelStatePath
        (encode R K J z0 k0 0) ω n = some x :=
    hlocal.symm.trans hx
  have hpop := labelStatePath_population_of_fired_eq_label
    N hPos inc R K J z0 k0 ω hω n x hx'
  exact hpop.trans (prefixToState_eq_pathState N z0 ω n).symm

end LocalizedSourceAlmostSure


section CausalTransport

variable {A B C E H Y : Type*}
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace E] [MeasurableSpace H] [MeasurableSpace Y]

theorem map_causal_history_next
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (ν : Measure C) [SFinite ν] (ξ : Measure E) [SFinite ξ]
    (θ : Kernel H Y) [IsSFiniteKernel θ]
    (history : A × C → H) (hHistory : Measurable history)
    (next : (A × C) × (B × E) → Y) (hNext : Measurable next)
    (hrow : ∀ᵐ ac ∂μ.prod ν,
      ((κ ac.1).prod ξ).map (fun be => next (ac, be)) =
        θ (history ac)) :
    ((μ ⊗ₘ κ).prod (ν.prod ξ)).map
        (fun q => (history (q.1.1, q.2.1),
          next ((q.1.1, q.2.1), (q.1.2, q.2.2)))) =
      ((μ.prod ν).map history) ⊗ₘ θ := by
  have hMap : Measurable (fun q : (A × B) × (C × E) =>
      (history (q.1.1, q.2.1),
        next ((q.1.1, q.2.1), (q.1.2, q.2.2)))) := by
    fun_prop
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  have hInner : Measurable (fun ac : A × C => ∫⁻ be,
      f (history ac, next (ac, be)) ∂(κ ac.1).prod ξ) := by
    have hsplit :
        (fun ac : A × C => ∫⁻ be,
          f (history ac, next (ac, be)) ∂(κ ac.1).prod ξ) =
        (fun ac : A × C => ∫⁻ b, ∫⁻ e,
          f (history ac, next (ac, (b, e))) ∂ξ ∂κ ac.1) := by
      funext ac
      exact lintegral_prod _ (by fun_prop)
    rw [hsplit]
    have hPair : Measurable (fun z : (A × C) × B => ∫⁻ e,
        f (history z.1, next (z.1, (z.2, e))) ∂ξ) := by
      fun_prop
    exact hPair.lintegral_kernel_prod_right'
      (κ := κ.comap (Prod.fst : A × C → A) measurable_fst)
  calc
    ∫⁻ y, f y ∂(((μ ⊗ₘ κ).prod (ν.prod ξ)).map
        (fun q => (history (q.1.1, q.2.1),
          next ((q.1.1, q.2.1), (q.1.2, q.2.2))))) =
        ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ e,
          f (history (a, c), next ((a, c), (b, e))) ∂ξ ∂ν ∂κ a ∂μ := by
      rw [lintegral_map hf hMap, lintegral_prod _ (by fun_prop),
        Measure.lintegral_compProd (by fun_prop)]
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro b
      exact lintegral_prod _ (by fun_prop)
    _ = ∫⁻ ac, ∫⁻ be,
        f (history ac, next (ac, be)) ∂(κ ac.1).prod ξ ∂μ.prod ν := by
      rw [lintegral_prod _ hInner.aemeasurable]
      apply lintegral_congr
      intro a
      rw [lintegral_lintegral_swap (by fun_prop :
        AEMeasurable
          (fun bc : B × C => ∫⁻ e,
            f (history (a, bc.2), next ((a, bc.2), (bc.1, e))) ∂ξ)
          ((κ a).prod ν))]
      apply lintegral_congr
      intro c
      exact (lintegral_prod
        (μ := κ a) (ν := ξ)
        (fun be : B × E =>
          f (history (a, c), next ((a, c), be)))
        (by fun_prop)).symm
    _ = ∫⁻ ac, ∫⁻ y, f (history ac, y) ∂θ (history ac) ∂μ.prod ν := by
      apply lintegral_congr_ae
      filter_upwards [hrow] with ac hac
      rw [← hac]
      have hn : Measurable (fun be : B × E => next (ac, be)) :=
        hNext.comp (measurable_const.prodMk measurable_id)
      exact (lintegral_map
        (μ := (κ ac.1).prod ξ)
        (f := fun y : Y => f (history ac, y))
        (g := fun be : B × E => next (ac, be))
        (by fun_prop) hn).symm
    _ = ∫⁻ h, ∫⁻ y, f (h, y) ∂θ h ∂(μ.prod ν).map history := by
      rw [lintegral_map (by fun_prop) hHistory]
    _ = ∫⁻ y, f y ∂(((μ.prod ν).map history) ⊗ₘ θ) :=
      (Measure.lintegral_compProd hf).symm

end CausalTransport


section LocalizedRecordLaw

variable {S : Type*} [Fintype S] [DecidableEq S]
variable (N : Network S) [DecidableEq N.I]

theorem timedLaw_map_prefix_pair
    (hPos : N.hasPositiveRates) (z0 : State S) (n : ℕ) :
    (timedLaw N hPos z0).map
        (fun η => (frestrictLe (π := fun _ => Option N.I) n η.1,
          clockPrefix n η.2)) =
      ((rawLaw N hPos z0).map (frestrictLe (π := fun _ => Option N.I) n)).prod
        (Measure.pi (fun _ : Fin n => expMeasure 1)) := by
  letI := rawLaw_isProbabilityMeasure N hPos z0
  change ((rawLaw N hPos z0).prod unitClockLaw).map
      (Prod.map (frestrictLe (π := fun _ => Option N.I) n) (clockPrefix n)) = _
  rw [← Measure.map_prod_map _ _ (measurable_frestrictLe (X := fun _ : ℕ => Option N.I) n)
    (measurable_clockPrefix n), unitClockLaw_map_prefix n]

theorem localized_nextRecord_row
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 n : ℕ)
    (p : (i : Finset.Iic n) → Option N.I) (c : Fin n → ℝ)
    (hsource : ∀ x : BoundedPopulation S R × Fin K × Fin J,
      (channels N inc R K J).labelStatePath
          (encode R K J z0 k0 0) (extendLabels n p) n = some x →
        population (some x) = prefixToState N z0 n p) :
    ((stepKernel N hPos z0 n p).prod (expMeasure 1)).map
        (fun be => (channels N inc R K J).nextRecord
          (encode R K J z0 k0 0) n ((p, c), be)) =
      (channels N inc R K J).qMatrix.jumpHoldTrajectoryStepKernel n
        ((channels N inc R K J).recordHistory (encode R K J z0 k0 0) n (p, c)) := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  let D := channels N inc R K J
  let x0 := encode R K J z0 k0 0
  change ((stepKernel N hPos z0 n p).prod (expMeasure 1)).map
      (fun be => D.nextRecord x0 n ((p, c), be)) =
    D.qMatrix.jumpHoldTrajectoryStepKernel n (D.recordHistory x0 n (p, c))
  rw [D.qMatrix.jumpHoldTrajectoryStepKernel_apply,
    D.recordHistory_currentState, D.qMatrix.jumpHoldStepKernel_apply]
  cases hs : D.labelStatePath x0 (extendLabels n p) n with
  | none =>
      have habs : D.qMatrix.IsAbsorbing none :=
        channels_isAbsorbing_none N inc R K J
      have hz : D.totalRate (none : LocalState S R K J) = 0 := by
        simp [D, FiniteChannels.totalRate, channels]
      rw [D.qMatrix.jumpHoldStepMeasureTotal_of_absorbing habs]
      have hconst :
          (fun be : Option N.I × ℝ =>
            D.nextRecord x0 n ((p, c), be)) =
          (fun _ : Option N.I × ℝ =>
            (0, (none : LocalState S R K J))) := by
        funext be
        simp only [FiniteChannels.nextRecord, hs,
          FiniteChannels.channelRecord, if_pos hz]
      rw [hconst]
      simp only [Measure.map_const, measure_univ, one_smul]
  | some x =>
      have hpop : population (some x) = prefixToState N z0 n p := hsource x hs
      have hkernel :
          stepKernel N hPos z0 n p = (D.channelPMF (some x)).toMeasure := by
        change (massActionPMF N hPos (prefixToState N z0 n p)).toMeasure =
          ((channels N inc R K J).channelPMF (some x)).toMeasure
        rw [channels_channelPMF_some N inc hPos R K J x, hpop]
      simp only [FiniteChannels.nextRecord, hs]
      rw [hkernel]
      change ((D.channelPMF (some x)).toMeasure.prod (expMeasure 1)).map
          (D.channelRecord (some x) ∘ Prod.swap) =
        D.qMatrix.jumpHoldStepMeasureTotal (some x)
      rw [← Measure.map_map (D.measurable_channelRecord (some x)) measurable_swap,
        Measure.prod_swap]
      exact D.channelRecord_map (some x)

/-- The actual stopped raw jump-and-clock law is the canonical finite
Q-matrix record law.  All source-law premises are discharged. -/
theorem timedLaw_map_localizedRecord
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ) :
    (timedLaw N hPos z0).map
        ((channels N inc R K J).recordMap (encode R K J z0 k0 0)) =
      (channels N inc R K J).qMatrix.canonicalRecordMeasure
        (encode R K J z0 k0 0) := by
  letI := rawLaw_isProbabilityMeasure N hPos z0
  let D := channels N inc R K J
  let x0 := encode R K J z0 k0 0
  let μ := (timedLaw N hPos z0).map (D.recordMap x0)
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (D.measurable_recordMap x0).aemeasurable
  change μ = D.qMatrix.canonicalRecordMeasure x0
  apply eq_canonicalRecordMeasure_of_history_next D.qMatrix x0 μ
  · exact D.recordMap_initial x0 (timedLaw N hPos z0)
  · intro n
    let μp := (rawLaw N hPos z0).map (frestrictLe (π := fun _ => Option N.I) n)
    let νc := Measure.pi (fun _ : Fin n => expMeasure 1)
    let θ := D.qMatrix.jumpHoldTrajectoryStepKernel n
    letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
      isProbabilityMeasure_expMeasure (by norm_num)
    letI : IsProbabilityMeasure μp :=
      Measure.isProbabilityMeasure_map (measurable_frestrictLe (X := fun _ : ℕ => Option N.I) n).aemeasurable
    letI : IsProbabilityMeasure νc := by
      dsimp [νc]
      infer_instance
    letI : IsMarkovKernel θ :=
      D.qMatrix.isMarkovKernel_jumpHoldTrajectoryStepKernel n
    have hsource :
        ∀ᵐ pc ∂μp.prod νc,
          ∀ x : BoundedPopulation S R × Fin K × Fin J,
            D.labelStatePath x0 (extendLabels n pc.1) n = some x →
              population (some x) = prefixToState N z0 n pc.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μp) (ν := νc)).ae
        (labelStatePath_population_prefix_ae N hPos inc R K J z0 k0 n)
    have hrow :
        ∀ᵐ pc ∂μp.prod νc,
          ((stepKernel N hPos z0 n pc.1).prod (expMeasure 1)).map
              (fun be => D.nextRecord x0 n (pc, be)) =
            θ (D.recordHistory x0 n pc) := by
      filter_upwards [hsource] with pc hpc
      exact localized_nextRecord_row N hPos inc R K J z0 k0 n pc.1 pc.2 hpc
    have htransport :=
      map_causal_history_next μp (stepKernel N hPos z0 n) νc (expMeasure 1) θ
        (D.recordHistory x0 n) (D.measurable_recordHistory x0 n)
        (D.nextRecord x0 n) (D.measurable_nextRecord x0 n) hrow
    have hmarg :
        μ.map (frestrictLe (π := fun _ => ℝ × LocalState S R K J) n) =
          (μp.prod νc).map (D.recordHistory x0 n) := by
      change ((timedLaw N hPos z0).map (D.recordMap x0)).map
          (frestrictLe (π := fun _ => ℝ × LocalState S R K J) n) = _
      rw [← timedLaw_map_prefix_pair N hPos z0 n,
        Measure.map_map (measurable_frestrictLe (X := fun _ : ℕ => ℝ × LocalState S R K J) n) (D.measurable_recordMap x0),
        Measure.map_map (D.measurable_recordHistory x0 n) (by fun_prop)]
      congr 1
      funext η
      exact (D.recordHistory_restrict x0 n η).symm
    calc
      μ.map (fun records => (frestrictLe (π := fun _ : ℕ => ℝ × LocalState S R K J) n records, records (n + 1))) =
          (timedLaw N hPos z0).map
            (fun η => (D.recordHistory x0 n (frestrictLe (π := fun _ : ℕ => Option N.I) n η.1, clockPrefix n η.2),
              D.nextRecord x0 n
                ((frestrictLe (π := fun _ : ℕ => Option N.I) n η.1, clockPrefix n η.2), (η.1 (n + 1), η.2 n)))) := by
        change ((timedLaw N hPos z0).map (D.recordMap x0)).map _ = _
        rw [Measure.map_map (by fun_prop) (D.measurable_recordMap x0)]
        congr 1
        funext η
        apply Prod.ext
        · exact (D.recordHistory_restrict x0 n η).symm
        · exact (D.nextRecord_restrict x0 n η).symm
      _ = ((μp ⊗ₘ stepKernel N hPos z0 n).prod (νc.prod (expMeasure 1))).map
          (fun q => (D.recordHistory x0 n (q.1.1, q.2.1),
            D.nextRecord x0 n ((q.1.1, q.2.1), (q.1.2, q.2.2)))) := by
        rw [← timedLaw_map_history_next N hPos z0 n,
          Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = ((μp.prod νc).map (D.recordHistory x0 n)) ⊗ₘ θ := htransport
      _ = μ.map (frestrictLe (π := fun _ : ℕ => ℝ × LocalState S R K J) n) ⊗ₘ θ := by rw [← hmarg]

end LocalizedRecordLaw


namespace FiniteChannels
variable {X : Type u} {I : Type v}
variable [Fintype X] [DecidableEq X] [Fintype I]
variable (D : FiniteChannels X I)

theorem labelStatePath_add_of_zero_rate (x₀ : X) (ω : ℕ → Option I)
    (n : ℕ) (hzero : D.totalRate (D.labelStatePath x₀ ω n) = 0) (k : ℕ) :
    D.labelStatePath x₀ ω (n + k) = D.labelStatePath x₀ ω n := by
  induction k with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
      rw [Nat.add_succ, labelStatePath, ih, labelStep, if_pos hzero]

theorem recordMap_add_of_zero_rate (x₀ : X)
    (η : (ℕ → Option I) × (ℕ → ℝ)) (n : ℕ)
    (hzero : D.totalRate (D.labelStatePath x₀ η.1 n) = 0) (k : ℕ) :
    D.recordMap x₀ η (n + k + 1) =
      (0, D.labelStatePath x₀ η.1 n) := by
  have hk : D.totalRate (D.labelStatePath x₀ η.1 (n + k)) = 0 := by
    rw [D.labelStatePath_add_of_zero_rate x₀ η.1 n hzero k]
    exact hzero
  rw [D.recordMap_of_zero_rate x₀ η (n + k) hk,
    D.labelStatePath_add_of_zero_rate x₀ η.1 n hzero k]
end FiniteChannels

section FiniteStop
variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]
variable (inc : State S → N.I → ℕ)

omit [DecidableEq N.I] in
theorem reactionCount_advance_of_eq_some {R K J : ℕ}
    (x y : BoundedPopulation S R × Fin K × Fin J) (i : N.I)
    (h : advance N inc (some x : LocalState S R K J) i = some y) :
    reactionCount (some y : LocalState S R K J) =
      reactionCount (some x : LocalState S R K J) + 1 := by
  exact reactionCount_encode_of_eq_some R K J
    ((N.rxn i).fire (population (some x : LocalState S R K J)))
    (x.2.1.val + inc (population (some x : LocalState S R K J)) i)
    (x.2.2.val + 1) h

theorem localization_absorbing_index_of_fired_eq_label
    (hPos : N.hasPositiveRates) (R K J : ℕ) (z₀ : State S) (k₀ : ℕ)
    (ω : ℕ → Option N.I)
    (hlabels : ∀ n, pathFired N z₀ ω n = ω (n + 1)) :
    ∃ stop : ℕ, stop ≤ J ∧
      (channels N inc R K J).totalRate
        ((channels N inc R K J).labelStatePath
          (encode R K J z₀ k₀ 0) ω stop) = 0 := by
  classical
  let D := channels N inc R K J
  let x₀ := encode R K J z₀ k₀ 0
  change ∃ stop : ℕ, stop ≤ J ∧ D.totalRate (D.labelStatePath x₀ ω stop) = 0
  by_contra hnot
  have hne : ∀ n, n ≤ J → D.totalRate (D.labelStatePath x₀ ω n) ≠ 0 := by
    intro n hn hz
    exact hnot ⟨n, hn, hz⟩
  have hpop :=
    labelStatePath_population_of_fired_eq_label N hPos inc R K J z₀ k₀ ω hlabels
  have hcount : ∀ n, n ≤ J →
      ∀ x : BoundedPopulation S R × Fin K × Fin J,
        D.labelStatePath x₀ ω n = some x → x.2.2.val = n := by
    intro n
    induction n with
    | zero =>
        intro hn x hx
        change encode R K J z₀ k₀ 0 = some x at hx
        exact reactionCount_encode_of_eq_some R K J z₀ k₀ 0 hx
    | succ n ih =>
        intro hn x hx
        have hnle : n ≤ J := (Nat.le_succ n).trans hn
        change D.labelStep (D.labelStatePath x₀ ω n) (ω (n + 1)) = some x at hx
        cases hy : D.labelStatePath x₀ ω n with
        | none =>
            exfalso
            exact hne n hnle (by rw [hy]; exact channels_totalRate_none N inc R K J)
        | some y =>
            have hnzero : D.totalRate (some y) ≠ 0 := by
              simpa only [hy] using hne n hnle
            have hp :
                population (some y : LocalState S R K J) = pathState N z₀ ω n :=
              hpop n y hy
            have hNT : ¬ N.Terminal (pathState N z₀ ω n) := by
              intro ht
              apply hnzero
              change N.totalPropensity (population (some y : LocalState S R K J)) = 0
              rw [hp]
              exact Network.totalPropensity_eq_zero_of_terminal ht
            obtain ⟨i, hi⟩ : ∃ i : N.I, ω (n + 1) = some i := by
              cases ho : ω (n + 1) with
              | none =>
                  have hl := hlabels n
                  simp [pathFired, hNT, ho] at hl
              | some i => exact ⟨i, rfl⟩
            have hc := ih hnle y hy
            simp only [hy, FiniteChannels.labelStep, if_neg hnzero, hi] at hx
            change advance N inc (some y : LocalState S R K J) i = some x at hx
            have hr := reactionCount_advance_of_eq_some N inc y x i hx
            change x.2.2.val = y.2.2.val + 1 at hr
            simpa only [hc] using hr
  cases hx : D.labelStatePath x₀ ω J with
  | none =>
      exact hne J le_rfl (by rw [hx]; exact channels_totalRate_none N inc R K J)
  | some x =>
      exact (Nat.ne_of_lt x.2.2.isLt) (hcount J le_rfl x hx)

theorem localization_absorbing_index_ae
    (hPos : N.hasPositiveRates) (R K J : ℕ) (z₀ : State S) (k₀ : ℕ) :
    ∀ᵐ ω ∂rawLaw N hPos z₀, ∃ stop : ℕ, stop ≤ J ∧
      (channels N inc R K J).totalRate
        ((channels N inc R K J).labelStatePath
          (encode R K J z₀ k₀ 0) ω stop) = 0 := by
  filter_upwards [source_fired_eq_label_ae N hPos z₀] with ω hlabels
  exact localization_absorbing_index_of_fired_eq_label
    N inc hPos R K J z₀ k₀ ω hlabels

theorem timed_localization_absorbing_index_ae
    (hPos : N.hasPositiveRates) (R K J : ℕ) (z₀ : State S) (k₀ : ℕ) :
    ∀ᵐ η ∂CTMCBridge.timedLaw N hPos z₀, ∃ stop : ℕ, stop ≤ J ∧
      (channels N inc R K J).totalRate
        ((channels N inc R K J).labelStatePath
          (encode R K J z₀ k₀ 0) η.1 stop) = 0 := by
  filter_upwards [CTMCBridge.timedLaw_fired_eq_label_ae N hPos z₀] with η hlabels
  exact localization_absorbing_index_of_fired_eq_label
    N inc hPos R K J z₀ k₀ η.1 hlabels
end FiniteStop


section StoppedInterpolation

variable {X : Type*}

/-- Time of record n; record zero is at time zero. -/
noncomputable def recordElapsed (ρ : ℕ → ℝ × X) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (ρ (j + 1)).1

@[simp]
theorem recordElapsed_zero (ρ : ℕ → ℝ × X) :
    recordElapsed ρ 0 = 0 := by
  simp [recordElapsed]

theorem recordElapsed_succ (ρ : ℕ → ℝ × X) (n : ℕ) :
    recordElapsed ρ (n + 1) = recordElapsed ρ n + (ρ (n + 1)).1 := by
  simp only [recordElapsed, Finset.sum_range_succ]

theorem recordElapsed_mono (ρ : ℕ → ℝ × X)
    (hhold : ∀ n, 0 ≤ (ρ (n + 1)).1) :
    Monotone (recordElapsed ρ) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [recordElapsed_succ]
  exact le_add_of_nonneg_right (hhold n)

theorem recordTrajectoryToPath_times_eq (ρ : ℕ → ℝ × X) (n : ℕ) :
    (Ripple.CTMC.QMatrix.recordTrajectoryToPath ρ).times n =
      recordElapsed ρ (n + 1) := rfl

/-- The canonical reader has the intended semantics on every occupied
half-open interval, without requiring strictly increasing sentinel times. -/
theorem record_stateAt_of_interval (ρ : ℕ → ℝ × X)
    (hhold : ∀ n, 0 ≤ (ρ (n + 1)).1)
    (n : ℕ) (t : ℝ)
    (hleft : recordElapsed ρ n ≤ t)
    (hright : t < recordElapsed ρ (n + 1)) :
    (Ripple.CTMC.QMatrix.recordTrajectoryToPath ρ).stateAt t = (ρ n).2 := by
  have hfirst :
      (Ripple.CTMC.QMatrix.recordTrajectoryToPath ρ).stateAt t =
        (Ripple.CTMC.QMatrix.recordTrajectoryToPath ρ).stateSeq n := by
    apply Ripple.CTMC.CTMCPath.stateAt_eq_stateSeq_of_first_time_gt
      (Ripple.CTMC.QMatrix.recordTrajectoryToPath ρ) t
    · exact hright
    · intro k hk
      have hkn : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have hle : recordElapsed ρ (k + 1) ≤ t :=
        (recordElapsed_mono ρ hhold hkn).trans hleft
      exact not_lt.mpr hle
  simpa only [Ripple.CTMC.QMatrix.recordTrajectoryToPath_stateSeq] using hfirst

/-- A physical absorbing extension of the canonical record reader, with the
specified stop record retained at and after its arrival time. -/
noncomputable def stoppedRecordStateAt
    (ρ : ℕ → ℝ × X) (stop : ℕ) (t : ℝ) : X :=
  if t < recordElapsed ρ stop then
    (Ripple.CTMC.QMatrix.recordTrajectoryToPath ρ).stateAt t
  else (ρ stop).2

theorem stoppedRecordStateAt_before (ρ : ℕ → ℝ × X)
    (stop : ℕ) (t : ℝ) (ht : t < recordElapsed ρ stop) :
    stoppedRecordStateAt ρ stop t =
      (Ripple.CTMC.QMatrix.recordTrajectoryToPath ρ).stateAt t := by
  simp only [stoppedRecordStateAt, if_pos ht]

theorem stoppedRecordStateAt_at_or_after (ρ : ℕ → ℝ × X)
    (stop : ℕ) (t : ℝ) (ht : recordElapsed ρ stop ≤ t) :
    stoppedRecordStateAt ρ stop t = (ρ stop).2 := by
  simp only [stoppedRecordStateAt, if_neg (not_lt.mpr ht)]

theorem stoppedRecordStateAt_of_interval (ρ : ℕ → ℝ × X)
    (hhold : ∀ n, 0 ≤ (ρ (n + 1)).1)
    (stop n : ℕ) (hn : n < stop) (t : ℝ)
    (hleft : recordElapsed ρ n ≤ t)
    (hright : t < recordElapsed ρ (n + 1)) :
    stoppedRecordStateAt ρ stop t = (ρ n).2 := by
  rw [stoppedRecordStateAt_before ρ stop t
    (hright.trans_le (recordElapsed_mono ρ hhold (Nat.succ_le_of_lt hn)))]
  exact record_stateAt_of_interval ρ hhold n t hleft hright

/-- A zero-time sentinel preserves the state and elapsed time after stopping. -/
theorem sentinel_padding_stable (ρ : ℕ → ℝ × X) (stop : ℕ)
    (hpad : ∀ n, stop ≤ n → ρ (n + 1) = (0, (ρ n).2)) :
    ∀ m, (ρ (stop + m)).2 = (ρ stop).2 ∧
      recordElapsed ρ (stop + m) = recordElapsed ρ stop := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hp := hpad (stop + m) (by omega)
      rw [Nat.add_succ, recordElapsed_succ, hp]
      simpa only [Prod.fst, Prod.snd, add_zero] using ih

/-- Later sentinel indices define the same physical absorbing extension. -/
theorem stoppedRecordStateAt_padding (ρ : ℕ → ℝ × X) (stop m : ℕ)
    (hpad : ∀ n, stop ≤ n → ρ (n + 1) = (0, (ρ n).2)) (t : ℝ) :
    stoppedRecordStateAt ρ (stop + m) t = stoppedRecordStateAt ρ stop t := by
  obtain ⟨hs, ht⟩ := sentinel_padding_stable ρ stop hpad m
  simp only [stoppedRecordStateAt, ht, hs]

/-- Two states, one transition at time one, then absorbing sentinels. -/
def absorbingExampleRecords (n : ℕ) : ℝ × Bool :=
  if n = 0 then (0, false) else (if n = 1 then 1 else 0, true)

theorem absorbingExample_times (n : ℕ) :
    (Ripple.CTMC.QMatrix.recordTrajectoryToPath absorbingExampleRecords).times n = 1 := by
  induction n with
  | zero =>
      norm_num [Ripple.CTMC.QMatrix.recordTrajectoryToPath, absorbingExampleRecords]
  | succ n ih =>
      rw [Ripple.CTMC.QMatrix.recordTrajectoryToPath_times_succ, ih]
      have hn : n + 2 ≠ 0 := by omega
      have hn' : n + 2 ≠ 1 := by omega
      simp [absorbingExampleRecords, hn, hn']

/-- PAPER-GAP for a global use of the existing unextended reader: at the
absorbing transition it returns the initial state. -/
theorem absorbingExample_unextended_stateAt :
    (Ripple.CTMC.QMatrix.recordTrajectoryToPath absorbingExampleRecords).stateAt 1 = false := by
  have hnone : ¬ ∃ n,
      1 < (Ripple.CTMC.QMatrix.recordTrajectoryToPath absorbingExampleRecords).times n := by
    rintro ⟨n, hn⟩
    rw [absorbingExample_times] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  simp only [Ripple.CTMC.CTMCPath.stateAt, dif_neg hnone,
    Ripple.CTMC.QMatrix.recordTrajectoryToPath_init]
  rfl

/-- The absorbing extension gives the physical post-transition state. -/
theorem absorbingExample_extended_stateAt :
    stoppedRecordStateAt absorbingExampleRecords 1 1 = true := by
  apply (stoppedRecordStateAt_at_or_after absorbingExampleRecords 1 1
    (by norm_num [recordElapsed, absorbingExampleRecords])).trans
  norm_num [absorbingExampleRecords]

theorem absorbingExample_readers_disagree :
    (Ripple.CTMC.QMatrix.recordTrajectoryToPath absorbingExampleRecords).stateAt 1 ≠
      stoppedRecordStateAt absorbingExampleRecords 1 1 := by
  rw [absorbingExample_unextended_stateAt, absorbingExample_extended_stateAt]
  decide


/-- The padded path fails the current time-divergence definition even though
the physical chain has only one jump. -/
theorem absorbingExample_not_nonExplosive :
    ¬(Ripple.CTMC.QMatrix.recordTrajectoryToPath
      absorbingExampleRecords).NonExplosive := by
  intro h
  obtain ⟨n, hn⟩ :=
    Ripple.CTMC.CTMCPath.exists_bound_of_nonExplosive
      (Ripple.CTMC.QMatrix.recordTrajectoryToPath absorbingExampleRecords) h 1
  rw [absorbingExample_times] at hn
  exact (lt_irrefl (1 : ℝ)) hn

/-- The canonical sentinel trajectory for an initially absorbing state. -/
def initialAbsorbingRecords : ℕ → ℝ × Unit :=
  fun _ => (0, ())

theorem initialAbsorbing_not_nonExplosive :
    ¬(Ripple.CTMC.QMatrix.recordTrajectoryToPath
      initialAbsorbingRecords).NonExplosive := by
  intro h
  obtain ⟨n, hn⟩ :=
    Ripple.CTMC.CTMCPath.exists_bound_of_nonExplosive
      (Ripple.CTMC.QMatrix.recordTrajectoryToPath initialAbsorbingRecords) h 0
  simpa [Ripple.CTMC.QMatrix.recordTrajectoryToPath, initialAbsorbingRecords] using hn

end StoppedInterpolation


section RecordHoldingTimes

variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]

theorem FiniteChannels.recordMap_holding_nonneg
    (D : FiniteChannels X I) (x0 : X)
    (η : (ℕ → Option I) × (ℕ → ℝ))
    (hclock : ∀ n, 0 ≤ η.2 n) (n : ℕ) :
    0 ≤ (D.recordMap x0 η (n + 1)).1 := by
  by_cases hz : D.totalRate (D.labelStatePath x0 η.1 n) = 0
  · simp only [FiniteChannels.recordMap, FiniteChannels.channelRecord,
      if_pos hz, Prod.fst, le_refl]
  · simpa only [FiniteChannels.recordMap, FiniteChannels.channelRecord,
      if_neg hz, Prod.fst] using
      (div_nonneg (hclock n) (D.totalRate (D.labelStatePath x0 η.1 n)).cast_nonneg)

end RecordHoldingTimes

section LocalizedPhysicalTime

universe uT vT
variable {S : Type uT} [Fintype S] [DecidableEq S]
variable (N : Network.{uT, vT} S) [DecidableEq N.I]

/-- Before local absorption, the record holds and the original physical
holds agree on the same time scale. -/
theorem localized_record_holding_eq
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ) (η : TimedΩ N)
    (hlabels : ∀ n, pathFired N z0 η.1 n = η.1 (n + 1)) (n : ℕ)
    (hlive : (channels N inc R K J).totalRate
      ((channels N inc R K J).labelStatePath
        (encode R K J z0 k0 0) η.1 n) ≠ 0) :
    ENNReal.ofReal (((channels N inc R K J).recordMap
      (encode R K J z0 k0 0) η (n + 1)).1) =
        holdingTime N z0 n η := by
  let D := channels N inc R K J
  let x0 := encode R K J z0 k0 0
  change D.totalRate (D.labelStatePath x0 η.1 n) ≠ 0 at hlive
  change ENNReal.ofReal ((D.recordMap x0 η (n + 1)).1) = _
  cases hs : D.labelStatePath x0 η.1 n with
  | none =>
      exact (hlive (by rw [hs]; exact channels_totalRate_none N inc R K J)).elim
  | some x =>
      have hpop : population (some x) = pathState N z0 η.1 n :=
        labelStatePath_population_of_fired_eq_label
          N hPos inc R K J z0 k0 η.1 hlabels n x hs
      have hr : N.totalPropensity (pathState N z0 η.1 n) ≠ 0 := by
        have h : D.totalRate (some x) ≠ 0 := by
          simpa only [hs] using hlive
        change N.totalPropensity (population (some x)) ≠ 0 at h
        simpa only [hpop] using h
      have hrecord : (D.recordMap x0 η (n + 1)).1 =
          η.2 n / CTMCBridge.totalRate N (pathState N z0 η.1 n) := by
        have hrate :
            (D.totalRate (D.labelStatePath x0 η.1 n) : ℝ) =
              CTMCBridge.totalRate N (pathState N z0 η.1 n) := by
          rw [hs]
          exact congrArg (fun z : State S => (N.totalPropensity z : ℝ)) hpop
        calc
          (D.recordMap x0 η (n + 1)).1 =
              η.2 n / (D.totalRate (D.labelStatePath x0 η.1 n) : ℝ) := by
            simp only [FiniteChannels.recordMap, FiniteChannels.channelRecord,
              if_neg hlive, Prod.fst]
          _ = η.2 n / CTMCBridge.totalRate N (pathState N z0 η.1 n) :=
            congrArg (fun r : ℝ => η.2 n / r) hrate
      rw [hrecord]
      exact (holdingTime_eq_ofReal_div N z0 n η (pos_iff_ne_zero.mpr hr)).symm

/-- Equality of all cumulative times through a live finite prefix.  No
conversion of an infinite terminal holding time to a real number occurs. -/
theorem localized_recordElapsed_eq_jumpTime
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ) (η : TimedΩ N)
    (hlabels : ∀ j, pathFired N z0 η.1 j = η.1 (j + 1))
    (hclock : ∀ j, 0 ≤ η.2 j) (n : ℕ)
    (hpre : ∀ j, j < n →
      (channels N inc R K J).totalRate
        ((channels N inc R K J).labelStatePath
          (encode R K J z0 k0 0) η.1 j) ≠ 0) :
    ENNReal.ofReal (recordElapsed
      ((channels N inc R K J).recordMap (encode R K J z0 k0 0) η) n) =
        jumpTime N z0 n η := by
  let D := channels N inc R K J
  let x0 := encode R K J z0 k0 0
  unfold recordElapsed jumpTime
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun j _ => D.recordMap_holding_nonneg x0 η hclock j)]
  apply Finset.sum_congr rfl
  intro j hj
  exact localized_record_holding_eq N hPos inc R K J z0 k0 η hlabels j
    (hpre j (Finset.mem_range.mp hj))

/-- On a pre-stop time interval, the canonical reader recovers the actual
population at that same physical time. -/
theorem localized_record_stateAt_of_interval
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ) (η : TimedΩ N)
    (hlabels : ∀ j, pathFired N z0 η.1 j = η.1 (j + 1))
    (hclock : ∀ j, 0 ≤ η.2 j) (n : ℕ) (t : ℝ)
    (hlive : (channels N inc R K J).totalRate
      ((channels N inc R K J).labelStatePath
        (encode R K J z0 k0 0) η.1 n) ≠ 0)
    (hleft : recordElapsed
      ((channels N inc R K J).recordMap (encode R K J z0 k0 0) η) n ≤ t)
    (hright : t < recordElapsed
      ((channels N inc R K J).recordMap (encode R K J z0 k0 0) η) (n + 1)) :
    population ((QMatrix.recordTrajectoryToPath
      ((channels N inc R K J).recordMap (encode R K J z0 k0 0) η)).stateAt t) =
        pathState N z0 η.1 n := by
  let D := channels N inc R K J
  let x0 := encode R K J z0 k0 0
  change population ((QMatrix.recordTrajectoryToPath
    (D.recordMap x0 η)).stateAt t) = _
  rw [record_stateAt_of_interval (D.recordMap x0 η)
    (D.recordMap_holding_nonneg x0 η hclock) n t hleft hright,
    D.recordMap_state]
  cases hs : D.labelStatePath x0 η.1 n with
  | none =>
      exact (hlive (by rw [hs]; exact channels_totalRate_none N inc R K J)).elim
  | some x =>
      exact labelStatePath_population_of_fired_eq_label
        N hPos inc R K J z0 k0 η.1 hlabels n x hs

end LocalizedPhysicalTime

section RecordIntervals

variable {X : Type*}

/-- Every nonnegative time strictly before a finite stop lies in a record
interval.  The strict right endpoint agrees with the canonical reader. -/
theorem exists_record_interval_before (ρ : ℕ → ℝ × X) (stop : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (hbefore : t < recordElapsed ρ stop) :
    ∃ n, n < stop ∧ recordElapsed ρ n ≤ t ∧
      t < recordElapsed ρ (n + 1) := by
  cases stop with
  | zero =>
      rw [recordElapsed_zero] at hbefore
      exact (not_lt_of_ge ht hbefore).elim
  | succ k =>
      have hex : ∃ n, t < recordElapsed ρ (n + 1) := ⟨k, hbefore⟩
      have hnk : Nat.find hex ≤ k := Nat.find_min' hex hbefore
      refine ⟨Nat.find hex, Nat.lt_succ_of_le hnk, ?_, Nat.find_spec hex⟩
      cases hn : Nat.find hex with
      | zero => simpa only [hn, recordElapsed_zero] using ht
      | succ m =>
          have hmin := Nat.find_min hex (show m < Nat.find hex by omega)
          have hle : recordElapsed ρ (m + 1) ≤ t := le_of_not_gt hmin
          simpa only [hn] using hle

end RecordIntervals


section AlmostSureInterpolation

universe uV vV
variable {S : Type uV} [Fintype S] [DecidableEq S]
variable (N : Network.{uV, vV} S) [DecidableEq N.I]

/-- The finite canonical record law reads the original timed path on every
pre-stop interval, and has a constant absorbing extension thereafter. -/
theorem localized_interpolation_ae
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ) :
    ∀ᵐ η ∂timedLaw N hPos z0,
      let D := channels N inc R K J
      let x0 := encode R K J z0 k0 0
      let ρ := D.recordMap x0 η
      ∃ stop : ℕ, stop ≤ J ∧
        D.totalRate (D.labelStatePath x0 η.1 stop) = 0 ∧
        (∀ n, n < stop → D.totalRate (D.labelStatePath x0 η.1 n) ≠ 0) ∧
        (∀ n, n ≤ stop →
          ENNReal.ofReal (recordElapsed ρ n) = jumpTime N z0 n η) ∧
        (∀ t : ℝ, 0 ≤ t → t < recordElapsed ρ stop →
          ∃ n, n < stop ∧
            jumpTime N z0 n η ≤ ENNReal.ofReal t ∧
            ENNReal.ofReal t < jumpTime N z0 (n + 1) η ∧
            population (stoppedRecordStateAt ρ stop t) = pathState N z0 η.1 n) ∧
        (∀ m, ρ (stop + m + 1) = (0, (ρ stop).2)) ∧
        (∀ t : ℝ, recordElapsed ρ stop ≤ t →
          stoppedRecordStateAt ρ stop t = (ρ stop).2) := by
  filter_upwards [timedLaw_fired_eq_label_ae N hPos z0,
    timedLaw_clocks_pos_ae N hPos z0] with η hlabels hpositive
  let D := channels N inc R K J
  let x0 := encode R K J z0 k0 0
  let ρ := D.recordMap x0 η
  have hclock : ∀ n, 0 ≤ η.2 n := fun n => (hpositive n).le
  obtain ⟨s, hsJ, hs⟩ :=
    localization_absorbing_index_of_fired_eq_label
      N inc hPos R K J z0 k0 η.1 hlabels
  have hex : ∃ n, D.totalRate (D.labelStatePath x0 η.1 n) = 0 := ⟨s, hs⟩
  let stop := Nat.find hex
  have hstop : D.totalRate (D.labelStatePath x0 η.1 stop) = 0 := Nat.find_spec hex
  have hpre : ∀ n, n < stop →
      D.totalRate (D.labelStatePath x0 η.1 n) ≠ 0 :=
    fun n hn => Nat.find_min hex hn
  have htime (n : ℕ) (hn : n ≤ stop) :
      ENNReal.ofReal (recordElapsed ρ n) = jumpTime N z0 n η :=
    localized_recordElapsed_eq_jumpTime N hPos inc R K J z0 k0 η hlabels hclock n
      (fun j hj => hpre j (hj.trans_le hn))
  refine ⟨stop, (Nat.find_min' hex hs).trans hsJ, hstop, hpre, htime, ?_, ?_, ?_⟩
  · intro t ht hbefore
    obtain ⟨n, hn, hleft, hright⟩ := exists_record_interval_before ρ stop t ht hbefore
    refine ⟨n, hn, ?_, ?_, ?_⟩
    · rw [← htime n hn.le]
      exact ENNReal.ofReal_le_ofReal hleft
    · rw [← htime (n + 1) (Nat.succ_le_of_lt hn)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr hright
    · rw [stoppedRecordStateAt_before ρ stop t hbefore]
      exact localized_record_stateAt_of_interval
        N hPos inc R K J z0 k0 η hlabels hclock n t (hpre n hn) hleft hright
  · intro m
    change D.recordMap x0 η (stop + m + 1) = (0, (D.recordMap x0 η stop).2)
    rw [D.recordMap_add_of_zero_rate x0 η stop hstop m, D.recordMap_state]
  · intro t ht
    exact stoppedRecordStateAt_at_or_after ρ stop t ht

end AlmostSureInterpolation


section LocalizedPrefixSurvival

universe uP vP
variable {S : Type uP} [Fintype S] [DecidableEq S]
variable (N : Network.{uP, vP} S) [DecidableEq N.I]

/-- The requested stopping counter along the source label path. -/
noncomputable def rawTargetCount (inc : State S → N.I → ℕ)
    (z0 : State S) (k0 : ℕ) (ω : ℕ → Option N.I) : ℕ → ℕ
  | 0 => k0
  | n + 1 => rawTargetCount inc z0 k0 ω n +
      match ω (n + 1) with
      | none => 0
      | some i => inc (pathState N z0 ω n) i

/-- Actual reaction labels; the absorbing none sentinel does not increment. -/
def rawFiringCount {I : Type*} (ω : ℕ → Option I) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rawFiringCount ω n +
      match ω (n + 1) with
      | none => 0
      | some _ => 1

theorem rawFiringCount_le_index {I : Type*} (ω : ℕ → Option I) (n : ℕ) :
    rawFiringCount ω n ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [rawFiringCount]
      cases ω (n + 1) <;> simp only [add_zero] <;> omega

theorem rawFiringCount_eq_index_of_nonterminal
    (z0 : State S) (ω : ℕ → Option N.I)
    (hlabels : ∀ j, pathFired N z0 ω j = ω (j + 1)) (n : ℕ)
    (hNT : ∀ j, j < n → ¬ N.Terminal (pathState N z0 ω j)) :
    rawFiringCount ω n = n := by
  revert hNT
  induction n with
  | zero =>
      intro _
      rfl
  | succ n ih =>
      intro hNT
      have hp := ih (fun j hj => hNT j (hj.trans (Nat.lt_succ_self n)))
      have hsome : ω (n + 1) ≠ none := by
        intro ho
        have hv := pathFired_valid N z0 ω n
        rw [hlabels n, ho] at hv
        exact hNT n (Nat.lt_succ_self n) hv.2
      rw [rawFiringCount, hp]
      cases ho : ω (n + 1) with
      | none => exact (hsome ho).elim
      | some i => rfl

/-- Exact encoding throughout a source prefix inside all three bounds.
Natural absorption preserves both counters. -/
theorem labelStatePath_eq_encode_of_bounds
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ)
    (ω : ℕ → Option N.I)
    (hlabels : ∀ n, pathFired N z0 ω n = ω (n + 1)) (n : ℕ)
    (hbound : ∀ j, j ≤ n →
      populationSize (pathState N z0 ω j) ≤ R ∧
      rawTargetCount N inc z0 k0 ω j < K ∧ rawFiringCount ω j < J) :
    (channels N inc R K J).labelStatePath (encode R K J z0 k0 0) ω n =
      encode R K J (pathState N z0 ω n)
        (rawTargetCount N inc z0 k0 ω n) (rawFiringCount ω n) := by
  classical
  let D := channels N inc R K J
  let x0 := encode R K J z0 k0 0
  change D.labelStatePath x0 ω n =
    encode R K J (pathState N z0 ω n)
      (rawTargetCount N inc z0 k0 ω n) (rawFiringCount ω n)
  revert hbound
  induction n with
  | zero =>
      intro _
      rfl
  | succ n ih =>
      intro hbound
      have hb := hbound n (Nat.le_succ n)
      have hpre := ih (fun j hj => hbound j (hj.trans (Nat.le_succ n)))
      have henc : encode R K J (pathState N z0 ω n)
          (rawTargetCount N inc z0 k0 ω n) (rawFiringCount ω n) ≠ none := by
        intro h
        exact (encode_eq_none_iff R K J _ _ _).mp h hb
      cases he : encode R K J (pathState N z0 ω n)
          (rawTargetCount N inc z0 k0 ω n) (rawFiringCount ω n) with
      | none => exact (henc he).elim
      | some x =>
          have hp : D.labelStatePath x0 ω n = some x := hpre.trans he
          have hz : population (some x) = pathState N z0 ω n :=
            population_encode_of_eq_some R K J _ _ _ he
          have hk : x.2.1.val = rawTargetCount N inc z0 k0 ω n :=
            targetCount_encode_of_eq_some R K J _ _ _ he
          have hj : x.2.2.val = rawFiringCount ω n :=
            reactionCount_encode_of_eq_some R K J _ _ _ he
          have hvalid := pathFired_valid N z0 ω n
          rw [hlabels n] at hvalid
          cases ho : ω (n + 1) with
          | none =>
              have hv : pathState N z0 ω (n + 1) = pathState N z0 ω n ∧
                  N.Terminal (pathState N z0 ω n) := by
                simpa only [ho] using hvalid
              rw [FiniteChannels.labelStatePath, hp, ho]
              have hs : D.labelStep (some x) none = some x := by
                simp [FiniteChannels.labelStep, FiniteChannels.labelDestination]
              rw [hs]
              simpa only [rawTargetCount, rawFiringCount, ho, add_zero, hv.1] using he.symm
          | some i =>
              have hv : N.StepAt i (pathState N z0 ω n)
                  (pathState N z0 ω (n + 1)) := by
                simpa only [ho] using hvalid
              have hr : D.totalRate (some x) ≠ 0 := by
                change N.totalPropensity (population (some x)) ≠ 0
                rw [hz]
                exact totalPropensity_ne_zero_of_nonTerminal N hPos
                  (fun hT => hT i hv.1)
              rw [FiniteChannels.labelStatePath, hp, ho]
              simp only [FiniteChannels.labelStep, if_neg hr]
              change advance N inc (some x) i = _
              change encode R K J ((N.rxn i).fire (population (some x)))
                (x.2.1.val + inc (population (some x)) i) (x.2.2.val + 1) = _
              rw [hz, hk, hj, ← hv.2]
              simp only [rawTargetCount, rawFiringCount, ho]

theorem labelStatePath_ne_none_of_population_and_target_bounds
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (R K J : ℕ) (z0 : State S) (k0 : ℕ)
    (ω : ℕ → Option N.I)
    (hlabels : ∀ n, pathFired N z0 ω n = ω (n + 1)) (n : ℕ)
    (hnJ : n < J)
    (hpop : ∀ j, j ≤ n → populationSize (pathState N z0 ω j) ≤ R)
    (htarget : ∀ j, j ≤ n → rawTargetCount N inc z0 k0 ω j < K) :
    (channels N inc R K J).labelStatePath
      (encode R K J z0 k0 0) ω n ≠ none := by
  have hbound : ∀ j, j ≤ n →
      populationSize (pathState N z0 ω j) ≤ R ∧
      rawTargetCount N inc z0 k0 ω j < K ∧ rawFiringCount ω j < J := by
    intro j hj
    exact ⟨hpop j hj, htarget j hj,
      lt_of_le_of_lt (rawFiringCount_le_index ω j) (lt_of_le_of_lt hj hnJ)⟩
  rw [labelStatePath_eq_encode_of_bounds N hPos inc R K J z0 k0 ω hlabels n hbound]
  intro h
  exact (encode_eq_none_iff R K J _ _ _).mp h (hbound n le_rfl)

end LocalizedPrefixSurvival


section LocalizationExhaustion

universe uE vE
variable {S : Type uE} [Fintype S] [DecidableEq S]
variable (N : Network.{uE, vE} S) [DecidableEq N.I]

/-- The finite box of populations whose coordinates are at most R. -/
noncomputable def populationBox (R : ℕ) : Finset (State S) := by
  classical
  exact Finset.univ.image
    (fun w : S → Fin (R + 1) => fun s => (w s).val)

theorem mem_populationBox (R : ℕ) (z : State S) :
    z ∈ populationBox (S := S) R ↔ ∀ s, z s ≤ R := by
  classical
  constructor
  · intro hz
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    intro s
    exact Nat.le_of_lt_succ (w s).isLt
  · intro hz
    let w : S → Fin (R + 1) :=
      fun s => ⟨z s, Nat.lt_succ_of_le (hz s)⟩
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩

/-- A finite-box localization of an initial-segment target mask. -/
def populationLocalizationActive (z0 : State S)
    (active : ℕ → (ℕ → Option N.I) → Prop) (R n : ℕ)
    (ω : ℕ → Option N.I) : Prop :=
  active n ω ∧ ∀ j, j ≤ n → pathState N z0 ω j ∈ populationBox (S := S) R

omit [DecidableEq N.I] in
theorem populationLocalizationActive_initialSegment (z0 : State S)
    (active : ℕ → (ℕ → Option N.I) → Prop) (R : ℕ)
    (hsegment : ∀ ω {m n : ℕ}, m ≤ n → active n ω → active m ω)
    (ω : ℕ → Option N.I) {m n : ℕ} (hmn : m ≤ n)
    (hn : populationLocalizationActive N z0 active R n ω) :
    populationLocalizationActive N z0 active R m ω := by
  refine ⟨hsegment ω hmn hn.1, ?_⟩
  intro j hj
  exact hn.2 j (hj.trans hmn)

/-- U1 is automatic inside each finite population localization. -/
theorem populationLocalization_noExplosion_before
    (hPos : N.hasPositiveRates) (z0 : State S)
    (active : ℕ → (ℕ → Option N.I) → Prop) (R : ℕ) :
    ∀ᵐ η ∂timedLaw N hPos z0,
      (∀ n, populationLocalizationActive N z0 active R n η.1) →
        occupationTime N z0 (populationLocalizationActive N z0 active R) η = ⊤ := by
  apply timedLaw_noExplosion_before_of_finite_states N hPos z0
    (populationLocalizationActive N z0 active R) (populationBox (S := S) R)
  exact Filter.Eventually.of_forall fun ω n hn => hn.2 n le_rfl

/-- An explicit bound containing the first m+1 population states. -/
noncomputable def prefixPopulationBound (z0 : State S)
    (ω : ℕ → Option N.I) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1), ∑ s, pathState N z0 ω j s

theorem population_le_prefixPopulationBound (z0 : State S)
    (ω : ℕ → Option N.I) (m j : ℕ) (hj : j ≤ m) :
    (∑ s, pathState N z0 ω j s) ≤ prefixPopulationBound N z0 ω m := by
  classical
  unfold prefixPopulationBound
  exact Finset.single_le_sum
    (f := fun k : ℕ => ∑ s, pathState N z0 ω k s)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem pathState_le_prefixPopulationBound (z0 : State S)
    (ω : ℕ → Option N.I) (m j : ℕ) (hj : j ≤ m) (s : S) :
    pathState N z0 ω j s ≤ prefixPopulationBound N z0 ω m := by
  classical
  calc
    pathState N z0 ω j s ≤ ∑ r, pathState N z0 ω j r :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    _ ≤ prefixPopulationBound N z0 ω m :=
      population_le_prefixPopulationBound N z0 ω m j hj

theorem jumpTime_monotone (z0 : State S) (η : TimedΩ N) :
    Monotone (fun n => jumpTime N z0 n η) := by
  apply monotone_nat_of_le_succ
  intro n
  change (∑ j ∈ Finset.range n, holdingTime N z0 j η) ≤
    ∑ j ∈ Finset.range (n + 1), holdingTime N z0 j η
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right
    (show (0 : ℝ≥0∞) ≤ holdingTime N z0 n η from bot_le)

omit [DecidableEq S] [DecidableEq N.I] in
/-- Divergence supplies a finite prefix extending beyond any finite horizon. -/
theorem exists_jumpTime_gt_of_noExplosion (z0 : State S) (η : TimedΩ N)
    (hUOne : ∑' n, holdingTime N z0 n η = ⊤)
    (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    ∃ m, t < jumpTime N z0 m η := by
  classical
  by_contra h
  have hbound : ∀ m, jumpTime N z0 m η ≤ t := by
    intro m
    exact le_of_not_gt (fun hm => h ⟨m, hm⟩)
  have hsum : (∑' n, holdingTime N z0 n η) ≤ t :=
    ENNReal.tsum_le_of_sum_range_le hbound
  rw [hUOne] at hsum
  exact ht (top_le_iff.mp hsum)

/-- Both finite bounds can contain a prefix extending beyond a finite horizon. -/
theorem finite_localization_brackets (z0 : State S) (η : TimedΩ N)
    (hUOne : ∑' n, holdingTime N z0 n η = ⊤)
    (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    ∃ R J m : ℕ, m < J ∧ t < jumpTime N z0 m η ∧
      ∀ j, j ≤ m → (∑ s, pathState N z0 η.1 j s) ≤ R := by
  obtain ⟨m, hm⟩ := exists_jumpTime_gt_of_noExplosion N z0 η hUOne t ht
  refine ⟨prefixPopulationBound N z0 η.1 m, m + 1, m,
    Nat.lt_succ_self m, hm, ?_⟩
  intro j hj
  exact population_le_prefixPopulationBound N z0 η.1 m j hj

theorem finite_localization_brackets_ae (hPos : N.hasPositiveRates)
    (z0 : State S)
    (hUOne : ∀ᵐ η ∂timedLaw N hPos z0,
      ∑' n, holdingTime N z0 n η = ⊤) :
    ∀ᵐ η ∂timedLaw N hPos z0, ∀ t : ℝ≥0∞, t ≠ ⊤ →
      ∃ R J m : ℕ, m < J ∧ t < jumpTime N z0 m η ∧
        ∀ j, j ≤ m → (∑ s, pathState N z0 η.1 j s) ≤ R := by
  filter_upwards [hUOne] with η hη
  intro t ht
  exact finite_localization_brackets N z0 η hη t ht

/-- Every jump state reached before the first inactive index has an open mask. -/
theorem active_of_jumpTime_le_before_firstExitTime (z0 : State S)
    (active : ℕ → (ℕ → Option N.I) → Prop) (η : TimedΩ N)
    (t : ℝ≥0∞) (ht : t < firstExitTime N z0 active η)
    (j : ℕ) (hj : jumpTime N z0 j η ≤ t) : active j η.1 := by
  classical
  by_contra hnot
  have hexit : ∃ n, ¬ active n η.1 := ⟨j, hnot⟩
  have hfind : Nat.find hexit ≤ j := Nat.find_min' hexit hnot
  have htime : firstExitTime N z0 active η ≤ jumpTime N z0 j η := by
    rw [firstExitTime, dif_pos hexit]
    exact jumpTime_monotone N z0 η hfind
  exact (not_lt_of_ge (htime.trans hj)) ht

/-- Global U1 identifies initial-segment occupation with the first-exit time. -/
theorem occupationTime_ae_eq_firstExitTime_of_noExplosion
    (hPos : N.hasPositiveRates) (z0 : State S)
    (active : ℕ → (ℕ → Option N.I) → Prop)
    (hsegment : ∀ (η : TimedΩ N) {m n : ℕ},
      m ≤ n → active n η.1 → active m η.1)
    (hUOne : ∀ᵐ η ∂timedLaw N hPos z0,
      ∑' n, holdingTime N z0 n η = ⊤) :
    occupationTime N z0 active =ᵐ[timedLaw N hPos z0]
      firstExitTime N z0 active := by
  apply occupationTime_ae_eq_firstExitTime N hPos z0 active hsegment
  filter_upwards [hUOne] with η hη
  intro hall
  rw [occupationTime_eq_tsum]
  simpa only [hall, if_true] using hη

end LocalizationExhaustion

section CTMStoppedIdentification

open ClockedCTM

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ}

theorem ctmElapsed_ae_eq_firstExitTime_of_noExplosion (C : CTM Q)
    (z0 : State (Sp Q L)) (K : ℕ)
    (hUOne : ∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∑' n, holdingTime (net C L) z0 n η = ⊤) :
    ctmElapsed C z0 K =ᵐ[timedLaw (net C L) (net_hasPositiveRates C L) z0]
      firstExitTime (net C L) z0 (ctmActive K) := by
  apply occupationTime_ae_eq_firstExitTime_of_noExplosion
    (net C L) (net_hasPositiveRates C L) z0 (ctmActive K)
    (fun η _ _ hmn hn => ctmActive_initialSegment K η.1 hmn hn) hUOne

theorem lintegral_ctmFirstExitTime_of_noExplosion (C : CTM Q)
    (z0 : State (Sp Q L)) (K : ℕ)
    (hUOne : ∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∑' n, holdingTime (net C L) z0 n η = ⊤) :
    (∫⁻ η, firstExitTime (net C L) z0 (ctmActive K) η
      ∂timedLaw (net C L) (net_hasPositiveRates C L) z0) =
        expTime C z0 K := by
  calc
    (∫⁻ η, firstExitTime (net C L) z0 (ctmActive K) η
        ∂timedLaw (net C L) (net_hasPositiveRates C L) z0) =
        ∫⁻ η, ctmElapsed C z0 K η
          ∂timedLaw (net C L) (net_hasPositiveRates C L) z0 :=
      lintegral_congr_ae
        (ctmElapsed_ae_eq_firstExitTime_of_noExplosion C z0 K hUOne).symm
    _ = expTime C z0 K := lintegral_ctmElapsed C z0 K

end CTMStoppedIdentification


section FiniteHorizonLocalization

universe uH vH
variable {S : Type uH} [Fintype S] [DecidableEq S]
variable (N : Network.{uH, vH} S) [DecidableEq N.I]

/-- U1 supplies a finite localization agreeing with every state reached by a
finite horizon before the target.  Natural absorption is allowed. -/
theorem finite_localization_agrees_before_target
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (z0 : State S) (k0 K : ℕ) (η : TimedΩ N)
    (hlabels : ∀ n, pathFired N z0 η.1 n = η.1 (n + 1))
    (hUOne : ∑' n, holdingTime N z0 n η = ⊤)
    (t : ℝ≥0∞) (ht : t ≠ ⊤)
    (hbefore : t < firstExitTime N z0
      (fun n ω => rawTargetCount N inc z0 k0 ω n < K) η) :
    ∃ R J : ℕ, ∀ n, jumpTime N z0 n η ≤ t →
      (channels N inc R K J).labelStatePath (encode R K J z0 k0 0) η.1 n ≠ none ∧
      population ((channels N inc R K J).labelStatePath
        (encode R K J z0 k0 0) η.1 n) = pathState N z0 η.1 n := by
  obtain ⟨R, J, m, hmJ, htm, hpop⟩ :=
    finite_localization_brackets N z0 η hUOne t ht
  refine ⟨R, J, ?_⟩
  intro n hn
  have hnm : n < m := by
    by_contra h
    have hmn : m ≤ n := Nat.le_of_not_gt h
    exact (not_lt_of_ge ((jumpTime_monotone N z0 η hmn).trans hn)) htm
  have hnJ : n < J := hnm.trans hmJ
  have hpopulation : ∀ j, j ≤ n →
      populationSize (pathState N z0 η.1 j) ≤ R := by
    intro j hj
    exact hpop j (hj.trans hnm.le)
  have htarget : ∀ j, j ≤ n → rawTargetCount N inc z0 k0 η.1 j < K := by
    intro j hj
    exact active_of_jumpTime_le_before_firstExitTime N z0
      (fun n ω => rawTargetCount N inc z0 k0 ω n < K) η t hbefore j
      ((jumpTime_monotone N z0 η hj).trans hn)
  have hlive := labelStatePath_ne_none_of_population_and_target_bounds
    N hPos inc R K J z0 k0 η.1 hlabels n hnJ hpopulation htarget
  refine ⟨hlive, ?_⟩
  cases hx : (channels N inc R K J).labelStatePath
      (encode R K J z0 k0 0) η.1 n with
  | none => exact (hlive hx).elim
  | some x =>
      exact labelStatePath_population_of_fired_eq_label
        N hPos inc R K J z0 k0 η.1 hlabels n x hx

end FiniteHorizonLocalization

section CTMFiniteHorizonLocalization

open ClockedCTM

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ}

/-- The stopping counter counts the clocked CTM's tick reaction. -/
def ctmTickIncrement (_z : State (Sp Q L)) (i : Rx Q L) : ℕ :=
  if i = .tick then 1 else 0

theorem rawTargetCount_ctmTick_eq_ticks (C : CTM Q)
    (z0 : State (Sp Q L)) (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    rawTargetCount (net C L) ctmTickIncrement z0 0 ω n = ticks n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rawTargetCount, ticks, ih]
      cases ho : ω (n + 1) with
      | none => simp [ho]
      | some i => simp [ho, ctmTickIncrement]

/-- Conditional U1 gives finite-localization coverage of every pre-target
finite horizon on a single conull set. -/
theorem ctm_finite_localizations_agree_before_target
    (C : CTM Q) (z0 : State (Sp Q L)) (K : ℕ)
    (hUOne : ∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∑' n, holdingTime (net C L) z0 n η = ⊤) :
    ∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∀ t : ℝ≥0∞, t ≠ ⊤ →
        t < firstExitTime (net C L) z0 (ctmActive K) η →
        ∃ R J : ℕ, ∀ n, jumpTime (net C L) z0 n η ≤ t →
          (channels (net C L) ctmTickIncrement R K J).labelStatePath
            (encode R K J z0 0 0) η.1 n ≠ none ∧
          population ((channels (net C L) ctmTickIncrement R K J).labelStatePath
            (encode R K J z0 0 0) η.1 n) =
              pathState (net C L) z0 η.1 n := by
  filter_upwards [hUOne,
    timedLaw_fired_eq_label_ae (net C L) (net_hasPositiveRates C L) z0] with η hη hlabels
  intro t ht hbefore
  apply finite_localization_agrees_before_target
    (net C L) (net_hasPositiveRates C L) ctmTickIncrement z0 0 K η hlabels hη t ht
  simpa only [rawTargetCount_ctmTick_eq_ticks, ctmActive] using hbefore

end CTMFiniteHorizonLocalization


section DiagonalLocalizationExhaustion

universe uX vX
variable {S : Type uX} [Fintype S] [DecidableEq S]
variable (N : Network.{uX, vX} S) [DecidableEq N.I]

/-- One diagonal sequence of finite localizations eventually agrees with
every population reached in each finite pre-target horizon. -/
theorem diagonal_localizations_agree_before_target
    (hPos : N.hasPositiveRates) (inc : State S → N.I → ℕ)
    (z0 : State S) (k0 K : ℕ) (η : TimedΩ N)
    (hlabels : ∀ n, pathFired N z0 η.1 n = η.1 (n + 1))
    (hUOne : ∑' n, holdingTime N z0 n η = ⊤)
    (t : ℝ≥0∞) (ht : t ≠ ⊤)
    (hbefore : t < firstExitTime N z0
      (fun n ω => rawTargetCount N inc z0 k0 ω n < K) η) :
    ∃ B : ℕ, ∀ b, B ≤ b → ∀ n, jumpTime N z0 n η ≤ t →
      (channels N inc b K b).labelStatePath (encode b K b z0 k0 0) η.1 n ≠ none ∧
      population ((channels N inc b K b).labelStatePath
        (encode b K b z0 k0 0) η.1 n) = pathState N z0 η.1 n := by
  obtain ⟨R, J, m, hmJ, htm, hpop⟩ :=
    finite_localization_brackets N z0 η hUOne t ht
  refine ⟨max R J, ?_⟩
  intro b hb n hn
  have hRb : R ≤ b := (le_max_left R J).trans hb
  have hJb : J ≤ b := (le_max_right R J).trans hb
  have hnm : n < m := by
    by_contra h
    have hmn : m ≤ n := Nat.le_of_not_gt h
    exact (not_lt_of_ge ((jumpTime_monotone N z0 η hmn).trans hn)) htm
  have hnb : n < b := (hnm.trans hmJ).trans_le hJb
  have hpopulation : ∀ j, j ≤ n →
      populationSize (pathState N z0 η.1 j) ≤ b := by
    intro j hj
    exact (hpop j (hj.trans hnm.le)).trans hRb
  have htarget : ∀ j, j ≤ n → rawTargetCount N inc z0 k0 η.1 j < K := by
    intro j hj
    exact active_of_jumpTime_le_before_firstExitTime N z0
      (fun n ω => rawTargetCount N inc z0 k0 ω n < K) η t hbefore j
      ((jumpTime_monotone N z0 η hj).trans hn)
  have hlive := labelStatePath_ne_none_of_population_and_target_bounds
    N hPos inc b K b z0 k0 η.1 hlabels n hnb hpopulation htarget
  refine ⟨hlive, ?_⟩
  cases hx : (channels N inc b K b).labelStatePath
      (encode b K b z0 k0 0) η.1 n with
  | none => exact (hlive hx).elim
  | some x =>
      exact labelStatePath_population_of_fired_eq_label
        N hPos inc b K b z0 k0 η.1 hlabels n x hx

end DiagonalLocalizationExhaustion

section CTMDiagonalLocalizationExhaustion

open ClockedCTM

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ}

/-- With U1, the stopped finite-Q models exhaust every finite pre-target CTM
horizon; no single global finite population domain is asserted. -/
theorem ctm_diagonal_localizations_agree_before_target
    (C : CTM Q) (z0 : State (Sp Q L)) (K : ℕ)
    (hUOne : ∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∑' n, holdingTime (net C L) z0 n η = ⊤) :
    ∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∀ t : ℝ≥0∞, t ≠ ⊤ →
        t < firstExitTime (net C L) z0 (ctmActive K) η →
        ∃ B : ℕ, ∀ b, B ≤ b → ∀ n, jumpTime (net C L) z0 n η ≤ t →
          (channels (net C L) ctmTickIncrement b K b).labelStatePath
            (encode b K b z0 0 0) η.1 n ≠ none ∧
          population ((channels (net C L) ctmTickIncrement b K b).labelStatePath
            (encode b K b z0 0 0) η.1 n) =
              pathState (net C L) z0 η.1 n := by
  filter_upwards [hUOne,
    timedLaw_fired_eq_label_ae (net C L) (net_hasPositiveRates C L) z0] with η hη hlabels
  intro t ht hbefore
  apply diagonal_localizations_agree_before_target
    (net C L) (net_hasPositiveRates C L) ctmTickIncrement z0 0 K η hlabels hη t ht
  simpa only [rawTargetCount_ctmTick_eq_ticks, ctmActive] using hbefore

/-- U3 for the CTM as a family of finite stopped canonical laws, together
with U1-dependent exhaustion and identification of the target stopping time. -/
theorem ctm_identification_up_to_target_of_noExplosion
    (C : CTM Q) (z0 : State (Sp Q L)) (K : ℕ)
    (hUOne : ∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∑' n, holdingTime (net C L) z0 n η = ⊤) :
    (∀ b : ℕ,
      (timedLaw (net C L) (net_hasPositiveRates C L) z0).map
          ((channels (net C L) ctmTickIncrement b K b).recordMap
            (encode b K b z0 0 0)) =
        (channels (net C L) ctmTickIncrement b K b).qMatrix.canonicalRecordMeasure
          (encode b K b z0 0 0)) ∧
    (∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∀ t : ℝ≥0∞, t ≠ ⊤ →
        t < firstExitTime (net C L) z0 (ctmActive K) η →
        ∃ B : ℕ, ∀ b, B ≤ b → ∀ n, jumpTime (net C L) z0 n η ≤ t →
          (channels (net C L) ctmTickIncrement b K b).labelStatePath
            (encode b K b z0 0 0) η.1 n ≠ none ∧
          population ((channels (net C L) ctmTickIncrement b K b).labelStatePath
            (encode b K b z0 0 0) η.1 n) =
              pathState (net C L) z0 η.1 n) ∧
    (ctmElapsed C z0 K =ᵐ[timedLaw (net C L) (net_hasPositiveRates C L) z0]
      firstExitTime (net C L) z0 (ctmActive K)) := by
  refine ⟨?_, ctm_diagonal_localizations_agree_before_target C z0 K hUOne,
    ctmElapsed_ae_eq_firstExitTime_of_noExplosion C z0 K hUOne⟩
  intro b
  exact timedLaw_map_localizedRecord
    (net C L) (net_hasPositiveRates C L) ctmTickIncrement b K b z0 0

end CTMDiagonalLocalizationExhaustion


section NullReactionCounterexample

/-- One positive-rate reaction that never changes the population. -/
def nullReactionNetwork : Network PUnit where
  I := PUnit
  fintypeI := inferInstance
  rxn _ := { l := 0, r := 0, k := 1 }

theorem nullReactionNetwork_hasPositiveRates :
    nullReactionNetwork.hasPositiveRates := by
  intro i
  exact (show (0 : Rate) < 1 from zero_lt_one)

theorem nullReactionNetwork_fire (z : State PUnit) (i : nullReactionNetwork.I) :
    (nullReactionNetwork.rxn i).fire z = z := by
  funext s
  simp [Reaction.fire, nullReactionNetwork]

theorem nullReactionNetwork_totalPropensity (z : State PUnit) :
    nullReactionNetwork.totalPropensity z = 1 := by
  simp [Network.totalPropensity, Reaction.propensity, nullReactionNetwork]

theorem nullReactionNetwork_nonselfRate (z : State PUnit) :
    (∑ i, if (nullReactionNetwork.rxn i).fire z = z then
      (0 : Rate) else (nullReactionNetwork.rxn i).propensity z) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  rw [nullReactionNetwork_fire, if_pos rfl]

end NullReactionCounterexample

end

end Ripple.sCRNUniversality.CTMCIdentification
