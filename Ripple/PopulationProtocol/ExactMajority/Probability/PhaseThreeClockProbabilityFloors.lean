-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockProbabilityFloors.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockGatedLevelOne

/-!
# Original-law probability floors for the asynchronous clock

This file proves the epidemic part of the gated law, the exceptional
level-one complement formula, and the raw probability floor in PHASE3 (26b).
It also supplies adaptedness of a general selected auxiliary-pair indicator.

These are local ingredients of N12 step 3. No finite-passage, shape, width,
or original-law seed-fibre tail is claimed here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockProbabilityFloors

open TimeTheorem PairLog PairLogAuxiliary
open PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne

variable {L K m : ℕ}

theorem frontCount_le_clockCount (f : Fin m → AgentState L K) (ℓ : ℕ) :
    frontCount f ℓ ≤ clockCount f := by
  apply Finset.card_le_card
  intro i hi
  simp only [aboveSet, clockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.1

theorem clockCount_le_card (f : Fin m → AgentState L K) :
    clockCount f ≤ m := by
  have h := Finset.card_le_card
    (Finset.filter_subset (fun i : Fin m => (f i).role = .clock) Finset.univ)
  simpa only [clockCount, clockSet, Finset.card_univ, Fintype.card_fin] using h

theorem frontCount_zero (f : Fin m → AgentState L K) :
    frontCount f 0 = clockCount f := by
  simp [frontCount, aboveSet, clockCount, clockSet]

theorem clockCount_eq_front_add_exact_zero (f : Fin m → AgentState L K) :
    clockCount f = frontCount f 1 + exactCount f 0 := by
  simpa only [Nat.sub_self, frontCount_zero] using frontCount_pred f 1 le_rfl

theorem inactiveCount_le_exact_zero (f : Fin m → AgentState L K) :
    inactiveCount f ≤ exactCount f 0 := by
  apply Finset.card_le_card
  intro i hi
  simp only [inactiveSet, exactSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi ⊢
  exact ⟨hi.1, effMinute_eq_zero_of_lt_three _ hi.2⟩

theorem mul_pred_add_self (a : ℕ) : a * (a - 1) + a = a * a := by
  by_cases ha : a = 0
  · simp [ha]
  · have hpred : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
    calc
      a * (a - 1) + a = a * (a - 1 + 1) := by ring
      _ = a * a := by rw [hpred]

/-- The complement form of PHASE3 (25a), without a truncated subtraction. -/
theorem gated_pairs_one_complement (f : Fin m → AgentState L K) :
    (goodPairs (GatedTick 1) f).card +
        frontCount f 1 * (frontCount f 1 - 1) +
        inactiveCount f * (inactiveCount f - 1) =
      clockCount f * (clockCount f - 1) := by
  have hcount := goodPairs_gatedTick_card_add f
  have hsplit := clockCount_eq_front_add_exact_zero f
  have hsub : clockCount f - frontCount f 1 = exactCount f 0 := by omega
  rw [hsub] at hcount
  have hfront := mul_pred_add_self (frontCount f 1)
  have hexact := mul_pred_add_self (exactCount f 0)
  have hclock := mul_pred_add_self (clockCount f)
  rw [hsplit] at hclock ⊢
  nlinarith

/-- The epidemic contribution survives the exceptional level-one gate. -/
theorem epidemic_le_gated_pairs (f : Fin m → AgentState L K)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    2 * frontCount f ℓ * (clockCount f - frontCount f ℓ) ≤
      (goodPairs (GatedTick ℓ) f).card := by
  by_cases hone : ℓ = 1
  · subst ℓ
    have hcount := goodPairs_gatedTick_card_add f
    have hi := inactiveCount_le_exact_zero f
    have hprod :
        inactiveCount f * (inactiveCount f - 1) ≤
          exactCount f 0 * (exactCount f 0 - 1) :=
      Nat.mul_le_mul hi (Nat.sub_le_sub_right hi 1)
    omega
  · have htwo : 2 ≤ ℓ := by omega
    rw [goodPairs_gatedTick_eq_of_two_le f ℓ htwo, goodPairs_raisingTick_card]
    exact Nat.le_add_right _ _

/-- A loose but useful level-one base: both the high and inactive
Clock populations may occupy at most one quarter of the Clock labels. -/
theorem half_clock_pairs_le_gated_one (f : Fin m → AgentState L K)
    (hC : 2 ≤ clockCount f)
    (hX : 4 * frontCount f 1 ≤ clockCount f)
    (hI : 4 * inactiveCount f ≤ clockCount f) :
    (clockCount f : ℝ) * ((clockCount f : ℝ) - 1) ≤
      2 * ((goodPairs (GatedTick 1) f).card : ℝ) := by
  have hbalance :
      ((goodPairs (GatedTick 1) f).card : ℝ) +
        (frontCount f 1 * (frontCount f 1 - 1) : ℕ) +
        (inactiveCount f * (inactiveCount f - 1) : ℕ) =
      (clockCount f * (clockCount f - 1) : ℕ) := by
    exact_mod_cast gated_pairs_one_complement f
  have hfront :
      ((frontCount f 1 * (frontCount f 1 - 1) : ℕ) : ℝ) ≤
        (frontCount f 1 : ℝ) * (frontCount f 1 : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left (frontCount f 1)
      (Nat.sub_le (frontCount f 1) 1)
  have hinactive :
      ((inactiveCount f * (inactiveCount f - 1) : ℕ) : ℝ) ≤
        (inactiveCount f : ℝ) * (inactiveCount f : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left (inactiveCount f)
      (Nat.sub_le (inactiveCount f) 1)
  have hXR : 4 * (frontCount f 1 : ℝ) ≤ (clockCount f : ℝ) := by
    exact_mod_cast hX
  have hIR : 4 * (inactiveCount f : ℝ) ≤ (clockCount f : ℝ) := by
    exact_mod_cast hI
  have hCR : (2 : ℝ) ≤ (clockCount f : ℝ) := by exact_mod_cast hC
  have hsX := mul_self_le_mul_self
    (by positivity : 0 ≤ 4 * (frontCount f 1 : ℝ)) hXR
  have hsI := mul_self_le_mul_self
    (by positivity : 0 ≤ 4 * (inactiveCount f : ℝ)) hIR
  have hsC := mul_nonneg
    (by positivity : 0 ≤ (clockCount f : ℝ))
    (by linarith : 0 ≤ (clockCount f : ℝ) - 2)
  have hclockcast :
      ((clockCount f * (clockCount f - 1) : ℕ) : ℝ) =
        (clockCount f : ℝ) * ((clockCount f : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ clockCount f), Nat.cast_one]
  rw [hclockcast] at hbalance
  nlinarith

/-- The probability conditional on sampling two Clock labels is at least 1/2
under the level-one base conditions. This is a count-ratio statement. -/
theorem gated_one_clock_rate_ge_half (f : Fin m → AgentState L K)
    (hC : 2 ≤ clockCount f)
    (hX : 4 * frontCount f 1 ≤ clockCount f)
    (hI : 4 * inactiveCount f ≤ clockCount f) :
    (1 / 2 : ℝ) ≤
      ((goodPairs (GatedTick 1) f).card : ℝ) /
        ((clockCount f : ℝ) * ((clockCount f : ℝ) - 1)) := by
  have hCR : (2 : ℝ) ≤ (clockCount f : ℝ) := by exact_mod_cast hC
  have hden : 0 < (clockCount f : ℝ) * ((clockCount f : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden).2
  simpa only [one_mul, mul_comm] using half_clock_pairs_le_gated_one f hC hX hI

/-- Scalar form of the raw epidemic lower bound in PHASE3 (26b). -/
theorem raw_epidemic_rate_lower (n C X : ℝ)
    (hn : 2 ≤ n) (hX : 0 ≤ X) (hdensity : 6 * n ≤ 25 * C)
    (hsparse : 10 * X ≤ C) :
    X / (3 * n) ≤ 2 * X * (C - X) / (n * (n - 1)) := by
  have hnpos : 0 < n := by linarith
  have hroom : n - 1 ≤ 6 * (C - X) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hroom
    (mul_nonneg hX hnpos.le)
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * n)
    (mul_pos hnpos (by linarith : 0 < n - 1))).2
  nlinarith

/-- The gated raw pair rate is at least X/(3m) throughout the sparse
positive front window. This includes the exceptional first level. -/
theorem gated_raw_rate_lower (f : Fin m → AgentState L K)
    (hm : 2 ≤ m) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hdensity : 6 * m ≤ 25 * clockCount f)
    (hsparse : 10 * frontCount f ℓ ≤ clockCount f) :
    (frontCount f ℓ : ℝ) / (3 * (m : ℝ)) ≤
      ((goodPairs (GatedTick ℓ) f).card : ℝ) /
        ((m : ℝ) * ((m : ℝ) - 1)) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have hXC := frontCount_le_clockCount f ℓ
  have hcount :
      2 * (frontCount f ℓ : ℝ) *
          ((clockCount f : ℝ) - (frontCount f ℓ : ℝ)) ≤
        ((goodPairs (GatedTick ℓ) f).card : ℝ) := by
    have h := epidemic_le_gated_pairs f ℓ hℓ
    have hcast :
        ((2 * frontCount f ℓ * (clockCount f - frontCount f ℓ) : ℕ) : ℝ) ≤
          ((goodPairs (GatedTick ℓ) f).card : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hXC] using hcast
  exact (raw_epidemic_rate_lower (m : ℝ) (clockCount f : ℝ)
    (frontCount f ℓ : ℝ) hmR (by positivity)
    (by exact_mod_cast hdensity) (by exact_mod_cast hsparse)).trans
      (div_le_div_of_nonneg_right hcount hden)

open Classical in
/-- Adaptedness for any selected-pair event evaluated on an auxiliary labelling. -/
theorem stronglyMeasurable_aux_pair_indicator
    (init : Cfg L K) (F : PairRule L K)
    (A : (Fin init.card → AgentState L K) →
      Fin init.card → Fin init.card → Prop) (t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)] (fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          A (auxLabels init F ω t) i j
      then (1 : ℝ) else 0) := by
  let trunc : (Finset.Iic (t + 1) → Draw L K) →
      (Finset.Iic t → Draw L K) :=
    fun q i => q ⟨i.val, Finset.mem_Iic.mpr
      (le_trans (Finset.mem_Iic.mp i.property) (Nat.le_succ t))⟩
  let H : (Finset.Iic (t + 1) → Draw L K) → ℝ := fun q =>
    if ∃ i j,
        selectLabels (prefixLabels init t (trunc q))
          (q ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩) = some (i, j) ∧
        A (auxPrefix init F t (trunc q)) i j
    then 1 else 0
  change StronglyMeasurable[pairLogFiltration L K (t + 1)]
    (fun ω => H (frestrictLe (π := fun _ => Draw L K) (t + 1) ω))
  exact ((measurable_of_countable H).comp
    (measurable_pairLog_prefix L K (t + 1))).stronglyMeasurable

open Classical in
/-- The actual original-law conditional probability has the P3a lower floor.
The two inequalities in the implication are current-state conditions. -/
theorem gated_conditional_front_floor (init : Cfg L K) (hc : 2 ≤ init.card)
    (ℓ t : ℕ) (hℓ : 1 ≤ ℓ) :
    ∀ᵐ ω ∂law init,
      6 * init.card ≤ 25 * clockCount (auxLabels init virtualRule ω t) →
      10 * frontCount (auxLabels init virtualRule ω t) ℓ ≤
          clockCount (auxLabels init virtualRule ω t) →
      (frontCount (auxLabels init virtualRule ω t) ℓ : ℝ) /
          (3 * (init.card : ℝ)) ≤
        ((law init)[fun ω =>
          if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
              GatedTick ℓ (auxLabels init virtualRule ω t) i j
          then (1 : ℝ) else 0 | pairLogFiltration L K t]) ω := by
  filter_upwards [gatedTick_conditional_law init hc ℓ t] with ω hω
  intro hdensity hsparse
  rw [hω]
  exact gated_raw_rate_lower _ hc ℓ hℓ hdensity hsparse

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockProbabilityFloors

end
