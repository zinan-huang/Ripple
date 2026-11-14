import Ripple.sCRNUniversality.CTMCIdentification
import Ripple.CTMC.ExpMartingale

/-!
# Global nonexplosion of the clocked CTM

The generic argument uses the finite-localization record-law identification
and the existing finite-Q exponential martingale. A second, independent
jump-count cutoff makes each auxiliary state space finite without assuming
that all states reachable from the initial state form a finite set.

For the CTM, the conserved control, clock, and catalyst populations give
a linear bound on the propensity-weighted positive population increment.
The deliberately nonoptimal coefficient includes the number of reaction
channels; this does not affect global nonexplosion.
-/

namespace Ripple.sCRNUniversality.CTMGlobalNonexplosion

open MeasureTheory ProbabilityTheory Preorder
open Ripple.CTMC
open Stochastic Stochastic.MassAction CTMCBridge CTMCIdentification
open scoped BigOperators ENNReal NNReal

universe u v

noncomputable section

section FiniteExponentialEstimate

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem realStepExponent_eq_before (Q : QMatrix X) (φ : X → ℝ)
    (t u : ℝ) (x : X) (r : ℝ × X)
    (hu : 0 ≤ u) (hr : 0 ≤ r.1) (ht : u + r.1 ≤ t) :
    Q.realStepExponent φ t u x r =
      φ r.2 - φ x - r.1 * Q.expCompRateReal φ x := by
  have hut : u ≤ t := (le_add_of_nonneg_right hr).trans ht
  simp only [QMatrix.realStepExponent, max_eq_left hu, max_eq_left hr,
    if_pos ht, min_eq_left ht, min_eq_left hut]
  ring

theorem realExpSum_lower_of_prefix (Q : QMatrix X) (φ : X → ℝ)
    (c t : ℝ) (ρ : ℕ → ℝ × X) (n : ℕ)
    (hhold : ∀ k, 0 ≤ (ρ (k + 1)).1)
    (htime : recordElapsed ρ n ≤ t)
    (hcomp : ∀ k, k < n → Q.expCompRateReal φ (ρ k).2 ≤ c) :
    φ (ρ n).2 - φ (ρ 0).2 - c * recordElapsed ρ n ≤
      Q.realExpSum φ t n ρ := by
  have hnonneg (k : ℕ) : 0 ≤ recordElapsed ρ k := by
    unfold recordElapsed
    exact Finset.sum_nonneg (fun j _ => hhold j)
  have hmono : Monotone (recordElapsed ρ) := recordElapsed_mono ρ hhold
  revert htime hcomp
  induction n with
  | zero =>
      intro _ _
      simp [recordElapsed, QMatrix.realExpSum]
  | succ n ih =>
      intro htime hcomp
      have hpre : recordElapsed ρ n ≤ t :=
        (hmono (Nat.le_succ n)).trans htime
      have ih' := ih hpre (fun k hk => hcomp k (lt_trans hk (Nat.lt_succ_self n)))
      have hstep := realStepExponent_eq_before Q φ t (recordElapsed ρ n)
        (ρ n).2 (ρ (n + 1)) (hnonneg n) (hhold n)
        (by simpa only [recordElapsed_succ] using htime)
      have hcost :=
        mul_le_mul_of_nonneg_left (hcomp n (Nat.lt_succ_self n)) (hhold n)
      have hsum := Q.realExpSum_succ φ t n ρ
      change Q.realExpSum φ t (n + 1) ρ =
        Q.realExpSum φ t n ρ +
          Q.realStepExponent φ t (recordElapsed ρ n)
            (ρ n).2 (ρ (n + 1)) at hsum
      rw [hstep] at hsum
      rw [recordElapsed_succ]
      nlinarith only [ih', hcost, hsum]

end FiniteExponentialEstimate

theorem finiteChannels_expCompRateReal
    {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (D : FiniteChannels X I) (φ : X → ℝ) (x : X) :
    D.qMatrix.expCompRateReal φ x =
      ∑ i, (D.channelRate x i : ℝ) *
        (Real.exp (φ (D.destination x i) - φ x) - 1) := by
  classical
  let g : X → ℝ := fun y => Real.exp (φ y - φ x) - 1
  have hg : g x = 0 := by simp [g]
  change (∑ y ∈ Finset.univ.filter (· ≠ x), D.qMatrix.rate x y * g y) =
    ∑ i, (D.channelRate x i : ℝ) * g (D.destination x i)
  calc
    _ = ∑ y, (D.destinationRate x y : ℝ) * g y := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = x
      · subst y
        simp [hg]
      · rw [if_pos hy, D.qMatrix_rate_offdiag x y (Ne.symm hy)]
    _ = ∑ i, ∑ y,
        ((if D.destination x i = y then D.channelRate x i else 0 : Rate) : ℝ) *
          g y := by
      simp only [FiniteChannels.destinationRate, NNRat.cast_sum]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ y, if y = D.destination x i then
            (D.channelRate x i : ℝ) * g y else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : y = D.destination x i
          · subst y
            simp
          · simp [hy, Ne.symm hy]
        _ = _ := by simp

section GenericTimedLaw

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-- A fixed finite label horizon has a deterministic finite population bound. -/
theorem exists_population_bound_for_prefix (z0 : State S) (m : ℕ) :
    ∃ P : ℕ, ∀ ω : ℕ → Option N.I, ∀ n ≤ m,
      populationSize (pathState N z0 ω n) ≤ P := by
  classical
  refine ⟨∑ j ∈ Finset.range (m + 1),
    ∑ p : (i : Finset.Iic j) → Option N.I, populationSize (prefixToState N z0 j p), ?_⟩
  intro ω n hn
  rw [← prefixToState_eq_pathState N z0 ω n]
  exact
    (Finset.single_le_sum
      (f := fun p : (i : Finset.Iic n) → Option N.I =>
        populationSize (prefixToState N z0 n p))
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (frestrictLe (π := fun _ : ℕ => Option N.I) n ω))).trans
    (Finset.single_le_sum
      (f := fun j => ∑ p : (i : Finset.Iic j) → Option N.I,
        populationSize (prefixToState N z0 j p))
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

theorem rawTargetCount_zero_increment (z0 : State S)
    (ω : ℕ → Option N.I) (n : ℕ) :
    rawTargetCount N (fun _ _ => 0) z0 0 ω n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases h : ω (n + 1) <;> simp [rawTargetCount, h, ih]

def localLyapunov (V : State S → ℝ) {R K J : ℕ} : LocalState S R K J → ℝ
  | none => 1
  | some x => V (population (some x : LocalState S R K J))

theorem one_le_localLyapunov (V : State S → ℝ)
    (hV : ∀ z, 1 ≤ V z) {R K J : ℕ} (x : LocalState S R K J) :
    1 ≤ localLyapunov V x := by
  cases x with
  | none => exact le_rfl
  | some x => exact hV _

theorem localLyapunov_encode (V : State S → ℝ) (R K J : ℕ)
    (z : State S) (k j : ℕ)
    (h : populationSize z ≤ R ∧ k < K ∧ j < J) :
    localLyapunov V (encode R K J z k j) = V z := by
  unfold encode
  rw [dif_pos h] <;> rfl

theorem localLyapunov_advance_le (inc : State S → N.I → ℕ)
    (V : State S → ℝ) (hV : ∀ z, 1 ≤ V z)
    {R K J : ℕ} (x : BoundedPopulation S R × Fin K × Fin J) (i : N.I) :
    localLyapunov V (advance N inc (some x : LocalState S R K J) i) ≤
      V ((N.rxn i).fire (population (some x : LocalState S R K J))) := by
  cases hnext : advance N inc (some x : LocalState S R K J) i with
  | none => exact hV _
  | some y =>
      change V (population (some y : LocalState S R K J)) ≤ _
      rw [population_advance_of_eq_some N inc x y i hnext] <;> exact le_rfl

theorem localized_log_comp_le (inc : State S → N.I → ℕ)
    (R K J : ℕ) (V : State S → ℝ) (hV : ∀ z, 1 ≤ V z)
    (c : ℝ) (x : BoundedPopulation S R × Fin K × Fin J)
    (hdrift : (∑ i, ((N.rxn i).propensity
          (population (some x : LocalState S R K J)) : ℝ) *
        max (V ((N.rxn i).fire (population (some x : LocalState S R K J))) -
          V (population (some x : LocalState S R K J))) 0) ≤
      c * V (population (some x : LocalState S R K J))) :
    (channels N inc R K J).qMatrix.expCompRateReal
      (fun y => Real.log (localLyapunov V y)) (some x) ≤ c := by
  let z : State S := population (some x : LocalState S R K J)
  have hpos (y : LocalState S R K J) : 0 < localLyapunov V y :=
    lt_of_lt_of_le zero_lt_one (one_le_localLyapunov V hV y)
  have hv : 0 < V z := lt_of_lt_of_le zero_lt_one (hV z)
  rw [finiteChannels_expCompRateReal]
  change (∑ i, ((N.rxn i).propensity z : ℝ) *
      (Real.exp (Real.log (localLyapunov V
          (advance N inc (some x : LocalState S R K J) i)) -
        Real.log (V z)) - 1)) ≤ c
  have hterm (i : N.I) :
      ((N.rxn i).propensity z : ℝ) *
        (Real.exp (Real.log (localLyapunov V
            (advance N inc (some x : LocalState S R K J) i)) -
          Real.log (V z)) - 1) ≤
      (((N.rxn i).propensity z : ℝ) *
        max (V ((N.rxn i).fire z) - V z) 0) / V z := by
    have hnext :
        localLyapunov V (advance N inc (some x : LocalState S R K J) i) ≤
          V ((N.rxn i).fire z) :=
      localLyapunov_advance_le N inc V hV x i
    have hdiff :
        localLyapunov V (advance N inc (some x : LocalState S R K J) i) - V z ≤
          max (V ((N.rxn i).fire z) - V z) 0 :=
      (sub_le_sub_right hnext (V z)).trans (le_max_left _ _)
    rw [Real.exp_sub, Real.exp_log (hpos _), Real.exp_log hv]
    calc
      _ = (((N.rxn i).propensity z : ℝ) *
          (localLyapunov V
              (advance N inc (some x : LocalState S R K J) i) -
            V z)) / V z := by
        field_simp [hv.ne']
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiff
          ((N.rxn i).propensity z).cast_nonneg) hv.le
  calc
    _ ≤ ∑ i, (((N.rxn i).propensity z : ℝ) *
        max (V ((N.rxn i).fire z) - V z) 0) / V z :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, ((N.rxn i).propensity z : ℝ) *
        max (V ((N.rxn i).fire z) - V z) 0) / V z := by
      rw [Finset.sum_div]
    _ ≤ (c * V z) / V z :=
      div_le_div_of_nonneg_right hdrift hv.le
    _ = c := by field_simp [hv.ne']

/-- A finite-jump-horizon exit estimate, uniform in the jump horizon. -/
theorem timedLaw_lyapunov_exit_le_finite
    (hPos : N.hasPositiveRates) (z0 : State S)
    (V : State S → ℝ) (hV : ∀ z, 1 ≤ V z)
    (c : ℝ) (hc : 0 ≤ c)
    (hdrift : ∀ (ω : ℕ → Option N.I) (n : ℕ),
      (∑ i, ((N.rxn i).propensity (pathState N z0 ω n) : ℝ) *
        max (V ((N.rxn i).fire (pathState N z0 ω n)) -
          V (pathState N z0 ω n)) 0) ≤
        c * V (pathState N z0 ω n))
    (T R m : ℕ) :
    timedLaw N hPos z0 {η | ∃ n ≤ m,
      (R : ℝ) ≤ V (pathState N z0 η.1 n) ∧
        jumpTime N z0 n η ≤ (T : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (c * T) * V z0) / (R : ℝ≥0∞) := by
  classical
  have hVpos : 0 < V z0 := lt_of_lt_of_le zero_lt_one (hV z0)
  by_cases hRzero : R = 0
  · subst R
    have hnum :
        ENNReal.ofReal (Real.exp (c * T) * V z0) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr
        (mul_pos (Real.exp_pos _) hVpos)
    simp only [Nat.cast_zero, div_eq_mul_inv, ENNReal.inv_zero,
      ENNReal.mul_top hnum, le_top]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero hRzero
  obtain ⟨P, hP⟩ := exists_population_bound_for_prefix N z0 m
  let D := channels N (fun _ _ => 0) P 1 (m + 1)
  let x0 := encode P 1 (m + 1) z0 0 0
  let φ : LocalState S P 1 (m + 1) → ℝ :=
    fun x => Real.log (localLyapunov V x)
  let a : ℝ := Real.log (R : ℝ) - Real.log (V z0) - c * T
  let G : Set (ℕ → ℝ × LocalState S P 1 (m + 1)) :=
    {ρ | ∃ n, Real.exp a ≤ Real.exp (D.qMatrix.realExpSum φ (T : ℝ) n ρ)}
  have hG : MeasurableSet G := by
    have heq : G = ⋃ n : ℕ,
        {ρ | Real.exp a ≤ Real.exp (D.qMatrix.realExpSum φ (T : ℝ) n ρ)} := by
      ext ρ
      simp only [G, Set.mem_setOf_eq, Set.mem_iUnion]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    have hm : Measurable (D.qMatrix.realExpSum φ (T : ℝ) n) :=
      (D.qMatrix.measurable_realExpSum_canonicalRecordFiltration φ (T : ℝ) n).mono
        ((QMatrix.canonicalRecordFiltration
          (S := LocalState S P 1 (m + 1))).le n) le_rfl
    exact measurableSet_le measurable_const (Real.continuous_exp.measurable.comp hm)
  have hVzero : localLyapunov V x0 = V z0 := by
    apply localLyapunov_encode
    exact ⟨hP (fun _ => none) 0 (Nat.zero_le m), by omega, by omega⟩
  have hsubset :
      ∀ᵐ η ∂timedLaw N hPos z0,
        (∃ n ≤ m, (R : ℝ) ≤ V (pathState N z0 η.1 n) ∧
          jumpTime N z0 n η ≤ (T : ℝ≥0∞)) →
        D.recordMap x0 η ∈ G := by
    filter_upwards [timedLaw_fired_eq_label_ae N hPos z0,
      timedLaw_clocks_pos_ae N hPos z0] with η hlabels hclock
    rintro ⟨n, hnm, hVR, htime⟩
    have hne (j : ℕ) (hj : j ≤ m) : D.labelStatePath x0 η.1 j ≠ none := by
      apply labelStatePath_ne_none_of_population_and_target_bounds
        N hPos (fun _ _ => 0) P 1 (m + 1) z0 0 η.1 hlabels j
        (Nat.lt_succ_of_le hj)
      · intro k hk
        exact hP η.1 k (hk.trans hj)
      · intro k _
        rw [rawTargetCount_zero_increment]
        omega
    have hpop (j : ℕ) (hj : j ≤ m) :
        population (D.labelStatePath x0 η.1 j) = pathState N z0 η.1 j := by
      cases hs : D.labelStatePath x0 η.1 j with
      | none => exact (hne j hj hs).elim
      | some x =>
          exact labelStatePath_population_of_fired_eq_label
            N hPos (fun _ _ => 0) P 1 (m + 1) z0 0 η.1 hlabels j x hs
    have hvalue (j : ℕ) (hj : j ≤ m) :
        localLyapunov V (D.labelStatePath x0 η.1 j) =
          V (pathState N z0 η.1 j) := by
      cases hs : D.labelStatePath x0 η.1 j with
      | none => exact (hne j hj hs).elim
      | some x =>
          change V (population (some x : LocalState S P 1 (m + 1))) = _
          exact congrArg V (by simpa only [hs] using hpop j hj)
    have hrate (j : ℕ) (hj : j < n) :
        N.totalPropensity (pathState N z0 η.1 j) ≠ 0 := by
      intro hz
      have htop := holdingTime_eq_top_of_rate_eq_zero N z0 j η hz (hclock j)
      have hle : holdingTime N z0 j η ≤ (T : ℝ≥0∞) :=
        (Finset.single_le_sum (f := fun k => holdingTime N z0 k η)
          (fun _ _ => zero_le') (Finset.mem_range.mpr hj)).trans htime
      rw [htop] at hle
      exact (not_le_of_gt (by simp : (T : ℝ≥0∞) < ⊤)) hle
    have hpre (j : ℕ) (hj : j < n) :
        D.totalRate (D.labelStatePath x0 η.1 j) ≠ 0 := by
      have hjm : j ≤ m := (Nat.le_of_lt hj).trans hnm
      cases hs : D.labelStatePath x0 η.1 j with
      | none => exact (hne j hjm hs).elim
      | some x =>
          change N.totalPropensity (population (some x : LocalState S P 1 (m + 1))) ≠ 0
          have hp := hpop j hjm
          rw [hs] at hp
          rw [hp]
          exact hrate j hj
    let ρ := D.recordMap x0 η
    have hhold (j : ℕ) : 0 ≤ (ρ (j + 1)).1 :=
      D.recordMap_holding_nonneg x0 η (fun k => (hclock k).le) j
    have heqtime : ENNReal.ofReal (recordElapsed ρ n) = jumpTime N z0 n η :=
      localized_recordElapsed_eq_jumpTime N hPos (fun _ _ => 0)
        P 1 (m + 1) z0 0 η hlabels (fun k => (hclock k).le) n hpre
    have ht : recordElapsed ρ n ≤ (T : ℝ) :=
      ENNReal.ofReal_le_natCast.mp (heqtime.le.trans htime)
    have hcomp (j : ℕ) (hj : j < n) :
        D.qMatrix.expCompRateReal φ (ρ j).2 ≤ c := by
      change D.qMatrix.expCompRateReal φ (D.recordMap x0 η j).2 ≤ c
      rw [D.recordMap_state]
      have hjm : j ≤ m := (Nat.le_of_lt hj).trans hnm
      cases hs : D.labelStatePath x0 η.1 j with
      | none => exact (hne j hjm hs).elim
      | some x =>
          apply localized_log_comp_le N (fun _ _ => 0) P 1 (m + 1) V hV c x
          have hp := hpop j hjm
          rw [hs] at hp
          simpa only [hp] using hdrift η.1 j
    have hφ :
        Real.log (R : ℝ) - Real.log (V z0) ≤ φ (ρ n).2 - φ x0 := by
      change Real.log (R : ℝ) - Real.log (V z0) ≤
        Real.log (localLyapunov V (D.recordMap x0 η n).2) -
          Real.log (localLyapunov V x0)
      rw [D.recordMap_state, hvalue n hnm, hVzero]
      exact sub_le_sub_right
        (Real.log_le_log hRpos hVR) _
    have hlower := realExpSum_lower_of_prefix D.qMatrix φ c (T : ℝ) ρ n hhold ht hcomp
    have hinit : (ρ 0).2 = x0 := rfl
    simp only [hinit] at hlower
    have hct := mul_le_mul_of_nonneg_left ht hc
    refine ⟨n, Real.exp_le_exp.mpr ?_⟩
    dsimp only [a]
    linarith only [hlower, hct, hφ]
  calc
    _ ≤ timedLaw N hPos z0 ((D.recordMap x0) ⁻¹' G) := measure_mono_ae hsubset
    _ = ((timedLaw N hPos z0).map (D.recordMap x0)) G :=
      (Measure.map_apply (D.measurable_recordMap x0) hG).symm
    _ = D.qMatrix.canonicalRecordMeasure x0 G := by
      rw [timedLaw_map_localizedRecord N hPos (fun _ _ => 0) P 1 (m + 1) z0 0]
    _ ≤ ENNReal.ofReal (1 / Real.exp a) :=
      D.qMatrix.ville_realExpSum φ (T : ℝ) x0 (Real.exp_pos a)
    _ = ENNReal.ofReal (Real.exp (c * T) * V z0) / (R : ℝ≥0∞) := by
      calc
        _ = ENNReal.ofReal (Real.exp (c * T) * V z0 / (R : ℝ)) := by
          congr 1
          simp only [a, Real.exp_sub, Real.exp_log hRpos, Real.exp_log hVpos]
          field_simp [hRpos.ne', hVpos.ne', (Real.exp_pos (c * T)).ne'] <;> ring
        _ = _ := by
          rw [ENNReal.ofReal_div_of_pos hRpos, ENNReal.ofReal_natCast]

/-- The exit estimate after removing the auxiliary jump-count horizon. -/
theorem timedLaw_lyapunov_exit_le
    (hPos : N.hasPositiveRates) (z0 : State S)
    (V : State S → ℝ) (hV : ∀ z, 1 ≤ V z)
    (c : ℝ) (hc : 0 ≤ c)
    (hdrift : ∀ (ω : ℕ → Option N.I) (n : ℕ),
      (∑ i, ((N.rxn i).propensity (pathState N z0 ω n) : ℝ) *
        max (V ((N.rxn i).fire (pathState N z0 ω n)) -
          V (pathState N z0 ω n)) 0) ≤
        c * V (pathState N z0 ω n))
    (T R : ℕ) :
    timedLaw N hPos z0 {η | ∃ n,
      (R : ℝ) ≤ V (pathState N z0 η.1 n) ∧
        jumpTime N z0 n η ≤ (T : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (c * T) * V z0) / (R : ℝ≥0∞) := by
  let E : ℕ → Set (TimedΩ N) := fun m => {η | ∃ n ≤ m,
    (R : ℝ) ≤ V (pathState N z0 η.1 n) ∧ jumpTime N z0 n η ≤ (T : ℝ≥0∞)}
  have heq : {η : TimedΩ N | ∃ n,
      (R : ℝ) ≤ V (pathState N z0 η.1 n) ∧ jumpTime N z0 n η ≤ (T : ℝ≥0∞)} =
      ⋃ m, E m := by
    ext η
    simp only [E, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, n, le_rfl, hn⟩
    · rintro ⟨m, n, _, hn⟩
      exact ⟨n, hn⟩
  have hmono : Monotone E := by
    intro m k hmk η hη
    obtain ⟨n, hnm, hn⟩ := hη
    exact ⟨n, hnm.trans hmk, hn⟩
  rw [heq]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono)
    (fun m => timedLaw_lyapunov_exit_le_finite N hPos z0 V hV c hc hdrift T R m)

/-- Bounded rates on Lyapunov sublevels and vanishing exit bounds imply U1. -/
theorem timedLaw_noExplosion_of_vanishing_exit_bounds
    (hPos : N.hasPositiveRates) (z0 : State S)
    (V : State S → ℝ) (B : ℕ → ℝ≥0)
    (hB : ∀ (R : ℕ) (ω : ℕ → Option N.I) (n : ℕ),
      V (pathState N z0 ω n) < (R : ℝ) →
        (N.totalPropensity (pathState N z0 ω n) : ℝ≥0) ≤ B R)
    (b : ℕ → ℕ → ℝ≥0∞)
    (hb : ∀ T, (⨅ R, b T R) = 0)
    (hexit : ∀ (T R : ℕ),
      timedLaw N hPos z0 {η | ∃ n,
        (R : ℝ) ≤ V (pathState N z0 η.1 n) ∧
          jumpTime N z0 n η ≤ (T : ℝ≥0∞)} ≤ b T R) :
    ∀ᵐ η ∂timedLaw N hPos z0,
      (∑' n, holdingTime N z0 n η) = ⊤ := by
  have hbounded (T : ℕ) : ∀ᵐ η ∂timedLaw N hPos z0,
      ∃ R : ℕ, ∀ n, jumpTime N z0 n η ≤ (T : ℝ≥0∞) →
        V (pathState N z0 η.1 n) < (R : ℝ) := by
    have hnull : timedLaw N hPos z0 {η | ∀ R : ℕ, ∃ n,
        (R : ℝ) ≤ V (pathState N z0 η.1 n) ∧
          jumpTime N z0 n η ≤ (T : ℝ≥0∞)} = 0 := by
      refine le_antisymm ?_ (by simp)
      calc
        _ ≤ ⨅ R : ℕ, b T R := by
          apply le_iInf
          intro R
          exact (measure_mono (fun η hη => by
            simp only [Set.mem_setOf_eq] at hη ⊢; exact hη R)).trans (hexit T R)
        _ = 0 := hb T
    rw [ae_iff]
    apply measure_mono_null ?_ hnull
    intro η hη R
    by_contra hnot
    apply hη
    refine ⟨R, ?_⟩
    intro n hn
    exact lt_of_not_ge (fun hV => hnot ⟨n, hV, hn⟩)
  have hall : ∀ᵐ η ∂timedLaw N hPos z0, ∀ T : ℕ,
      ∃ R : ℕ, ∀ n, jumpTime N z0 n η ≤ (T : ℝ≥0∞) →
        V (pathState N z0 η.1 n) < (R : ℝ) :=
    ae_all_iff.mpr hbounded
  filter_upwards [hall, timedLaw_unitClock_sum_eq_top_ae N hPos z0] with η hη hc
  by_contra hfinite
  obtain ⟨T, hT⟩ := ENNReal.exists_nat_gt hfinite
  obtain ⟨R, hR⟩ := hη T
  have hrates : ∀ n,
      (N.totalPropensity (pathState N z0 η.1 n) : ℝ≥0∞) ≤
        (B R : ℝ≥0∞) := by
    intro n
    have ht : jumpTime N z0 n η ≤ (T : ℝ≥0∞) :=
      (ENNReal.sum_le_tsum (Finset.range n)).trans hT.le
    exact_mod_cast hB R η.1 n (hR n ht)
  exact hfinite (holdingTime_tsum_eq_top_of_bound N z0 η
    (B R : ℝ≥0∞) ENNReal.coe_ne_top hrates hc)

theorem iInf_div_natCast_eq_zero (a : ℝ≥0∞) (ha : a ≠ ⊤) :
    (⨅ R : ℕ, a / (R : ℝ≥0∞)) = 0 := by
  simp_rw [div_eq_mul_inv]
  rw [← ENNReal.mul_iInf (fun h => (ha h).elim),
    ← ENNReal.inv_iSup, ENNReal.iSup_natCast]
  simp

/-- Global nonexplosion from a real-valued Lyapunov function.

The drift and rate-bound hypotheses are required only on sanitized paths from z0.
A bounded single-jump increment is unnecessary: finite label prefixes supply the
finite auxiliary localizations used in the proof. -/
theorem timedLaw_noExplosion_of_linearLyapunov
    (hPos : N.hasPositiveRates) (z0 : State S)
    (V : State S → ℝ) (hV : ∀ z, 1 ≤ V z)
    (c : ℝ) (hc : 0 ≤ c)
    (hdrift : ∀ (ω : ℕ → Option N.I) (n : ℕ),
      (∑ i, ((N.rxn i).propensity (pathState N z0 ω n) : ℝ) *
        max (V ((N.rxn i).fire (pathState N z0 ω n)) -
          V (pathState N z0 ω n)) 0) ≤
        c * V (pathState N z0 ω n))
    (B : ℕ → ℝ≥0)
    (hB : ∀ (R : ℕ) (ω : ℕ → Option N.I) (n : ℕ),
      V (pathState N z0 ω n) < (R : ℝ) →
        (N.totalPropensity (pathState N z0 ω n) : ℝ≥0) ≤ B R) :
    ∀ᵐ η ∂timedLaw N hPos z0,
      (∑' n, holdingTime N z0 n η) = ⊤ := by
  apply timedLaw_noExplosion_of_vanishing_exit_bounds N hPos z0 V B hB
    (fun T R => ENNReal.ofReal (Real.exp (c * T) * V z0) / (R : ℝ≥0∞))
  · intro T
    exact iInf_div_natCast_eq_zero _ ENNReal.ofReal_ne_top
  · exact timedLaw_lyapunov_exit_le N hPos z0 V hV c hc hdrift

end GenericTimedLaw

/-! ## The clocked CTM network -/

section NetworkBounds

open ClockedCTM


def weightedPopulation {S : Type u} [Fintype S]
    (w : S → ℕ) (z : State S) : ℕ := ∑ s, w s * z s

theorem weightedPopulation_zero {S : Type u} [Fintype S] (w : S → ℕ) :
    weightedPopulation w 0 = 0 := by
  simp [weightedPopulation]

theorem weightedPopulation_add {S : Type u} [Fintype S]
    (w : S → ℕ) (z x : State S) :
    weightedPopulation w (z + x) =
      weightedPopulation w z + weightedPopulation w x := by
  simp [weightedPopulation, Nat.mul_add, Finset.sum_add_distrib]

theorem weightedPopulation_nsmul {S : Type u} [Fintype S]
    (w : S → ℕ) (k : ℕ) (z : State S) :
    weightedPopulation w (k • z) = k * weightedPopulation w z := by
  induction k with
  | zero => simp [weightedPopulation_zero]
  | succ k ih =>
      rw [succ_nsmul, weightedPopulation_add, ih, Nat.succ_mul]

theorem weightedPopulation_fire_balance {S : Type u} [Fintype S]
    (w : S → ℕ) (ρ : Reaction S) (z : State S) (he : ρ.enabled z) :
    weightedPopulation w (ρ.fire z) + weightedPopulation w ρ.l =
      weightedPopulation w z + weightedPopulation w ρ.r := by
  unfold weightedPopulation
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hs : ρ.fire z s + ρ.l s = z s + ρ.r s := by
    have hle := he s
    simp only [Reaction.fire_apply]
    omega
  calc
    w s * ρ.fire z s + w s * ρ.l s =
        w s * (ρ.fire z s + ρ.l s) := (Nat.mul_add _ _ _).symm
    _ = w s * (z s + ρ.r s) := congrArg (fun x => w s * x) hs
    _ = w s * z s + w s * ρ.r s := Nat.mul_add _ _ _

theorem weightedPopulation_fire_le {S : Type u} [Fintype S]
    (w : S → ℕ) (ρ : Reaction S) (z : State S) :
    weightedPopulation w (ρ.fire z) ≤
      weightedPopulation w z + weightedPopulation w ρ.r := by
  unfold weightedPopulation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  simp only [Reaction.fire_apply, Nat.mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) le_rfl

theorem conserved_pathState {S : Type u} [Fintype S] [DecidableEq S]
    (N : Network.{u, v} S) [DecidableEq N.I] {α : Type*}
    (g : State S → α)
    (hg : ∀ z i, (N.rxn i).enabled z → g ((N.rxn i).fire z) = g z)
    (z0 : State S) (ω : ℕ → Option N.I) (n : ℕ) :
    g (pathState N z0 ω n) = g z0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change g (stateStep N (pathState N z0 ω n) (ω (n + 1))) = g z0
      unfold stateStep
      split_ifs with hT
      · exact ih
      · exact (hg _ _ (fireOptionSanitized_enabled N _ _ hT)).trans ih

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ}

theorem weightedPopulation_one (w : Sp Q L → ℕ) (s : Sp Q L) :
    weightedPopulation w (one s) = w s := by
  simp [weightedPopulation, one, mul_ite]

def controlWeight : Sp Q L → ℕ
  | .s1 _ | .s2 _ | .s3 _ | .rq _ | .u _ _ => 1
  | _ => 0

def clockWeight : Sp Q L → ℕ
  | .clk _ => 1
  | _ => 0

def controlPopulation (z : State (Sp Q L)) : ℕ :=
  weightedPopulation controlWeight z

def clockPopulation (z : State (Sp Q L)) : ℕ :=
  weightedPopulation clockWeight z

def moleculeCount (z : State (Sp Q L)) : ℕ :=
  weightedPopulation (fun _ => 1) z

def populationLyapunov (z : State (Sp Q L)) : ℕ := 1 + moleculeCount z

theorem populationLyapunov_pos (z : State (Sp Q L)) :
    1 ≤ populationLyapunov z := by
  unfold populationLyapunov
  omega

theorem coord_le_population (z : State (Sp Q L)) (s : Sp Q L) :
    z s ≤ moleculeCount z := by
  simpa only [moleculeCount, weightedPopulation, one_mul] using
    (Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ s))

theorem u_le_controlPopulation (z : State (Sp Q L)) (q : Q) (b : Bool) :
    z (.u q b) ≤ controlPopulation z := by
  have h := Finset.single_le_sum
    (f := fun s => controlWeight s * z s) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (Sp.u q b))
  simpa only [controlWeight, one_mul, controlPopulation, weightedPopulation] using h

theorem clk_le_clockPopulation (z : State (Sp Q L)) (c : Fin (L + 1)) :
    z (.clk c) ≤ clockPopulation z := by
  have h := Finset.single_le_sum
    (f := fun s => clockWeight s * z s) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (Sp.clk c))
  simpa only [clockWeight, one_mul, clockPopulation, weightedPopulation] using h

theorem control_complex_balance (C : CTM Q) (i : Rx Q L) :
    weightedPopulation controlWeight (rxn C i).l =
      weightedPopulation controlWeight (rxn C i).r := by
  change weightedPopulation controlWeight (one (src1 i) + one (src2 C i)) =
    weightedPopulation controlWeight (out C i)
  cases i <;>
    simp only [src1, src2, out, weightedPopulation_add, weightedPopulation_one,
      weightedPopulation_nsmul, weightedPopulation_zero, controlWeight,
      mul_zero, zero_add, add_zero]

theorem clock_complex_balance (C : CTM Q) (i : Rx Q L) :
    weightedPopulation clockWeight (rxn C i).l =
      weightedPopulation clockWeight (rxn C i).r := by
  change weightedPopulation clockWeight (one (src1 i) + one (src2 C i)) =
    weightedPopulation clockWeight (out C i)
  cases i <;>
    simp only [src1, src2, out, weightedPopulation_add, weightedPopulation_one,
      weightedPopulation_nsmul, weightedPopulation_zero, clockWeight,
      mul_zero, zero_add, add_zero]

theorem controlPopulation_fire (C : CTM Q) (i : Rx Q L)
    (z : State (Sp Q L)) (he : (rxn C i).enabled z) :
    controlPopulation ((rxn C i).fire z) = controlPopulation z := by
  have h := weightedPopulation_fire_balance controlWeight (rxn C i) z he
  rw [control_complex_balance C i] at h
  exact Nat.add_right_cancel h

theorem clockPopulation_fire (C : CTM Q) (i : Rx Q L)
    (z : State (Sp Q L)) (he : (rxn C i).enabled z) :
    clockPopulation ((rxn C i).fire z) = clockPopulation z := by
  have h := weightedPopulation_fire_balance clockWeight (rxn C i) z he
  rw [clock_complex_balance C i] at h
  exact Nat.add_right_cancel h

theorem acc_fire (C : CTM Q) (i : Rx Q L)
    (z : State (Sp Q L)) (he : (rxn C i).enabled z) :
    (rxn C i).fire z .acc = z .acc := by
  apply Reaction.fire_apply_of_l_eq_r_of_le _ _ _ _ (he .acc)
  cases i <;> simp [rxn, bimol, src1, src2, out, one]

theorem accS_fire (C : CTM Q) (i : Rx Q L)
    (z : State (Sp Q L)) (he : (rxn C i).enabled z) :
    (rxn C i).fire z .accS = z .accS := by
  apply Reaction.fire_apply_of_l_eq_r_of_le _ _ _ _ (he .accS)
  cases i <;> simp [rxn, bimol, src1, src2, out, one]

theorem controlPopulation_pathState (C : CTM Q) (z0 : State (Sp Q L))
    (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    controlPopulation (pathState (net C L) z0 ω n) = controlPopulation z0 :=
  conserved_pathState (net C L) controlPopulation
    (fun z i he => controlPopulation_fire C i z he) z0 ω n

theorem clockPopulation_pathState (C : CTM Q) (z0 : State (Sp Q L))
    (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    clockPopulation (pathState (net C L) z0 ω n) = clockPopulation z0 :=
  conserved_pathState (net C L) clockPopulation
    (fun z i he => clockPopulation_fire C i z he) z0 ω n

theorem acc_pathState (C : CTM Q) (z0 : State (Sp Q L))
    (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    pathState (net C L) z0 ω n .acc = z0 .acc :=
  conserved_pathState (net C L) (fun z => z .acc)
    (fun z i he => acc_fire C i z he) z0 ω n

theorem accS_pathState (C : CTM Q) (z0 : State (Sp Q L))
    (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    pathState (net C L) z0 ω n .accS = z0 .accS :=
  conserved_pathState (net C L) (fun z => z .accS)
    (fun z i he => accS_fire C i z he) z0 ω n

def reactionGrowth (C : CTM Q) : Rx Q L → ℕ
  | .tick => 1
  | .cM _ _ => 2
  | .cD _ _ => 3
  | .cB q b => (C.next q b).2.toNat + 1
  | _ => 0

theorem reactionGrowth_le (C : CTM Q) (i : Rx Q L) :
    reactionGrowth C i ≤ 3 := by
  cases i with
  | cB q b => cases h : (C.next q b).2 <;> simp [reactionGrowth, h]
  | _ => simp [reactionGrowth]

theorem population_input (C : CTM Q) (i : Rx Q L) :
    moleculeCount (rxn C i).l = 2 := by
  change weightedPopulation (fun _ => 1) (one (src1 i) + one (src2 C i)) = 2
  rw [weightedPopulation_add, weightedPopulation_one, weightedPopulation_one]

theorem population_output_growth (C : CTM Q) (i : Rx Q L) :
    moleculeCount (rxn C i).r - 2 = reactionGrowth C i := by
  change weightedPopulation (fun _ => 1) (out C i) - 2 = reactionGrowth C i
  cases i <;>
    simp only [out, weightedPopulation_add, weightedPopulation_one,
      weightedPopulation_nsmul, weightedPopulation_zero, reactionGrowth,
      mul_one] <;> omega

theorem population_output_le (C : CTM Q) (i : Rx Q L) :
    moleculeCount (rxn C i).r ≤ 5 := by
  have h := population_output_growth C i
  have hg := reactionGrowth_le C i
  omega

theorem populationLyapunov_increase (C : CTM Q) (i : Rx Q L)
    (z : State (Sp Q L)) (he : (rxn C i).enabled z) :
    populationLyapunov ((rxn C i).fire z) - populationLyapunov z =
      reactionGrowth C i := by
  have hb := weightedPopulation_fire_balance (fun _ => 1) (rxn C i) z he
  change moleculeCount ((rxn C i).fire z) + moleculeCount (rxn C i).l =
    moleculeCount z + moleculeCount (rxn C i).r at hb
  rw [population_input] at hb
  have hg := population_output_growth C i
  unfold populationLyapunov
  omega

theorem populationLyapunov_fire_le (C : CTM Q) (i : Rx Q L)
    (z : State (Sp Q L)) (he : (rxn C i).enabled z) :
    populationLyapunov ((rxn C i).fire z) ≤ populationLyapunov z + 3 := by
  have h := populationLyapunov_increase C i z he
  have hg := reactionGrowth_le C i
  omega

theorem populationLyapunov_fire_le_unconditional (C : CTM Q) (i : Rx Q L)
    (z : State (Sp Q L)) :
    populationLyapunov ((rxn C i).fire z) ≤ populationLyapunov z + 5 := by
  have h := weightedPopulation_fire_le (fun _ => 1) (rxn C i) z
  have ho := population_output_le C i
  change moleculeCount ((rxn C i).fire z) ≤ moleculeCount z + moleculeCount (rxn C i).r at h
  unfold populationLyapunov
  omega

theorem rate_mul_positive_increase (C : CTM Q) (i : Rx Q L)
    (z : State (Sp Q L)) :
    rate C i z *
      (populationLyapunov ((rxn C i).fire z) - populationLyapunov z) =
      rate C i z * reactionGrowth C i := by
  by_cases h : rate C i z = 0
  · simp only [h, zero_mul]
  · rw [populationLyapunov_increase C i z ((enabled_iff C i z).mpr h)]

/-- A finite, deliberately nonoptimal linear growth coefficient. -/
def growthCoefficient (z : State (Sp Q L)) : ℕ :=
  Fintype.card (Rx Q L) *
    (clockPopulation z * z .accS + 3 * controlPopulation z)

theorem rate_mul_growth_le (C : CTM Q) (i : Rx Q L) (z : State (Sp Q L)) :
    rate C i z * reactionGrowth C i ≤
      (clockPopulation z * z .accS + 3 * controlPopulation z) *
        populationLyapunov z := by
  have hmem (u x k : ℕ) (hu : u ≤ controlPopulation z)
      (hx : x ≤ moleculeCount z) (hk : k ≤ 3) :
      u * x * k ≤
        (clockPopulation z * z .accS + 3 * controlPopulation z) *
          populationLyapunov z := by
    calc
      u * x * k ≤ controlPopulation z * moleculeCount z * 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul hu hx) hk
      _ = (3 * controlPopulation z) * moleculeCount z := by ring
      _ ≤ (3 * controlPopulation z) * populationLyapunov z :=
        Nat.mul_le_mul_left _ (by unfold populationLyapunov; omega)
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  cases i with
  | tick =>
      simp only [rate, src1, src2, reactionGrowth, mul_one]
      calc
        z (.clk 0) * z .accS ≤ clockPopulation z * z .accS :=
          Nat.mul_le_mul_right _ (clk_le_clockPopulation z 0)
        _ ≤ (clockPopulation z * z .accS) * populationLyapunov z := by
          simpa only [mul_one] using
            Nat.mul_le_mul_left (clockPopulation z * z .accS)
              (populationLyapunov_pos z)
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  | cM q b =>
      exact hmem _ _ 2 (u_le_controlPopulation z q b)
        (coord_le_population z (.mem .m)) (by decide)
  | cD q b =>
      exact hmem _ _ 3 (u_le_controlPopulation z q b)
        (coord_le_population z (.mem .d)) (by decide)
  | cB q b =>
      exact hmem _ _ _ (u_le_controlPopulation z q b)
        (coord_le_population z (.mem .b)) (reactionGrowth_le (L := L) C (.cB q b))
  | _ => simp [reactionGrowth]

theorem positive_drift_nat (C : CTM Q) (z : State (Sp Q L)) :
    (∑ i : Rx Q L, rate C i z *
      (populationLyapunov ((rxn C i).fire z) - populationLyapunov z)) ≤
      growthCoefficient z * populationLyapunov z := by
  calc
    _ ≤ ∑ _i : Rx Q L,
        (clockPopulation z * z .accS + 3 * controlPopulation z) *
          populationLyapunov z := by
      apply Finset.sum_le_sum
      intro i _
      rw [rate_mul_positive_increase]
      exact rate_mul_growth_le C i z
    _ = _ := by simp [growthCoefficient, mul_assoc]

theorem positive_drift_real (C : CTM Q) (z : State (Sp Q L)) :
    (∑ i : Rx Q L, ((rxn C i).propensity z : ℝ) *
      ((populationLyapunov ((rxn C i).fire z) -
        populationLyapunov z : ℕ) : ℝ)) ≤
      (growthCoefficient z : ℝ) * (populationLyapunov z : ℝ) := by
  have h : ((∑ i : Rx Q L, rate C i z *
      (populationLyapunov ((rxn C i).fire z) - populationLyapunov z) : ℕ) : ℝ) ≤
      (growthCoefficient z : ℝ) * (populationLyapunov z : ℝ) := by
    exact_mod_cast positive_drift_nat C z
  simpa only [Nat.cast_sum, Nat.cast_mul, propensity_rxn,
    NNRat.cast_mul, NNRat.cast_natCast, rate] using h

theorem growthCoefficient_pathState (C : CTM Q) (z0 : State (Sp Q L))
    (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    growthCoefficient (pathState (net C L) z0 ω n) = growthCoefficient z0 := by
  simp only [growthCoefficient, controlPopulation_pathState,
    clockPopulation_pathState, accS_pathState]

theorem positive_drift_pathState (C : CTM Q) (z0 : State (Sp Q L))
    (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    (∑ i : Rx Q L,
      ((rxn C i).propensity (pathState (net C L) z0 ω n) : ℝ) *
      ((populationLyapunov ((rxn C i).fire (pathState (net C L) z0 ω n)) -
        populationLyapunov (pathState (net C L) z0 ω n) : ℕ) : ℝ)) ≤
      (growthCoefficient z0 : ℝ) *
        (populationLyapunov (pathState (net C L) z0 ω n) : ℝ) := by
  simpa only [growthCoefficient_pathState] using
    positive_drift_real C (pathState (net C L) z0 ω n)

theorem natCast_tsub_eq_max (a b : ℕ) :
    ((a - b : ℕ) : ℝ) = max ((a : ℝ) - (b : ℝ)) 0 := by
  rcases le_total b a with h | h
  · have hadd : ((a - b : ℕ) : ℝ) + (b : ℝ) = (a : ℝ) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel h]
    rw [max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr h))]
    linarith only [hadd]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero,
      max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr h))]

theorem positive_drift_pathState_max (C : CTM Q) (z0 : State (Sp Q L))
    (ω : ℕ → Option (Rx Q L)) (n : ℕ) :
    (∑ i : Rx Q L,
      ((rxn C i).propensity (pathState (net C L) z0 ω n) : ℝ) *
        max ((populationLyapunov ((rxn C i).fire
            (pathState (net C L) z0 ω n)) : ℝ) -
          (populationLyapunov (pathState (net C L) z0 ω n) : ℝ)) 0) ≤
      (growthCoefficient z0 : ℝ) *
        (populationLyapunov (pathState (net C L) z0 ω n) : ℝ) := by
  simpa only [natCast_tsub_eq_max] using positive_drift_pathState C z0 ω n

theorem btot_le_population_square (C : CTM Q) (z : State (Sp Q L)) :
    btot C z ≤ Fintype.card (Rx Q L) * moleculeCount z ^ 2 := by
  calc
    btot C z ≤ ∑ _i : Rx Q L, moleculeCount z * moleculeCount z :=
      Finset.sum_le_sum fun i _ =>
        Nat.mul_le_mul (coord_le_population z (src1 i))
          (coord_le_population z (src2 C i))
    _ = _ := by simp [pow_two]

theorem sublevel_totalRate_bound (C : CTM Q) (R : ℕ)
    (z : State (Sp Q L)) (hz : populationLyapunov z ≤ R) :
    CTMCBridge.totalRate (net C L) z ≤ (Fintype.card (Rx Q L) * R ^ 2 : ℕ) := by
  have hp : moleculeCount z ≤ R := by unfold populationLyapunov at hz; omega
  have hsq : moleculeCount z ^ 2 ≤ R ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hp hp
  have h := (btot_le_population_square C z).trans
    (Nat.mul_le_mul_left _ hsq)
  unfold CTMCBridge.totalRate
  rw [totalPropensity_eq]
  exact_mod_cast h

def emptyStateMachine : CTM Unit := ⟨fun _ _ => ((), false)⟩

theorem disabled_cD_zero_growth :
    ¬ (rxn (L := 0) emptyStateMachine (.cD () false)).enabled (fun _ => 0) ∧
    populationLyapunov ((rxn (L := 0) emptyStateMachine (.cD () false)).fire
      (fun _ => 0)) = 6 ∧
    populationLyapunov (fun _ : Sp Unit 0 => 0) = 1 := by
  unfold Reaction.enabled
  decide

end NetworkBounds


/-! ## Global U1 and unconditional U3 -/

section CTMConsequences

open ClockedCTM

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ}

/-- The clocked CTM is nonexplosive from every finite natural-valued state.
No encoded-initial-state, one-clock, or accuracy assumption is needed. -/
theorem ctm_noExplosion (C : CTM Q) (z0 : State (Sp Q L)) :
    ∀ᵐ η ∂timedLaw (net C L) (net_hasPositiveRates C L) z0,
      ∑' n, holdingTime (net C L) z0 n η = ⊤ := by
  apply timedLaw_noExplosion_of_linearLyapunov
    (net C L) (net_hasPositiveRates C L) z0
    (fun z => (populationLyapunov z : ℝ))
    (fun z => by
      change (1 : ℝ) ≤ (populationLyapunov z : ℝ)
      exact Nat.one_le_cast.mpr (populationLyapunov_pos z))
    (growthCoefficient z0 : ℝ) (Nat.cast_nonneg _)
    (positive_drift_pathState_max C z0)
    (fun R => ((Fintype.card (Rx Q L) * R ^ 2 : ℕ) : ℝ≥0))
  intro R ω n hV
  have hNat : populationLyapunov (pathState (net C L) z0 ω n) < R :=
    Nat.cast_lt.mp hV
  have h := sublevel_totalRate_bound C R (pathState (net C L) z0 ω n) hNat.le
  unfold CTMCBridge.totalRate at h
  exact (NNRat.cast_le_natCast (K := ℝ≥0)).mpr
    ((NNRat.cast_le_natCast (K := ℝ)).mp h)

/-- The U3 headline with global U1 discharged by ctm_noExplosion. -/
theorem ctm_identification_up_to_target
    (C : CTM Q) (z0 : State (Sp Q L)) (K : ℕ) :
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
  exact CTMCIdentification.ctm_identification_up_to_target_of_noExplosion C z0 K
    (ctm_noExplosion C z0)

end CTMConsequences

end

end Ripple.sCRNUniversality.CTMGlobalNonexplosion
