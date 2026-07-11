import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.OptimalWindowsFaithful
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.GenericKeystone

set_option linter.style.header false

/-!
# Log-regime time windows

This file rethreads the probabilistic time-window endpoint through a strong
reset seed.  The strong seed records the exact fuel written by the reset
transition (`resetcount = Rmax`) and the leader flag, and deliberately omits
the old `nonResettingCount < resetcount` dominance clause.
-/

namespace SSEM

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

/-- Time-side strong reset seed endpoint.

This is the time-window analogue of `CorrectResetSeedStrong` from the
correctness-side log regime, kept local to the time hierarchy to avoid pulling
the full correctness stack into the complexity keystone. -/
def StrongResetSeed {n : ℕ} (Rmax : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop :=
  (∃ r : Fin n,
    (C r).1.role = .Resetting ∧
    (C r).1.resetcount = Rmax ∧
    (C r).1.leader = .L ∧
    (C r).1.answer = majorityAnswer C) ∧
  (∀ w : Fin n,
    (C w).1.role = .Resetting →
    0 < (C w).1.resetcount ∧
    (C w).1.answer = majorityAnswer C)

/-- Strong seed constructor for a one-step pair reset out of an `InSrank`
configuration.  All non-endpoints were `Settled` before the step, so the
all-Resetting answer clause only has to inspect the two endpoints. -/
theorem strongResetSeed_of_step_pair
    {n : ℕ} {Y : Type*} {P : Protocol (AgentState n) Opinion Y}
    {Rmax : ℕ} {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hRmax_pos : 0 < Rmax)
    (hC : InSrank C) (huv : u ≠ v)
    (hu_role : (C.step P u v u).1.role = .Resetting)
    (hu_rc : (C.step P u v u).1.resetcount = Rmax)
    (hu_L : (C.step P u v u).1.leader = .L)
    (hu_ans : (C.step P u v u).1.answer = majorityAnswer (C.step P u v))
    (_hv_role : (C.step P u v v).1.role = .Resetting)
    (hv_rc : (C.step P u v v).1.resetcount = Rmax)
    (hv_ans : (C.step P u v v).1.answer = majorityAnswer (C.step P u v)) :
    StrongResetSeed Rmax (C.step P u v) := by
  refine ⟨⟨u, hu_role, hu_rc, hu_L, hu_ans⟩, ?_⟩
  intro w hw
  by_cases hwu : w = u
  · subst w
    exact ⟨by rw [hu_rc]; exact hRmax_pos, hu_ans⟩
  · by_cases hwv : w = v
    · subst w
      exact ⟨by rw [hv_rc]; exact hRmax_pos, hv_ans⟩
    · have hw_old : C.step P u v w = C w := by
        unfold Config.step
        simp [huv, hwu, hwv]
      rw [hw_old] at hw
      rw [hC.allSettled w] at hw
      cases hw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000000 in
theorem step_timer_le_one_median_max_creates_StrongResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer ≤ 1)
    (hv_max : (D v).1.rank.val + 1 = n)
    (hμ_correct : (D μ).1.answer = majorityAnswer D)
    (hv_wrong : (D v).1.answer ≠ majorityAnswer D) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    StrongResetSeed Rmax (D.step P μ v) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hv_no_med : (D v).1.rank.val + 1 ≠ ceilHalf n := by
    intro h
    apply hμv
    apply hS.toInSrank.ranks_inj
    exact Fin.ext (Nat.add_right_cancel (hμ_med.trans h.symm))
  have hsi := hS.toInSrank.allSettled μ
  have hsv := hS.toInSrank.allSettled v
  have hrij : (D μ).1.rank ≠ (D v).1.rank :=
    fun h => hμv (hS.toInSrank.ranks_inj h)
  have h_no_swap := hS.swap_condition_false μ v
  have h_post_diff : (D μ).1.answer ≠ (D v).1.answer := by
    rw [hμ_correct]
    exact fun h => hv_wrong h.symm
  have h_fst := Config.step_fst_state P D hμv
  have h_snd := Config.step_snd_state P D hμv (Ne.symm hμv)
  have hv_not_upper : (D v).1.rank.val + 1 ≠ n / 2 + 1 := by omega
  have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := by
      unfold ceilHalf
      omega
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
      rw [← hceil]
      exact hμ_med
    have hv_not_lower : (D v).1.rank.val + 1 ≠ n / 2 := by
      omega
    by_cases hTimer0 : (D μ).1.timer = 0
    · have htr := propagation_reset_fires_even_lower_timer_zero_no_swap_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hpar hμ_lower
        hv_not_lower hv_not_upper hTimer0 h_no_swap h_post_diff
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_v : (D.step P μ v v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hμv
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_correct])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_correct])
    · have hTimer1 : (D μ).1.timer = 1 := by omega
      have htr := propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hμv hpar hμ_lower
        hv_max hTimer1 h_no_swap h_post_diff
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with timer := 0, role := .Resetting, leader := .L, resetcount := Rmax } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_v : (D.step P μ v v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hμv
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_correct])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_correct])
  · have hμ_ans_eq : opinionToAnswer (D μ).2 = (D μ).1.answer := by
      rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar,
        hμ_correct]
    have h_post_diff_odd : opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
      rw [hμ_ans_eq]
      exact h_post_diff
    by_cases hTimer0 : (D μ).1.timer = 0
    · have htr := propagation_reset_fires_no_swap_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hμ_med hv_no_med
        hTimer0 h_no_swap hpar h_post_diff_odd
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_v : (D.step P μ v v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hμv
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_ans_eq, hμ_correct])
    · have hTimer1 : (D μ).1.timer = 1 := by omega
      have htr := propagation_reset_fires_no_swap_max_timer_one_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hμv hμ_med hv_max
        hTimer1 h_no_swap hpar h_post_diff_odd
      have h_post_μ : (D.step P μ v μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2, timer := 0 } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_v : (D.step P μ v v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hμv
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_ans_eq, hμ_correct])

set_option maxHeartbeats 800000000 in
theorem step_timer_zero_median_wrong_nonupper_creates_StrongResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (_hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer = 0)
    (hμ_correct : (D μ).1.answer = majorityAnswer D)
    (hv_wrong : (D v).1.answer ≠ majorityAnswer D)
    (hv_no_upper : (D v).1.rank.val + 1 ≠ n / 2 + 1) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    StrongResetSeed Rmax (D.step P μ v) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hv_no_med : (D v).1.rank.val + 1 ≠ ceilHalf n := by
    intro h
    apply hμv
    apply hS.toInSrank.ranks_inj
    exact Fin.ext (Nat.add_right_cancel (hμ_med.trans h.symm))
  have h_no_swap := hS.swap_condition_false μ v
  have h_post_diff : (D μ).1.answer ≠ (D v).1.answer := by
    rw [hμ_correct]
    exact fun h => hv_wrong h.symm
  have h_fst := Config.step_fst_state P D hμv
  have h_snd := Config.step_snd_state P D hμv (Ne.symm hμv)
  have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := by
      unfold ceilHalf
      omega
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
      rw [← hceil]
      exact hμ_med
    have hv_not_lower : (D v).1.rank.val + 1 ≠ n / 2 := by
      rw [← hceil]
      exact hv_no_med
    have htr := propagation_reset_fires_even_lower_timer_zero_no_swap_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hpar hμ_lower
      hv_not_lower hv_no_upper hμ_timer h_no_swap h_post_diff
    have h_post_μ : (D.step P μ v μ).1 =
        { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax } := by
      rw [h_fst]
      show (transitionPEM _ _ _ _ _).1 = _
      rw [htr]
    have h_post_v : (D.step P μ v v).1 =
        { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
      rw [h_snd]
      show (transitionPEM _ _ _ _ _).2 = _
      rw [htr]
    exact
      strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hμv
        (by rw [h_post_μ])
        (by rw [h_post_μ])
        (by rw [h_post_μ])
        (by rw [h_post_μ]; simp [h_maj, hμ_correct])
        (by rw [h_post_v])
        (by rw [h_post_v])
        (by rw [h_post_v]; simp [h_maj, hμ_correct])
  · have hμ_ans_eq : opinionToAnswer (D μ).2 = (D μ).1.answer := by
      rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar,
        hμ_correct]
    have h_post_diff_odd : opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
      rw [hμ_ans_eq]
      exact h_post_diff
    have htr := propagation_reset_fires_no_swap_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      rankDeltaOSSR_satisfies_fix hS.toInSrank hμv hμ_med hv_no_med
      hμ_timer h_no_swap hpar h_post_diff_odd
    have h_post_μ : (D.step P μ v μ).1 =
        { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
      rw [h_fst]
      show (transitionPEM _ _ _ _ _).1 = _
      rw [htr]
    have h_post_v : (D.step P μ v v).1 =
        { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
      rw [h_snd]
      show (transitionPEM _ _ _ _ _).2 = _
      rw [htr]
    exact
      strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hμv
        (by rw [h_post_μ])
        (by rw [h_post_μ])
        (by rw [h_post_μ])
        (by rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct])
        (by rw [h_post_v])
        (by rw [h_post_v])
        (by rw [h_post_v]; simp [h_maj, hμ_ans_eq, hμ_correct])

set_option maxHeartbeats 800000000 in
theorem step_timer_le_one_max_median_creates_StrongResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {v μ : Fin n} (hvμ : v ≠ μ)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer ≤ 1)
    (hv_max : (D v).1.rank.val + 1 = n)
    (hμ_correct : (D μ).1.answer = majorityAnswer D)
    (hv_wrong : (D v).1.answer ≠ majorityAnswer D) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    StrongResetSeed Rmax (D.step P v μ) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hv_no_med : (D v).1.rank.val + 1 ≠ ceilHalf n := by
    intro h
    apply hvμ
    apply hS.toInSrank.ranks_inj
    exact Fin.ext (Nat.add_right_cancel (h.trans hμ_med.symm))
  have h_no_swap := hS.swap_condition_false v μ
  have h_post_diff : (D μ).1.answer ≠ (D v).1.answer := by
    rw [hμ_correct]
    exact fun h => hv_wrong h.symm
  have h_fst := Config.step_fst_state P D hvμ
  have h_snd := Config.step_snd_state P D hvμ (Ne.symm hvμ)
  have h_maj : majorityAnswer (D.step P v μ) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D v μ
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := by
      unfold ceilHalf
      omega
    have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
      rw [← hceil]
      exact hμ_med
    by_cases hTimer0 : (D μ).1.timer = 0
    · have hv_not_lower : (D v).1.rank.val + 1 ≠ n / 2 := by omega
      have hv_not_upper : (D v).1.rank.val + 1 ≠ n / 2 + 1 := by omega
      have htr := propagation_reset_fires_even_no_swap_responder_median_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hvμ hpar hμ_lower
        hv_not_lower hv_not_upper hTimer0 h_no_swap h_post_diff
      have h_post_v : (D.step P v μ v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_μ : (D.step P v μ μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hvμ
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_correct])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_correct])
    · have hTimer1 : (D μ).1.timer = 1 := by omega
      have htr := propagation_reset_fires_even_no_swap_responder_median_max_timer_one_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hvμ hpar hμ_lower
        hv_max hTimer1 h_no_swap h_post_diff
      have h_post_v : (D.step P v μ v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_μ : (D.step P v μ μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, timer := 0 } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hvμ
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_correct])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_correct])
  · have hμ_ans_eq : opinionToAnswer (D μ).2 = (D μ).1.answer := by
      rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar,
        hμ_correct]
    have h_post_diff_odd : opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
      rw [hμ_ans_eq]
      exact h_post_diff
    by_cases hTimer0 : (D μ).1.timer = 0
    · have htr := propagation_reset_fires_no_swap_responder_median_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hvμ hμ_med hv_no_med
        hTimer0 h_no_swap hpar h_post_diff_odd
      have h_post_v : (D.step P v μ v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_μ : (D.step P v μ μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hvμ
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_ans_eq, hμ_correct])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct])
    · have hTimer1 : (D μ).1.timer = 1 := by omega
      have htr := propagation_reset_fires_no_swap_responder_median_max_timer_one_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hn4 hvμ hμ_med hv_max
        hTimer1 h_no_swap hpar h_post_diff_odd
      have h_post_v : (D.step P v μ v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_μ : (D.step P v μ μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2, timer := 0 } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hvμ
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_ans_eq, hμ_correct])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct])

set_option maxHeartbeats 800000000 in
theorem step_timer_zero_wrong_nonupper_median_creates_StrongResetSeed
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D)
    {v μ : Fin n} (hvμ : v ≠ μ)
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hμ_timer : (D μ).1.timer = 0)
    (hμ_correct : (D μ).1.answer = majorityAnswer D)
    (hv_wrong : (D v).1.answer ≠ majorityAnswer D)
    (hv_no_upper : (D v).1.rank.val + 1 ≠ n / 2 + 1) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    StrongResetSeed Rmax (D.step P v μ) := by
  have hle : (D μ).1.timer ≤ 1 := by omega
  by_cases hv_max : (D v).1.rank.val + 1 = n
  · exact
      step_timer_le_one_max_median_creates_StrongResetSeed
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax_pos hS hvμ hμ_med hle hv_max hμ_correct hv_wrong
  · classical
    set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    have hv_no_med : (D v).1.rank.val + 1 ≠ ceilHalf n := by
      intro h
      apply hvμ
      apply hS.toInSrank.ranks_inj
      exact Fin.ext (Nat.add_right_cancel (h.trans hμ_med.symm))
    have h_no_swap := hS.swap_condition_false v μ
    have h_post_diff : (D μ).1.answer ≠ (D v).1.answer := by
      rw [hμ_correct]
      exact fun h => hv_wrong h.symm
    have h_fst := Config.step_fst_state P D hvμ
    have h_snd := Config.step_snd_state P D hvμ (Ne.symm hvμ)
    have h_maj : majorityAnswer (D.step P v μ) = majorityAnswer D := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D v μ
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := by
        unfold ceilHalf
        omega
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
        rw [← hceil]
        exact hμ_med
      have hv_not_lower : (D v).1.rank.val + 1 ≠ n / 2 := by
        rw [← hceil]
        exact hv_no_med
      have htr := propagation_reset_fires_even_no_swap_responder_median_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hvμ hpar hμ_lower
        hv_not_lower hv_no_upper hμ_timer h_no_swap h_post_diff
      have h_post_v : (D.step P v μ v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := (D μ).1.answer } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_μ : (D.step P v μ μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hvμ
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_correct])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_correct])
    · have hμ_ans_eq : opinionToAnswer (D μ).2 = (D μ).1.answer := by
        rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar,
          hμ_correct]
      have h_post_diff_odd : opinionToAnswer (D μ).2 ≠ (D v).1.answer := by
        rw [hμ_ans_eq]
        exact h_post_diff
      have htr := propagation_reset_fires_no_swap_responder_median_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        rankDeltaOSSR_satisfies_fix hS.toInSrank hvμ hμ_med hv_no_med
        hμ_timer h_no_swap hpar h_post_diff_odd
      have h_post_v : (D.step P v μ v).1 =
          { (D v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_fst]
        show (transitionPEM _ _ _ _ _).1 = _
        rw [htr]
      have h_post_μ : (D.step P v μ μ).1 =
          { (D μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer (D μ).2 } := by
        rw [h_snd]
        show (transitionPEM _ _ _ _ _).2 = _
        rw [htr]
      exact
        strongResetSeed_of_step_pair (P := P) hRmax_pos hS.toInSrank hvμ
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v])
          (by rw [h_post_v]; simp [h_maj, hμ_ans_eq, hμ_correct])
          (by rw [h_post_μ])
          (by rw [h_post_μ])
          (by rw [h_post_μ]; simp [h_maj, hμ_ans_eq, hμ_correct])

private theorem phase4_propagate_fst_settled_of_eq_answer_log
    {n Rmax : ℕ} {b₀ b₁ : AgentState n}
    (hs₀ : b₀.role = .Settled) (heq : b₀.answer = b₁.answer) :
    (phase4_propagate n Rmax b₀ b₁).1.role = .Settled := by
  simp only [phase4_propagate]
  by_cases h1 : b₀.rank.val + 1 = ceilHalf n
  · simp only [h1, ite_true]
    by_cases h2 : b₁.rank.val + 1 = n
    · simp only [h2, ite_true]
      split_ifs with hg
      · exfalso
        exact hg.2 heq
      · exact hs₀
    · simp only [h2, ite_false]
      split_ifs with hg
      · exfalso
        exact hg.2 heq
      · exact hs₀
  · simp only [h1, ite_false]
    by_cases h3 : b₁.rank.val + 1 = ceilHalf n
    · simp only [h3, ite_true]
      by_cases h4 : b₀.rank.val + 1 = n
      · simp only [h4, ite_true]
        split_ifs with hg
        · exfalso
          exact hg.2 heq.symm
        · exact hs₀
      · simp only [h4, ite_false]
        split_ifs with hg
        · exfalso
          exact hg.2 heq.symm
        · exact hs₀
    · simp only [h3, ite_false]
      exact hs₀

private theorem InSswap_preserved_of_output_settled_log
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n} (hS : InSswap D)
    {i j : Fin n} (hij : i ≠ j)
    (hri : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j i).1.role = .Settled)
    (hrj : (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j j).1.role = .Settled) :
    InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have h_rank_w : ∀ w, (D.step P i j w).1.rank = (D w).1.rank :=
    fun w => step_rank_preserved_of_InSswap hn0 hS w
  have h_input_w : ∀ w, (D.step P i j w).2 = (D w).2 :=
    fun w => step_input_preserved P D i j w
  have h_nA : nAOf (D.step P i j) = nAOf D := by
    simp only [P, PEMProtocolCoupled, PEMProtocol]
    exact nAOf_step_eq (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro w
    by_cases hwi : w = i
    · exact hwi ▸ hri
    · by_cases hwj : w = j
      · exact hwj ▸ hrj
      · have : D.step P i j w = D w := by
          unfold Config.step
          simp [hij, hwi, hwj]
        rw [this]
        exact hS.allSettled w
  · intro w₁ w₂ heq
    have : (D w₁).1.rank = (D w₂).1.rank := by
      rw [← h_rank_w w₁, ← h_rank_w w₂]
      exact heq
    exact hS.ranks_inj this
  · intro w
    rw [h_input_w, h_rank_w, h_nA]
    exact hS.input_rank w

set_option maxRecDepth 65536 in
set_option maxHeartbeats 800000000 in
theorem crs_of_InSswap_break_with_MedC_strong
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hS' : ¬ InSswap
      (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j)) :
    StrongResetSeed Rmax
      (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hij : i = j
  · exfalso
    apply hS'
    subst hij
    simp [Config.step]
    exact hS
  have hsi : (D i).1.role = .Settled := hS.toInSrank.allSettled i
  have hsj : (D j).1.role = .Settled := hS.toInSrank.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank :=
    fun h => hij (hS.toInSrank.ranks_inj h)
  have hFix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix
  have hPδ : ∀ p, P.δ p =
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) p :=
    fun _ => rfl
  have hf := Config.step_fst_state P D hij
  have hs := Config.step_snd_state P D hij (Ne.symm hij)
  have hRoles := transitionPEM_role_settled_or_resetting_of_InSswap
    (trank := Rmax) (Rmax := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
    hFix hsi hsj hrij
  have hri : (D.step P i j i).1.role = .Settled ∨
      (D.step P i j i).1.role = .Resetting := by
    rw [congrArg AgentState.role hf, hPδ]
    exact hRoles.1
  have hrj : (D.step P i j j).1.role = .Settled ∨
      (D.step P i j j).1.role = .Resetting := by
    rw [congrArg AgentState.role hs, hPδ]
    exact hRoles.2
  have h_no_swap := hS.swap_condition_false i j
  rcases hri with his | hir
  · rcases hrj with hjs | hjr
    · exfalso
      apply hS'
      exact InSswap_preserved_of_output_settled_log hn0 hS hij his hjs
    · exfalso
      have h2r :
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).2.role = .Resetting := by
        rw [← hPδ, ← congrArg AgentState.role hs]
        exact hjr
      have h1r := transitionPEM_snd_resetting_implies_fst_of_InSswap
        (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
        hFix hsi hsj hrij h2r
      have h1s :
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D i, D j)).1.role = .Settled := by
        rw [← hPδ, ← congrArg AgentState.role hf]
        exact his
      rw [h1s] at h1r
      exact Role.noConfusion h1r
  · have h1r :
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).1.role = .Resetting := by
      rw [← hPδ, ← congrArg AgentState.role hf]
      exact hir
    have h2r := transitionPEM_fst_resetting_implies_snd_of_InSswap
      (trank := Rmax) (x₀ := (D i).2) (x₁ := (D j).2)
      hFix hsi hsj hrij h1r
    have hjr : (D.step P i j j).1.role = .Resetting := by
      rw [congrArg AgentState.role hs, hPδ]
      exact h2r
    by_cases hpar : n % 2 = 0
    · have hmed := transitionPEM_fst_resetting_implies_some_median_even
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hFix hsi hsj hrij h_no_swap hpar h1r
      rcases hmed with hi_med | hj_med
      · have hj_no_med : (D j).1.rank.val + 1 ≠ ceilHalf n := by
          intro h
          exact hrij (Fin.ext (Nat.add_right_cancel (hi_med.trans h.symm)))
        have hi_correct : (D i).1.answer = majorityAnswer D := hM i hi_med
        have hceil : ceilHalf n = n / 2 := by
          unfold ceilHalf
          omega
        have hi_lower : (D i).1.rank.val + 1 = n / 2 := by
          rw [← hceil]
          exact hi_med
        have hj_not_upper : (D j).1.rank.val + 1 ≠ n / 2 + 1 := by
          intro hj_upper
          have hirr := h1r
          simp only [transitionPEM] at hirr
          rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at hirr
          unfold transitionPEM_phase4 at hirr
          simp only [hsi, hsj, and_self, ite_true] at hirr
          unfold phase4_swap at hirr
          simp only [h_no_swap, ite_false] at hirr
          have hd : phase4_decide n (D i).1 (D j).1 (D i).2 (D j).2 =
              if (D i).2 = (D j).2 then
                ({ (D i).1 with answer := opinionToAnswer (D i).2 },
                 { (D j).1 with answer := opinionToAnswer (D i).2 })
              else
                ({ (D i).1 with answer := .outT },
                 { (D j).1 with answer := .outT }) := by
            simp only [phase4_decide, hpar, ite_true]
            simp [hi_lower, show (D j).1.rank.val = n / 2 from by omega]
          rw [hd] at hirr
          split_ifs at hirr
          · exact absurd
              (phase4_propagate_fst_settled_of_eq_answer_log
                (Rmax := Rmax)
                (b₀ := { (D i).1 with answer := opinionToAnswer (D i).2 })
                (b₁ := { (D j).1 with answer := opinionToAnswer (D i).2 })
                hsi rfl)
              (by rw [hirr]; exact Role.noConfusion)
          · exact absurd
              (phase4_propagate_fst_settled_of_eq_answer_log
                (Rmax := Rmax)
                (b₀ := { (D i).1 with answer := .outT })
                (b₁ := { (D j).1 with answer := .outT })
                hsi rfl)
              (by rw [hirr]; exact Role.noConfusion)
        have hdiff : (D i).1.answer ≠ (D j).1.answer := by
          by_contra heq
          have hirr := h1r
          simp only [transitionPEM] at hirr
          rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at hirr
          unfold transitionPEM_phase4 at hirr
          simp only [hsi, hsj, and_self, ite_true] at hirr
          unfold phase4_swap at hirr
          simp only [h_no_swap, ite_false] at hirr
          unfold phase4_decide at hirr
          simp only [hpar, ite_true, hi_lower, hj_not_upper] at hirr
          have hj_not_lower : ¬ ((D j).1.rank.val + 1 = n / 2) := by
            rw [← hceil]
            exact hj_no_med
          simp only [hj_not_lower] at hirr
          simp only [true_and, false_and, ite_false] at hirr
          exact absurd
            (phase4_propagate_fst_settled_of_eq_answer_log
              (Rmax := Rmax) hsi heq)
            (by rw [hirr]; exact Role.noConfusion)
        have hj_wrong : (D j).1.answer ≠ majorityAnswer D := by
          intro h
          exact hdiff (by rw [hi_correct, h])
        by_cases hj_max : (D j).1.rank.val + 1 = n
        · have htimer := transitionPEM_fst_resetting_s0_med_max_even_timer_le_one
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            hFix hsi hsj hrij h_no_swap hpar hn4 hi_med hj_no_med hj_max h1r
          exact
            step_timer_le_one_median_max_creates_StrongResetSeed
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hij hi_med htimer hj_max hi_correct hj_wrong
        · have htimer := transitionPEM_fst_resetting_s0_med_no_max_even_timer_zero
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            hFix hsi hsj hrij h_no_swap hpar hi_med hj_no_med hj_max h1r
          exact
            step_timer_zero_median_wrong_nonupper_creates_StrongResetSeed
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hij hi_med htimer hi_correct hj_wrong
              hj_not_upper
      · have hi_no_med : (D i).1.rank.val + 1 ≠ ceilHalf n := by
          intro h
          exact hrij (Fin.ext (Nat.add_right_cancel (h.trans hj_med.symm)))
        have hj_correct : (D j).1.answer = majorityAnswer D := hM j hj_med
        have h_ans_diff := transitionPEM_fst_resetting_s1_med_even_answer_diff
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hFix hsi hsj hrij h_no_swap hpar hn4 hi_no_med hj_med h1r
        have hi_wrong : (D i).1.answer ≠ majorityAnswer D := by
          intro h
          exact h_ans_diff (by rw [hj_correct, h])
        have hceil : ceilHalf n = n / 2 := by
          unfold ceilHalf
          omega
        have hj_lower : (D j).1.rank.val + 1 = n / 2 := by
          rw [← hceil]
          exact hj_med
        have hi_not_upper : (D i).1.rank.val + 1 ≠ n / 2 + 1 := by
          intro hi_upper
          have hirr := h1r
          simp only [transitionPEM] at hirr
          rw [transitionPEM_prePhase4_eq_of_settled_distinct hFix hsi hsj hrij] at hirr
          unfold transitionPEM_phase4 at hirr
          simp only [hsi, hsj, and_self, ite_true] at hirr
          unfold phase4_swap at hirr
          simp only [h_no_swap, ite_false] at hirr
          unfold phase4_decide at hirr
          have hm : (D j).1.rank.val + 1 = n / 2 ∧
              (D i).1.rank.val + 1 = n / 2 + 1 := ⟨hj_lower, hi_upper⟩
          simp only [hpar, ite_true] at hirr
          simp [hm] at hirr
          split_ifs at hirr
          · exact absurd
              (phase4_propagate_fst_settled_of_eq_answer_log
                (Rmax := Rmax)
                (b₀ := { (D i).1 with answer := opinionToAnswer (D j).2 })
                (b₁ := { (D j).1 with answer := opinionToAnswer (D j).2 })
                hsi rfl)
              (by rw [hirr]; exact Role.noConfusion)
          · exact absurd
              (phase4_propagate_fst_settled_of_eq_answer_log
                (Rmax := Rmax)
                (b₀ := { (D i).1 with answer := .outT })
                (b₁ := { (D j).1 with answer := .outT })
                hsi rfl)
              (by rw [hirr]; exact Role.noConfusion)
        by_cases hi_max : (D i).1.rank.val + 1 = n
        · have htimer := transitionPEM_fst_resetting_s1_med_max_even_timer_le_one
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            hFix hsi hsj hrij h_no_swap hpar hn4 hi_no_med hj_med hi_max h1r
          exact
            step_timer_le_one_max_median_creates_StrongResetSeed
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hij hj_med htimer hi_max hj_correct hi_wrong
        · have htimer := transitionPEM_fst_resetting_s1_med_no_max_even_timer_zero
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            hFix hsi hsj hrij h_no_swap hpar hi_no_med hj_med hi_max h1r
          exact
            step_timer_zero_wrong_nonupper_median_creates_StrongResetSeed
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hij hj_med htimer hj_correct hi_wrong
              hi_not_upper
    · have hmed := transitionPEM_fst_resetting_implies_some_median_odd
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hFix hsi hsj hrij h_no_swap hpar h1r
      rcases hmed with hi_med | hj_med
      · have hj_no_med : (D j).1.rank.val + 1 ≠ ceilHalf n := by
          intro h
          exact hrij (Fin.ext (Nat.add_right_cancel (hi_med.trans h.symm)))
        have h_ans_diff := transitionPEM_fst_resetting_s0_med_odd_answer_diff
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hFix hsi hsj hrij h_no_swap hpar hi_med hj_no_med h1r
        have hi_op_majority : opinionToAnswer (D i).2 = majorityAnswer D :=
          opinionToAnswer_median_eq_majorityAnswer_odd hS hi_med hpar
        have hi_correct : (D i).1.answer = majorityAnswer D := hM i hi_med
        have hj_wrong : (D j).1.answer ≠ majorityAnswer D := by
          intro h
          exact h_ans_diff (by rw [hi_op_majority, h])
        by_cases hj_max : (D j).1.rank.val + 1 = n
        · have htimer := transitionPEM_fst_resetting_s0_med_max_odd_timer_le_one
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            hFix hsi hsj hrij h_no_swap hpar hi_med hj_no_med hj_max h1r
          exact
            step_timer_le_one_median_max_creates_StrongResetSeed
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hij hi_med htimer hj_max hi_correct hj_wrong
        · have htimer := transitionPEM_fst_resetting_s0_med_no_max_odd_timer_zero
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            hFix hsi hsj hrij h_no_swap hpar hi_med hj_no_med hj_max h1r
          have hj_no_upper : (D j).1.rank.val + 1 ≠ n / 2 + 1 := by
            have hceil : ceilHalf n = n / 2 + 1 := by
              unfold ceilHalf
              omega
            rwa [← hceil]
          exact
            step_timer_zero_median_wrong_nonupper_creates_StrongResetSeed
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hij hi_med htimer hi_correct hj_wrong
              hj_no_upper
      · have hi_no_med : (D i).1.rank.val + 1 ≠ ceilHalf n := by
          intro h
          exact hrij (Fin.ext (Nat.add_right_cancel (h.trans hj_med.symm)))
        have h_ans_diff := transitionPEM_fst_resetting_s1_med_odd_answer_diff
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hFix hsi hsj hrij h_no_swap hpar hi_no_med hj_med h1r
        have hj_op_majority : opinionToAnswer (D j).2 = majorityAnswer D :=
          opinionToAnswer_median_eq_majorityAnswer_odd hS hj_med hpar
        have hj_correct : (D j).1.answer = majorityAnswer D := hM j hj_med
        have hi_wrong : (D i).1.answer ≠ majorityAnswer D := by
          intro h
          exact h_ans_diff (by rw [hj_op_majority, h])
        by_cases hi_max : (D i).1.rank.val + 1 = n
        · have htimer := transitionPEM_fst_resetting_s1_med_max_odd_timer_le_one
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            hFix hsi hsj hrij h_no_swap hpar hi_no_med hj_med hi_max h1r
          exact
            step_timer_le_one_max_median_creates_StrongResetSeed
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hij hj_med htimer hi_max hj_correct hi_wrong
        · have htimer := transitionPEM_fst_resetting_s1_med_no_max_odd_timer_zero
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            hFix hsi hsj hrij h_no_swap hpar hi_no_med hj_med hi_max h1r
          have hi_no_upper : (D i).1.rank.val + 1 ≠ n / 2 + 1 := by
            have hceil : ceilHalf n = n / 2 + 1 := by
              unfold ceilHalf
              omega
            rwa [← hceil]
          exact
            step_timer_zero_wrong_nonupper_median_creates_StrongResetSeed
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hij hj_med htimer hj_correct hi_wrong
              hi_no_upper

theorem generic_crs_of_InSswap_break_with_MedC_strong
    {n trank Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D)
    {i j : Fin n}
    (hS' : ¬ InSswap
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j)) :
    StrongResetSeed Rmax
      (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j) := by
  let Pg := PEMProtocol n trank Rmax Emax Dmax hn0
  let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hEq : D.step Pg i j = D.step Pc i j :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank i j
  have hBreakCoupled :
      ¬ InSswap (D.step Pc i j) := by
    intro hCoupled
    exact hS' (by simpa [Pg, Pc, hEq] using hCoupled)
  have hSeedCoupled :
      StrongResetSeed Rmax (D.step Pc i j) :=
    crs_of_InSswap_break_with_MedC_strong
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax_pos hS hM hBreakCoupled
  simpa [Pg, Pc, hEq] using hSeedCoupled

set_option maxHeartbeats 200000 in
theorem timer_ge_two_descent_step_strong
    {n Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) [Inhabited (Fin n × Fin n)] (hn0 : 0 < n)
    (_hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D) (_hT : MedianTimerAtLeast 1 D)
    {μ v : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (D v).1.rank.val + 1 = n)
    (huv : μ ≠ v)
    (hTimer2 : 2 ≤ (D μ).1.timer) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    let Goal := fun D' : Config (AgentState n) Opinion n =>
      IsConsensusConfig D' ∨ StrongResetSeed Rmax D' ∨
        ¬ (InSswap D' ∧ MedianTimerAtLeast 1 D')
    let Inv := fun D' : Config (AgentState n) Opinion n =>
      InSswap D' ∧ MedianAnswerCorrect D' ∧ MedianTimerAtLeast 1 D'
    ((Inv (D.step P μ v) ∧ maxMedianTimer (D.step P μ v) < maxMedianTimer D) ∨
      Goal (D.step P μ v)) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  set Goal := fun D' : Config (AgentState n) Opinion n =>
    IsConsensusConfig D' ∨ StrongResetSeed Rmax D' ∨
      ¬ (InSswap D' ∧ MedianTimerAtLeast 1 D')
  set Inv := fun D' : Config (AgentState n) Opinion n =>
    InSswap D' ∧ MedianAnswerCorrect D' ∧ MedianTimerAtLeast 1 D'
  have h_no_swap := hS.swap_condition_false μ v
  by_cases hS' : InSswap (D.step P μ v)
  · left
    have hM' : MedianAnswerCorrect (D.step P μ v) :=
      step_median_answer_of_InSswap_both hn0 hn4 hS hS' hM
    have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
      rw [step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn0 hS μ]
      exact hμ_med
    have h_timer_le : (D.step P μ v μ).1.timer ≤ (D μ).1.timer :=
      step_timer_le_of_InSswap (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn0 hS μ
    have h_timer_eq : (D.step P μ v μ).1.timer = (D μ).1.timer - 1 := by
      by_cases hpar : n % 2 = 0
      · have hceil : ceilHalf n = n / 2 := by
          unfold ceilHalf
          omega
        have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
          rw [← hceil]
          exact hμ_med
        have hstep := step_at_even_lower_max_timer_ge_two
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          rankDeltaOSSR_satisfies_fix hS hn4 huv hpar hμ_lower hv_max
          h_no_swap hTimer2
        simpa [P, PEMProtocolCoupled, PEMProtocol] using hstep.1
      · have hstep := step_at_median_max_no_swap_odd_explicit
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          rankDeltaOSSR_satisfies_fix hS (by omega : 2 ≤ n) huv hμ_med
          hv_max hpar h_no_swap hTimer2
        simpa [P, PEMProtocolCoupled, PEMProtocol] using hstep.1
    have hTimer1' : MedianTimerAtLeast 1 (D.step P μ v) := by
      intro ν hν
      have hνμ : ν = μ := by
        apply hS'.toInSrank.ranks_inj
        exact Fin.ext (show (D.step P μ v ν).1.rank.val =
          (D.step P μ v μ).1.rank.val by omega)
      subst hνμ
      omega
    have hmm_ge : (D μ).1.timer ≤ maxMedianTimer D := by
      unfold maxMedianTimer
      exact Finset.le_sup_of_le (Finset.mem_univ μ) (by rw [if_pos hμ_med])
    have hmm_le : maxMedianTimer (D.step P μ v) ≤ (D μ).1.timer - 1 := by
      unfold maxMedianTimer
      apply Finset.sup_le
      intro w _
      split_ifs with hw_med
      · have hwμ : w = μ := by
          apply hS'.toInSrank.ranks_inj
          exact Fin.ext (show (D.step P μ v w).1.rank.val =
            (D.step P μ v μ).1.rank.val by omega)
        subst hwμ
        exact le_of_eq h_timer_eq
      · exact Nat.zero_le _
    exact ⟨⟨hS', hM', hTimer1'⟩, by omega⟩
  · right
    exact Or.inr (Or.inr (fun hLive => hS' hLive.1))

theorem generic_timer_ge_two_descent_step_strong
    {n trank Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) [Inhabited (Fin n × Fin n)] (hn0 : 0 < n)
    (hRmax_pos : 0 < Rmax)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) (hM : MedianAnswerCorrect D) (hT : MedianTimerAtLeast 1 D)
    {μ v : Fin n}
    (hμ_med : (D μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (D v).1.rank.val + 1 = n)
    (huv : μ ≠ v)
    (hTimer2 : 2 ≤ (D μ).1.timer) :
    let P := PEMProtocol n trank Rmax Emax Dmax hn0
    let Goal := fun D' : Config (AgentState n) Opinion n =>
      IsConsensusConfig D' ∨ StrongResetSeed Rmax D' ∨
        ¬ (InSswap D' ∧ MedianTimerAtLeast 1 D')
    let Inv := fun D' : Config (AgentState n) Opinion n =>
      InSswap D' ∧ MedianAnswerCorrect D' ∧ MedianTimerAtLeast 1 D'
    ((Inv (D.step P μ v) ∧ maxMedianTimer (D.step P μ v) < maxMedianTimer D) ∨
      Goal (D.step P μ v)) := by
  let Pg := PEMProtocol n trank Rmax Emax Dmax hn0
  let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hEq : D.step Pg μ v = D.step Pc μ v :=
    generic_step_eq_coupled_of_InSrank
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn0 hS.toInSrank μ v
  have hCoupled :=
    timer_ge_two_descent_step_strong
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax_pos hS hM hT hμ_med hv_max huv hTimer2
  simpa [Pg, Pc, hEq] using hCoupled

/-- Productive decision endpoint with the strong reset seed. -/
def DecisionProductiveTargetStrong {n : ℕ} (Rmax : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianAnswerCorrect C ∧ MedianTimerAtLeast 1 C) ∨
    IsConsensusConfig C ∨ StrongResetSeed Rmax C

private theorem log_ennreal_inv_two_eq_inv_four_add_inv_four :
    ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) + ((4 : ENNReal)⁻¹) := by
  have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have h4 : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hsum : ((4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h4, h4⟩
  rw [← ENNReal.toReal_eq_toReal_iff' h2 hsum]
  rw [ENNReal.toReal_add h4 h4]
  simp [ENNReal.toReal_inv]
  norm_num

private theorem ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
    {Q X Y : Type*} {n : ℕ} (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (A B : Config Q X n → Prop) (t : ℕ)
    (hor : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t)
    (hB : Probability.ProbHitWithin P hn C₀ B t ≤ ((4 : ENNReal)⁻¹)) :
    ((4 : ENNReal)⁻¹) ≤ Probability.ProbHitWithin P hn C₀ A t := by
  classical
  let x := Probability.ProbHitWithin P hn C₀ A t
  let y := Probability.ProbHitWithin P hn C₀ B t
  have hOr :
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t ≤ x + y := by
    simpa [x, y] using Probability.ProbHitWithin_union_le P hn C₀ A B t
  have hhalf_le : ((2 : ENNReal)⁻¹) ≤ x + (4 : ENNReal)⁻¹ := by
    calc
      ((2 : ENNReal)⁻¹)
          ≤ Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t := hor
      _ ≤ x + y := hOr
      _ ≤ x + (4 : ENNReal)⁻¹ := by
        exact add_le_add_right (show y ≤ (4 : ENNReal)⁻¹ from hB) x
  have hquarter_ne_top : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  rw [log_ennreal_inv_two_eq_inv_four_add_inv_four] at hhalf_le
  rw [add_comm x ((4 : ENNReal)⁻¹)] at hhalf_le
  exact (ENNReal.add_le_add_iff_left hquarter_ne_top).mp hhalf_le

/-- Decision-before-timeout isolation with the strong endpoint.  The proof
does not use any reset endpoint; it only hits the live MAC branch. -/
theorem generic_decision_before_timer_zero_of_exit_le_quarter_strong
    {n trank Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hS : InSswap C) (hT : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (decisionWindow n) ≤ (4 : ENNReal)⁻¹) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (DecisionProductiveTargetStrong Rmax :
          Config (AgentState n) Opinion n → Prop)
        (decisionWindow n) := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  let LiveDecision : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  let Exit : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  have hn2 : 2 ≤ n := by omega
  by_cases hMAC : MedianAnswerCorrect C
  · have hGoal : DecisionProductiveTargetStrong Rmax C :=
      Or.inl ⟨hS, hMAC, hT⟩
    have hZero :
        Probability.ProbHitWithin P hn2 C
          (DecisionProductiveTargetStrong Rmax :
            Config (AgentState n) Opinion n → Prop) 0 = 1 :=
      Probability.probHitBy_zero_of_goal P hn2 C
        (DecisionProductiveTargetStrong Rmax :
          Config (AgentState n) Opinion n → Prop) hGoal
    have hOne :
        (1 : ENNReal) ≤
          Probability.ProbHitWithin P hn2 C
            (DecisionProductiveTargetStrong Rmax :
              Config (AgentState n) Opinion n → Prop)
            (decisionWindow n) := by
      rw [← hZero]
      exact Probability.ProbHitWithin_mono_time P hn2 C
        (DecisionProductiveTargetStrong Rmax :
          Config (AgentState n) Opinion n → Prop) (Nat.zero_le _)
    exact le_trans (by norm_num : ((4 : ENNReal)⁻¹) ≤ 1) hOne
  · have hGoalEq :
        (fun D : Config (AgentState n) Opinion n =>
            (InSswap D ∧ MedianAnswerCorrect D) ∨ Exit D) =
          (fun D => LiveDecision D ∨ Exit D) := by
      funext D
      apply propext
      constructor
      · intro h
        rcases h with hdec | hexit
        · by_cases htimer : MedianTimerAtLeast 1 D
          · exact Or.inl ⟨hdec.1, hdec.2, htimer⟩
          · exact Or.inr (fun hLive => htimer hLive.2)
        · exact Or.inr hexit
      · intro h
        rcases h with hdec | hexit
        · exact Or.inl ⟨hdec.1, hdec.2.1⟩
        · exact Or.inr hexit
    have hor :
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C
            (fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨ Exit D)
            (decisionWindow n) := by
      simpa [P, Exit, decisionWindow, Nat.mul_assoc] using
        (generic_decision_window
          (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn4 hn0 C hS hT hMAC)
    have hDecision :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C LiveDecision (decisionWindow n) :=
      ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
        P hn2 C LiveDecision Exit (decisionWindow n)
        (by simpa [hGoalEq] using hor)
        (by simpa [P, Exit] using hExit)
    exact hDecision.trans
      (Probability.ProbHitWithin_mono_goal P hn2 C
        LiveDecision
        (DecisionProductiveTargetStrong Rmax :
          Config (AgentState n) Opinion n → Prop)
        (fun D hD => Or.inl hD) (decisionWindow n))

theorem generic_decision_before_timer_zero_strong
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (hS : InSswap C) (hT : MedianTimerAtLeast 35 C) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (DecisionProductiveTargetStrong Rmax :
          Config (AgentState n) Opinion n → Prop)
        (decisionWindow n) := by
  classical
  let P := PEMProtocol n trank Rmax Emax Dmax hn0
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  have hn2 : 2 ≤ n := by omega
  have hT1 : MedianTimerAtLeast 1 C :=
    MedianTimerAtLeast.mono (n := n) (a := 1) (b := 35) (by norm_num) hT
  have hBadBig :
      Probability.ProbHitWithin P hn2 C Bad
          (4 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹ := by
    simpa [P, Bad] using
      (generic_PEM_srank_or_timer_failure_prob_le_quarter_short35_no_counter
        (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn4 hn0 C hS.toInSrank hT)
  have hBadSmall :
      Probability.ProbHitWithin P hn2 C Bad
          (decisionWindow n) ≤ (4 : ENNReal)⁻¹ := by
    exact
      (Probability.ProbHitWithin_mono_time P hn2 C Bad
        (by
          dsimp [decisionWindow]
          nlinarith [Nat.zero_le (n * (n - 1))])).trans hBadBig
  have hExitSmall :
      Probability.ProbHitWithin P hn2 C
          (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
          (decisionWindow n) ≤ (4 : ENNReal)⁻¹ := by
    exact
      (generic_live_exit_ProbHitWithin_le_bad
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 hn2 C ⟨hS, hT1⟩ (decisionWindow n)).trans
        (by simpa [P, Bad] using hBadSmall)
  exact
    generic_decision_before_timer_zero_of_exit_le_quarter_strong
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 C hS hT1 hExitSmall

set_option maxHeartbeats 16000000 in
theorem generic_timer_drain_to_zero_productive_strong
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocol n trank Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  have hmax_zero_of_not_live :
      ∀ D : Config (AgentState n) Opinion n, InSswap D →
        ¬ MedianTimerAtLeast 1 D → maxMedianTimer D = 0 := by
    intro D hSD hnl
    rw [MedianTimerAtLeast] at hnl
    push Not at hnl
    obtain ⟨ν, hν_med, hν_lt⟩ := hnl
    have hν0 : (D ν).1.timer = 0 := by omega
    unfold maxMedianTimer
    apply Nat.le_zero.mp
    apply Finset.sup_le
    intro μ _
    split_ifs with hμ_med
    · have hrank_eq : (D μ).1.rank = (D ν).1.rank := by
        apply Fin.ext
        have h1 : (D μ).1.rank.val + 1 = ceilHalf n := hμ_med
        have h2 : (D ν).1.rank.val + 1 = ceilHalf n := hν_med
        omega
      have hμν : μ = ν := hSD.toInSrank.ranks_inj hrank_eq
      rw [hμν, hν0]
    · exact Nat.zero_le 0
  have hBridge :
      Probability.expectedHittingTime P (by omega : 2 ≤ n) C Goal ≤
        ↑(maxMedianTimer C) * ((n * (n - 1) : ℕ) : ENNReal) := by
    refine Probability.expectedHittingTime_le_of_deterministic_descent
      P (by omega : 2 ≤ n) C Goal Inv maxMedianTimer
      ⟨hSswap, hMedCorrect, hTimerLo⟩ ?_ ?_ ?_ ?_
    ·
        intro D ⟨hSwap_D, hM_D, _hT_D⟩ h0
        exact Or.inr (Or.inr ⟨hSwap_D, hM_D, h0⟩)
    ·
        intro D ⟨hS, hM, hT⟩ _hG i j
        by_cases hS' : InSswap (D.step P i j)
        · have hM' : MedianAnswerCorrect (D.step P i j) :=
            generic_step_median_answer_of_InSswap_both
              (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn0 hn4 hS hS' hM
          by_cases hT' : MedianTimerAtLeast 1 (D.step P i j)
          · exact Or.inl ⟨hS', hM', hT'⟩
          · exact Or.inr (Or.inr (Or.inr ⟨hS', hM', hmax_zero_of_not_live _ hS' hT'⟩))
        · exact Or.inr (Or.inr (Or.inl
            (generic_crs_of_InSswap_break_with_MedC_strong
              (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn4 hn0 hRmax_pos hS hM hS')))
    ·
        intro D ⟨hS, _hM, _hT⟩ _hG i j
        unfold maxMedianTimer
        apply Finset.sup_le
        intro μ _
        split_ifs with hμ_med
        · by_cases hij : i = j
          · subst hij
            simp only [Config.step, ite_true] at hμ_med ⊢
            exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
          · by_cases hμi : μ = i
            · rw [hμi]
              have hrank : (D.step P i j i).1.rank = (D i).1.rank :=
                generic_step_rank_preserved_of_InSswap
                  (trank := trank) (Rmax := Rmax) (Emax := Emax)
                  (Dmax := Dmax) hn0 hS i
              have hμ_pre : (D i).1.rank.val + 1 = ceilHalf n := by
                rw [← hrank]; rwa [hμi] at hμ_med
              calc (D.step P i j i).1.timer
                  ≤ (D i).1.timer :=
                    generic_step_timer_le_of_InSswap
                      (trank := trank) (Rmax := Rmax) (Emax := Emax)
                      (Dmax := Dmax) hn0 hS i
                _ ≤ maxMedianTimer D :=
                    Finset.le_sup_of_le (Finset.mem_univ i) (by simp [hμ_pre])
            · by_cases hμj : μ = j
              · rw [hμj]
                have hrank : (D.step P i j j).1.rank = (D j).1.rank :=
                  generic_step_rank_preserved_of_InSswap
                    (trank := trank) (Rmax := Rmax) (Emax := Emax)
                    (Dmax := Dmax) hn0 hS j
                have hμ_pre : (D j).1.rank.val + 1 = ceilHalf n := by
                  rw [← hrank]; rwa [hμj] at hμ_med
                calc (D.step P i j j).1.timer
                    ≤ (D j).1.timer :=
                      generic_step_timer_le_of_InSswap
                        (trank := trank) (Rmax := Rmax) (Emax := Emax)
                        (Dmax := Dmax) hn0 hS j
                  _ ≤ maxMedianTimer D :=
                      Finset.le_sup_of_le (Finset.mem_univ j) (by simp [hμ_pre])
              · have hbyst : D.step P i j μ = D μ := by
                  unfold Config.step
                  simp [P, hij, hμi, hμj]
                rw [show (D.step P i j μ).1.timer = (D μ).1.timer from
                  congrArg (fun x => x.1.timer) hbyst]
                rw [show (D.step P i j μ).1.rank = (D μ).1.rank from
                  congrArg (fun x => x.1.rank) hbyst] at hμ_med
                exact Finset.le_sup_of_le (Finset.mem_univ μ) (by simp [hμ_med])
        · exact Nat.zero_le _
    ·
        intro D ⟨hS, hM, hT⟩ _hG _hφ
        have hn_pos : 0 < n := by omega
        obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median hn_pos
        have hsurj : Function.Surjective (fun v => (D v).1.rank) :=
          Finite.injective_iff_surjective.mp hS.toInSrank.ranks_inj
        have hn_bound : n - 1 < n := by omega
        obtain ⟨v, hv_eq⟩ := hsurj ⟨n - 1, hn_bound⟩
        have hv_max : (D v).1.rank.val + 1 = n := by
          have h := congrArg Fin.val hv_eq
          simp only at h
          omega
        have huv : μ ≠ v := by
          intro h
          subst h
          have : ceilHalf n = n := by omega
          have : ceilHalf n ≤ (n + 1) / 2 := by
            unfold ceilHalf
            omega
          omega
        refine ⟨μ, v, huv, ?_⟩
        have hTimerPos : 1 ≤ (D μ).1.timer := hT μ hμ_med
        by_cases hTimer2 : 2 ≤ (D μ).1.timer
        · have hstep := generic_timer_ge_two_descent_step_strong
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax_pos hS hM hT hμ_med hv_max huv hTimer2
          simp only [] at hstep
          rcases hstep with hleft | hright
          · exact Or.inl hleft
          · rcases hright with hc | hcrs | hnl
            · exact Or.inr (Or.inl hc)
            · exact Or.inr (Or.inr (Or.inl hcrs))
            · by_cases hS' : InSswap (D.step P μ v)
              · have hM' : MedianAnswerCorrect (D.step P μ v) :=
                  generic_step_median_answer_of_InSswap_both
                    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                    hn0 hn4 hS hS' hM
                have hnt : ¬ MedianTimerAtLeast 1 (D.step P μ v) := fun ht => hnl ⟨hS', ht⟩
                exact Or.inr (Or.inr (Or.inr ⟨hS', hM', hmax_zero_of_not_live _ hS' hnt⟩))
              · exact Or.inr (Or.inr (Or.inl
                  (generic_crs_of_InSswap_break_with_MedC_strong
                    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                    hn4 hn0 hRmax_pos hS hM hS')))
        · have hTimer1 : (D μ).1.timer = 1 := by omega
          by_cases hv_wrong : (D v).1.answer ≠ majorityAnswer D
          · let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
            have hSeedCoupled : StrongResetSeed Rmax (D.step Pc μ v) := by
              simpa [Pc] using
                step_timer_le_one_median_max_creates_StrongResetSeed
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                  hn4 hn0 hRmax_pos hS huv hμ_med (by omega) hv_max
                  (hM μ hμ_med) hv_wrong
            have hEqStep : D.step P μ v = D.step Pc μ v := by
              simpa [P, Pc] using
                generic_step_eq_coupled_of_InSrank
                  (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                  hn0 hS.toInSrank μ v
            exact Or.inr (Or.inr (Or.inl (by rw [hEqStep]; exact hSeedCoupled)))
          · have hv_correct : (D v).1.answer = majorityAnswer D := by
              by_contra h
              exact hv_wrong h
            by_cases hpar : n % 2 = 0
            · have hceil : ceilHalf n = n / 2 := by
                unfold ceilHalf
                omega
              have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
                rw [← hceil]
                exact hμ_med
              have h_post_same : (D μ).1.answer = (D v).1.answer := by
                rw [hM μ hμ_med, hv_correct]
              let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
              have hclean := insswap_drain_median_timer_one_step
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
                hS hn4 huv hpar hμ_lower hv_max hTimer1
                (hS.swap_condition_false μ v) h_post_same
              have hEqStep : D.step P μ v = D.step Pc μ v := by
                simpa [P, Pc] using
                  generic_step_eq_coupled_of_InSrank
                    (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                    hn0 hS.toInSrank μ v
              have hS' : InSswap (D.step P μ v) := by
                rw [hEqStep]
                simpa [Pc, PEMProtocolCoupled, PEMProtocol] using hclean.1
              have hM' : MedianAnswerCorrect (D.step P μ v) :=
                generic_step_median_answer_of_InSswap_both
                  (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                  hn0 hn4 hS hS' hM
              have hμ_timer_post : (D.step P μ v μ).1.timer = 0 := by
                rw [hEqStep]
                simpa [Pc, PEMProtocolCoupled, PEMProtocol] using hclean.2.1
              have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
                rw [hEqStep, hceil]
                simpa [Pc, PEMProtocolCoupled, PEMProtocol] using hclean.2.2.2
              refine Or.inr (Or.inr (Or.inr ⟨hS', hM', ?_⟩))
              apply hmax_zero_of_not_live _ hS'
              rw [MedianTimerAtLeast]
              push Not
              exact ⟨μ, hμ_rank_post, by rw [hμ_timer_post]; norm_num⟩
            · have h_no_swap := hS.swap_condition_false μ v
              have h_post_same : opinionToAnswer (D μ).2 = (D v).1.answer := by
                rw [opinionToAnswer_median_eq_majorityAnswer_odd hS hμ_med hpar,
                  hv_correct]
              have hclean := step_at_median_max_timer_one_no_reset_explicit
                (trank := trank) (Rmax := Rmax)
                (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
                rankDeltaOSSR_satisfies_fix hS hn4 huv hμ_med hv_max hpar
                h_no_swap hTimer1 h_post_same
              have hS' : InSswap (D.step P μ v) := by
                simpa [P, PEMProtocol] using hclean.1
              have hM' : MedianAnswerCorrect (D.step P μ v) :=
                generic_step_median_answer_of_InSswap_both
                  (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                  hn0 hn4 hS hS' hM
              have hμ_timer_post : (D.step P μ v μ).1.timer = 0 := by
                simpa [P, PEMProtocol] using hclean.2.1
              have hμ_rank_post : (D.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
                simpa [P, PEMProtocol] using hclean.2.2.2.1
              refine Or.inr (Or.inr (Or.inr ⟨hS', hM', ?_⟩))
              apply hmax_zero_of_not_live _ hS'
              rw [MedianTimerAtLeast]
              push Not
              exact ⟨μ, hμ_rank_post, by rw [hμ_timer_post]; norm_num⟩
  have hMaxTimer : maxMedianTimer C ≤ T_timer := by
    unfold maxMedianTimer
    apply Finset.sup_le
    intro μ _
    split_ifs with h
    · exact hTimerHi μ
    · exact Nat.zero_le _
  calc Probability.expectedHittingTime P (by omega) C Goal
      ≤ ↑(maxMedianTimer C) * ((n * (n - 1) : ℕ) : ENNReal) := hBridge
    _ ≤ ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
        norm_cast
        calc maxMedianTimer C * (n * (n - 1))
            ≤ T_timer * (n * (n - 1)) :=
              Nat.mul_le_mul_right _ hMaxTimer
          _ = T_timer * n * (n - 1) := by ring

theorem generic_PEM_expected_timer_drain_poly_strong
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
        ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocol n trank Rmax Emax Dmax hn0
  let Productive : Config (AgentState n) Opinion n → Prop :=
    fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)
  let ExitGoal : Config (AgentState n) Opinion n → Prop :=
    fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
      ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  have hProd :
      Probability.expectedHittingTime P (by omega : 2 ≤ n) C Productive ≤
        ((T_timer * n * (n - 1) : ℕ) : ENNReal) := by
    simpa [P, Productive] using
      (generic_timer_drain_to_zero_productive_strong
        (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax_pos T_timer C hSswap hMedCorrect hTimerLo hTimerHi)
  have hmono : ∀ D : Config (AgentState n) Opinion n,
      Productive D → ExitGoal D := by
    intro D hD
    rcases hD with hCons | hSeed | hZero
    · exact Or.inl hCons
    · exact Or.inr (Or.inl hSeed)
    · rcases hZero with ⟨hS, _hM, hmax0⟩
      exact Or.inr (Or.inr (by
        intro hLive
        obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median hn0
        have htimer_ge : 1 ≤ (D μ).1.timer := hLive.2 μ hμ_med
        have htimer_le : (D μ).1.timer ≤ maxMedianTimer D := by
          unfold maxMedianTimer
          exact Finset.le_sup_of_le (Finset.mem_univ μ) (by rw [if_pos hμ_med])
        omega))
  exact
    (Probability.expectedHittingTime_mono_goal P (by omega : 2 ≤ n) C
      Productive ExitGoal hmono).trans hProd

theorem generic_timer_drain_window_strong
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hMAC : MedianAnswerCorrect C) (hTLo : MedianTimerAtLeast 1 C)
    (hTHi : IsTimerBoundedConfig T_timer C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (T_timer * n * (n - 1))) :=
  Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocol n trank Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _
    (generic_PEM_expected_timer_drain_poly_strong
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax_pos T_timer C hC hMAC hTLo hTHi)
    (by omega)

theorem generic_PEM_expected_reset_trigger_v2_strong
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (_hWrong : 0 < wrongAnswerCount C)
    (hTimer0 : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
      (C μ).1.timer = 0) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D) ≤
      ((n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocol n trank Rmax Emax Dmax hn0
  set Goal := fun D : Config (AgentState n) Opinion n =>
    IsConsensusConfig D ∨ StrongResetSeed Rmax D
  set Inv := fun D : Config (AgentState n) Opinion n =>
    InSswap D ∧ MedianAnswerCorrect D ∧
      (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n → (D μ).1.timer = 0)
  refine (Probability.expectedHittingTime_le_inv_of_local_one_lower_bound_until_goal
    P (by omega) C Goal Inv ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ?_ ?_ ?_).trans
    (by rw [inv_inv])
  · exact ⟨hSswap, hMedCorrect, hTimer0⟩
  · intro D ⟨hS, hM, hT⟩ _hGoalD i j
    by_cases hS' : InSswap (D.step P i j)
    · have hM' :=
        generic_step_median_answer_of_InSswap_both
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn0 hn4 hS hS' hM
      left
      refine ⟨hS', hM', ?_⟩
      intro μ hμ
      have hrank : (D.step P i j μ).1.rank = (D μ).1.rank :=
        generic_step_rank_preserved_of_InSswap
          (trank := trank) (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS μ
      have hμ_pre : (D μ).1.rank.val + 1 = ceilHalf n := by
        rwa [← show (D.step P i j μ).1.rank.val = (D μ).1.rank.val from
          congrArg Fin.val hrank]
      have h0 := hT μ hμ_pre
      have hle : (D.step P i j μ).1.timer ≤ (D μ).1.timer :=
        generic_step_timer_le_of_InSswap
          (trank := trank) (Rmax := Rmax) (Emax := Emax)
          (Dmax := Dmax) hn0 hS (i := i) (j := j) μ
      omega
    · exact Or.inr (Or.inr
        (generic_crs_of_InSswap_break_with_MedC_strong
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax_pos hS hM hS'))
  · intro D ⟨hS, hM, hT⟩ hGoalD
    have hNotCons : ¬ IsConsensusConfig D := fun h => hGoalD (Or.inl h)
    have hWrongExists : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D := by
      by_contra h
      push Not at h
      exact hNotCons ⟨hS.allSettled, hS.toInSrank.ranks_inj, hS.input_rank, h⟩
    obtain ⟨μ, hμ_med⟩ := hS.toInSrank.exists_median (by omega : 0 < n)
    have hμ_correct : (D μ).1.answer = majorityAnswer D := hM μ hμ_med
    have hμ_timer : (D μ).1.timer = 0 := hT μ hμ_med
    by_cases hNonUpper : ∃ v : Fin n, (D v).1.answer ≠ majorityAnswer D ∧
        (D v).1.rank.val + 1 ≠ n / 2 + 1
    · obtain ⟨v, hv_wrong, hv_no_upper⟩ := hNonUpper
      have hμv : μ ≠ v := fun h => by
        subst h
        exact hv_wrong hμ_correct
      apply Probability.ProbHitWithin_one_lower_bound_of_step P (by omega) D Goal
        (fun h => hGoalD h) hμv
      let Pc := PEMProtocolCoupled n Rmax Emax Dmax hn0
      have hSeedCoupled : StrongResetSeed Rmax (D.step Pc μ v) := by
        simpa [Pc] using
          step_timer_zero_median_wrong_nonupper_creates_StrongResetSeed
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax_pos hS hμv hμ_med hμ_timer hμ_correct
            hv_wrong hv_no_upper
      have hEqStep : D.step P μ v = D.step Pc μ v := by
        simpa [P, Pc] using
          generic_step_eq_coupled_of_InSrank
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn0 hS.toInSrank μ v
      exact Or.inr (by rw [hEqStep]; exact hSeedCoupled)
    · push Not at hNonUpper
      obtain ⟨v, hv_wrong⟩ := hWrongExists
      have hμv : μ ≠ v := fun h => by
        subst h
        exact hv_wrong hμ_correct
      apply Probability.ProbHitWithin_one_lower_bound_of_step P (by omega) D Goal
        (fun h => hGoalD h) hμv
      have hv_upper : (D v).1.rank.val + 1 = n / 2 + 1 :=
        hNonUpper v hv_wrong
      have hpar : n % 2 = 0 := by
        by_contra h
        push Not at h
        have hceil : ceilHalf n = n / 2 + 1 := by
          unfold ceilHalf
          omega
        apply hμv
        apply (hS.toInSrank.ranks_inj (Fin.ext ?_)).symm
        show (D v).1.rank.val = (D μ).1.rank.val
        have h1 : (D v).1.rank.val + 1 = (D μ).1.rank.val + 1 := by
          rw [hv_upper, hμ_med, hceil]
        omega
      left
      have hceil : ceilHalf n = n / 2 := by
        unfold ceilHalf
        omega
      have hμ_lower : (D μ).1.rank.val + 1 = n / 2 := by
        rw [← hceil]
        exact hμ_med
      have hsμ : (D μ).1.role = .Settled := hS.allSettled μ
      have hsv : (D v).1.role = .Settled := hS.allSettled v
      have h_maj : majorityAnswer (D.step P μ v) = majorityAnswer D := by
        simpa [P, PEMProtocol] using
          majorityAnswer_step_eq (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D μ v
      by_cases hxeq : (D μ).2 = (D v).2
      · have hSwap' : InSswap (D.step P μ v) :=
          step_at_median_pair_even_preserves_InSswap
            (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hS hμv hpar hμ_lower hv_upper hxeq hn4
        have hC'_eq := step_at_median_pair_even_agreed_inputs
            (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hμv hsμ hsv hpar hμ_lower hv_upper hxeq hn4
        have h_sum := nAOf_add_nBOf D
        have hμ_rank : (D μ).1.rank.val = n / 2 - 1 := by omega
        have hv_rank : (D v).1.rank.val = n / 2 := by omega
        have hne : nAOf D ≠ nBOf D := by
          rcases hx : (D μ).2 with _ | _
          · have hxv : (D v).2 = Opinion.A := by
              rw [← hxeq]
              exact hx
            have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxv
            intro h
            omega
          · have hxv : (D v).2 = Opinion.B := by
              rw [← hxeq]
              exact hx
            have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
              intro hh
              have := (hS.input_rank μ).mpr hh
              rw [hx] at this
              cases this
            have h2 : ¬ ((D v).1.rank.val < nAOf D) := by
              intro h
              have := (hS.input_rank v).mpr h
              rw [hxv] at this
              cases this
            intro h
            omega
        have h_μ_eq_maj : opinionToAnswer (D μ).2 = majorityAnswer D :=
          opinionToAnswer_lower_median_eq_majorityAnswer_even hS hμ_lower hpar hne
        refine ⟨hSwap'.allSettled, hSwap'.ranks_inj, hSwap'.input_rank, ?_⟩
        intro w
        rw [h_maj]
        have h_step_w : D.step P μ v w = (
            fun w => if w = μ then ({(D μ).1 with answer := opinionToAnswer (D μ).2}, (D μ).2)
                     else if w = v then ({(D v).1 with answer := opinionToAnswer (D μ).2}, (D v).2)
                     else D w) w := by
          rw [hC'_eq]
        by_cases hwμ : w = μ
        · subst hwμ
          rw [h_step_w]
          simp [h_μ_eq_maj]
        · by_cases hwv : w = v
          · subst hwv
            rw [h_step_w]
            simp [hwμ, h_μ_eq_maj]
          · rw [h_step_w]
            simp [hwμ, hwv]
            by_cases hw_ans : (D w).1.answer = majorityAnswer D
            · exact hw_ans
            · exfalso
              apply hwv
              apply hS.toInSrank.ranks_inj
              exact Fin.ext (Nat.add_right_cancel ((hNonUpper w hw_ans).trans hv_upper.symm))
      · have h_no_swap_disagree : ¬ ((D μ).2 = Opinion.B ∧ (D v).2 = Opinion.A) := by
          intro ⟨hxμB, hxvA⟩
          have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
            intro h
            have := (hS.input_rank μ).mpr h
            rw [hxμB] at this
            cases this
          have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxvA
          have h_sum := nAOf_add_nBOf D
          omega
        have h_step := step_at_median_pair_even_disagreed_inputs
            (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            rankDeltaOSSR_satisfies_fix hμv hsμ hsv hpar hμ_lower hv_upper hxeq
            h_no_swap_disagree hn4
        obtain ⟨h_μ_post, h_v_post, h_others_post, h_inputs_post⟩ := h_step
        have hTie : nAOf D = nBOf D := by
          have h_sum := nAOf_add_nBOf D
          rcases hxμ : (D μ).2 with _ | _
          · have hxvB : (D v).2 = Opinion.B := by
              cases hxv : (D v).2 with
              | A => exfalso; apply hxeq; rw [hxμ, hxv]
              | B => rfl
            have h1 : (D μ).1.rank.val < nAOf D := (hS.input_rank μ).mp hxμ
            have h2 : ¬ ((D v).1.rank.val < nAOf D) := by
              intro h
              have := (hS.input_rank v).mpr h
              rw [hxvB] at this
              cases this
            omega
          · have hxvA : (D v).2 = Opinion.A := by
              cases hxv : (D v).2 with
              | A => rfl
              | B => exfalso; apply hxeq; rw [hxμ, hxv]
            have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
              intro h
              have := (hS.input_rank μ).mpr h
              rw [hxμ] at this
              cases this
            have h2 : (D v).1.rank.val < nAOf D := (hS.input_rank v).mp hxvA
            omega
        have hMaj_outT : majorityAnswer D = .outT := majorityAnswer_eq_outT_of_tie hTie
        constructor
        · intro w
          by_cases hwμ : w = μ
          · rw [hwμ, h_μ_post]
            exact hsμ
          · by_cases hwv : w = v
            · rw [hwv, h_v_post]
              exact hsv
            · rw [show (D.step P μ v w).1 = (D w).1 from
                congrArg Prod.fst (h_others_post w hwμ hwv)]
              exact hS.allSettled w
        · intro w1 w2 heq
          have h_rank_w : ∀ w, (D.step P μ v w).1.rank = (D w).1.rank := by
            intro w
            by_cases hwμ : w = μ
            · rw [hwμ, h_μ_post]
            · by_cases hwv : w = v
              · rw [hwv, h_v_post]
              · rw [show (D.step P μ v w).1 = (D w).1 from
                  congrArg Prod.fst (h_others_post w hwμ hwv)]
          simp only [h_rank_w] at heq
          exact hS.toInSrank.ranks_inj heq
        · intro w
          have h_nA : nAOf (D.step P μ v) = nAOf D := by
            unfold nAOf Config.agentsWithInput Config.inputOf
            congr 1
            ext w'
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨hm, hh⟩ => ⟨hm, by rw [h_inputs_post w'] at hh; exact hh⟩,
                    fun ⟨hm, hh⟩ => ⟨hm, by rw [h_inputs_post w']; exact hh⟩⟩
          have h_rank_w : (D.step P μ v w).1.rank = (D w).1.rank := by
            by_cases hwμ : w = μ
            · rw [hwμ, h_μ_post]
            · by_cases hwv : w = v
              · rw [hwv, h_v_post]
              · rw [show (D.step P μ v w).1 = (D w).1 from
                  congrArg Prod.fst (h_others_post w hwμ hwv)]
          rw [h_inputs_post w, h_rank_w, h_nA]
          exact hS.input_rank w
        · intro w
          rw [h_maj, hMaj_outT]
          by_cases hwμ : w = μ
          · rw [hwμ]
            show (D.step P μ v μ).1.answer = .outT
            rw [h_μ_post]
          · by_cases hwv : w = v
            · rw [hwv]
              show (D.step P μ v v).1.answer = .outT
              rw [h_v_post]
            · rw [show (D.step P μ v w).1 = (D w).1 from
                congrArg Prod.fst (h_others_post w hwμ hwv)]
              by_cases hw_ans : (D w).1.answer = majorityAnswer D
              · rw [hw_ans, hMaj_outT]
              · exfalso
                apply hwv
                apply hS.toInSrank.ranks_inj
                exact Fin.ext (Nat.add_right_cancel ((hNonUpper w hw_ans).trans hv_upper.symm))

theorem generic_MAClive_to_consensus_or_crs_strong
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hSswap : InSswap C)
    (hMedCorrect : MedianAnswerCorrect C)
    (hTimerLo : MedianTimerAtLeast 1 C)
    (hTimerHi : IsTimerBoundedConfig T_timer C) :
    Probability.expectedHittingTime
      (PEMProtocol n trank Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D) ≤
      ((T_timer * n * (n - 1) + n * (n - 1) : ℕ) : ENNReal) := by
  classical
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  have hMid : Probability.expectedHittingTime P (by omega : 2 ≤ n) C
      (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) ≤
      ((T_timer * n * (n - 1) : ℕ) : ENNReal) :=
    generic_timer_drain_to_zero_productive_strong
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax_pos T_timer C hSswap hMedCorrect hTimerLo hTimerHi
  have hGoal : ∀ D : Config (AgentState n) Opinion n,
      (IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) →
      Probability.expectedHittingTime P (by omega : 2 ≤ n) D
        (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D) ≤
        ((n * (n - 1) : ℕ) : ENNReal) := by
    intro D hMidD
    rcases hMidD with hc | hcrs | ⟨hSD, hMD, hmax0⟩
    · exact le_of_eq_of_le
        (Probability.expectedHittingTime_eq_zero_of_goal P (by omega : 2 ≤ n) D _ (Or.inl hc))
        zero_le
    · exact le_of_eq_of_le
        (Probability.expectedHittingTime_eq_zero_of_goal P (by omega : 2 ≤ n) D _ (Or.inr hcrs))
        zero_le
    · have hTimer0 : ∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
          (D μ).1.timer = 0 := by
        intro μ hμ
        have hle : (if (D μ).1.rank.val + 1 = ceilHalf n then (D μ).1.timer else 0)
            ≤ maxMedianTimer D := by
          unfold maxMedianTimer
          exact Finset.le_sup
            (f := fun μ => if (D μ).1.rank.val + 1 = ceilHalf n then (D μ).1.timer else 0)
            (Finset.mem_univ μ)
        rw [hmax0, if_pos hμ] at hle
        omega
      by_cases hw : 0 < wrongAnswerCount D
      · exact
          generic_PEM_expected_reset_trigger_v2_strong
            (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax_pos D hSD hMD hw hTimer0
      · have hw0 : wrongAnswerCount D = 0 := by omega
        exact le_of_eq_of_le
          (Probability.expectedHittingTime_eq_zero_of_goal P (by omega : 2 ≤ n) D _
            (Or.inl (isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hSD hw0)))
          zero_le
  have hMidGoal : ∀ D : Config (AgentState n) Opinion n,
      (IsConsensusConfig D ∨ StrongResetSeed Rmax D) →
      (IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
        (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0)) := by
    intro D hD
    rcases hD with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hadd := Probability.expectedHittingTime_add_le P (by omega : 2 ≤ n) C
    (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
      (InSswap D ∧ MedianAnswerCorrect D ∧ maxMedianTimer D = 0))
    (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D)
    ((T_timer * n * (n - 1) : ℕ) : ENNReal) ((n * (n - 1) : ℕ) : ENNReal)
    hMid hGoal hMidGoal
  refine hadd.trans ?_
  rw [← Nat.cast_add]

theorem generic_MAClive_to_consensus_or_crs_window_strong
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hC : InSswap C) (hMAC : MedianAnswerCorrect C)
    (hTLo : MedianTimerAtLeast 1 C)
    (hTHi : IsTimerBoundedConfig T_timer C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D)
        (2 * (T_timer * n * (n - 1) + n * (n - 1))) := by
  have hM :=
    generic_MAClive_to_consensus_or_crs_strong
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax_pos T_timer C hC hMAC hTLo hTHi
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocol n trank Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _
    hM
    (by omega)

theorem generic_swap_live_to_cons_or_strong_or_break
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax_pos : 0 < Rmax)
    (T_timer : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer
          (D.step (PEMProtocol n trank Rmax Emax Dmax hn0) i j))
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hT : MedianTimerAtLeast 1 C) (hB : IsTimerBoundedConfig T_timer C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocol n trank Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (n * (n - 1)) + 2 * (T_timer * n * (n - 1))) := by
  have hn2 : (2 : ℕ) ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  set Inv : Config (AgentState n) Opinion n → Prop :=
    fun D => IsTimerBoundedConfig T_timer D with hInvDef
  set Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => IsConsensusConfig D ∨ StrongResetSeed Rmax D ∨
      ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
    with hGoalDef
  have hInvStep : ∀ D, Inv D → ∀ i j, Inv (D.step P i j) :=
    fun D hD i j => by
      simpa [P, Inv] using hTimerStep D hD i j
  by_cases hMAC : MedianAnswerCorrect C
  · refine le_trans ?_ (Probability.ProbHitWithin_mono_time P hn2 C Goal
      (m := 2 * (T_timer * n * (n - 1))) (by omega))
    refine le_trans ?_ (generic_timer_drain_window_strong
      (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax_pos T_timer C hC hMAC hT hB)
    rw [ENNReal.inv_le_inv]
    norm_num
  · set dG : Config (AgentState n) Opinion n → Prop :=
      fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨
        ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
      with hdGDef
    set Mid : Config (AgentState n) Opinion n → Prop :=
      fun D => dG D ∧ Inv D with hMidDef
    have hMid : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Mid (2 * (n * (n - 1))) := by
      rw [hMidDef,
        Probability.ProbHitWithin_eq_and_inv_of_invariant P hn2 C dG Inv hB hInvStep]
      exact
        generic_decision_window
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 C hC hT hMAC
    have hGoal : ∀ C' : Config (AgentState n) Opinion n, Mid C' →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) := by
      intro C' hC'
      obtain ⟨hdg, hinv⟩ := hC'
      by_cases hlive : InSswap C' ∧ MedianTimerAtLeast 1 C'
      · have hmac : MedianAnswerCorrect C' := by
          rcases hdg with ⟨_, hm⟩ | hexit
          · exact hm
          · exact absurd hlive hexit
        exact generic_timer_drain_window_strong
          (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax_pos T_timer C' hlive.1 hmac hlive.2 hinv
      · have hgC' : Goal C' := Or.inr (Or.inr hlive)
        have h1 : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) := by
          calc (1 : ENNReal) = Probability.probReached P hn2 C' Goal 0 :=
                (Probability.probReached_zero_of_goal P hn2 C' Goal hgC').symm
            _ ≤ Probability.ProbHitWithin P hn2 C' Goal 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C' Goal 0
            _ ≤ Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) :=
                Probability.ProbHitWithin_mono_time P hn2 C' Goal (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) h1
    have hchain := Probability.ProbHitWithin_add_ge_mul P hn2 C Mid Goal
      (2 * (n * (n - 1))) (2 * (T_timer * n * (n - 1)))
      ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹) hMid hGoal
    have harith : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    rwa [harith] at hchain

/-- Strong-endpoint version of the faithful [12] reset-completion contract.

The input is the exact seed produced by the reset transition: one resetting
leader at fuel `Rmax`, and every resetting agent already carries the correct
majority answer.  It deliberately omits the old fuel-dominance clause. -/
structure CRSReset12FaithfulStrong {n Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (d : ℕ) (p_reset : ENNReal) (C_reset K_reset : ℕ) : Prop where
  wakeBudget_le_Dmax : d ≤ Dmax
  resetProb_pos : 0 < p_reset
  resetProb_le_one : p_reset ≤ 1
  resetConstant_pos : 0 < C_reset
  resetWindow_quadratic : K_reset ≤ C_reset * n * n
  freshSeedReach :
    ∀ (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n),
      WellFormed 1 Rmax Emax Dmax C →
      StrongResetSeed Rmax C →
        p_reset ≤
          Probability.ProbHitWithin
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
            (ResetSeedWithWakeBudget d (majorityAnswer C)) K_reset

/-- Compose a strong reset seed with the proven no-wake answer-epidemic
bridge. -/
theorem faithful_strong_reset_to_phiGoal
    {n Rmax Emax Dmax K_reset K_bridge C_reset d : ℕ}
    (hn : 0 < n) (hn2 : 2 ≤ n) (hd_pos : 0 < d)
    {p_reset pE : ENNReal}
    (h12reset :
      CRSReset12FaithfulStrong (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn d p_reset C_reset K_reset)
    (epidemicFast :
      StandardEpidemicFastHypothesisPEM
        n Rmax Emax Dmax K_bridge hn hn2 pE)
    (hTail : drainNoWakeTail n K_bridge d ≤ pE / 2) :
    ∀ C : Config (AgentState n) Opinion n,
      WellFormed 1 Rmax Emax Dmax C →
      StrongResetSeed Rmax C →
        p_reset * (pE / 2) ≤
          Probability.ProbHitWithin
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
            (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧
              AllAgentsResetting D)
            (K_reset + K_bridge) := by
  classical
  intro C hWF hSeed
  let P : Protocol (AgentState n) Opinion Output :=
    PEMProtocol n 1 Rmax Emax Dmax hn
  let Mid : Config (AgentState n) Opinion n → Prop :=
    ResetSeedWithWakeBudget d (majorityAnswer C)
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => EpidemicPhiGoal (majorityAnswer C) D ∧ AllAgentsResetting D
  have hFreshSeed :
      p_reset ≤ Probability.ProbHitWithin P hn2 C Mid K_reset := by
    simpa [P, Mid] using h12reset.freshSeedReach hn2 C hWF hSeed
  have hBridge :
      ∀ D : Config (AgentState n) Opinion n, Mid D →
        pE / 2 ≤ Probability.ProbHitWithin P hn2 D Goal K_bridge := by
    intro D hD
    exact
      answer_epidemic_bridge_from_fresh_resetting
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (K := K_bridge) (d := d) (C₀ := D) (m := majorityAnswer C)
        (pE := pE) hn hn2 hd_pos h12reset.wakeBudget_le_Dmax
        hD.2.1 hD.2.2 hD.1 hTail epidemicFast
  exact
    Probability.ProbHitWithin_add_ge_mul P hn2 C Mid Goal
      K_reset K_bridge p_reset (pE / 2) hFreshSeed hBridge

/-- Strong reset-completion contract for the generic renewal keystone. -/
structure CRSResetCompletion12StrongGeneric {n trank Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (p_reset : ENNReal) (C_reset K_reset : ℕ) : Prop where
  resetProb_pos : 0 < p_reset
  resetProb_le_one : p_reset ≤ 1
  resetConstant_pos : 0 < C_reset
  resetWindow_quadratic : K_reset ≤ C_reset * n * n
  resetReach :
    ∀ (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n),
      WellFormed trank Rmax Emax Dmax C →
      StrongResetSeed Rmax C →
        p_reset ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax hn) hn2 C
            (EpidemicPhiGoal (majorityAnswer C)) K_reset

/-- Convert the faithful strong reset citation plus the proven answer-epidemic
bridge into the strong generic reset-completion contract. -/
theorem crsReset12FaithfulStrong_to_generic
    {n Rmax Emax Dmax K_reset K_bridge C_reset C_bridge d : ℕ}
    (hn : 0 < n) (hn2 : 2 ≤ n) (hd_pos : 0 < d)
    {p_reset pE : ENNReal}
    (h12reset :
      CRSReset12FaithfulStrong (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) hn d p_reset C_reset K_reset)
    (epidemicFast :
      StandardEpidemicFastHypothesisPEM
        n Rmax Emax Dmax K_bridge hn hn2 pE)
    (hTail : drainNoWakeTail n K_bridge d ≤ pE / 2)
    (hpE_pos : 0 < pE) (hpE_le_one : pE ≤ 1)
    (hBridgeWindow : K_bridge ≤ C_bridge * n * n) :
    CRSResetCompletion12StrongGeneric (n := n) (trank := 1) (Rmax := Rmax)
      (Emax := Emax) (Dmax := Dmax) hn
      (p_reset * (pE / 2)) (C_reset + C_bridge)
      (K_reset + K_bridge) where
  resetProb_pos := by
    have hhalf_pos : 0 < pE / 2 :=
      ENNReal.half_pos (ne_of_gt hpE_pos)
    exact ENNReal.mul_pos (ne_of_gt h12reset.resetProb_pos)
      (ne_of_gt hhalf_pos)
  resetProb_le_one := by
    have hsplit : pE / 2 + pE / 2 = pE := by
      simp
    have hhalf_le_pE : pE / 2 ≤ pE := by
      calc
        pE / 2 ≤ pE / 2 + pE / 2 :=
          (le_self_add : pE / 2 ≤ pE / 2 + pE / 2)
        _ = pE := hsplit
    have hhalf_le_one : pE / 2 ≤ 1 := hhalf_le_pE.trans hpE_le_one
    have hmul :
        p_reset * (pE / 2) ≤ (1 : ENNReal) * 1 :=
      mul_le_mul' h12reset.resetProb_le_one hhalf_le_one
    simpa using hmul
  resetConstant_pos := by
    exact Nat.add_pos_left h12reset.resetConstant_pos C_bridge
  resetWindow_quadratic := by
    calc
      K_reset + K_bridge ≤
          C_reset * n * n + C_bridge * n * n :=
        Nat.add_le_add h12reset.resetWindow_quadratic hBridgeWindow
      _ = (C_reset + C_bridge) * n * n := by
        ring
  resetReach := by
    intro hn2' C hWF hSeed
    have epidemicFast' :
        StandardEpidemicFastHypothesisPEM
          n Rmax Emax Dmax K_bridge hn hn2' pE := by
      have hhn2 : hn2 = hn2' := Subsingleton.elim hn2 hn2'
      cases hhn2
      exact fun {m} {D} hRegion => epidemicFast hRegion
    have hFaithful :
        p_reset * (pE / 2) ≤
          Probability.ProbHitWithin
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2' C
            (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧
              AllAgentsResetting D)
            (K_reset + K_bridge) :=
      faithful_strong_reset_to_phiGoal
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (K_reset := K_reset) (K_bridge := K_bridge)
        (C_reset := C_reset) (d := d) hn hn2' hd_pos
        h12reset epidemicFast' hTail C hWF hSeed
    exact hFaithful.trans
      (Probability.ProbHitWithin_mono_goal
        (PEMProtocol n 1 Rmax Emax Dmax hn) hn2' C
        (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧
          AllAgentsResetting D)
        (EpidemicPhiGoal (majorityAnswer C))
        (fun D hD => hD.1) (K_reset + K_bridge))

/-- Strong CRS-to-consensus wrapper retaining the product probability. -/
theorem CRSStrong_to_consensus_faithful_product_generic
    {n trank Rmax Emax Dmax K_reset T_rank C_reset : ℕ}
    (hn4 : 4 ≤ n)
    (p_reset rankProb : ENNReal)
    (h12resetCompletion :
      CRSResetCompletion12StrongGeneric (n := n) (trank := trank)
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (by omega : 0 < n) p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
        WellFormed trank Rmax Emax Dmax D →
        majorityAnswer D = m →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      WellFormed trank Rmax Emax Dmax C →
      StrongResetSeed Rmax C →
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          Probability.ProbHitWithin
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  classical
  intro C hWF hSeed
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  let MajInv : Config (AgentState n) Opinion n → Prop :=
    fun D => majorityAnswer D = majorityAnswer C
  let ChainInv : Config (AgentState n) Opinion n → Prop :=
    fun D => WellFormed trank Rmax Emax Dmax D ∧ MajInv D
  have hWFStep : ∀ D : Config (AgentState n) Opinion n,
      WellFormed trank Rmax Emax Dmax D →
      ∀ i j : Fin n, WellFormed trank Rmax Emax Dmax (D.step P i j) := by
    intro D hD i j
    simpa [P] using
      (WellFormed_step (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) hn0 D hD i j)
  have hMajInvStep : ∀ D : Config (AgentState n) Opinion n, MajInv D →
      ∀ i j : Fin n, MajInv (D.step P i j) := by
    intro D hD i j
    calc
      majorityAnswer (D.step P i j) = majorityAnswer D := by
        simpa [P, PEMProtocol] using
          (majorityAnswer_step_eq
            (trank := trank) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j)
      _ = majorityAnswer C := hD
  have hChainInvStep : ∀ D : Config (AgentState n) Opinion n, ChainInv D →
      ∀ i j : Fin n, ChainInv (D.step P i j) := by
    intro D hD i j
    exact ⟨hWFStep D hD.1 i j, hMajInvStep D hD.2 i j⟩
  have hReset :
      p_reset ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧ ChainInv D)
          K_reset := by
    have hResetRaw :
        p_reset ≤
          Probability.ProbHitWithin P hn2 C
            (EpidemicPhiGoal (majorityAnswer C)) K_reset := by
      simpa [P] using h12resetCompletion.resetReach hn2 C hWF hSeed
    rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
      P hn2 C (EpidemicPhiGoal (majorityAnswer C)) ChainInv ⟨hWF, rfl⟩
      hChainInvStep K_reset]
    exact hResetRaw
  have hRankToSilence :
      ∀ D : Config (AgentState n) Opinion n,
        (EpidemicPhiGoal (majorityAnswer C) D ∧ ChainInv D) →
          rankProb ≤ Probability.ProbHitWithin P hn2 D OW_silenceEndpoint T_rank := by
    intro D hD
    have hRankRaw :
        rankProb ≤
          Probability.ProbHitWithin P hn2 D
            (OW_rankedEpidemicEndpoint (majorityAnswer C)) T_rank := by
      simpa [P] using h12rank (majorityAnswer C) D hD.1 hD.2.1 hD.2.2
    exact hRankRaw.trans
      (Probability.ProbHitWithin_mono_goal P hn2 D
        (OW_rankedEpidemicEndpoint (majorityAnswer C)) OW_silenceEndpoint
        (fun E hE => OW_silenceEndpoint_of_rankedEpidemicEndpoint hE)
        T_rank)
  have hStrong :
      p_reset * rankProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + T_rank) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C
      (fun D => EpidemicPhiGoal (majorityAnswer C) D ∧ ChainInv D)
      OW_silenceEndpoint K_reset T_rank p_reset rankProb
      hReset hRankToSilence
  have hWeak :
      p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤ p_reset * rankProb := by
    have hmul :
        p_reset * ((2 : ENNReal)⁻¹) ≤ p_reset * (1 : ENNReal) := by
      exact mul_le_mul' le_rfl (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1)
    have hmulRank :
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          p_reset * (1 : ENNReal) * rankProb := by
      exact mul_le_mul' hmul le_rfl
    simpa [mul_assoc] using hmulRank
  have hSilence :
      p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + T_rank) :=
    hWeak.trans hStrong
  have hTime :
      Probability.ProbHitWithin P hn2 C OW_silenceEndpoint (K_reset + T_rank) ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + OW_answerEpidemicWindow n + T_rank) :=
    Probability.ProbHitWithin_mono_time P hn2 C OW_silenceEndpoint (by omega)
  exact (hSilence.trans hTime).trans
    (Probability.ProbHitWithin_mono_goal P hn2 C
      OW_silenceEndpoint IsConsensusConfig
      (fun D hD => isConsensusConfig_of_InSswap_phiCount_zero hD.1 hD.2.1 hD.2.2)
      (K_reset + OW_answerEpidemicWindow n + T_rank))

theorem PEM_expectedParallelTime_optimal_generic_strong
    {n trank Rmax Emax Dmax : ℕ}
    [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n) (hRmax_pos : 0 < Rmax)
    (C_rank T_timer K_reset T_rank T_rerank : ℕ)
    (p_reset : ENNReal) (C_reset : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer
          (D.step (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n)) i j))
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed trank Rmax Emax Dmax C →
          IsTimerBoundedConfig T_timer C →
          Probability.expectedHittingTime
            (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => (InSrank D ∧ MedianTimerAtLeast 35 D ∧
              WellFormed trank Rmax Emax Dmax D ∧
              IsTimerBoundedConfig T_timer D) ∨ IsConsensusConfig D) ≤
            ((C_rank * n * n : ℕ) : ENNReal))
    (h12resetCompletion :
      CRSResetCompletion12StrongGeneric (n := n) (trank := trank) (Rmax := Rmax)
        (Emax := Emax) (Dmax := Dmax) (by omega : 0 < n)
        p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
        WellFormed trank Rmax Emax Dmax D →
        majorityAnswer D = m →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed trank Rmax Emax Dmax C →
        IsTimerBoundedConfig T_timer C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => (InSswap D ∧ MedianTimerAtLeast 35 D) ∨
                IsConsensusConfig D) T_rerank) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      WellFormed trank Rmax Emax Dmax C₀ →
      IsTimerBoundedConfig T_timer C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocol n trank Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((OW_globalWindow n C_rank T_timer K_reset T_rank T_rerank : ℕ) : ENNReal) *
          (p_reset * ((128 : ENNReal)⁻¹))⁻¹ / n) := by
  classical
  intro C₀ hWF₀ hTimerT₀
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocol n trank Rmax Emax Dmax hn0 with hP
  let Inv : Config (AgentState n) Opinion n → Prop :=
    fun C => WellFormed trank Rmax Emax Dmax C ∧
      IsTimerBoundedConfig T_timer C
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        WellFormed trank Rmax Emax Dmax C ∧
        IsTimerBoundedConfig T_timer C
  let RankOrConsensus : Config (AgentState n) Opinion n → Prop :=
    fun C => RankTarget C ∨ IsConsensusConfig C
  let Live35 : Config (AgentState n) Opinion n → Prop :=
    fun C => InSswap C ∧ MedianTimerAtLeast 35 C
  let LiveOrConsensus : Config (AgentState n) Opinion n → Prop :=
    fun C => Live35 C ∨ IsConsensusConfig C
  let Live35Target : Config (AgentState n) Opinion n → Prop :=
    fun C => Live35 C ∧ Inv C
  let LiveOrConsensusTarget : Config (AgentState n) Opinion n → Prop :=
    fun C => LiveOrConsensus C ∧ Inv C
  let DecisionTarget : Config (AgentState n) Opinion n → Prop :=
    (DecisionProductiveTargetStrong Rmax : Config (AgentState n) Opinion n → Prop)
  let DecisionMid : Config (AgentState n) Opinion n → Prop :=
    fun C => DecisionTarget C ∧ Inv C
  let ConsOrCRS : Config (AgentState n) Opinion n → Prop :=
    fun C => IsConsensusConfig C ∨ StrongResetSeed Rmax C
  let ConsOrCRSMid : Config (AgentState n) Opinion n → Prop :=
    fun C => ConsOrCRS C ∧ Inv C
  let KLive : ℕ := OW_liveConsensusWindow n T_timer K_reset T_rank
  let K : ℕ := OW_globalWindow n C_rank T_timer K_reset T_rank T_rerank
  have hKpos : 0 < K := by
    have hDecisionPos : 0 < decisionWindow n := by
      dsimp [decisionWindow]
      exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    have hLivePos : 0 < OW_liveConsensusWindow n T_timer K_reset T_rank := by
      dsimp [OW_liveConsensusWindow]
      omega
    dsimp [K, OW_globalWindow]
    omega
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : p_reset * ((128 : ENNReal)⁻¹) ≤ 1 := by
    exact (mul_le_mul' h12resetCompletion.resetProb_le_one
      (by norm_num : ((128 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    constructor
    · simpa [P, Inv] using
        (WellFormed_step (n := n) (trank := trank) (Rmax := Rmax)
          (Emax := Emax) (Dmax := Dmax) hn0 C hC.1 i j)
    · simpa [P, Inv] using hTimerStep C hC.2 i j
  have hConsOrCRSToConsensus :
      ∀ C : Config (AgentState n) Opinion n, ConsOrCRSMid C →
        p_reset * ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    intro C hC
    rcases hC with ⟨hEvent, hInvC⟩
    rcases hEvent with hCons | hSeed
    · have hOne : (1 : ENNReal) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        calc
          (1 : ENNReal) = Probability.probReached P hn2 C IsConsensusConfig 0 := by
              exact (Probability.probReached_zero_of_goal P hn2 C IsConsensusConfig hCons).symm
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig 0 :=
              Probability.probReached_le_ProbHitWithin P hn2 C IsConsensusConfig 0
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig
                (K_reset + OW_answerEpidemicWindow n + T_rank) :=
              Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig (Nat.zero_le _)
      have hp4_le_one : p_reset * ((4 : ENNReal)⁻¹) ≤ 1 := by
        exact (mul_le_mul' h12resetCompletion.resetProb_le_one
          (by norm_num : ((4 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
      exact hp4_le_one.trans hOne
    · have hCRS :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C IsConsensusConfig
              (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        simpa [P] using
          (CRSStrong_to_consensus_faithful_product_generic
            (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 p_reset ((2 : ENNReal)⁻¹)
            h12resetCompletion h12rank C hInvC.1 hSeed)
      have hprod :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) =
            p_reset * ((4 : ENNReal)⁻¹) := by
        have hhalf :
            ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
          rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          norm_num
        rw [mul_assoc, hhalf]
      simpa [hprod] using hCRS
  have hDecisionToConsOrCRS :
      ∀ C : Config (AgentState n) Opinion n, DecisionMid C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (OW_macLiveWindow n T_timer) := by
    intro C hC
    rcases hC with ⟨hDecision, hInvC⟩
    rcases hDecision with hMAC | hRest
    · have hBase :
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRS
              (OW_macLiveWindow n T_timer) := by
        simpa [P, ConsOrCRS, OW_macLiveWindow] using
          (generic_MAClive_to_consensus_or_crs_window_strong
            (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax_pos T_timer C
            hMAC.1 hMAC.2.1 hMAC.2.2 hInvC.2)
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C ConsOrCRS Inv hInvC hInvStep (OW_macLiveWindow n T_timer)]
      exact hBase
    · rcases hRest with hCons | hSeed
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inl hCons, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inr hSeed, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
  have hLiveToConsensus :
      ∀ C : Config (AgentState n) Opinion n, Live35Target C →
        p_reset * ((32 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig KLive := by
    intro C hLiveTarget
    rcases hLiveTarget with ⟨hLive, hInvC⟩
    have hDecisionBase :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionTarget (decisionWindow n) := by
      simpa [P, DecisionTarget] using
        (generic_decision_before_timer_zero_strong
          (n := n) (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 C hLive.1 hLive.2)
    have hDecision :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionMid (decisionWindow n) := by
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C DecisionTarget Inv hInvC hInvStep (decisionWindow n)]
      exact hDecisionBase
    have hAB :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (decisionWindow n + OW_macLiveWindow n T_timer) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C DecisionMid ConsOrCRSMid
        (decisionWindow n) (OW_macLiveWindow n T_timer)
        ((4 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
        hDecision hDecisionToConsOrCRS
    have hChain :
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) *
            (p_reset * ((4 : ENNReal)⁻¹)) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            ((decisionWindow n + OW_macLiveWindow n T_timer) +
              (K_reset + OW_answerEpidemicWindow n + T_rank)) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C ConsOrCRSMid IsConsensusConfig
        (decisionWindow n + OW_macLiveWindow n T_timer)
        (K_reset + OW_answerEpidemicWindow n + T_rank)
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹))
        (p_reset * ((4 : ENNReal)⁻¹))
        hAB hConsOrCRSToConsensus
    have h42 :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((8 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have h84 :
        ((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) = ((32 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have hprod :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹)) =
          p_reset * ((32 : ENNReal)⁻¹) := by
      calc
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹))
            = p_reset * (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
                ((4 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * (((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) := by rw [h42]
        _ = p_reset * ((32 : ENNReal)⁻¹) := by rw [h84]
    simpa [KLive, OW_liveConsensusWindow, hprod] using hChain
  have hwin : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      p_reset * ((128 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hInvC _hNot
    have hRankE : Probability.expectedHittingTime P hn2 C RankOrConsensus ≤
        ((C_rank * n * n : ℕ) : ENNReal) := by
      simpa [P, RankOrConsensus, RankTarget, Inv] using
        h12ranking C hInvC.1 hInvC.2
    have hRankW : 2 * (C_rank * n * n) ≤ (2 * C_rank * n * n) + 1 := by nlinarith
    have hRankPH : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C RankOrConsensus (2 * C_rank * n * n) :=
      Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
        P hn2 C RankOrConsensus hRankE hRankW
    have hLiveOrConsensusToConsensus :
        ∀ E : Config (AgentState n) Opinion n, LiveOrConsensusTarget E →
          p_reset * ((32 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 E IsConsensusConfig KLive := by
      intro E hE
      rcases hE with ⟨hEvent, hInvE⟩
      rcases hEvent with hLiveE | hConsE
      · exact hLiveToConsensus E ⟨hLiveE, hInvE⟩
      · have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 E IsConsensusConfig KLive := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 E IsConsensusConfig 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 E
                    IsConsensusConfig hConsE).symm
            _ ≤ Probability.ProbHitWithin P hn2 E IsConsensusConfig 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 E IsConsensusConfig 0
            _ ≤ Probability.ProbHitWithin P hn2 E IsConsensusConfig KLive :=
                Probability.ProbHitWithin_mono_time P hn2 E IsConsensusConfig
                  (Nat.zero_le _)
        have hp32_le_one : p_reset * ((32 : ENNReal)⁻¹) ≤ 1 := by
          exact (mul_le_mul' h12resetCompletion.resetProb_le_one
            (by norm_num : ((32 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
        exact hp32_le_one.trans hOne
    have hAfterRank :
        ∀ D : Config (AgentState n) Opinion n, RankOrConsensus D →
          p_reset * ((64 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 D IsConsensusConfig (T_rerank + KLive) := by
      intro D hD
      rcases hD with hRankD | hConsD
      · have hInvD : Inv D := hRankD.2.2
        by_cases hLive : Live35 D
        · have hGoalD : Live35Target D := ⟨hLive, hInvD⟩
          have hBase :
              p_reset * ((32 : ENNReal)⁻¹) ≤
                Probability.ProbHitWithin P hn2 D IsConsensusConfig KLive :=
            hLiveToConsensus D hGoalD
          have hBase' :
              p_reset * ((32 : ENNReal)⁻¹) ≤
                Probability.ProbHitWithin P hn2 D IsConsensusConfig
                  (T_rerank + KLive) :=
            hBase.trans
              (Probability.ProbHitWithin_mono_time P hn2 D IsConsensusConfig
                (by omega : KLive ≤ T_rerank + KLive))
          have hweak :
              p_reset * ((64 : ENNReal)⁻¹) ≤
                p_reset * ((32 : ENNReal)⁻¹) :=
            mul_le_mul' le_rfl (by norm_num : ((64 : ENNReal)⁻¹) ≤ ((32 : ENNReal)⁻¹))
          exact hweak.trans hBase'
        · have hBase :
              ((2 : ENNReal)⁻¹) ≤
                Probability.ProbHitWithin P hn2 D LiveOrConsensus T_rerank := by
            simpa [P, LiveOrConsensus, Live35] using
              h12reRank D hInvD.1 hInvD.2 hLive
          have hRerank :
              ((2 : ENNReal)⁻¹) ≤
                Probability.ProbHitWithin P hn2 D LiveOrConsensusTarget T_rerank := by
            rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
              P hn2 D LiveOrConsensus Inv hInvD hInvStep T_rerank]
            exact hBase
          have hChain :
              ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) ≤
                Probability.ProbHitWithin P hn2 D IsConsensusConfig
                  (T_rerank + KLive) :=
            Probability.ProbHitWithin_add_ge_mul P hn2 D
              LiveOrConsensusTarget IsConsensusConfig
              T_rerank KLive
              ((2 : ENNReal)⁻¹) (p_reset * ((32 : ENNReal)⁻¹))
              hRerank hLiveOrConsensusToConsensus
          have hprod :
              ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) =
                p_reset * ((64 : ENNReal)⁻¹) := by
            have h2_32 :
                ((2 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹) =
                  ((64 : ENNReal)⁻¹) := by
              rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
              norm_num
            calc
              ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹))
                  = p_reset * (((2 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹)) := by
                    ac_rfl
              _ = p_reset * ((64 : ENNReal)⁻¹) := by rw [h2_32]
          simpa [hprod] using hChain
      · have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 D IsConsensusConfig
              (T_rerank + KLive) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 D IsConsensusConfig 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 D
                    IsConsensusConfig hConsD).symm
            _ ≤ Probability.ProbHitWithin P hn2 D IsConsensusConfig 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 D IsConsensusConfig 0
            _ ≤ Probability.ProbHitWithin P hn2 D IsConsensusConfig
                  (T_rerank + KLive) :=
                Probability.ProbHitWithin_mono_time P hn2 D IsConsensusConfig
                  (Nat.zero_le _)
        have hp64_le_one : p_reset * ((64 : ENNReal)⁻¹) ≤ 1 := by
          exact (mul_le_mul' h12resetCompletion.resetProb_le_one
            (by norm_num : ((64 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
        exact hp64_le_one.trans hOne
    have hChain : ((2 : ENNReal)⁻¹) * (p_reset * ((64 : ENNReal)⁻¹)) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig
          (2 * C_rank * n * n + (T_rerank + KLive)) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C RankOrConsensus IsConsensusConfig
        (2 * C_rank * n * n) (T_rerank + KLive)
        ((2 : ENNReal)⁻¹) (p_reset * ((64 : ENNReal)⁻¹))
        hRankPH hAfterRank
    have hprod :
        ((2 : ENNReal)⁻¹) * (p_reset * ((64 : ENNReal)⁻¹)) =
          p_reset * ((128 : ENNReal)⁻¹) := by
      have h2_64 :
          ((2 : ENNReal)⁻¹) * ((64 : ENNReal)⁻¹) = ((128 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      calc
        ((2 : ENNReal)⁻¹) * (p_reset * ((64 : ENNReal)⁻¹))
            = p_reset * (((2 : ENNReal)⁻¹) * ((64 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * ((128 : ENNReal)⁻¹) := by rw [h2_64]
    simpa [K, OW_globalWindow, hprod, Nat.add_assoc, add_assoc] using hChain
  simpa [Probability.expectedParallelTimeToConsensus, P, Inv, K] using
    (Probability.expectedParallelTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K (p_reset * ((128 : ENNReal)⁻¹))
      hp_le_one ⟨hWF₀, hTimerT₀⟩ hInvStep hwin)

theorem PEM_expectedParallelTime_On_faithful_log
    {n Rmax Emax Dmax K_reset K_bridge C_reset C_bridge d : ℕ}
    [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax)
    (hd_pos : 0 < d)
    (C_rank T_rank T_rerank : ℕ)
    {p_reset pE : ENNReal}
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed 1 Rmax Emax Dmax C →
          Probability.expectedHittingTime
            (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => (InSrank D ∧ MedianTimerAtLeast 35 D ∧
              WellFormed 1 Rmax Emax Dmax D ∧
              IsTimerBoundedConfig PEM_trank1_timer D) ∨ IsConsensusConfig D) ≤
            ((C_rank * n * n : ℕ) : ENNReal))
    (h12reset :
      CRSReset12FaithfulStrong (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) d p_reset C_reset K_reset)
    (epidemicFast :
      StandardEpidemicFastHypothesisPEM
        n Rmax Emax Dmax K_bridge (by omega : 0 < n)
        (by omega : 2 ≤ n) pE)
    (hTail : drainNoWakeTail n K_bridge d ≤ pE / 2)
    (hpE_pos : 0 < pE) (hpE_le_one : pE ≤ 1)
    (hBridgeWindow : K_bridge ≤ C_bridge * n * n)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
        WellFormed 1 Rmax Emax Dmax D →
        majorityAnswer D = m →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        WellFormed 1 Rmax Emax Dmax C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => (InSswap D ∧ MedianTimerAtLeast 35 D) ∨
                IsConsensusConfig D) T_rerank) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      WellFormed 1 Rmax Emax Dmax C₀ →
        Probability.expectedParallelTimeToConsensus
          (PEMProtocol n 1 Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          (((OW_globalWindow n C_rank PEM_trank1_timer
              (K_reset + K_bridge) T_rank T_rerank : ℕ) : ENNReal) *
            ((p_reset * (pE / 2)) * ((128 : ENNReal)⁻¹))⁻¹ / n) := by
  intro C₀ hWF₀
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hRmax_pos : 0 < Rmax := by omega
  have hGeneric :=
    crsReset12FaithfulStrong_to_generic
      (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (K_reset := K_reset) (K_bridge := K_bridge)
      (C_reset := C_reset) (C_bridge := C_bridge)
      (d := d) hn0 hn2 hd_pos h12reset
      epidemicFast hTail hpE_pos hpE_le_one hBridgeWindow
  have hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig PEM_trank1_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig PEM_trank1_timer
          (D.step (PEMProtocol n 1 Rmax Emax Dmax hn0) i j) := by
    intro D hD i j
    simpa [PEM_trank1_timer] using
      (generic_timer_preservation
        (n := n) (trank := 1) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn0 (by norm_num : 7 * (1 + 4) ≤ 35) D hD i j)
  exact
    (PEM_expectedParallelTime_optimal_generic_strong
      (n := n) (trank := 1) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hRmax_pos C_rank PEM_trank1_timer (K_reset + K_bridge)
      T_rank T_rerank (p_reset * (pE / 2)) (C_reset + C_bridge)
      hTimerStep
      (fun C hWF _hT =>
        by
          simpa [PEM_trank1_timer] using h12ranking C hWF)
      hGeneric
      h12rank
      (fun C hWF _hT hNot =>
        by
          simpa [PEM_trank1_timer] using h12reRank C hWF hNot)
      C₀
      (by simpa [PEM_trank1_timer] using hWF₀)
      (by simpa [PEM_trank1_timer, WellFormed] using hWF₀.1))

end SSEM
