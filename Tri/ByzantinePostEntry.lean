/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineEntry

/-!
# Adaptive post-entry no-backsliding for Byzantine Tri

After the entry phase reaches `4x ≥ 3n`, this file proves the safety half of
the move to the strong region `x + 2z ≥ n`. Until strong entry, `y > z`.
Above the concrete lower barrier `32x > 23n`, the paper-worst one-step masses
satisfy `5 * downWeight ≤ 4 * upWeight`. Consequently `(4/5)^x` is a
supermartingale for every adaptive history while the process remains between
the lower barrier and strong entry.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B : ℕ}

/-- Concrete lower failure boundary for the post-entry phase. -/
def PostEntryFailure (s : State n B) : Prop :=
  32 * State.x s ≤ 23 * n

instance postEntryFailureDecidable (s : State n B) :
    Decidable (PostEntryFailure s) := by
  unfold PostEntryFailure
  infer_instance

/-- The post-entry phase ends successfully at the paper's strong checkpoint. -/
def PostEntryTarget (s : State n B) : Prop :=
  StrongXEntry s

instance postEntryTargetDecidable (s : State n B) :
    Decidable (PostEntryTarget s) := by
  unfold PostEntryTarget StrongXEntry
  infer_instance

/-- The physical region on which the uniform `4/5` adverse bias is proved. -/
def PostEntryLive (s : State n B) : Prop :=
  23 * n < 32 * State.x s ∧
    State.x s + 2 * State.z s < n

/-- Fixed geometric base for the post-entry safety monitor. -/
noncomputable def postEntryBase : ℝ≥0∞ :=
  (4 : ℝ≥0∞) / 5

/-- Integer lower threshold corresponding to `32x ≤ 23n`. -/
def postEntryLower (n : ℕ) : ℕ :=
  (23 * n) / 32

/-- Stop on either lower failure or successful strong entry. -/
def PostEntryStop (s : State n B) : Prop :=
  PostEntryFailure s ∨ PostEntryTarget s

instance postEntryStopDecidable (s : State n B) :
    Decidable (PostEntryStop s) := by
  unfold PostEntryStop
  infer_instance

@[simp] theorem postEntryBase_le_one : postEntryBase ≤ 1 := by
  unfold postEntryBase
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
  norm_num

@[simp] theorem postEntryBase_ne_zero : postEntryBase ≠ 0 := by
  unfold postEntryBase
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by norm_num, by norm_num⟩

@[simp] theorem postEntryBase_ne_top : postEntryBase ≠ ⊤ := by
  unfold postEntryBase
  finiteness

/-- Powers of the post-entry base are antitone in the exponent. -/
theorem postEntryBase_pow_antitone :
    Antitone (fun k : ℕ => postEntryBase ^ k) := by
  intro a b hab
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  change postEntryBase ^ (a + k) ≤ postEntryBase ^ a
  rw [pow_add]
  have hk : postEntryBase ^ k ≤ 1 :=
    pow_le_one₀ bot_le postEntryBase_le_one
  calc
    postEntryBase ^ a * postEntryBase ^ k ≤
        postEntryBase ^ a * 1 := by
      gcongr
    _ = postEntryBase ^ a := by simp

/-- Entry at `x ≥ 3n/4` starts strictly above the post-entry lower barrier. -/
theorem entryTarget_not_postEntryFailure
    (s : State n B) (hn : 0 < n) (hentry : EntryTarget s) :
    ¬ PostEntryFailure s := by
  unfold EntryTarget PostEntryFailure at *
  omega

/-- The entry checkpoint has an integer buffer of at least `⌊n/32⌋` above the
post-entry lower threshold. -/
theorem entryTarget_postEntry_buffer
    (s : State n B) (hentry : EntryTarget s) :
    postEntryLower n + n / 32 ≤ State.x s := by
  unfold EntryTarget postEntryLower at *
  omega

/-- Exact count-level adverse bias throughout the post-entry live band. -/
theorem postEntryLive_worst_weight_cross
    (s : State n B) (hn : 64 ≤ n) (hs : PostEntryLive s) :
    5 * worstDownWeight s ≤ 4 * worstUpWeight s := by
  let x := State.x s
  let y := State.y s
  let z := State.z s
  let m := y + z
  rcases hs with ⟨hlower, htarget⟩
  change 23 * n < 32 * x at hlower
  change x + 2 * z < n at htarget
  have htotal : x + m = n := by
    dsimp only [x, y, z, m]
    have ht := State.total s
    omega
  have hmx : 23 * m < 9 * x := by omega
  have hzy : z < y := by
    omega
  have hm1 : m - 1 ≤ 2 * y := by
    dsimp only [m]
    omega
  have hx41 : 41 ≤ x := by omega
  have hfive : 5 * m ≤ 2 * (x - 1) := by omega
  have hten : 10 * m ≤ 4 * (x - 1) := by omega
  have hcore :
      5 * (m * (m - 1)) ≤ 4 * ((x - 1) * y) := by
    calc
      5 * (m * (m - 1)) ≤ 5 * (m * (2 * y)) := by
        gcongr
      _ = (10 * m) * y := by ring
      _ ≤ (4 * (x - 1)) * y := Nat.mul_le_mul_right y hten
      _ = 4 * ((x - 1) * y) := by ring
  have htwoM : 2 * Nat.choose m 2 = m * (m - 1) :=
    two_mul_choose_two m
  have htwoX : 2 * Nat.choose x 2 = x * (x - 1) :=
    two_mul_choose_two x
  have hscaled :
      2 * (5 * worstDownWeight s) ≤
        2 * (4 * worstUpWeight s) := by
    unfold worstDownWeight worstUpWeight
    change
      2 * (5 * (x * Nat.choose m 2)) ≤
        2 * (4 * (Nat.choose x 2 * y))
    calc
      2 * (5 * (x * Nat.choose m 2)) =
          x * (5 * (2 * Nat.choose m 2)) := by ring
      _ = x * (5 * (m * (m - 1))) := by rw [htwoM]
      _ ≤ x * (4 * ((x - 1) * y)) :=
        Nat.mul_le_mul_left x hcore
      _ = 4 * ((2 * Nat.choose x 2) * y) := by
        rw [htwoX]
        ring
      _ = 2 * (4 * (Nat.choose x 2 * y)) := by ring
  omega

/-- Exact PMF mass form of the post-entry adverse bias. -/
theorem postEntryLive_worst_mass_bias
    (h3 : 3 ≤ n) (s : State n B) (hn : 64 ≤ n)
    (hs : PostEntryLive s) :
    movePMF Control.worst s h3 .down ≤
      movePMF Control.worst s h3 .up * postEntryBase := by
  rw [movePMF_down, movePMF_up, downWeight_worst, upWeight_worst]
  apply div_le_div_mul_right
  unfold postEntryBase
  have hden0 : (5 : ℝ≥0∞) ≠ 0 := by norm_num
  have hdenTop : (5 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)]
  exact_mod_cast (by
    simpa [mul_comm] using postEntryLive_worst_weight_cross s hn hs)

/-- The geometric post-entry potential is conserved under the paper-worst
response at every live state. -/
theorem postEntryLive_worst_conserve
    (h3 : 3 ≤ n) (s : State n B) (hn : 64 ≤ n)
    (hs : PostEntryLive s) :
    expect (step Control.worst s h3)
        (fun t => postEntryBase ^ State.x t) ≤
      postEntryBase ^ State.x s := by
  have hx : 0 < State.x s := by
    have hlower := hs.1
    omega
  rw [expect_step_x_actions]
  have hkey := three_term_drift_ennreal
    (movePMF_masses_sum Control.worst s h3)
    postEntryBase_le_one
    (postEntryLive_worst_mass_bias h3 s hn hs)
  have hpowx :
      postEntryBase ^ State.x s =
        postEntryBase ^ (State.x s - 1) * postEntryBase := by
    rw [show State.x s = (State.x s - 1) + 1 by omega, pow_add]
    simp
  have hpowx1 :
      postEntryBase ^ (State.x s + 1) =
        postEntryBase ^ (State.x s - 1) * postEntryBase ^ 2 := by
    rw [show State.x s + 1 = (State.x s - 1) + 2 by omega, pow_add]
  calc
    movePMF Control.worst s h3 .down *
          postEntryBase ^ (State.x s - 1) +
        movePMF Control.worst s h3 .stay *
          postEntryBase ^ State.x s +
        movePMF Control.worst s h3 .up *
          postEntryBase ^ (State.x s + 1) =
      postEntryBase ^ (State.x s - 1) *
        (movePMF Control.worst s h3 .down +
          movePMF Control.worst s h3 .stay * postEntryBase +
          movePMF Control.worst s h3 .up * postEntryBase ^ 2) := by
      rw [hpowx, hpowx1]
      ring
    _ ≤ postEntryBase ^ (State.x s - 1) * postEntryBase :=
      mul_le_mul_right hkey _
    _ = postEntryBase ^ State.x s := hpowx.symm

/-- The one-step conservation inequality is uniform over the complete adaptive
history. -/
theorem adaptiveStep_postEntry_conserve
    (σ : Strategy n B) (hist : History n B)
    (s : State n B) (h3 : 3 ≤ n) (hn : 64 ≤ n)
    (hbad : ¬ PostEntryFailure s)
    (htarget : ¬ PostEntryTarget s) :
    expect (adaptiveStep σ hist s h3)
        (fun t => postEntryBase ^ State.x t) ≤
      postEntryBase ^ State.x s := by
  have hlive : PostEntryLive s := by
    constructor
    · unfold PostEntryFailure at hbad
      omega
    · unfold PostEntryTarget StrongXEntry at htarget
      omega
  exact
    (adaptiveStep_expect_x_le_worst σ hist s h3
      (fun k => postEntryBase ^ k)
      postEntryBase_pow_antitone).trans
        (postEntryLive_worst_conserve h3 s hn hlive)

/-- Genuine history-dependent physical law stopped at post-entry failure or
strong entry. -/
noncomputable def postEntryLaw
    (σ : Strategy n B) (h3 : 3 ≤ n) :
    ℕ → History n B → State n B → PMF (State n B)
  | 0, _, s => PMF.pure s
  | T + 1, hist, s =>
      if PostEntryStop s then
        PMF.pure s
      else
        (adaptiveEventStep σ hist s h3).bind
          (fun e => postEntryLaw σ h3 T (e :: hist) e.after)

/-- The post-entry geometric potential is a supermartingale for every horizon
and every history-dependent adversary. -/
theorem postEntryLaw_expect_le
    (σ : Strategy n B) (h3 : 3 ≤ n) (hn : 64 ≤ n) :
    ∀ T hist s,
      expect (postEntryLaw σ h3 T hist s)
          (fun t => postEntryBase ^ State.x t) ≤
        postEntryBase ^ State.x s := by
  intro T
  induction T with
  | zero =>
      intro hist s
      simp [postEntryLaw]
  | succ T ih =>
      intro hist s
      by_cases hstop : PostEntryStop s
      · rw [postEntryLaw, if_pos hstop, expect_pure]
      · rw [postEntryLaw, if_neg hstop, expect_bind']
        have hbad : ¬ PostEntryFailure s := by
          intro h
          exact hstop (Or.inl h)
        have htarget : ¬ PostEntryTarget s := by
          intro h
          exact hstop (Or.inr h)
        calc
          (∑' e, adaptiveEventStep σ hist s h3 e *
              expect (postEntryLaw σ h3 T (e :: hist) e.after)
                (fun t => postEntryBase ^ State.x t)) ≤
              ∑' e, adaptiveEventStep σ hist s h3 e *
                postEntryBase ^ State.x e.after := by
            exact ENNReal.tsum_le_tsum fun e =>
              mul_le_mul_right (ih (e :: hist) e.after) _
          _ = expect (adaptiveEventStep σ hist s h3)
                (fun e => postEntryBase ^ State.x e.after) := by
            rfl
          _ = expect (adaptiveStep σ hist s h3)
                (fun t => postEntryBase ^ State.x t) :=
            expect_adaptiveEventStep_after σ hist s h3
              (fun t => postEntryBase ^ State.x t)
          _ ≤ postEntryBase ^ State.x s :=
            adaptiveStep_postEntry_conserve
              σ hist s h3 hn hbad htarget

/-- Lower-boundary mass of the stopped adaptive physical law. -/
noncomputable def postEntryFailureMass
    (σ : Strategy n B) (h3 : 3 ≤ n) (T : ℕ)
    (hist : History n B) (s : State n B) : ℝ≥0∞ :=
  ∑' t, if PostEntryFailure t then
    postEntryLaw σ h3 T hist s t else 0

/-- Every lower-failure state has at least the boundary value of the geometric
potential. -/
theorem postEntryPotential_failure_floor
    (s : State n B) (hs : PostEntryFailure s) :
    postEntryBase ^ postEntryLower n ≤
      postEntryBase ^ State.x s := by
  apply postEntryBase_pow_antitone
  unfold postEntryLower PostEntryFailure at *
  omega

/-- Exact finite-horizon post-entry no-backsliding bound, uniform over every
history-dependent Byzantine strategy. -/
theorem adaptive_postEntry_failure_le
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (T : ℕ) (s₀ : State n B) (hn : 64 ≤ n) :
    postEntryFailureMass σ h3 T [] s₀ ≤
      postEntryBase ^ State.x s₀ /
        postEntryBase ^ postEntryLower n := by
  have hpow0 : postEntryBase ^ postEntryLower n ≠ 0 :=
    pow_ne_zero _ postEntryBase_ne_zero
  have hpowtop : postEntryBase ^ postEntryLower n ≠ ⊤ :=
    ENNReal.pow_ne_top postEntryBase_ne_top
  unfold postEntryFailureMass
  calc
    (∑' t, if PostEntryFailure t then
        postEntryLaw σ h3 T [] s₀ t else 0) ≤
      ∑' t, if postEntryBase ^ postEntryLower n ≤
          postEntryBase ^ State.x t then
        postEntryLaw σ h3 T [] s₀ t else 0 := by
      refine ENNReal.tsum_le_tsum fun t => ?_
      by_cases ht : PostEntryFailure t
      · have hf := postEntryPotential_failure_floor t ht
        simp [ht, hf]
      · simp [ht]
    _ ≤ expect (postEntryLaw σ h3 T [] s₀)
          (fun t => postEntryBase ^ State.x t) /
        postEntryBase ^ postEntryLower n :=
      markov_div _ _ _ hpow0 hpowtop
    _ ≤ postEntryBase ^ State.x s₀ /
          postEntryBase ^ postEntryLower n :=
      ENNReal.div_le_div_right
        (postEntryLaw_expect_le σ h3 hn T [] s₀) _

/-- Paper-facing specialization from the preceding entry checkpoint. -/
theorem adaptive_postEntry_failure_le_of_entryTarget
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (T : ℕ) (s₀ : State n B) (hn : 64 ≤ n)
    (hentry : EntryTarget s₀) :
    postEntryFailureMass σ h3 T [] s₀ ≤
      postEntryBase ^ State.x s₀ /
        postEntryBase ^ postEntryLower n := by
  have _hstart : ¬ PostEntryFailure s₀ :=
    entryTarget_not_postEntryFailure s₀ (by omega) hentry
  exact adaptive_postEntry_failure_le σ h3 T s₀ hn

end Tri.Byzantine

#print axioms Tri.Byzantine.entryTarget_postEntry_buffer
#print axioms Tri.Byzantine.postEntryLive_worst_weight_cross
#print axioms Tri.Byzantine.postEntryLive_worst_mass_bias
#print axioms Tri.Byzantine.postEntryLive_worst_conserve
#print axioms Tri.Byzantine.adaptiveStep_postEntry_conserve
#print axioms Tri.Byzantine.postEntryLaw_expect_le
#print axioms Tri.Byzantine.adaptive_postEntry_failure_le
