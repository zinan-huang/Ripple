/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedOdds
import Tri.Phase3Productive
import Tri.Phase3Level
import Tri.DoubleBAssembly
import Tri.EscapeSplit
import Tri.RelaxedProductivity
import Tri.RelaxedBandErrorConstants

/-!
# Paper Lemma 7 — α-relaxed minority decay

The paper's displayed rate condition is used only through the live-band odds
guard `β * y ≤ α * x`.  This file keeps that guard in cleared form and runs the
same stopped productive-event argument as `Tri.PaperCorollary2`.

## Constants, and where they come from

The paper states the deadline as `Θ(n/((β−1)k))` productive events with failure
`exp(−Ω((β−1)γ lg n))`, for a constant `1 < β ≤ 2`, at a state with `y = n/k` and
`1 + β ≤ k ≤ n/(γ lg n)`, under the rate condition
`α ≥ β(n/k + d)/(n(k−1)/k − d)` where `d = γ lg n`.

This file makes those explicit:

* `lemma7PaperDeadline β P` is the least `T` with `(β−1)T ≥ 4096·P`, i.e. `T = ⌈4096P/(β−1)⌉`.
  With `P = n/k` the minority count this is `Θ(n/((β−1)k))` — the paper's order, with `4096`
  the constant this proof route carries.
* The envelope `2 exp(−(β−1)d/4096)` is the paper's `exp(−Ω((β−1)γ lg n))` with the same
  explicit constant.
* The rate premise is carried CROSS-MULTIPLIED and subtraction-free as
  `β(P + d) ≤ r.fire · xLo` with `xLo + d = x₀`, which is the printed inequality cleared of
  its denominator.

`β` is part of Lemma 7's own statement, not a call-site choice; Theorem 4's Phase II
instantiates it at `β = 6/5`.
-/

namespace Tri

open scoped ENNReal NNReal

variable {α : Type*}

theorem lemma7_freeze_congr (K : α → PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ s, P s ↔ Q s) :
    freeze P K = freeze Q K := by
  funext s
  unfold freeze
  by_cases hs : P s
  · rw [if_pos hs, if_pos ((h s).1 hs)]
  · rw [if_neg hs, if_neg (fun hq => hs ((h s).2 hq))]

theorem lemma7_terminalFailureMass_congr (p : PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ s, P s ↔ Q s) :
    terminalFailureMass p P = terminalFailureMass p Q := by
  unfold terminalFailureMass
  refine tsum_congr fun z => ?_
  by_cases hz : P z
  · rw [if_pos hz, if_pos ((h z).1 hz)]
  · rw [if_neg hz, if_neg (fun hq => hz ((h z).2 hq))]

theorem lemma7_hitProb_congr (K : α → PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ s, P s ↔ Q s) (T : ℕ) (s₀ : α) :
    hitProb P K T s₀ = hitProb Q K T s₀ := by
  unfold hitProb
  rw [lemma7_freeze_congr K P Q h]
  congr 1
  funext z
  unfold ind
  by_cases hz : P z
  · rw [if_pos hz, if_pos ((h z).1 hz)]
  · rw [if_neg hz, if_neg (fun hq => hz ((h z).2 hq))]

private theorem ennreal_ratio_ge_of_mul_le {β down up : ℝ≥0∞}
    (hβt : β ≠ ⊤)
    (hdt : down ≠ ⊤) (hut : up ≠ ⊤)
    (hden0 : down + up ≠ 0)
    (hmul : β * down ≤ up) :
    β / (β + 1) ≤ up / (down + up) := by
  have hβden0 : β + 1 ≠ 0 := by
    simp
  have hβdent : β + 1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hβt, ENNReal.one_ne_top⟩
  have hdent : down + up ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hdt, hut⟩
  rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)]
  have hdivmul :
      β / (β + 1) * (down + up) = β * (down + up) / (β + 1) := by
    simp only [ENNReal.div_eq_inv_mul]
    ring
  rw [hdivmul]
  rw [ENNReal.div_le_iff_le_mul (Or.inl hβden0) (Or.inl hβdent)]
  calc
    β * (down + up) = β * down + β * up := by ring
    _ ≤ up + β * up := add_le_add hmul le_rfl
    _ = up * (β + 1) := by ring

/-- Relaxed analogue of `productive_down_mass_ge`.  Conditional on a productive
relaxed reaction, the minority-down mass is at least `β / (1 + β)` whenever the
cleared live-band guard `β * y ≤ α * x` holds. -/
theorem relaxed_down_mass_ge
    (r : RelaxedRate) {β : NNReal} {a b : ℕ}
    (h : 3 ≤ (a + 1) + (b + 1))
    (hfireβ : r.fire ≤ β)
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2) ≠ 0)
    (hguard :
      β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal)) :
    (β : ℝ≥0∞) / ((β : ℝ≥0∞) + 1) ≤
      relaxedTriStep r (a + 1) (b + 1) h (a + 2) /
        (relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2)) := by
  exact ennreal_ratio_ge_of_mul_le ENNReal.coe_ne_top
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _) hprod
    (relaxedTriStep_mass_bias r h hfireβ hguard)

/-- The symbolic lower bound on the minority-down productive probability. -/
noncomputable def lemma7DownProb (β : NNReal) : ℝ≥0∞ :=
  ((β / (β + 1) : NNReal) : ℝ≥0∞)

/-- The complementary symbolic minority-up productive probability. -/
noncomputable def lemma7UpProb (β : NNReal) : ℝ≥0∞ :=
  (((1 : NNReal) / (β + 1) : NNReal) : ℝ≥0∞)

/-- Deadline potential base for the symbolic `β` scalar step. -/
noncomputable def lemma7DeadlineW (β : NNReal) : ℝ≥0∞ :=
  (((2 : NNReal) / (β + 1) : NNReal) : ℝ≥0∞)

/-- The factored one-step deadline scalar at the floor `β/(1+β)`. -/
noncomputable def lemma7DeadlineFactor (β : NNReal) : ℝ≥0∞ :=
  lemma7UpProb β + lemma7DownProb β * lemma7DeadlineW β ^ 2

theorem lemma7_prob_sum (β : NNReal) :
    lemma7DownProb β + lemma7UpProb β = 1 := by
  unfold lemma7DownProb lemma7UpProb
  rw [← ENNReal.coe_add, show (β / (β + 1) + 1 / (β + 1) : NNReal) = 1 by
    rw [← add_div]
    field_simp]
  simp

theorem lemma7DownProb_eq (β : NNReal) :
    lemma7DownProb β = (β : ℝ≥0∞) / ((β : ℝ≥0∞) + 1) := by
  unfold lemma7DownProb
  rw [ENNReal.coe_div (by positivity : β + 1 ≠ 0)]
  simp

theorem lemma7DeadlineW_le_one {β : NNReal} (hβ1 : (1 : NNReal) ≤ β) :
    lemma7DeadlineW β ≤ 1 := by
  unfold lemma7DeadlineW
  exact_mod_cast (by
    rw [div_le_one]
    · calc
        (2 : NNReal) = 1 + 1 := by norm_num
        _ ≤ 1 + β := add_le_add_right hβ1 1
        _ = β + 1 := by ring
    · positivity)

theorem lemma7DeadlineW_sq_le_one {β : NNReal} (hβ1 : (1 : NNReal) ≤ β) :
    lemma7DeadlineW β ^ 2 ≤ 1 := by
  exact pow_le_one₀ (n := 2) (by positivity) (lemma7DeadlineW_le_one hβ1)

/-- Deadline scalar step, obtained directly from `scalar_step_antitone` at
`q₀ = β/(1+β)` and `q₀' = 1/(1+β)`. -/
theorem lemma7_deadline_scalar_step {β : NNReal} {q q' : ℝ≥0∞}
    (hβ1 : (1 : NNReal) ≤ β)
    (hsum : q + q' = 1) (hq : lemma7DownProb β ≤ q) :
    q' + q * lemma7DeadlineW β ^ 2 ≤ lemma7DeadlineFactor β := by
  unfold lemma7DeadlineFactor
  exact scalar_step_antitone hsum (lemma7_prob_sum β) hq
    (lemma7DeadlineW_sq_le_one hβ1)

/-- Feller scalar step, obtained directly from `scalar_step_antitone` at
`q₀ = β/(1+β)` and `q₀' = 1/(1+β)`. -/
theorem lemma7_feller_scalar_step {β : NNReal} {q q' : ℝ≥0∞}
    (hβ1 : (1 : NNReal) ≤ β)
    (hsum : q + q' = 1) (hq : lemma7DownProb β ≤ q) :
    q' + q * ((β : ℝ≥0∞)⁻¹ ^ 2) ≤ (β : ℝ≥0∞)⁻¹ := by
  have hu1 : (β : ℝ≥0∞)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.mpr (by exact_mod_cast hβ1)
  have hv : (β : ℝ≥0∞)⁻¹ ^ 2 ≤ 1 :=
    pow_le_one₀ (n := 2) (by positivity) hu1
  refine le_trans (scalar_step_antitone hsum (lemma7_prob_sum β) hq hv) ?_
  unfold lemma7DownProb lemma7UpProb
  have hβ0NN : β ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hβ1)
  rw [← ENNReal.coe_inv hβ0NN]
  apply le_of_eq
  apply congrArg (fun x : NNReal => (x : ℝ≥0∞))
  apply NNReal.eq
  change
    ((1 / (β + 1) + β / (β + 1) * β⁻¹ ^ 2 : NNReal) : ℝ) =
      ((β⁻¹ : NNReal) : ℝ)
  have hβR0 : (β : ℝ) ≠ 0 := by
    exact_mod_cast hβ0NN
  have hβR1 : (β : ℝ) + 1 ≠ 0 := by positivity
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_inv,
    NNReal.coe_pow, NNReal.coe_one]
  field_simp [hβR0, hβR1]

/-- The relaxed two-point productive law, conditioned on a productive reaction. -/
noncomputable def relaxedProductiveTriInterior
    (r : RelaxedRate) (a b : ℕ) (h : 3 ≤ (a + 1) + (b + 1))
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2) ≠ 0) :
    PMF ℕ :=
  (PMF.ofFintype
    (fun up : Bool =>
      if up then
        relaxedTriStep r (a + 1) (b + 1) h (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2))
      else
        relaxedTriStep r (a + 1) (b + 1) h a /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2)))
    (by
      rw [show (Finset.univ : Finset Bool) = {false, true} by
        ext up
        cases up <;> simp]
      simp only [Finset.sum_insert, Finset.mem_singleton, Bool.false_eq_true,
        not_false_eq_true, Finset.sum_singleton, ↓reduceIte]
      rw [ENNReal.div_add_div_same, ENNReal.div_self hprod]
      exact ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)).map
    fun up => if up then a + 2 else a

theorem expect_relaxedProductiveTriInterior
    (r : RelaxedRate) (a b : ℕ) (h : 3 ≤ (a + 1) + (b + 1))
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2) ≠ 0)
    (V : ℕ → ℝ≥0∞) :
    expect (relaxedProductiveTriInterior r a b h hprod) V =
      relaxedTriStep r (a + 1) (b + 1) h a /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2)) * V a +
        relaxedTriStep r (a + 1) (b + 1) h (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2)) * V (a + 2) := by
  rw [relaxedProductiveTriInterior, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext up
    cases up <;> simp]
  simp

theorem relaxedProductiveTriInterior_masses
    (r : RelaxedRate) (a b : ℕ) (h : 3 ≤ (a + 1) + (b + 1))
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2) ≠ 0) :
    relaxedTriStep r (a + 1) (b + 1) h (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2)) +
      relaxedTriStep r (a + 1) (b + 1) h a /
          (relaxedTriStep r (a + 1) (b + 1) h a +
            relaxedTriStep r (a + 1) (b + 1) h (a + 2)) = 1 := by
  rw [ENNReal.div_add_div_same]
  rw [add_comm (relaxedTriStep r (a + 1) (b + 1) h (a + 2))]
  exact ENNReal.div_self hprod
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)

noncomputable def relaxedProductiveTriChain
    (r : RelaxedRate) (n : ℕ) : ℕ → PMF ℕ := fun x =>
  if hphys : 3 ≤ n ∧ 0 < x ∧ x < n then
    let a := x - 1
    let b := n - x - 1
    let hstep : 3 ≤ (a + 1) + (b + 1) := by omega
    if hprod :
        relaxedTriStep r (a + 1) (b + 1) hstep a +
            relaxedTriStep r (a + 1) (b + 1) hstep (a + 2) ≠ 0 then
      relaxedProductiveTriInterior r a b hstep hprod
    else
      PMF.pure x
  else
    PMF.pure x

theorem relaxedProductiveTriChain_apply
    (r : RelaxedRate) {n a b : ℕ}
    (hpop : a + b + 2 = n) (h3 : 3 ≤ n)
    (hprod :
      relaxedTriStep r (a + 1) (b + 1) (by omega) a +
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0) :
    relaxedProductiveTriChain r n (a + 1) =
      relaxedProductiveTriInterior r a b (by omega) hprod := by
  unfold relaxedProductiveTriChain
  rw [dif_pos ⟨h3, by omega, by omega⟩]
  dsimp only
  simp only [show a + 1 - 1 = a by omega, show n - (a + 1) - 1 = b by omega]
  rw [dif_pos hprod]

theorem relaxedProductiveTriChain_support_le
    (r : RelaxedRate) (n : ℕ) :
    ∀ x, x ≤ n → ∀ z, relaxedProductiveTriChain r n x z ≠ 0 → z ≤ n := by
  intro x hx z hz
  unfold relaxedProductiveTriChain at hz
  by_cases hphys : 3 ≤ n ∧ 0 < x ∧ x < n
  · rw [dif_pos hphys] at hz
    dsimp only at hz
    obtain ⟨h3, hx0, hxn⟩ := hphys
    split_ifs at hz with hprod
    · by_contra hzn
      push Not at hzn
      apply hz
      unfold relaxedProductiveTriInterior
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro up
      cases up with
      | false => rw [if_neg (by simp; omega)]
      | true => rw [if_neg (by simp; omega)]
    · simp only [PMF.pure_apply] at hz
      by_cases hzz : z = x
      · omega
      · simp [hzz] at hz
  · rw [dif_neg hphys] at hz
    simp only [PMF.pure_apply] at hz
    by_cases hzz : z = x
    · omega
    · simp [hzz] at hz

def Lemma7Target (n x : ℕ) : Prop := n ≤ x

def Lemma7Escape (n P d x : ℕ) : Prop := x + (P + d) < n ∨ n < x

def Lemma7Stop (n P d x : ℕ) : Prop :=
  Lemma7Target n x ∨ Lemma7Escape n P d x

instance lemma7TargetDecidable (n : ℕ) :
    DecidablePred (Lemma7Target n) := by
  intro x
  unfold Lemma7Target
  infer_instance

instance lemma7EscapeDecidable (n P d : ℕ) :
    DecidablePred (Lemma7Escape n P d) := by
  intro x
  unfold Lemma7Escape
  infer_instance

instance lemma7StopDecidable (n P d : ℕ) :
    DecidablePred (Lemma7Stop n P d) := by
  intro x
  unfold Lemma7Stop Lemma7Target Lemma7Escape
  infer_instance

theorem lemma7_live_interior {n P d x : ℕ}
    (hroom : P + d < n)
    (hstop : ¬ Lemma7Stop n P d x) :
    ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n ∧
      ¬ Lemma7Stop n P d (a + 1) := by
  have hstopOrig := hstop
  unfold Lemma7Stop Lemma7Target Lemma7Escape at hstop
  push Not at hstop
  obtain ⟨htarget, hesc, hphys⟩ := hstop
  refine ⟨x - 1, n - x - 1, ?_, ?_, ?_⟩
  · omega
  · omega
  · simpa [show x - 1 + 1 = x by omega] using hstopOrig

noncomputable def lemma7DeadlinePhi (β : NNReal) : ℝ≥0∞ :=
  lemma7DeadlineFactor β / lemma7DeadlineW β

theorem lemma7DeadlineW_ne_zero (β : NNReal) :
    lemma7DeadlineW β ≠ 0 := by
  unfold lemma7DeadlineW
  simp only [ne_eq, ENNReal.coe_eq_zero]
  positivity

theorem lemma7DeadlineW_ne_top (β : NNReal) :
    lemma7DeadlineW β ≠ ⊤ := by
  unfold lemma7DeadlineW
  exact ENNReal.coe_ne_top

theorem lemma7DeadlinePhi_mul_w (β : NNReal) :
    lemma7DeadlinePhi β * lemma7DeadlineW β = lemma7DeadlineFactor β := by
  unfold lemma7DeadlinePhi
  exact ENNReal.div_mul_cancel (lemma7DeadlineW_ne_zero β)
    (lemma7DeadlineW_ne_top β)

theorem lemma7_stopped_potential_step
    (r : RelaxedRate) (β : NNReal) (n P d : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n)
    (hβ1 : (1 : NNReal) ≤ β)
    (hguard :
      ∀ a b : ℕ, a + b + 2 = n → ¬ Lemma7Stop n P d (a + 1) →
        β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal))
    (hprodLive :
      ∀ a b : ℕ, (hpop : a + b + 2 = n) → ¬ Lemma7Stop n P d (a + 1) →
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0)
    (x : ℕ) :
    expect (freeze (Lemma7Stop n P d) (relaxedProductiveTriChain r n) x)
        (fun z => if Lemma7Stop n P d z then 0 else lemma7DeadlineW β ^ z)
      ≤ lemma7DeadlinePhi β *
          (if Lemma7Stop n P d x then 0 else lemma7DeadlineW β ^ x) := by
  classical
  by_cases hstop : Lemma7Stop n P d x
  · simp [freeze, hstop]
  · obtain ⟨a, b, hx, hpop, hstopab⟩ :=
      lemma7_live_interior hroom hstop
    subst hx
    have hprod := hprodLive a b hpop hstopab
    rw [show freeze (Lemma7Stop n P d) (relaxedProductiveTriChain r n) (a + 1)
          = relaxedProductiveTriChain r n (a + 1) by simp [freeze, hstopab],
      relaxedProductiveTriChain_apply r hpop h3 hprod]
    have hdrop : ∀ z : ℕ,
        (if Lemma7Stop n P d z then 0 else lemma7DeadlineW β ^ z)
          ≤ lemma7DeadlineW β ^ z := by
      intro z
      split <;> simp
    refine le_trans
      (expect_mono (relaxedProductiveTriInterior r a b (by omega) hprod) hdrop) ?_
    rw [expect_relaxedProductiveTriInterior]
    have hq : lemma7DownProb β ≤
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) := by
      rw [lemma7DownProb_eq]
      exact relaxed_down_mass_ge r (by omega)
        (by
          have hfire1 : r.fire ≤ 1 := by
            rw [← r.add_eq_one]
            exact le_add_right le_rfl
          exact hfire1.trans hβ1)
        hprod (hguard a b hpop hstopab)
    have hsum : relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) +
        relaxedTriStep r (a + 1) (b + 1) (by omega) a /
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) = 1 := by
      exact relaxedProductiveTriInterior_masses r a b (by omega) hprod
    have hscalar := lemma7_deadline_scalar_step hβ1 hsum hq
    have hwphi : lemma7DeadlinePhi β * lemma7DeadlineW β = lemma7DeadlineFactor β :=
      lemma7DeadlinePhi_mul_w β
    have hpow1 : lemma7DeadlineW β ^ (a + 1) =
        lemma7DeadlineW β ^ a * lemma7DeadlineW β := by
      rw [pow_succ]
    have hpow2 : lemma7DeadlineW β ^ (a + 2) =
        lemma7DeadlineW β ^ a * lemma7DeadlineW β ^ 2 := by
      rw [pow_add]
    rw [hpow1, hpow2, if_neg hstopab]
    calc
      relaxedTriStep r (a + 1) (b + 1) (by omega) a /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
              lemma7DeadlineW β ^ a +
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
              (lemma7DeadlineW β ^ a * lemma7DeadlineW β ^ 2)
          = (relaxedTriStep r (a + 1) (b + 1) (by omega) a /
                (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                  relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
                (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                  relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
                lemma7DeadlineW β ^ 2) *
              lemma7DeadlineW β ^ a := by ring
      _ ≤ lemma7DeadlineFactor β * lemma7DeadlineW β ^ a :=
          mul_le_mul_left hscalar _
      _ = lemma7DeadlinePhi β *
            (lemma7DeadlineW β ^ a * lemma7DeadlineW β) := by
          rw [← hwphi]
          ring

theorem lemma7_deadline_branch
    (r : RelaxedRate) (β : NNReal) (n P d x₀ T : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n)
    (hβ1 : (1 : NNReal) ≤ β)
    (hx₀n : x₀ ≤ n)
    (hguard :
      ∀ a b : ℕ, a + b + 2 = n → ¬ Lemma7Stop n P d (a + 1) →
        β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal))
    (hprodLive :
      ∀ a b : ℕ, (hpop : a + b + 2 = n) → ¬ Lemma7Stop n P d (a + 1) →
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0) :
    terminalFailureMass
        (iter (freeze (Lemma7Stop n P d) (relaxedProductiveTriChain r n)) T x₀)
        (Lemma7Stop n P d)
      ≤ lemma7DeadlinePhi β ^ T *
          (if Lemma7Stop n P d x₀ then 0 else lemma7DeadlineW β ^ x₀) /
            lemma7DeadlineW β ^ n := by
  classical
  have htail := count_tail_frozen (relaxedProductiveTriChain r n) (Lemma7Stop n P d)
    id (lemma7DeadlineW β) (lemma7DeadlinePhi β) (lemma7DeadlineW_le_one hβ1)
    (lemma7DeadlineW_ne_zero β)
    (lemma7_stopped_potential_step r β n P d h3 hroom hβ1 hguard hprodLive)
    T n x₀
  refine le_trans ?_ htail
  unfold terminalFailureMass
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hzstop : Lemma7Stop n P d z
  · simp [hzstop]
  · by_cases hzero :
      iter (freeze (Lemma7Stop n P d) (relaxedProductiveTriChain r n)) T x₀ z = 0
    · simp [hzstop, hzero]
    · have hzle : z ≤ n := by
        exact iter_support_closed
          (freeze (Lemma7Stop n P d) (relaxedProductiveTriChain r n))
          (fun s => s ≤ n)
          (freeze_support_closed (relaxedProductiveTriChain r n) (Lemma7Stop n P d)
            (fun s => s ≤ n) (relaxedProductiveTriChain_support_le r n))
          T x₀ z hx₀n hzero
      simp [hzstop, hzle]

def lemma7EscapeBound (n P d : ℕ) : ℕ := n - (P + d) - 1

theorem lemma7Level_le_iff (n P d z : ℕ) (hroom : P + d < n) :
    phase3Level n z ≤ lemma7EscapeBound n P d ↔ Lemma7Escape n P d z := by
  unfold phase3Level lemma7EscapeBound Lemma7Escape
  by_cases hz : n < z
  · simp only [if_pos hz]
    exact ⟨fun _ => Or.inr hz, fun _ => Nat.zero_le _⟩
  · simp only [if_neg hz]
    constructor
    · intro h
      exact Or.inl (by omega)
    · rintro (h | h) <;> omega

theorem lemma7_feller_hfroz_stop
    (r : RelaxedRate) (β : NNReal) (n P d : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n)
    (hβ1 : (1 : NNReal) ≤ β)
    (hguard :
      ∀ a b : ℕ, a + b + 2 = n → ¬ Lemma7Stop n P d (a + 1) →
        β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal))
    (hprodLive :
      ∀ a b : ℕ, (hpop : a + b + 2 = n) → ¬ Lemma7Stop n P d (a + 1) →
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0)
    (x : ℕ) :
    expect
        (freeze (Lemma7Stop n P d) (relaxedProductiveTriChain r n) x)
        (fun z => ((β : ℝ≥0∞)⁻¹) ^ phase3Level n z)
      ≤ ((β : ℝ≥0∞)⁻¹) ^ phase3Level n x := by
  classical
  by_cases hstop : Lemma7Stop n P d x
  · simp [freeze, hstop]
  · obtain ⟨a, b, hx, hpop, hstopab⟩ :=
      lemma7_live_interior hroom hstop
    subst hx
    have hprod := hprodLive a b hpop hstopab
    rw [show freeze (Lemma7Stop n P d) (relaxedProductiveTriChain r n) (a + 1)
          = relaxedProductiveTriChain r n (a + 1) by simp [freeze, hstopab],
      relaxedProductiveTriChain_apply r hpop h3 hprod,
      expect_relaxedProductiveTriInterior]
    have hla : phase3Level n a = a := by
      simp [phase3Level, show ¬ n < a by omega]
    have hla2 : phase3Level n (a + 2) = a + 2 := by
      simp [phase3Level, show ¬ n < a + 2 by omega]
    have hla1 : phase3Level n (a + 1) = a + 1 := by
      simp [phase3Level, show ¬ n < a + 1 by omega]
    rw [hla, hla2, hla1]
    have hq : lemma7DownProb β ≤
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) := by
      rw [lemma7DownProb_eq]
      exact relaxed_down_mass_ge r (by omega)
        (by
          have hfire1 : r.fire ≤ 1 := by
            rw [← r.add_eq_one]
            exact le_add_right le_rfl
          exact hfire1.trans hβ1)
        hprod (hguard a b hpop hstopab)
    have hsum : relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) +
        relaxedTriStep r (a + 1) (b + 1) (by omega) a /
          (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) = 1 := by
      exact relaxedProductiveTriInterior_masses r a b (by omega) hprod
    have hscalar := lemma7_feller_scalar_step hβ1 hsum hq
    have hpow1 : ((β : ℝ≥0∞)⁻¹) ^ (a + 1) =
        ((β : ℝ≥0∞)⁻¹) ^ a * ((β : ℝ≥0∞)⁻¹) := by
      rw [pow_succ]
    have hpow2 : ((β : ℝ≥0∞)⁻¹) ^ (a + 2) =
        ((β : ℝ≥0∞)⁻¹) ^ a * ((β : ℝ≥0∞)⁻¹) ^ 2 := by
      rw [pow_add]
    rw [hpow1, hpow2]
    calc
      relaxedTriStep r (a + 1) (b + 1) (by omega) a /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
              ((β : ℝ≥0∞)⁻¹) ^ a +
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
            (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
              (((β : ℝ≥0∞)⁻¹) ^ a * ((β : ℝ≥0∞)⁻¹) ^ 2)
          = (relaxedTriStep r (a + 1) (b + 1) (by omega) a /
                (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                  relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) +
              relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) /
                (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
                  relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
                ((β : ℝ≥0∞)⁻¹) ^ 2) *
              ((β : ℝ≥0∞)⁻¹) ^ a := by ring
      _ ≤ (β : ℝ≥0∞)⁻¹ * ((β : ℝ≥0∞)⁻¹) ^ a :=
          mul_le_mul_left hscalar _
      _ = ((β : ℝ≥0∞)⁻¹) ^ a * ((β : ℝ≥0∞)⁻¹) := by ring

theorem lemma7_escape_branch
    (r : RelaxedRate) (β : NNReal) (n P d x₀ T b : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n)
    (hβ1 : (1 : NNReal) ≤ β)
    (hstart : phase3Level n x₀ = lemma7EscapeBound n P d + b)
    (hguard :
      ∀ a b : ℕ, a + b + 2 = n → ¬ Lemma7Stop n P d (a + 1) →
        β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal))
    (hprodLive :
      ∀ a b : ℕ, (hpop : a + b + 2 = n) → ¬ Lemma7Stop n P d (a + 1) →
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0) :
    hitProb (Lemma7Escape n P d)
        (freeze (Lemma7Target n) (relaxedProductiveTriChain r n)) T x₀
      ≤ ((β : ℝ≥0∞)⁻¹) ^ b := by
  classical
  set K := relaxedProductiveTriChain r n with hK
  set m := lemma7EscapeBound n P d with hm
  have hstopeq : ∀ s, (Lemma7Target n s ∨ Lemma7Escape n P d s)
      ↔ Lemma7Stop n P d s := fun _ => Iff.rfl
  have hescIff : ∀ s, (phase3Level n s ≤ m) ↔ Lemma7Escape n P d s := by
    intro s
    rw [hm]
    exact lemma7Level_le_iff n P d s hroom
  have hfroz : ∀ s,
      expect (freeze (fun z => phase3Level n z ≤ m)
          (freeze (Lemma7Target n) K) s)
        (fun z => ((β : ℝ≥0∞)⁻¹) ^ phase3Level n z)
        ≤ ((β : ℝ≥0∞)⁻¹) ^ phase3Level n s := by
    intro s
    rw [lemma7_freeze_congr (freeze (Lemma7Target n) K)
        (fun z => phase3Level n z ≤ m) (Lemma7Escape n P d) hescIff,
      show freeze (Lemma7Escape n P d) (freeze (Lemma7Target n) K)
          = freeze (fun z => Lemma7Target n z ∨ Lemma7Escape n P d z) K from
        freeze_escape_freeze_done K (Lemma7Target n) (Lemma7Escape n P d),
      lemma7_freeze_congr K (fun z => Lemma7Target n z ∨ Lemma7Escape n P d z)
        (Lemma7Stop n P d) hstopeq]
    rw [hK]
    exact lemma7_feller_hfroz_stop r β n P d h3 hroom hβ1 hguard hprodLive s
  rw [← lemma7_hitProb_congr (freeze (Lemma7Target n) K)
      (fun z => phase3Level n z ≤ m) (Lemma7Escape n P d) hescIff T x₀]
  refine le_trans (le_iSup
    (fun T => hitProb (fun z => phase3Level n z ≤ m)
      (freeze (Lemma7Target n) K) T x₀) T) ?_
  exact feller_ruin_u (K := freeze (Lemma7Target n) K) (phase3Level n)
    m b ((β : ℝ≥0∞)⁻¹)
    (ENNReal.inv_le_one.mpr (by exact_mod_cast hβ1))
    (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)
    (fun z => ((β : ℝ≥0∞)⁻¹) ^ phase3Level n z) (fun _ => rfl)
    hfroz x₀ (by rw [hm] at hstart; exact hstart)

theorem lemma7
    (r : RelaxedRate) (β : NNReal) (n P d x₀ T b : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n)
    (hβgt : (1 : NNReal) < β) (hβ2 : β ≤ 2)
    (hx₀n : x₀ ≤ n)
    (hstart : phase3Level n x₀ = lemma7EscapeBound n P d + b)
    (hguard :
      ∀ a b : ℕ, a + b + 2 = n → ¬ Lemma7Stop n P d (a + 1) →
        β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal))
    (hprodLive :
      ∀ a b : ℕ, (hpop : a + b + 2 = n) → ¬ Lemma7Stop n P d (a + 1) →
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0) :
    terminalFailureMass
        (iter (freeze (Lemma7Target n) (relaxedProductiveTriChain r n)) T x₀)
        (Lemma7Target n)
      ≤ ((β : ℝ≥0∞)⁻¹) ^ b +
        lemma7DeadlinePhi β ^ T *
          (if Lemma7Stop n P d x₀ then 0 else lemma7DeadlineW β ^ x₀) /
            lemma7DeadlineW β ^ n := by
  classical
  have hβ1 : (1 : NNReal) ≤ β := le_of_lt hβgt
  have _hβ2 : β ≤ 2 := hβ2
  have hstopeq : ∀ s, (Lemma7Target n s ∨ Lemma7Escape n P d s)
      ↔ Lemma7Stop n P d s := fun _ => Iff.rfl
  have hsplit := terminalFailureMass_le_escape_add_live
    (relaxedProductiveTriChain r n) (Lemma7Target n) (Lemma7Escape n P d) T x₀
  rw [lemma7_freeze_congr (relaxedProductiveTriChain r n)
      (fun s => Lemma7Target n s ∨ Lemma7Escape n P d s)
      (Lemma7Stop n P d) hstopeq,
    lemma7_terminalFailureMass_congr _
      (fun s => Lemma7Target n s ∨ Lemma7Escape n P d s)
      (Lemma7Stop n P d) hstopeq] at hsplit
  refine le_trans hsplit ?_
  exact add_le_add
    (lemma7_escape_branch r β n P d x₀ T b h3 hroom hβ1 hstart hguard hprodLive)
    (lemma7_deadline_branch r β n P d x₀ T h3 hroom hβ1 hx₀n hguard hprodLive)

/-- Real form of the deadline contraction factor. -/
theorem lemma7DeadlineFactor_toReal (β : NNReal) :
    (lemma7DeadlineFactor β).toReal =
      (1 : ℝ) / ((β : ℝ) + 1) +
        ((β : ℝ) / ((β : ℝ) + 1)) *
          (((2 : ℝ) / ((β : ℝ) + 1)) ^ 2) := by
  unfold lemma7DeadlineFactor
  rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow]
  · simp [lemma7UpProb, lemma7DownProb, lemma7DeadlineW]
    have hsum : (((β : ℝ≥0∞) + 1).toReal) = (β : ℝ) + 1 := by
      rw [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.one_ne_top]
      simp
    rw [hsum]
  · unfold lemma7UpProb
    exact ENNReal.coe_ne_top
  · unfold lemma7DownProb lemma7DeadlineW
    finiteness

/-- Real form of the deadline potential base. -/
theorem lemma7DeadlineW_toReal (β : NNReal) :
    (lemma7DeadlineW β).toReal = (2 : ℝ) / ((β : ℝ) + 1) := by
  unfold lemma7DeadlineW
  simp
  have hsum : (((β : ℝ≥0∞) + 1).toReal) = (β : ℝ) + 1 := by
    rw [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.one_ne_top]
    simp
  rw [hsum]

/-- The symbolic deadline factor is exactly
`1 - (β-1)^2/(2(β+1)^2)` in real coordinates. -/
theorem lemma7DeadlinePhi_toReal (β : NNReal) :
    (lemma7DeadlinePhi β).toReal =
      1 - (((β : ℝ) - 1) ^ 2 / (2 * (((β : ℝ) + 1) ^ 2))) := by
  unfold lemma7DeadlinePhi
  rw [ENNReal.toReal_div]
  rw [lemma7DeadlineFactor_toReal, lemma7DeadlineW_toReal]
  have hbpos : (0 : ℝ) < (β : ℝ) + 1 := by positivity
  field_simp [hbpos.ne']
  ring

/-- A loose quadratic upper envelope for the deadline contraction factor on
the paper range `1 < β ≤ 2`. -/
theorem lemma7DeadlinePhi_le_expBase
    (β : NNReal) (hβgt : (1 : NNReal) < β) (hβ2 : β ≤ 2) :
    lemma7DeadlinePhi β ≤
      ENNReal.ofReal (1 - (((β : ℝ) - 1) ^ 2 / 18)) := by
  have htop : lemma7DeadlinePhi β ≠ ⊤ := by
    unfold lemma7DeadlinePhi lemma7DeadlineFactor lemma7UpProb lemma7DownProb
      lemma7DeadlineW
    finiteness
  have hβR1 : (1 : ℝ) ≤ β := by exact_mod_cast (le_of_lt hβgt)
  have hβR2 : (β : ℝ) ≤ 2 := by exact_mod_cast hβ2
  have hnonneg : 0 ≤ 1 - (((β : ℝ) - 1) ^ 2 / 18) := by
    have hs : ((β : ℝ) - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((β : ℝ) - 1)]
    nlinarith
  rw [← ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top]
  rw [lemma7DeadlinePhi_toReal, ENNReal.toReal_ofReal hnonneg]
  have hden : 2 * (((β : ℝ) + 1) ^ 2) ≤ 18 := by
    nlinarith [sq_nonneg ((β : ℝ) + 1)]
  have hfrac :
      (((β : ℝ) - 1) ^ 2 / 18) ≤
        (((β : ℝ) - 1) ^ 2 / (2 * (((β : ℝ) + 1) ^ 2))) := by
    apply div_le_div_of_nonneg_left
    · positivity
    · positivity
    · exact hden
  linarith

/-- The potential gain from starting `P` levels below the target is
exponentially bounded on the paper range. -/
theorem lemma7DeadlineW_inv_pow_le_exp
    (β : NNReal) (P : ℕ) (hβgt : (1 : NNReal) < β) :
    (lemma7DeadlineW β ^ P)⁻¹ ≤
      ENNReal.ofReal (Real.exp ((P : ℝ) * ((β : ℝ) - 1))) := by
  have hw0 : lemma7DeadlineW β ≠ 0 := lemma7DeadlineW_ne_zero β
  have hleftTop : (lemma7DeadlineW β ^ P)⁻¹ ≠ ⊤ := by
    exact ENNReal.inv_ne_top.mpr (pow_ne_zero P hw0)
  rw [← ENNReal.toReal_le_toReal hleftTop ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, lemma7DeadlineW_toReal]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hβR : (1 : ℝ) ≤ β := by exact_mod_cast (le_of_lt hβgt)
  have hbase :
      ((2 : ℝ) / ((β : ℝ) + 1))⁻¹ ≤ Real.exp ((β : ℝ) - 1) := by
    have hdenpos : 0 < (β : ℝ) + 1 := by positivity
    have hbaseeq :
        ((2 : ℝ) / ((β : ℝ) + 1))⁻¹ = ((β : ℝ) + 1) / 2 := by
      field_simp [hdenpos.ne']
    rw [hbaseeq]
    have hlin : ((β : ℝ) + 1) / 2 ≤ 1 + ((β : ℝ) - 1) := by
      linarith
    exact hlin.trans
      (by simpa [add_comm] using Real.add_one_le_exp ((β : ℝ) - 1))
  calc
    (((2 : ℝ) / ((β : ℝ) + 1)) ^ P)⁻¹ =
        (((2 : ℝ) / ((β : ℝ) + 1))⁻¹) ^ P := by
      rw [inv_pow]
    _ ≤ (Real.exp ((β : ℝ) - 1)) ^ P := by
      exact pow_le_pow_left₀ (by positivity) hbase P
    _ = Real.exp ((P : ℝ) * ((β : ℝ) - 1)) := by
      rw [← Real.exp_nat_mul]

/-- Exact cancellation of the starting potential against the target potential. -/
theorem lemma7DeadlineW_pow_cancel
    (w : ℝ≥0∞) (x P : ℕ) (hw0 : w ≠ 0) (hwt : w ≠ ⊤) :
    w ^ x / w ^ (x + P) = (w ^ P)⁻¹ := by
  rw [pow_add]
  conv_lhs =>
    lhs
    rw [← mul_one (w ^ x)]
  rw [ENNReal.mul_div_mul_left (c := w ^ x) (a := 1) (b := w ^ P)
    (pow_ne_zero x hw0) (ENNReal.pow_ne_top hwt)]
  simp

/-- Existence of an integer productive deadline of order `P/(β-1)`. -/
theorem lemma7PaperDeadline_exists
    (β : NNReal) (P : ℕ) (hβgt : (1 : NNReal) < β) :
    ∃ T : ℕ, 4096 * (P : ℝ) ≤ ((β : ℝ) - 1) * (T : ℝ) := by
  let c : ℝ := (4096 * (P : ℝ)) / ((β : ℝ) - 1)
  obtain ⟨T, hT⟩ := exists_nat_ge c
  refine ⟨T, ?_⟩
  have hβgtR : (1 : ℝ) < β := by exact_mod_cast hβgt
  have htpos : 0 < (β : ℝ) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hT htpos.le
  have hceq : ((β : ℝ) - 1) * c = 4096 * (P : ℝ) := by
    dsimp [c]
    field_simp [htpos.ne']
  nlinarith

/-- Explicit paper-facing productive deadline, chosen as the least integer
satisfying `(β-1)T ≥ 4096P`. -/
noncomputable def lemma7PaperDeadline (β : NNReal) (P : ℕ) : ℕ :=
  if hβ : (1 : NNReal) < β then
    Nat.find (lemma7PaperDeadline_exists β P hβ)
  else 0

theorem lemma7PaperDeadline_budget
    (β : NNReal) (P : ℕ) (hβgt : (1 : NNReal) < β) :
    4096 * (P : ℝ) ≤
      ((β : ℝ) - 1) * (lemma7PaperDeadline β P : ℝ) := by
  unfold lemma7PaperDeadline
  rw [dif_pos hβgt]
  exact Nat.find_spec (lemma7PaperDeadline_exists β P hβgt)

/-- The deadline branch of `lemma7` fits the same paper exponential envelope. -/
theorem lemma7_deadline_product_le_exp
    (β : NNReal) (P d T : ℕ)
    (hβgt : (1 : NNReal) < β) (hβ2 : β ≤ 2) (hdP : d ≤ P)
    (hbudget : 4096 * (P : ℝ) ≤ ((β : ℝ) - 1) * (T : ℝ)) :
    lemma7DeadlinePhi β ^ T * (lemma7DeadlineW β ^ P)⁻¹ ≤
      ENNReal.ofReal
        (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) := by
  let t : ℝ := (β : ℝ) - 1
  let δ : ℝ := t ^ 2 / 18
  have hβR1 : (1 : ℝ) ≤ β := by exact_mod_cast (le_of_lt hβgt)
  have hβR2 : (β : ℝ) ≤ 2 := by exact_mod_cast hβ2
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    have hs : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    nlinarith
  have hphi :
      lemma7DeadlinePhi β ^ T ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) := by
    refine enn_pow_le_ofReal_exp (lemma7DeadlinePhi β) δ T hδ0 hδ1 ?_
    dsimp [δ, t]
    simpa only [div_eq_mul_inv] using
      lemma7DeadlinePhi_le_expBase β hβgt hβ2
  have hwinv := lemma7DeadlineW_inv_pow_le_exp β P hβgt
  calc
    lemma7DeadlinePhi β ^ T * (lemma7DeadlineW β ^ P)⁻¹ ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) *
          ENNReal.ofReal (Real.exp ((P : ℝ) * t)) := by
      exact mul_le_mul hphi hwinv bot_le bot_le
    _ = ENNReal.ofReal
        (Real.exp (-(δ * (T : ℝ)) + (P : ℝ) * t)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_add]
    _ ≤ ENNReal.ofReal
        (Real.exp (-(t * (d : ℝ) / 4096))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hbudget' : 4096 * (P : ℝ) ≤ t * (T : ℝ) := by
        simpa [t] using hbudget
      have hδT : 2 * (P : ℝ) * t ≤ δ * (T : ℝ) := by
        calc
          2 * (P : ℝ) * t ≤ (4096 / 18) * (P : ℝ) * t := by
            nlinarith [mul_nonneg (show 0 ≤ (P : ℝ) by positivity) ht0]
          _ = t * (4096 * (P : ℝ)) / 18 := by ring
          _ ≤ t * (t * (T : ℝ)) / 18 := by gcongr
          _ = δ * (T : ℝ) := by
            dsimp [δ]
            ring
      have hdP' : (d : ℝ) ≤ (P : ℝ) := by exact_mod_cast hdP
      have htarget : t * (d : ℝ) / 4096 ≤ (P : ℝ) * t := by
        have hdmul : (d : ℝ) * t ≤ (P : ℝ) * t := by gcongr
        have hdt0 : 0 ≤ (d : ℝ) * t := by positivity
        nlinarith
      nlinarith

/-- The escape branch of `lemma7` fits the paper exponential envelope. -/
theorem lemma7_escape_le_exp
    (β : NNReal) (d : ℕ)
    (hβgt : (1 : NNReal) < β) (hβ2 : β ≤ 2) :
    ((β : ℝ≥0∞)⁻¹) ^ (d + 1) ≤
      ENNReal.ofReal
        (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) := by
  have hβpos : (0 : NNReal) < β := lt_trans zero_lt_one hβgt
  rw [relaxedRuin_error_eq_exp β (d + 1) hβpos]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hβRpos : 0 < (β : ℝ) := by positivity
  have hβR1 : (1 : ℝ) ≤ β := by exact_mod_cast (le_of_lt hβgt)
  have hβR2 : (β : ℝ) ≤ 2 := by exact_mod_cast hβ2
  let t : ℝ := (β : ℝ) - 1
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hlogLower : t / 2 ≤ Real.log (β : ℝ) := by
    have hbase : 1 - ((β : ℝ)⁻¹) ≤ Real.log (β : ℝ) :=
      Real.one_sub_inv_le_log_of_pos hβRpos
    have hhalf : t / 2 ≤ 1 - ((β : ℝ)⁻¹) := by
      dsimp [t]
      field_simp [hβRpos.ne']
      nlinarith
    exact hhalf.trans hbase
  have htarget :
      t * (d : ℝ) / 4096 ≤
        ((d + 1 : ℕ) : ℝ) * Real.log (β : ℝ) := by
    have hdt0 : 0 ≤ (d : ℝ) * t := by positivity
    have hsmall : t * (d : ℝ) / 4096 ≤ (d : ℝ) * (t / 2) := by
      nlinarith
    have hmid : (d : ℝ) * (t / 2) ≤
        (d : ℝ) * Real.log (β : ℝ) := by
      gcongr
    have hlog0 : 0 ≤ Real.log (β : ℝ) := by
      exact (show (0 : ℝ) ≤ t / 2 by positivity).trans hlogLower
    have hlast :
        (d : ℝ) * Real.log (β : ℝ) ≤
          ((d + 1 : ℕ) : ℝ) * Real.log (β : ℝ) := by
      gcongr
      exact_mod_cast (Nat.le_succ d)
    exact (hsmall.trans hmid).trans hlast
  nlinarith

/-- **Paper Lemma 7 wrapper.**  Starting `P` minority molecules from the
target and with safety buffer `d`, the productive-time failure probability by
the explicit deadline `lemma7PaperDeadline β P` is bounded by
`2 exp(-((β-1)d)/4096)`.

The paper's rate condition is carried in cleared additive form:
`xLo + d = x₀` and `β(P+d) ≤ r.fire*xLo`; this supplies the live guard
`β*y ≤ α*x` throughout the protected band without exposing any natural-number
subtraction in the statement. -/
theorem lemma7_paper
    (r : RelaxedRate) (β : NNReal) (n P d x₀ xLo : ℕ)
    (h3 : 3 ≤ n) (hroom : P + d < n)
    (hβgt : (1 : NNReal) < β) (hβ2 : β ≤ 2)
    (hpop : x₀ + P = n) (hxLo : xLo + d = x₀)
    (hdP : d ≤ P) (hfire : 0 < r.fire)
    (hrate :
      β * (((P + d : ℕ) : NNReal)) ≤
        r.fire * ((xLo : ℕ) : NNReal)) :
    terminalFailureMass
        (iter
          (freeze (Lemma7Target n) (relaxedProductiveTriChain r n))
          (lemma7PaperDeadline β P) x₀)
        (Lemma7Target n) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) := by
  classical
  let T := lemma7PaperDeadline β P
  have hx₀n : x₀ ≤ n := by omega
  have hstart :
      phase3Level n x₀ = lemma7EscapeBound n P d + (d + 1) := by
    unfold phase3Level lemma7EscapeBound
    have hnlt : ¬ n < x₀ := by omega
    simp [hnlt]
    omega
  have hguard :
      ∀ a b : ℕ, a + b + 2 = n → ¬ Lemma7Stop n P d (a + 1) →
        β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal) := by
    intro a b hstate hstop
    have hy_le : b + 1 ≤ P + d := by
      unfold Lemma7Stop Lemma7Target Lemma7Escape at hstop
      push Not at hstop
      omega
    have hxlo_le : xLo ≤ a + 1 := by
      unfold Lemma7Stop Lemma7Target Lemma7Escape at hstop
      push Not at hstop
      omega
    calc
      β * (b + 1 : NNReal) ≤
          β * (((P + d : ℕ) : NNReal)) := by
        exact mul_le_mul_left' (by exact_mod_cast hy_le) β
      _ ≤ r.fire * ((xLo : ℕ) : NNReal) := hrate
      _ ≤ r.fire * (a + 1 : NNReal) := by
        exact mul_le_mul_left' (by exact_mod_cast hxlo_le) r.fire
  have hprodLive :
      ∀ a b : ℕ, (hpop' : a + b + 2 = n) → ¬ Lemma7Stop n P d (a + 1) →
        relaxedTriStep r (a + 1) (b + 1) (by omega) a +
            relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) ≠ 0 := by
    intro a b hstate _ hzero
    have hlower :=
      relaxed_productive_mass_ge_interior r a b n h3 hstate
    have hfireE0 : (r.fire : ℝ≥0∞) ≠ 0 := by
      simpa [ENNReal.coe_eq_zero] using (ne_of_gt hfire)
    have hthreeDiv0 :
        ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) ≠ 0 := by
      exact ne_of_gt
        (ENNReal.div_pos (by norm_num) (ENNReal.natCast_ne_top n))
    have hleftpos :
        0 < (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) :=
      ENNReal.mul_pos hfireE0 hthreeDiv0
    have hle0 :
        (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) ≤ 0 := by
      simpa [hzero] using hlower
    exact (not_le_of_gt hleftpos) hle0
  have hengine :=
    lemma7 r β n P d x₀ T (d + 1)
      h3 hroom hβgt hβ2 hx₀n hstart hguard hprodLive
  have herr :
      ENNReal.ofReal
          (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) +
        ENNReal.ofReal
          (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) =
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) := by
    ring
  calc
    terminalFailureMass
        (iter (freeze (Lemma7Target n) (relaxedProductiveTriChain r n)) T x₀)
        (Lemma7Target n) ≤
      ((β : ℝ≥0∞)⁻¹) ^ (d + 1) +
        lemma7DeadlinePhi β ^ T *
          (if Lemma7Stop n P d x₀ then 0 else lemma7DeadlineW β ^ x₀) /
            lemma7DeadlineW β ^ n := hengine
    _ ≤ ENNReal.ofReal
          (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) +
        ENNReal.ofReal
          (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) := by
      apply add_le_add
      · exact lemma7_escape_le_exp β d hβgt hβ2
      · calc
          lemma7DeadlinePhi β ^ T *
              (if Lemma7Stop n P d x₀ then 0 else lemma7DeadlineW β ^ x₀) /
                lemma7DeadlineW β ^ n ≤
            lemma7DeadlinePhi β ^ T * lemma7DeadlineW β ^ x₀ /
                lemma7DeadlineW β ^ n := by
              gcongr
              split <;> simp
          _ = lemma7DeadlinePhi β ^ T *
              (lemma7DeadlineW β ^ P)⁻¹ := by
            rw [← hpop]
            rw [mul_div_assoc]
            rw [lemma7DeadlineW_pow_cancel (lemma7DeadlineW β) x₀ P
              (lemma7DeadlineW_ne_zero β) (lemma7DeadlineW_ne_top β)]
          _ ≤ ENNReal.ofReal
              (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) :=
            lemma7_deadline_product_le_exp β P d T hβgt hβ2 hdP
              (by simpa [T] using lemma7PaperDeadline_budget β P hβgt)
    _ = (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((β : ℝ) - 1) * (d : ℝ) / 4096))) := herr

example :
    terminalFailureMass
        (iter
          (freeze (Lemma7Target 4)
            (relaxedProductiveTriChain
              ({ fire := 1, idle := 0, add_eq_one := by norm_num } :
                RelaxedRate) 4))
          (lemma7PaperDeadline (2 : NNReal) 1) 3)
        (Lemma7Target 4) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((((2 : NNReal) : ℝ) - 1) * (0 : ℝ) / 4096))) := by
  simpa using
    lemma7_paper
      ({ fire := 1, idle := 0, add_eq_one := by norm_num } : RelaxedRate)
      (2 : NNReal) 4 1 0 3 3
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

end Tri

#print axioms Tri.relaxed_down_mass_ge
#print axioms Tri.lemma7_freeze_congr
#print axioms Tri.lemma7_terminalFailureMass_congr
#print axioms Tri.lemma7_hitProb_congr
#print axioms Tri.lemma7_prob_sum
#print axioms Tri.lemma7DownProb_eq
#print axioms Tri.lemma7DeadlineW_le_one
#print axioms Tri.lemma7DeadlineW_sq_le_one
#print axioms Tri.lemma7_deadline_scalar_step
#print axioms Tri.lemma7_feller_scalar_step
#print axioms Tri.expect_relaxedProductiveTriInterior
#print axioms Tri.relaxedProductiveTriInterior_masses
#print axioms Tri.relaxedProductiveTriChain_apply
#print axioms Tri.relaxedProductiveTriChain_support_le
#print axioms Tri.lemma7_live_interior
#print axioms Tri.lemma7DeadlineW_ne_zero
#print axioms Tri.lemma7DeadlineW_ne_top
#print axioms Tri.lemma7DeadlinePhi_mul_w
#print axioms Tri.lemma7_stopped_potential_step
#print axioms Tri.lemma7_deadline_branch
#print axioms Tri.lemma7Level_le_iff
#print axioms Tri.lemma7_feller_hfroz_stop
#print axioms Tri.lemma7_escape_branch
#print axioms Tri.lemma7
#print axioms Tri.lemma7DeadlinePhi_toReal
#print axioms Tri.lemma7PaperDeadline_budget
#print axioms Tri.lemma7_deadline_product_le_exp
#print axioms Tri.lemma7_escape_le_exp
#print axioms Tri.lemma7_paper
