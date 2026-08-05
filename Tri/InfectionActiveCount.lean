/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivationBand

/-!
# Counting all-active infection interactions

This counted kernel is frozen once the active population exceeds a cap `A`.
While live, the exact increment probability is
`C(active,3) / C(n,3)`, hence at most `C(A,3) / C(n,3)`.
-/

namespace Tri

open scoped ENNReal

namespace InfectionEvent

def allActiveInc : InfectionEvent → ℕ
  | .activeXXX
  | .activeXXY
  | .activeXYY
  | .activeYYY => 1
  | .activateOneX
  | .activateOneY
  | .activateTwoXX
  | .activateTwoXY
  | .activateTwoYY
  | .inactiveOnly => 0

def productiveActiveInc : InfectionEvent → ℕ
  | .activeXXY
  | .activeXYY => 1
  | .activeXXX
  | .activeYYY
  | .activateOneX
  | .activateOneY
  | .activateTwoXX
  | .activateTwoXY
  | .activateTwoYY
  | .inactiveOnly => 0

theorem productiveActiveInc_le_allActiveInc (e : InfectionEvent) :
    e.productiveActiveInc ≤ e.allActiveInc := by
  cases e <;> simp [productiveActiveInc, allActiveInc]

end InfectionEvent

noncomputable def infectionAllActiveMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionEventPMF s h .activeXXX +
    infectionEventPMF s h .activeXXY +
    infectionEventPMF s h .activeXYY +
    infectionEventPMF s h .activeYYY

noncomputable def infectionNotAllActiveMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionActivationMass s h + infectionEventPMF s h .inactiveOnly

theorem infectionAllActiveMass_eq
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionAllActiveMass s h =
      (Nat.choose s.active 3 : ℝ≥0∞) /
        (Nat.choose s.total 3 : ℝ≥0∞) := by
  unfold infectionAllActiveMass
  rw [infectionEventPMF_apply, infectionEventPMF_apply,
    infectionEventPMF_apply, infectionEventPMF_apply]
  simp only [InfectionEvent.weight, InfectionCfg.active]
  rw [choose_three_split s.ax s.ay]
  simp only [div_eq_mul_inv]
  push_cast
  ring

theorem infectionAllActiveMasses_sum
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionAllActiveMass s h + infectionNotAllActiveMass s h = 1 := by
  simpa [infectionAllActiveMass, infectionNotAllActiveMass,
    infectionNoActivationMass, add_assoc, add_left_comm, add_comm] using
    infectionActivationMasses_sum s h

noncomputable def infectionAllActiveCap (n A : ℕ) : ℝ≥0∞ :=
  (Nat.choose A 3 : ℝ≥0∞) / (Nat.choose n 3 : ℝ≥0∞)

noncomputable def infectionAllActiveCapCompl (n A : ℕ) : ℝ≥0∞ :=
  1 - infectionAllActiveCap n A

theorem infectionAllActiveCap_le_one
    (n A : ℕ) (h3 : 3 ≤ n) (hA : A ≤ n) :
    infectionAllActiveCap n A ≤ 1 := by
  have hchoose : Nat.choose A 3 ≤ Nat.choose n 3 :=
    Nat.choose_le_choose 3 hA
  have hden0 : ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (choose_three_pos h3).ne'
  have hdenTop : ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    infectionAllActiveCap n A ≤
        (Nat.choose n 3 : ℝ≥0∞) / (Nat.choose n 3 : ℝ≥0∞) := by
      unfold infectionAllActiveCap
      exact ENNReal.div_le_div_right (by exact_mod_cast hchoose) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

theorem infectionAllActiveCap_add_compl
    (n A : ℕ) (h3 : 3 ≤ n) (hA : A ≤ n) :
    infectionAllActiveCap n A + infectionAllActiveCapCompl n A = 1 := by
  unfold infectionAllActiveCapCompl
  rw [add_comm]
  exact tsub_add_cancel_of_le (infectionAllActiveCap_le_one n A h3 hA)

theorem infectionAllActiveMass_le_cap
    (n A : ℕ) (h3 : 3 ≤ n) (s : InfectionState n)
    (hactive : s.1.active ≤ A) :
    infectionAllActiveMass s.1 (by
      have hs := s.2
      simp only [InfectionCfg.Inv] at hs
      omega) ≤ infectionAllActiveCap n A := by
  rw [infectionAllActiveMass_eq]
  have htotal : s.1.total = n := s.2
  rw [htotal]
  unfold infectionAllActiveCap
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.choose_le_choose 3 hactive

noncomputable def infectionAllActiveStop
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ) :
    InfectionState n → PMF (InfectionState n) :=
  freeze (fun s : InfectionState n => A < s.1.active)
    (infectionStateStep n h3)

noncomputable def infectionAllActiveCount
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ) :
    InfectionState n × ℕ → PMF (InfectionState n × ℕ) := fun q =>
  if A < q.1.1.active then
    PMF.pure q
  else
    (infectionEventPMF q.1.1 (by
      have hs := q.1.2
      simp only [InfectionCfg.Inv] at hs
      omega)).map (fun e =>
        (InfectionEvent.nextState q.1 e, q.2 + e.allActiveInc))

theorem infectionAllActiveCount_map_fst
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ)
    (q : InfectionState n × ℕ) :
    (infectionAllActiveCount n h3 A q).map Prod.fst =
      infectionAllActiveStop n h3 A q.1 := by
  by_cases hstop : A < q.1.1.active
  · rw [infectionAllActiveCount, if_pos hstop,
      infectionAllActiveStop, freeze_of_mem q.1 hstop]
    exact PMF.pure_map Prod.fst q
  · rw [infectionAllActiveCount, if_neg hstop,
      infectionAllActiveStop, freeze_of_not_mem q.1 hstop]
    unfold infectionStateStep
    rw [PMF.map_comp]
    rfl

theorem infectionAllActiveCount_decomp
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ)
    (s : InfectionState n) (c : ℕ)
    (hlive : ¬ A < s.1.active) (w : ℝ≥0∞) :
    expect (infectionAllActiveCount n h3 A (s, c))
        (fun q => w ^ q.2) =
      infectionNotAllActiveMass s.1 (by
        have hs := s.2
        simp only [InfectionCfg.Inv] at hs
        omega) * w ^ c +
      infectionAllActiveMass s.1 (by
        have hs := s.2
        simp only [InfectionCfg.Inv] at hs
        omega) * w ^ (c + 1) := by
  unfold infectionAllActiveCount
  rw [if_neg hlive, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset InfectionEvent) =
    {InfectionEvent.activeXXX, InfectionEvent.activeXXY,
      InfectionEvent.activeXYY, InfectionEvent.activeYYY,
      InfectionEvent.activateOneX, InfectionEvent.activateOneY,
      InfectionEvent.activateTwoXX, InfectionEvent.activateTwoXY,
      InfectionEvent.activateTwoYY, InfectionEvent.inactiveOnly} from rfl]
  simp [InfectionEvent.allActiveInc, infectionAllActiveMass,
    infectionNotAllActiveMass, infectionActivationMass,
    infectionActivationOneMass, infectionActivationTwoMass]
  ring

variable {α : Type*}

theorem upper_step_factor_monotone
    {p p' q q' w : ℝ}
    (hp : p + p' = 1) (hq : q + q' = 1)
    (hw : 1 ≤ w) (hqp : q ≤ p) :
    q' + q * w ≤ p' + p * w := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hqp) (sub_nonneg.mpr hw)]

theorem upper_step_factor_monotone_ennreal
    {p p' q q' w : ℝ≥0∞}
    (hp : p + p' = 1) (hq : q + q' = 1)
    (hw : 1 ≤ w) (hqp : q ≤ p) (hwt : w ≠ ⊤) :
    q' + q * w ≤ p' + p * w := by
  have hple : p ≤ 1 := by rw [← hp]; exact le_add_right le_rfl
  have hp'le : p' ≤ 1 := by rw [← hp]; exact le_add_left le_rfl
  have hqle : q ≤ 1 := by rw [← hq]; exact le_add_right le_rfl
  have hq'le : q' ≤ 1 := by rw [← hq]; exact le_add_left le_rfl
  have fp : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hple
  have fp' : p' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp'le
  have fq : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hqle
  have fq' : q' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq'le
  rw [← ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨fq', ENNReal.mul_ne_top fq hwt⟩)
    (ENNReal.add_ne_top.mpr ⟨fp', ENNReal.mul_ne_top fp hwt⟩)]
  rw [ENNReal.toReal_add fq' (ENNReal.mul_ne_top fq hwt),
    ENNReal.toReal_add fp' (ENNReal.mul_ne_top fp hwt),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  apply upper_step_factor_monotone
  · have := congrArg ENNReal.toReal hp
    rwa [ENNReal.toReal_add fp fp', ENNReal.toReal_one] at this
  · have := congrArg ENNReal.toReal hq
    rwa [ENNReal.toReal_add fq fq', ENNReal.toReal_one] at this
  · simpa using
      (ENNReal.toReal_le_toReal ENNReal.one_ne_top hwt).mpr hw
  · exact (ENNReal.toReal_le_toReal fq fp).mpr hqp

theorem count_upper_tail
    (K : α → PMF α) (count : α → ℕ) (w φ : ℝ≥0∞)
    (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (hstep : ∀ s,
      expect (K s) (fun z => w ^ count z) ≤ φ * w ^ count s)
    (T m : ℕ) (s0 : α) :
    ∑' z, (if m ≤ count z then iter K T s0 z else 0) ≤
      φ ^ T * w ^ count s0 / w ^ m := by
  have hw0 : w ≠ 0 := by
    intro hwz
    rw [hwz] at hw1
    simp at hw1
  let theta : ℝ≥0∞ := w ^ m
  have htheta0 : theta ≠ 0 := pow_ne_zero _ hw0
  have hthetatop : theta ≠ ⊤ := ENNReal.pow_ne_top hwt
  have hsub : ∀ z,
      (if m ≤ count z then iter K T s0 z else 0) ≤
        (if theta ≤ w ^ count z then iter K T s0 z else 0) := by
    intro z
    by_cases hz : m ≤ count z
    · have hpow : theta ≤ w ^ count z := by
        dsimp only [theta]
        exact pow_le_pow_right₀ hw1 hz
      simp [hz, hpow]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div (iter K T s0) (fun z => w ^ count z)
      theta htheta0 hthetatop) ?_
  exact ENNReal.div_le_div_right
    (expect_iter_le K (fun z => w ^ count z) φ hstep T s0) theta

theorem count_upper_tail_bernoulli
    (K : α → PMF α) (count : α → ℕ)
    (w p p' : ℝ≥0∞)
    (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (hstep : ∀ s,
      expect (K s) (fun z => w ^ count z) ≤
        (p' + p * w) * w ^ count s)
    (T m : ℕ) (s0 : α) :
    ∑' z, (if m ≤ count z then iter K T s0 z else 0) ≤
      (p' + p * w) ^ T * w ^ count s0 / w ^ m :=
  count_upper_tail K count w (p' + p * w) hw1 hwt hstep T m s0

theorem infectionAllActiveCount_step
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ) (hA : A ≤ n)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤) :
    ∀ q,
      expect (infectionAllActiveCount n h3 A q)
          (fun z => w ^ z.2) ≤
        (infectionAllActiveCapCompl n A +
            infectionAllActiveCap n A * w) * w ^ q.2 := by
  rintro ⟨s, c⟩
  have hcapSum := infectionAllActiveCap_add_compl n A h3 hA
  by_cases hstop : A < s.1.active
  · rw [infectionAllActiveCount, if_pos hstop, expect_pure]
    have hfactor :
        1 ≤ infectionAllActiveCapCompl n A +
          infectionAllActiveCap n A * w := by
      have hmono := upper_step_factor_monotone_ennreal
        (p := infectionAllActiveCap n A)
        (p' := infectionAllActiveCapCompl n A)
        (q := 0) (q' := 1) (w := w)
        hcapSum (by simp) hw1 bot_le hwt
      simpa using hmono
    calc
      w ^ c = 1 * w ^ c := by rw [one_mul]
      _ ≤ (infectionAllActiveCapCompl n A +
          infectionAllActiveCap n A * w) * w ^ c :=
        by simpa [mul_comm] using
          (mul_le_mul_right hfactor (w ^ c))
  · let hs3 : 3 ≤ s.1.total := by
      have hs := s.2
      simp only [InfectionCfg.Inv] at hs
      omega
    let q := infectionAllActiveMass s.1 hs3
    let q' := infectionNotAllActiveMass s.1 hs3
    have hqsum : q + q' = 1 := by
      dsimp only [q, q']
      exact infectionAllActiveMasses_sum s.1 hs3
    have hqcap : q ≤ infectionAllActiveCap n A := by
      dsimp only [q]
      apply infectionAllActiveMass_le_cap n A h3 s
      omega
    have hfactor :
        q' + q * w ≤ infectionAllActiveCapCompl n A +
          infectionAllActiveCap n A * w :=
      upper_step_factor_monotone_ennreal hcapSum hqsum hw1 hqcap hwt
    rw [infectionAllActiveCount_decomp n h3 A s c hstop w]
    change q' * w ^ c + q * w ^ (c + 1) ≤
      (infectionAllActiveCapCompl n A +
        infectionAllActiveCap n A * w) * w ^ c
    calc
      q' * w ^ c + q * w ^ (c + 1)
          = (q' + q * w) * w ^ c := by
            rw [pow_succ]
            ring
      _ ≤ (infectionAllActiveCapCompl n A +
          infectionAllActiveCap n A * w) * w ^ c :=
        by simpa [mul_comm] using
          (mul_le_mul_right hfactor (w ^ c))

theorem infectionAllActiveCount_tail
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ) (hA : A ≤ n)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (T M c0 : ℕ) (s0 : InfectionState n) :
    ∑' q, (if M ≤ q.2 then
        iter (infectionAllActiveCount n h3 A) T (s0, c0) q else 0) ≤
      (infectionAllActiveCapCompl n A +
          infectionAllActiveCap n A * w) ^ T * w ^ c0 / w ^ M := by
  exact count_upper_tail_bernoulli
    (infectionAllActiveCount n h3 A) Prod.snd
    w (infectionAllActiveCap n A) (infectionAllActiveCapCompl n A)
    hw1 hwt
    (infectionAllActiveCount_step n h3 A hA w hw1 hwt)
    T M (s0, c0)

theorem infectionAllActiveCount_tail_zero
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ) (hA : A ≤ n)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (T M : ℕ) (s0 : InfectionState n) :
    ∑' q, (if M ≤ q.2 then
        iter (infectionAllActiveCount n h3 A) T (s0, 0) q else 0) ≤
      (infectionAllActiveCapCompl n A +
          infectionAllActiveCap n A * w) ^ T / w ^ M := by
  simpa using infectionAllActiveCount_tail
    n h3 A hA w hw1 hwt T M 0 s0

end Tri

#print axioms Tri.infectionAllActiveMass_eq
#print axioms Tri.infectionAllActiveCount_map_fst
#print axioms Tri.upper_step_factor_monotone_ennreal
#print axioms Tri.count_upper_tail
#print axioms Tri.infectionAllActiveCount_step
#print axioms Tri.infectionAllActiveCount_tail_zero
