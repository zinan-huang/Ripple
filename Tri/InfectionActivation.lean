/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionHandoff
import Tri.Progress

/-!
# Activation-count dynamics for infection-initiated Tri

This file isolates the epidemic clock from all `X`/`Y` label concentration.
A mixed interaction activates one or two inactive molecules; active-only and
inactive-only triples activate none.
-/

namespace Tri

open scoped ENNReal

namespace InfectionEvent

/-- Number of inactive molecules activated by an event class. -/
def activationInc : InfectionEvent → ℕ
  | .activateOneX
  | .activateOneY => 1
  | .activateTwoXX
  | .activateTwoXY
  | .activateTwoYY => 2
  | .activeXXX
  | .activeXXY
  | .activeXYY
  | .activeYYY
  | .inactiveOnly => 0

/-- Impossible zero-weight labels contribute no realized activation. -/
def realizedActivationInc (s : InfectionCfg) (e : InfectionEvent) : ℕ :=
  if InfectionEvent.weight s e = 0 then 0 else e.activationInc

/-- Every positive-weight event removes exactly its activation increment from
the inactive population. -/
theorem next_inactive_add_activationInc
    (s : InfectionCfg) (e : InfectionEvent)
    (he : InfectionEvent.weight s e ≠ 0) :
    (InfectionEvent.next s e).inactive + e.activationInc =
      s.inactive := by
  rcases s with ⟨ax, ay, ix, iy⟩
  cases e with
  | activeXXX =>
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
  | activeXXY =>
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
  | activeXYY =>
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
  | activeYYY =>
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
  | activateOneX =>
      have hix : ix ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa [InfectionEvent.weight, InfectionCfg.active] using he)).2
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
      omega
  | activateOneY =>
      have hiy : iy ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (by
          simpa [InfectionEvent.weight, InfectionCfg.active] using he)).2
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
      omega
  | activateTwoXX =>
      have hprod : (ax + ay) * Nat.choose ix 2 ≠ 0 := by
        simpa [InfectionEvent.weight, InfectionCfg.active] using he
      have hchoose : Nat.choose ix 2 ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp hprod).2
      have hix : 2 ≤ ix := Nat.choose_ne_zero_iff.mp hchoose
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
      omega
  | activateTwoXY =>
      have hmul : (ax + ay) * ix * iy ≠ 0 := by
        simpa [InfectionEvent.weight, InfectionCfg.active] using he
      have hix : ix ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp (Nat.mul_ne_zero_iff.mp hmul).1).2
      have hiy : iy ≠ 0 := (Nat.mul_ne_zero_iff.mp hmul).2
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
      omega
  | activateTwoYY =>
      have hprod : (ax + ay) * Nat.choose iy 2 ≠ 0 := by
        simpa [InfectionEvent.weight, InfectionCfg.active] using he
      have hchoose : Nat.choose iy 2 ≠ 0 :=
        (Nat.mul_ne_zero_iff.mp hprod).2
      have hiy : 2 ≤ iy := Nat.choose_ne_zero_iff.mp hchoose
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]
      omega
  | inactiveOnly =>
      simp [InfectionEvent.next, activationInc, InfectionCfg.inactive]

/-- The guarded subtype update has the same exact inactive decrement. -/
theorem nextState_inactive_add_realizedActivationInc
    {n : ℕ} (s : InfectionState n) (e : InfectionEvent) :
    (InfectionEvent.nextState s e).1.inactive +
        realizedActivationInc s.1 e =
      s.1.inactive := by
  by_cases he : InfectionEvent.weight s.1 e = 0
  · rw [InfectionEvent.nextState, dif_pos he,
      realizedActivationInc, if_pos he]
    simp
  · rw [InfectionEvent.nextState, dif_neg he,
      realizedActivationInc, if_neg he]
    exact next_inactive_add_activationInc s.1 e he

/-- The inactive population never increases. -/
theorem nextState_inactive_le
    {n : ℕ} (s : InfectionState n) (e : InfectionEvent) :
    (InfectionEvent.nextState s e).1.inactive ≤ s.1.inactive := by
  have h := nextState_inactive_add_realizedActivationInc s e
  omega

/-- A single interaction activates at most two molecules. -/
theorem realizedActivationInc_le_two
    (s : InfectionCfg) (e : InfectionEvent) :
    realizedActivationInc s e ≤ 2 := by
  unfold realizedActivationInc
  split_ifs
  · simp
  · cases e <;> simp [activationInc]

/-- Complete one-step classification of the inactive update. -/
theorem nextState_inactive_classify
    {n : ℕ} (s : InfectionState n) (e : InfectionEvent) :
    ∃ d : ℕ, d ≤ 2 ∧
      (InfectionEvent.nextState s e).1.inactive + d =
        s.1.inactive := by
  refine ⟨realizedActivationInc s.1 e,
    realizedActivationInc_le_two s.1 e, ?_⟩
  exact nextState_inactive_add_realizedActivationInc s e

/-- Active count increases by the same realized activation increment. -/
theorem nextState_active_eq_add_realizedActivationInc
    {n : ℕ} (s : InfectionState n) (e : InfectionEvent) :
    (InfectionEvent.nextState s e).1.active =
      s.1.active + realizedActivationInc s.1 e := by
  have hs := s.2
  have hn := (InfectionEvent.nextState s e).2
  have hi := nextState_inactive_add_realizedActivationInc s e
  simp only [InfectionCfg.Inv, InfectionCfg.total] at hs hn
  omega

/-- Active count is monotone. -/
theorem active_le_nextState_active
    {n : ℕ} (s : InfectionState n) (e : InfectionEvent) :
    s.1.active ≤ (InfectionEvent.nextState s e).1.active := by
  rw [nextState_active_eq_add_realizedActivationInc]
  exact Nat.le_add_right _ _

end InfectionEvent

/-- Probability of activating exactly one molecule. -/
noncomputable def infectionActivationOneMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionEventPMF s h .activateOneX +
    infectionEventPMF s h .activateOneY

/-- Probability of activating exactly two molecules. -/
noncomputable def infectionActivationTwoMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionEventPMF s h .activateTwoXX +
    infectionEventPMF s h .activateTwoXY +
    infectionEventPMF s h .activateTwoYY

/-- Probability of activating at least one molecule. -/
noncomputable def infectionActivationMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionActivationOneMass s h + infectionActivationTwoMass s h

/-- Probability of no activation. -/
noncomputable def infectionNoActivationMass
    (s : InfectionCfg) (h : 3 ≤ s.total) : ℝ≥0∞ :=
  infectionEventPMF s h .activeXXX +
    infectionEventPMF s h .activeXXY +
    infectionEventPMF s h .activeXYY +
    infectionEventPMF s h .activeYYY +
    infectionEventPMF s h .inactiveOnly

/-- Exact one-activation mass. -/
theorem infectionActivationOneMass_eq
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionActivationOneMass s h =
      ((Nat.choose s.active 2 * s.inactive : ℕ) : ℝ≥0∞) /
        (Nat.choose s.total 3 : ℝ≥0∞) := by
  unfold infectionActivationOneMass
  rw [infectionEventPMF_apply, infectionEventPMF_apply]
  simp only [InfectionEvent.weight, InfectionCfg.active,
    InfectionCfg.inactive, div_eq_mul_inv]
  push_cast
  ring

/-- Exact two-activation mass. -/
theorem infectionActivationTwoMass_eq
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionActivationTwoMass s h =
      ((s.active * Nat.choose s.inactive 2 : ℕ) : ℝ≥0∞) /
        (Nat.choose s.total 3 : ℝ≥0∞) := by
  unfold infectionActivationTwoMass
  rw [infectionEventPMF_apply, infectionEventPMF_apply,
    infectionEventPMF_apply]
  simp only [InfectionEvent.weight, InfectionCfg.active,
    InfectionCfg.inactive]
  rw [← choose_two_add s.ix s.iy]
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-- Exact mixed-interaction activation mass. -/
theorem infectionActivationMass_eq
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionActivationMass s h =
      ((Nat.choose s.active 2 * s.inactive +
          s.active * Nat.choose s.inactive 2 : ℕ) : ℝ≥0∞) /
        (Nat.choose s.total 3 : ℝ≥0∞) := by
  rw [infectionActivationMass,
    infectionActivationOneMass_eq, infectionActivationTwoMass_eq]
  rw [ENNReal.div_add_div_same]
  push_cast
  rfl

/-- Exact no-activation mass. -/
theorem infectionNoActivationMass_eq
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionNoActivationMass s h =
      ((Nat.choose s.active 3 + Nat.choose s.inactive 3 : ℕ) : ℝ≥0∞) /
        (Nat.choose s.total 3 : ℝ≥0∞) := by
  unfold infectionNoActivationMass
  rw [infectionEventPMF_apply, infectionEventPMF_apply,
    infectionEventPMF_apply, infectionEventPMF_apply,
    infectionEventPMF_apply]
  simp only [InfectionEvent.weight, InfectionCfg.active,
    InfectionCfg.inactive]
  rw [choose_three_split s.ax s.ay]
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-- No-activation and activation masses partition one interaction. -/
theorem infectionActivationMasses_sum
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    infectionNoActivationMass s h + infectionActivationMass s h = 1 := by
  rw [infectionNoActivationMass_eq, infectionActivationMass_eq]
  have hnum :
      (Nat.choose s.active 3 + Nat.choose s.inactive 3) +
          (Nat.choose s.active 2 * s.inactive +
            s.active * Nat.choose s.inactive 2) =
        Nat.choose s.total 3 := by
    have hall := choose_three_add s.active s.inactive
    simpa [InfectionCfg.total, add_assoc, add_left_comm, add_comm] using hall
  have hden0 : ((Nat.choose s.total 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (choose_three_pos h).ne'
  have hdenTop : ((Nat.choose s.total 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    ((Nat.choose s.active 3 + Nat.choose s.inactive 3 : ℕ) : ℝ≥0∞) /
          (Nat.choose s.total 3 : ℝ≥0∞) +
        ((Nat.choose s.active 2 * s.inactive +
            s.active * Nat.choose s.inactive 2 : ℕ) : ℝ≥0∞) /
          (Nat.choose s.total 3 : ℝ≥0∞)
      = (((Nat.choose s.active 3 + Nat.choose s.inactive 3) +
          (Nat.choose s.active 2 * s.inactive +
            s.active * Nat.choose s.inactive 2) : ℕ) : ℝ≥0∞) /
          (Nat.choose s.total 3 : ℝ≥0∞) := by
            rw [ENNReal.div_add_div_same]
            push_cast
            rfl
    _ = (Nat.choose s.total 3 : ℝ≥0∞) /
          (Nat.choose s.total 3 : ℝ≥0∞) := by rw [hnum]
    _ = 1 := ENNReal.div_self hden0 hdenTop

/-- Exact expected number of newly activated molecules in one interaction. -/
theorem infection_expected_activationInc
    (s : InfectionCfg) (h : 3 ≤ s.total) :
    expect (infectionEventPMF s h)
        (fun e => (e.activationInc : ℝ≥0∞)) =
      infectionActivationOneMass s h +
        2 * infectionActivationTwoMass s h := by
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset InfectionEvent) =
    {InfectionEvent.activeXXX, InfectionEvent.activeXXY,
      InfectionEvent.activeXYY, InfectionEvent.activeYYY,
      InfectionEvent.activateOneX, InfectionEvent.activateOneY,
      InfectionEvent.activateTwoXX, InfectionEvent.activateTwoXY,
      InfectionEvent.activateTwoYY, InfectionEvent.inactiveOnly} from rfl]
  simp [InfectionEvent.activationInc,
    infectionActivationOneMass, infectionActivationTwoMass]
  ring

/-- Rectangular lower bound for the probability of activation. -/
noncomputable def infectionActivationFloor
    (n aLo iLo : ℕ) : ℝ≥0∞ :=
  ((Nat.choose aLo 2 * iLo + aLo * Nat.choose iLo 2 : ℕ) : ℝ≥0∞) /
    (Nat.choose n 3 : ℝ≥0∞)

/-- The corner activation floor is valid throughout the rectangle. -/
theorem infectionActivationFloor_le
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionState n)
    (aLo iLo : ℕ)
    (ha : aLo ≤ s.1.active) (hi : iLo ≤ s.1.inactive) :
    infectionActivationFloor n aLo iLo ≤
      infectionActivationMass s.1 (by
        have hs := s.2
        simp only [InfectionCfg.Inv] at hs
        omega) := by
  rw [infectionActivationFloor, infectionActivationMass_eq]
  have htotal : s.1.total = n := s.2
  rw [htotal]
  apply ENNReal.div_le_div_right
  exact_mod_cast add_le_add
    (Nat.mul_le_mul (Nat.choose_le_choose 2 ha) hi)
    (Nat.mul_le_mul ha (Nat.choose_le_choose 2 hi))

/-- Physical infection chain stopped after reaching an active-count target. -/
noncomputable def infectionActivationStop
    (n : ℕ) (h3 : 3 ≤ n) (target : ℕ) :
    InfectionState n → PMF (InfectionState n) :=
  freeze (fun s : InfectionState n => target ≤ s.1.active)
    (infectionStateStep n h3)

/-- Counted stopped chain. The counter records molecules activated, with exact
increments zero, one, or two. After success it is advanced artificially by one
so that a global lower-tail contraction remains valid. -/
noncomputable def infectionActivationCount
    (n : ℕ) (h3 : 3 ≤ n) (target : ℕ) :
    InfectionState n × ℕ → PMF (InfectionState n × ℕ) := fun q =>
  if hdone : target ≤ q.1.1.active then
    PMF.pure (q.1, q.2 + 1)
  else
    (infectionEventPMF q.1.1 (by
      have hs := q.1.2
      simp only [InfectionCfg.Inv] at hs
      omega)).map (fun e =>
        (InfectionEvent.nextState q.1 e, q.2 + e.activationInc))

/-- Forgetting the counter gives the physically stopped activation chain. -/
theorem infectionActivationCount_map_fst
    (n : ℕ) (h3 : 3 ≤ n) (target : ℕ)
    (q : InfectionState n × ℕ) :
    (infectionActivationCount n h3 target q).map Prod.fst =
      infectionActivationStop n h3 target q.1 := by
  by_cases hdone : target ≤ q.1.1.active
  · rw [infectionActivationCount, dif_pos hdone,
      infectionActivationStop, freeze_of_mem q.1 hdone]
    exact PMF.pure_map Prod.fst (q.1, q.2 + 1)
  · rw [infectionActivationCount, dif_neg hdone,
      infectionActivationStop, freeze_of_not_mem q.1 hdone]
    unfold infectionStateStep
    rw [PMF.map_comp]
    rfl

/-- Either the target has already been reached, or active molecules and the
activation counter satisfy their exact pathwise ledger. -/
def InfectionActivationAccount
    {n : ℕ} (target initialActive initialCount : ℕ)
    (q : InfectionState n × ℕ) : Prop :=
  target ≤ q.1.1.active ∨
    q.1.1.active + initialCount = initialActive + q.2

/-- The activation account holds at its initial state. -/
theorem infectionActivationAccount_initial
    {n target initialCount : ℕ} (s : InfectionState n) :
    InfectionActivationAccount target s.1.active initialCount
      (s, initialCount) := by
  right
  rfl

/-- One supported counted step preserves the target-or-ledger account. -/
theorem infectionActivationCount_account_of_apply_ne_zero
    {n target initialActive initialCount : ℕ} (h3 : 3 ≤ n)
    (q z : InfectionState n × ℕ)
    (hq : InfectionActivationAccount target initialActive initialCount q)
    (hqz : infectionActivationCount n h3 target q z ≠ 0) :
    InfectionActivationAccount target initialActive initialCount z := by
  by_cases hdone : target ≤ q.1.1.active
  · rw [infectionActivationCount, dif_pos hdone, PMF.pure_apply] at hqz
    by_cases hz : z = (q.1, q.2 + 1)
    · rw [hz]
      exact Or.inl hdone
    · simp [hz] at hqz
  · have hledger :
        q.1.1.active + initialCount = initialActive + q.2 :=
      hq.resolve_left hdone
    unfold infectionActivationCount at hqz
    rw [dif_neg hdone, PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
    push Not at hqz
    obtain ⟨e, he⟩ := hqz
    split_ifs at he with hze
    · have hs3 : 3 ≤ q.1.1.total := by
        have hs := q.1.2
        simp only [InfectionCfg.Inv] at hs
        omega
      have hweight : InfectionEvent.weight q.1.1 e ≠ 0 :=
        fun hw => he (infectionEventPMF_zero_of_weight_zero
          (s := q.1.1) (h := hs3) (e := e) hw)
      rw [hze]
      right
      have hactive :=
        InfectionEvent.nextState_active_eq_add_realizedActivationInc q.1 e
      have hrealized :
          InfectionEvent.realizedActivationInc q.1.1 e =
            e.activationInc := by
        simp [InfectionEvent.realizedActivationInc, hweight]
      rw [hrealized] at hactive
      dsimp only
      omega
    · exact absurd rfl he

/-- The activation account holds throughout every finite counted path. -/
theorem infectionActivationCount_iter_account
    {n target initialActive initialCount T : ℕ} (h3 : 3 ≤ n)
    (q z : InfectionState n × ℕ)
    (hq : InfectionActivationAccount target initialActive initialCount q)
    (hz : iter (infectionActivationCount n h3 target) T q z ≠ 0) :
    InfectionActivationAccount target initialActive initialCount z := by
  induction T generalizing q with
  | zero =>
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = q
      · rwa [h]
      · simp [h] at hz
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply] at hz
      by_contra hzAccount
      apply hz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hqa : infectionActivationCount n h3 target q a = 0
      · simp [hqa]
      · have haAccount :=
          infectionActivationCount_account_of_apply_ne_zero
            h3 q a hq hqa
        have hiaz :
            iter (infectionActivationCount n h3 target) T a z = 0 := by
          by_contra hne
          exact hzAccount (ih a haAccount hne)
        simp [hiaz]

/-- On an accounted path, enough counted activations force the target. -/
theorem infectionActivation_target_of_account
    {n target initialActive initialCount : ℕ}
    (q : InfectionState n × ℕ)
    (hq : InfectionActivationAccount target initialActive initialCount q)
    (hcount : target + initialCount ≤ initialActive + q.2) :
    target ≤ q.1.1.active := by
  rcases hq with htarget | hledger
  · exact htarget
  · omega

/-- Exact zero/one/two exponential-moment decomposition on a live state. -/
theorem infectionActivationCount_decomp
    (n : ℕ) (h3 : 3 ≤ n) (target : ℕ)
    (s : InfectionState n) (c : ℕ)
    (hlive : ¬ target ≤ s.1.active) (w : ℝ≥0∞) :
    expect (infectionActivationCount n h3 target (s, c))
        (fun q => w ^ q.2) =
      infectionNoActivationMass s.1 (by
        have hs := s.2
        simp only [InfectionCfg.Inv] at hs
        omega) * w ^ c +
      infectionActivationOneMass s.1 (by
        have hs := s.2
        simp only [InfectionCfg.Inv] at hs
        omega) * w ^ (c + 1) +
      infectionActivationTwoMass s.1 (by
        have hs := s.2
        simp only [InfectionCfg.Inv] at hs
        omega) * w ^ (c + 2) := by
  unfold infectionActivationCount
  rw [dif_neg hlive, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset InfectionEvent) =
    {InfectionEvent.activeXXX, InfectionEvent.activeXXY,
      InfectionEvent.activeXYY, InfectionEvent.activeYYY,
      InfectionEvent.activateOneX, InfectionEvent.activateOneY,
      InfectionEvent.activateTwoXX, InfectionEvent.activateTwoXY,
      InfectionEvent.activateTwoYY, InfectionEvent.inactiveOnly} from rfl]
  simp [InfectionEvent.activationInc, infectionNoActivationMass,
    infectionActivationOneMass, infectionActivationTwoMass]
  ring

/-- Pointwise one-step counter contraction from a local activation floor. -/
theorem infectionActivationCount_step_at
    (n : ℕ) (h3 : 3 ≤ n) (target : ℕ)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (q : InfectionState n × ℕ)
    (hfloor : ¬ target ≤ q.1.1.active →
      p ≤ infectionActivationMass q.1.1 (by
        have hs := q.1.2
        simp only [InfectionCfg.Inv] at hs
        omega)) :
    expect (infectionActivationCount n h3 target q)
        (fun z => w ^ z.2) ≤
      (p' + p * w) * w ^ q.2 := by
  rcases q with ⟨s, c⟩
  by_cases hdone : target ≤ s.1.active
  · apply count_step_of_masses
      (K := infectionActivationCount n h3 target)
      (count := Prod.snd) (s := (s, c))
      (w := w) (q := 1) (q' := 0) (p := p) (p' := p')
    · simp
    · exact hp
    · exact hw
    · rw [← hp]
      exact le_add_right le_rfl
    · rw [infectionActivationCount, dif_pos hdone, expect_pure]
      simp
  · rw [infectionActivationCount_decomp n h3 target s c hdone w]
    let hs3 : 3 ≤ s.1.total := by
      have hs := s.2
      simp only [InfectionCfg.Inv] at hs
      omega
    let q0 := infectionNoActivationMass s.1 hs3
    let q1 := infectionActivationOneMass s.1 hs3
    let q2 := infectionActivationTwoMass s.1 hs3
    have hsum : q0 + (q1 + q2) = 1 := by
      dsimp only [q0, q1, q2]
      simpa [infectionActivationMass, add_assoc] using
        infectionActivationMasses_sum s.1 hs3
    have hpw : w ^ (c + 2) ≤ w ^ (c + 1) :=
      pow_le_pow_right_of_le_one' hw (by omega)
    have hcollapse :
        q0 * w ^ c + q1 * w ^ (c + 1) + q2 * w ^ (c + 2) ≤
          q0 * w ^ c + (q1 + q2) * w ^ (c + 1) := by
      calc
        q0 * w ^ c + q1 * w ^ (c + 1) + q2 * w ^ (c + 2)
            ≤ q0 * w ^ c + q1 * w ^ (c + 1) +
                q2 * w ^ (c + 1) := by
                  have hq2 :
                      q2 * w ^ (c + 2) ≤ q2 * w ^ (c + 1) := by
                    simpa [mul_comm] using mul_le_mul_left hpw q2
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_left hq2
                      (q0 * w ^ c + q1 * w ^ (c + 1))
        _ = q0 * w ^ c + (q1 + q2) * w ^ (c + 1) := by ring
    calc
      q0 * w ^ c + q1 * w ^ (c + 1) + q2 * w ^ (c + 2)
          ≤ q0 * w ^ c + (q1 + q2) * w ^ (c + 1) := hcollapse
      _ = (q0 + (q1 + q2) * w) * w ^ c := by ring
      _ ≤ (p' + p * w) * w ^ c := by
        have hsum' : (q1 + q2) + q0 = 1 := by
          simpa [add_comm] using hsum
        have hpq : p ≤ q1 + q2 := by
          dsimp only [q1, q2]
          simpa [infectionActivationMass] using hfloor hdone
        have hfactor :=
          step_factor_antitone_ennreal hp hsum' hw hpq
        simpa [mul_comm] using mul_le_mul_right hfactor (w ^ c)

/-- Uniform one-step counter contraction. The activation probability may vary
adaptively with the current infection state. -/
theorem infectionActivationCount_step
    (n : ℕ) (h3 : 3 ≤ n) (target : ℕ)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hfloor : ∀ s : InfectionState n,
      ¬ target ≤ s.1.active →
      p ≤ infectionActivationMass s.1 (by
        have hs := s.2
        simp only [InfectionCfg.Inv] at hs
        omega)) :
    ∀ q, expect (infectionActivationCount n h3 target q)
        (fun z => w ^ z.2) ≤
      (p' + p * w) * w ^ q.2 := by
  intro q
  exact infectionActivationCount_step_at
    n h3 target w p p' hw hp q (hfloor q.1)

/-- Adapted Chernoff lower tail for the number of molecules activated. -/
theorem infectionActivationCount_tail
    (n : ℕ) (h3 : 3 ≤ n) (target : ℕ)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hfloor : ∀ s : InfectionState n,
      ¬ target ≤ s.1.active →
      p ≤ infectionActivationMass s.1 (by
        have hs := s.2
        simp only [InfectionCfg.Inv] at hs
        omega))
    (T M c0 : ℕ) (s0 : InfectionState n) :
    ∑' q, (if q.2 ≤ M then
        iter (infectionActivationCount n h3 target) T (s0, c0) q
      else 0) ≤
      (p' + p * w) ^ T * w ^ c0 / w ^ M := by
  exact count_tail_bernoulli
    (infectionActivationCount n h3 target) Prod.snd
    w p p' hw1 hw0
    (infectionActivationCount_step n h3 target w p p' hw1 hp hfloor)
    T M (s0, c0)

/-- Rectangle-instantiated version with the exact combinatorial floor. -/
theorem infectionActivationCount_tail_rectangle
    (n : ℕ) (h3 : 3 ≤ n) (target aLo iLo : ℕ)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hpFloor : p ≤ infectionActivationFloor n aLo iLo)
    (hband : ∀ s : InfectionState n,
      ¬ target ≤ s.1.active →
      aLo ≤ s.1.active ∧ iLo ≤ s.1.inactive)
    (T M c0 : ℕ) (s0 : InfectionState n) :
    ∑' q, (if q.2 ≤ M then
        iter (infectionActivationCount n h3 target) T (s0, c0) q
      else 0) ≤
      (p' + p * w) ^ T * w ^ c0 / w ^ M := by
  apply infectionActivationCount_tail n h3 target
    w p p' hw1 hw0 hp
  intro s hs
  exact hpFloor.trans
    (infectionActivationFloor_le n h3 s aLo iLo
      (hband s hs).1 (hband s hs).2)

end Tri

#print axioms Tri.InfectionEvent.nextState_inactive_classify
#print axioms Tri.infectionActivationMass_eq
#print axioms Tri.infectionActivationFloor_le
#print axioms Tri.infectionActivationCount_iter_account
#print axioms Tri.infectionActivationCount_decomp
#print axioms Tri.infectionActivationCount_tail_rectangle
