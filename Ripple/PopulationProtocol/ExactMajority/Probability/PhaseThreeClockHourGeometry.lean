-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHourGeometry.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCore

/-!
# Exact-hour occupancy from genuine quantile endpoints

The closed endpoint is handled using unit increments at the first small
hit. The implemented small threshold is the natural floor C/1000.
Positive hours use the difference of two effective fronts; hour zero uses
the active fixed Clock mask instead of the zero-level front.

These are deterministic consequences of first-passage data. They do not
postulate a probability law conditioned on successful future shape.
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourGeometry

open TimeTheorem PairLog PhaseThreeClockCore

variable {n : ℕ}

/-- At a positive hour, the effective lower front partitions into the
active exact-hour population and the next-hour front. -/
theorem positive_hour_front_partition (init : InputCfg n)
    (fS fv : Lab init) (h : ℕ) (hh : 1 ≤ h) :
    frontCountL init fS fv (256 * h) =
      exactHourClocksL init fS fv h +
        frontCountL init fS fv (256 * (h + 1)) := by
  classical
  let P : Fin init.card → Prop := fun i =>
    fixedRoleL init fS .clock i ∧ 256 * h ≤ effectiveMinuteL init fv i
  let Q : Fin init.card → Prop := fun i => (fv i).minute.val / 256 = h
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ.filter P) Q
  have hleft :
      (Finset.univ.filter P).filter Q =
        Finset.univ.filter (fun i =>
          fixedRoleL init fS .clock i ∧ activeL init fv i ∧
            (fv i).minute.val / 256 = h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, Q]
    by_cases hF : fixedRoleL init fS .clock i <;> by_cases ha : activeL init fv i <;>
      simp only [effectiveMinuteL, hF, ha, ↓reduceIte, true_and, and_true, false_and, and_false,
        iff_false, false_iff] <;>
      omega
  have hright :
      (Finset.univ.filter P).filter (fun i => ¬ Q i) =
        Finset.univ.filter (fun i =>
          fixedRoleL init fS .clock i ∧
            256 * (h + 1) ≤ effectiveMinuteL init fv i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, Q]
    by_cases hF : fixedRoleL init fS .clock i <;> by_cases ha : activeL init fv i <;>
      simp only [effectiveMinuteL, hF, ha, ↓reduceIte, true_and, and_true, false_and, and_false,
        iff_false, false_iff] <;>
      omega
  rw [hleft, hright] at hpartition
  unfold frontCountL exactHourClocksL StageEventSpec.labelCount
  convert hpartition.symm

/-- Hour zero must count active Clock labels, because effective minute
zero also contains inactive Clocks. -/
theorem active_clock_hour_zero_partition (init : InputCfg n)
    (fS fv : Lab init) :
    activeRoleCountL init fS fv .clock =
      exactHourClocksL init fS fv 0 + frontCountL init fS fv 256 := by
  classical
  let P : Fin init.card → Prop := fun i =>
    fixedRoleL init fS .clock i ∧ activeL init fv i
  let Q : Fin init.card → Prop := fun i => (fv i).minute.val / 256 = 0
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ.filter P) Q
  have hleft :
      (Finset.univ.filter P).filter Q =
        Finset.univ.filter (fun i =>
          fixedRoleL init fS .clock i ∧ activeL init fv i ∧
            (fv i).minute.val / 256 = 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, Q]
    tauto
  have hright :
      (Finset.univ.filter P).filter (fun i => ¬ Q i) =
        Finset.univ.filter (fun i =>
          fixedRoleL init fS .clock i ∧ 256 ≤ effectiveMinuteL init fv i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, Q]
    by_cases hF : fixedRoleL init fS .clock i <;> by_cases ha : activeL init fv i <;>
      simp only [effectiveMinuteL, hF, ha, ↓reduceIte, true_and, and_true, false_and, and_false,
        iff_false, false_iff] <;>
      omega
  rw [hleft, hright] at hpartition
  unfold activeRoleCountL frontCountL exactHourClocksL StageEventSpec.labelCount
  convert hpartition.symm

theorem highThreshold_rounding (C : ℕ) :
    9 * C ≤ 10 * StageEventSpec.highThreshold C := by
  have h := Nat.le_ceil (9 * (C : ℝ) / 10)
  have hr : 9 * (C : ℝ) ≤
      10 * (StageEventSpec.highThreshold C : ℝ) := by
    unfold StageEventSpec.highThreshold
    linarith
  exact_mod_cast hr

theorem smallThreshold_rounding (C : ℕ) :
    1000 * StageEventSpec.smallThreshold C ≤ C := by
  unfold StageEventSpec.smallThreshold
  omega

theorem positive_hour_occupancy (init : InputCfg n) (fS fv : Lab init)
    (h C : ℕ) (hh : 1 ≤ h)
    (hlower : StageEventSpec.highThreshold C ≤
      frontCountL init fS fv (256 * h))
    (hupper : frontCountL init fS fv (256 * (h + 1)) ≤
      StageEventSpec.smallThreshold C) :
    899 * C ≤ 1000 * exactHourClocksL init fS fv h := by
  have hp := positive_hour_front_partition init fS fv h hh
  have hhigh := highThreshold_rounding C
  have hsmall := smallThreshold_rounding C
  omega

theorem zero_hour_occupancy (init : InputCfg n) (fS fv : Lab init)
    (C : ℕ)
    (hactive : 23 * C ≤ 24 * activeRoleCountL init fS fv .clock)
    (hupper : frontCountL init fS fv 256 ≤ StageEventSpec.smallThreshold C) :
    899 * C ≤ 1000 * exactHourClocksL init fS fv 0 := by
  have hp := active_clock_hour_zero_partition init fS fv
  have hsmall := smallThreshold_rounding C
  omega

/-- A unit-increment process cannot overshoot its first target. The
initial value may already equal the target. -/
theorem firstAfter_count_eq {X : ℕ → ℕ} {S t b : ℕ}
    (hfirst : StageEventSpec.firstAfter (fun v => b ≤ X v) S t)
    (hstart : X S ≤ b)
    (hunit : ∀ v, S ≤ v → X (v + 1) ≤ X v + 1) :
    X t = b := by
  have hhit := hfirst.2.1
  have hSt := hfirst.1
  by_cases ht : t = S
  · subst t
    omega
  · have hprev := hfirst.2.2 (t - 1) (by omega) (by omega)
    have hstep := hunit (t - 1) (by omega)
    have heq : t - 1 + 1 = t := by omega
    rw [heq] at hstep
    omega

/-- In particular the count is at most the target on the closed interval
ending at its first hit. -/
theorem count_le_on_closed_firstAfter {X : ℕ → ℕ} {S t b v : ℕ}
    (hfirst : StageEventSpec.firstAfter (fun k => b ≤ X k) S t)
    (hstart : X S ≤ b)
    (hunit : ∀ k, S ≤ k → X (k + 1) ≤ X k + 1)
    (hSv : S ≤ v) (hvt : v ≤ t) :
    X v ≤ b := by
  by_cases hvt' : v = t
  · subst v
    exact (firstAfter_count_eq hfirst hstart hunit).le
  · have hbefore := hfirst.2.2 v hSv (by omega)
    omega

theorem successive_quantile_firstAfter_lt {X : ℕ → ℕ} {S e s a b : ℕ}
    (hab : a < b)
    (he : StageEventSpec.firstAfter (fun v => a ≤ X v) S e)
    (hs : StageEventSpec.firstAfter (fun v => b ≤ X v) S s)
    (hstart : X S ≤ a)
    (hunit : ∀ v, S ≤ v → X (v + 1) ≤ X v + 1) :
    e < s := by
  have heq := firstAfter_count_eq he hstart hunit
  have hhit := hs.2.1
  have hes : e ≤ s := by
    by_contra hn
    have hbefore := he.2.2 s hs.1 (by omega)
    omega
  have hne : e ≠ s := by
    intro heqs
    subst e
    omega
  omega

/-- Positive-hour occupancy on the complete closed quantile interval.
The upper-front unit law is used at the finish endpoint. -/
theorem positive_hour_window_occupancy (init : InputCfg n)
    (lab : ℕ → Lab init) (S s e h C : ℕ) (hh : 1 ≤ h)
    (hstart : StageEventSpec.firstAfter (fun v =>
      StageEventSpec.highThreshold C ≤ frontCountL init (lab S) (lab v) (256 * h)) S s)
    (hfinish : StageEventSpec.firstAfter (fun v =>
      StageEventSpec.smallThreshold C ≤ frontCountL init (lab S) (lab v)
        (256 * (h + 1))) S e)
    (hinitial : frontCountL init (lab S) (lab S) (256 * (h + 1)) ≤
      StageEventSpec.smallThreshold C)
    (hunit : ∀ v, S ≤ v →
      frontCountL init (lab S) (lab (v + 1)) (256 * (h + 1)) ≤
        frontCountL init (lab S) (lab v) (256 * (h + 1)) + 1)
    (hmono : ∀ u v, S ≤ u → u ≤ v →
      frontCountL init (lab S) (lab u) (256 * h) ≤
        frontCountL init (lab S) (lab v) (256 * h)) :
    ∀ v, s ≤ v → v ≤ e →
      899 * C ≤ 1000 * exactHourClocksL init (lab S) (lab v) h := by
  intro v hsv hve
  apply positive_hour_occupancy init (lab S) (lab v) h C hh
  · exact hstart.2.1.trans (hmono s v hstart.1 hsv)
  · exact count_le_on_closed_firstAfter
      (X := fun k => frontCountL init (lab S) (lab k) (256 * (h + 1))) hfinish hinitial hunit
      (hstart.1.trans hsv) hve

/-- Hour-zero occupancy uses its observed active-Clock floor at the
ninety-nine-percent start, rather than a positive-level lower quantile. -/
theorem zero_hour_window_occupancy (init : InputCfg n)
    (lab : ℕ → Lab init) (S α e C : ℕ) (hSα : S ≤ α)
    (hfinish : StageEventSpec.firstAfter (fun v =>
      StageEventSpec.smallThreshold C ≤ frontCountL init (lab S) (lab v) 256) S e)
    (hinitial : frontCountL init (lab S) (lab S) 256 ≤ StageEventSpec.smallThreshold C)
    (hunit : ∀ v, S ≤ v →
      frontCountL init (lab S) (lab (v + 1)) 256 ≤
        frontCountL init (lab S) (lab v) 256 + 1)
    (hactive : ∀ v, α ≤ v →
      23 * C ≤ 24 * activeRoleCountL init (lab S) (lab v) .clock) :
    ∀ v, α ≤ v → v ≤ e →
      899 * C ≤ 1000 * exactHourClocksL init (lab S) (lab v) 0 := by
  intro v hαv hve
  exact zero_hour_occupancy init (lab S) (lab v) C (hactive v hαv)
    (count_le_on_closed_firstAfter
      (X := fun k => frontCountL init (lab S) (lab k) 256) hfinish hinitial hunit
      (hSα.trans hαv) hve)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourGeometry

end
