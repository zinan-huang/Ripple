/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma9

/-!
# Byzantine effective-rate adapters

This file records the count-level interval adapter used by Theorem 4 phase I.
The paper writes the current signed gap as `2x - n`; all statements below use
additive witnesses instead.  The effective-rate conclusions are phrased in
division-free form, and the final lemma is the exact `lemma6_paper` rate
premise.
-/

namespace Tri.Byzantine

open scoped ENNReal NNReal

variable {n B : ℕ}

/-- Lemma 9 restated with additive witnesses for the complement population and
for each natural-number inequality. -/
theorem lemma9_effectiveRate_cross_witness
    {s : State n B} {Δ₀ Δ ŷ zSlack lowerSlack upperSlack : ℕ}
    (hyhat : State.x s + ŷ = n)
    (hbudget : 16 * State.z s + zSlack = Δ₀)
    (hlower : Δ₀ + lowerSlack = 2 * Δ)
    (hupper : 2 * Δ + upperSlack = n)
    (hgap : n + Δ = 2 * State.x s) :
    2 * n * State.z s ≤ Δ * ŷ := by
  have hyhat_eq : State.y s + State.z s = ŷ := by
    have htotal := State.total s
    omega
  have h :=
    lemma9_effectiveRate_cross
      (s := s) (Δ₀ := Δ₀) (Δ := Δ)
      (by omega) (by omega) (by omega) hgap
  simpa [hyhat_eq] using h

/-- Lemma 9's effective-idle conclusion with the same additive witnesses. -/
theorem lemma9_effectiveIdleRate_cross_witness
    {s : State n B} {Δ₀ Δ ŷ zSlack lowerSlack upperSlack : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hn : 0 < n)
    (hyhat : State.x s + ŷ = n)
    (hbudget : 16 * State.z s + zSlack = Δ₀)
    (hlower : Δ₀ + lowerSlack = 2 * Δ)
    (hupper : 2 * Δ + upperSlack = n)
    (hgap : n + Δ = 2 * State.x s) :
    ((2 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞) ≤
      (Δ : ℝ≥0∞) := by
  exact
    lemma9_effectiveIdleRate_cross
      (s := s) (Δ₀ := Δ₀) (Δ := Δ)
      r hrate hn (by omega) (by omega) (by omega) hgap

/-- The per-band adapter in count form.  If the band anchor `a` dominates the
initial Byzantine budget and the current gap is in `[a/2,n/2]`, then the idle
mass satisfies the stronger cross inequality corresponding to
`idle ≤ a/(4n)`. -/
theorem interval_effectiveRate_quarter_cross_witness
    {s : State n B} {Δ₀ Δ a ŷ zSlack anchorSlack lowerSlack upperSlack : ℕ}
    (hyhat : State.x s + ŷ = n)
    (hbudget : 16 * State.z s + zSlack = Δ₀)
    (hanchor : Δ₀ + anchorSlack = a)
    (hlower : a + lowerSlack = 2 * Δ)
    (hupper : 2 * Δ + upperSlack = n)
    (hgap : n + Δ = 2 * State.x s) :
    4 * n * State.z s ≤ a * ŷ := by
  have hyhat_gap : 2 * ŷ + Δ = n := by
    omega
  have hn_le_four_yhat : n ≤ 4 * ŷ := by
    omega
  have hz_le : 16 * State.z s ≤ a := by
    omega
  have hmul := Nat.mul_le_mul hz_le hn_le_four_yhat
  nlinarith

/-- The same interval adapter weakened to the exact cross form consumed by
Lemma 6's rate premise. -/
theorem interval_effectiveRate_cross_witness
    {s : State n B} {Δ₀ Δ a ŷ zSlack anchorSlack lowerSlack upperSlack : ℕ}
    (hyhat : State.x s + ŷ = n)
    (hbudget : 16 * State.z s + zSlack = Δ₀)
    (hanchor : Δ₀ + anchorSlack = a)
    (hlower : a + lowerSlack = 2 * Δ)
    (hupper : 2 * Δ + upperSlack = n)
    (hgap : n + Δ = 2 * State.x s) :
    2 * n * State.z s ≤ a * ŷ := by
  have hquarter :=
    interval_effectiveRate_quarter_cross_witness
      (s := s) (Δ₀ := Δ₀) (Δ := Δ) (a := a) (ŷ := ŷ)
      (zSlack := zSlack) (anchorSlack := anchorSlack)
      (lowerSlack := lowerSlack) (upperSlack := upperSlack)
      hyhat hbudget hanchor hlower hupper hgap
  nlinarith

/-- `ENNReal` form of the stronger per-band adapter:
`idle ≤ a/(4n)`, written without division. -/
theorem interval_effectiveIdleRate_quarter_cross_witness
    {s : State n B} {Δ₀ Δ a ŷ zSlack anchorSlack lowerSlack upperSlack : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hn : 0 < n)
    (hyhat : State.x s + ŷ = n)
    (hbudget : 16 * State.z s + zSlack = Δ₀)
    (hanchor : Δ₀ + anchorSlack = a)
    (hlower : a + lowerSlack = 2 * Δ)
    (hupper : 2 * Δ + upperSlack = n)
    (hgap : n + Δ = 2 * State.x s) :
    ((4 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞) ≤
      (a : ℝ≥0∞) := by
  have hcross :=
    interval_effectiveRate_quarter_cross_witness
      (s := s) (Δ₀ := Δ₀) (Δ := Δ) (a := a) (ŷ := ŷ)
      (zSlack := zSlack) (anchorSlack := anchorSlack)
      (lowerSlack := lowerSlack) (upperSlack := upperSlack)
      hyhat hbudget hanchor hlower hupper hgap
  have hyhat_eq : State.y s + State.z s = ŷ := by
    have htotal := State.total s
    omega
  have hyhat_pos : 0 < ŷ := by
    omega
  have hyhat_ne : (ŷ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hyhat_pos.ne'
  have hyhat_top : (ŷ : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hyhat_cast :
      (State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞) =
        (ŷ : ℝ≥0∞) := by
    rw [← Nat.cast_add, hyhat_eq]
  have hidle_yhat :
      (r.idle : ℝ≥0∞) * (ŷ : ℝ≥0∞) =
        (State.z s : ℝ≥0∞) := by
    simpa [hyhat_cast] using hrate.idle_cross
  apply (ENNReal.mul_le_mul_iff_right hyhat_ne hyhat_top).mp
  calc
    (ŷ : ℝ≥0∞) *
        (((4 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞)) =
        ((4 * n : ℕ) : ℝ≥0∞) *
          ((r.idle : ℝ≥0∞) * (ŷ : ℝ≥0∞)) := by
      ring
    _ = ((4 * n : ℕ) : ℝ≥0∞) *
          (State.z s : ℝ≥0∞) := by
      rw [hidle_yhat]
    _ = ((4 * n * State.z s : ℕ) : ℝ≥0∞) := by
      push_cast
      ring
    _ ≤ ((a * ŷ : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hcross
    _ = (ŷ : ℝ≥0∞) * (a : ℝ≥0∞) := by
      push_cast
      ring

/-- The interval adapter in the exact `ENNReal` cross form matching
Lemma 6's printed floor `fire ≥ 1 - a/(2n)`. -/
theorem interval_effectiveIdleRate_cross_witness
    {s : State n B} {Δ₀ Δ a ŷ zSlack anchorSlack lowerSlack upperSlack : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hn : 0 < n)
    (hyhat : State.x s + ŷ = n)
    (hbudget : 16 * State.z s + zSlack = Δ₀)
    (hanchor : Δ₀ + anchorSlack = a)
    (hlower : a + lowerSlack = 2 * Δ)
    (hupper : 2 * Δ + upperSlack = n)
    (hgap : n + Δ = 2 * State.x s) :
    ((2 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞) ≤
      (a : ℝ≥0∞) := by
  have hquarter :=
    interval_effectiveIdleRate_quarter_cross_witness
      (s := s) (Δ₀ := Δ₀) (Δ := Δ) (a := a) (ŷ := ŷ)
      (zSlack := zSlack) (anchorSlack := anchorSlack)
      (lowerSlack := lowerSlack) (upperSlack := upperSlack)
      r hrate hn hyhat hbudget hanchor hlower hupper hgap
  calc
    ((2 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞) ≤
        ((4 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞) := by
      have hcoef :
          ((2 * n : ℕ) : ℝ≥0∞) ≤ ((4 * n : ℕ) : ℝ≥0∞) := by
        exact_mod_cast (by omega : 2 * n ≤ 4 * n)
      simpa [mul_comm] using
        (mul_le_mul_right hcoef (r.idle : ℝ≥0∞))
    _ ≤ (a : ℝ≥0∞) := hquarter

/-- The per-band adapter as the `lemma6_paper` rate premise. -/
theorem interval_lemma6_rate_premise_witness
    {s : State n B} {Δ₀ Δ a ŷ zSlack anchorSlack lowerSlack upperSlack : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hn : 0 < n)
    (hyhat : State.x s + ŷ = n)
    (hbudget : 16 * State.z s + zSlack = Δ₀)
    (hanchor : Δ₀ + anchorSlack = a)
    (hlower : a + lowerSlack = 2 * Δ)
    (hupper : 2 * Δ + upperSlack = n)
    (hgap : n + Δ = 2 * State.x s) :
    (1 : NNReal) ≤
      r.fire + (((a : ℕ) : NNReal) /
        (((2 * n : ℕ) : NNReal))) := by
  have hcross :=
    interval_effectiveRate_cross_witness
      (s := s) (Δ₀ := Δ₀) (Δ := Δ) (a := a) (ŷ := ŷ)
      (zSlack := zSlack) (anchorSlack := anchorSlack)
      (lowerSlack := lowerSlack) (upperSlack := upperSlack)
      hyhat hbudget hanchor hlower hupper hgap
  have hyhat_eq : State.y s + State.z s = ŷ := by
    have htotal := State.total s
    omega
  have hyhat_pos : 0 < ŷ := by
    omega
  have hyhat_cast :
      (State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞) =
        (ŷ : ℝ≥0∞) := by
    rw [← Nat.cast_add, hyhat_eq]
  have hidle_yhatE :
      (r.idle : ℝ≥0∞) * (ŷ : ℝ≥0∞) =
        (State.z s : ℝ≥0∞) := by
    simpa [hyhat_cast] using hrate.idle_cross
  have hidle_yhatR :
      (r.idle : ℝ) * (ŷ : ℝ) = (State.z s : ℝ) := by
    have h := congrArg ENNReal.toReal hidle_yhatE
    simpa [ENNReal.toReal_mul] using h
  have hcrossR :
      (((2 * n : ℕ) : ℝ) * (State.z s : ℝ)) ≤
        (a : ℝ) * (ŷ : ℝ) := by
    exact_mod_cast hcross
  have hmul :
      (((2 * n : ℕ) : ℝ) * (r.idle : ℝ)) ≤ (a : ℝ) := by
    have hcross' :
        (((2 * n : ℕ) : ℝ) * (r.idle : ℝ)) * (ŷ : ℝ) ≤
          (a : ℝ) * (ŷ : ℝ) := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_right (by exact_mod_cast hyhat_pos)).mp
      hcross'
  have hidle_le :
      (r.idle : ℝ) ≤ (a : ℝ) / (((2 * n : ℕ) : ℝ)) := by
    rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < 2 * n))]
    simpa [mul_comm] using hmul
  have haddR : (r.fire : ℝ) + (r.idle : ℝ) = 1 := by
    exact_mod_cast r.add_eq_one
  have hreal :
      (1 : ℝ) ≤
        (r.fire : ℝ) + (a : ℝ) / (((2 * n : ℕ) : ℝ)) := by
    calc
      (1 : ℝ) = (r.fire : ℝ) + (r.idle : ℝ) := haddR.symm
      _ ≤ (r.fire : ℝ) + (a : ℝ) / (((2 * n : ℕ) : ℝ)) := by
        exact add_le_add le_rfl hidle_le
  rw [← NNReal.coe_le_coe]
  simpa [NNReal.coe_add, NNReal.coe_div] using hreal

namespace RateAdapterExample

private def s : State 4 0 := by
  refine ⟨(⟨3, by decide⟩, ⟨0, by decide⟩), ?_⟩
  decide

private def r : RelaxedRate :=
  { fire := 1
    idle := 0
    add_eq_one := by norm_num }

private theorem hrate : IsPaperEffectiveRate r s := by
  constructor <;> norm_num [r, s, State.x, State.y, State.z]

example :
    2 * 4 * State.z s ≤ 2 * 1 := by
  exact
    lemma9_effectiveRate_cross_witness
      (s := s) (Δ₀ := 0) (Δ := 2) (ŷ := 1)
      (zSlack := 0) (lowerSlack := 4) (upperSlack := 0)
      (by norm_num [s, State.x])
      (by norm_num [s, State.z])
      (by norm_num) (by norm_num) (by norm_num [s, State.x])

example :
    ((2 * 4 : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞) ≤
      (2 : ℝ≥0∞) := by
  exact
    lemma9_effectiveIdleRate_cross_witness
      (s := s) (Δ₀ := 0) (Δ := 2) (ŷ := 1)
      (zSlack := 0) (lowerSlack := 4) (upperSlack := 0)
      r hrate (by norm_num)
      (by norm_num [s, State.x])
      (by norm_num [s, State.z])
      (by norm_num) (by norm_num) (by norm_num [s, State.x])

example :
    4 * 4 * State.z s ≤ 2 * 1 := by
  exact
    interval_effectiveRate_quarter_cross_witness
      (s := s) (Δ₀ := 0) (Δ := 2) (a := 2) (ŷ := 1)
      (zSlack := 0) (anchorSlack := 2)
      (lowerSlack := 2) (upperSlack := 0)
      (by norm_num [s, State.x])
      (by norm_num [s, State.z])
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [s, State.x])

example :
    ((2 * 4 : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞) ≤
      (2 : ℝ≥0∞) := by
  exact
    interval_effectiveIdleRate_cross_witness
      (s := s) (Δ₀ := 0) (Δ := 2) (a := 2) (ŷ := 1)
      (zSlack := 0) (anchorSlack := 2)
      (lowerSlack := 2) (upperSlack := 0)
      r hrate (by norm_num)
      (by norm_num [s, State.x])
      (by norm_num [s, State.z])
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [s, State.x])

example :
    (1 : NNReal) ≤
      r.fire + (((2 : ℕ) : NNReal) /
        (((2 * 4 : ℕ) : NNReal))) := by
  exact
    interval_lemma6_rate_premise_witness
      (s := s) (Δ₀ := 0) (Δ := 2) (a := 2) (ŷ := 1)
      (zSlack := 0) (anchorSlack := 2)
      (lowerSlack := 2) (upperSlack := 0)
      r hrate (by norm_num)
      (by norm_num [s, State.x])
      (by norm_num [s, State.z])
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [s, State.x])

end RateAdapterExample

end Tri.Byzantine

#print axioms Tri.Byzantine.lemma9_effectiveRate_cross_witness
#print axioms Tri.Byzantine.lemma9_effectiveIdleRate_cross_witness
#print axioms Tri.Byzantine.interval_effectiveRate_quarter_cross_witness
#print axioms Tri.Byzantine.interval_effectiveRate_cross_witness
#print axioms Tri.Byzantine.interval_effectiveIdleRate_quarter_cross_witness
#print axioms Tri.Byzantine.interval_effectiveIdleRate_cross_witness
#print axioms Tri.Byzantine.interval_lemma6_rate_premise_witness
