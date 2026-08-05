/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionReactionPotential
import Tri.PaperLemma3

/-!
# Positive-gap safety for productive infection reactions

While the active `X-Y` gap is at least `D`, the adverse type-(2) reaction has
odds at most the harmonic base from paper Lemma 3.  This yields a geometric
supermartingale for the type-(2) minus type-(1) reaction count, without any
finite exposure budget.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Natural-number cross product for the positive-gap reaction odds. -/
theorem infection_typeTwo_weight_safety_cross
    (n D x y : ℕ)
    (hD : D < n)
    (hactive : x + y ≤ n)
    (hgap : y + D ≤ x) :
    (x * Nat.choose y 2) * (2 * n + D) ≤
      (Nat.choose x 2 * y) * (2 * n - D) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx
  have hy1 : 1 ≤ y := Nat.pos_of_ne_zero hy
  have hchooseX :
      2 * (Nat.choose x 2 : ℝ) =
        (x : ℝ) * ((x : ℝ) - 1) := by
    exact_mod_cast two_mul_choose_two x
  have hchooseY :
      2 * (Nat.choose y 2 : ℝ) =
        (y : ℝ) * ((y : ℝ) - 1) := by
    exact_mod_cast two_mul_choose_two y
  have hnD : D ≤ 2 * n := by omega
  have hactiveR :
      (x : ℝ) + (y : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hactive
  have hgapR :
      (y : ℝ) + (D : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hgap
  have hcore :
      ((y : ℝ) - 1) * (2 * (n : ℝ) + (D : ℝ)) ≤
        ((x : ℝ) - 1) * (2 * (n : ℝ) - (D : ℝ)) := by
    nlinarith
  have hxy : (0 : ℝ) ≤ (x : ℝ) * (y : ℝ) / 2 := by
    positivity
  have hmul :=
    mul_le_mul_of_nonneg_left hcore hxy
  have hreal :
      ((x * Nat.choose y 2 : ℕ) : ℝ) *
            (((2 * n + D : ℕ) : ℝ)) ≤
        ((Nat.choose x 2 * y : ℕ) : ℝ) *
            (((2 * n - D : ℕ) : ℝ)) := by
    push_cast
    rw [Nat.cast_sub hnD]
    rw [
      show
        (Nat.choose x 2 : ℝ) =
          (x : ℝ) * ((x : ℝ) - 1) / 2 by
        nlinarith [hchooseX],
      show
        (Nat.choose y 2 : ℝ) =
          (y : ℝ) * ((y : ℝ) - 1) / 2 by
        nlinarith [hchooseY]]
    norm_num only [Nat.cast_mul, Nat.cast_add] at hmul ⊢
    ring_nf at hmul ⊢
    exact hmul
  exact_mod_cast hreal

/-- Under a positive active gap, adverse raw reaction mass is at most the
favourable mass times the Lemma 3 harmonic base. -/
theorem infectionTypeTwoMass_le_typeOne_mul_safetyBase
    (n D : ℕ) (h3 : 3 ≤ n)
    (hD : 0 < D) (hDn : D < n)
    (s : InfectionState n)
    (hgap : s.1.ay + D ≤ s.1.ax) :
    infectionTypeTwoMass s.1
        (by
          have htotal : s.1.total = n := s.2
          omega) ≤
      infectionTypeOneMass s.1
          (by
            have htotal : s.1.total = n := s.2
            omega) *
        lemma3SafetyBase n D := by
  let w₁ : ℕ := Nat.choose s.1.ax 2 * s.1.ay
  let w₂ : ℕ := s.1.ax * Nat.choose s.1.ay 2
  let d : ℕ := Nat.choose n 3
  have hactive : s.1.ax + s.1.ay ≤ n := by
    have htotal : s.1.total = n := s.2
    simp only [InfectionCfg.total,
      InfectionCfg.active] at htotal
    omega
  have hcross :
      w₂ * (2 * n + D) ≤ w₁ * (2 * n - D) := by
    exact
      infection_typeTwo_weight_safety_cross
        n D s.1.ax s.1.ay hDn hactive hgap
  have hden0 :
      ((2 * n + D : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show 2 * n + D ≠ 0 by omega)
  have hdenTop :
      ((2 * n + D : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hweight :
      (w₂ : ℝ≥0∞) ≤
        (w₁ : ℝ≥0∞) * lemma3SafetyBase n D := by
    unfold lemma3SafetyBase
    rw [← mul_div_assoc,
      ENNReal.le_div_iff_mul_le
        (Or.inl hden0) (Or.inl hdenTop)]
    exact_mod_cast hcross
  have hn :
      s.1.total = n := s.2
  simp only [infectionTypeTwoMass,
    infectionTypeOneMass, infectionEventPMF_apply,
    InfectionEvent.weight]
  rw [hn]
  change
    (w₂ : ℝ≥0∞) / (d : ℝ≥0∞) ≤
      ((w₁ : ℝ≥0∞) / (d : ℝ≥0∞)) *
        lemma3SafetyBase n D
  calc
    (w₂ : ℝ≥0∞) / (d : ℝ≥0∞) ≤
        ((w₁ : ℝ≥0∞) * lemma3SafetyBase n D) /
          (d : ℝ≥0∞) :=
      ENNReal.div_le_div_right hweight _
    _ =
        ((w₁ : ℝ≥0∞) / (d : ℝ≥0∞)) *
          lemma3SafetyBase n D := by
      simp only [div_eq_mul_inv]
      ring

/-- Geometric potential for adverse type-(2) reaction excess. -/
noncomputable def infectionReactionSafetyPotential
    {n : ℕ} (D : ℕ)
    (q : InfectionReactionTraceState n) : ℝ≥0∞ :=
  lemma3SafetyBase n D ^ q.typeOneCount *
    (lemma3SafetyBase n D)⁻¹ ^ q.typeTwoCount

theorem infectionReactionSafetyPotential_afterEvent
    {n : ℕ} (D : ℕ)
    (q : InfectionReactionTraceState n)
    (e : InfectionEvent) :
    infectionReactionSafetyPotential D (q.afterEvent e) =
      match e with
      | .activeXXY =>
          lemma3SafetyBase n D *
            infectionReactionSafetyPotential D q
      | .activeXYY =>
          (lemma3SafetyBase n D)⁻¹ *
            infectionReactionSafetyPotential D q
      | _ =>
          infectionReactionSafetyPotential D q := by
  cases e <;>
    simp [infectionReactionSafetyPotential,
      InfectionReactionTraceState.afterEvent,
      InfectionEvent.typeOneInc,
      InfectionEvent.typeTwoInc,
      pow_succ] <;>
    ring

/-- One raw infection interaction preserves the positive-gap safety
potential whenever the current active gap is at least `D`. -/
theorem expect_infectionEventPMF_reactionSafetyPotential
    (n D : ℕ) (h3 : 3 ≤ n)
    (hD : 0 < D) (hDn : D < n)
    (q : InfectionReactionTraceState n)
    (hgap : q.current.1.ay + D ≤ q.current.1.ax) :
    expect
        ((infectionEventPMF q.current.1
            (by
              have htotal :
                  q.current.1.total = n :=
                q.current.2
              omega)).map
          q.afterEvent)
        (infectionReactionSafetyPotential D)
      ≤ infectionReactionSafetyPotential D q := by
  let hn : 3 ≤ q.current.1.total := by
    have htotal :
        q.current.1.total = n := q.current.2
    omega
  let u := lemma3SafetyBase n D
  let pBad := infectionTypeTwoMass q.current.1 hn
  let pGood := infectionTypeOneMass q.current.1 hn
  let pStay := infectionNonProductiveActiveMass q.current.1 hn
  let V := infectionReactionSafetyPotential D q
  have hsum : pBad + pStay + pGood = 1 := by
    dsimp only [pBad, pStay, pGood]
    rw [show
        infectionTypeTwoMass q.current.1 hn +
            infectionNonProductiveActiveMass q.current.1 hn +
            infectionTypeOneMass q.current.1 hn =
          infectionProductiveActiveMass q.current.1 hn +
            infectionNonProductiveActiveMass q.current.1 hn by
      unfold infectionProductiveActiveMass
      ring]
    exact
      infectionProductiveActiveMass_add_compl
        q.current.1 hn
  have hdrift : pBad ≤ pGood * u := by
    simpa [pBad, pGood, u] using
      infectionTypeTwoMass_le_typeOne_mul_safetyBase
        n D h3 hD hDn q.current hgap
  have hcore :
      pBad + pStay * u + pGood * u ^ 2 ≤ u :=
    three_term_drift_ennreal hsum
      (lemma3SafetyBase_le_one hDn) hdrift
  have hu0 : u ≠ 0 :=
    lemma3SafetyBase_ne_zero hDn
  have huTop : u ≠ ⊤ := by
    exact
      ne_top_of_le_ne_top ENNReal.one_ne_top
        (lemma3SafetyBase_le_one hDn)
  have hfactor :
      pBad * u⁻¹ + pStay + pGood * u ≤ 1 := by
    have hcancel : u⁻¹ * u = 1 :=
      ENNReal.inv_mul_cancel hu0 huTop
    have hstay :
        u⁻¹ * (pStay * u) = pStay := by
      calc
        u⁻¹ * (pStay * u) =
            pStay * (u⁻¹ * u) := by ring
        _ = pStay := by rw [hcancel, mul_one]
    have hgood :
        u⁻¹ * (pGood * u ^ 2) =
          pGood * u := by
      rw [pow_two]
      calc
        u⁻¹ * (pGood * (u * u)) =
            pGood * (u⁻¹ * u) * u := by ring
        _ = pGood * u := by rw [hcancel, mul_one]
    calc
      pBad * u⁻¹ + pStay + pGood * u =
          u⁻¹ *
            (pBad + pStay * u + pGood * u ^ 2) := by
        rw [mul_add, mul_add, hstay, hgood]
        ring
      _ ≤ u⁻¹ * u := mul_le_mul_left' hcore _
      _ = 1 := ENNReal.inv_mul_cancel hu0 huTop
  rw [expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show
      (Finset.univ : Finset InfectionEvent) =
        {InfectionEvent.activeXXX,
          InfectionEvent.activeXXY,
          InfectionEvent.activeXYY,
          InfectionEvent.activeYYY,
          InfectionEvent.activateOneX,
          InfectionEvent.activateOneY,
          InfectionEvent.activateTwoXX,
          InfectionEvent.activateTwoXY,
          InfectionEvent.activateTwoYY,
          InfectionEvent.inactiveOnly} from rfl]
  simp only [infectionReactionSafetyPotential_afterEvent]
  have heq :
      (∑ e ∈
          {InfectionEvent.activeXXX,
            InfectionEvent.activeXXY,
            InfectionEvent.activeXYY,
            InfectionEvent.activeYYY,
            InfectionEvent.activateOneX,
            InfectionEvent.activateOneY,
            InfectionEvent.activateTwoXX,
            InfectionEvent.activateTwoXY,
            InfectionEvent.activateTwoYY,
            InfectionEvent.inactiveOnly},
          infectionEventPMF q.current.1 hn e *
            match e with
            | .activeXXY => u * V
            | .activeXYY => u⁻¹ * V
            | _ => V) =
        (pBad * u⁻¹ + pStay + pGood * u) * V := by
    dsimp only [pBad, pStay, pGood, V, u]
    unfold infectionNonProductiveActiveMass
      infectionNotAllActiveMass infectionActivationMass
      infectionActivationOneMass infectionActivationTwoMass
      infectionTypeOneMass infectionTypeTwoMass
    simp
    ring
  rw [heq]
  simpa only [mul_comm, one_mul] using
    (mul_le_mul_right hfactor V)

/-- The reaction trace stop preserves the positive-gap safety estimate. -/
theorem expect_infectionReactionTraceStep_reactionSafetyPotential
    (n D : ℕ) (h3 : 3 ≤ n)
    (hD : 0 < D) (hDn : D < n)
    (A G : ℕ)
    (q : InfectionReactionTraceState n)
    (hgap : q.current.1.ay + D ≤ q.current.1.ax) :
    expect (infectionReactionTraceStep n h3 A G q)
        (infectionReactionSafetyPotential D) ≤
      infectionReactionSafetyPotential D q := by
  by_cases hstop :
      InfectionReactionTraceStop A G q
  · unfold infectionReactionTraceStep
    rw [if_pos hstop, expect_pure]
  · unfold infectionReactionTraceStep
    rw [if_neg hstop]
    exact
      expect_infectionEventPMF_reactionSafetyPotential
        n D h3 hD hDn q hgap

end

end Tri

#print axioms Tri.infection_typeTwo_weight_safety_cross
#print axioms Tri.infectionTypeTwoMass_le_typeOne_mul_safetyBase
#print axioms Tri.infectionReactionSafetyPotential_afterEvent
#print axioms Tri.expect_infectionEventPMF_reactionSafetyPotential
#print axioms Tri.expect_infectionReactionTraceStep_reactionSafetyPotential
