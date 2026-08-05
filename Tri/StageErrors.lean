/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase2Contract
import Tri.Phase3Stop

/-!
# Scalar obstructions in the phase-2 and phase-3 stage errors

This module checks the two remaining scalar obligations before they are used
to inhabit the phase bridges.  A concrete phase-2 band can meet its advertised
error only with a contraction strictly stronger than the currently exported
`phase2DecayENN`; the latter choice is disproved explicitly.  The phase-3
escape-slack condition is also false in general, because frozen escape mass
persists while the killed-potential expectation decays geometrically.
-/

namespace Tri

open scoped ENNReal

/-- At `n = 16`, stage `s = 2`, the band parameters
`(bandLo, bandBHi, bandGap, upperGap) = (11, 3, 1, 2)` and return parameters
`(returnLo, returnBHi, returnGap) = (13, 1, 1)` fit the stage budget when the
strict band factor is `25 / 28`.  The direct return certificate with gap one
fits the same budget. -/
theorem phase2_herror_proved :
    (((((3 : ℝ≥0∞) / 11) ^ 1 +
          ((25 : ℝ≥0∞) / 28) ^ (4 * 16) *
            ((1 : ℝ≥0∞) / 2) ^ 12 /
              ((1 : ℝ≥0∞) / 2) ^ (12 + 2)) +
        ((1 : ℝ≥0∞) / 13) ^ 1 ≤ phase2StageError 16 2) ∧
      ((1 : ℝ≥0∞) / 13) ^ 1 ≤ phase2StageError 16 2) := by
  constructor
  · have hlower : ((3 : ℝ≥0∞) / 11) ^ 1 ≠ ⊤ :=
      ENNReal.pow_ne_top
        (ENNReal.div_ne_top (ENNReal.natCast_ne_top 3) (by norm_num))
    have htail : ((25 : ℝ≥0∞) / 28) ^ (4 * 16) *
          ((1 : ℝ≥0∞) / 2) ^ 12 /
            ((1 : ℝ≥0∞) / 2) ^ (12 + 2) ≠ ⊤ :=
      ENNReal.div_ne_top
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top
          (ENNReal.div_ne_top (ENNReal.natCast_ne_top 25) (by norm_num)))
          (ENNReal.pow_ne_top (by norm_num)))
        (pow_ne_zero _ (by norm_num))
    have hret : ((1 : ℝ≥0∞) / 13) ^ 1 ≠ ⊤ :=
      ENNReal.pow_ne_top
        (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num))
    have hsum := ENNReal.add_ne_top.mpr ⟨hlower, htail⟩
    have hleft := ENNReal.add_ne_top.mpr ⟨hsum, hret⟩
    have hright : phase2StageError 16 2 ≠ ⊤ := by
      unfold phase2StageError
      exact ENNReal.ofReal_ne_top
    rw [← ENNReal.toReal_le_toReal hleft hright,
      ENNReal.toReal_add hsum hret, ENNReal.toReal_add hlower htail]
    norm_num [phase2StageError, phase2Decay, ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_pow]
  · have hright : phase2StageError 16 2 ≠ ⊤ := by
      unfold phase2StageError
      exact ENNReal.ofReal_ne_top
    have hleft : ((1 : ℝ≥0∞) / 13) ^ 1 ≠ ⊤ :=
      ENNReal.pow_ne_top
        (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num))
    rw [← ENNReal.toReal_le_toReal hleft hright]
    norm_num [phase2StageError, phase2Decay, ENNReal.toReal_div,
      ENNReal.toReal_pow]

/-- The exact local contraction on the concrete open band `11 < x < 14` is
`25 / 28`, strictly stronger than `phase2DecayENN 2 = 125 / 128`. -/
theorem phase2_hcontract_16_2 :
    ∀ (a b : ℕ) (hlocal : 3 ≤ (a + 1) + (b + 1)),
      a + b + 2 = 16 →
      11 < a + 1 → a + 1 < 14 →
      triStep (a + 1) (b + 1) hlocal a +
            triStep (a + 1) (b + 1) hlocal (a + 1) *
              ((1 : ℝ≥0∞) / 2) +
            triStep (a + 1) (b + 1) hlocal (a + 2) *
              ((1 : ℝ≥0∞) / 2) ^ 2 ≤
          ((25 : ℝ≥0∞) / 28) * ((1 : ℝ≥0∞) / 2) := by
  intro a b hlocal hpop hlo hhi
  have ha : a = 11 ∨ a = 12 := by omega
  rcases ha with rfl | rfl
  · have hb : b = 3 := by omega
    subst b
    rw [triStep_down, triStep_stay, triStep_up]
    norm_num [Nat.choose]
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
  · have hb : b = 2 := by omega
    subst b
    rw [triStep_down, triStep_stay, triStep_up]
    norm_num [Nat.choose]
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]

/-- A complete concrete `Phase2BandBridge` whose `herror` field is supplied by
`phase2_herror_proved`; no field of this instance is assumed. -/
noncomputable def phase2BandBridge_16_2_12 : Phase2BandBridge 16 2 12 where
  bandLo := 11
  bandBHi := 3
  bandGap := 1
  upperGap := 2
  returnLo := 13
  returnBHi := 1
  returnGap := 1
  φ := (25 : ℝ≥0∞) / 28
  hstart := by norm_num
  hbandPop := by norm_num
  hbandLo := by norm_num
  hbandBHi := by norm_num
  hbandMaj := by norm_num
  hbandGap := by norm_num
  hupperGap := by norm_num
  hupperPhysical := by norm_num
  hreturnPop := by norm_num
  hreturnLo := by norm_num
  hreturnBHi := by norm_num
  hreturnMaj := by norm_num
  hreturnGap := by norm_num
  hlower := by
    intro z hz
    unfold Phase2Upper at hz
    omega
  hupper := by
    intro z hz
    unfold Phase2Upper
    omega
  hfailure := by
    intro z hz
    unfold Phase2Upper at hz
    omega
  hcontract := by
    simpa using phase2_hcontract_16_2
  herror := by simpa using phase2_herror_proved.1

/-- A complete direct-return bridge for the next state in the same concrete
stage; its Feller term is the second conjunct of `phase2_herror_proved`. -/
noncomputable def phase2ReturnBridge_16_2_14 : Phase2ReturnBridge 16 2 14 where
  returnLo := 13
  bHi := 1
  k := 1
  hpop := by norm_num
  hreturnLo := by norm_num
  hbHi := by norm_num
  hmaj := by norm_num
  hgap := by norm_num
  hfailure := by
    intro z hz
    unfold Phase2Upper at hz
    omega
  herror := by simpa using phase2_herror_proved.2

/-- The contraction factor currently supplied by `phase2_hcontract` leaves
no scalar slack even in the first concrete dyadic band.  In fact its live-tail
term alone is twice `phase2StageError 16 2`, so the full `herror` inequality is
false. -/
theorem phase2_herror_decay_false :
    ¬ ((((3 : ℝ≥0∞) / 11) ^ 1 +
          phase2DecayENN 2 ^ (4 * 16) *
            ((1 : ℝ≥0∞) / 2) ^ 12 /
              ((1 : ℝ≥0∞) / 2) ^ (12 + 2)) +
        ((1 : ℝ≥0∞) / 13) ^ 1 ≤ phase2StageError 16 2) := by
  intro hbad
  have hlower : ((3 : ℝ≥0∞) / 11) ^ 1 ≠ ⊤ :=
    ENNReal.pow_ne_top
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top 3) (by norm_num))
  have htail : phase2DecayENN 2 ^ (4 * 16) *
        ((1 : ℝ≥0∞) / 2) ^ 12 /
          ((1 : ℝ≥0∞) / 2) ^ (12 + 2) ≠ ⊤ :=
    ENNReal.div_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top (by norm_num)))
      (pow_ne_zero _ (by norm_num))
  have hret : ((1 : ℝ≥0∞) / 13) ^ 1 ≠ ⊤ :=
    ENNReal.pow_ne_top
      (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num))
  have hsum := ENNReal.add_ne_top.mpr ⟨hlower, htail⟩
  have hright : phase2StageError 16 2 ≠ ⊤ := by
    unfold phase2StageError
    exact ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hright hbad
  rw [ENNReal.toReal_add hsum hret,
    ENNReal.toReal_add hlower htail] at hreal
  norm_num [phase2DecayENN, phase2StageError, phase2Decay,
    ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow] at hreal

/-- Independently of the scalar estimate, the present positive-complement
certificate interface cannot cover the final non-consensus checkpoint at
`n = 16`: failure of stage `5` includes state `15`, forcing `returnLo ≥ 15`,
while the population decomposition and positive `bHi` force `returnLo ≤ 13`. -/
theorem phase2_final_certificate_false :
    ¬ Nonempty (Phase2ReturnBridge 16 4 15 ⊕
      Phase2BandBridge 16 4 15) := by
  rintro ⟨B⟩
  have hfailure : ¬ Phase2Upper 16 (4 + 1) 15 := by
    unfold Phase2Upper
    norm_num
  rcases B with B | B
  · have hlo := B.hfailure 15 hfailure
    have hpop := B.hpop
    have hbHi := B.hbHi
    omega
  · have hlo := B.hfailure 15 hfailure
    have hpop := B.hreturnPop
    have hbHi := B.hreturnBHi
    omega

/-- Consequently, the certificate family required by `phase2_bridge 16` is
uninhabited: its `i = 2`, `x = 15` instance is exactly the impossible final
checkpoint certificate above. -/
theorem phase2_ladder_certificates_false :
    ¬ Nonempty (∀ i, i < Nat.log 2 16 → ∀ x,
      Phase2Stage 16 (2 + i) x → x < 16 →
      Phase2ReturnBridge 16 (2 + i) x ⊕
        Phase2BandBridge 16 (2 + i) x) := by
  rintro ⟨hcertificates⟩
  have B := hcertificates 2 (by decide) 15
    (by norm_num [Phase2Stage]) (by norm_num)
  exact phase2_final_certificate_false ⟨by simpa using B⟩

/-- Escape mass of the phase-3 stopped chain is monotone in the horizon,
because every non-consensus state outside `Phase3Region` is frozen. -/
theorem phase3EscapeMass_mono (n x : ℕ) :
    Monotone (fun T => phase3EscapeMass n T x) := by
  let V : ℕ → ℝ≥0∞ := fun z =>
    if ¬ Phase3Region n z ∧ z ≠ n then 1 else 0
  have hmass (q : PMF ℕ) :
      (∑' z, if ¬ Phase3Region n z ∧ z ≠ n then q z else 0) =
        expect q V := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : ¬ Phase3Region n z ∧ z ≠ n <;> simp [hz]
  have hstep (z : ℕ) : V z ≤ expect (phase3Stop n z) V := by
    by_cases hz : ¬ Phase3Region n z ∧ z ≠ n
    · rw [phase3Stop, freeze_of_mem z hz.1, expect_pure]
    · simp [V, hz]
  refine monotone_nat_of_le_succ fun T => ?_
  unfold phase3EscapeMass
  rw [hmass, hmass, iter_succ', expect_bind]
  unfold expect
  exact ENNReal.tsum_le_tsum fun z => mul_le_mul_right (hstep z) _

/-- From `x = 20` at population `24`, the first step escapes downward to the
frozen state `19` with mass exactly `15 / 253`; this mass remains present at
every horizon at least one. -/
theorem phase3_escapeMass_24_192_lower :
    (15 : ℝ≥0∞) / 253 ≤ phase3EscapeMass 24 192 20 := by
  have hregion20 : Phase3Region 24 20 := by
    unfold Phase3Region
    omega
  have hnotregion19 : ¬ Phase3Region 24 19 := by
    unfold Phase3Region
    omega
  have hone : (15 : ℝ≥0∞) / 253 ≤ phase3EscapeMass 24 1 20 := by
    unfold phase3EscapeMass
    calc
      (15 : ℝ≥0∞) / 253 =
          (if ¬ Phase3Region 24 19 ∧ 19 ≠ 24 then
            iter (phase3Stop 24) 1 20 19 else 0) := by
        simp only [hnotregion19, ne_eq, OfNat.ofNat, not_false_eq_true,
          true_and]
        simp only [iter, PMF.bind_pure]
        rw [phase3Stop,
          freeze_of_not_mem 20 (by simpa using hregion20),
          triChain_apply (show 19 + 3 + 2 = 24 by norm_num) (by norm_num),
          triStep_down]
        apply (ENNReal.div_eq_div_iff (by norm_num)
          (ENNReal.natCast_ne_top 2024) (by norm_num)
          (ENNReal.natCast_ne_top 253)).2
        norm_num [Nat.choose]
      _ ≤ ∑' z, if ¬ Phase3Region 24 z ∧ z ≠ 24 then
          iter (phase3Stop 24) 1 20 z else 0 := ENNReal.le_tsum 19
  exact hone.trans ((phase3EscapeMass_mono 24 20) (by norm_num : 1 ≤ 192))

/-- At the same concrete state, geometric contraction bounds the killed
potential expectation after 192 steps strictly below `15 / 253`. -/
theorem phase3_expect_24_192_upper :
    expect (iter (phase3Stop 24) 192 20) (phase3StoppedPotential 24) <
      (15 : ℝ≥0∞) / 253 := by
  have hregion20 : Phase3Region 24 20 := by
    unfold Phase3Region
    omega
  have hbound := phase3Stop_expect_iter_le 24 192 20 (by norm_num)
  have hpotential : phase3StoppedPotential 24 20 = 15 := by
    rw [phase3StoppedPotential_of_mem hregion20,
      phase3Potential_apply (show 20 + 4 = 24 by norm_num)]
    norm_num
  refine hbound.trans_lt ?_
  have hleft : phase3Factor 24 ^ 192 * (15 : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (phase3Factor_ne_top 24))
      (by norm_num)
  have hright : (15 : ℝ≥0∞) / 253 ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top 15) (by norm_num)
  rw [hpotential, ← ENNReal.toReal_lt_toReal hleft hright]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow,
    phase3Factor_toReal]

/-- `Phase3EscapeSlack` is false at the concrete physical live state
`(n, x, T) = (24, 20, 192)`: persistent escape mass is already at least
`15 / 253`, while the entire killed-potential expectation is smaller than that. -/
theorem phase3_escapeSlack_false :
    ¬ Phase3EscapeSlack 24 192 20 := by
  intro hslack
  have hescapeExpect : phase3EscapeMass 24 192 20 ≤
      expect (iter (phase3Stop 24) 192 20) (phase3StoppedPotential 24) :=
    hslack.trans tsub_le_self
  have hcontra : (15 : ℝ≥0∞) / 253 ≤
      expect (iter (phase3Stop 24) 192 20) (phase3StoppedPotential 24) :=
    phase3_escapeMass_24_192_lower.trans hescapeExpect
  exact (not_le_of_gt phase3_expect_24_192_upper) hcontra

/-- The base-two logarithm of the counterexample population is four. -/
theorem log_two_twentyfour : Nat.log 2 24 = 4 := by decide

/-- The counterexample horizon is exactly the phase-3 horizon selected by
`C₃ = 2` at population `24`. -/
theorem phase3Horizon_two_twentyfour : phase3Horizon 2 24 = 192 := by
  norm_num [phase3Horizon, log_two_twentyfour]

/-- The escape-slack failure therefore occurs at an actual selected phase-3
horizon, not merely at an unrelated deterministic time. -/
theorem phase3_escapeSlack_horizon_false :
    ¬ Phase3EscapeSlack 24 (phase3Horizon 2 24) 20 := by
  rw [phase3Horizon_two_twentyfour]
  exact phase3_escapeSlack_false

/-- The selected-horizon counterexample satisfies the headline size guard and
starts in `Phase2Exit 24 1`; hence it lies in the exact family required by
`hphase3_proved_of_escapeSlack`. -/
theorem phase3_escapeSlack_admissible_false :
    3 ≤ 24 ∧ 1 ≤ 1 ∧ 6 * 1 * Nat.log 2 24 ≤ 24 ∧
      Phase2Exit 24 1 20 ∧
        ¬ Phase3EscapeSlack 24 (phase3Horizon 2 24) 20 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_,
    phase3_escapeSlack_horizon_false⟩
  · norm_num [log_two_twentyfour]
  · norm_num [Phase2Exit, log_two_twentyfour]

/-- The escape-slack conclusion is valid under the single precise residual
condition that the stopped chain assigns no mass to non-consensus escape
states.  The preceding counterexample shows why this condition cannot be
removed for the current killed potential. -/
theorem phase3_escapeSlack_proved (n T x : ℕ)
    (hnoescape : phase3EscapeMass n T x = 0) :
    Phase3EscapeSlack n T x := by
  unfold Phase3EscapeSlack
  rw [hnoescape]
  exact bot_le

#print axioms phase2_herror_proved
#print axioms phase2_hcontract_16_2
#print axioms phase2_herror_decay_false
#print axioms phase2_final_certificate_false
#print axioms phase2_ladder_certificates_false
#print axioms phase3EscapeMass_mono
#print axioms phase3_escapeMass_24_192_lower
#print axioms phase3_expect_24_192_upper
#print axioms phase3_escapeSlack_false
#print axioms log_two_twentyfour
#print axioms phase3Horizon_two_twentyfour
#print axioms phase3_escapeSlack_horizon_false
#print axioms phase3_escapeSlack_admissible_false
#print axioms phase3_escapeSlack_proved

end Tri
