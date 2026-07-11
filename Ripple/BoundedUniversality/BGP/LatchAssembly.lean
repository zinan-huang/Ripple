/-
Ripple.BoundedUniversality.BGP.LatchAssembly
------------------------
Halt latch (paper §5: constr:halt-latch, constr:halt-indicator,
lem:rational-gate, lem:halt-latch), stereographic compactification
(§6), and the assembled main-theorem target (constr:assembled,
thm:main).

Revision 3 after adversarial round 2 (codex R2; log:
notes/bgp-adversarial-rounds.md).  R2 fixes: chart readout via
ChartThresholdReadout + stereo_chart_identity/stereo_readout_transfer
(R2#1/#7, identity PROVED), state-coordinate margin hypothesis
(R2#5), slab working set (R2#6), machine-parametric conditional
main_assembled (R2#8).  Revision 2 (R1) fixes:
* R1#7: `haltIndicator_exists` now requires the state coordinate to
  have FINITE range on the lattice (a nonconstant polynomial is
  unbounded over infinitely many tubes; the counterexample
  `enc n = n` refuted the v1 statement).
* R1#8: `HaltIndicator` carries a working set `W` with global
  `0 ≤ H ≤ 1` on `W` (paper's pointwise bound on the working set,
  def:working-set), not only on configuration tubes; the latch lemma
  takes trajectory-in-`W` as hypothesis.
* R1#9: the stable-window hypothesis is indexed to the POST-transition
  configuration `step^[j+1]` (paper cor:stable-window-tracking,
  main.tex:1009-1020).
* R1#10 (⊃ self-audit S3): indicator and latch parameters `I, K, R`
  are fixed UNIFORMLY before `∀ w` in the assembled statement — one
  vector field for all inputs.
* R1#11 (= self-audit S4): `compactification_exists` strengthened
  from tangency-only (vacuous via `Y = 0`) to: concrete inverse
  stereographic embedding, tangency, AND trajectory transfer under a
  strictly monotone unbounded time change.  `Y = 0` no longer
  qualifies (a nonconstant Euclidean solution transfers to a
  nonconstant sphere solution).

Remaining obligations P7–P13; no new axioms.
-/

import Ripple.BoundedUniversality.BGP.PhaseClock
import Ripple.BoundedUniversality.GPAC.TimeChangeConstruct
import Mathlib

namespace Ripple.BoundedUniversality.BGP

open Real

/-! ## The stable-phase gate (lem:rational-gate) -/

/-- Stable-phase gate `G_R(s, c) = ((1 - c)/2)^R` along the
oscillator: `gPulse R t = ((1 - cos t)/2)^R`, peaked at `t = π`
(mod 2π) — the mid-cycle stable window, away from both sampling
pulses. -/
noncomputable def gPulse (R : ℕ) (t : ℝ) : ℝ := ((1 - Real.cos t) / 2) ^ R

theorem gPulse_nonneg (R : ℕ) (t : ℝ) : 0 ≤ gPulse R t := by
  apply pow_nonneg
  nlinarith [Real.cos_le_one t]

theorem gPulse_le_one (R : ℕ) (t : ℝ) : gPulse R t ≤ 1 := by
  apply pow_le_one₀
  · nlinarith [Real.cos_le_one t]
  · nlinarith [Real.neg_one_le_cos t]

theorem gPulse_continuous (R : ℕ) : Continuous (gPulse R) := by
  unfold gPulse
  fun_prop

private theorem sqrt_three_le_87_div_50 : Real.sqrt 3 ≤ (87 : ℝ) / 50 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sqrt_nonneg (3 : ℝ)]

private theorem sqrt_three_ge_43_div_25 : (43 : ℝ) / 25 ≤ Real.sqrt 3 := by
  rw [Real.le_sqrt' (by norm_num)]
  norm_num

private theorem cos_pi_div_twelve_ge_24_div_25 :
    (24 : ℝ) / 25 ≤ Real.cos (π / 12) := by
  have hhalf := Real.cos_half (x := π / 6)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsqrt : (24 : ℝ) / 25 ≤ Real.sqrt (((1 + Real.cos (π / 6)) / 2)) := by
    rw [Real.le_sqrt' (by norm_num)]
    rw [Real.cos_pi_div_six]
    nlinarith [sqrt_three_ge_43_div_25]
  rw [show π / 12 = π / 6 / 2 by ring]
  rw [hhalf]
  exact hsqrt

private theorem cos_shift_eq_neg_cos_center (j : ℕ) (t : ℝ) :
    Real.cos t = -Real.cos (t - 2 * π * (j : ℝ) - π) := by
  have hteq : t =
      ((t - 2 * π * (j : ℝ) - π) + π) + (j : ℕ) * (2 * π) := by
    push_cast
    ring
  conv_lhs => rw [hteq]
  rw [Real.cos_add_nat_mul_two_pi, Real.cos_add_pi]

private theorem cos_stable_inner_le (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j + 11 * π / 12 ≤ t)
    (h2 : t ≤ 2 * π * j + 13 * π / 12) :
    Real.cos t ≤ -(24 : ℝ) / 25 := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxabs : |x| ≤ π / 12 := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> linarith
  have hcosx : (24 : ℝ) / 25 ≤ Real.cos x := by
    rw [← Real.cos_abs x]
    calc
      (24 : ℝ) / 25 ≤ Real.cos (π / 12) := cos_pi_div_twelve_ge_24_div_25
      _ ≤ Real.cos |x| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
            (by linarith) hxabs
  rw [cos_shift_eq_neg_cos_center j t]
  linarith

private theorem cos_off_left_ge (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j ≤ t)
    (h2 : t ≤ 2 * π * j + 5 * π / 6) :
    -(87 : ℝ) / 100 ≤ Real.cos t := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxlo : π / 6 ≤ |x| := by
    rw [le_abs]
    right
    simp only [hx]
    linarith
  have hxhi : |x| ≤ π := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> linarith
  have hcosx : Real.cos x ≤ (87 : ℝ) / 100 := by
    rw [← Real.cos_abs x]
    calc
      Real.cos |x| ≤ Real.cos (π / 6) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
            hxhi hxlo
      _ = Real.sqrt 3 / 2 := Real.cos_pi_div_six
      _ ≤ (87 : ℝ) / 100 := by
          nlinarith [sqrt_three_le_87_div_50]
  rw [cos_shift_eq_neg_cos_center j t]
  linarith

private theorem cos_off_right_ge (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j + 7 * π / 6 ≤ t)
    (h2 : t ≤ 2 * π * (j + 1)) :
    -(87 : ℝ) / 100 ≤ Real.cos t := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxlo : π / 6 ≤ |x| := by
    rw [le_abs]
    left
    simp only [hx]
    linarith
  have hxhi : |x| ≤ π := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> nlinarith [hπ, h1, h2]
  have hcosx : Real.cos x ≤ (87 : ℝ) / 100 := by
    rw [← Real.cos_abs x]
    calc
      Real.cos |x| ≤ Real.cos (π / 6) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
            hxhi hxlo
      _ = Real.sqrt 3 / 2 := Real.cos_pi_div_six
      _ ≤ (87 : ℝ) / 100 := by
          nlinarith [sqrt_three_le_87_div_50]
  rw [cos_shift_eq_neg_cos_center j t]
  linarith

private theorem gPulse_ge_stable_inner {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j + 11 * π / 12 ≤ t)
    (h2 : t ≤ 2 * π * j + 13 * π / 12) :
    ((49 : ℝ) / 50) ^ R ≤ gPulse R t := by
  unfold gPulse
  apply pow_le_pow_left₀ (by norm_num)
  have hcos := cos_stable_inner_le j h1 h2
  linarith

private theorem gPulse_le_off_left {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j ≤ t)
    (h2 : t ≤ 2 * π * j + 5 * π / 6) :
    gPulse R t ≤ ((187 : ℝ) / 200) ^ R := by
  unfold gPulse
  apply pow_le_pow_left₀
  · nlinarith [Real.cos_le_one t]
  · have hcos := cos_off_left_ge j h1 h2
    linarith

private theorem gPulse_le_off_right {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j + 7 * π / 6 ≤ t)
    (h2 : t ≤ 2 * π * (j + 1)) :
    gPulse R t ≤ ((187 : ℝ) / 200) ^ R := by
  unfold gPulse
  apply pow_le_pow_left₀
  · nlinarith [Real.cos_le_one t]
  · have hcos := cos_off_right_ge j h1 h2
    linarith

private theorem latch_intInt (f : ℝ → ℝ) (hf : Continuous f) (u v : ℝ) :
    IntervalIntegrable f MeasureTheory.volume u v :=
  hf.intervalIntegrable u v

private theorem latch_intConst (c u v : ℝ) :
    IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume u v :=
  _root_.intervalIntegrable_const

private theorem gPulse_stable_inner_integral_lower (R j : ℕ) :
    (π / 6) * ((49 : ℝ) / 50) ^ R ≤
      ∫ t in (2 * π * j + 11 * π / 12)..(2 * π * j + 13 * π / 12),
        gPulse R t := by
  have hπ := Real.pi_pos
  have hab : 2 * π * (j : ℝ) + 11 * π / 12 ≤
      2 * π * (j : ℝ) + 13 * π / 12 := by linarith
  have hint := latch_intInt (gPulse R) (gPulse_continuous R)
  have hconst :
      (∫ _t in (2 * π * (j : ℝ) + 11 * π / 12)..
          (2 * π * (j : ℝ) + 13 * π / 12), ((49 : ℝ) / 50) ^ R)
        = (π / 6) * ((49 : ℝ) / 50) ^ R := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab (latch_intConst _ _ _)
    (hint _ _)
  intro t ht
  exact gPulse_ge_stable_inner ht.1 ht.2

private theorem gPulse_off_left_integral_upper (R j : ℕ) :
    (∫ t in (2 * π * j)..(2 * π * j + 5 * π / 6), gPulse R t)
      ≤ (5 * π / 6) * ((187 : ℝ) / 200) ^ R := by
  have hπ := Real.pi_pos
  have hab : 2 * π * (j : ℝ) ≤ 2 * π * (j : ℝ) + 5 * π / 6 := by
    linarith
  have hint := latch_intInt (gPulse R) (gPulse_continuous R)
  have hconst :
      (∫ _t in (2 * π * (j : ℝ))..(2 * π * (j : ℝ) + 5 * π / 6),
          ((187 : ℝ) / 200) ^ R)
        = (5 * π / 6) * ((187 : ℝ) / 200) ^ R := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab (hint _ _)
    (latch_intConst _ _ _)
  intro t ht
  exact gPulse_le_off_left ht.1 ht.2

private theorem gPulse_off_right_integral_upper (R j : ℕ) :
    (∫ t in (2 * π * j + 7 * π / 6)..(2 * π * ((j : ℝ) + 1)), gPulse R t)
      ≤ (5 * π / 6) * ((187 : ℝ) / 200) ^ R := by
  have hπ := Real.pi_pos
  have hab : 2 * π * (j : ℝ) + 7 * π / 6 ≤ 2 * π * ((j : ℝ) + 1) := by
    linarith
  have hint := latch_intInt (gPulse R) (gPulse_continuous R)
  have hconst :
      (∫ _t in (2 * π * (j : ℝ) + 7 * π / 6)..(2 * π * ((j : ℝ) + 1)),
          ((187 : ℝ) / 200) ^ R)
        = (5 * π / 6) * ((187 : ℝ) / 200) ^ R := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab (hint _ _)
    (latch_intConst _ _ _)
  intro t ht
  apply gPulse_le_off_right ht.1
  simpa [Nat.cast_add, Nat.cast_one] using ht.2

private theorem gPulse_stable_integral_lower (R j : ℕ) :
    (π / 6) * ((49 : ℝ) / 50) ^ R ≤
      ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
        gPulse R t := by
  have hπ := Real.pi_pos
  have hinner :=
    gPulse_stable_inner_integral_lower R j
  have hmono :
      (∫ t in (2 * π * j + 11 * π / 12)..(2 * π * j + 13 * π / 12),
        gPulse R t)
        ≤ ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
          gPulse R t := by
    apply intervalIntegral.integral_mono_interval
    · linarith
    · linarith
    · linarith
    · exact Filter.Eventually.of_forall fun t => gPulse_nonneg R t
    · exact latch_intInt (gPulse R) (gPulse_continuous R) _ _
  exact le_trans hinner hmono

private theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have h2exp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h ⊢
    exact h
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr h2exp

private theorem latch_parameter_exists :
    ∃ (K : ℚ) (R : ℕ), 0 < K ∧
      (∀ j : ℕ,
        Real.exp (-((K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t)) ≤ (1 / 2 : ℝ)) ∧
      (K : ℝ) * ((187 : ℝ) / 200) ^ R * (5 * π / 6) ≤ (1 / 100 : ℝ) := by
  let q : ℝ := (187 : ℝ) / 196
  have hq0 : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  obtain ⟨R, hR⟩ : ∃ R : ℕ, q ^ R < (3 : ℝ) / 2500 :=
    exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 3 / 2500) hq1
  let Glo : ℝ := (π / 6) * ((49 : ℝ) / 50) ^ R
  have hGlo_pos : 0 < Glo := by
    dsimp [Glo]
    positivity
  let N : ℕ := Nat.ceil (1 / Glo)
  let K : ℚ := (N : ℚ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.ceil_pos.mpr (by positivity)
  have hKpos : 0 < K := by
    dsimp [K]
    exact_mod_cast hNpos
  refine ⟨K, R, hKpos, ?_, ?_⟩
  · intro j
    have hceil : (1 / Glo : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
    have hKGlo : 1 ≤ (K : ℝ) * Glo := by
      have := mul_le_mul_of_nonneg_right hceil hGlo_pos.le
      have hcast : (K : ℝ) = (N : ℝ) := by norm_num [K]
      rw [hcast] 
      rwa [one_div_mul_cancel hGlo_pos.ne'] at this
    have hint :=
      gPulse_stable_integral_lower R j
    have hKnonneg : 0 ≤ (K : ℝ) := by exact_mod_cast hKpos.le
    have hprod :
        1 ≤ (K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t := by
      calc
        1 ≤ (K : ℝ) * Glo := hKGlo
        _ ≤ (K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t := by
              apply mul_le_mul_of_nonneg_left
              · simpa [Glo] using hint
              · exact hKnonneg
    calc
      Real.exp (-((K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t))
          ≤ Real.exp (-1) := by
            apply Real.exp_le_exp.mpr
            linarith
      _ ≤ (1 / 2 : ℝ) := exp_neg_one_le_half
  · have hceil_lt : (N : ℝ) < 1 / Glo + 1 := by
      dsimp [N]
      exact Nat.ceil_lt_add_one (by positivity)
    have hKle : (K : ℝ) ≤ 1 / Glo + 1 := by
      have hcast : (K : ℝ) = (N : ℝ) := by norm_num [K]
      rw [hcast]
      exact hceil_lt.le
    have hoff_le_q : ((187 : ℝ) / 200) ^ R ≤ q ^ R := by
      apply pow_le_pow_left₀
      · norm_num
      · norm_num [q]
    have hπ4 : π ≤ (4 : ℝ) := Real.pi_le_four
    have hleak_bound :
        (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
          ≤ ((25 : ℝ) / 3) * q ^ R := by
      have hstable_pos : 0 < ((49 : ℝ) / 50) ^ R := by positivity
      have hoff_nonneg : 0 ≤ ((187 : ℝ) / 200) ^ R := by positivity
      have hqpow_nonneg : 0 ≤ q ^ R := by positivity
      calc
        (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
            = (5 * (((187 : ℝ) / 200) ^ R / (((49 : ℝ) / 50) ^ R)) +
                (5 * π / 6) * ((187 : ℝ) / 200) ^ R) := by
                field_simp [Glo, hGlo_pos.ne', Real.pi_ne_zero, hstable_pos.ne']
                ring
        _ ≤ 5 * q ^ R + (5 * π / 6) * q ^ R := by
              have hratio :
                  ((187 : ℝ) / 200) ^ R / (((49 : ℝ) / 50) ^ R) = q ^ R := by
                rw [← div_pow]
                congr 1
                norm_num [q]
              rw [hratio]
              gcongr
        _ ≤ 5 * q ^ R + (10 / 3 : ℝ) * q ^ R := by
              have hcoef : 5 * π / 6 ≤ (10 / 3 : ℝ) := by
                nlinarith [hπ4]
              have hterm :
                  (5 * π / 6) * q ^ R ≤ (10 / 3 : ℝ) * q ^ R :=
                mul_le_mul_of_nonneg_right hcoef hqpow_nonneg
              linarith
        _ = ((25 : ℝ) / 3) * q ^ R := by ring
    calc
      (K : ℝ) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
          ≤ (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6) := by
            gcongr
      _ ≤ ((25 : ℝ) / 3) * q ^ R := hleak_bound
      _ ≤ (1 / 100 : ℝ) := by
            nlinarith [hR]

/-! ## The halt indicator (constr:halt-indicator) -/

/-- A rational halt indicator for machine `Mch` under encoding `E`:
a polynomial `H` over ℚ, a working set `W` (the simulator's working
volume, def:working-set) on which `H` takes values in `[0, 1]`
globally (R1#8), containing all configuration tubes of radius `ρ`,
with `H ≈ 1` on halted-configuration tubes and `H ≈ 0` on
running-configuration tubes. -/
structure HaltIndicator {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d) where
  H : MvPolynomial (Fin d) ℚ
  W : Set (Fin d → ℝ)
  ρ : ℚ
  ηH : ℚ
  ρ_pos : 0 < ρ
  ηH_pos : 0 < ηH
  ηH_lt : ηH < 1/8
  tubes_subset : ∀ (c : Conf) (x : Fin d → ℝ),
    (∀ i, |x i - E.enc c i| ≤ (ρ : ℝ)) → x ∈ W
  in_unit : ∀ x ∈ W,
    0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) x H ∧
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x H ≤ 1
  on_halted : ∀ (c : Conf), Mch.halted c = true → ∀ (x : Fin d → ℝ),
    (∀ i, |x i - E.enc c i| ≤ (ρ : ℝ)) →
    1 - (ηH : ℝ) ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) x H
  on_running : ∀ (c : Conf), Mch.halted c = false → ∀ (x : Fin d → ℝ),
    (∀ i, |x i - E.enc c i| ≤ (ρ : ℝ)) →
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x H ≤ (ηH : ℝ)

noncomputable def HaltIndicator.evalH {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ}
    {E : LatticeEncoding Mch d} (I : HaltIndicator Mch d E)
    (x : Fin d → ℝ) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) x I.H

private theorem HaltIndicator.evalH_continuous_along
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ}
    {E : LatticeEncoding Mch d} (I : HaltIndicator Mch d E)
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀) :
    Continuous fun t => I.evalH (sol.z t) := by
  have hz : Continuous fun t => sol.z t :=
    continuous_pi fun i => sol.cont_z i
  unfold HaltIndicator.evalH
  convert
    (MvPolynomial.continuous_eval
      (p := MvPolynomial.map (algebraMap ℚ ℝ) I.H)).comp hz
    using 1
  ext t
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (sol.z t) I.H

private theorem DiscreteMachine.halted_of_halts_after
    {Conf : Type} [Primcodable Conf] (Mch : DiscreteMachine Conf)
    {w n : ℕ}
    (hn : Mch.halted (Mch.step^[n] (Mch.init w)) = true) :
    ∀ m : ℕ, n ≤ m →
      Mch.halted (Mch.step^[m] (Mch.init w)) = true := by
  intro m hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero =>
      simpa using hn
  | succ k ih =>
      rw [Nat.add_succ, Function.iterate_succ_apply']
      have ih' : Mch.halted (Mch.step^[n + k] (Mch.init w)) = true :=
        ih (Nat.le_add_right n k)
      have hfix :
          Mch.step (Mch.step^[n + k] (Mch.init w)) =
            Mch.step^[n + k] (Mch.init w) :=
        Mch.halted_absorbing _ ih'
      simpa [hfix] using ih'

private theorem DiscreteMachine.running_of_not_haltsOn
    {Conf : Type} [Primcodable Conf] (Mch : DiscreteMachine Conf)
    {w j : ℕ} (h : ¬ Mch.haltsOn w) :
    Mch.halted (Mch.step^[j] (Mch.init w)) = false := by
  cases hj : Mch.halted (Mch.step^[j] (Mch.init w)) with
  | false => rfl
  | true =>
      exact False.elim (h ⟨j, hj⟩)

-- P8 `haltIndicator_exists` now lives in BernsteinSeparator.lean (proved).

/-! ## The latch (constr:halt-latch, lem:halt-latch) -/

/-- A latch solution riding on an iterator solution: the scalar latch
coordinate `a` driven by the gated indicator of the `z`-channel. -/
structure LatchSol {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (R : ℕ) where
  a : ℝ → ℝ
  init_a : a 0 = 0
  ode_a : ∀ t : ℝ,
    HasDerivAt a (K * gPulse R t * (Hval (sol.z t) - a t)) t

/-- Monotonicity from pointwise `HasDerivAt` with nonnegative
derivative on `[0, t]`. -/
private theorem nonneg_of_hasDerivAt_nonneg
    (f : ℝ → ℝ) (f' : ℝ → ℝ)
    (hderiv : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hpos : ∀ s : ℝ, 0 ≤ s → 0 ≤ f' s)
    (h0 : 0 ≤ f 0) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · exact (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
    · intro s hs
      exact ((hderiv s).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hderiv s).deriv]
      exact hpos s hs.1.le
  have := hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
  linarith

/-- **P7, forward invariance of `[0, 1]`** for the latch (paper
lem:bounded-working-volume, latch part): the field points inward at
the endpoints whenever `0 ≤ Hval ∘ z ≤ 1` along the trajectory. -/
theorem latch_mem_unitInterval
    {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (hK : 0 < K) (R : ℕ)
    (L : LatchSol sol Hval K R)
    (hH : ∀ t : ℝ, 0 ≤ t → 0 ≤ Hval (sol.z t) ∧ Hval (sol.z t) ≤ 1) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ L.a t ∧ L.a t ≤ 1 := by
  intro t ht
  set φ : ℝ → ℝ := fun s => K * gPulse R s with hφdef
  have hφcont : Continuous φ := by
    have : Continuous (gPulse R) := by
      unfold gPulse
      fun_prop
    fun_prop
  set Φ : ℝ → ℝ := fun s => ∫ τ in (0:ℝ)..s, φ τ with hΦdef
  have hΦderiv : ∀ s : ℝ, HasDerivAt Φ (φ s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hφcont.intervalIntegrable 0 s)
      (hφcont.stronglyMeasurableAtFilter _ _)
      hφcont.continuousAt
  set E : ℝ → ℝ := fun s => Real.exp (Φ s) with hEdef
  have hEderiv : ∀ s : ℝ, HasDerivAt E (φ s * E s) s := by
    intro s
    have := (hΦderiv s).exp
    convert this using 1
    simp only [hEdef]
    ring
  have hEpos : ∀ s, 0 < E s := fun s => Real.exp_pos _
  have hE0 : E 0 = 1 := by simp [hEdef, hΦdef]
  constructor
  · have hfderiv : ∀ s : ℝ, HasDerivAt (fun τ => L.a τ * E τ)
        (K * gPulse R s * Hval (sol.z s) * E s) s := by
      intro s
      have h1 := (L.ode_a s).mul (hEderiv s)
      convert h1 using 1
      simp only [hφdef, hEdef]
      ring
    have h := nonneg_of_hasDerivAt_nonneg (fun τ => L.a τ * E τ) _
      hfderiv
      (fun s hs => by
        have hHs := (hH s hs).1
        have := (hEpos s).le
        have := gPulse_nonneg R s
        positivity)
      (by simp [L.init_a]) t ht
    nlinarith [hEpos t, h]
  · have hfderiv : ∀ s : ℝ, HasDerivAt (fun τ => (1 - L.a τ) * E τ)
        (K * gPulse R s * (1 - Hval (sol.z s)) * E s) s := by
      intro s
      have h0 : HasDerivAt (fun τ => 1 - L.a τ)
          (-(K * gPulse R s * (Hval (sol.z s) - L.a s))) s :=
        (L.ode_a s).const_sub 1
      have h1 := h0.mul (hEderiv s)
      convert h1 using 1
      simp only [hφdef, hEdef]
      ring
    have h := nonneg_of_hasDerivAt_nonneg (fun τ => (1 - L.a τ) * E τ) _
      hfderiv
      (fun s hs => by
        have hHs := (hH s hs).2
        have h1 : 0 ≤ 1 - Hval (sol.z s) := by linarith
        have := (hEpos s).le
        have := gPulse_nonneg R s
        positivity)
      (by simp [L.init_a, hE0]) t ht
    nlinarith [hEpos t, h]

private theorem latch_one_sided_target_upper
    (A : ℝ) (hA : 0 < A) (φ w y : ℝ → ℝ)
    (a b η : ℝ) (hab : a ≤ b)
    (hφ_cont : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc a b, 0 ≤ φ t)
    (hwη : ∀ t ∈ Set.Icc a b, w t ≤ η)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (A * φ t * (w t - y t)) t) :
    y b ≤
      Real.exp (-(A * ∫ t in a..b, φ t)) * y a +
        (1 - Real.exp (-(A * ∫ t in a..b, φ t))) * η := by
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, φ s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (φ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hφ_cont.intervalIntegrable a t)
      (hφ_cont.stronglyMeasurableAtFilter _ _)
      hφ_cont.continuousAt
  have hΦa : Φ a = 0 := by simp [hΦdef]
  have hΦcont : Continuous Φ := by
    exact continuous_iff_continuousAt.mpr fun t => (hΦderiv t).continuousAt
  set Efun : ℝ → ℝ := fun t => Real.exp (A * Φ t) with hEdef
  have hEderiv : ∀ t : ℝ,
      HasDerivAt Efun (A * φ t * Efun t) t := by
    intro t
    have h1 : HasDerivAt (fun τ => A * Φ τ) (A * φ t) t :=
      (hΦderiv t).const_mul A
    have h2 := h1.exp
    convert h2 using 1
    simp [hEdef]
    ring
  have hEpos : ∀ t, 0 < Efun t := fun t => Real.exp_pos _
  have hEa : Efun a = 1 := by simp [hEdef, hΦa]
  set v : ℝ → ℝ := fun t => (y t - η) * Efun t with hvdef
  have hvderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt v (A * φ t * (w t - η) * Efun t) t := by
    intro t ht
    have h1 : HasDerivAt (fun τ => y τ - η)
        (A * φ t * (w t - y t)) t := (hy t ht).sub_const η
    have h2 := h1.mul (hEderiv t)
    convert h2 using 1
    simp [hvdef, hEdef]
    ring
  have hvanti : AntitoneOn v (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · intro t ht
      exact (hvderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact ((hvderiv t (interior_subset ht)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [(hvderiv t (interior_subset ht)).deriv]
      have hφt := hφ0 t (interior_subset ht)
      have hwt := hwη t (interior_subset ht)
      have hEt : 0 ≤ Efun t := (hEpos t).le
      have hwsub : w t - η ≤ 0 := by linarith
      have hcoef : 0 ≤ A * φ t * Efun t := by positivity
      have hnonpos : A * φ t * (w t - η) * Efun t ≤ 0 := by
        calc
          A * φ t * (w t - η) * Efun t =
              (A * φ t * Efun t) * (w t - η) := by ring
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcoef hwsub
      simpa using hnonpos
  have hvle : v b ≤ v a :=
    hvanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  have hEbpos := hEpos b
  have hmain : y b - η ≤ (y a - η) / Efun b := by
    have hvle' : (y b - η) * Efun b ≤ (y a - η) * Efun a := by
      simpa [hvdef] using hvle
    rw [hEa] at hvle'
    rw [le_div_iff₀ hEbpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hvle'
  have hEinv :
      (y a - η) / Efun b =
        Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) := by
    simp [hEdef, hΦdef, div_eq_mul_inv, Real.exp_neg, mul_comm, mul_left_comm,
      mul_assoc]
  rw [hEinv] at hmain
  have hfinal :
      y b ≤ Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) + η := by
    linarith
  calc
    y b ≤ Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) + η := hfinal
    _ = Real.exp (-(A * ∫ t in a..b, φ t)) * y a +
        (1 - Real.exp (-(A * ∫ t in a..b, φ t))) * η := by ring

private noncomputable def latchSample (j : ℕ) : ℝ :=
  2 * π * (j : ℝ) + 7 * π / 6

private noncomputable def latchStableStart (j : ℕ) : ℝ :=
  2 * π * (j : ℝ) + 5 * π / 6

private theorem latchSample_add (j n : ℕ) :
    latchSample (j + n) = latchSample j + 2 * π * (n : ℝ) := by
  unfold latchSample
  push_cast
  ring

private theorem latchSample_succ (j : ℕ) :
    latchSample (j + 1) = 2 * π * ((j : ℝ) + 1) + 7 * π / 6 := by
  unfold latchSample
  push_cast
  ring

private theorem latchSample_nonneg (j : ℕ) : 0 ≤ latchSample j := by
  unfold latchSample
  positivity

private theorem latchStableStart_nonneg (j : ℕ) : 0 ≤ latchStableStart j := by
  unfold latchStableStart
  positivity

private theorem latch_cycle_cover {base t : ℝ} (hbase : base ≤ t) :
    ∃ n : ℕ, base + 2 * π * (n : ℝ) ≤ t ∧
      t ≤ base + 2 * π * ((n : ℝ) + 1) := by
  let p : ℝ := 2 * π
  have hp : 0 < p := by
    dsimp [p]
    positivity
  let x : ℝ := (t - base) / p
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (sub_nonneg.mpr hbase) hp.le
  refine ⟨Nat.floor x, ?_, ?_⟩
  · have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hmul := mul_le_mul_of_nonneg_left hfloor hp.le
    have hpx : p * x = t - base := by
      dsimp [x]
      field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith
  · have hlt : x < ((Nat.floor x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmul := mul_lt_mul_of_pos_left hlt hp
    have hpx : p * x = t - base := by
      dsimp [x]
      field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith

private theorem convex_combo_le_max {θ x η : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * x + (1 - θ) * η ≤ max x η := by
  by_cases hx : x ≤ η
  · have hmax : max x η = η := max_eq_right hx
    rw [hmax]
    nlinarith
  · have hx' : η ≤ x := le_of_lt (lt_of_not_ge hx)
    have hmax : max x η = x := max_eq_left hx'
    rw [hmax]
    nlinarith

private theorem latch_drift_upper
    (K : ℝ) (hK0 : 0 ≤ K) (R : ℕ)
    (y w : ℝ → ℝ) (a b C ε : ℝ)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hC0 : 0 ≤ C)
    (hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1)
    (hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t ∧ w t ≤ 1)
    (hy : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (K * gPulse R t * (w t - y t)) t)
    (hg : ∀ t ∈ Set.Icc a b, gPulse R t ≤ C)
    (hε : K * C * (b - a) ≤ ε) :
    y b ≤ y a + ε := by
  have hbound : ∀ t ∈ Set.Icc a b,
      |K * gPulse R t * (w t - y t)| ≤ K * C := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    have hyt := hy01 t ht0
    have hwt := hw01 t ht0
    have hwy : |w t - y t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hg0 := gPulse_nonneg R t
    have hgC := hg t ht
    calc
      |K * gPulse R t * (w t - y t)|
          = K * gPulse R t * |w t - y t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_nonneg hg0]
      _ ≤ K * C * 1 := by
            gcongr
      _ = K * C := by ring
  have hhold := hold_bound y
    (fun t => K * gPulse R t * (w t - y t)) (K * C) a b hab hy hbound
  have hdiff : y b - y a ≤ ε := by
    calc
      y b - y a ≤ |y b - y a| := le_abs_self _
      _ ≤ K * C * (b - a) := hhold
      _ ≤ ε := hε
  linarith

private theorem latch_stable_max_upper
    (K : ℝ) (hK : 0 < K) (R : ℕ)
    (y w : ℝ → ℝ) (η a b : ℝ)
    (hab : a ≤ b)
    (hwη : ∀ t ∈ Set.Icc a b, w t ≤ η)
    (hy : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (K * gPulse R t * (w t - y t)) t) :
    y b ≤ max (y a) η := by
  have hmain := latch_one_sided_target_upper K hK (gPulse R) w y a b η hab
    (gPulse_continuous R)
    (fun t ht => gPulse_nonneg R t)
    hwη hy
  set θ : ℝ := Real.exp (-(K * ∫ t in a..b, gPulse R t)) with hθ
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    exact (Real.exp_pos _).le
  have hint0 : 0 ≤ ∫ t in a..b, gPulse R t :=
    intervalIntegral.integral_nonneg hab (fun t _ => gPulse_nonneg R t)
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hK.le, hint0]
  exact le_trans (by simpa [hθ] using hmain) (convex_combo_le_max hθ0 hθ1)

private theorem latch_eventual_upper
    (K : ℝ) (hK : 0 < K) (R : ℕ)
    (hθ : ∀ j : ℕ,
      Real.exp (-(K *
        ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
          gPulse R t)) ≤ (1 / 2 : ℝ))
    (hℓ : K * ((187 : ℝ) / 200) ^ R * (5 * π / 6) ≤ (1 / 100 : ℝ))
    (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 8)
    (j₀ : ℕ) (y w : ℝ → ℝ)
    (hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1)
    (hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t ∧ w t ≤ 1)
    (hy : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (K * gPulse R t * (w t - y t)) t)
    (hwStable : ∀ j : ℕ, j₀ ≤ j →
      ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
        w t ≤ η) :
    ∃ T : ℝ, ∀ t ≥ T, 0 ≤ y t ∧ y t ≤ 1 / 4 := by
  let C : ℝ := ((187 : ℝ) / 200) ^ R
  let ℓ : ℝ := (1 / 100 : ℝ)
  let B : ℝ := η + 4 * ℓ
  have hK0 : 0 ≤ K := hK.le
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hℓ0 : 0 ≤ ℓ := by norm_num [ℓ]
  have hleak : K * C * (5 * π / 6) ≤ ℓ := by
    simpa [C, ℓ] using hℓ
  have hoff_right :
      ∀ j : ℕ, ∀ t ∈ Set.Icc (latchSample j) (2 * π * ((j : ℝ) + 1)),
        y t ≤ y (latchSample j) + ℓ := by
    intro j t ht
    have hab : latchSample j ≤ t := ht.1
    have ha0 : 0 ≤ latchSample j := latchSample_nonneg j
    apply latch_drift_upper K hK0 R y w (latchSample j) t C ℓ hab ha0 hC0
      hy01 hw01
    · intro s hs
      exact hy s (le_trans ha0 hs.1)
    · intro s hs
      apply gPulse_le_off_right (j := j)
      · simpa [latchSample] using hs.1
      · exact le_trans hs.2 ht.2
    · have hlen : t - latchSample j ≤ 5 * π / 6 := by
        unfold latchSample at ht ⊢
        nlinarith [ht.2]
      calc
        K * C * (t - latchSample j) ≤ K * C * (5 * π / 6) := by
          gcongr
        _ ≤ ℓ := hleak
  have hoff_left :
      ∀ j : ℕ, ∀ t ∈ Set.Icc (2 * π * (j : ℝ)) (latchStableStart j),
        y t ≤ y (2 * π * (j : ℝ)) + ℓ := by
    intro j t ht
    have hab : 2 * π * (j : ℝ) ≤ t := ht.1
    have ha0 : 0 ≤ 2 * π * (j : ℝ) := by positivity
    apply latch_drift_upper K hK0 R y w (2 * π * (j : ℝ)) t C ℓ hab ha0 hC0
      hy01 hw01
    · intro s hs
      exact hy s (le_trans ha0 hs.1)
    · intro s hs
      apply gPulse_le_off_left (j := j)
      · exact hs.1
      · exact le_trans hs.2 ht.2
    · have hlen : t - 2 * π * (j : ℝ) ≤ 5 * π / 6 := by
        unfold latchStableStart at ht
        nlinarith [ht.2]
      calc
        K * C * (t - 2 * π * (j : ℝ)) ≤ K * C * (5 * π / 6) := by
          gcongr
        _ ≤ ℓ := hleak
  have hstable :
      ∀ j : ℕ, j₀ ≤ j → ∀ t ∈ Set.Icc (latchStableStart j) (latchSample j),
        y t ≤ max (y (latchStableStart j)) η := by
    intro j hj t ht
    have hab : latchStableStart j ≤ t := ht.1
    apply latch_stable_max_upper K hK R y w η (latchStableStart j) t hab
    · intro s hs
      apply hwStable j hj s
      constructor
      · simpa [latchStableStart] using hs.1
      · exact le_trans hs.2 ht.2
    · intro s hs
      exact hy s (le_trans (latchStableStart_nonneg j) hs.1)
  have hcycle :
      ∀ j : ℕ, j₀ ≤ j →
        y (latchSample (j + 1)) ≤
          Real.exp (-(K *
            ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
              (2 * π * (j + 1) + 7 * π / 6), gPulse R t)) *
              y (latchSample j) + 2 * ℓ +
            (1 - Real.exp (-(K *
              ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
                (2 * π * (j + 1) + 7 * π / 6), gPulse R t))) * η := by
    intro j hj
    let m : ℝ := 2 * π * ((j : ℝ) + 1)
    let s : ℝ := 2 * π * ((j : ℝ) + 1) + 5 * π / 6
    let e : ℝ := latchSample (j + 1)
    have hsam_m : latchSample j ≤ m := by
      dsimp [m, latchSample]
      nlinarith [Real.pi_pos]
    have hm_s : m ≤ s := by
      dsimp [m, s]
      nlinarith [Real.pi_pos]
    have hs_e : s ≤ e := by
      dsimp [s, e, latchSample]
      push_cast
      nlinarith [Real.pi_pos]
    have hm_bound : y m ≤ y (latchSample j) + ℓ := by
      apply hoff_right j m
      constructor
      · exact hsam_m
      · rfl
    have hs_bound : y s ≤ y (latchSample j) + 2 * ℓ := by
      have hs1 : y s ≤ y m + ℓ := by
        have := hoff_left (j + 1) s
        have hmem : s ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ)) (latchStableStart (j + 1)) := by
          constructor
          · dsimp [s]
            push_cast
            nlinarith [Real.pi_pos]
          · dsimp [s, latchStableStart]
            push_cast
            exact le_rfl
        have hthis := this hmem
        simpa [m, s, Nat.cast_add, Nat.cast_one] using hthis
      linarith
    have hmain := latch_one_sided_target_upper K hK (gPulse R) w y s e η hs_e
      (gPulse_continuous R)
      (fun t ht => gPulse_nonneg R t)
      (by
        intro t ht
        apply hwStable (j + 1) (le_trans hj (Nat.le_succ j)) t
        constructor
        · simpa [s, latchStableStart, Nat.cast_add, Nat.cast_one] using ht.1
        · simpa [e, latchSample, Nat.cast_add, Nat.cast_one] using ht.2)
      (by
        intro t ht
        exact hy t (le_trans (by dsimp [s]; positivity) ht.1))
    have hθnonneg :
        0 ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) :=
      (Real.exp_pos _).le
    calc
      y (latchSample (j + 1)) = y e := rfl
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) * y s +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := hmain
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) *
            (y (latchSample j) + 2 * ℓ) +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := by
            gcongr
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) * y (latchSample j) +
            2 * ℓ +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := by
            have hθle : Real.exp (-(K * ∫ t in s..e, gPulse R t)) ≤ 1 := by
              apply Real.exp_le_one_iff.mpr
              have hint0 : 0 ≤ ∫ t in s..e, gPulse R t :=
                intervalIntegral.integral_nonneg hs_e (fun t _ => gPulse_nonneg R t)
              nlinarith [hK.le, hint0]
            nlinarith [hℓ0, hθnonneg, hθle]
      _ = Real.exp (-(K *
            ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
              (2 * π * (j + 1) + 7 * π / 6), gPulse R t)) *
              y (latchSample j) + 2 * ℓ +
            (1 - Real.exp (-(K *
              ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
                (2 * π * (j + 1) + 7 * π / 6), gPulse R t))) * η := by
            congr 3 <;> simp [s, e, latchSample, Nat.cast_add, Nat.cast_one]
  have hsample :
      ∀ n : ℕ, y (latchSample (j₀ + n)) ≤ B + (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
        have hyb := (hy01 (latchSample j₀) (latchSample_nonneg j₀)).2
        dsimp [B]
        norm_num
        nlinarith [hη0, hℓ0, hyb]
    | succ n ih =>
        have hjle : j₀ ≤ j₀ + n := Nat.le_add_right _ _
        have hrec := hcycle (j₀ + n) hjle
        have htheta := hθ (j₀ + n + 1)
        have htheta0 :
            0 ≤ Real.exp (-(K *
              ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) :=
          (Real.exp_pos _).le
        have hstep :
            y (latchSample (j₀ + (n + 1))) ≤
              B + (1 / 2 : ℝ) ^ (n + 1) := by
          have hrec' :
              y (latchSample (j₀ + (n + 1))) ≤
                Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) *
                    y (latchSample (j₀ + n)) + 2 * ℓ +
                  (1 - Real.exp (-(K *
                    ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                      (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))) * η := by
            simpa [Nat.add_assoc] using hrec
          calc
            y (latchSample (j₀ + (n + 1))) ≤
                Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) *
                    y (latchSample (j₀ + n)) + 2 * ℓ +
                  (1 - Real.exp (-(K *
                    ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                      (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))) * η := hrec'
            _ ≤ B + (1 / 2 : ℝ) ^ (n + 1) := by
              have hpownonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
              have hpowstep : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) * (1 / 2) ^ n := by
                rw [pow_succ]
                ring
              set θv : ℝ := Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))
              have hθv0 : 0 ≤ θv := by simpa [θv] using htheta0
              have hθv : θv ≤ 1 / 2 := by simpa [θv, Nat.cast_add, Nat.cast_one] using htheta
              have hfirst :
                  θv * y (latchSample (j₀ + n)) + 2 * ℓ + (1 - θv) * η
                    ≤ θv * (B + (1 / 2 : ℝ) ^ n) + 2 * ℓ + (1 - θv) * η := by
                gcongr
              have hsecond :
                  θv * (B + (1 / 2 : ℝ) ^ n) + 2 * ℓ + (1 - θv) * η
                    ≤ B + (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
                dsimp [B]
                nlinarith [hθv, hθv0, hpownonneg, hℓ0]
              dsimp [B]
              rw [hpowstep]
              exact le_trans (by simpa [θv] using hfirst) hsecond
        exact hstep
  refine ⟨latchSample (j₀ + 4), ?_⟩
  intro t htT
  have hy_nonneg := (hy01 t (le_trans (latchSample_nonneg (j₀ + 4)) htT)).1
  refine ⟨hy_nonneg, ?_⟩
  obtain ⟨n, hnlo, hnhi⟩ := latch_cycle_cover htT
  let j : ℕ := j₀ + 4 + n
  have hj_ge : j₀ ≤ j := by
    dsimp [j]
    omega
  have hj4 : ∃ m : ℕ, j = j₀ + m ∧ 4 ≤ m := by
    refine ⟨4 + n, ?_, ?_⟩
    · dsimp [j]
      omega
    · omega
  have hsamp_eq : latchSample j = latchSample (j₀ + 4) + 2 * π * (n : ℝ) := by
    simpa [j, Nat.add_assoc] using latchSample_add (j₀ + 4) n
  have hnext_eq : latchSample (j + 1) =
      latchSample (j₀ + 4) + 2 * π * ((n : ℝ) + 1) := by
    simpa [j, Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
      latchSample_add (j₀ + 4) (n + 1)
  have htcycle : t ∈ Set.Icc (latchSample j) (latchSample (j + 1)) := by
    constructor
    · simpa [hsamp_eq] using hnlo
    · simpa [hnext_eq, Nat.cast_add, Nat.cast_one] using hnhi
  obtain ⟨m, hjm, hm4⟩ := hj4
  have hsample_j : y (latchSample j) ≤ B + (1 / 2 : ℝ) ^ m := by
    simpa [hjm] using hsample m
  have hpow_le : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (4 : ℕ) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hm4
  have hsample_j' : y (latchSample j) ≤ B + (1 / 16 : ℝ) := by
    norm_num at hpow_le
    nlinarith
  have hcycle_bound : y t ≤ max (y (latchSample j) + 2 * ℓ) η := by
    let mpt : ℝ := 2 * π * ((j : ℝ) + 1)
    have hmpt_eq : 2 * π * ((j + 1 : ℕ) : ℝ) = mpt := by
      dsimp [mpt]
      rw [Nat.cast_add, Nat.cast_one]
    have hsample_mpt : latchSample j ≤ mpt := by
      change 2 * π * (j : ℝ) + 7 * π / 6 ≤ 2 * π * ((j : ℝ) + 1)
      nlinarith [Real.pi_pos]
    have hm_bound : y mpt ≤ y (latchSample j) + ℓ := by
      apply hoff_right j mpt
      exact ⟨hsample_mpt, le_rfl⟩
    have hstable_left :
        2 * π * ((j + 1 : ℕ) : ℝ) ≤ latchStableStart (j + 1) := by
      change 2 * π * ((j + 1 : ℕ) : ℝ) ≤
        2 * π * ((j + 1 : ℕ) : ℝ) + 5 * π / 6
      exact le_add_of_nonneg_right (by positivity)
    by_cases ht_m : t ≤ mpt
    · have hmem : t ∈ Set.Icc (latchSample j) mpt := ⟨htcycle.1, ht_m⟩
      have h1 := hoff_right j t hmem
      exact le_trans (by nlinarith [hℓ0]) (le_max_left _ _)
    · have hm_t : mpt ≤ t := le_of_lt (lt_of_not_ge ht_m)
      by_cases ht_s : t ≤ latchStableStart (j + 1)
      ·
        have hleft : y t ≤ y mpt + ℓ := by
          have hmem : t ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ))
              (latchStableStart (j + 1)) := by
            constructor
            · rw [hmpt_eq]
              exact hm_t
            · exact ht_s
          have := hoff_left (j + 1) t hmem
          rw [hmpt_eq] at this
          exact this
        exact le_trans (by nlinarith) (le_max_left _ _)
      · have hs_t : latchStableStart (j + 1) ≤ t := le_of_lt (lt_of_not_ge ht_s)
        have hs_bound :
            y (latchStableStart (j + 1)) ≤ y (latchSample j) + 2 * ℓ := by
          have hleft : y (latchStableStart (j + 1)) ≤ y mpt + ℓ := by
            have hmem :
                latchStableStart (j + 1) ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ))
                (latchStableStart (j + 1)) := by
              constructor
              · exact hstable_left
              · exact le_rfl
            have := hoff_left (j + 1) (latchStableStart (j + 1)) hmem
            rw [hmpt_eq] at this
            exact this
          linarith [hm_bound]
        have hstab : y t ≤ max (y (latchStableStart (j + 1))) η := by
          have hmem : t ∈ Set.Icc (latchStableStart (j + 1)) (latchSample (j + 1)) := by
            constructor
            · exact hs_t
            · exact htcycle.2
          exact hstable (j + 1) (le_trans hj_ge (Nat.le_succ j)) t hmem
        have hstab_bound :
            max (y (latchStableStart (j + 1))) η ≤ max (y (latchSample j) + 2 * ℓ) η := by
          apply max_le
          · exact le_trans hs_bound (le_max_left _ _)
          · exact le_max_right _ _
        exact le_trans hstab hstab_bound
  have harith : B + (1 / 16 : ℝ) + 2 * ℓ < 1 / 4 := by
    calc
      B + (1 / 16 : ℝ) + 2 * ℓ = η + (49 / 400 : ℝ) := by
        dsimp [B, ℓ]
        ring
      _ < 1 / 8 + (49 / 400 : ℝ) := by
        linarith [hη]
      _ < 1 / 4 := by
        norm_num
  have hmax_bound : max (y (latchSample j) + 2 * ℓ) η ≤ B + (1 / 16 : ℝ) + 2 * ℓ := by
    apply max_le
    · calc
        y (latchSample j) + 2 * ℓ = 2 * ℓ + y (latchSample j) := by ring
        _ ≤ 2 * ℓ + (B + (1 / 16 : ℝ)) := add_le_add_right hsample_j' (2 * ℓ)
        _ = B + (1 / 16 : ℝ) + 2 * ℓ := by ring
    · dsimp [B]
      linarith [hℓ0]
  exact le_of_lt (lt_of_le_of_lt (le_trans hcycle_bound hmax_bound) harith)

/-- **P9, halt-latch eventual readout** (lem:halt-latch).  Run the
latch on an iterator that all-time tracks at radius `≤ I.ρ` and whose
z-channel stays in the working set `W` (R1#8) and, on the mid-cycle
stable window, in the tube of the POST-transition configuration
`step^[j+1]` (R1#9).  If the machine halts the latch eventually stays
in `[3/4, 1]`; if it never halts, in `[0, 1/4]`.  Parameters `K, R`
are chosen uniformly (independent of `w` — they depend only on `ηH`
and the gate integrals; prop:latch-feasibility). -/
theorem halt_latch_eventual_readout
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (I : HaltIndicator Mch d E) :
    ∃ (K : ℚ) (R : ℕ), 0 < K ∧
      ∀ (A : ℝ), 0 < A → ∀ (M : ℕ) (w : ℕ)
        (sol : IteratorSol d S.evalF A M (orbitPoint Mch E w 0)),
        (∀ j : ℕ, ∀ i,
          |sol.z (2*π*j) i - orbitPoint Mch E w j i| ≤ (I.ρ : ℝ) ∧
          |sol.u (2*π*j) i - orbitPoint Mch E w j i| ≤ (I.ρ : ℝ)) →
        (∀ t : ℝ, 0 ≤ t → sol.z t ∈ I.W) →
        (∀ j : ℕ, ∀ t ∈ Set.Icc (2*π*j + 5*π/6) (2*π*j + 7*π/6),
          ∀ i, |sol.z t i - orbitPoint Mch E w (j+1) i| ≤ (I.ρ : ℝ)) →
        ∀ L : LatchSol sol I.evalH (K : ℝ) R,
          (Mch.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 3/4 ≤ L.a t ∧ L.a t ≤ 1) ∧
          (¬ Mch.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 0 ≤ L.a t ∧ L.a t ≤ 1/4) := by
  classical
  obtain ⟨K, R, hK, hθ, hℓ⟩ := latch_parameter_exists
  refine ⟨K, R, hK, ?_⟩
  intro A hA M w sol _htrack hzW hstable L
  have hKℝ : 0 < (K : ℝ) := by exact_mod_cast hK
  have hη0ℝ : 0 ≤ (I.ηH : ℝ) := by exact_mod_cast I.ηH_pos.le
  have hηltℝ : (I.ηH : ℝ) < 1 / 8 := by
    have h : (I.ηH : ℝ) < ((1 / 8 : ℚ) : ℝ) := by
      exact_mod_cast I.ηH_lt
    norm_num at h
    exact h
  have hHunit : ∀ t : ℝ, 0 ≤ t →
      0 ≤ I.evalH (sol.z t) ∧ I.evalH (sol.z t) ≤ 1 := by
    intro t ht
    exact I.in_unit (sol.z t) (hzW t ht)
  have haUnit : ∀ t : ℝ, 0 ≤ t → 0 ≤ L.a t ∧ L.a t ≤ 1 :=
    latch_mem_unitInterval sol I.evalH (K : ℝ) hKℝ R L hHunit
  constructor
  · intro hhalt
    obtain ⟨jhalt, hjhalt⟩ := hhalt
    let y : ℝ → ℝ := fun t => 1 - L.a t
    let wtar : ℝ → ℝ := fun t => 1 - I.evalH (sol.z t)
    have hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1 := by
      intro t ht
      have ht' := haUnit t ht
      dsimp [y]
      constructor <;> linarith
    have hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ wtar t ∧ wtar t ≤ 1 := by
      intro t ht
      have ht' := hHunit t ht
      dsimp [wtar]
      constructor <;> linarith
    have hyderiv : ∀ t : ℝ, 0 ≤ t →
        HasDerivAt y ((K : ℝ) * gPulse R t * (wtar t - y t)) t := by
      intro t _ht
      have h0 : HasDerivAt (fun τ => 1 - L.a τ)
          (-((K : ℝ) * gPulse R t * (I.evalH (sol.z t) - L.a t))) t :=
        (L.ode_a t).const_sub 1
      convert h0 using 1 <;> dsimp [y, wtar] <;> ring
    have hwStable : ∀ j : ℕ, jhalt + 1 ≤ j →
        ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
          wtar t ≤ (I.ηH : ℝ) := by
      intro j hj t ht
      have hclose := hstable j t ht
      have hhalted :
          Mch.halted (Mch.step^[j + 1] (Mch.init w)) = true := by
        apply DiscreteMachine.halted_of_halts_after Mch hjhalt (j + 1)
        omega
      have hH := I.on_halted (Mch.step^[j + 1] (Mch.init w)) hhalted
        (sol.z t) hclose
      dsimp [wtar, HaltIndicator.evalH]
      linarith
    obtain ⟨T, hT⟩ := latch_eventual_upper (K : ℝ) hKℝ R hθ hℓ
      (I.ηH : ℝ) hη0ℝ hηltℝ (jhalt + 1) y wtar
      hy01 hw01 hyderiv hwStable
    refine ⟨T, ?_⟩
    intro t ht
    have hyT := hT t ht
    dsimp [y] at hyT
    constructor
    · linarith
    · linarith
  · intro hnonhalt
    let y : ℝ → ℝ := L.a
    let wtar : ℝ → ℝ := fun t => I.evalH (sol.z t)
    have hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1 := by
      intro t ht
      exact haUnit t ht
    have hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ wtar t ∧ wtar t ≤ 1 := by
      intro t ht
      exact hHunit t ht
    have hyderiv : ∀ t : ℝ, 0 ≤ t →
        HasDerivAt y ((K : ℝ) * gPulse R t * (wtar t - y t)) t := by
      intro t _ht
      simpa [y, wtar] using L.ode_a t
    have hwStable : ∀ j : ℕ, 0 ≤ j →
        ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
          wtar t ≤ (I.ηH : ℝ) := by
      intro j _hj t ht
      have hclose := hstable j t ht
      have hrunning :
          Mch.halted (Mch.step^[j + 1] (Mch.init w)) = false :=
        DiscreteMachine.running_of_not_haltsOn Mch hnonhalt
      exact I.on_running (Mch.step^[j + 1] (Mch.init w)) hrunning
        (sol.z t) hclose
    obtain ⟨T, hT⟩ := latch_eventual_upper (K : ℝ) hKℝ R hθ hℓ
      (I.ηH : ℝ) hη0ℝ hηltℝ 0 y wtar
      hy01 hw01 hyderiv hwStable
    refine ⟨T, ?_⟩
    intro t ht
    exact hT t ht

/-! ## Existence of solutions (Picard–Lindelöf layer) -/

-- old unconditional iterator_solution_exists DELETED (false in general;
-- superseded by Existence.lean's boxed_iterator_exists per R3#8/D-runway).

/-- **P10b (R3#7), latch solution existence**: the scalar latch ODE
has a global solution riding on any iterator solution, provided the
driving term is continuous (the indicator polynomial composed with
the continuous z-channel).  Scalar linear ODE with continuous
time-dependent coefficients; same Picard–Lindelöf layer as P10. -/
theorem latch_solution_exists
    {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    (Hval : (Fin d → ℝ) → ℝ)
    (hHcont : Continuous fun t => Hval (sol.z t))
    (K : ℝ) (R : ℕ) :
    Nonempty (LatchSol sol Hval K R) := by
  classical
  set φ : ℝ → ℝ := fun t => K * gPulse R t with hφdef
  have hφcont : Continuous φ := by
    have hg : Continuous (gPulse R) := by
      unfold gPulse
      fun_prop
    fun_prop
  set Φ : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, φ s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (φ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hφcont.intervalIntegrable 0 t)
      (hφcont.stronglyMeasurableAtFilter _ _)
      hφcont.continuousAt
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set B : ℝ → ℝ :=
    fun t => ∫ s in (0:ℝ)..t, φ s * Hval (sol.z s) * Real.exp (Φ s) with hBdef
  have hBcont_integrand :
      Continuous (fun s : ℝ => φ s * Hval (sol.z s) * Real.exp (Φ s)) := by
    have hE : Continuous fun s : ℝ => Real.exp (Φ s) :=
      Real.continuous_exp.comp hΦcont
    exact (hφcont.mul hHcont).mul hE
  have hBderiv : ∀ t : ℝ,
      HasDerivAt B (φ t * Hval (sol.z t) * Real.exp (Φ t)) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hBcont_integrand.intervalIntegrable 0 t)
      (hBcont_integrand.stronglyMeasurableAtFilter _ _)
      hBcont_integrand.continuousAt
  set a : ℝ → ℝ := fun t => Real.exp (-(Φ t)) * B t with hadef
  refine ⟨{ a := a, init_a := ?_, ode_a := ?_ }⟩
  · simp [hadef, hBdef]
  · intro t
    have hExpDeriv : HasDerivAt (fun τ : ℝ => Real.exp (-(Φ τ)))
        (-(φ t) * Real.exp (-(Φ t))) t := by
      have hneg : HasDerivAt (fun τ : ℝ => -(Φ τ)) (-(φ t)) t :=
        (hΦderiv t).neg
      have h := hneg.exp
      convert h using 1
      ring
    have hprod := hExpDeriv.mul (hBderiv t)
    convert hprod using 1
    simp only [hadef, hφdef, hBdef]
    have hexp : Real.exp (-(Φ t)) * Real.exp (Φ t) = 1 := by
      rw [← Real.exp_add]
      simp
    have hterm :
        Real.exp (-(Φ t)) *
            (K * gPulse R t * Hval (sol.z t) * Real.exp (Φ t)) =
          K * gPulse R t * Hval (sol.z t) := by
      calc
        Real.exp (-(Φ t)) *
            (K * gPulse R t * Hval (sol.z t) * Real.exp (Φ t)) =
            (Real.exp (-(Φ t)) * Real.exp (Φ t)) *
              (K * gPulse R t * Hval (sol.z t)) := by
              ring
        _ = K * gPulse R t * Hval (sol.z t) := by
              rw [hexp]
              ring
    rw [hterm]
    ring

/-! ## The assembled Euclidean target (constr:assembled) -/

-- P11 `assembled_euclidean_simulation` now lives in BernsteinSeparator.lean
-- (proved, with the documented etastep-smallness hypothesis;
-- HANDOFF/p11-mismatches.md).

/-! ## Compactification (§6) — P12 -/

/-- Denominator of the stereographic embedding. -/
noncomputable def stereoDenom {nE : ℕ} (x : Fin nE → ℝ) : ℝ :=
  (∑ i, x i ^ 2) + 1

theorem stereoDenom_pos {nE : ℕ} (x : Fin nE → ℝ) : 0 < stereoDenom x := by
  unfold stereoDenom
  positivity

/-- The inverse stereographic embedding `ℝ^n → S^n ⊂ ℝ^{n+1}` (south
chart): `y₀ = (‖x‖² - 1)/(‖x‖² + 1)`, `y_{i+1} = 2 x_i/(‖x‖² + 1)`.
Misses only the north pole `(1, 0, …, 0)`. -/
noncomputable def stereo {nE : ℕ} (x : Fin nE → ℝ) : Fin (nE + 1) → ℝ :=
  fun j => Fin.cases (((∑ i, x i ^ 2) - 1) / stereoDenom x)
    (fun i => 2 * x i / stereoDenom x) j

/-- The image avoids the north pole: `y₀ < 1` always (chart safety,
R2#7). -/
theorem stereo_lt_one {nE : ℕ} (x : Fin nE → ℝ) : stereo x 0 < 1 := by
  unfold stereo
  rw [Fin.cases_zero]
  rw [div_lt_one (stereoDenom_pos x)]
  unfold stereoDenom
  linarith

/-- **Chart-observable identity** (R2#7): the rational chart
observable recovers the Euclidean coordinate exactly,
`y_{i+1} = (1 - y₀) · x_i`, i.e. `a(stereo x) = x_i` whenever the
chart observable `a(y) = y_{i+1}/(1-y₀)` is formed.  This is what
transfers the Euclidean latch readout `x_A ∈ [3/4,1] ∪ [0,1/4]` to
the polynomial inequalities of `ChartThresholdReadout` verbatim. -/
theorem stereo_chart_identity {nE : ℕ} (x : Fin nE → ℝ) (i : Fin nE) :
    stereo x i.succ = (1 - stereo x 0) * x i := by
  unfold stereo stereoDenom
  rw [Fin.cases_succ, Fin.cases_zero]
  have hpos : (0:ℝ) < (∑ i, x i ^ 2) + 1 := by positivity
  field_simp
  ring

private noncomputable def compactHat {nE : ℕ} (D : ℕ)
    (p : MvPolynomial (Fin nE) ℚ) :
    MvPolynomial (Fin (nE + 1)) ℚ :=
  ∑ α ∈ p.support,
    MvPolynomial.C (p.coeff α) *
      (∏ i : Fin nE, MvPolynomial.X i.succ ^ α i) *
      (1 - MvPolynomial.X 0) ^ (D - (α.sum fun _ e => e))

private noncomputable def compactC {nE : ℕ} (D : ℕ)
    (X : Fin nE → MvPolynomial (Fin nE) ℚ) :
    MvPolynomial (Fin (nE + 1)) ℚ :=
  ∑ i : Fin nE, MvPolynomial.X i.succ * compactHat D (X i)

private noncomputable def compactY {nE : ℕ} (D : ℕ)
    (X : Fin nE → MvPolynomial (Fin nE) ℚ) :
    Fin (nE + 1) → MvPolynomial (Fin (nE + 1)) ℚ :=
  Fin.cases ((1 - MvPolynomial.X 0) * compactC D X)
    (fun i => (1 - MvPolynomial.X 0) * compactHat D (X i) -
      MvPolynomial.X i.succ * compactC D X)

private lemma compact_monomial_prod {nE : ℕ} (α : Fin nE →₀ ℕ)
    (x : Fin nE → ℝ) (h : ℝ) :
    (∏ i : Fin nE, (h * x i) ^ α i) =
      h ^ (α.sum fun _ e => e) * ∏ i : Fin nE, x i ^ α i := by
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Finsupp.sum_fintype α (fun _ e => e) (by simp)).symm

private lemma compactHat_eval {nE : ℕ} (D : ℕ)
    (p : MvPolynomial (Fin nE) ℚ) (x : Fin nE → ℝ)
    (y : Fin (nE + 1) → ℝ) (h : ℝ)
    (h0 : 1 - y 0 = h) (hsucc : ∀ i, y i.succ = h * x i)
    (hD : p.totalDegree ≤ D) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (compactHat D p) =
      h ^ D * MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p := by
  rw [compactHat]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X]
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, MvPolynomial.eval₂_X]
  rw [h0]
  rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hαD : α.sum (fun _ e => e) ≤ D := (MvPolynomial.le_totalDegree hα).trans hD
  rw [show (∏ i : Fin nE, y i.succ ^ α i) =
      ∏ i : Fin nE, (h * x i) ^ α i by
    apply Finset.prod_congr rfl
    intro i _hi
    rw [hsucc i]]
  rw [compact_monomial_prod]
  rw [← Finsupp.prod_pow]
  change (algebraMap ℚ ℝ) (MvPolynomial.coeff α p) *
      (h ^ (α.sum fun x e => e) * (∏ i ∈ α.support, x i ^ α i)) *
        h ^ (D - α.sum fun x e => e) =
    h ^ D * ((algebraMap ℚ ℝ) (MvPolynomial.coeff α p) *
      ∏ i ∈ α.support, x i ^ α i)
  calc
    (algebraMap ℚ ℝ) (MvPolynomial.coeff α p) *
        (h ^ (α.sum fun x e => e) * (∏ i ∈ α.support, x i ^ α i)) *
          h ^ (D - α.sum fun x e => e)
        = (h ^ (α.sum fun x e => e) * h ^ (D - α.sum fun x e => e)) *
            ((algebraMap ℚ ℝ) (MvPolynomial.coeff α p) *
              ∏ i ∈ α.support, x i ^ α i) := by ring
    _ = h ^ D * ((algebraMap ℚ ℝ) (MvPolynomial.coeff α p) *
          ∏ i ∈ α.support, x i ^ α i) := by
      rw [← pow_add, Nat.add_sub_of_le hαD]

private lemma compact_tangent {nE : ℕ} (D : ℕ)
    (X : Fin nE → MvPolynomial (Fin nE) ℚ) :
    (∑ j : Fin (nE + 1), MvPolynomial.X j * compactY D X j) =
      (-compactC D X) *
        ((∑ j : Fin (nE + 1), MvPolynomial.X j * MvPolynomial.X j) - 1) := by
  let P : Fin nE → MvPolynomial (Fin (nE + 1)) ℚ := fun i => compactHat D (X i)
  change
    let C : MvPolynomial (Fin (nE + 1)) ℚ := ∑ i : Fin nE, MvPolynomial.X i.succ * P i
    let Y : Fin (nE + 1) → MvPolynomial (Fin (nE + 1)) ℚ :=
      Fin.cases ((1 - MvPolynomial.X 0) * C)
        (fun i => (1 - MvPolynomial.X 0) * P i - MvPolynomial.X i.succ * C)
    (∑ j : Fin (nE + 1), MvPolynomial.X j * Y j) =
      (-C) * ((∑ j : Fin (nE + 1), MvPolynomial.X j * MvPolynomial.X j) - 1)
  dsimp only
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [Fin.sum_univ_succ]
  have htail :
      (∑ x : Fin nE, MvPolynomial.X x.succ *
          ((1 - MvPolynomial.X 0) * P x -
            MvPolynomial.X x.succ * (∑ x, MvPolynomial.X x.succ * P x))) =
        (1 - MvPolynomial.X 0) *
            (∑ x : Fin nE, MvPolynomial.X x.succ * P x) -
          (∑ x : Fin nE, MvPolynomial.X x.succ * P x) *
            (∑ x : Fin nE, MvPolynomial.X x.succ * MvPolynomial.X x.succ) := by
    calc
      (∑ x : Fin nE, MvPolynomial.X x.succ *
          ((1 - MvPolynomial.X 0) * P x -
            MvPolynomial.X x.succ * (∑ x, MvPolynomial.X x.succ * P x)))
          = ∑ x : Fin nE, ((1 - MvPolynomial.X 0) *
              (MvPolynomial.X x.succ * P x) -
              (∑ x : Fin nE, MvPolynomial.X x.succ * P x) *
                (MvPolynomial.X x.succ * MvPolynomial.X x.succ)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            ring
      _ = (∑ x : Fin nE, (1 - MvPolynomial.X 0) *
              (MvPolynomial.X x.succ * P x)) -
            (∑ x : Fin nE, (∑ x : Fin nE, MvPolynomial.X x.succ * P x) *
              (MvPolynomial.X x.succ * MvPolynomial.X x.succ)) := by
            rw [Finset.sum_sub_distrib]
      _ = (1 - MvPolynomial.X 0) *
            (∑ x : Fin nE, MvPolynomial.X x.succ * P x) -
            (∑ x : Fin nE, MvPolynomial.X x.succ * P x) *
              (∑ x : Fin nE, MvPolynomial.X x.succ * MvPolynomial.X x.succ) := by
            rw [Finset.mul_sum, Finset.mul_sum]
  rw [htail]
  ring

private lemma compactC_eval_stereo {nE : ℕ} (D : ℕ)
    (X : Fin nE → MvPolynomial (Fin nE) ℚ)
    (hD : ∀ i, (X i).totalDegree ≤ D) (x : Fin nE → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (stereo x) (compactC D X) =
      (1 - stereo x 0) ^ (D + 1) *
        (∑ i : Fin nE, x i *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (X i)) := by
  rw [compactC]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
  calc
    (∑ i : Fin nE, stereo x i.succ *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (stereo x) (compactHat D (X i)))
        = ∑ i : Fin nE, ((1 - stereo x 0) * x i) *
            ((1 - stereo x 0) ^ D *
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (X i)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [stereo_chart_identity]
          rw [compactHat_eval D (X i) x (stereo x) (1 - stereo x 0) rfl
            (fun k => stereo_chart_identity x k) (hD i)]
    _ = (1 - stereo x 0) ^ (D + 1) *
        (∑ i : Fin nE, x i *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (X i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [pow_succ]
          ring

private lemma compactY_eval_stereo_zero {nE : ℕ} (D : ℕ)
    (X : Fin nE → MvPolynomial (Fin nE) ℚ)
    (hD : ∀ i, (X i).totalDegree ≤ D) (x : Fin nE → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (stereo x) (compactY D X 0) =
      (1 - stereo x 0) ^ (D + 2) *
        (∑ i : Fin nE, x i *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (X i)) := by
  rw [compactY]
  simp only [Fin.cases_zero, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_X]
  rw [compactC_eval_stereo D X hD x]
  rw [pow_succ]
  ring

private lemma compactY_eval_stereo_succ {nE : ℕ} (D : ℕ)
    (X : Fin nE → MvPolynomial (Fin nE) ℚ)
    (hD : ∀ i, (X i).totalDegree ≤ D) (x : Fin nE → ℝ) (k : Fin nE) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (stereo x) (compactY D X k.succ) =
      (1 - stereo x 0) ^ (D + 1) *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (X k) -
        (1 - stereo x 0) ^ (D + 2) * x k *
          (∑ i : Fin nE, x i *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (X i)) := by
  rw [compactY]
  simp only [Fin.cases_succ, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_X]
  rw [compactHat_eval D (X k) x (stereo x) (1 - stereo x 0)]
  · rw [compactC_eval_stereo D X hD x]
    rw [stereo_chart_identity]
    rw [pow_succ (1 - stereo x 0) (D + 1)]
    ring
  · rfl
  · intro i
    exact stereo_chart_identity x i
  · exact hD k

private noncomputable def compactForwardExtend (h : ℝ → ℝ) (v0 : ℝ) : ℝ → ℝ :=
  fun t => if 0 ≤ t then h t else h 0 + t * v0

private theorem compactForwardExtend_eq_of_nonneg (h : ℝ → ℝ) (v0 : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    compactForwardExtend h v0 t = h t := by
  simp [compactForwardExtend, ht]

private theorem compactForwardExtend_continuous (h : ℝ → ℝ) (v : ℝ → ℝ)
    (hder : ∀ t : ℝ, 0 ≤ t → HasDerivAt h (v t) t) :
    Continuous (compactForwardExtend h (v 0)) := by
  have hleft : ContinuousOn (compactForwardExtend h (v 0)) (Set.Iic (0 : ℝ)) := by
    refine (by fun_prop : Continuous fun t : ℝ => h 0 + t * v 0).continuousOn.congr ?_
    intro t ht
    rcases lt_or_eq_of_le (show t ≤ 0 from ht) with htneg | rfl
    · simp [compactForwardExtend, not_le_of_gt htneg]
    · simp [compactForwardExtend]
  have hright : ContinuousOn (compactForwardExtend h (v 0)) (Set.Ici (0 : ℝ)) := by
    have hh : ContinuousOn h (Set.Ici (0 : ℝ)) := by
      intro t ht
      exact (hder t ht).continuousAt.continuousWithinAt
    refine hh.congr ?_
    intro t ht
    have ht0 : 0 ≤ t := ht
    simp [compactForwardExtend, ht0]
  have huniv : Set.Iic (0 : ℝ) ∪ Set.Ici (0 : ℝ) = Set.univ := by
    ext t
    simp
  have hcontOn : ContinuousOn (compactForwardExtend h (v 0)) Set.univ := by
    simpa [huniv] using
      hleft.union_of_isClosed hright isClosed_Iic isClosed_Ici
  simpa using hcontOn

private theorem compactTimeIntegral_surjective_nonneg
    (ρ : ℝ → ℝ) (hρ_cont : Continuous ρ) (c : ℝ) (hc : 0 < c)
    (hρ_lb : ∀ t, c ≤ ρ t) (y : ℝ) (hy : 0 ≤ y) :
    ∃ t, 0 ≤ t ∧ Ripple.BoundedUniversality.GPAC.timeChangeIntegral ρ t = y := by
  obtain ⟨R₀, hR₀⟩ := (Filter.tendsto_atTop_atTop.mp
    (Ripple.BoundedUniversality.GPAC.timeChangeIntegral_tendsto ρ hρ_cont c hc hρ_lb)) y
  let R := max R₀ 0
  have hR0 : 0 ≤ R := le_max_right R₀ 0
  have hLR : y ≤ Ripple.BoundedUniversality.GPAC.timeChangeIntegral ρ R := hR₀ R (le_max_left R₀ 0)
  have hL0 : Ripple.BoundedUniversality.GPAC.timeChangeIntegral ρ 0 ≤ y := by
    rw [Ripple.BoundedUniversality.GPAC.timeChangeIntegral_zero]
    exact hy
  obtain ⟨t, ⟨ht0, _⟩, htL⟩ := intermediate_value_Icc hR0
    ((Differentiable.continuous fun τ =>
      (Ripple.BoundedUniversality.GPAC.timeChangeIntegral_hasDerivAt ρ hρ_cont τ).differentiableAt)).continuousOn
    ⟨hL0, hLR⟩
  exact ⟨t, ht0, htL⟩

private theorem compactTimeIntegral_inverse
    (ρ : ℝ → ℝ) (hρ_cont : Continuous ρ) (c : ℝ) (hc : 0 < c)
    (hρ_lb : ∀ t, c ≤ ρ t) :
    ∃ s : ℝ → ℝ,
      s 0 = 0 ∧
      (∀ τ : ℝ, 0 ≤ τ → HasDerivAt s ((ρ (s τ))⁻¹) τ) ∧
      StrictMonoOn s (Set.Ici (0 : ℝ)) ∧
      Filter.Tendsto s Filter.atTop Filter.atTop ∧
      (∀ τ : ℝ, 0 ≤ τ → 0 ≤ s τ) := by
  classical
  let L : ℝ → ℝ := Ripple.BoundedUniversality.GPAC.timeChangeIntegral ρ
  have hL0 : L 0 = 0 := by simpa [L] using Ripple.BoundedUniversality.GPAC.timeChangeIntegral_zero ρ
  have hLderiv : ∀ x : ℝ, HasDerivAt L (ρ x) x := by
    intro x
    simpa [L] using Ripple.BoundedUniversality.GPAC.timeChangeIntegral_hasDerivAt ρ hρ_cont x
  have hLmono : StrictMono L := by
    exact Ripple.BoundedUniversality.GPAC.timeChangeIntegral_strictMono ρ hρ_cont
      (fun t => lt_of_lt_of_le hc (hρ_lb t))
  have hLcont : Continuous L :=
    Differentiable.continuous fun τ => (hLderiv τ).differentiableAt
  have hL_tendsto : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using Ripple.BoundedUniversality.GPAC.timeChangeIntegral_tendsto ρ hρ_cont c hc hρ_lb
  have hL_le_linear_of_nonpos : ∀ t : ℝ, t ≤ 0 → L t ≤ c * t := by
    intro t ht
    have h_const_int : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume t 0 :=
      continuous_const.intervalIntegrable t 0
    have hρ_int : IntervalIntegrable ρ MeasureTheory.volume t 0 :=
      hρ_cont.intervalIntegrable t 0
    have hmono_int :
        (∫ u in t..0, c) ≤ ∫ u in t..0, ρ u :=
      intervalIntegral.integral_mono_on ht h_const_int hρ_int (fun u _ => hρ_lb u)
    have hsymm : L t = - ∫ u in t..0, ρ u := by
      dsimp [L, Ripple.BoundedUniversality.GPAC.timeChangeIntegral]
      rw [intervalIntegral.integral_symm]
    calc
      L t = - ∫ u in t..0, ρ u := hsymm
      _ ≤ - ∫ u in t..0, c := by linarith
      _ = c * t := by
        rw [intervalIntegral.integral_const, zero_sub, smul_eq_mul]
        ring
  have hsurj : Function.Surjective L := by
    intro y
    by_cases hy : 0 ≤ y
    · rcases compactTimeIntegral_surjective_nonneg ρ hρ_cont c hc hρ_lb y hy
        with ⟨t, _, ht_eq⟩
      exact ⟨t, by simpa [L] using ht_eq⟩
    · have hylt : y < 0 := lt_of_not_ge hy
      let a : ℝ := y / c - 1
      have ha0 : a ≤ 0 := by
        dsimp [a]
        have hc' : 0 < c := hc
        nlinarith [div_neg_of_neg_of_pos hylt hc']
      have hca : c * a ≤ y := by
        dsimp [a]
        field_simp [ne_of_gt hc]
        nlinarith [hc]
      have hLa_le_y : L a ≤ y := (hL_le_linear_of_nonpos a ha0).trans hca
      have hy_le_L0 : y ≤ L 0 := by linarith [hL0]
      obtain ⟨x, _, hx⟩ := intermediate_value_Icc ha0 hLcont.continuousOn
        ⟨hLa_le_y, hy_le_L0⟩
      exact ⟨x, hx⟩
  let s : ℝ → ℝ := Function.invFun L
  have hs_inv : ∀ y : ℝ, L (s y) = y := fun y => Function.invFun_eq (hsurj y)
  have hs0 : s 0 = 0 := by
    apply hLmono.injective
    simpa [hL0] using hs_inv 0
  have hs_strict : StrictMono s := by
    intro a b hab
    by_contra h
    push_neg at h
    linarith [hLmono.monotone h, hs_inv a, hs_inv b]
  have hs_cont : Continuous s := by
    let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective L hLmono hsurj
    have hLe_symm : ∀ y, L (e.symm y) = y := by
      intro y
      have : e (e.symm y) = y := e.apply_symm_apply y
      change (e (e.symm y) : ℝ) = y
      simpa [this]
    have hs_eq_e : s = e.symm := by
      funext y
      apply hLmono.injective
      exact (hs_inv y).trans (hLe_symm y).symm
    rw [hs_eq_e]
    exact e.symm.continuous
  have hs_tendsto : Filter.Tendsto s Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (L b)] with y hy
    by_contra hnot
    exact not_lt_of_ge (show L b ≤ L (s y) by simpa [hs_inv y] using hy)
      (hLmono (lt_of_not_ge hnot))
  have hs_nonneg : ∀ τ : ℝ, 0 ≤ τ → 0 ≤ s τ := by
    intro τ hτ
    by_contra hneg
    have hslt : s τ < 0 := lt_of_not_ge hneg
    have hLlt : L (s τ) < L 0 := hLmono hslt
    linarith [hs_inv τ, hL0]
  refine ⟨s, hs0, ?_, fun a ha b hb hab => hs_strict hab, hs_tendsto, hs_nonneg⟩
  intro τ _hτ
  exact HasDerivAt.of_local_left_inverse
    hs_cont.continuousAt
    (hLderiv (s τ))
    (ne_of_gt (lt_of_lt_of_le hc (hρ_lb (s τ))))
    (Filter.Eventually.of_forall hs_inv)

private lemma stereo_hasDerivAt_zero_raw {nE : ℕ}
    {z : ℝ → Fin nE → ℝ} {z' : Fin nE → ℝ} {τ : ℝ}
    (hz : HasDerivAt z z' τ) :
    HasDerivAt (fun σ => stereo (z σ) 0)
      ((((∑ i : Fin nE, 2 * z τ i * z' i) * stereoDenom (z τ) -
          ((∑ i : Fin nE, z τ i ^ 2) - 1) *
            (∑ i : Fin nE, 2 * z τ i * z' i)) /
        stereoDenom (z τ) ^ 2)) τ := by
  simp only [stereo, Fin.cases_zero]
  let r : ℝ → ℝ := fun σ => ∑ i : Fin nE, z σ i ^ 2
  have hr : HasDerivAt r (∑ i : Fin nE, 2 * z τ i * z' i) τ := by
    dsimp [r]
    apply HasDerivAt.fun_sum
    intro i _hi
    have hzi : HasDerivAt (fun σ => z σ i) (z' i) τ := hasDerivAt_pi.mp hz i
    convert hzi.pow 2 using 1
    ring
  have hnum : HasDerivAt (fun σ => r σ - 1)
      (∑ i : Fin nE, 2 * z τ i * z' i) τ := hr.sub_const 1
  have hden : HasDerivAt (fun σ => stereoDenom (z σ))
      (∑ i : Fin nE, 2 * z τ i * z' i) τ := by
    unfold stereoDenom
    simpa [r] using hr.const_add 1
  exact hnum.div hden (ne_of_gt (stereoDenom_pos (z τ)))

private lemma stereo_hasDerivAt_succ_raw {nE : ℕ}
    {z : ℝ → Fin nE → ℝ} {z' : Fin nE → ℝ} {τ : ℝ} (k : Fin nE)
    (hz : HasDerivAt z z' τ) :
    HasDerivAt (fun σ => stereo (z σ) k.succ)
      ((((2 * z' k) * stereoDenom (z τ) -
          (2 * z τ k) * (∑ i : Fin nE, 2 * z τ i * z' i)) /
        stereoDenom (z τ) ^ 2)) τ := by
  simp only [stereo, Fin.cases_succ]
  let r : ℝ → ℝ := fun σ => ∑ i : Fin nE, z σ i ^ 2
  have hr : HasDerivAt r (∑ i : Fin nE, 2 * z τ i * z' i) τ := by
    dsimp [r]
    apply HasDerivAt.fun_sum
    intro i _hi
    have hzi : HasDerivAt (fun σ => z σ i) (z' i) τ := hasDerivAt_pi.mp hz i
    convert hzi.pow 2 using 1
    ring
  have hnum : HasDerivAt (fun σ => 2 * z σ k) (2 * z' k) τ := by
    exact (hasDerivAt_pi.mp hz k).const_mul 2
  have hden : HasDerivAt (fun σ => stereoDenom (z σ))
      (∑ i : Fin nE, 2 * z τ i * z' i) τ := by
    unfold stereoDenom
    simpa [r] using hr.const_add 1
  exact hnum.div hden (ne_of_gt (stereoDenom_pos (z τ)))

private lemma compact_deriv_zero_algebra (D : ℕ) {A h r dot : ℝ}
    (hA : A = r + 1) (hh : h = 2 / A) (hAne : A ≠ 0) :
    ((2 * h ^ D * dot) * A - (r - 1) * (2 * h ^ D * dot)) / A ^ 2 =
      h ^ (D + 2) * dot := by
  have hh2 : h ^ 2 = 4 / A ^ 2 := by
    rw [hh]
    field_simp [hAne]
    ring
  calc
    ((2 * h ^ D * dot) * A - (r - 1) * (2 * h ^ D * dot)) / A ^ 2
        = 4 * h ^ D * dot / A ^ 2 := by
          field_simp [hAne]
          rw [hA]
          ring
    _ = h ^ D * h ^ 2 * dot := by
          rw [hh2]
          ring_nf
    _ = h ^ (D + 2) * dot := by
          rw [show h ^ (D + 2) = h ^ D * h ^ 2 by
            rw [pow_add]]

private lemma compact_deriv_succ_algebra (D : ℕ) {A h P x dot : ℝ}
    (hh : h = 2 / A) (hAne : A ≠ 0) :
    (2 * (h ^ D * P) * A - 2 * x * (2 * h ^ D * dot)) / A ^ 2 =
      h ^ (D + 1) * P - h ^ (D + 2) * x * dot := by
  have hh2 : h ^ 2 = 4 / A ^ 2 := by
    rw [hh]
    field_simp [hAne]
    ring
  calc
    (2 * (h ^ D * P) * A - 2 * x * (2 * h ^ D * dot)) / A ^ 2
        = h ^ D * h * P - h ^ D * h ^ 2 * x * dot := by
          rw [hh2]
          rw [hh]
          field_simp [hAne]
          ring_nf
    _ = h ^ (D + 1) * P - h ^ (D + 2) * x * dot := by
          rw [show h ^ (D + 1) = h ^ D * h by
            rw [pow_succ]]
          rw [show h ^ (D + 2) = h ^ D * h ^ 2 by
            rw [pow_add]]

/-- **P12, stereographic compactification** (§6, restated 2026-06-11
with the explicit oracle-derived construction; tangency is now
POINTWISE vanishing on the sphere — ideal membership for generic `X`
is a formalization trap, pointwise is what thm:main uses).

Construction (derived and hand-verified; cross-check by ChatGPT life
tab in flight):  with the clearing substitution
`clear_m(p) := Σ_α coeff_α · y^α · (1−y₀)^{m−|α|}` (x_i ↦ y_i/(1−y₀),
denominators cleared to total degree m), set
`P_i := clear_d(X_i)`, `N := clear_{d+1}(⟨x, X⟩)` and
`Y₀ := (1−y₀)·N`, `Y_i := (1−y₀)·P_i − y_i·N`.
Off-sphere identity: `⟨y, Y⟩ = (1−y₀)(Σ y_i P_i − N) − N(|y|²−1)`;
on the sphere the first factor dies pointwise (chart identity away
from the pole, `1−y₀ = 0` at it).  Time change: `τ(s) :=
∫₀ˢ ((1+|γ|²)/2)^d ≥ s`, so the inverse `s(τ)` is global, strictly
monotone, unbounded — NO boundedness hypothesis on `γ` needed. -/
theorem compactification_exists
    (nE : ℕ) (X : Fin nE → MvPolynomial (Fin nE) ℚ) :
    ∃ (Y : Fin (nE + 1) → MvPolynomial (Fin (nE + 1)) ℚ),
      -- (i) tangency as EXACT ideal membership (GPT-life cross-check
      -- 2026-06-11: ⟨y,Y⟩ = −q·C closes identically off-sphere with
      -- Qpoly := −C; no remainder, no pointwise retreat needed)
      (∃ Qpoly : MvPolynomial (Fin (nE + 1)) ℚ,
        (∑ j, MvPolynomial.X j * Y j) =
          Qpoly * ((∑ j, MvPolynomial.X j * MvPolynomial.X j) - 1)) ∧
      -- (ii) trajectory transfer under a strictly monotone unbounded
      --      time change
      ∀ (γ : ℝ → Fin nE → ℝ),
        (∀ t : ℝ, 0 ≤ t → HasDerivAt γ
          (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (γ t) (X i)) t) →
        ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
          Filter.Tendsto s Filter.atTop Filter.atTop ∧
          ∀ τ : ℝ, 0 ≤ τ → HasDerivAt (fun σ => stereo (γ (s σ)))
            (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
              (stereo (γ (s τ))) (Y j)) τ := by
  classical
  let D : ℕ := Finset.univ.sup fun i : Fin nE => (X i).totalDegree
  refine ⟨compactY D X, ?_, ?_⟩
  · refine ⟨-compactC D X, ?_⟩
    exact compact_tangent D X
  · intro γ hγ
    let vf : ℝ → Fin nE → ℝ :=
      fun t i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (γ t) (X i)
    let γbar : ℝ → Fin nE → ℝ :=
      fun t i => compactForwardExtend (fun u => γ u i) (vf 0 i) t
    let ρ : ℝ → ℝ := fun t => (stereoDenom (γbar t) / 2) ^ D
    have hD : ∀ i : Fin nE, (X i).totalDegree ≤ D := by
      intro i
      dsimp [D]
      exact Finset.le_sup (f := fun i : Fin nE => (X i).totalDegree) (Finset.mem_univ i)
    have hγcoord : ∀ i : Fin nE, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (fun u => γ u i) (vf t i) t := by
      intro i t ht
      exact hasDerivAt_pi.mp (hγ t ht) i
    have hγbar_nonneg : ∀ t : ℝ, 0 ≤ t → γbar t = γ t := by
      intro t ht
      funext i
      exact compactForwardExtend_eq_of_nonneg (fun u => γ u i) (vf 0 i) ht
    have hγbar_cont : Continuous γbar := by
      apply continuous_pi
      intro i
      exact compactForwardExtend_continuous (fun u => γ u i) (fun u => vf u i)
        (hγcoord i)
    have hρ_cont : Continuous ρ := by
      dsimp [ρ]
      have hden_cont : Continuous fun t : ℝ => stereoDenom (γbar t) := by
        unfold stereoDenom
        fun_prop
      exact (hden_cont.div_const 2).pow D
    let c : ℝ := (1 / 2 : ℝ) ^ D
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hρ_lb : ∀ t : ℝ, c ≤ ρ t := by
      intro t
      dsimp [c, ρ]
      apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hsum_nonneg : 0 ≤ ∑ i : Fin nE, γbar t i ^ 2 := by
        exact Finset.sum_nonneg fun i _ => sq_nonneg (γbar t i)
      unfold stereoDenom
      nlinarith
    obtain ⟨s, hs0, hsderiv, hsmono, hstendsto, hs_nonneg⟩ :=
      compactTimeIntegral_inverse ρ hρ_cont c hc hρ_lb
    refine ⟨s, hs0, hsmono, hstendsto, ?_⟩
    intro τ hτ
    have hsτ_nonneg : 0 ≤ s τ := hs_nonneg τ hτ
    have hγbar_sτ : γbar (s τ) = γ (s τ) := hγbar_nonneg (s τ) hsτ_nonneg
    have hρ_sτ :
        ρ (s τ) = (stereoDenom (γ (s τ)) / 2) ^ D := by
      dsimp [ρ]
      rw [hγbar_sτ]
    have hrate :
        (ρ (s τ))⁻¹ = (1 - stereo (γ (s τ)) 0) ^ D := by
      rw [hρ_sτ]
      have hden_pos : 0 < stereoDenom (γ (s τ)) := stereoDenom_pos (γ (s τ))
      have hchart : 1 - stereo (γ (s τ)) 0 = 2 / stereoDenom (γ (s τ)) := by
        unfold stereo stereoDenom
        rw [Fin.cases_zero]
        field_simp [ne_of_gt hden_pos]
        ring
      rw [hchart]
      rw [← inv_pow]
      congr 1
      field_simp [ne_of_gt hden_pos]
    have hsderiv_rate : HasDerivAt s ((1 - stereo (γ (s τ)) 0) ^ D) τ :=
      (hsderiv τ hτ).congr_deriv hrate
    have hγ_at : HasDerivAt γ (vf (s τ)) (s τ) := hγ (s τ) hsτ_nonneg
    have hz : HasDerivAt (fun σ => γ (s σ))
        (((1 - stereo (γ (s τ)) 0) ^ D) • vf (s τ)) τ :=
      hγ_at.scomp τ hsderiv_rate
    apply hasDerivAt_pi.mpr
    intro j
    refine Fin.cases ?_ ?_ j
    ·
      have hraw := stereo_hasDerivAt_zero_raw (z := fun σ => γ (s σ))
        (z' := ((1 - stereo (γ (s τ)) 0) ^ D) • vf (s τ)) hz
      refine hraw.congr_deriv ?_
      let rate : ℝ := (1 - stereo (γ (s τ)) 0) ^ D
      let dot : ℝ := ∑ i : Fin nE, γ (s τ) i * vf (s τ) i
      have hsum :
          (∑ i : Fin nE, 2 * γ (s τ) i * (rate • vf (s τ)) i) =
            2 * rate * dot := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp [dot, vf, rate]
        ring
      have hden_pos : 0 < stereoDenom (γ (s τ)) := stereoDenom_pos (γ (s τ))
      have hchart : 1 - stereo (γ (s τ)) 0 = 2 / stereoDenom (γ (s τ)) := by
        unfold stereo stereoDenom
        rw [Fin.cases_zero]
        field_simp [ne_of_gt hden_pos]
        ring
      rw [hsum]
      rw [compactY_eval_stereo_zero D X hD (γ (s τ))]
      dsimp [dot, vf, rate]
      exact compact_deriv_zero_algebra D (h := 1 - stereo (γ (s τ)) 0)
        (A := stereoDenom (γ (s τ))) (r := ∑ x : Fin nE, γ (s τ) x ^ 2)
        (dot := ∑ x : Fin nE, γ (s τ) x *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (γ (s τ)) (X x))
        (by unfold stereoDenom; ring) hchart (ne_of_gt hden_pos)
    · intro k
      have hraw := stereo_hasDerivAt_succ_raw (z := fun σ => γ (s σ))
        (z' := ((1 - stereo (γ (s τ)) 0) ^ D) • vf (s τ)) k hz
      refine hraw.congr_deriv ?_
      let rate : ℝ := (1 - stereo (γ (s τ)) 0) ^ D
      let dot : ℝ := ∑ i : Fin nE, γ (s τ) i * vf (s τ) i
      have hsum :
          (∑ i : Fin nE, 2 * γ (s τ) i * (rate • vf (s τ)) i) =
            2 * rate * dot := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp [dot, vf, rate]
        ring
      have hden_pos : 0 < stereoDenom (γ (s τ)) := stereoDenom_pos (γ (s τ))
      have hchart : 1 - stereo (γ (s τ)) 0 = 2 / stereoDenom (γ (s τ)) := by
        unfold stereo stereoDenom
        rw [Fin.cases_zero]
        field_simp [ne_of_gt hden_pos]
        ring
      rw [hsum]
      rw [compactY_eval_stereo_succ D X hD (γ (s τ)) k]
      dsimp [dot, vf, rate]
      exact compact_deriv_succ_algebra D (h := 1 - stereo (γ (s τ)) 0)
        (A := stereoDenom (γ (s τ)))
        (P := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (γ (s τ)) (X k))
        (x := γ (s τ) k)
        (dot := ∑ x : Fin nE, γ (s τ) x *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (γ (s τ)) (X x))
        hchart (ne_of_gt hden_pos)

/-- Readout transfer along `stereo` (R2#7, derived from the chart
identity): if the Euclidean latch coordinate `A` eventually lies in
`[3/4, 1]` (resp. `[0, 1/4]`), then the compactified trajectory
eventually lies in the chart `HaltRegion` (resp. `NonhaltRegion`) of
thm:main.  Pure algebra: `y_{A+1} = (1-y₀)·x_A` with `1-y₀ > 0`. -/
theorem stereo_readout_transfer {nE : ℕ} (x : Fin nE → ℝ) (A : Fin nE) :
    ((3/4 ≤ x A ∧ x A ≤ 1) →
      (stereo x 0 < 1 ∧
       3 * (1 - stereo x 0) ≤ 4 * stereo x A.succ ∧
       stereo x A.succ ≤ 1 - stereo x 0)) ∧
    ((0 ≤ x A ∧ x A ≤ 1/4) →
      (stereo x 0 < 1 ∧
       0 ≤ stereo x A.succ ∧
       4 * stereo x A.succ ≤ 1 - stereo x 0)) := by
  have hlt := stereo_lt_one x
  have hid := stereo_chart_identity x A
  have hpos : 0 < 1 - stereo x 0 := by linarith
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hlt, ?_, ?_⟩
    · rw [hid]; nlinarith
    · rw [hid]; nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨hlt, ?_, ?_⟩
    · rw [hid]; nlinarith
    · rw [hid]; nlinarith

/-! ## The main statement — P13 -/

/- **Main theorem target** (thm:main), conditional form (R2#8): for
every FIXED undecidable machine carrying the §4 package — lattice
encoding, robust real extension, finite-range margin-separated state
coordinate, uniform moving-box certificate — there is a rational PIVP
(the compactified assembled simulator) with a bounded,
honestly-encoded, eventual chart-threshold simulation of THAT machine.
Composes P11 (assembled Euclidean) + P12 (compactification) +
`stereo_readout_transfer`.

The UNCONDITIONAL thm:main then requires instantiating the package
for a concrete universal machine.  DOCTRINE.md "DISCOVERY 2026-06-11"
records that the paper's current §3+§4 cannot satisfy `hstepbox`
(BCGH integer encoding has unbounded per-cycle displacement) nor
survive the leak-depth obstruction (fractional encoding); the package
hypotheses below are therefore the precise interface the §3 redesign
(dynamic-sharpness gates) must meet.  Do NOT instantiate with the
fuel machine (`no_robust_increment_freeze`). -/
-- The theorem `main_assembled` (P13 conditional form) is PROVED in
-- `Ripple.BoundedUniversality.BGP.MainAssembled` (import direction: it composes P11 from
-- `BernsteinSeparator`, which imports this file, so it cannot live here).
-- Its statement is this file's original statement plus exactly two
-- documented interface deltas (`hstepSmall`, `hsupply`) — see
-- `HANDOFF/main-assembled-deltas.md`.

end Ripple.BoundedUniversality.BGP
