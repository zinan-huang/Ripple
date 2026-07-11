/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `MainProfileDrift` — the concrete Main above-cap squaring `hdrift`, PROVEN (C5c-A core).

`MainConfinementHours.MainHourSquaringAtom` isolates the genuine per-hour probabilistic content into
its `hdrift` field.  This file PROVES that field concretely for the Main above-cap profile potential
`Φ = exp(lam · mainProfileAbove i)`, reducing it to two SATISFIABLE per-step protocol facts:

* `hstep` — the above-cap count rises by at most TWO in one interaction (one interaction replaces two
  agents), a deterministic config-level lift of the Phase-3 pair ledger;
* `hrise` — the hour-gated rise-rate floor `(K c){N c < N c'} ≤ q` (the squaring source bound
  `q ≲ (μᵢ/|M|)²`).

The analytic core is `mgf_one_step_add_two`, the `+2` analogue of `ClimbTail.mgf_one_step` (one
interaction can raise the count by two, so the MGF gap uses `e^{2·lam}`).  `mainHourSquaringAtom_of_rareRise`
then builds a full `MainHourSquaringAtom` with `hdrift` discharged — the remaining carries are exactly
`hstep`/`hrise` (protocol facts) and the scalar Bennett budget `hbudgetScalar`.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Provenance: ChatGPT (family3 task 57438081) C5c hdrift draft, audited against `844b1db` — field names
matched; the flagged `Real.log_mul` step replaced by the robust `Real.exp_add` rewrite; `λ` (the Lean 4
lambda keyword) renamed to `lam`.
Reference: `AUDIT_HEADLINE_THEOREMS.md` (core C5c-A); Doty et al. (arXiv:2106.10201v2) Theorem 6.2.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MainConfinementHours

namespace ExactMajority

namespace MainExponentConfinement

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-- **A `+2` version of `ClimbTail.mgf_one_step`.**  If `N` rises by at most `2` a.e. and the rise
event `{n₀ < N}` has probability `≤ q`, then `E exp(lam·N) ≤ (1 + q(e^{2lam} − 1))·exp(lam·n₀)`.  The
elementary one-step Bennett/Chernoff MGF bound for a two-output population-protocol interaction. -/
theorem mgf_one_step_add_two
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (lam : ℝ) (hlam : 0 ≤ lam)
    (N : α → ℕ) (n₀ : ℕ)
    (hstep : ∀ᵐ y ∂μ, N y ≤ n₀ + 2)
    (q : ℝ) (hq0 : 0 ≤ q)
    (hprob : μ {y | n₀ < N y} ≤ ENNReal.ofReal q) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (N y : ℝ))) ∂μ
      ≤ ENNReal.ofReal
          ((1 + q * (Real.exp (2 * lam) - 1)) * Real.exp (lam * (n₀ : ℝ))) := by
  classical
  set D : Set α := {y | n₀ < N y} with hD
  have hD_meas : MeasurableSet D := DiscreteMeasurableSpace.forall_measurableSet _
  have hpt : ∀ᵐ y ∂μ,
      ENNReal.ofReal (Real.exp (lam * (N y : ℝ))) ≤
        (if y ∈ D then
          ENNReal.ofReal (Real.exp (2 * lam) * Real.exp (lam * (n₀ : ℝ)))
        else
          ENNReal.ofReal (Real.exp (lam * (n₀ : ℝ)))) := by
    filter_upwards [hstep] with y hy
    by_cases hyD : y ∈ D
    · simp only [hyD, if_true]
      have hrhs : Real.exp (2 * lam) * Real.exp (lam * (n₀ : ℝ))
          = Real.exp (lam * ((n₀ + 2 : ℕ) : ℝ)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [hrhs]
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hy) hlam)
    · simp only [hyD, if_false]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hle : N y ≤ n₀ := by
        by_contra h
        exact hyD (by simpa [D] using Nat.lt_of_not_ge h)
      have hcast : (N y : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hle
      exact mul_le_mul_of_nonneg_left hcast hlam
  calc
    ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (N y : ℝ))) ∂μ
        ≤ ∫⁻ y,
            (if y ∈ D then
              ENNReal.ofReal (Real.exp (2 * lam) * Real.exp (lam * (n₀ : ℝ)))
            else
              ENNReal.ofReal (Real.exp (lam * (n₀ : ℝ)))) ∂μ :=
          lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp (2 * lam) * Real.exp (lam * (n₀ : ℝ))) * μ D
        + ENNReal.ofReal (Real.exp (lam * (n₀ : ℝ))) * μ Dᶜ := by
          rw [← lintegral_add_compl _ hD_meas]
          congr 1
          · rw [setLIntegral_congr_fun hD_meas
                (g := fun _ => ENNReal.ofReal (Real.exp (2 * lam) * Real.exp (lam * (n₀ : ℝ))))
                (fun y hy => by simp only [hy, if_true])]
            rw [lintegral_const, Measure.restrict_apply_univ]
          · rw [setLIntegral_congr_fun hD_meas.compl
                (g := fun _ => ENNReal.ofReal (Real.exp (lam * (n₀ : ℝ))))
                (fun y hy => by
                  simp only [Set.mem_compl_iff] at hy
                  simp only [hy, if_false])]
            rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal
          ((1 + q * (Real.exp (2 * lam) - 1)) * Real.exp (lam * (n₀ : ℝ))) := by
          have hΦnn : (0 : ℝ) ≤ Real.exp (lam * (n₀ : ℝ)) := (Real.exp_pos _).le
          have hμD_le_one : μ D ≤ 1 := by
            calc μ D ≤ μ Set.univ := measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          have hμD_ne_top : μ D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμD_le_one
          set qr := (μ D).toReal with hqr
          have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
          have hqr_le_one : qr ≤ 1 := by
            rw [hqr, show (1 : ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
            exact ENNReal.toReal_mono ENNReal.one_ne_top hμD_le_one
          have hqr_le_q : qr ≤ q := by
            rw [hqr]
            calc (μ D).toReal ≤ (ENNReal.ofReal q).toReal :=
                  ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
              _ = q := ENNReal.toReal_ofReal hq0
          have hμD_eq : μ D = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hμD_ne_top).symm
          have hμDc_eq : μ Dᶜ = ENNReal.ofReal (1 - qr) := by
            have hcompl := measure_compl hD_meas hμD_ne_top
            rw [show μ Set.univ = 1 from measure_univ] at hcompl
            rw [hcompl, hμD_eq,
              show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_sub 1 hqr_nonneg]
          rw [hμD_eq, hμDc_eq,
            ← ENNReal.ofReal_mul
              (by positivity : (0 : ℝ) ≤ Real.exp (2 * lam) * Real.exp (lam * (n₀ : ℝ))),
            ← ENNReal.ofReal_mul hΦnn,
            ← ENNReal.ofReal_add
              (mul_nonneg (by positivity) hqr_nonneg)
              (mul_nonneg hΦnn (by linarith : (0 : ℝ) ≤ 1 - qr))]
          apply ENNReal.ofReal_le_ofReal
          have hfac :
              Real.exp (2 * lam) * Real.exp (lam * (n₀ : ℝ)) * qr
                + Real.exp (lam * (n₀ : ℝ)) * (1 - qr)
              = Real.exp (lam * (n₀ : ℝ)) * (1 + (Real.exp (2 * lam) - 1) * qr) := by ring
          rw [hfac]
          have hbound :
              1 + (Real.exp (2 * lam) - 1) * qr ≤ 1 + q * (Real.exp (2 * lam) - 1) := by
            have hnonneg : 0 ≤ Real.exp (2 * lam) - 1 := by
              have : (1 : ℝ) ≤ Real.exp (2 * lam) := Real.one_le_exp (by nlinarith)
              linarith
            nlinarith [mul_le_mul_of_nonneg_left hqr_le_q hnonneg]
          calc
            Real.exp (lam * (n₀ : ℝ)) * (1 + (Real.exp (2 * lam) - 1) * qr)
                ≤ Real.exp (lam * (n₀ : ℝ)) * (1 + q * (Real.exp (2 * lam) - 1)) :=
              mul_le_mul_of_nonneg_left hbound hΦnn
            _ = (1 + q * (Real.exp (2 * lam) - 1)) * Real.exp (lam * (n₀ : ℝ)) := by ring

/-- The exponential potential for the Main above-cap profile. -/
noncomputable def mainAboveExpPot
    (i : Fin (L + 1)) (lam : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lam * (mainProfileAbove (L := L) (K := K) i c : ℝ)))

theorem mainAboveExpPot_measurable (i : Fin (L + 1)) (lam : ℝ) :
    Measurable (mainAboveExpPot (L := L) (K := K) i lam) :=
  Measurable.of_discrete

/-- **The concrete Main above-cap one-step MGF drift**, from the two hour-gated protocol facts
`hstep` (the `+2` increment bound) and `hrise` (the rise-rate floor). -/
theorem mainAbove_exp_mgf_drift_add_two
    (i : Fin (L + 1))
    (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (Q : Config (AgentState L K) → Prop)
    (hstep : ∀ c, Q c →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        mainProfileAbove (L := L) (K := K) i c'
          ≤ mainProfileAbove (L := L) (K := K) i c + 2)
    (hrise : ∀ c, Q c →
      ((NonuniformMajority L K).transitionKernel c)
        {c' | mainProfileAbove (L := L) (K := K) i c
            < mainProfileAbove (L := L) (K := K) i c'}
        ≤ ENNReal.ofReal q) :
    ∀ c, Q c →
      ∫⁻ c', mainAboveExpPot (L := L) (K := K) i lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * mainAboveExpPot (L := L) (K := K) i lam c := by
  intro c hcQ
  classical
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
    (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
  have hfac_nonneg : 0 ≤ 1 + q * (Real.exp (2 * lam) - 1) := by
    have hexp2 : 1 ≤ Real.exp (2 * lam) := Real.one_le_exp (by nlinarith)
    nlinarith [hq0, hexp2]
  have h :=
    mgf_one_step_add_two
      ((NonuniformMajority L K).transitionKernel c) lam hlam
      (fun c' => mainProfileAbove (L := L) (K := K) i c')
      (mainProfileAbove (L := L) (K := K) i c)
      (hstep c hcQ) q hq0 (hrise c hcQ)
  calc
    ∫⁻ c', mainAboveExpPot (L := L) (K := K) i lam c'
        ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal
            ((1 + q * (Real.exp (2 * lam) - 1))
              * Real.exp (lam * (mainProfileAbove (L := L) (K := K) i c : ℝ))) := by
          simpa [mainAboveExpPot] using h
    _ = ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
          * mainAboveExpPot (L := L) (K := K) i lam c := by
          rw [mainAboveExpPot, ENNReal.ofReal_mul hfac_nonneg]

/-- **A concrete `MainHourSquaringAtom` with `hdrift` PROVEN**, parameterised by the two carried
protocol facts `hstep`/`hrise` and the scalar Bennett budget `hbudgetScalar`.  `Post c := mainProfileAbove i c < A`. -/
noncomputable def mainHourSquaringAtom_of_rareRise
    (i : Fin (L + 1))
    (hourLen A N₀ : ℕ)
    (Good GoodNext Q : Config (AgentState L K) → Prop)
    (ηhour : ℝ≥0∞)
    (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (hQ_abs :
      ∀ c c', Q c →
        c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (hQ_of_good : ∀ c, Good c → Q c)
    (hGoodNext_of_post :
      ∀ c, mainProfileAbove (L := L) (K := K) i c < A → GoodNext c)
    (hGood_bound :
      ∀ c, Good c → mainProfileAbove (L := L) (K := K) i c ≤ N₀)
    (hstep :
      ∀ c, Q c →
        ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          mainProfileAbove (L := L) (K := K) i c'
            ≤ mainProfileAbove (L := L) (K := K) i c + 2)
    (hrise :
      ∀ c, Q c →
        ((NonuniformMajority L K).transitionKernel c)
          {c' | mainProfileAbove (L := L) (K := K) i c
              < mainProfileAbove (L := L) (K := K) i c'}
          ≤ ENNReal.ofReal q)
    (hbudgetScalar :
      (ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))) ^ hourLen
        * ENNReal.ofReal (Real.exp (lam * (N₀ : ℝ)))
        / ENNReal.ofReal (Real.exp (lam * (A : ℝ))) ≤ ηhour) :
    MainHourSquaringAtom (L := L) (K := K) hourLen Good GoodNext ηhour where
  Φ := mainAboveExpPot (L := L) (K := K) i lam
  hΦ := mainAboveExpPot_measurable (L := L) (K := K) i lam
  Q := Q
  hQ_abs := hQ_abs
  r := ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
  Post := fun c => mainProfileAbove (L := L) (K := K) i c < A
  θ := ENNReal.ofReal (Real.exp (lam * (A : ℝ)))
  hθ := by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  hθ_top := ENNReal.ofReal_ne_top
  hQ_of_good := hQ_of_good
  hgood_next_of_post := hGoodNext_of_post
  hlink := by
    intro c hfail
    rw [not_lt] at hfail
    unfold mainAboveExpPot
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : (A : ℝ) ≤ (mainProfileAbove (L := L) (K := K) i c : ℝ) := by exact_mod_cast hfail
    exact mul_le_mul_of_nonneg_left hcast hlam
  hdrift :=
    mainAbove_exp_mgf_drift_add_two (L := L) (K := K) i lam q hlam hq0 Q hstep hrise
  hbudget := by
    intro c hcGood
    have hΦ_le :
        mainAboveExpPot (L := L) (K := K) i lam c
          ≤ ENNReal.ofReal (Real.exp (lam * (N₀ : ℝ))) := by
      unfold mainAboveExpPot
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hcast : (mainProfileAbove (L := L) (K := K) i c : ℝ) ≤ (N₀ : ℝ) := by
        exact_mod_cast hGood_bound c hcGood
      exact mul_le_mul_of_nonneg_left hcast hlam
    calc
      (ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))) ^ hourLen
          * mainAboveExpPot (L := L) (K := K) i lam c
          / ENNReal.ofReal (Real.exp (lam * (A : ℝ)))
          ≤ (ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))) ^ hourLen
              * ENNReal.ofReal (Real.exp (lam * (N₀ : ℝ)))
              / ENNReal.ofReal (Real.exp (lam * (A : ℝ))) := by gcongr
      _ ≤ ηhour := hbudgetScalar

end MainExponentConfinement

end ExactMajority
