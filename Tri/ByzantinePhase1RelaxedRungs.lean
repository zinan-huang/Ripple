/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedProductiveMonotone
import Tri.ByzantinePhase1RawRung
import Tri.ByzantinePhase2ClockFloor
import Tri.ByzantineJointLaw
import Tri.StoppedHitMonotone
import Tri.Emulation

/-!
# Unconditional Byzantine Phase-I ladder

This module discharges the productive-rung, live-band, and productive-clock
premises in the older Phase-I interfaces.  Each rung compares the
state-dependent paper-worst productive law to a fixed relaxed rate, applies
the stopped form of Lemma 6 at the least integral checkpoint start, and then
uses starting-count monotonicity.  The resulting productive and raw-clock
ladders have no caller-supplied probabilistic hypotheses.
-/

namespace Tri.Byzantine

open scoped ENNReal NNReal

noncomputable section

variable {n B z : ℕ}

noncomputable def phase1DyadicRelaxedRate
    (n A : ℕ) (hn : 0 < n) (hA : A ≤ 2 * n) :
    RelaxedRate where
  fire :=
    1 - (((A : ℕ) : NNReal) / (((2 * n : ℕ) : NNReal)))
  idle :=
    ((A : ℕ) : NNReal) / (((2 * n : ℕ) : NNReal))
  add_eq_one := by
    exact tsub_add_cancel_of_le (by
      rw [div_le_one]
      · exact_mod_cast hA
      · exact_mod_cast (show 0 < 2 * n by omega))

theorem phase1DyadicRelaxedRate_add_allowance
    (n A : ℕ) (hn : 0 < n) (hA : A ≤ 2 * n) :
    (phase1DyadicRelaxedRate n A hn hA).fire +
        (((A : ℕ) : NNReal) / (((2 * n : ℕ) : NNReal))) = 1 :=
  (phase1DyadicRelaxedRate n A hn hA).add_eq_one

theorem phase1DyadicRelaxedRate_fire_pos
    (n A : ℕ) (hn : 0 < n) (hA : A < 2 * n) :
    0 < (phase1DyadicRelaxedRate n A hn hA.le).fire := by
  unfold phase1DyadicRelaxedRate
  simp only
  rw [tsub_pos_iff_lt, div_lt_one]
  · exact_mod_cast hA
  · exact_mod_cast (show 0 < 2 * n by omega)

theorem phase1CheckpointStart_exists
    (n A : ℕ) (hn : 3 ≤ n) (hA0 : 1 ≤ A) (hA : 2 * A ≤ n) :
    ∃ x₀ y₀ D,
      x₀ = (n + A + 1) / 2 ∧
      x₀ + y₀ = n ∧ y₀ + D = x₀ ∧
      n + D = 2 * x₀ ∧
      A ≤ D ∧ D ≤ A + 1 ∧ 0 < D ∧ D < n := by
  let x₀ := (n + A + 1) / 2
  refine ⟨x₀, n - x₀, 2 * x₀ - n, rfl, ?_⟩
  dsimp only [x₀]
  omega

theorem phase1LowerBad_implies_lemma3Bad
    (n A x₀ D : ℕ)
    (hx₀ : x₀ = (n + A + 1) / 2)
    (hgap : n + D = 2 * x₀) :
    ∀ x, 4 * x < 2 * n + A → Lemma3Bad x₀ D x := by
  intro x hx
  unfold Lemma3Bad
  have hq := lemma3Quarter_bounds D
  omega

theorem phase1CheckpointStart_le
    (n A s : ℕ)
    (hpre : n + A ≤ 2 * s) :
    (n + A + 1) / 2 ≤ s := by
  omega

theorem phase1DyadicScale_succ_le_two_mul
    (n d₀ j : ℕ) :
    phase1DyadicScale n d₀ (j + 1) ≤
      2 * phase1DyadicScale n d₀ j := by
  unfold phase1DyadicScale
  rw [pow_succ]
  by_cases h : 2 ^ j * d₀ ≤ (n + 1) / 2
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans_eq (by ring)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans
      (Nat.le_mul_of_pos_left _ (by norm_num))

theorem phase1DyadicScale_seed_le
    (n d₀ j : ℕ) (hd : d₀ ≤ n / 2) :
    d₀ ≤ phase1DyadicScale n d₀ j := by
  unfold phase1DyadicScale
  apply le_min
  · have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    nlinarith
  · omega

/-- `log₂ n` dyadic doublings always reach the ceiling half-population cap
from any positive seed. -/
theorem phase1DyadicScale_log_final
    (n d₀ : ℕ) (hd₀ : 1 ≤ d₀) :
    n ≤ 2 * phase1DyadicScale n d₀ (Nat.log 2 n) := by
  have hpow :
      (n + 1) / 2 ≤ 2 ^ Nat.log 2 n := by
    have hlt :
        n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) n
    rw [pow_succ] at hlt
    omega
  have hpowSeed :
      (n + 1) / 2 ≤ 2 ^ Nat.log 2 n * d₀ := by
    exact hpow.trans
      (Nat.le_mul_of_pos_right _ (by omega))
  unfold phase1DyadicScale
  rw [min_eq_right hpowSeed]
  omega

theorem lemma6TraceStep_isLazyProjection_stopped_subset
    (r : RelaxedRate) (n x₀ Δ : ℕ)
    (Bad : ℕ → Prop) [DecidablePred Bad]
    (hBad : ∀ x, Bad x → Lemma3Bad x₀ Δ x) :
    IsLazyProjection
      (freeze
        (fun x => Bad x ∨ Lemma3Target n Δ x)
        (relaxedProductiveTriChain r n))
      (lemma6TraceStep r n x₀ Δ)
      Lemma3Trace.toX := by
  classical
  intro q
  by_cases hstop : Bad q.x ∨ Lemma3Target n Δ q.x
  · left
    have hbound :
        Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x :=
      hstop.elim (fun h => Or.inl (hBad q.x h)) Or.inr
    rw [lemma6TraceStep_of_boundary r n x₀ Δ q hbound]
    change
      (PMF.pure
        { x := q.x, success := q.success + 1,
          clock := q.clock + 1 }).map Lemma3Trace.toX =
        freeze
          (fun x => Bad x ∨ Lemma3Target n Δ x)
          (relaxedProductiveTriChain r n) q.x
    rw [freeze_of_mem q.x hstop, PMF.pure_map]
    rfl
  · rcases lemma6TraceStep_isLazyProjection r n x₀ Δ q with hK | hpure
    · left
      change
        (lemma6TraceStep r n x₀ Δ q).map Lemma3Trace.toX =
          freeze
            (fun x => Bad x ∨ Lemma3Target n Δ x)
            (relaxedProductiveTriChain r n) q.x
      rw [freeze_of_not_mem q.x hstop]
      exact hK
    · exact Or.inr hpure

theorem lemma6_stopped_of_bad_subset
    (r : RelaxedRate) (n x₀ y₀ Δ : ℕ)
    (Bad : ℕ → Prop) [DecidablePred Bad]
    (hBad : ∀ x, Bad x → Lemma3Bad x₀ Δ x)
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) :
    terminalFailureMass
        (iter
          (freeze
            (fun x => Bad x ∨ Lemma3Target n Δ x)
            (relaxedProductiveTriChain r n))
          (5 * n) x₀)
        (Lemma3Target n Δ) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) := by
  let K :=
    freeze
      (fun x => Bad x ∨ Lemma3Target n Δ x)
      (relaxedProductiveTriChain r n)
  have hlazy :
      IsLazyProjection K
        (lemma6TraceStep r n x₀ Δ) Lemma3Trace.toX :=
    lemma6TraceStep_isLazyProjection_stopped_subset
      r n x₀ Δ Bad hBad
  have hprojection :=
    targetFreeze_failure_le_lazy_projection
      (Lemma3Target n Δ) K
      (lemma6TraceStep r n x₀ Δ)
      Lemma3Trace.toX hlazy
      (5 * n) (lemma3Initial x₀)
  have hfreeze :
      freeze (Lemma3Target n Δ) K = K := by
    funext x
    by_cases htarget : Lemma3Target n Δ x
    · rw [freeze_of_mem x htarget]
      dsimp only [K]
      rw [freeze_of_mem x (Or.inr htarget)]
    · rw [freeze_of_not_mem x htarget]
  rw [hfreeze] at hprojection
  have hfire := lemma6_fire_pos hΔ0 hΔn hrate
  have htrace :=
    (lemma6Trace_failure_explicit
      hpop hgap hΔ0 hΔn hfire hrate).trans
      (lemma6_explicit_errors_le_common hΔ0 hΔn)
  exact hprojection.trans (by
    simpa [K, Lemma3Trace.toX, lemma3Initial] using htrace)

noncomputable def phase1ProductiveXStep
    (h3 : 3 ≤ n) (base : Phase1Level n B z) (x : ℕ) : PMF ℕ :=
  if hxz : x + z ≤ n then
    (phase1ProductiveReferenceStep h3
      (phase1LevelWithX base x hxz)).map
        (fun q => State.x q.1)
  else
    PMF.pure x

theorem phase1ProductiveXStep_of_level
    (h3 : 3 ≤ n) (base q : Phase1Level n B z) :
    phase1ProductiveXStep h3 base (State.x q.1) =
      (phase1ProductiveReferenceStep h3 q).map
        (fun r => State.x r.1) := by
  have hxz : State.x q.1 + z ≤ n := by
    have hxz' := State.xz_le q.1
    have hzq : State.z q.1 = z := q.2
    omega
  rw [phase1ProductiveXStep, dif_pos hxz]
  have hlev := phase1Level_ext_x
    (phase1LevelWithX base (State.x q.1) hxz) q rfl
  rw [hlev]

theorem phase1DyadicRelaxedRate_expect_le_productiveXStep
    (h3 : 3 ≤ n) (base : Phase1Level n B z)
    (d₀ A An x : ℕ)
    (hd₀ : 16 * z ≤ d₀)
    (hdA : d₀ ≤ A)
    (hA : 2 * A ≤ n)
    (hnext : An ≤ 2 * A)
    (hnextCeil : An ≤ (n + 1) / 2)
    (hbad : ¬ 4 * x < 2 * n + A)
    (hgood : ¬ n + An ≤ 2 * x)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect
        (relaxedProductiveTriChain
          (phase1DyadicRelaxedRate n A (by omega) (by omega)) n x) F ≤
      expect (phase1ProductiveXStep h3 base x) F := by
  have hxz : x + z ≤ n := by
    push Not at hbad hgood
    omega
  let q : Phase1Level n B z :=
    phase1LevelWithX base x hxz
  have hxq : State.x q.1 = x := rfl
  have hzq : State.z q.1 = z := q.2
  have hyq : 0 < State.y q.1 := by
    have ht := State.total q.1
    push Not at hbad hgood
    omega
  have hxpos : 0 < x := by
    push Not at hbad
    omega
  let D := 2 * x - n
  have hgap : n + D = 2 * x := by
    dsimp only [D]
    push Not at hbad
    omega
  have hlow : A ≤ 2 * D := by
    dsimp only [D]
    push Not at hbad
    omega
  have hupp : 2 * D ≤ n := by
    dsimp only [D]
    push Not at hgood
    omega
  have hyhat : x + (n - x) = n := by omega
  have hagg : State.y q.1 + State.z q.1 = n - x := by
    have ht := State.total q.1
    omega
  let rEff := phase2PaperEffectiveRate q
  have hrate : IsPaperEffectiveRate rEff q.1 :=
    phase2PaperEffectiveRate_spec q
  have hratePremise :
      (1 : NNReal) ≤
        rEff.fire +
          (((A : ℕ) : NNReal) /
            (((2 * n : ℕ) : NNReal))) := by
    exact interval_lemma6_rate_premise_witness
      (s := q.1) (Δ₀ := d₀) (Δ := D) (a := A) (ŷ := n - x)
      (zSlack := d₀ - 16 * z) (anchorSlack := A - d₀)
      (lowerSlack := 2 * D - A) (upperSlack := n - 2 * D)
      rEff hrate (by omega) (by simpa [hxq] using hyhat)
      (by simpa [hzq] using (show 16 * z + (d₀ - 16 * z) = d₀ by omega))
      (by omega) (by omega) (by omega)
      (by simpa [hxq] using hgap)
  have hfireOrder :
      (phase1DyadicRelaxedRate n A (by omega) (by omega)).fire ≤ rEff.fire :=
    fire_le_of_common_idle_allowance
      (phase1DyadicRelaxedRate_add_allowance
        n A (by omega) (by omega)) hratePremise
  have hfire₀ :
      0 < (phase1DyadicRelaxedRate n A (by omega) (by omega)).fire :=
    phase1DyadicRelaxedRate_fire_pos n A (by omega) (by omega)
  have hfireEff : 0 < rEff.fire := hfire₀.trans_le hfireOrder
  let xPred := x - 1
  let mPred := n - x - 1
  have hxPred : State.x q.1 = xPred + 1 := by
    simp only [hxq, xPred]
    omega
  have hmPred :
      State.y q.1 + State.z q.1 = mPred + 1 := by
    simp only [hagg, mPred]
    omega
  have hpopPred : xPred + mPred + 2 = n := by
    simp only [xPred, mPred]
    omega
  have hprodEff :
      relaxedTriStep rEff (xPred + 1) (mPred + 1) (by omega) xPred +
          relaxedTriStep rEff (xPred + 1) (mPred + 1) (by omega)
            (xPred + 2) ≠ 0 :=
    lemma6_live_productive_nonzero rEff h3 hpopPred hfireEff
  have hmass :=
    phase1ProductiveMass_eq_relaxed
      h3 q rEff hxPred hmPred hrate
  have hP : phase1ProductiveMass h3 q ≠ 0 := by
    intro hzero
    apply hprodEff
    rw [← hmass, hzero]
  calc
    expect
        (relaxedProductiveTriChain
          (phase1DyadicRelaxedRate n A (by omega) (by omega)) n x) F =
      expect
        (relaxedProductiveTriChain
          (phase1DyadicRelaxedRate n A (by omega) (by omega)) n
          (State.x q.1)) F := by rw [hxq]
    _ ≤ expect
        (relaxedProductiveTriChain rEff n (State.x q.1)) F :=
      phase1_band_floor_productive_expect_le_paperWorst
        h3 q (phase1DyadicRelaxedRate n A (by omega) (by omega)) rEff
        (Δ₀ := d₀) (Δ := D) (A := A) (ŷ := n - x)
        (zSlack := d₀ - 16 * z) (anchorSlack := A - d₀)
        (lowerSlack := 2 * D - A) (upperSlack := n - 2 * D)
        (xPred := xPred) (mPred := mPred)
        hxPred hmPred hrate
        (by simpa [hxq] using hyhat)
        (by simpa [hzq] using
          (show 16 * z + (d₀ - 16 * z) = d₀ by omega))
        (by omega) (by omega) (by omega)
        (by simpa [hxq] using hgap)
        (phase1DyadicRelaxedRate_add_allowance
          n A (by omega) (by omega))
        F hF
    _ = expect (phase1ProductiveXStep h3 base x) F := by
      rw [← hxq]
      rw [phase1ProductiveXStep_of_level h3 base q]
      rw [phase1ProductiveReferenceStep_map_x_eq_relaxed
        h3 q rEff hxPred hmPred hyq hrate hP]

theorem lemma6_error_antitone_gap
    (n A D : ℕ) (hn : 0 < n) (hAD : A ≤ D) :
    (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((D : ℝ) ^ 2 / (96 * (n : ℝ))))) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((A : ℝ) ^ 2 / (96 * (n : ℝ))))) := by
  gcongr

theorem phase1_count_productive_dyadic_rung
    (h3 : 3 ≤ n)
    (base : Phase1Level n B z)
    (d₀ j : ℕ)
    (hd₀ : 1 ≤ d₀)
    (hd₀half : d₀ ≤ n / 2)
    (hbudget : 16 * z ≤ d₀) :
    Reaches
      (freeze
        (fun x : ℕ =>
          4 * x < 2 * n + phase1DyadicScale n d₀ j ∨
            n + phase1DyadicScale n d₀ (j + 1) ≤ 2 * x)
        (phase1ProductiveXStep h3 base))
      (5 * n)
      (fun x => n + phase1DyadicScale n d₀ j ≤ 2 * x)
      (fun x =>
        n + phase1DyadicScale n d₀ (j + 1) ≤ 2 * x)
      (phase1DyadicRungEnvelope n d₀ j) := by
  let A := phase1DyadicScale n d₀ j
  let An := phase1DyadicScale n d₀ (j + 1)
  let Bad := fun x : ℕ => 4 * x < 2 * n + A
  let Good := fun x : ℕ => n + An ≤ 2 * x
  let Pre := fun x : ℕ => n + A ≤ 2 * x
  change
    Reaches
      (freeze (fun x => Bad x ∨ Good x)
        (phase1ProductiveXStep h3 base))
      (5 * n) Pre Good
      (phase1DyadicRungEnvelope n d₀ j)
  have hA0 : 1 ≤ A :=
    hd₀.trans (phase1DyadicScale_seed_le n d₀ j hd₀half)
  have hAnCeil : An ≤ (n + 1) / 2 := by
    dsimp only [An, phase1DyadicScale]
    exact min_le_right _ _
  have hnext : An ≤ 2 * A := by
    exact phase1DyadicScale_succ_le_two_mul n d₀ j
  by_cases hsame : A = An
  · intro x hx
    have hgood : Good x := by
      dsimp only [Good, Pre] at *
      rwa [← hsame]
    rw [iter_targetFreeze_of_mem (fun x => Bad x ∨ Good x)
      (phase1ProductiveXStep h3 base) x (Or.inr hgood) (5 * n)]
    change terminalFailureMass (PMF.pure x) Good ≤
      phase1DyadicRungEnvelope n d₀ j
    rw [terminalFailureMass_pure, if_pos hgood]
    exact bot_le
  · have hAexact : A = 2 ^ j * d₀ := by
      dsimp only [A, An, phase1DyadicScale] at hsame ⊢
      by_cases hle : 2 ^ j * d₀ ≤ (n + 1) / 2
      · exact min_eq_left hle
      · have hcur :
            min (2 ^ j * d₀) ((n + 1) / 2) = (n + 1) / 2 :=
          min_eq_right (le_of_not_ge hle)
        have hnxt :
            min (2 ^ (j + 1) * d₀) ((n + 1) / 2) =
              (n + 1) / 2 := by
          apply min_eq_right
          rw [pow_succ]
          nlinarith [(Nat.one_le_two_pow : 1 ≤ 2 ^ j)]
        exact False.elim (hsame (hcur.trans hnxt.symm))
    have hAhalf : 2 * A ≤ n := by
      have hpowle :
          2 ^ j * d₀ ≤ 2 ^ (j + 1) * d₀ := by
        rw [pow_succ]
        have hmul :
            2 ^ j * d₀ ≤ 2 * (2 ^ j * d₀) :=
          Nat.le_mul_of_pos_left _ (by norm_num)
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
      have hAle : A ≤ An := by
        dsimp only [A, An, phase1DyadicScale]
        exact min_le_min_right _ hpowle
      have hAlt : A < An := lt_of_le_of_ne hAle hsame
      omega
    have hA2n : A ≤ 2 * n := by omega
    let r₀ := phase1DyadicRelaxedRate n A (by omega) hA2n
    let Kref := relaxedProductiveTriChain r₀ n
    let Kdom := phase1ProductiveXStep h3 base
    have hBadLower :
        ∀ ⦃i k : ℕ⦄, i ≤ k → Bad k → Bad i := by
      intro i k hik hk
      exact lt_of_le_of_lt (Nat.mul_le_mul_left 4 hik) hk
    have hGoodUpper :
        ∀ ⦃i k : ℕ⦄, i ≤ k → Good i → Good k := by
      intro i k hik hi
      exact hi.trans (Nat.mul_le_mul_left 2 hik)
    obtain
      ⟨x₀, y₀, D, hx₀, hpop, hgap, hgap₂,
        hAD, hDA, hD0, hDn⟩ :=
      phase1CheckpointStart_exists n A h3 hA0 hAhalf
    have hrateD :
        (1 : NNReal) ≤
          r₀.fire +
            (((D : ℕ) : NNReal) /
              (((2 * n : ℕ) : NNReal))) := by
      calc
        (1 : NNReal) =
            r₀.fire +
              (((A : ℕ) : NNReal) /
                (((2 * n : ℕ) : NNReal))) := by
          exact
            (phase1DyadicRelaxedRate_add_allowance
              n A (by omega) hA2n).symm
        _ ≤ r₀.fire +
                (((D : ℕ) : NNReal) /
                (((2 * n : ℕ) : NNReal))) := by
          gcongr
    have hBadLemma :
        ∀ x, Bad x → Lemma3Bad x₀ D x := by
      exact phase1LowerBad_implies_lemma3Bad
        n A x₀ D hx₀ hgap₂
    have hrel :
        terminalFailureMass
            (iter
              (freeze
                (fun x => Bad x ∨ Lemma3Target n D x)
                Kref)
              (5 * n) x₀)
            (Lemma3Target n D) ≤
          phase1DyadicRungEnvelope n d₀ j := by
      calc
        terminalFailureMass
              (iter
                (freeze
                  (fun x => Bad x ∨ Lemma3Target n D x)
                  Kref)
                (5 * n) x₀)
              (Lemma3Target n D) ≤
            (2 : ℝ≥0∞) *
              ENNReal.ofReal
                (Real.exp
                  (-((D : ℝ) ^ 2 / (96 * (n : ℝ))))) := by
          exact lemma6_stopped_of_bad_subset
            r₀ n x₀ y₀ D Bad hBadLemma
            hpop hgap hD0 hDn hrateD
        _ ≤ (2 : ℝ≥0∞) *
              ENNReal.ofReal
                (Real.exp
                  (-((A : ℝ) ^ 2 / (96 * (n : ℝ))))) :=
          lemma6_error_antitone_gap n A D (by omega) hAD
        _ = phase1DyadicRungEnvelope n d₀ j := by
          rw [phase1DyadicRungEnvelope_eq_gap, hAexact]
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_ofNat]
    have hcapGood :
        ∀ x, Lemma3Target n D x → Good x := by
      intro x hx
      unfold Lemma3Target at hx
      dsimp only [Good]
      have hAnD : An ≤ min (2 * D) n := by
        apply le_min
        · exact hnext.trans (Nat.mul_le_mul_left 2 hAD)
        · omega
      exact (Nat.add_le_add_left hAnD n).trans hx
    have href :
        ∀ s, Pre s →
          terminalFailureMass
              (iter
                (freeze (fun x => Bad x ∨ Good x) Kref)
                (5 * n) s)
              Good ≤
            phase1DyadicRungEnvelope n d₀ j := by
      intro s hs
      by_cases hgood : Good s
      · rw [iter_targetFreeze_of_mem
          (fun x => Bad x ∨ Good x) Kref s (Or.inr hgood) (5 * n)]
        simp [terminalFailureMass_pure, hgood]
      · have hstartle : x₀ ≤ s := by
          rw [hx₀]
          exact phase1CheckpointStart_le n A s hs
        calc
          terminalFailureMass
                (iter
                  (freeze (fun x => Bad x ∨ Good x) Kref)
                  (5 * n) s)
                Good ≤
              terminalFailureMass
                (iter
                  (freeze
                    (fun x => Bad x ∨ Lemma3Target n D x)
                    Kref)
                  (5 * n) s)
                (Lemma3Target n D) :=
            stoppedBand_failure_mono_good
              Bad (Lemma3Target n D) Good Kref hcapGood (5 * n) s
          _ ≤ terminalFailureMass
                (iter
                  (freeze
                    (fun x => Bad x ∨ Lemma3Target n D x)
                    Kref)
                  (5 * n) x₀)
                (Lemma3Target n D) :=
            stoppedBand_failure_antitone_start
              Bad (Lemma3Target n D) Kref hBadLower
              (by
                intro i k hik hi
                unfold Lemma3Target at hi ⊢
                exact hi.trans (Nat.mul_le_mul_left 2 hik))
              (fun F hF =>
                relaxedProductiveTriChain_expect_monotone
                  r₀ n
                  (phase1DyadicRelaxedRate_fire_pos
                    n A (by omega) (by omega))
                  F hF)
              (5 * n) hstartle
          _ ≤ phase1DyadicRungEnvelope n d₀ j := hrel
    have hreach :
        Reaches (freeze (fun x => Bad x ∨ Good x) Kdom)
          (5 * n) Pre Good
          (phase1DyadicRungEnvelope n d₀ j) := by
      intro x hx
      exact
        (stoppedBand_failure_le_of_live_stochDom
          Bad Good Kref Kdom hBadLower hGoodUpper
          (fun F hF =>
            relaxedProductiveTriChain_expect_monotone
              r₀ n
              (phase1DyadicRelaxedRate_fire_pos
                n A (by omega) (by omega))
              F hF)
          (fun i hbad hgood F hF =>
            phase1DyadicRelaxedRate_expect_le_productiveXStep
              h3 base d₀ A An i
              hbudget
              (phase1DyadicScale_seed_le n d₀ j hd₀half)
              hAhalf hnext hAnCeil hbad hgood F hF)
          (5 * n) x).trans
          (href x hx)
    simpa [Good, Pre, Kdom, A, An] using hreach

theorem phase1_reference_productive_dyadic_rung
    (h3 : 3 ≤ n)
    (d₀ j : ℕ)
    (hd₀ : 1 ≤ d₀)
    (hd₀half : d₀ ≤ n / 2)
    (hbudget : 16 * z ≤ d₀) :
    Reaches
      (freeze
        (Phase1DyadicStop
          (B := B) (z := z) n d₀ j)
        (phase1ProductiveReferenceStep
          (n := n) (B := B) (z := z) h3))
      (5 * n)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
      (Phase1DyadicCheckpoint
        (B := B) (z := z) n d₀ (j + 1))
      (phase1DyadicRungEnvelope n d₀ j) := by
  let StopState :=
    Phase1DyadicStop (B := B) (z := z) n d₀ j
  let GoodState :=
    Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1)
  let StopCount :=
    fun x : ℕ =>
      4 * x < 2 * n + phase1DyadicScale n d₀ j ∨
        n + phase1DyadicScale n d₀ (j + 1) ≤ 2 * x
  let GoodCount :=
    fun x : ℕ => n + phase1DyadicScale n d₀ (j + 1) ≤ 2 * x
  let Kstate :=
    freeze StopState
      (phase1ProductiveReferenceStep
        (n := n) (B := B) (z := z) h3)
  intro q hq
  let base : Phase1Level n B z := q
  have hcount :=
    phase1_count_productive_dyadic_rung
      (n := n) (B := B) (z := z)
      h3 base d₀ j hd₀ hd₀half hbudget
  have hpre :
      n + phase1DyadicScale n d₀ j ≤ 2 * State.x q.1 := hq
  have hgood :
      ∀ r : Phase1Level n B z,
        GoodState r ↔ GoodCount (State.x r.1) := by
    intro r
    rfl
  have hstop :
      ∀ r : Phase1Level n B z,
        StopState r ↔ StopCount (State.x r.1) := by
    intro r
    rfl
  let Kcount :=
    freeze StopCount (phase1ProductiveXStep h3 base)
  have hstep :
      ∀ r : Phase1Level n B z,
        (Kstate r).map (fun s => State.x s.1) =
          Kcount (State.x r.1) := by
    intro r
    dsimp only [Kstate, Kcount]
    by_cases hr : StopState r
    · have hrc : StopCount (State.x r.1) := (hstop r).1 hr
      rw [freeze_of_mem r hr,
        freeze_of_mem (State.x r.1) hrc, PMF.pure_map]
    · have hrc : ¬ StopCount (State.x r.1) :=
        fun hc => hr ((hstop r).2 hc)
      rw [freeze_of_not_mem r hr,
        freeze_of_not_mem (State.x r.1) hrc]
      exact (phase1ProductiveXStep_of_level h3 base r).symm
  have hmap :
      (iter Kstate (5 * n) q).map
          (fun s => State.x s.1) =
        iter Kcount (5 * n) (State.x q.1) :=
    iter_map_of_step_map Kstate Kcount
      (fun s => State.x s.1) hstep (5 * n) q
  have hc := hcount (State.x q.1) hpre
  change
    terminalFailureMass (iter Kstate (5 * n) q) GoodState ≤
      phase1DyadicRungEnvelope n d₀ j
  change
    terminalFailureMass
        (iter Kcount (5 * n) (State.x q.1)) GoodCount ≤
      phase1DyadicRungEnvelope n d₀ j at hc
  rw [← hmap, terminalFailureMass_map] at hc
  simpa [GoodState, GoodCount, Phase1DyadicCheckpoint] using hc

theorem phase1PaperEffectiveRate_fire_ge_three_quarters
    (q : Phase1Level n B z)
    (hmpos : 0 < State.y q.1 + State.z q.1)
    (hminor : 4 * z ≤ State.y q.1 + State.z q.1) :
    (3 / 4 : NNReal) ≤ (phase2PaperEffectiveRate q).fire := by
  have hm : State.y q.1 + State.z q.1 ≠ 0 := by omega
  simp only [phase2PaperEffectiveRate, hm, ↓reduceDIte]
  change
    (3 : NNReal) / 4 ≤
      (State.y q.1 : NNReal) /
        (State.y q.1 + State.z q.1 : ℕ)
  rw [div_le_div_iff₀
    (by norm_num : (0 : NNReal) < 4)
    (by exact_mod_cast hmpos)]
  have hzq : State.z q.1 = z := q.2
  have hnat :
      3 * (State.y q.1 + State.z q.1) ≤
        4 * State.y q.1 := by omega
  exact_mod_cast (by simpa [mul_comm] using hnat)

theorem phase1_reference_raw_dyadic_rung
    (h3 : 3 ≤ n)
    (d₀ j : ℕ)
    (hd₀ : 1 ≤ d₀)
    (hd₀half : d₀ ≤ n / 2)
    (hbudget : 16 * z ≤ d₀) :
    Reaches
      (freeze
        (Phase1DyadicCheckpoint
          (B := B) (z := z) n d₀ (j + 1))
        (phase1ReferenceStep
          (n := n) (B := B) (z := z) h3))
      (phase1RawDyadicRungHorizon n)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
      (Phase1DyadicCheckpoint
        (B := B) (z := z) n d₀ (j + 1))
      (phase1RawDyadicRungError n d₀ j) := by
  let A := phase1DyadicScale n d₀ j
  let An := phase1DyadicScale n d₀ (j + 1)
  have hA0 : 1 ≤ A :=
    hd₀.trans (phase1DyadicScale_seed_le n d₀ j hd₀half)
  have hACeil : A ≤ (n + 1) / 2 := by
    dsimp only [A, phase1DyadicScale]
    exact min_le_right _ _
  have hAnCeil : An ≤ (n + 1) / 2 := by
    dsimp only [An, phase1DyadicScale]
    exact min_le_right _ _
  have hlive :
      ∀ q : Phase1Level n B z,
        ¬ Phase1DyadicStop (B := B) (z := z) n d₀ j q →
          0 < State.x q.1 ∧ 0 < State.y q.1 := by
    intro q hstop
    unfold Phase1DyadicStop at hstop
    push Not at hstop
    have ht := State.total q.1
    have hzq : State.z q.1 = z := q.2
    unfold Phase1LowerFailure Phase1DyadicCheckpoint at hstop
    have hlower :
        2 * n + A ≤ 4 * State.x q.1 := by
      dsimp only [A]
      omega
    have hupper :
        2 * State.x q.1 < n + An := by
      dsimp only [An]
      omega
    constructor <;> omega
  have hpFloor :
      ∀ q : Phase1Level n B z,
        ¬ Phase1DyadicStop (B := B) (z := z) n d₀ j q →
          (phase1ClockP : ℝ≥0∞) ≤ phase1ProductiveMass h3 q := by
    intro q hstop
    have hl := hlive q hstop
    unfold Phase1DyadicStop at hstop
    push Not at hstop
    unfold Phase1LowerFailure Phase1DyadicCheckpoint at hstop
    have hlower :
        2 * n + A ≤ 4 * State.x q.1 := by
      dsimp only [A]
      omega
    have hupper :
        2 * State.x q.1 < n + An := by
      dsimp only [An]
      omega
    have hxLo : n < 2 * State.x q.1 := by omega
    have hxHi : 4 * State.x q.1 < 3 * n := by omega
    have hminor :
        4 * z ≤ State.y q.1 + State.z q.1 := by
      have ht := State.total q.1
      have hzq : State.z q.1 = z := q.2
      omega
    have hmpos : 0 < State.y q.1 + State.z q.1 := by omega
    let xPred := State.x q.1 - 1
    let mPred := State.y q.1 + State.z q.1 - 1
    have hxPred : State.x q.1 = xPred + 1 := by
      simp only [xPred]
      omega
    have hmPred :
        State.y q.1 + State.z q.1 = mPred + 1 := by
      simp only [mPred]
      omega
    exact phase1ProductiveMass_ge_clockP
      h3 q (phase2PaperEffectiveRate q)
      hxPred hmPred (phase2PaperEffectiveRate_spec q)
      (phase1PaperEffectiveRate_fire_ge_three_quarters
        q hmpos hminor) hxLo hxHi
  exact phase1_reference_raw_dyadic_rung_of_productive
    (n := n) (B := B) (z := z)
    h3 d₀ j hlive hpFloor
    (phase1_reference_productive_dyadic_rung
      (n := n) (B := B) (z := z)
      h3 d₀ j hd₀ hd₀half hbudget)

theorem phase1_reference_raw_dyadic_ladder_to_half
    (h3 : 3 ≤ n)
    (d₀ J : ℕ)
    (hd₀ : 1 ≤ d₀)
    (hd₀half : d₀ ≤ n / 2)
    (hbudget : 16 * z ≤ d₀)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J) :
    Reaches
      (freeze
        (Phase1HalfTarget (n := n) (B := B) (z := z))
        (phase1ReferenceStep
          (n := n) (B := B) (z := z) h3))
      (phase1RawDyadicLadderHorizon n J)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (phase1RawDyadicLadderError n d₀ J) := by
  apply phase1_reference_raw_stopped_ladder_to_half
    (n := n) (B := B) (z := z) h3 d₀ J hfinal
  intro j hj
  exact phase1_reference_raw_dyadic_rung
    (n := n) (B := B) (z := z)
    h3 d₀ j hd₀ hd₀half hbudget

/-- Joint history/fixed-fibre form of the unconditional raw Phase-I ladder
for an arbitrary adaptive Byzantine strategy. -/
theorem phase1_controlled_raw_dyadic_ladder_to_half
    (σ : Strategy n B)
    (h3 : 3 ≤ n)
    (d₀ J : ℕ)
    (hd₀ : 1 ≤ d₀)
    (hd₀half : d₀ ≤ n / 2)
    (hbudget : 16 * z ≤ d₀)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J) :
    Reaches
      (freeze
        (fun r : History n B × Phase1Level n B z =>
          Phase1HalfTarget r.2)
        (fun r =>
          phase1ControlledStep
            (n := n) (B := B) (z := z)
            σ h3 r.1 r.2))
      (phase1RawDyadicLadderHorizon n J)
      (fun r =>
        Phase1DyadicCheckpoint
          (B := B) (z := z) n d₀ 0 r.2)
      (fun r => Phase1HalfTarget r.2)
      (phase1RawDyadicLadderError n d₀ J) := by
  rintro ⟨hist, q⟩ hq
  have hcompare :=
    stoppedControlledBand_failure_le_reference
      (fun _ : Phase1Level n B z => False)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (phase1ReferenceStep
        (n := n) (B := B) (z := z) h3)
      (fun hist q =>
        phase1ControlledStep
          (n := n) (B := B) (z := z)
          σ h3 hist q)
      (by
        intro i k hik hk
        exact False.elim hk)
      (by
        intro i k hik hi
        exact phase1HalfTarget_upper hik hi)
      (phase1ReferenceStep_mono
        (n := n) (B := B) (z := z) h3)
      (phase1_reference_le_controlled
        (n := n) (B := B) (z := z) σ h3)
      (phase1RawDyadicLadderHorizon n J)
      hist q
  have hfreezeControlled :
      freeze
          (fun r : History n B × Phase1Level n B z =>
            False ∨ Phase1HalfTarget r.2)
          (fun r =>
            phase1ControlledStep
              (n := n) (B := B) (z := z)
              σ h3 r.1 r.2) =
        freeze
          (fun r : History n B × Phase1Level n B z =>
            Phase1HalfTarget r.2)
          (fun r =>
            phase1ControlledStep
              (n := n) (B := B) (z := z)
              σ h3 r.1 r.2) := by
    funext r
    unfold freeze
    by_cases hr : Phase1HalfTarget r.2
    · rw [if_pos (Or.inr hr), if_pos hr]
    · rw [if_neg (by simpa using hr), if_neg hr]
  have hfreezeReference :
      freeze
          (fun r : Phase1Level n B z =>
            False ∨ Phase1HalfTarget r)
          (phase1ReferenceStep
            (n := n) (B := B) (z := z) h3) =
        freeze
          (Phase1HalfTarget
            (n := n) (B := B) (z := z))
          (phase1ReferenceStep
            (n := n) (B := B) (z := z) h3) := by
    funext r
    unfold freeze
    by_cases hr : Phase1HalfTarget r
    · rw [if_pos (Or.inr hr), if_pos hr]
    · rw [if_neg (by simpa using hr), if_neg hr]
  rw [hfreezeControlled, hfreezeReference] at hcompare
  exact hcompare.trans
    (phase1_reference_raw_dyadic_ladder_to_half
      (n := n) (B := B) (z := z)
      h3 d₀ J hd₀ hd₀half hbudget hfinal q hq)

/-- Forget the fixed-fibre proof while retaining the adaptive transcript. -/
def phase1JointForget
    (q : History n B × Phase1Level n B z) :
    ControlledJointState n B :=
  (q.1, q.2.1)

/-- The Phase-I fibre controlled step projects exactly to the physical joint
history/state step. -/
theorem phase1ControlledStep_map_jointForget
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (hist : History n B) (q : Phase1Level n B z) :
    (phase1ControlledStep
        (n := n) (B := B) (z := z)
        σ h3 hist q).map phase1JointForget =
      controlledJointStep σ h3 (hist, q.1) := by
  unfold phase1JointForget controlledJointStep
    phase1ControlledStep adaptiveEventStep fixedEventStep
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- Physical joint-law form of the complete unconditional Phase-I ladder. -/
theorem phase1_controlledJoint_raw_dyadic_ladder_to_half
    (σ : Strategy n B)
    (h3 : 3 ≤ n)
    (d₀ J : ℕ)
    (hd₀ : 1 ≤ d₀)
    (hd₀half : d₀ ≤ n / 2)
    (hbudget : 16 * z ≤ d₀)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J) :
    Reaches
      (freeze
        (fun r : ControlledJointState n B =>
          4 * (State.y r.2 + State.z r.2) ≤ n)
        (controlledJointStep σ h3))
      (phase1RawDyadicLadderHorizon n J)
      (fun r =>
        n + phase1DyadicScale n d₀ 0 ≤ 2 * State.x r.2 ∧
          State.z r.2 = z)
      (fun r => 4 * (State.y r.2 + State.z r.2) ≤ n)
      (phase1RawDyadicLadderError n d₀ J) := by
  rintro ⟨hist, s⟩ ⟨hs, hsz⟩
  let q : Phase1Level n B z := ⟨s, hsz⟩
  let GoodFibre :=
    fun r : History n B × Phase1Level n B z =>
      Phase1HalfTarget r.2
  let GoodPhysical :=
    fun r : ControlledJointState n B =>
      4 * (State.y r.2 + State.z r.2) ≤ n
  let Kfibre :=
    freeze GoodFibre
      (fun r =>
        phase1ControlledStep
          (n := n) (B := B) (z := z)
          σ h3 r.1 r.2)
  let Kphysical :=
    freeze GoodPhysical (controlledJointStep σ h3)
  have hq :
      Phase1DyadicCheckpoint
        (B := B) (z := z) n d₀ 0 q := by
    exact hs
  have hfibre :=
    phase1_controlled_raw_dyadic_ladder_to_half
      (n := n) (B := B) (z := z)
      σ h3 d₀ J hd₀ hd₀half hbudget hfinal (hist, q) hq
  have hgood :
      ∀ r : History n B × Phase1Level n B z,
        GoodFibre r ↔ GoodPhysical (phase1JointForget r) := by
    intro r
    unfold GoodFibre GoodPhysical phase1JointForget Phase1HalfTarget
    change
      3 * n ≤ 4 * State.x r.2.1 ↔
        4 * (State.y r.2.1 + State.z r.2.1) ≤ n
    have ht := State.total r.2.1
    omega
  have hstep :
      ∀ r : History n B × Phase1Level n B z,
        (Kfibre r).map phase1JointForget =
          Kphysical (phase1JointForget r) := by
    intro r
    dsimp only [Kfibre, Kphysical]
    by_cases hr : GoodFibre r
    · have hr' : GoodPhysical (phase1JointForget r) :=
        (hgood r).1 hr
      rw [freeze_of_mem r hr,
        freeze_of_mem (phase1JointForget r) hr',
        PMF.pure_map]
    · have hr' : ¬ GoodPhysical (phase1JointForget r) :=
        fun hp => hr ((hgood r).2 hp)
      rw [freeze_of_not_mem r hr,
        freeze_of_not_mem (phase1JointForget r) hr']
      exact phase1ControlledStep_map_jointForget
        σ h3 r.1 r.2
  have hmap :
      (iter Kfibre
          (phase1RawDyadicLadderHorizon n J)
          (hist, q)).map phase1JointForget =
        iter Kphysical
          (phase1RawDyadicLadderHorizon n J)
          (hist, s) :=
    iter_map_of_step_map
      Kfibre Kphysical phase1JointForget hstep
      (phase1RawDyadicLadderHorizon n J)
      (hist, q)
  change
    terminalFailureMass
        (iter Kphysical
          (phase1RawDyadicLadderHorizon n J)
          (hist, s))
        GoodPhysical ≤
      phase1RawDyadicLadderError n d₀ J
  rw [← hmap, terminalFailureMass_map]
  calc
    terminalFailureMass
          (iter Kfibre
            (phase1RawDyadicLadderHorizon n J)
            (hist, q))
          (fun r => GoodPhysical (phase1JointForget r)) =
        terminalFailureMass
          (iter Kfibre
            (phase1RawDyadicLadderHorizon n J)
            (hist, q))
          GoodFibre := by
      unfold terminalFailureMass
      apply tsum_congr
      intro r
      by_cases hp : GoodPhysical (phase1JointForget r)
      · rw [if_pos hp, if_pos ((hgood r).2 hp)]
      · rw [if_neg hp, if_neg (fun hf => hp ((hgood r).1 hf))]
    _ ≤ phase1RawDyadicLadderError n d₀ J := hfibre

end

end Tri.Byzantine

#print axioms Tri.Byzantine.phase1_count_productive_dyadic_rung
#print axioms Tri.Byzantine.phase1_reference_productive_dyadic_rung
#print axioms Tri.Byzantine.phase1_reference_raw_dyadic_rung
#print axioms Tri.Byzantine.phase1_reference_raw_dyadic_ladder_to_half
#print axioms Tri.Byzantine.phase1_controlledJoint_raw_dyadic_ladder_to_half
