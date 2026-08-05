/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedFinal
import Tri.Theorem6FixedThreshold

/-!
# Fixed-parameter paper form of Theorem 6

The finite construction exposes three numerical size guards and uses a
factor-two stage-count budget.  For each fixed `γ ≥ 1`, the explicit threshold
absorbs all size conditions.  Running the finite construction with `γ + 1`
supplies the factor-two budget; this changes the paper time and gap scales
only by universal constants.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Paper-facing square-root majority gap.  Its doubled slope absorbs the
internal use of `γ + 1 ≤ 2 * γ`. -/
def theorem6FixedLiftedPaperGap
    (n γ : ℕ) : ℕ :=
  (16 * 17_528_751_390_721) *
      (Nat.sqrt (theorem6Q n γ * n) + 1) +
    4_278_190_080

/-- The public `γ`-gap pays the internal `(γ + 1)`-gap. -/
theorem theorem6FixedPaperGap_succ_le_lifted
    {n γ : ℕ}
    (hγ : 1 ≤ γ) :
    theorem6FixedPaperGap
        (theorem6Q n (γ + 1)) n ≤
      theorem6FixedLiftedPaperGap n γ := by
  let x := theorem6Q n γ * n
  let y := theorem6Q n (γ + 1) * n
  have hparameter : γ + 1 ≤ 2 * γ := by omega
  have hq :
      theorem6Q n (γ + 1) ≤
        2 * theorem6Q n γ := by
    unfold theorem6Q
    calc
      (γ + 1) * Nat.log 2 n ≤
          (2 * γ) * Nat.log 2 n :=
        Nat.mul_le_mul_right (Nat.log 2 n)
          hparameter
      _ = 2 * (γ * Nat.log 2 n) := by ring
  have hy : y ≤ 2 * x := by
    dsimp [x, y]
    calc
      theorem6Q n (γ + 1) * n ≤
          (2 * theorem6Q n γ) * n :=
        Nat.mul_le_mul_right n hq
      _ = 2 * (theorem6Q n γ * n) := by ring
  have hsqrt :
      Nat.sqrt y + 1 ≤
        2 * (Nat.sqrt x + 1) := by
    let g := Nat.sqrt x + 1
    have hxUpper : x < g ^ 2 := by
      simpa [g] using Nat.lt_succ_sqrt' x
    have htwoUpper :
        2 * x < (2 * g) ^ 2 := by
      calc
        2 * x < 2 * g ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hxUpper
            (by norm_num)
        _ ≤ 4 * g ^ 2 := by omega
        _ = (2 * g) ^ 2 := by ring
    have hsqrtTwo :
        Nat.sqrt (2 * x) < 2 * g :=
      (Nat.sqrt_lt').2 htwoUpper
    have hySqrt :
        Nat.sqrt y ≤ Nat.sqrt (2 * x) :=
      Nat.sqrt_le_sqrt hy
    omega
  unfold theorem6FixedPaperGap
    theorem6FixedLiftedPaperGap
  calc
    (8 * 17_528_751_390_721) *
          (Nat.sqrt (theorem6Q n (γ + 1) * n) + 1) +
        4_278_190_080 ≤
      (8 * 17_528_751_390_721) *
          (2 *
            (Nat.sqrt (theorem6Q n γ * n) + 1)) +
        4_278_190_080 :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left
          (8 * 17_528_751_390_721)
          (by simpa [x, y] using hsqrt))
        4_278_190_080
    _ =
      (16 * 17_528_751_390_721) *
          (Nat.sqrt (theorem6Q n γ * n) + 1) +
        4_278_190_080 := by ring

/-- The internal `(γ + 1)` horizon is bounded by a universal multiple of the
paper `γ` horizon. -/
theorem theorem6FixedSuccHorizon_le
    (C n γ : ℕ)
    (hγ : 1 ≤ γ) :
    theorem6FixedHorizonCoeff C *
          (γ + 1) * n * Nat.log 2 n ≤
      (2 * theorem6FixedHorizonCoeff C) *
          γ * n * Nat.log 2 n := by
  have hparameter : γ + 1 ≤ 2 * γ := by omega
  calc
    theorem6FixedHorizonCoeff C *
          (γ + 1) * n * Nat.log 2 n ≤
      theorem6FixedHorizonCoeff C *
          (2 * γ) * n * Nat.log 2 n := by
        gcongr
    _ =
      (2 * theorem6FixedHorizonCoeff C) *
          γ * n * Nat.log 2 n := by ring

/-- Paper-facing fixed-parameter Theorem 6.  The population threshold may
depend on the fixed concentration exponent `γ`; the horizon and error
constants do not. -/
theorem theorem6_fixed :
    ∃ C : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧
      ∀ γ : ℕ,
        1 ≤ γ →
        ∃ n₀ : {k : ℕ // 3 ≤ k},
          ∀ n : ℕ,
            ∀ hn : 0 < n,
            ∀ s : InfectionRevealPhysicalState n,
            ∀ hseedActive : s.coarse.1.active = 1,
            ∀ hn₀n : n₀.1 ≤ n,
            s.initialR +
                theorem6FixedLiftedPaperGap n γ ≤
              s.initialB →
            terminalFailureMass
                (iter
                  (infectionStateStep n
                    (n₀.2.trans hn₀n))
                  (C * γ * n * Nat.log 2 n)
                  (infectionRevealPhysicalForget s))
                InfectionXConsensus
              ≤
                2 * ((n : ℝ≥0∞)⁻¹ ^
                  (c * (γ : ℝ))) := by
  rcases theorem6_fixed_of_size_guards with
    ⟨Ccore, nCore, c, hCcore, hc, hnCore,
      hcore⟩
  let C := 2 * theorem6FixedHorizonCoeff Ccore
  have hC : 0 < C := by
    dsimp [C, theorem6FixedHorizonCoeff]
    omega
  refine ⟨C, c, hC, hc, ?_⟩
  intro γ hγ
  let δ := γ + 1
  let n₀ :=
    max nCore (theorem6FixedThreshold δ)
  have hnCoreLe : nCore ≤ n₀ := by
    exact Nat.le_max_left _ _
  have hthresholdLe :
      theorem6FixedThreshold δ ≤ n₀ := by
    exact Nat.le_max_right _ _
  refine
    ⟨⟨n₀, hnCore.trans hnCoreLe⟩, ?_⟩
  intro n hn s hseedActive hn₀n hmargin
  have hnCoreN : nCore ≤ n :=
    hnCoreLe.trans hn₀n
  have hthresholdN :
      theorem6FixedThreshold δ ≤ n :=
    hthresholdLe.trans hn₀n
  have hδ : 2 ≤ δ := by
    dsimp [δ]
    omega
  have hδOne : 1 ≤ δ := by omega
  have hmarginInternal :
      s.initialR +
          theorem6FixedPaperGap
            (theorem6Q n δ) n ≤
        s.initialB := by
    exact
      (Nat.add_le_add_left
        (by
          simpa [δ] using
            theorem6FixedPaperGap_succ_le_lifted
              (n := n) hγ)
        s.initialR).trans hmargin
  have hsize :
      6 * δ * Nat.log 2 n ≤ n := by
    simpa [theorem6Q, mul_assoc] using
      theorem6FixedThreshold_size hthresholdN
  have hmain :=
    hcore n δ hn s hseedActive hnCoreN hδ
      hsize
      (theorem6FixedThreshold_qLarge
        hδOne hthresholdN)
      (theorem6FixedThreshold_cubeGuard
        hδOne hthresholdN)
      (theorem6FixedThreshold_sqrtGuard
        hδOne hthresholdN)
      hmarginInternal
  let K :=
    infectionStateStep n (hnCore.trans hnCoreN)
  let x₀ := infectionRevealPhysicalForget s
  let Tcore :=
    theorem6FixedHorizonCoeff Ccore *
      δ * n * Nat.log 2 n
  let Tpaper := C * γ * n * Nat.log 2 n
  have htimeLe : Tcore ≤ Tpaper := by
    dsimp [Tcore, Tpaper, C, δ]
    exact theorem6FixedSuccHorizon_le
      Ccore n γ hγ
  have hreach :
      Reaches K Tcore (fun z => z = x₀)
        InfectionXConsensus
        (2 * ((n : ℝ≥0∞)⁻¹ ^
          (c * (δ : ℝ)))) := by
    intro z hz
    subst z
    simpa [K, Tcore, x₀] using hmain
  let U := Tpaper - Tcore
  have htime : Tcore + U = Tpaper := by
    exact Nat.add_sub_of_le htimeLe
  have hpadded :=
    hreach.pad_of_absorbing
      (infectionStateStep_consensus n
        (hnCore.trans hnCoreN)) U
  rw [htime] at hpadded
  have hmainPadded :
      terminalFailureMass
          (iter K Tpaper x₀)
          InfectionXConsensus
        ≤
          2 * ((n : ℝ≥0∞)⁻¹ ^
            (c * (δ : ℝ))) := by
    exact hpadded x₀ rfl
  have hbase :
      (n : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast (show 1 ≤ n by omega)
  have hγReal :
      (γ : ℝ) ≤ (δ : ℝ) := by
    exact_mod_cast (show γ ≤ δ by
      dsimp [δ]
      omega)
  have hexponent :
      c * (γ : ℝ) ≤ c * (δ : ℝ) :=
    mul_le_mul_of_nonneg_left hγReal hc.le
  exact hmainPadded.trans
    (mul_le_mul_left'
      (ENNReal.rpow_le_rpow_of_exponent_ge
        hbase hexponent) 2)

end

end Tri

#print axioms Tri.theorem6_fixed
#print axioms
  Tri.theorem6FixedPaperGap_succ_le_lifted
#print axioms Tri.theorem6FixedSuccHorizon_le
