/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase2Contract
import Tri.Phase3Stop

/-!
# Final assembly of Theorem 1(b)

`theorem1b_of_available_components` is the shortest conditional headline
supported by the modules currently present in the repository.  It invokes
`theorem1b_of_fewer`, constructs every phase-2 `hcontract` field from
`phase2_hcontract`, and constructs every phase-3 bridge from
`phase3Bridge_of_escapeSlack`.

The following files named by the final assembly specification are currently
absent: `Tri.Phase1Ladder` and `Tri.StageErrors`.  Their exact remaining outputs
are exposed as four hypotheses.

`hphase1` is **(ii), needs `Tri.Phase1Ladder`**, with type

    ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → AssemblyInitial n γ x →
      Phase1BandBridge n x (phase1Horizon C₁ n γ) (ε₁ n γ).

`hphase2Certificates` is **(ii), needs the phase-2 part of
`Tri.StageErrors`**, with type

    ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ∀ i < Nat.log 2 n, ∀ x, Phase2Stage n (2 + i) x → x < n →
      Phase2ArithmeticCertificate n (2 + i) x.

The band alternative contains no contraction field; that field is proved here
from its `Phase2Live` inclusion.

`hescape` is **(ii), needs `phase3_escapeSlack_proved` from
`Tri.StageErrors`**, with type

    ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase2Exit n γ x →
      Phase3EscapeSlack n (phase3Horizon C₃ n) x.

`hbudget` is **(i), arithmetic/analysis**, with type

    ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ε₁ n γ + phase2Error n + phase3Error C₃ n γ ≤
      (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ)).

No residual is classified **(iii), looks false**.  In particular, the known
false whole-phase single-base contraction is not assumed here.
-/

namespace Tri

open scoped ENNReal

/-- Arithmetic, live-region, and scalar-error data for the band alternative of
one phase-2 stage.  Its one-step contraction is deliberately omitted because
`phase2_hcontract` proves it. -/
structure Phase2BandArithmetic (n s x : ℕ) where
  /-- Lower freeze boundary. -/
  bandLo : ℕ
  /-- Complementary population parameter at the lower boundary. -/
  bandBHi : ℕ
  /-- Distance of the initial state above the lower boundary. -/
  bandGap : ℕ
  /-- Distance from the initial state to the upper freeze boundary. -/
  upperGap : ℕ
  /-- Threshold below which a return from the upper boundary is failure. -/
  returnLo : ℕ
  /-- Complementary population parameter at the return threshold. -/
  returnBHi : ℕ
  /-- Distance used in the upper Feller-return estimate. -/
  returnGap : ℕ
  /-- The initial state is exactly `bandGap` above the lower boundary. -/
  hstart : bandLo + bandGap = x
  /-- Population decomposition at the lower boundary. -/
  hbandPop : bandLo + bandBHi + 2 = n
  /-- Positivity of the lower boundary. -/
  hbandLo : 0 < bandLo
  /-- Positivity of its complementary population parameter. -/
  hbandBHi : 0 < bandBHi
  /-- The lower boundary is on the majority side. -/
  hbandMaj : bandBHi ≤ bandLo
  /-- The initial state lies strictly above the lower boundary. -/
  hbandGap : 0 < bandGap
  /-- The upper boundary lies strictly above the initial state. -/
  hupperGap : 0 < upperGap
  /-- The upper boundary remains in the physical range. -/
  hupperPhysical : x + upperGap ≤ n
  /-- Population decomposition at the return threshold. -/
  hreturnPop : returnLo + returnBHi + 2 = n
  /-- Positivity of the return threshold. -/
  hreturnLo : 0 < returnLo
  /-- Positivity of its complementary population parameter. -/
  hreturnBHi : 0 < returnBHi
  /-- The return threshold is on the majority side. -/
  hreturnMaj : returnBHi ≤ returnLo
  /-- The upper boundary has the required return gap. -/
  hreturnGap : returnLo + returnGap ≤ x + upperGap
  /-- A next-stage success lies above the lower freeze boundary. -/
  hlower : ∀ z, Phase2Upper n (s + 1) z → bandLo < z
  /-- Reaching the upper freeze boundary implies the next checkpoint. -/
  hupper : ∀ z, x + upperGap ≤ z → Phase2Upper n (s + 1) z
  /-- Every failure of the next checkpoint lies below `returnLo`. -/
  hfailure : ∀ z, ¬ Phase2Upper n (s + 1) z → z ≤ returnLo
  /-- The complete selected open band lies in the proved phase-2 live region. -/
  hlive : ∀ z, bandLo < z → z < x + upperGap → Phase2Live n s z
  /-- Lower ruin, contracted live mass, and upper return fit the stage error. -/
  herror :
    (((bandBHi : ℝ≥0∞) / (bandLo : ℝ≥0∞)) ^ bandGap +
        phase2DecayENN s ^ (4 * n) * ((1 : ℝ≥0∞) / 2) ^ x /
          ((1 : ℝ≥0∞) / 2) ^ (x + upperGap)) +
      ((returnBHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ returnGap ≤
        phase2StageError n s

/-- Convert arithmetic phase-2 band data into the full bridge, using the
proved live-band contraction for its only probabilistic field. -/
noncomputable def Phase2BandArithmetic.toBandBridge
    {n s x : ℕ} (B : Phase2BandArithmetic n s x) :
    Phase2BandBridge n s x where
  bandLo := B.bandLo
  bandBHi := B.bandBHi
  bandGap := B.bandGap
  upperGap := B.upperGap
  returnLo := B.returnLo
  returnBHi := B.returnBHi
  returnGap := B.returnGap
  φ := phase2DecayENN s
  hstart := B.hstart
  hbandPop := B.hbandPop
  hbandLo := B.hbandLo
  hbandBHi := B.hbandBHi
  hbandMaj := B.hbandMaj
  hbandGap := B.hbandGap
  hupperGap := B.hupperGap
  hupperPhysical := B.hupperPhysical
  hreturnPop := B.hreturnPop
  hreturnLo := B.hreturnLo
  hreturnBHi := B.hreturnBHi
  hreturnMaj := B.hreturnMaj
  hreturnGap := B.hreturnGap
  hlower := B.hlower
  hupper := B.hupper
  hfailure := B.hfailure
  hcontract := phase2_hcontract n s B.bandLo (x + B.upperGap) B.hlive
  herror := B.herror

/-- The residual certificate choice for one nonconsensus phase-2 state. -/
abbrev Phase2ArithmeticCertificate (n s x : ℕ) :=
  Phase2ReturnBridge n s x ⊕ Phase2BandArithmetic n s x

/-- Construct the complete phase-2 ladder from arithmetic/scalar certificates;
all band contractions are supplied by `phase2_hcontract`. -/
noncomputable def phase2_bridge_of_arithmetic (n : ℕ) (h3 : 3 ≤ n)
    (hcertificates : ∀ i < Nat.log 2 n, ∀ x,
      Phase2Stage n (2 + i) x → x < n →
        Phase2ArithmeticCertificate n (2 + i) x) :
    Phase2Bridge n (Nat.log 2 n) :=
  phase2_bridge n h3 (by
    intro i hi x hx hxlt
    rcases hcertificates i hi x hx hxlt with B | B
    · exact Sum.inl B
    · exact Sum.inr B.toBandBridge)

/-- **Theorem 1(b) from every component currently proved in the repository.**

The four hypotheses are exactly the outputs still missing from
`Tri.Phase1Ladder` and `Tri.StageErrors`; phase-2 contraction and the phase-3
stopped bridge are not residual assumptions. -/
theorem theorem1b_of_available_components
    (C₁ C₃ n₀ : ℕ) (c : ℝ) (ε₁ : ℕ → ℕ → ℝ≥0∞)
    (hc : 0 < c) (hn₀ : 3 ≤ n₀)
    (hphase1 : ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → AssemblyInitial n γ x →
        Phase1BandBridge n x (phase1Horizon C₁ n γ) (ε₁ n γ))
    (hphase2Certificates : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ∀ i < Nat.log 2 n, ∀ x, Phase2Stage n (2 + i) x → x < n →
        Phase2ArithmeticCertificate n (2 + i) x)
    (hescape : ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase2Exit n γ x →
        Phase3EscapeSlack n (phase3Horizon C₃ n) x)
    (hbudget : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ε₁ n γ + phase2Error n + phase3Error C₃ n γ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) :
    Theorem1b_statement := by
  apply theorem1b_of_fewer C₁ C₃ n₀ c ε₁ hc hn₀ hphase1
  · intro n γ hn hγ hsize
    exact phase2_bridge_of_arithmetic n (hn₀.trans hn)
      (hphase2Certificates n γ hn hγ hsize)
  · intro n γ hn hγ hsize
    exact phase3Bridge_of_escapeSlack C₃ n γ (hn₀.trans hn) hsize
      (fun x hx => hescape n γ x hn hγ hsize hx)
  · exact hbudget

#print axioms phase2_bridge_of_arithmetic
#print axioms theorem1b_of_available_components

end Tri
