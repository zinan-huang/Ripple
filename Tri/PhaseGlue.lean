/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BandReturn
import Tri.DirectionProgress
import Tri.Phase2CRN
import Tri.Phase3CRN

/-!
# Wiring the proved phase components into Theorem 1(b)

This module specializes the five abstract inputs of `theorem1b_of_phases` to
the horizons and errors now exposed by the phase files.  It discharges the
schedule completely and replaces the three opaque phase hypotheses by the
specific stopped-chain bridges that the current lemma stock actually needs.

The chosen horizons are

* phase 1: `C₁ * γ * n * lg n`;
* phase 2: `lg n * (4 * n)`;
* phase 3: `C₃ * n * lg n`.

Thus the headline constant is `C₁ + 4 + C₃`.  The assumption `1 ≤ γ` makes the
last two horizons fit under their `γ`-scaled shares, and `hschedule_proved`
constructs the padding duration.

## Final residuals of `theorem1b_of_fewer`

* `hn₀`, `hc` -- **(i), arithmetic-only witness conditions** already present
  in the headline existential statement.
* `hphase1` -- **(ii), needs a phase-1 band-direction lemma.**  Its residual is
  `Phase1BandBridge.hband`: for each admissible initial state, prove the upper
  threshold on `bandCount`.  `Reaches.of_bandCount_upper`, its return error,
  and preservation of the physical range are discharged here.  This is where
  `band_rung_bound` and a true direction tail must eventually be composed.
* `hphase2` -- **(ii), needs the stopped-recurrence bridge represented by
  `Phase2Bridge`**.  `phase2_reaches`, the complete dyadic ladder, and its final
  threshold arithmetic are discharged here.
* `hphase3` -- **(ii), needs the stopped-recurrence/escape bridge represented by
  `Phase3Bridge`**.  The wrapper calls `phase3_reaches` directly.
* `hbudget` -- **(i), arithmetic/analysis only.**  It is now the explicit sum
  of the phase-1 error, the finite phase-2 stage-error sum, and the phase-3
  corrected-potential error.

No residual is classified **(iii), looks false**.  In particular, neither
`phase1_uniform_productive_false` nor
`phase1_productive_direction_false` is reused or hidden in a bridge.
-/

namespace Tri

open scoped ENNReal

/-- The fixed phase-1 horizon used by the glued theorem. -/
def phase1Horizon (C₁ n γ : ℕ) : ℕ :=
  C₁ * γ * n * Nat.log 2 n

/-- The complete phase-2 ladder uses one block of `4*n` interactions for each
of `lg n` dyadic stages. -/
def phase2Horizon (n : ℕ) : ℕ :=
  Nat.log 2 n * (4 * n)

/-- The single phase-3 absorption block. -/
def phase3Horizon (C₃ n : ℕ) : ℕ :=
  C₃ * n * Nat.log 2 n

/-- The accumulated explicit error of all `lg n` phase-2 stages. -/
noncomputable def phase2Error (n : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (Nat.log 2 n), phase2StageError n (2 + i)

/-- The explicit corrected-potential error produced by `phase3_reaches`. -/
noncomputable def phase3Error (C₃ n γ : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 : ℝ) ^ (γ * Nat.log 2 n) - 1) *
    (1 - ((105 : ℝ) / 128) / (n : ℝ)) ^ phase3Horizon C₃ n)

/-- One Tri step started in the physical range assigns zero mass to every
state above the fixed population. -/
theorem triChain_eq_zero_above (n x z : ℕ) (h3 : 3 ≤ n)
    (hx : x ≤ n) (hz : n < z) :
    triChain n x z = 0 := by
  rcases x.eq_zero_or_pos with rfl | hxpos
  · have hzero : triChain n 0 = PMF.pure 0 := by
      unfold triChain
      rw [dif_pos ⟨h3, by omega⟩]
      exact triStep_consensus_Y n (by omega)
    rw [hzero]
    simp [PMF.pure_apply]
    omega
  · by_cases hxn : x = n
    · subst x
      rw [triChain_consensus h3]
      simp [PMF.pure_apply]
      omega
    · have hxlt : x < n := lt_of_le_of_ne hx hxn
      obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
      obtain ⟨b, hpop⟩ : ∃ b, a + b + 2 = n :=
        ⟨n - a - 2, by omega⟩
      rw [triChain_apply hpop h3]
      exact triStep_eq_zero a (b + 1) (by omega) (by omega) (by omega)
        (by omega)

/-- Every deterministic iterate of `triChain` preserves the physical range
`x ≤ n`. -/
theorem iter_triChain_eq_zero_above (n T x z : ℕ) (h3 : 3 ≤ n)
    (hx : x ≤ n) (hz : n < z) :
    iter (triChain n) T x z = 0 := by
  induction T generalizing x with
  | zero =>
      simp [iter, PMF.pure_apply]
      omega
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply, ENNReal.tsum_eq_zero]
      intro y
      by_cases hy : y ≤ n
      · rw [ih y hy, mul_zero]
      · rw [triChain_eq_zero_above n x y h3 hx (by omega), zero_mul]

/-- An upper-threshold reachability estimate becomes `Phase1Exit` when the
precondition starts in the physical range.  The only apparent mismatch is at
states `z > n`, and `iter_triChain_eq_zero_above` proves that those states have
zero mass. -/
theorem Reaches.phase1Exit_of_upper {n T : ℕ} {P : ℕ → Prop}
    [DecidablePred P] {ε : ℝ≥0∞} (h3 : 3 ≤ n)
    (hphysical : ∀ x, P x → x ≤ n)
    (hupper : Reaches (triChain n) T P (fun z => 5 * n ≤ 6 * z) ε) :
    Reaches (triChain n) T P (Phase1Exit n) ε := by
  intro x hx
  calc
    ∑' z, (if Phase1Exit n z then 0 else iter (triChain n) T x z) ≤
        ∑' z, (if 5 * n ≤ 6 * z then 0 else iter (triChain n) T x z) := by
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hupperZ : 5 * n ≤ 6 * z
      · by_cases hphysicalZ : z ≤ n
        · have hexit : Phase1Exit n z := ⟨hphysicalZ, hupperZ⟩
          simp [hexit, hupperZ]
        · have hzero := iter_triChain_eq_zero_above n T x z h3
            (hphysical x hx) (by omega)
          simp [Phase1Exit, hphysicalZ, hupperZ, hzero]
      · by_cases hexit : Phase1Exit n z <;> simp [hexit, hupperZ]
    _ ≤ ε := hupper x hx

/-- The exact remaining phase-1 datum for one admissible initial state.

The probabilistic field `hband` is the missing band-direction theorem.  Every
other field is arithmetic information needed by `Reaches.of_bandCount_upper`;
the return term is already included in `herror`. -/
structure Phase1BandBridge (n x T : ℕ) (ε : ℝ≥0∞) where
  /-- Lower boundary of the stopped band. -/
  bandLo : ℕ
  /-- Upper success boundary of the stopped band. -/
  aHi : ℕ
  /-- Threshold below which a return counts as phase-1 failure. -/
  returnLo : ℕ
  /-- Complementary population parameter at `returnLo`. -/
  bHi : ℕ
  /-- Distance used in the Feller return estimate. -/
  k : ℕ
  /-- Initial productive-counter value. -/
  c₀ : ℕ
  /-- Failure allowance for the stopped-band estimate. -/
  εband : ℝ≥0∞
  /-- Population decomposition at the return threshold. -/
  hpop : returnLo + bHi + 2 = n
  /-- The return threshold is positive. -/
  hreturnLo : 0 < returnLo
  /-- The complementary population parameter is positive. -/
  hbHi : 0 < bHi
  /-- The return threshold remains on the majority side. -/
  hmaj : bHi ≤ returnLo
  /-- The upper boundary is at least `k` states above the return threshold. -/
  hgap : returnLo + k ≤ aHi
  /-- Every phase-1 upper success lies above the lower stopped boundary. -/
  hlower : ∀ z, 5 * n ≤ 6 * z → bandLo < z
  /-- Failure of the upper threshold lies below `returnLo`. -/
  hfailure : ∀ z, ¬ 5 * n ≤ 6 * z → z ≤ returnLo
  /-- The remaining direction-sensitive stopped-band reachability theorem. -/
  hband : Reaches (bandCount n bandLo aHi) T
    (fun s => s = (x, c₀)) (fun s => 5 * n ≤ 6 * s.1) εband
  /-- The stopped-band and Feller-return errors fit the phase-1 allowance. -/
  herror : εband +
    ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k ≤ ε

/-- The current band lemmas reduce the exact `hphase1` input to a family of
`Phase1BandBridge`s.  In particular, the upper-boundary transfer and the
physical-range conjunct of `Phase1Exit` are no longer residual hypotheses. -/
theorem hphase1_proved_of_band
    (C₁ n₀ : ℕ) (ε₁ : ℕ → ℕ → ℝ≥0∞) (hn₀ : 3 ≤ n₀)
    (hbridges : ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → AssemblyInitial n γ x →
      Phase1BandBridge n x (phase1Horizon C₁ n γ) (ε₁ n γ)) :
    ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (phase1Horizon C₁ n γ)
        (AssemblyInitial n γ) (Phase1Exit n) (ε₁ n γ) := by
  intro n γ hn hγ hsize x hx
  let B := hbridges n γ x hn hγ hsize hx
  have h3 : 3 ≤ n := hn₀.trans hn
  have hupper := Reaches.of_bandCount_upper
    n B.bandLo B.aHi B.returnLo B.bHi B.k (phase1Horizon C₁ n γ)
    x B.c₀ h3 B.hpop B.hreturnLo B.hbHi B.hmaj B.hgap
    (fun z => 5 * n ≤ 6 * z) B.εband B.hlower B.hfailure B.hband
  have hupper' := hupper.mono_error B.herror
  have hexit := hupper'.phase1Exit_of_upper h3 (fun z hz => by
    subst z
    exact hx.1)
  exact hexit x rfl

/-- The stopped-recurrence and escape data still required by the proved
phase-2 ladder. -/
structure Phase2Bridge (n k : ℕ) where
  /-- Stage-indexed corrected moments. -/
  V : ℕ → ℕ → ℕ → ℝ
  /-- Initial moment bound for every dyadic stage. -/
  hV0 : ∀ i < k, ∀ x, Phase2Stage n (2 + i) x →
    V i x 0 ≤ (2 : ℝ) ^ (n / 2 ^ (2 + i))
  /-- Global stopped recurrence for every dyadic stage. -/
  hVstep : ∀ i < k, ∀ x, Phase2Stage n (2 + i) x →
    Phase2Guard n x → ∀ t,
      V i x (t + 1) ≤ phase2Decay (2 + i) * V i x t
  /-- Markov/escape conversion for every dyadic stage. -/
  hfail : ∀ i < k, ∀ x, Phase2Stage n (2 + i) x →
    ∑' z, (if Phase2Stage n (2 + i + 1) z then 0
      else iter (triChain n) (4 * n) x z) ≤
        ENNReal.ofReal (V i x (4 * n) /
          (2 : ℝ) ^ (n / 2 ^ (2 + i + 1) + 1))

/-- Choosing `k = lg n` makes the final dyadic minority threshold zero, hence
at most `γ * lg n`. -/
theorem phase2_log_threshold (n γ : ℕ) :
    n / 2 ^ (2 + Nat.log 2 n) ≤ γ * Nat.log 2 n := by
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hpow : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ (2 + Nat.log 2 n) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
  have hzero : n / 2 ^ (2 + Nat.log 2 n) = 0 :=
    Nat.div_eq_of_lt (hlt.trans_le hpow)
  rw [hzero]
  exact Nat.zero_le _

/-- `phase2_reaches` discharges the exact `hphase2` input once its single
`Phase2Bridge` family is supplied.  The stage count and final threshold are no
longer residuals. -/
theorem hphase2_proved
    (n₀ : ℕ)
    (hbridges : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase2Bridge n (Nat.log 2 n)) :
    ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (phase2Horizon n) (Phase1Exit n) (Phase2Exit n γ)
        (phase2Error n) := by
  intro n γ hn hγ hsize
  let B := hbridges n γ hn hγ hsize
  simpa [phase2Horizon, phase2Error] using
    phase2_reaches n γ (Nat.log 2 n) B.V B.hV0 B.hVstep B.hfail
      (phase2_log_threshold n γ)

/-- The stopped-recurrence and failure-conversion data still required by the
proved phase-3 endgame. -/
structure Phase3Bridge (C₃ n γ : ℕ) where
  /-- Corrected potential after each phase-3 interaction. -/
  V : ℕ → ℕ → ℝ
  /-- Initial corrected-potential bound on `Phase2Exit`. -/
  hV0 : ∀ x, Phase2Exit n γ x →
    V x 0 ≤ (2 : ℝ) ^ (γ * Nat.log 2 n) - 1
  /-- Uniform global recurrence for the corrected potential. -/
  hVstep : ∀ x, Phase2Exit n γ x → ∀ t,
    V x (t + 1) ≤
      (1 - ((105 : ℝ) / 128) / (n : ℝ)) * V x t
  /-- Conversion from the corrected potential to actual terminal failure. -/
  hfail : ∀ x, Phase2Exit n γ x →
    ∑' z, (if IsXMajority n z then 0
      else iter (triChain n) (phase3Horizon C₃ n) x z) ≤
        ENNReal.ofReal (V x (phase3Horizon C₃ n))

/-- `phase3_reaches` discharges the exact `hphase3` input once the specific
stopped-recurrence/escape bridge is supplied. -/
theorem hphase3_proved
    (C₃ n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (hbridges : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase3Bridge C₃ n γ) :
    ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (phase3Horizon C₃ n) (Phase2Exit n γ)
        (IsXMajority n) (phase3Error C₃ n γ) := by
  intro n γ hn hγ hsize
  let B := hbridges n γ hn hγ hsize
  have h3 : 3 ≤ n := hn₀.trans hn
  simpa [phase3Horizon, phase3Error] using
    phase3_reaches C₃ n γ h3 B.V B.hV0 B.hVstep B.hfail

/-- The selected phase horizons always fit the headline horizon with constant
`C₁ + 4 + C₃`; the unused time is supplied by an explicit additive witness. -/
theorem hschedule_proved (C₁ C₃ : ℕ) :
    ∀ n γ : ℕ, 1 ≤ γ →
      ∃ U : ℕ,
        phase1Horizon C₁ n γ + phase2Horizon n + phase3Horizon C₃ n + U =
          (C₁ + 4 + C₃) * γ * n * Nat.log 2 n := by
  intro n γ hγ
  have hscale : n * Nat.log 2 n ≤ γ * (n * Nat.log 2 n) := by
    calc
      n * Nat.log 2 n = 1 * (n * Nat.log 2 n) := by simp
      _ ≤ γ * (n * Nat.log 2 n) := Nat.mul_le_mul_right _ hγ
  have hle :
      phase1Horizon C₁ n γ + phase2Horizon n + phase3Horizon C₃ n ≤
        (C₁ + 4 + C₃) * γ * n * Nat.log 2 n := by
    calc
      phase1Horizon C₁ n γ + phase2Horizon n + phase3Horizon C₃ n =
          C₁ * γ * n * Nat.log 2 n + (4 + C₃) * (n * Nat.log 2 n) := by
            simp only [phase1Horizon, phase2Horizon, phase3Horizon]
            ring
      _ ≤ C₁ * γ * n * Nat.log 2 n +
          (4 + C₃) * (γ * (n * Nat.log 2 n)) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left (4 + C₃) hscale) _
      _ = (C₁ + 4 + C₃) * γ * n * Nat.log 2 n := by ring
  exact Nat.le.dest hle

/-- Once the phase errors are fixed to the explicit functions above, the
generic `hbudget` input is exactly this one scalar inequality.  No
probabilistic premise remains hidden in it. -/
theorem hbudget_proved_of_explicit
    (C₃ n₀ : ℕ) (c : ℝ) (ε₁ : ℕ → ℕ → ℝ≥0∞)
    (hbudget : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ε₁ n γ + phase2Error n + phase3Error C₃ n γ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) :
    ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ε₁ n γ + phase2Error n + phase3Error C₃ n γ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ)) :=
  hbudget

/-- **Theorem 1(b) from the genuinely remaining bridges.**

Compared with `theorem1b_of_phases`, the schedule is proved, the phase-2 and
phase-3 horizons/errors are fixed to their proved lemmas, and phase 1 carries
only a stopped-band direction bridge rather than an original-chain transfer.
The remaining `hbudget` is an explicit scalar inequality. -/
theorem theorem1b_of_fewer
    (C₁ C₃ n₀ : ℕ) (c : ℝ) (ε₁ : ℕ → ℕ → ℝ≥0∞)
    (hc : 0 < c) (hn₀ : 3 ≤ n₀)
    (hphase1 : ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → AssemblyInitial n γ x →
      Phase1BandBridge n x (phase1Horizon C₁ n γ) (ε₁ n γ))
    (hphase2 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase2Bridge n (Nat.log 2 n))
    (hphase3 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase3Bridge C₃ n γ)
    (hbudget : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ε₁ n γ + phase2Error n + phase3Error C₃ n γ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) :
    Theorem1b_statement := by
  exact theorem1b_of_phases
    (C₁ + 4 + C₃) n₀ c
    (phase1Horizon C₁) (fun n _γ => phase2Horizon n)
      (fun n _γ => phase3Horizon C₃ n)
    ε₁ (fun n _γ => phase2Error n) (phase3Error C₃)
    (by omega) hc hn₀
    (hphase1_proved_of_band C₁ n₀ ε₁ hn₀ hphase1)
    (hphase2_proved n₀ hphase2)
    (hphase3_proved C₃ n₀ hn₀ hphase3)
    (fun n γ _hn hγ _hsize => hschedule_proved C₁ C₃ n γ hγ)
    (hbudget_proved_of_explicit C₃ n₀ c ε₁ hbudget)

end Tri
