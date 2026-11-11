import Tri.PaperLemma13
import Tri.PaperLemma12StateDependent
import Tri.Theorem1a
import Tri.Theorem4Entry
import Tri.PaperLemma10
import Tri.PaperLemma6

/-!
# Explicit and stronger forms of the Tri paper results

The declarations below expose stronger forms that the proved ingredients
already give.

[P] Condon, Hajiaghayi, Kirkpatrick, and Maňuch,
"Approximate majority analyses using tri-molecular chemical reaction networks",
Natural Computing 19 (2020), 249–270.

Raw interactions and productive slots are kept distinct. The Byzantine
Theorem 4 statement below is the corrected entry clause.
-/

namespace Tri

open scoped ENNReal NNReal

noncomputable section

namespace Multi

/-- **[P], Lemma 13, with the stronger raw-clock error.**
At the same raw deadline, the probability that the productive counter is at
most `288 * n` and the stopped phase is still live is at most `exp (-n)`.

The original confidence-scale and species premises are used only through
their consequence `6 * m ≤ n`; no confidence parameter is needed here.
This is the clock-failure event, not a claim that every boundary exit is
successful stage completion. -/
theorem lemma13_phase0_rawDeadline_exp_n
    {m n : ℕ}
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD : 3 * D ≤ n)
    (hnm : 6 * m ≤ n)
    (c0 : Config m n)
    (hmax : IsMaxSpecies c0 X)
    (hphase0 : count c0 X ≤ zSum c0 X + D) :
    (∑' q, if q.2 ≤ 288 * n ∧
          ¬ PaperPhase0ClockBoundary X D q then
        iter (multiPaperPhase0ClockStop h3 X D)
          (129472 * m * n) (c0, 0) q
      else 0) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
  have hq0 :
      ¬ PaperPhase0ClockBoundary X D (c0, 0) := by
    simp only [PaperPhase0ClockBoundary, not_not]
    exact ⟨hmax, hphase0⟩
  have hclock :=
    multiPaperPhase0ClockStop_productivity_deadline
      h3 X D hD hnm (288 * n) n (c0, 0) hq0 rfl
  have hHorizon :
      multiPaperPhase0ClockHorizon m (288 * n) n =
        129472 * m * n := by
    simp only [multiPaperPhase0ClockHorizon, multiPhase0ClockHorizon]
    ring
  rw [hHorizon] at hclock
  exact hclock

end Multi


namespace Multi

/-- **[P], Lemma 12, with the stronger capped quadrupling target.**
Under exactly the hypotheses of `lemma12`, the productive chain reaches
`HasPairwiseGap c X (min (4 * Δ) n)` within the same `288 * n`
productive slots and with the same `432 * exp (-g / 663552)` error,
where `g = gamma * Nat.log 2 n`.

This exposes the internal checkpoint without the public wrapper's
target-weakening step. -/
theorem lemma12_gap_min_four
    {m n : ℕ}
    (h3 : 3 ≤ n) (X : Species m) (Δ gamma : ℕ)
    (hgLarge :
      properStageSizeThreshold ≤ gamma * Nat.log 2 n)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (hscale : gamma * n * Nat.log 2 n ≤ Δ ^ 2)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    let A : Config m n → Prop :=
      fun c => HasPairwiseGap c X (min (4 * Δ) n)
    terminalFailureMass
        (iter (freeze A (productiveStep h3)) (288 * n) c0) A ≤
      (432 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(((gamma * Nat.log 2 n : ℕ) : ℝ) /
              properStageExponentDenominator))) := by
  have hscale' :
      (gamma * Nat.log 2 n) * n ≤ Δ ^ 2 := by
    calc
      (gamma * Nat.log 2 n) * n =
          gamma * n * Nat.log 2 n := by ring
      _ ≤ Δ ^ 2 := hscale
  have hhit :=
    productiveStep_properAmplification_hitting_stateDependent
      h3 X (gamma * Nat.log 2 n) Δ hgLarge hΔ4 hm
      hscale' hΔn c0 hinit
  dsimp only at hhit ⊢
  rw [productiveAmplificationBlockError_144] at hhit
  exact hhit

end Multi

set_option exponentiation.threshold 500 in
/-- **[P], Theorem 1(b), with the proved explicit constants.**
For `n ≥ 2^420`, confidence `γ ≥ 1`, and `6 * γ * Nat.log 2 n ≤ n`,
the majority-gap initial predicate reaches all-X consensus within
`48 * γ * n * Nat.log 2 n` raw interactions, with failure mass at most
`(n⁻¹)^(γ/100)`.

The source definition `phase0Error n γ` uses exponent
`(1 / 100 : ℝ) * (γ : ℝ)`; the proof below rewrites that exact exponent
as `(γ : ℝ) / 100`. -/
theorem theorem1b_explicit
    (n γ : ℕ)
    (hn : 2 ^ 420 ≤ n)
    (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (triChain n) (48 * γ * n * Nat.log 2 n)
      (AssemblyInitial n γ) (IsXMajority n)
      ((n : ℝ≥0∞)⁻¹ ^ ((γ : ℝ) / 100)) := by
  have hexponent :
      (1 / 100 : ℝ) * (γ : ℝ) = (γ : ℝ) / 100 := by
    ring
  simpa only [phase0Error, hexponent] using
    (phase123_reaches_X n γ hn hγ hsize)

namespace Byzantine

set_option exponentiation.threshold 1100 in
/-- **[P], corrected Theorem 4 entry clause, with explicit constants.**
Under the original initial-state and strategy hypotheses, the
reached-by-deadline failure probability is at most `n^(-γ/136)` at the
raw-interaction deadline determined by `theorem4Phase2Scalars`.

The single non-strict guard `68 * γ * Nat.log 2 n ≤ 3 * n` implies the
separate `6γL ≤ n` guard used in error compression. No strict population
guard is needed. This theorem asserts entry into relaxed consensus. -/
theorem theorem4_entry_weak_guard
    (n γ : ℕ)
    (hn : 2 ^ 1000 ≤ n)
    (hγ : 1 ≤ γ)
    (hweak : 68 * γ * Nat.log 2 n ≤ 3 * n)
    (x₀ y₀ B d : ℕ)
    (hinit : Theorem4PaperInitial n γ x₀ y₀ B d)
    (σ : Strategy n B) :
    theorem4EntryHittingFailureMass σ
        ((40 + 12288 * theorem4Phase2Scalars.C *
            theorem4Phase2Scalars.R₀) *
          γ * n * Nat.log 2 n)
        []
        (theorem4InitialState n x₀ y₀ B hinit.1) ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 136 : ℝ) * (γ : ℝ)) := by
  let S := theorem4Phase2Scalars
  let C := 40 + 12288 * S.C * S.R₀
  let g := γ * Nat.log 2 n
  let s₀ := theorem4InitialState n x₀ y₀ B hinit.1
  let T :=
    phase1RawDyadicLadderHorizon n (Nat.log 2 n) +
      phase2BufferedLadderHorizon S g n
        (phase2BufferedStageCount n)
  have h3 : 3 ≤ n := by
    exact three_le_two_pow_1000.trans hn
  have hlog : 1000 ≤ Nat.log 2 n := by
    exact Nat.le_log_of_pow_le (by decide) hn
  have hg : 1 ≤ g := by
    dsimp only [g]
    have hL : 1 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
    nlinarith
  have hlarge : 68 * g ≤ 3 * n := by
    simpa only [g, Nat.mul_assoc] using hweak
  have hguard : 6 * γ * Nat.log 2 n ≤ n := by
    have hsmall : 6 * g ≤ n := by omega
    simpa only [g, Nat.mul_assoc] using hsmall
  have hlogle : Nat.log 2 n ≤ g := by
    dsimp only [g]
    nlinarith
  have hT :
      T ≤ C * γ * n * Nat.log 2 n := by
    have hbound :=
      phase12Horizon_le_linear S hg hlarge hlogle
    dsimp only [T, C, g] at *
    calc
      phase1RawDyadicLadderHorizon n (Nat.log 2 n) +
            phase2BufferedLadderHorizon S
              (γ * Nat.log 2 n) n
              (phase2BufferedStageCount n) ≤
          (40 + 12288 * S.C * S.R₀) *
            (γ * Nat.log 2 n) * n :=
        hbound
      _ = (40 + 12288 * S.C * S.R₀) *
          γ * n * Nat.log 2 n := by ring
  have hfinite :=
    theorem4EntryHittingFailureMass_le_finite
      (n := n) (B := B)
      σ h3 S γ g x₀ y₀ d hg hlarge hinit
  have herror :=
    phase12Error_le_inv_rpow S n γ d hn hγ hguard
      hlarge hinit.2.2.1
  change
    theorem4EntryHittingFailureMass σ
        (C * γ * n * Nat.log 2 n) [] s₀ ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 136 : ℝ) * (γ : ℝ))
  calc
    theorem4EntryHittingFailureMass σ
          (C * γ * n * Nat.log 2 n) [] s₀ ≤
        theorem4EntryHittingFailureMass σ T [] s₀ := by
      rw [theorem4EntryHittingFailureMass_eq_joint σ h3,
        theorem4EntryHittingFailureMass_eq_joint σ h3]
      exact
        terminalFailureMass_iter_freeze_antitone_of_subset
          (fun q : ControlledJointState n B =>
            RelaxedXConsensus q.2)
          (fun q : ControlledJointState n B =>
            RelaxedXConsensus q.2)
          (controlledJointStep σ h3)
          (fun _ h => h) T (C * γ * n * Nat.log 2 n)
          hT ([], s₀)
    _ ≤ phase1RawDyadicLadderError n d (Nat.log 2 n) +
          phase2BufferedLadderError S g n
            (phase2BufferedStageCount n) :=
      hfinite
    _ ≤ (n : ℝ≥0∞)⁻¹ ^
          ((1 / 136 : ℝ) * (γ : ℝ)) :=
      herror

/-- **[P], Lemma 10, with count-based and non-strict population guards.**
This is the division-free effective-rate comparison from
`lemma10_effectiveRate_cross`. The premise `4 * (y + z) ≤ n`
replaces the integral-ratio premises; `68 * g ≤ 3 * n` replaces their
strict population guard. All remaining local hypotheses are retained.

The final inequality is strict because `x + 2 * z < n` and population
conservation imply `z < y`, hence `y + z < 2 * y`. -/
theorem lemma10_effectiveRate_cross_weak_guard
    {n B : ℕ} {s : State n B} {g den : ℕ}
    (hx : State.x s + 2 * State.z s < n)
    (hshare : 4 * (State.y s + State.z s) ≤ n)
    (hden : State.y s + State.z s + g + den = n)
    (hlarge : 68 * g ≤ 3 * n) :
    6 * (State.y s + State.z s + g) *
        (State.y s + State.z s) <
      5 * den * State.y s := by
  have htotal := State.total s
  have hyz : State.z s < State.y s := by
    omega
  have hy : 0 < State.y s := by
    omega
  have hscalar :
      12 * (State.y s + State.z s + g) ≤ 5 * den := by
    omega
  have hcoef :
      0 < 6 * (State.y s + State.z s + g) := by
    omega
  have hpair :
      State.y s + State.z s < 2 * State.y s := by
    omega
  calc
    6 * (State.y s + State.z s + g) *
          (State.y s + State.z s) <
        6 * (State.y s + State.z s + g) *
          (2 * State.y s) :=
      (Nat.mul_lt_mul_left hcoef).2 hpair
    _ = (12 * (State.y s + State.z s + g)) *
          State.y s := by ring
    _ ≤ (5 * den) * State.y s :=
      Nat.mul_le_mul_right _ hscalar
    _ = 5 * den * State.y s := by ring

end Byzantine

/-- **[P], Theorem 1(a), with the proved explicit constants.**
For `n ≥ 2^420`, confidence `γ ≥ 1`, `6 * γ * Nat.log 2 n ≤ n` and any
start `x₀ ≤ n`, the mass not in consensus after `258 * γ * n * Nat.log 2 n`
raw interactions is at most `(n⁻¹)^(γ/200)`. The deadline is the phase-0
witness `210` plus the phase-1--3 budget `48`. -/
theorem theorem1a_explicit
    (n γ x₀ : ℕ)
    (hn : 2 ^ 420 ≤ n)
    (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hx₀ : x₀ ≤ n) :
    ∑' z, (if IsConsensus n z then 0
      else iter (triChain n) (258 * γ * n * Nat.log 2 n) x₀ z)
        ≤ (n : ℝ≥0∞)⁻¹ ^ ((γ : ℝ) / 200) := by
  have hexponent :
      (1 / 200 : ℝ) * (γ : ℝ) = (γ : ℝ) / 200 := by
    ring
  have h := theorem1a_bound_of_phase0 210 phase0Hyp_210 n γ x₀ hn hγ hsize hx₀
  rw [hexponent] at h
  simpa only [show (210 + 48 : ℕ) = 258 from rfl] using h

/-- **[P], Lemma 6, with both error terms kept.**
Same fixed-rate, target-frozen productive chain and deadline `5 n` as
`lemma6_paper`; the failure mass is at most
`exp(-Δ²/(8n+4Δ)) + exp(-Δ²/(80n+16Δ))` instead of `2 exp(-Δ²/(96n))`. -/
theorem lemma6_paper_two_term
    (r : RelaxedRate) (n x₀ y₀ Δ : ℕ)
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (((Δ : ℕ) : NNReal) /
          (((2 * n : ℕ) : NNReal)))) :
    terminalFailureMass
        (iter
          (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n))
          (5 * n) x₀)
        (Lemma3Target n Δ) ≤
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (8 * (n : ℝ) + 4 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (80 * (n : ℝ) + 16 * (Δ : ℝ))))) := by
  have hfire := lemma6_fire_pos hΔ0 hΔn hrate
  have hprojection :=
    targetFreeze_failure_le_lazy_projection
      (Lemma3Target n Δ)
      (relaxedProductiveTriChain r n)
      (lemma6TraceStep r n x₀ Δ)
      Lemma3Trace.toX
      (lemma6TraceStep_isLazyProjection r n x₀ Δ)
      (5 * n) (lemma3Initial x₀)
  calc
    terminalFailureMass
        (iter
          (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n))
          (5 * n) x₀)
        (Lemma3Target n Δ) ≤
      terminalFailureMass
          (iter (lemma6TraceStep r n x₀ Δ) (5 * n)
            (lemma3Initial x₀))
          (fun z => Lemma3Target n Δ z.x) := by
      simpa [Lemma3Trace.toX, lemma3Initial] using hprojection
    _ ≤ _ := lemma6Trace_failure_explicit hpop hgap hΔ0 hΔn hfire hrate

end

end Tri
