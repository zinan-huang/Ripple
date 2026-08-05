/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase2Contract
import Tri.Phase2Reconciled

/-!
# The buffered phase-2 stopped moment

This module constructs the killed base-two moment for one phase-2 rung and
proves its initial bound and global stopped-chain recurrence.  Markov's
inequality controls the mass which remains in `Phase2Live` at the end of the
block.

The stopped moment cannot itself fill `Phase2Bridge.hfail`.  Freezing outside
`Phase2Live` kills lower-guard exits, while the original chain can recover from
them; freezing a successful state also suppresses later returns.  The theorem
`phase2_stopped_one_step_conversion_false` gives a closed buffered-rung
counterexample to the proposed Markov conversion.

Accordingly the final construction uses the deterministic geometric envelope
already forced by `hV0` and `hVstep`.  Its one precisely named residual,
`Phase2BufferedOriginalChainBound`, is the original-chain exact-time estimate
which is not supplied by the stopped contraction.  No recurrence or initial
moment claim is carried.
-/

namespace Tri

open scoped ENNReal

/-- The base-two minority potential, defined without natural subtraction.
States outside the physical population range receive value zero. -/
noncomputable def phase2PhysicalPotential (n x : ℕ) : ℝ≥0∞ :=
  ∑' y : ℕ, if x + y = n then (2 : ℝ≥0∞) ^ y else 0

/-- Evaluation of the physical phase-2 potential at a population
decomposition. -/
theorem phase2PhysicalPotential_apply {n x y : ℕ} (hxy : x + y = n) :
    phase2PhysicalPotential n x = (2 : ℝ≥0∞) ^ y := by
  unfold phase2PhysicalPotential
  rw [tsum_eq_single y]
  · simp [hxy]
  · intro z hz
    rw [if_neg]
    intro hxz
    omega

/-- The phase-2 chain stopped on leaving the two-sided live region. -/
noncomputable def phase2Stop (n s : ℕ) : ℕ → PMF ℕ :=
  freeze (fun x => ¬ Phase2Live n s x) (triChain n)

/-- The killed base-two potential: it agrees with the physical potential on
the live region and vanishes at every frozen state. -/
noncomputable def phase2StoppedPotential (n s x : ℕ) : ℝ≥0∞ :=
  if Phase2Live n s x then phase2PhysicalPotential n x else 0

/-- In the live region the killed potential is the physical base-two
potential. -/
theorem phase2StoppedPotential_of_mem {n s x : ℕ}
    (hx : Phase2Live n s x) :
    phase2StoppedPotential n s x = phase2PhysicalPotential n x := by
  simp [phase2StoppedPotential, hx]

/-- Outside the live region the killed potential is zero. -/
theorem phase2StoppedPotential_of_not_mem {n s x : ℕ}
    (hx : ¬ Phase2Live n s x) :
    phase2StoppedPotential n s x = 0 := by
  simp [phase2StoppedPotential, hx]

/-- Killing outside the live region can only decrease the physical
potential. -/
theorem phase2StoppedPotential_le (n s x : ℕ) :
    phase2StoppedPotential n s x ≤ phase2PhysicalPotential n x := by
  by_cases hx : Phase2Live n s x
  · rw [phase2StoppedPotential_of_mem hx]
  · rw [phase2StoppedPotential_of_not_mem hx]
    exact bot_le

/-- A live phase-2 state has an interior successor-coordinate population
decomposition. -/
theorem phase2Live_successors {n s x : ℕ} (h3 : 3 ≤ n)
    (hx : Phase2Live n s x) :
    ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n := by
  have hxphysical : x ≤ n := hx.1.1
  have hxpos : 0 < x := by
    have hxguard := hx.1
    unfold Phase2Guard at hxguard
    omega
  have hxlt : x < n := by
    apply lt_of_le_of_ne hxphysical
    intro hxn
    apply hx.2
    subst x
    constructor
    · exact le_rfl
    · omega
  obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, a + b + 2 = n :=
    ⟨n - a - 2, by omega⟩
  exact ⟨a, b, rfl, hb⟩

/-- The killed phase-2 potential contracts in one step at every state of the
stopped chain.  Live states use `phase2_hcontract_of_live`; frozen states have
zero killed potential. -/
theorem phase2Stop_step (n s : ℕ) (h3 : 3 ≤ n) :
    ∀ x, expect (phase2Stop n s x) (phase2StoppedPotential n s) ≤
      phase2DecayENN s * phase2StoppedPotential n s x := by
  intro x
  by_cases hx : Phase2Live n s x
  · rw [phase2Stop, freeze_of_not_mem x (by simpa using hx),
      phase2StoppedPotential_of_mem hx]
    obtain ⟨a, b, rfl, hpop⟩ := phase2Live_successors h3 hx
    have hcontract := phase2_hcontract_of_live a b n s (by omega) hpop hx
    calc
      expect (triChain n (a + 1)) (phase2StoppedPotential n s) ≤
          expect (triChain n (a + 1)) (phase2PhysicalPotential n) := by
        unfold expect
        exact ENNReal.tsum_le_tsum fun z =>
          mul_le_mul_right (phase2StoppedPotential_le n s z) _
      _ = (2 : ℝ≥0∞) ^ (b + 2) *
          (triStep (a + 1) (b + 1) (by omega) a +
            triStep (a + 1) (b + 1) (by omega) (a + 1) *
              ((1 : ℝ≥0∞) / 2) +
            triStep (a + 1) (b + 1) (by omega) (a + 2) *
              ((1 : ℝ≥0∞) / 2) ^ 2) := by
        have hhalf : ((1 : ℝ≥0∞) / 2) * 2 = 1 := by
          rw [div_eq_mul_inv, one_mul]
          exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        have hweighted (p₀ p₁ p₂ : ℝ≥0∞) :
            p₀ * (2 : ℝ≥0∞) ^ (b + 2) +
                p₁ * (2 : ℝ≥0∞) ^ (b + 1) +
                p₂ * (2 : ℝ≥0∞) ^ b =
              (2 : ℝ≥0∞) ^ (b + 2) *
                (p₀ + p₁ * ((1 : ℝ≥0∞) / 2) +
                  p₂ * ((1 : ℝ≥0∞) / 2) ^ 2) := by
          have h₁ : p₁ * (2 : ℝ≥0∞) ^ (b + 1) =
              (2 : ℝ≥0∞) ^ (b + 2) *
                (p₁ * ((1 : ℝ≥0∞) / 2)) := by
            rw [show b + 2 = (b + 1) + 1 by omega, pow_succ]
            calc
              p₁ * (2 : ℝ≥0∞) ^ (b + 1) =
                  p₁ * 2 ^ (b + 1) * (((1 : ℝ≥0∞) / 2) * 2) := by
                    rw [hhalf]
                    ring
              _ = _ := by ring
          have h₂ : p₂ * (2 : ℝ≥0∞) ^ b =
              (2 : ℝ≥0∞) ^ (b + 2) *
                (p₂ * ((1 : ℝ≥0∞) / 2) ^ 2) := by
            rw [show b + 2 = b + 1 + 1 by omega, pow_succ, pow_succ]
            calc
              p₂ * (2 : ℝ≥0∞) ^ b =
                  p₂ * 2 ^ b *
                    ((((1 : ℝ≥0∞) / 2) * 2) *
                      (((1 : ℝ≥0∞) / 2) * 2)) := by
                        rw [hhalf]
                        ring
              _ = _ := by rw [pow_two]; ring
          rw [h₁, h₂]
          ring
        rw [triChain_apply hpop h3, expect_triStep,
          phase2PhysicalPotential_apply
            (show a + (b + 2) = n by omega),
          phase2PhysicalPotential_apply
            (show a + 1 + (b + 1) = n by omega),
          phase2PhysicalPotential_apply
            (show a + 2 + b = n by omega)]
        exact hweighted _ _ _
      _ ≤ (2 : ℝ≥0∞) ^ (b + 2) *
          (phase2DecayENN s * ((1 : ℝ≥0∞) / 2)) :=
        mul_le_mul_right hcontract _
      _ = phase2DecayENN s * (2 : ℝ≥0∞) ^ (b + 1) := by
        have hhalf : ((1 : ℝ≥0∞) / 2) * 2 = 1 := by
          rw [div_eq_mul_inv, one_mul]
          exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        rw [show b + 2 = (b + 1) + 1 by omega, pow_succ]
        calc
          (2 : ℝ≥0∞) ^ (b + 1) * 2 *
                (phase2DecayENN s * ((1 : ℝ≥0∞) / 2)) =
              phase2DecayENN s * 2 ^ (b + 1) *
                (((1 : ℝ≥0∞) / 2) * 2) := by ring
          _ = _ := by rw [hhalf]; ring
      _ = phase2DecayENN s * phase2PhysicalPotential n (a + 1) := by
        rw [phase2PhysicalPotential_apply
          (show a + 1 + (b + 1) = n by omega)]
  · rw [phase2Stop, freeze_of_mem x hx, expect_pure,
      phase2StoppedPotential_of_not_mem hx]
    simp

/-- Iterating the stopped one-step contraction gives geometric decay at every
finite horizon. -/
theorem phase2Stop_expect_iter_le (n s T x : ℕ) (h3 : 3 ≤ n) :
    expect (iter (phase2Stop n s) T x) (phase2StoppedPotential n s) ≤
      phase2DecayENN s ^ T * phase2StoppedPotential n s x := by
  exact expect_iter_le (phase2Stop n s) (phase2StoppedPotential n s)
    (phase2DecayENN s) (phase2Stop_step n s h3) T x

/-- The physical base-two potential is finite at every state. -/
theorem phase2PhysicalPotential_ne_top (n x : ℕ) :
    phase2PhysicalPotential n x ≠ ⊤ := by
  by_cases hx : x ≤ n
  · obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hx
    rw [phase2PhysicalPotential_apply hy.symm]
    exact ENNReal.pow_ne_top (by norm_num)
  · have hzero : phase2PhysicalPotential n x = 0 := by
      unfold phase2PhysicalPotential
      apply ENNReal.tsum_eq_zero.mpr
      intro y
      simp only [ite_eq_right_iff]
      intro hxy
      omega
    rw [hzero]
    exact ENNReal.zero_ne_top

/-- The killed phase-2 potential is finite at every state. -/
theorem phase2StoppedPotential_ne_top (n s x : ℕ) :
    phase2StoppedPotential n s x ≠ ⊤ := by
  exact ne_top_of_le_ne_top (phase2PhysicalPotential_ne_top n x)
    (phase2StoppedPotential_le n s x)

/-- Every stopped phase-2 expectation is finite. -/
theorem phase2Stop_expect_ne_top (n s T x : ℕ) (h3 : 3 ≤ n) :
    expect (iter (phase2Stop n s) T x) (phase2StoppedPotential n s) ≠ ⊤ := by
  have hbound := phase2Stop_expect_iter_le n s T x h3
  have hright : phase2DecayENN s ^ T *
      phase2StoppedPotential n s x ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (phase2StoppedPotential_ne_top n s x)
  exact ne_top_of_le_ne_top hright hbound

/-- The real killed moment after `T` stopped interactions. -/
noncomputable def phase2StoppedMoment (n s x T : ℕ) : ℝ :=
  ENNReal.toReal
    (expect (iter (phase2Stop n s) T x) (phase2StoppedPotential n s))

/-- The stopped real moment contracts from time `T` to time `T+1`. -/
theorem phase2StoppedMoment_step (n s x T : ℕ) (h3 : 3 ≤ n) :
    phase2StoppedMoment n s x (T + 1) ≤
      phase2Decay s * phase2StoppedMoment n s x T := by
  have hstep :
      expect (iter (phase2Stop n s) (T + 1) x)
          (phase2StoppedPotential n s) ≤
        phase2DecayENN s *
          expect (iter (phase2Stop n s) T x)
            (phase2StoppedPotential n s) := by
    rw [iter_succ', expect_bind]
    calc
      ∑' a, iter (phase2Stop n s) T x a *
            expect (phase2Stop n s a) (phase2StoppedPotential n s) ≤
          ∑' a, iter (phase2Stop n s) T x a *
            (phase2DecayENN s * phase2StoppedPotential n s a) :=
        ENNReal.tsum_le_tsum fun a =>
          mul_le_mul_right (phase2Stop_step n s h3 a) _
      _ = phase2DecayENN s *
          ∑' a, iter (phase2Stop n s) T x a *
            phase2StoppedPotential n s a := by
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext a
        ring
  have hright : phase2DecayENN s *
      expect (iter (phase2Stop n s) T x) (phase2StoppedPotential n s) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (phase2Stop_expect_ne_top n s T x h3)
  have hreal := ENNReal.toReal_mono hright hstep
  simpa only [phase2StoppedMoment, ENNReal.toReal_mul, phase2DecayENN,
    ENNReal.toReal_ofReal (phase2Decay_nonneg s)] using hreal

/-- At time zero, the stopped moment of a stage state is bounded by its dyadic
minority checkpoint. -/
theorem phase2StoppedMoment_zero_le (n s x : ℕ) (h3 : 3 ≤ n)
    (hx : Phase2Stage n s x) :
    phase2StoppedMoment n s x 0 ≤ (2 : ℝ) ^ (n / 2 ^ s) := by
  by_cases hlive : Phase2Live n s x
  · obtain ⟨a, b, rfl, hpop⟩ := phase2Live_successors h3 hlive
    have hy := phase2_stage_minority_bound hpop hx
    simp only [phase2StoppedMoment, iter_zero, expect_pure,
      phase2StoppedPotential_of_mem hlive,
      phase2PhysicalPotential_apply
        (show a + 1 + (b + 1) = n by omega),
      ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hy
  · simp only [phase2StoppedMoment, iter_zero, expect_pure,
      phase2StoppedPotential_of_not_mem hlive, ENNReal.toReal_zero]
    positivity

/-- The stopped mass still in the live region at the end of a block. -/
noncomputable def phase2StoppedLiveMass (n s T x : ℕ) : ℝ≥0∞ :=
  ∑' z, if Phase2Live n s z then iter (phase2Stop n s) T x z else 0

/-- The stopped mass frozen below the phase-2 guard without reaching the next
checkpoint. -/
noncomputable def phase2StoppedEscapeMass (n s T x : ℕ) : ℝ≥0∞ :=
  ∑' z, if ¬ Phase2Live n s z ∧ ¬ Phase2Stage n (s + 1) z then
    iter (phase2Stop n s) T x z else 0

/-- The exact extra terminal-failure mass created by running the original
chain instead of the chain frozen outside the live region. -/
noncomputable def phase2TransferExcess (n s T x : ℕ) : ℝ≥0∞ :=
  (∑' z, if Phase2Stage n (s + 1) z then 0 else
      iter (triChain n) T x z) -
    (∑' z, if Phase2Stage n (s + 1) z then 0 else
      iter (phase2Stop n s) T x z)

/-- Stopped failure is the disjoint sum of live mass and lower-guard escape
mass. -/
theorem phase2_stopped_failure_eq_live_add_escape (n s T x : ℕ) :
    (∑' z, if Phase2Stage n (s + 1) z then 0 else
      iter (phase2Stop n s) T x z) =
      phase2StoppedLiveMass n s T x +
        phase2StoppedEscapeMass n s T x := by
  unfold phase2StoppedLiveMass phase2StoppedEscapeMass
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro z
  by_cases hlive : Phase2Live n s z
  · have hfailure : ¬ Phase2Stage n (s + 1) z := hlive.2
    simp [hlive, hfailure]
  · by_cases htarget : Phase2Stage n (s + 1) z
    · simp [hlive, htarget]
    · simp [hlive, htarget]

/-- Actual terminal failure is at most stopped terminal failure plus the exact
transfer excess. -/
theorem phase2_failure_le_stopped_failure_add_excess (n s T x : ℕ) :
    (∑' z, if Phase2Stage n (s + 1) z then 0 else
      iter (triChain n) T x z) ≤
      (∑' z, if Phase2Stage n (s + 1) z then 0 else
        iter (phase2Stop n s) T x z) +
        phase2TransferExcess n s T x := by
  unfold phase2TransferExcess
  exact le_add_tsub

/-- Every live state has base-two potential at least the Markov threshold for
failure of the next dyadic checkpoint. -/
theorem phase2_markov_threshold_le {n s z : ℕ} (h3 : 3 ≤ n)
    (hz : Phase2Live n s z) :
    (2 : ℝ≥0∞) ^ (n / 2 ^ (s + 1) + 1) ≤
      phase2StoppedPotential n s z := by
  obtain ⟨a, b, rfl, hpop⟩ := phase2Live_successors h3 hz
  have hnot := hz.2
  have hminority : n / 2 ^ (s + 1) < b + 1 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (s + 1))).2
    unfold Phase2Stage at hnot
    push Not at hnot
    have := hnot (by omega : a + 1 ≤ n)
    nlinarith
  rw [phase2StoppedPotential_of_mem hz,
    phase2PhysicalPotential_apply
      (show a + 1 + (b + 1) = n by omega)]
  exact pow_le_pow_right' (by norm_num) (by omega)

/-- Markov's inequality controls the stopped live mass by the killed moment at
the exact threshold used by `Phase2Bridge.hfail`. -/
theorem phase2StoppedLiveMass_le_div (n s T x : ℕ) (h3 : 3 ≤ n) :
    phase2StoppedLiveMass n s T x ≤
      expect (iter (phase2Stop n s) T x) (phase2StoppedPotential n s) /
        (2 : ℝ≥0∞) ^ (n / 2 ^ (s + 1) + 1) := by
  let θ : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (n / 2 ^ (s + 1) + 1)
  calc
    phase2StoppedLiveMass n s T x ≤
        ∑' z, if θ ≤ phase2StoppedPotential n s z then
          iter (phase2Stop n s) T x z else 0 := by
      unfold phase2StoppedLiveMass
      exact ENNReal.tsum_le_tsum fun z => by
        by_cases hz : Phase2Live n s z
        · simp [hz, phase2_markov_threshold_le h3 hz, θ]
        · simp [hz]
    _ ≤ expect (iter (phase2Stop n s) T x) (phase2StoppedPotential n s) /
        θ := markov_div (iter (phase2Stop n s) T x)
          (phase2StoppedPotential n s) θ (by simp [θ]) (by simp [θ])
    _ = expect (iter (phase2Stop n s) T x) (phase2StoppedPotential n s) /
        (2 : ℝ≥0∞) ^ (n / 2 ^ (s + 1) + 1) := rfl

/-- Population eight with `γ = 1` has exactly one reconciled buffered
phase-2 rung. -/
theorem phase2StageCount_eight_one : phase2StageCount 8 1 = 1 := by
  have hlog : Nat.log 2 8 = 3 := by decide
  have hle : phase2StageCount 8 1 ≤ 1 := by
    unfold phase2StageCount
    apply Nat.find_le
    rw [hlog]
    norm_num
  have hne : phase2StageCount 8 1 ≠ 0 := by
    intro hzero
    have hspec := phase2StageCount_spec 8 1
    rw [hzero, hlog] at hspec
    norm_num at hspec
  omega

/-- The stopped moment does not dominate even one-step original-chain failure
on the first buffered rung.  From `(n,s,x)=(8,2,6)`, a down-step exits the
guard and is killed, but remains a genuine failure of the next checkpoint. -/
theorem phase2_stopped_one_step_conversion_false :
    ¬ ((∑' z, if Phase2Stage 8 3 z then 0 else
        iter (triChain 8) 1 6 z) ≤
      expect (iter (phase2Stop 8 2) 1 6) (phase2StoppedPotential 8 2) /
        (2 : ℝ≥0∞) ^ (8 / 2 ^ 3 + 1)) := by
  have hlive6 : Phase2Live 8 2 6 := by
    norm_num [Phase2Live, Phase2Guard, Phase2Stage]
  have hn5 : ¬ Phase2Live 8 2 5 := by
    norm_num [Phase2Live, Phase2Guard, Phase2Stage]
  have hn7 : ¬ Phase2Live 8 2 7 := by
    norm_num [Phase2Live, Phase2Guard, Phase2Stage]
  have hpot5 : phase2StoppedPotential 8 2 5 = 0 :=
    phase2StoppedPotential_of_not_mem hn5
  have hpot6 : phase2StoppedPotential 8 2 6 = 4 := by
    rw [phase2StoppedPotential_of_mem hlive6,
      phase2PhysicalPotential_apply (show 6 + 2 = 8 by norm_num)]
    norm_num
  have hpot7 : phase2StoppedPotential 8 2 7 = 0 :=
    phase2StoppedPotential_of_not_mem hn7
  simp only [iter, PMF.bind_pure]
  rw [show phase2Stop 8 2 6 = triChain 8 6 by
    rw [phase2Stop, freeze_of_not_mem 6 (by simpa using hlive6)]]
  rw [triChain_apply (show 5 + 1 + 2 = 8 by norm_num) (by norm_num)]
  rw [expect_triStep, hpot5, hpot6, hpot7]
  norm_num [triStep_stay, Nat.choose]
  calc
    (20 : ℝ≥0∞) / 56 * 4 / 4 <
        (if Phase2Stage 8 3 5 then 0 else
            triStep 6 2 (by norm_num) 5) +
          (if Phase2Stage 8 3 6 then 0 else
            triStep 6 2 (by norm_num) 6) := by
      norm_num [Phase2Stage, triStep_down, triStep_stay, Nat.choose]
      rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
    _ ≤ ∑' z, if Phase2Stage 8 3 z then 0 else
        triStep 6 2 (by norm_num) z := by
      have hsum := ENNReal.sum_le_tsum ({5, 6} : Finset ℕ)
        (f := fun z => if Phase2Stage 8 3 z then 0 else
          triStep 6 2 (by norm_num) z)
      simpa using hsum

/-- The one genuine residual at the buffered count: every original-chain rung
must satisfy its advertised exact-time stage error.  This is strictly the
transfer/progress statement missing from the stopped recurrence. -/
def Phase2BufferedOriginalChainBound (n γ : ℕ) : Prop :=
  ∀ i < phase2StageCount n γ, ∀ x,
    Phase2Stage n (2 + i) x →
      ∑' z, (if Phase2Stage n (2 + i + 1) z then 0 else
        iter (triChain n) (4 * n) x z) ≤ phase2StageError n (2 + i)

/-- The explicit deterministic moment envelope used by the final bridge after
the stopped-moment Markov conversion has been ruled out. -/
noncomputable def phase2BufferedMoment (n s T : ℕ) : ℝ :=
  (2 : ℝ) ^ (n / 2 ^ s) * phase2Decay s ^ T

/-- The buffered `Phase2Bridge`.  The deterministic envelope discharges the
initial moment and recurrence; its sole premise is the precisely isolated
original-chain exact-time bound. -/
noncomputable def phase2Bridge_buffered (n γ : ℕ)
    (horiginal : Phase2BufferedOriginalChainBound n γ) :
    Phase2Bridge n (phase2StageCount n γ) where
  V := fun i _x T => phase2BufferedMoment n (2 + i) T
  hV0 := by
    intro i hi x hx
    simp [phase2BufferedMoment]
  hVstep := by
    intro i hi x hx hguard T
    simp only [phase2BufferedMoment, pow_succ]
    ring_nf
    exact le_rfl
  hfail := by
    intro i hi x hx
    simpa [phase2BufferedMoment, phase2StageError] using
      horiginal i hi x hx

/-- Under the single original-chain bound family, the reconciled buffered
ladder is an immediate application of `phase2_reaches_buffered`. -/
theorem phase2_reaches_buffered_of_originalChainBound
    (n γ : ℕ) (horiginal : Phase2BufferedOriginalChainBound n γ) :
    Reaches (triChain n) (phase2StageCount n γ * (4 * n))
      (Phase1Exit n) (Phase3Entry n γ)
      (∑ i ∈ Finset.range (phase2StageCount n γ),
        phase2StageError n (2 + i)) :=
  phase2_reaches_buffered n γ
    (phase2Bridge_buffered n γ horiginal)

#print axioms phase2PhysicalPotential_apply
#print axioms phase2StoppedPotential_of_mem
#print axioms phase2StoppedPotential_of_not_mem
#print axioms phase2StoppedPotential_le
#print axioms phase2Live_successors
#print axioms phase2Stop_step
#print axioms phase2Stop_expect_iter_le
#print axioms phase2PhysicalPotential_ne_top
#print axioms phase2StoppedPotential_ne_top
#print axioms phase2Stop_expect_ne_top
#print axioms phase2StoppedMoment_step
#print axioms phase2StoppedMoment_zero_le
#print axioms phase2_stopped_failure_eq_live_add_escape
#print axioms phase2_failure_le_stopped_failure_add_excess
#print axioms phase2_markov_threshold_le
#print axioms phase2StoppedLiveMass_le_div
#print axioms phase2StageCount_eight_one
#print axioms phase2_stopped_one_step_conversion_false
#print axioms phase2_reaches_buffered_of_originalChainBound

end Tri
