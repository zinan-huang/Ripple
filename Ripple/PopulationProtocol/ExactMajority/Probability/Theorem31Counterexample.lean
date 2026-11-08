import Ripple.PopulationProtocol.ExactMajority.Probability.Theorem31

/-!
# Theorem 3.1 terminal-calibration counterexample

The current terminal time assembly uses the concrete Phase-10 block length

`s10Concrete n = ceil (6 * n^2 * (1 + 2 * log n))`

and repeats that block `k10` times.  Its headline calibration simultaneously
requires every phase to take at most `17 * n * (L + 1)` interactions and to
fail with probability at most `1 / n^2`.

Those requirements are jointly unsatisfiable in `PaperRegime`:

* the Phase-10 error `(1/2)^k10 <= 1/n^2` forces `1 <= k10`;
* one concrete Phase-10 block already has length at least `6*n^2`;
* `L = clog 2 n` and `n >= 10^40` imply
  `17 * n * (L + 1) < 6*n^2`.

The final theorem below mirrors the actual `ht` and `hε` inputs of
`Theorem31.time_bound_of_terminal_hypotheses`.  It proves that no terminal
assembly can supply both inputs.  This refutes that assembly interface; it
does **not** refute the paper's O(log n) result or the protocol itself.
-/

namespace Ripple.PopulationProtocol.ExactMajority.Theorem31

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

attribute [local instance] Classical.propDecidable

/-- A coarse linear upper bound on binary ceiling-logarithm, sufficient for
the Phase-10 contradiction. -/
theorem four_mul_clog_two_add_one_le (n : ℕ) (hn : 32 ≤ n) :
    4 * (Nat.clog 2 n + 1) ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n < 64
      · have hn64 : n ≤ 2 ^ 6 := by norm_num; omega
        have hclog : Nat.clog 2 n ≤ 6 := Nat.clog_le_of_le_pow hn64
        omega
      · have hn64 : 64 ≤ n := by omega
        have hm32 : 32 ≤ (n + 1) / 2 := by omega
        have hm_lt : (n + 1) / 2 < n := by omega
        have hrec := ih ((n + 1) / 2) hm_lt hm32
        rw [Nat.clog_of_two_le (by omega) (by omega)]
        have harg : (n + 2 - 1) / 2 = (n + 1) / 2 := by omega
        rw [harg]
        omega

/-- The concrete Phase-10 block is already quadratic in the population size. -/
theorem six_mul_sq_le_s10Concrete (n : ℕ) (hn : 1 ≤ n) :
    6 * n ^ 2 ≤ WorkBuilder.s10Concrete n := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have htarget : ((6 * n ^ 2 : ℕ) : ℝ) ≤ WorkBuilder.s10RealTarget n := by
    unfold WorkBuilder.s10RealTarget
    norm_num [Nat.cast_mul, Nat.cast_pow]
    nlinarith [sq_nonneg (n : ℝ)]
  have hceil : WorkBuilder.s10RealTarget n ≤ (WorkBuilder.s10Concrete n : ℝ) := by
    simpa [WorkBuilder.s10Concrete] using Nat.le_ceil (WorkBuilder.s10RealTarget n)
  have hcast : ((6 * n ^ 2 : ℕ) : ℝ) ≤ (WorkBuilder.s10Concrete n : ℝ) :=
    htarget.trans hceil
  exact_mod_cast hcast

/-- The scalar Phase-10 time/error calibrations are incompatible in the paper
regime. -/
theorem regime_phase10_scalar_inputs_unsatisfiable
    {n L K k10 : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (ht : k10 * WorkBuilder.s10Concrete n ≤
      NumeralChainBounds.C0_numeral * n * (L + 1))
    (hε : ((((1 / 2 : ℝ≥0) ^ k10 : ℝ≥0) : ℝ≥0∞)) ≤
      1 / (n : ℝ≥0∞) ^ 2) :
    False := by
  have hn2 : 2 ≤ n := hReg.two_le_n
  have hn32 : 32 ≤ n := by
    have hN32 : 32 ≤ Params.N₀ := by unfold Params.N₀; norm_num
    exact hN32.trans hReg.hN
  have hk10 : 1 ≤ k10 := by
    by_contra hk
    have hk0 : k10 = 0 := by omega
    subst k10
    simp only [pow_zero, ENNReal.coe_one] at hε
    have hn_cast : (2 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn2
    have hn_sq : (1 : ℝ≥0∞) < (n : ℝ≥0∞) ^ 2 := by
      have hn_sq_le : (2 : ℝ≥0∞) ^ 2 ≤ (n : ℝ≥0∞) ^ 2 := by gcongr
      exact lt_of_lt_of_le (by norm_num) hn_sq_le
    have hinv : 1 / (n : ℝ≥0∞) ^ 2 < 1 := by
      simpa [one_div] using
        (ENNReal.inv_lt_one (a := (n : ℝ≥0∞) ^ 2)).2 hn_sq
    exact (not_lt_of_ge hε) hinv
  have hs : 6 * n ^ 2 ≤ WorkBuilder.s10Concrete n :=
    six_mul_sq_le_s10Concrete n (by omega)
  have htime : 6 * n ^ 2 ≤ NumeralChainBounds.C0_numeral * n * (L + 1) := by
    calc
      6 * n ^ 2 ≤ WorkBuilder.s10Concrete n := hs
      _ ≤ k10 * WorkBuilder.s10Concrete n := Nat.le_mul_of_pos_left _ hk10
      _ ≤ NumeralChainBounds.C0_numeral * n * (L + 1) := ht
  have hclog := four_mul_clog_two_add_one_le n hn32
  rw [hReg.hLlog] at htime
  simp only [NumeralChainBounds.C0_numeral] at htime
  have htime_factor : n * (6 * n) ≤ n * (17 * (Nat.clog 2 n + 1)) := by
    simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using htime
  have htime_linear : 6 * n ≤ 17 * (Nat.clog 2 n + 1) :=
    le_of_mul_le_mul_left htime_factor (by omega)
  omega

section TerminalWork

variable {L K : ℕ}
variable {θ : Phase3GoodClock.ClockTimingParams}
variable {tr : Phase3GoodClock.Trace L K}
variable {D : Phase3Core.Phase3ModeDomain L}
variable {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
variable {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
variable {entry : Config (AgentState L K)}

/-- The terminal work family really assigns `k10 * s10Concrete n` to work 10. -/
theorem terminalWork_phase10_time
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post : Phase3Assembly.Phase3PostTailShape
      (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞)) :
    ((terminalWork
      (L := L) (K := K)
      A post ε3 hpost)
      ⟨10, by omega⟩).t = A.k10 * WorkBuilder.s10Concrete n := by
  rfl

/-- The terminal work family really assigns error `(1/2)^k10` to work 10. -/
theorem terminalWork_phase10_error
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post : Phase3Assembly.Phase3PostTailShape
      (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞)) :
    ((terminalWork
      (L := L) (K := K)
      A post ε3 hpost)
      ⟨10, by omega⟩).ε = (1 / 2 : ℝ≥0) ^ A.k10 := by
  rfl

/-- Any reachable terminal assembly using this concrete work family has
incompatible per-phase time and error calibrations. -/
theorem terminalAssemblyR_calibration_unsatisfiable
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post : Phase3Assembly.Phase3PostTailShape
      (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (hwork : asm.work = terminalWork
      (L := L) (K := K)
      A post ε3 hpost)
    (ht : ∀ i, (phasesR asm i).t ≤ NumeralChainBounds.C0_numeral * n * (L + 1))
    (hε : ∀ i, ((phasesR asm i).ε : ℝ≥0∞) ≤ 1 / (n : ℝ≥0∞) ^ 2) :
    False := by
  apply regime_phase10_scalar_inputs_unsatisfiable hReg
  · have h20 := ht (⟨20, by omega⟩ : Fin 21)
    rw [phasesR_even asm ⟨20, by omega⟩ (by norm_num)] at h20
    change (asm.work (ExactAdvanceChain.workIdx ⟨20, by omega⟩)).t
      ≤ NumeralChainBounds.C0_numeral * n * (L + 1) at h20
    have hidx : ExactAdvanceChain.workIdx (⟨20, by omega⟩ : Fin 21) =
        (⟨10, by omega⟩ : Fin 11) := by
      apply Fin.ext
      norm_num [ExactAdvanceChain.workIdx]
    rw [hidx, hwork,
      terminalWork_phase10_time A post ε3 hpost] at h20
    exact h20
  · have h20 := hε (⟨20, by omega⟩ : Fin 21)
    rw [phasesR_even asm ⟨20, by omega⟩ (by norm_num)] at h20
    change (((asm.work (ExactAdvanceChain.workIdx ⟨20, by omega⟩)).ε : ℝ≥0) : ℝ≥0∞)
      ≤ 1 / (n : ℝ≥0∞) ^ 2 at h20
    have hidx : ExactAdvanceChain.workIdx (⟨20, by omega⟩ : Fin 21) =
        (⟨10, by omega⟩ : Fin 11) := by
      apply Fin.ext
      norm_num [ExactAdvanceChain.workIdx]
    rw [hidx, hwork,
      terminalWork_phase10_error A post ε3 hpost] at h20
    exact h20

/-- **Permanent anti-vacuity certificate for the current Theorem 3.1
assembly.** These are exactly the terminal core, `ht`, and `hε` inputs carried
by the former paper-facing time theorem.  No values can inhabit them together. -/
theorem theorem31_calibration_hypotheses_unsatisfiable
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K))
    (hcard : Multiset.card c₀ = n)
    (hValid : validInitial c₀)
    (A : Phase035Work.WorkFamilyTailData (L := L) (K := K) n)
    (post : Phase3Assembly.Phase3PostTailShape
      (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε3 : ℝ≥0)
    (hpost : ((post.entryTail).ε : ℝ≥0∞) ≤ (ε3 : ℝ≥0∞))
    (seamP seamT : Fin 10 → ℕ)
    (εovershoot : Fin 10 → ℝ≥0)
    (hTjanson : ∀ k,
      AdvanceBudgetSlack.advanceJansonT6 (L := L) (K := K) (seamP k) n A.hn ≤ seamT k)
    (hSeamEntryFromWorkPost : ∀ k : Fin 10,
      AdvanceEntryNoOvershoot.AdvanceEntryFromWorkPost
        (L := L) (K := K) (seamP k) n
        ((terminalWork
          (L := L) (K := K)
          A post ε3 hpost)
          ⟨k.val, by omega⟩).Post)
    (hOvershoot : TerminalReachableOvershootHypotheses
      (L := L) (K := K) c₀ n seamP seamT εovershoot)
    (payload : TerminalAdvancePayloadHypotheses (L := L) (K := K) c₀ n 10
      (terminalWork
        (L := L) (K := K)
        A post ε3 hpost)
      seamP seamT εovershoot)
    (tie : TerminalAdvanceEntryHypotheses (L := L) (K := K) n
      (terminalWork
        (L := L) (K := K)
        A post ε3 hpost)
      seamP)
    (ht :
      let core := terminalWorkAdvanceCore
        (L := L) (K := K)
        c₀ hcard hValid
        A post ε3 hpost
        seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot payload tie
      ∀ i, (phasesR core.asm i).t ≤ NumeralChainBounds.C0_numeral * n * (L + 1))
    (hε :
      let core := terminalWorkAdvanceCore
        (L := L) (K := K)
        c₀ hcard hValid
        A post ε3 hpost
        seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot payload tie
      ∀ i, ((phasesR core.asm i).ε : ℝ≥0∞) ≤ 1 / (n : ℝ≥0∞) ^ 2) :
    False := by
  let core := terminalWorkAdvanceCore
    (L := L) (K := K)
    c₀ hcard hValid
    A post ε3 hpost
    seamP seamT εovershoot hTjanson hSeamEntryFromWorkPost hOvershoot payload tie
  apply terminalAssemblyR_calibration_unsatisfiable
    hReg c₀ A post ε3 hpost core.asm
  · rfl
  · simpa [core] using ht
  · simpa [core] using hε

end TerminalWork

#print axioms regime_phase10_scalar_inputs_unsatisfiable
#print axioms terminalAssemblyR_calibration_unsatisfiable
#print axioms theorem31_calibration_hypotheses_unsatisfiable

end Ripple.PopulationProtocol.ExactMajority.Theorem31
