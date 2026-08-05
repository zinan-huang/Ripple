/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Endgame
import Tri.Hoeffding
import Tri.Regions
import Tri.Rung
import Tri.Statement

/-!
# Conditional end-to-end assembly of Theorem 1(b)

This module reaches `Theorem1b_statement` itself, without weakening its horizon,
initial condition, terminal event, or error bound.  `Reaches.comp` discharges the
sequential-composition step.  The exact remaining-work board for
`theorem1b_of_phases` is:

* `hC`, `hc`, and `hn₀` -- **(i)** elementary witness conditions.  They become
  closed arithmetic facts after concrete constants are chosen.
* `hphase1` -- **(ii)** the phase-1 checkpoint on `triChain`.  It needs a
  new theorem `phase1_reaches` with exactly the displayed hypothesis type.  Its
  missing ingredients can be named `band_rung_bound`, `band_rung_transfer`, and
  `phase1_direction_progress`: an upper-success-guarded rung, its transfer to
  the original chain, and a direction-sensitive progress bound.  Merely
  exceeding the productive-reaction counter threshold does not imply gap
  doubling.
* `hphase2` -- **(ii)** the phase-2 checkpoint on `triChain`.  It needs a
  new `phase2_halving_stage`, again with both ruin and success guards, followed
  by a `phase2_reaches` composition of the halving stages.
* `hphase3` -- **(ii)** the phase-3 checkpoint on `triChain`.  The scalar lemmas
  `absorption_uniformise` and `absorption_iterate` are available, but a new
  CRN-specific `phase3_corrected_step` and a `phase3_reaches` conversion to the
  displayed `ℝ≥0∞` failure mass are still needed.
* `hschedule` -- **(i)** arithmetic: the three chosen phase horizons must add to
  no more than the headline horizon, witnessed without natural subtraction by
  an explicit padding duration.
* `hbudget` -- **(i)** arithmetic/analysis after the phase estimates are fixed:
  their union-bound sum must fit the headline power-law budget.

## Keystone: the current rung productivity premise is false at phase-1 parameters

The tempting missing step is **(iii), UNSATISFIABLE**: instantiate the existing
`rung_bound` uniformly with the phase-1 lower bound `p = 21/64`.  Its `hprod`
quantifies over every live state above `aLo`, without the phase's upper success
boundary.  Take `n = 64`, `γ = 1`, `aLo = bHi = 31`, `a = 62`, and `b = 0`
(so `x = 63`, `y = 1`).  These values satisfy `6 * γ * lg n ≤ n` and all the
rung population/majority side conditions, but the productive mass is `3/64`,
strictly below `21/64`.  The theorem `phase1_uniform_productive_false` proves
this mismatch in Lean.  Consequently this false premise is not quietly carried
by the headline theorem: `hphase1` must instead be proved using a kernel guarded
at both the ruin boundary and the phase-success boundary.
-/

namespace Tri

open scoped ENNReal

/-- Initial states covered by the headline theorem, packaged as a phase
precondition. -/
def AssemblyInitial (n γ x : ℕ) : Prop :=
  x ≤ n ∧ HasXInitialGap n γ x

/-- The phase-1 exit region.  On a physical state this is the subtraction-free
form of saying that the minority count is at most `n / 6`. -/
def Phase1Exit (n x : ℕ) : Prop :=
  x ≤ n ∧ 5 * n ≤ 6 * x

/-- Membership in the phase-1 exit region is decidable. -/
instance (n : ℕ) : DecidablePred (Phase1Exit n) := by
  intro x
  unfold Phase1Exit
  infer_instance

/-- The phase-2 exit region.  On a physical state this is the subtraction-free
form of saying that the minority count is at most `γ * lg n`. -/
def Phase2Exit (n γ x : ℕ) : Prop :=
  x ≤ n ∧ n ≤ x + γ * Nat.log 2 n

/-- Membership in the phase-2 exit region is decidable. -/
instance (n γ : ℕ) : DecidablePred (Phase2Exit n γ) := by
  intro x
  unfold Phase2Exit
  infer_instance

/-- A uniform lower bound on productive mass above a lower guard.  This is the
precise premise consumed by `rung_bound`; notably, it has no upper guard. -/
def UniformProductiveLower (n aLo : ℕ) (p : ℝ≥0∞) : Prop :=
  ∀ (_h3 : 3 ≤ n) (a b : ℕ) (hab : a + b + 2 = n), aLo ≤ a →
    p ≤ triStep (a + 1) (b + 1) (by omega) a +
      triStep (a + 1) (b + 1) (by omega) (a + 2)

/-- The phase-1 constant `21/64` is not a uniform productive-mass lower bound
for the current one-sided guarded rung, even at the headline-admissible
population `64`. -/
theorem phase1_uniform_productive_false :
    ¬ UniformProductiveLower 64 31 ((21 : ℝ≥0∞) / 64) := by
  intro h
  have hbad := h (by norm_num) 62 0 (by norm_num) (by norm_num)
  rw [triStep_down, triStep_up] at hbad
  norm_num [Nat.choose] at hbad
  have hreal := ENNReal.toReal_mono
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (1953 : ℝ≥0∞) / 41664 ≠ ⊤) hbad
  norm_num [ENNReal.toReal_div] at hreal

/-- Three exact-time checkpoints compose without an additional probabilistic
hypothesis; their failure bounds add by two applications of `Reaches.comp`. -/
theorem Reaches.three {K : ℕ → PMF ℕ} {P Q R S : ℕ → Prop}
    [DecidablePred Q] [DecidablePred R] [DecidablePred S]
    {T₁ T₂ T₃ : ℕ} {ε₁ ε₂ ε₃ : ℝ≥0∞}
    (h₁ : Reaches K T₁ P Q ε₁) (h₂ : Reaches K T₂ Q R ε₂)
    (h₃ : Reaches K T₃ R S ε₃) :
    Reaches K (T₁ + T₂ + T₃) P S (ε₁ + ε₂ + ε₃) := by
  exact (h₁.comp h₂).comp h₃

/-- A reachability bound may be padded by any deterministic number of steps
when its postcondition is absorbing. -/
theorem Reaches.pad_of_absorbing {α : Type*} {K : α → PMF α}
    {P Q : α → Prop} [DecidablePred Q] {T : ℕ} {ε : ℝ≥0∞}
    (h : Reaches K T P Q ε) (habs : ∀ s, Q s → K s = PMF.pure s) (U : ℕ) :
    Reaches K (T + U) P Q ε := by
  have hstay : Reaches K U Q Q 0 := by
    intro s hs
    have hiter : iter K U s = PMF.pure s := by
      induction U with
      | zero => rfl
      | succ U ih =>
          rw [iter_succ, habs s hs, PMF.pure_bind]
          exact ih
    rw [hiter]
    rw [nonpos_iff_eq_zero, ENNReal.tsum_eq_zero]
    intro z
    by_cases hz : Q z
    · simp [hz]
    · have hzs : z ≠ s := by
        intro hzs
        subst z
        exact hz hs
      simp [hz, hzs]
  simpa using h.comp hstay

/-- Conditional end-to-end assembly of the exact formal statement of Theorem
1(b).  The phase hypotheses are the only remaining probabilistic inputs;
composition is proved by `Reaches.three`. -/
theorem theorem1b_of_phases
    (C n₀ : ℕ) (c : ℝ)
    (T₁ T₂ T₃ : ℕ → ℕ → ℕ)
    (ε₁ ε₂ ε₃ : ℕ → ℕ → ℝ≥0∞)
    (hC : 0 < C) (hc : 0 < c) (hn₀ : 3 ≤ n₀)
    (hphase1 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (T₁ n γ) (AssemblyInitial n γ) (Phase1Exit n)
        (ε₁ n γ))
    (hphase2 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (T₂ n γ) (Phase1Exit n) (Phase2Exit n γ)
        (ε₂ n γ))
    (hphase3 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (T₃ n γ) (Phase2Exit n γ) (IsXMajority n)
        (ε₃ n γ))
    (hschedule : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ∃ U : ℕ, T₁ n γ + T₂ n γ + T₃ n γ + U =
        C * γ * n * Nat.log 2 n)
    (hbudget : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      ε₁ n γ + ε₂ n γ + ε₃ n γ ≤
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))) :
    Theorem1b_statement := by
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro n γ x₀ hn hγ hsize hx hgap
  have hreach := Reaches.three
    (hphase1 n γ hn hγ hsize)
    (hphase2 n γ hn hγ hsize)
    (hphase3 n γ hn hγ hsize)
  obtain ⟨U, hU⟩ := hschedule n γ hn hγ hsize
  have hpadded := hreach.pad_of_absorbing (fun s hs => by
    apply consensus_absorbing n s
    right
    exact hs) U
  rw [hU] at hpadded
  exact (hpadded x₀ ⟨hx, hgap⟩).trans (hbudget n γ hn hγ hsize)

end Tri
