/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Main
import Tri.StageErrors

/-!
# Escape slack at the phase-2/phase-3 handoff

The proposed unconditional handoff is false for the current killed phase-3
potential.  At population `24`, the admissible start `x = 20` escapes to the
frozen state `19` with positive mass.  That mass persists, while the killed
potential expectation contracts below it by the selected horizon for `C₃ = 2`.

This module records the exact handoff family, proves the concrete obstruction,
and isolates the one genuine residual that suffices for the existing interface:
no non-consensus downward escape mass from a non-consensus phase-2 exit.  The
all-`X` branch is discharged unconditionally.
-/

namespace Tri

open scoped ENNReal

/-- The exact phase-2/phase-3 escape-slack family consumed by
`theorem1b_of_available_components`. -/
def Phase3EscapeHandoff (C₃ n₀ : ℕ) : Prop :=
  ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
    6 * γ * Nat.log 2 n ≤ n → Phase2Exit n γ x →
      Phase3EscapeSlack n (phase3Horizon C₃ n) x

/-- The single residual left by the false unconditional handoff: every
non-consensus phase-2 exit has zero stopped mass at non-consensus escape
states.  The consensus branch is excluded because it is proved directly. -/
def NoPhase3DownwardEscapeFromExit (C₃ n₀ : ℕ) : Prop :=
  ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
    6 * γ * Nat.log 2 n ≤ n → Phase2Exit n γ x → x < n →
      phase3EscapeMass n (phase3Horizon C₃ n) x = 0

/-- Starting from all-`X` consensus, the stopped chain assigns zero mass to
every non-consensus escape state at every horizon. -/
theorem phase3EscapeMass_consensus (n T : ℕ) :
    phase3EscapeMass n T n = 0 := by
  have hnregion : ¬ Phase3Region n n := by
    unfold Phase3Region
    omega
  have hstop : phase3Stop n n = PMF.pure n := by
    rw [phase3Stop, freeze_of_mem n hnregion]
  have hiter : iter (phase3Stop n) T n = PMF.pure n := by
    induction T with
    | zero => rfl
    | succ T ih =>
        rw [iter_succ, hstop, PMF.pure_bind, ih]
  unfold phase3EscapeMass
  rw [hiter]
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  by_cases hz : ¬ Phase3Region n z ∧ z ≠ n
  · simp [hz, PMF.pure_apply]
  · simp [hz]

/-- The proposed no-downward-escape residual is itself false for `C₃ = 2`
whenever the cutoff admits the concrete population `24`.  The escaping mass is
at least `15 / 253`, rather than zero. -/
theorem phase2Exit_no_downward_escape_false (n₀ : ℕ) (hn₀ : n₀ ≤ 24) :
    ¬ NoPhase3DownwardEscapeFromExit 2 n₀ := by
  intro hnoescape
  rcases phase3_escapeSlack_admissible_false with
    ⟨_h3, hγ, hsize, hexit, _hslack⟩
  have hzero := hnoescape 24 1 20 hn₀ hγ hsize hexit (by norm_num)
  rw [phase3Horizon_two_twentyfour] at hzero
  have hlower := phase3_escapeMass_24_192_lower
  rw [hzero] at hlower
  norm_num at hlower

/-- The exact unconditional handoff required by the final assembly is false
for `C₃ = 2` whenever `n₀ ≤ 24`. -/
theorem hescape_two_at_most_twentyfour_false (n₀ : ℕ) (hn₀ : n₀ ≤ 24) :
    ¬ Phase3EscapeHandoff 2 n₀ := by
  intro hescape
  rcases phase3_escapeSlack_admissible_false with
    ⟨_h3, hγ, hsize, hexit, hfalse⟩
  exact hfalse (hescape 24 1 20 hn₀ hγ hsize hexit)

/-- The exact `hescape` input of `theorem1b_of_available_components`, derived
from the single explicitly named no-downward-escape residual. -/
theorem hescape_proved (C₃ n₀ : ℕ)
    (hnoescape : NoPhase3DownwardEscapeFromExit C₃ n₀) :
    ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase2Exit n γ x →
        Phase3EscapeSlack n (phase3Horizon C₃ n) x := by
  intro n γ x hn hγ hsize hexit
  rcases eq_or_lt_of_le hexit.1 with hxn | hxlt
  · subst x
    exact phase3_escapeSlack_proved n (phase3Horizon C₃ n) n
      (phase3EscapeMass_consensus n (phase3Horizon C₃ n))
  · exact phase3_escapeSlack_proved n (phase3Horizon C₃ n) x
      (hnoescape n γ x hn hγ hsize hexit hxlt)

#print axioms phase3EscapeMass_consensus
#print axioms phase2Exit_no_downward_escape_false
#print axioms hescape_two_at_most_twentyfour_false
#print axioms hescape_proved

end Tri
