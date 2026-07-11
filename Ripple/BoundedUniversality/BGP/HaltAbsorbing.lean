import Ripple.BoundedUniversality.BGP.Interfaces

/-!
Ripple.BoundedUniversality.BGP.HaltAbsorbing
------------------------
Generic absorbing-halt consequences for `DiscreteMachine`: once a configuration is halted, the
`step` map freezes it, so the iterated configuration is eventually constant on every halting run.

This is the model-level backbone for the *halt-flag-coordinate* route to the eventual-threshold
simulation: the readout regions constrain only the halt-flag coordinate, whose target
`enc (M.step^[j] (M.init w)) haltCoord` is EVENTUALLY CONSTANT — `= halted-value` once the run has
halted, `= nonhalt-value` throughout a nonhalting run.  That removes the need for the (vacuous,
for `j > D`) full-config depth-budget all-cycle tube.

Pure generic facts (only `DiscreteMachine.halted_absorbing` + Mathlib `Function.iterate`).  The
`M_U`-specific bridge `enc … haltCoordU = haltFlagU = (if halted then 1 else 0)` is a thin wrapper
added downstream.
-/

namespace Ripple.BoundedUniversality.BGP

open Function

variable {Conf : Type} [Primcodable Conf]

/-- **Halt freezes the step map.**  If `c` is halted, `step^[m] c = c` for every `m`
(`halted_absorbing` iterated). -/
theorem DiscreteMachine.iterate_halted_fixed (M : DiscreteMachine Conf) {c : Conf}
    (hc : M.halted c = true) : ∀ m, M.step^[m] c = c := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact M.halted_absorbing c hc

/-- **Configuration is eventually constant on a halting run.**  If the run on `w` is halted at
step `n`, then `step^[j] (init w) = step^[n] (init w)` for every `j ≥ n`. -/
theorem DiscreteMachine.config_const_of_halted_at (M : DiscreteMachine Conf) {w n : ℕ}
    (hn : M.halted (M.step^[n] (M.init w)) = true) :
    ∀ j ≥ n, M.step^[j] (M.init w) = M.step^[n] (M.init w) := by
  intro j hj
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm n m, Function.iterate_add_apply]
  exact M.iterate_halted_fixed hn m

/-- **Halting run: the halt test is eventually `true`.**  From the witness step `n`, the halt test
of every later iterate is `true` (the config is frozen at the halted one). -/
theorem DiscreteMachine.halted_eventually_of_halts (M : DiscreteMachine Conf) {w n : ℕ}
    (hn : M.halted (M.step^[n] (M.init w)) = true) :
    ∀ j ≥ n, M.halted (M.step^[j] (M.init w)) = true := by
  intro j hj
  rw [M.config_const_of_halted_at hn j hj]
  exact hn

/-- **Nonhalting run: the halt test is always `false`.**  Direct from the definition of `haltsOn`
(no `n` halts). -/
theorem DiscreteMachine.halted_false_of_not_halts (M : DiscreteMachine Conf) {w : ℕ}
    (hw : ¬ M.haltsOn w) :
    ∀ j, M.halted (M.step^[j] (M.init w)) = false := by
  intro j
  cases hb : M.halted (M.step^[j] (M.init w)) with
  | false => rfl
  | true => exact absurd ⟨j, hb⟩ hw

/-- **Eventual constancy of the halt test along the run**, packaged as a single existential: there
is a threshold `N` past which `M.halted (step^[j] (init w))` equals the run's halting verdict
`decide (M.haltsOn w)` — `true` from the witness on a halting run, `false` throughout a nonhalting
run.  This is the model fact the halt-flag-coordinate readout route consumes. -/
theorem DiscreteMachine.halted_eventually_const (M : DiscreteMachine Conf) (w : ℕ)
    [Decidable (M.haltsOn w)] :
    ∃ N, ∀ j ≥ N, M.halted (M.step^[j] (M.init w)) = decide (M.haltsOn w) := by
  by_cases hw : M.haltsOn w
  · obtain ⟨n, hn⟩ := hw
    refine ⟨n, fun j hj => ?_⟩
    rw [M.halted_eventually_of_halts hn j hj]
    simp [show M.haltsOn w from ⟨n, hn⟩]
  · refine ⟨0, fun j _ => ?_⟩
    rw [M.halted_false_of_not_halts hw j]
    simp [hw]

end Ripple.BoundedUniversality.BGP
