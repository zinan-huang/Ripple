/-
Roles in the Doty et al. exact majority protocol.

After Phase 0 (population splitting), each agent has one of three roles:
- Main: holds an opinion and bias, computes majority
- Reserve: holds an opinion (initially) for later split-fuel use in Phase 6
- Clock: drives the fixed-resolution phase clock

Two transient roles MCR and CR appear during Phase 0 itself.

Reference: Doty et al., §3.2 Phase 0; §3.4 pseudocode.
-/

import Mathlib.Data.Fintype.Basic

namespace ExactMajority

inductive Role
  | main
  | reserve
  | clock
  | mcr     -- transient: undecided among Main / Clock / Reserve
  | cr      -- transient: undecided among Clock / Reserve
  deriving DecidableEq, Repr

namespace Role

instance : Fintype Role where
  elems := {.main, .reserve, .clock, .mcr, .cr}
  complete r := by cases r <;> simp

instance : Inhabited Role := ⟨.mcr⟩

end Role
end ExactMajority
