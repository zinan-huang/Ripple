/-
Ripple.BoundedUniversality.Core.Computability
-------------------------
Shared computability abstractions used by both HenonSelector and GPAC branches.
-/

import Mathlib

namespace Ripple.BoundedUniversality.Core

def BoolDecides (b : ℕ → Bool) (P : ℕ → Prop) : Prop :=
  ∀ n : ℕ, b n = true ↔ P n

def HasComputableBoolDecider (P : ℕ → Prop) : Prop :=
  ∃ b : ℕ → Bool, Computable b ∧ BoolDecides b P

def NoComputableBoolDecider (P : ℕ → Prop) : Prop :=
  ¬ HasComputableBoolDecider P

end Ripple.BoundedUniversality.Core
