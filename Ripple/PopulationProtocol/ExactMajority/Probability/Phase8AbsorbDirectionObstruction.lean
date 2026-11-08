/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-8 absorb-direction obstruction (historical archive) + fixed-direction check

HISTORY (2026-07-16): the pre-fix `absorbConsume` comparison was reversed
relative to dyadic mass — a larger Lean index denotes a SMALLER absolute bias
(`Bias.dyadic s k` = ±2^{−k}), while the paper's Phase 8 ("Low-exponent
Minority Elimination", paper:1256) has the agent with the LARGER |bias| absorb.
For the concrete pair `+2^-3` and `-2^-2`, the reversed implementation kept the
positive bias and deleted the negative bias, flipping the signed bias sum from
`-1/8` to `+1/8` — which would have made every sign-preservation ledger false.

The reversed comparison was fixed in `Protocol/Transition.lean` the same day.
This file (a) archives the reversed behaviour on an INLINE copy of the old
definition (`absorbConsumeReversed`) so the counterexample survives the fix,
and (b) checks that the LIVE fixed `absorbConsume` on the same pair absorbs in
the paper direction and preserves the sign of the pair sum.
-/

import Ripple.PopulationProtocol.ExactMajority.Protocol.Transition

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase8AbsorbDirectionObstruction

/-- A non-full phase-8 Main agent carrying the smaller positive mass `+2^-3`. -/
def smallPositive : AgentState 3 0 :=
  { input := .A
    output := .A
    phase := ⟨8, by decide⟩
    role := .main
    assigned := false
    bias := .dyadic .pos ⟨3, by decide⟩
    smallBias := ⟨3, by decide⟩
    hour := ⟨0, by decide⟩
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨0, by decide⟩
    counter := ⟨0, by decide⟩ }

/-- A non-full phase-8 Main agent carrying the larger negative mass `-2^-2`. -/
def largeNegative : AgentState 3 0 :=
  { input := .B
    output := .B
    phase := ⟨8, by decide⟩
    role := .main
    assigned := false
    bias := .dyadic .neg ⟨2, by decide⟩
    smallBias := ⟨3, by decide⟩
    hour := ⟨0, by decide⟩
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨0, by decide⟩
    counter := ⟨0, by decide⟩ }

/-! ## (a) The archived reversed definition and its counterexample -/

/-- INLINE archive of the pre-fix (reversed) `absorbConsume` body.  Kept as a
local definition precisely so this counterexample never again binds to the live
protocol: the live `absorbConsume` now uses `<` (paper direction). -/
def absorbConsumeReversed (L K : ℕ) (s t : AgentState L K) :
    AgentState L K × AgentState L K :=
  match s.bias, t.bias with
  | .dyadic .pos i, .dyadic .neg j =>
      if i.val > j.val ∧ ¬ s.full then
        ({ s with full := true }, { t with bias := .zero })
      else if j.val > i.val ∧ ¬ t.full then
        ({ s with bias := .zero }, { t with full := true })
      else (s, t)
  | .dyadic .neg i, .dyadic .pos j =>
      if i.val > j.val ∧ ¬ s.full then
        ({ s with full := true }, { t with bias := .zero })
      else if j.val > i.val ∧ ¬ t.full then
        ({ s with bias := .zero }, { t with full := true })
      else (s, t)
  | _, _ => (s, t)

/-- The reversed absorber kept `+2^-3`, marked it full, and deleted `-2^-2`. -/
theorem absorbConsumeReversed_concrete_behavior :
    absorbConsumeReversed 3 0 smallPositive largeNegative =
      ({smallPositive with full := true},
       {largeNegative with bias := .zero}) := by
  rfl

/-- The reversed direction flipped the signed pair sum from `-1/8` to `+1/8`:
the archived refutation of any sign-preservation claim about the old body. -/
theorem reversed_direction_sign_mismatch :
    Bias.toRat smallPositive.bias + Bias.toRat largeNegative.bias < 0 ∧
      0 <
        Bias.toRat (absorbConsumeReversed 3 0 smallPositive largeNegative).1.bias +
          Bias.toRat (absorbConsumeReversed 3 0 smallPositive largeNegative).2.bias := by
  rw [absorbConsumeReversed_concrete_behavior]
  constructor <;> norm_num [smallPositive, largeNegative, Bias.toRat]

/-! ## (b) The live fixed direction on the same pair -/

/-- The FIXED live absorber has the larger mass `-2^-2` absorb: it marks the
negative agent full and deletes the smaller `+2^-3`. -/
theorem absorbConsume_concrete_behavior :
    absorbConsume 3 0 smallPositive largeNegative =
      ({smallPositive with bias := .zero},
       {largeNegative with full := true}) := by
  rfl

/-- Under the fixed direction the recorded pair sum stays negative (the eaten
`+2^-3` is accounted by the `full` flag): the sign of the recorded pair sum is
preserved on this pair. -/
theorem absorbConsume_sign_preserved :
    Bias.toRat smallPositive.bias + Bias.toRat largeNegative.bias < 0 ∧
      Bias.toRat (absorbConsume 3 0 smallPositive largeNegative).1.bias +
          Bias.toRat (absorbConsume 3 0 smallPositive largeNegative).2.bias < 0 := by
  rw [absorbConsume_concrete_behavior]
  constructor <;> norm_num [smallPositive, largeNegative, Bias.toRat]

#print axioms absorbConsumeReversed_concrete_behavior
#print axioms reversed_direction_sign_mismatch
#print axioms absorbConsume_concrete_behavior
#print axioms absorbConsume_sign_preserved

end Phase8AbsorbDirectionObstruction
end Ripple.PopulationProtocol.ExactMajority
