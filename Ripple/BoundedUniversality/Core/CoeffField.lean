/-
Ripple.BoundedUniversality.Core.CoeffField
----------------------
Coefficient field definitions: ℚ (rational) and ℚ(π) (rationals adjoin π).
-/

import Mathlib

namespace Ripple.BoundedUniversality.Core

/-- The rational coefficient field, just ℚ. -/
abbrev Qrat : Type := ℚ

/-- ℚ(π) as a subfield of ℝ: the smallest subfield containing π. -/
noncomputable def QpiSubfield : Subfield ℝ :=
  Subfield.closure ({Real.pi} : Set ℝ)

/-- The type of elements in ℚ(π). -/
noncomputable abbrev Qpi : Type := QpiSubfield

theorem pi_mem_QpiSubfield : Real.pi ∈ QpiSubfield :=
  Subfield.subset_closure (Set.mem_singleton _)

theorem rat_mem_QpiSubfield (q : ℚ) : (q : ℝ) ∈ QpiSubfield :=
  SubfieldClass.ratCast_mem QpiSubfield q

noncomputable def pi_Qpi : Qpi :=
  ⟨Real.pi, pi_mem_QpiSubfield⟩

theorem twoPi_mem_QpiSubfield : 2 * Real.pi ∈ QpiSubfield :=
  QpiSubfield.mul_mem (rat_mem_QpiSubfield 2) pi_mem_QpiSubfield

noncomputable def twoPi_Qpi : Qpi :=
  ⟨2 * Real.pi, twoPi_mem_QpiSubfield⟩

end Ripple.BoundedUniversality.Core
