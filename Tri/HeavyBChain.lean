/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBKernel

/-!
# The Heavy-B Markov chain on physical configurations

`heavyBStep` and `heavyBChain` are the physical-configuration analogues of
`heavyStateStep`, needed for the formal statement of Theorem 2 (Heavy-B clause).

## Consensus is absorbing

At all-`X` consensus (`x = n, y = 0, b = 0`), every drawn pair is `(X,X)`,
which is inert.  So the chain fixes that configuration.

## The `n ≤ 2` degeneracy

The Heavy-B invariant `x + y + 2b = n` allows the lone-heavy-blank
configuration `(0, 0, 1)` at `n = 2`, which has fewer than two entities and
is absorbing but NOT consensus.  The formal statement excludes this by
requiring `3 ≤ n` (equivalently `3 ≤ n₀`), matching `heavy_two_entities`.
-/

namespace Tri

open scoped ENNReal

/-- One Heavy-B interaction on physical configurations. -/
noncomputable def heavyBStep (s : BiCfg) (h : 2 ≤ s.x + s.y + s.b) :
    PMF BiCfg :=
  (dbPairPMF s.x s.y s.b h).map (PairComp.heavyNext s)

/-- The Heavy-B Markov chain on `BiCfg`: react while `≥ 2` entities remain,
otherwise stay put. -/
noncomputable def heavyBChain : BiCfg → PMF BiCfg := fun s =>
  if h : 2 ≤ s.x + s.y + s.b then heavyBStep s h else PMF.pure s

/-- **All-`X` consensus is absorbing for `heavyBChain`.**  With only `X` present
every pair is `(X,X)`, which is inert under `heavyNext`. -/
theorem heavyBChain_consensusX (x : ℕ) (h : 2 ≤ x) :
    heavyBChain ⟨x, 0, 0⟩ = PMF.pure ⟨x, 0, 0⟩ := by
  unfold heavyBChain
  rw [dif_pos (by simpa using h)]
  unfold heavyBStep
  have hpos : 0 < Nat.choose x 2 := Nat.choose_pos h
  have hne : ((Nat.choose x 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
  have htop : ((Nat.choose x 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext t
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
    {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb,
     PairComp.bb} from rfl]
  simp only [PairComp.heavyNext, PairComp.weight, dbPairPMF,
    PMF.ofFintype_apply, PMF.pure_apply, Nat.add_zero, Nat.mul_zero,
    Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton]
  split_ifs with ht <;> simp_all [ENNReal.div_self hne htop]

/-- **All-`Y` consensus is absorbing for `heavyBChain`.** -/
theorem heavyBChain_consensusY (y : ℕ) (h : 2 ≤ y) :
    heavyBChain ⟨0, y, 0⟩ = PMF.pure ⟨0, y, 0⟩ := by
  unfold heavyBChain
  rw [dif_pos (by simpa using h)]
  unfold heavyBStep
  have hpos : 0 < Nat.choose y 2 := Nat.choose_pos h
  have hne : ((Nat.choose y 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
  have htop : ((Nat.choose y 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext t
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
    {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb,
     PairComp.bb} from rfl]
  simp only [PairComp.heavyNext, PairComp.weight, dbPairPMF,
    PMF.ofFintype_apply, PMF.pure_apply, Nat.zero_add, Nat.zero_mul,
    Nat.mul_zero, Nat.choose_zero_right, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton]
  split_ifs with ht <;> simp_all [ENNReal.div_self hne htop]

end Tri

#print axioms Tri.heavyBChain_consensusX
#print axioms Tri.heavyBChain_consensusY
