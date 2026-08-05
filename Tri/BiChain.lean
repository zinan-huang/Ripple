/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BiStep

/-!
# The Double-B Markov chain (Theorem 2)

`doubleBChain` iterates the Double-B step while at least two molecules remain,
and freezes otherwise.  Consensus is absorbing for free: when only one species
is present every drawn pair is inert, so the step is already the identity — no
special case is needed in the definition.
-/

namespace Tri

open scoped ENNReal

/-- The Double-B Markov chain on `BiCfg`: react while `≥ 2` molecules remain,
otherwise stay put. -/
noncomputable def doubleBChain : BiCfg → PMF BiCfg := fun s =>
  if h : 2 ≤ s.x + s.y + s.b then doubleBStep s h else PMF.pure s

/-- **All-`X` consensus is absorbing.**  With only `X` present every pair is
inert (`xx`), so the chain fixes `⟨x,0,0⟩`. -/
theorem doubleBChain_consensusX (x : ℕ) (h : 2 ≤ x) :
    doubleBChain ⟨x, 0, 0⟩ = PMF.pure ⟨x, 0, 0⟩ := by
  unfold doubleBChain
  rw [dif_pos (by simpa using h)]
  unfold doubleBStep
  have hpos : 0 < Nat.choose x 2 := Nat.choose_pos h
  have hne : ((Nat.choose x 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
  have htop : ((Nat.choose x 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext t
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
    {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  simp only [PairComp.next, PairComp.weight, dbPairPMF, PMF.ofFintype_apply, PMF.pure_apply,
    Nat.add_zero, Nat.mul_zero, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton]
  split_ifs with ht <;> simp_all [ENNReal.div_self hne htop]

/-- **All-`Y` consensus is absorbing.** -/
theorem doubleBChain_consensusY (y : ℕ) (h : 2 ≤ y) :
    doubleBChain ⟨0, y, 0⟩ = PMF.pure ⟨0, y, 0⟩ := by
  unfold doubleBChain
  rw [dif_pos (by simpa using h)]
  unfold doubleBStep
  have hpos : 0 < Nat.choose y 2 := Nat.choose_pos h
  have hne : ((Nat.choose y 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
  have htop : ((Nat.choose y 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext t
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
    {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  simp only [PairComp.next, PairComp.weight, dbPairPMF, PMF.ofFintype_apply, PMF.pure_apply,
    Nat.zero_add, Nat.zero_mul, Nat.mul_zero, Nat.choose_zero_right, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton]
  split_ifs with ht <;> simp_all [ENNReal.div_self hne htop]

end Tri
