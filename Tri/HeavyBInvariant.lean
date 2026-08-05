/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBChain
import Tri.DoubleBAssembly
import Tri.Theorem2

/-!
# The Heavy-B invariant subtype and consensus properties

This file lifts the Heavy-B chain to the invariant subtype `HeavyState n`,
proves the projection back to `heavyBChain`, and establishes that all-`X`
consensus is absorbing and is characterised exactly by `heavyLevel = n`.
-/

namespace Tri

open scoped ENNReal

/-- All-`X` consensus on the Heavy-B invariant subtype. -/
def HeavyXConsensus {n : ℕ} (s : HeavyState n) : Prop :=
  s.1.x = n ∧ s.1.y = 0 ∧ s.1.b = 0

instance {n : ℕ} : DecidablePred (@HeavyXConsensus n) := by
  intro s
  unfold HeavyXConsensus
  infer_instance

/-- `heavyLevel = n` characterises all-`X` consensus on the subtype. -/
theorem heavyLevel_eq_n_iff {n : ℕ} (s : HeavyState n) :
    BiCfg.heavyLevel s.1 = n ↔ HeavyXConsensus s := by
  rcases s with ⟨⟨x, y, b⟩, h⟩
  simp only [BiCfg.heavyLevel, BiCfg.HeavyInv, HeavyXConsensus] at h ⊢
  omega

private theorem heavyStateStep_unfold {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n) :
    heavyStateStep n s
      = (dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s)).map
          (PairComp.nextHeavyState s) := by
  unfold heavyStateStep
  exact dif_pos (heavy_two_entities hn s)

private theorem heavyBChain_unfold {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n) :
    heavyBChain s.1
      = (dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s)).map
          (PairComp.heavyNext s.1) := by
  unfold heavyBChain heavyBStep
  exact dif_pos (heavy_two_entities hn s)

/-- The lifted Heavy-B step projects back to the physical `heavyBChain`. -/
theorem heavyStateStep_map_val {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n) :
    (heavyStateStep n s).map Subtype.val = heavyBChain s.1 := by
  have hs2 := heavy_two_entities hn s
  let p := dbPairPMF s.1.x s.1.y s.1.b hs2
  calc (heavyStateStep n s).map Subtype.val
      = (p.map (PairComp.nextHeavyState s)).map Subtype.val :=
        congrArg (PMF.map Subtype.val) (heavyStateStep_unfold hn s)
    _ = p.map (Subtype.val ∘ PairComp.nextHeavyState s) :=
        PMF.map_comp _ _ _
    _ = p.map (PairComp.heavyNext s.1) :=
        PMF.map_change_on_zero_mass _ _ _ fun k hk => by
          simp only [Function.comp, PairComp.nextHeavyState] at hk
          split_ifs at hk with hw
          · exact dbPairPMF_zero_of_weight_zero hw
          · exact absurd rfl hk
    _ = heavyBChain s.1 :=
        (heavyBChain_unfold hn s).symm

/-- The raw `heavyBChain` iterate is the pushforward of the subtype iterate. -/
theorem iter_heavyBChain_eq_map {n : ℕ} (hn : 3 ≤ n) (T : ℕ) (s : HeavyState n) :
    iter heavyBChain T s.1 = (iter (heavyStateStep n) T s).map Subtype.val :=
  iter_map_equivariant (heavyStateStep n) heavyBChain Subtype.val
    (heavyStateStep_map_val hn) T s

/-- **All-`X` consensus is absorbing for `heavyStateStep`.**
At consensus, every drawn pair is `(X,X)`, which is inert. -/
theorem heavyStateStep_consensus
    (n : ℕ) (hn : 3 ≤ n) (s : HeavyState n)
    (hs : HeavyXConsensus s) :
    heavyStateStep n s = PMF.pure s := by
  have hconst : ∀ k, PairComp.nextHeavyState s k = s := by
    intro k
    unfold PairComp.nextHeavyState
    split_ifs with hk
    · rfl
    · apply Subtype.ext
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [HeavyXConsensus] at hs
      rcases hs with ⟨rfl, rfl, rfl⟩
      cases k <;> simp [PairComp.weight, PairComp.heavyNext] at hk ⊢
  rw [heavyStateStep_unfold hn]
  rw [show PairComp.nextHeavyState s = (fun _ => s) from funext hconst]
  ext z
  rw [PMF.map_apply, PMF.pure_apply]
  by_cases hz : z = s
  · subst z
    simp only [if_true]
    exact PMF.tsum_coe _
  · simp only [if_neg hz, tsum_zero]

/-- Non-consensus mass agrees before and after projecting the invariant subtype
to physical configurations. -/
theorem heavyState_nonconsensus_mass_eq
    (n : ℕ) (hn : 3 ≤ n) (T : ℕ) (s : HeavyState n) :
    (∑' z : HeavyState n,
        if HeavyXConsensus z then 0
        else iter (heavyStateStep n) T s z) =
      ∑' z : BiCfg,
        if BiXConsensus n z then 0
        else iter heavyBChain T s.1 z := by
  rw [masked_eq_expect (HeavyXConsensus), masked_eq_expect (BiXConsensus n),
    iter_heavyBChain_eq_map hn T s, expect_map]
  unfold expect
  apply tsum_congr
  intro z
  congr 1

end Tri

#print axioms Tri.heavyLevel_eq_n_iff
#print axioms Tri.heavyStateStep_map_val
#print axioms Tri.iter_heavyBChain_eq_map
#print axioms Tri.heavyStateStep_consensus
#print axioms Tri.heavyState_nonconsensus_mass_eq
