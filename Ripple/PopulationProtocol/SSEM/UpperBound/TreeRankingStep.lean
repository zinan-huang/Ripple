/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Consequences of one tree-phase step of P_EM (P3 Lemma 11)

From `pem_tree_step`: after one interaction from a configuration satisfying `TreeStepHyp`,

* the tree stays valid (`TreeCore`), assigned ranks stay assigned, computing agents stay
  computing (`tree_step_core`);
* a non-Settled agent is not moved by the Phase-4 swap, so it changes as `StepRel` says
  (`tree_step_nonSettled`);
* the *timer exponent* `tExp C = (T₀ - medTimer C) + [rank n-1 unassigned]` grows by at most one,
  and only on a tick pair (`tExp_step_le`; this includes the tick at the creation of rank `n-1`
  by the median, R3 review F1).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingPEM
import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingCount

namespace Ripple.PopulationProtocol.SSEM

open scoped BigOperators

variable {n : ℕ}

theorem stepRel_congr {Emax : ℕ} {a b b' : AgentState n} (h : StepRel Emax a b)
    (e : rhoS b' = rhoS b) : StepRel Emax a b' := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := rhoS_eq_iff.mp e
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · rw [e1, e2]; exact h.settled h1
  · rw [e4, e7]; exact h.resetting (e1 ▸ h1)
  · rw [e6]; exact h.unsettled (e1 ▸ h1)
  · rw [e1]; exact h.computing h1

/-- The timer exponent: `T₀ - (median timer)` plus one while rank `n-1` is unassigned. -/
noncomputable def tExp (T₀ : ℕ) (C : Config (AgentState n) Opinion n) : ℕ :=
  (T₀ - medTimer T₀ C) + (if Asg (kC C) (n - 1) then 0 else 1)

section Step

variable {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}

/-- The tree after one step. -/
theorem tree_step_core (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C) {u v : Fin n}
    (huv : u ≠ v) (hT0 : 2 ≤ 7 * (trank + 4)) (hn3 : 3 ≤ n) :
    TreeCore (kC (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v)) ∧
      (∀ j, Asg (kC C) j →
        Asg (kC (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v)) j) ∧
      (∀ j, Asg (kC (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v)) j
        ↔ Asg (kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v) j) ∧
      (AllCompK (kC C) →
        AllCompK (kC (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v)))
      := by
  obtain ⟨hT', hsu, hsv, π, hπ, -, -⟩ := pem_tree_step (trank := trank) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) C h huv hT0 hn3
  have hA := asg_of_rhoS_perm (k₁ := kC (C.step _ u v)) π hπ
  refine ⟨treeCore_of_rhoS_perm π hπ hT', fun j hj => (hA j).mpr
    (kstep_asg_mono huv hsu hsv hj), hA, fun hc w => ?_⟩
  have e := congrArg AgentState.role (hπ w)
  simp only [rhoS_role] at e
  show (C.step _ u v w).1.role ≠ .Resetting
  rw [e]
  set x := π w
  by_cases hxu : x = u
  · rw [hxu]; exact hsu.computing (hc u)
  · by_cases hxv : x = v
    · rw [hxv]; exact hsv.computing (hc v)
    · rw [kstep_other _ _ hxu hxv]; exact hc x

/-- A non-Settled agent after one step. -/
theorem tree_step_nonSettled (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C)
    {u v : Fin n} (huv : u ≠ v) (hT0 : 2 ≤ 7 * (trank + 4)) (hn3 : 3 ≤ n) (w : Fin n)
    (hw : (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1.role ≠
      .Settled) :
    (w ≠ u ∧ w ≠ v ∧
      C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w = C w) ∨
    ((w = u ∨ w = v) ∧ StepRel Emax (C w).1
      (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1) := by
  obtain ⟨_, hsu, hsv, π, hπ, hfix, -⟩ := pem_tree_step (trank := trank) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) C h huv hT0 hn3
  have e := hπ w
  have hrole : (kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v (π w)).role ≠ .Settled := by
    have := congrArg AgentState.role e
    simp only [rhoS_role] at this
    rw [← this]; exact hw
  rw [hfix w hrole] at e
  by_cases hwu : w = u
  · subst hwu; exact Or.inr ⟨Or.inl rfl, stepRel_congr hsu e⟩
  · by_cases hwv : w = v
    · subst hwv; exact Or.inr ⟨Or.inr rfl, stepRel_congr hsv e⟩
    · exact Or.inl ⟨hwu, hwv, step_other C hwu hwv⟩

/-- **The timer exponent grows only on a tick pair.** -/
theorem tExp_step_le (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C) {u v : Fin n}
    (huv : u ≠ v) (hT0 : 2 ≤ 7 * (trank + 4)) (hn3 : 3 ≤ n) :
    tExp (7 * (trank + 4))
        (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) ≤
      tExp (7 * (trank + 4)) C + (if TickPair C u v then 1 else 0) := by
  obtain ⟨hT', hsu, hsv, π, hπ, -, hmt, -⟩ := pem_tree_step (trank := trank) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) C h huv hT0 hn3
  obtain ⟨hTC', hmono, hA, -⟩ := tree_step_core (trank := trank) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) C h huv hT0 hn3
  set C' := C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
  set K' := kstep (rankDeltaOSSR Rmax Emax Dmax hn) (kC C) u v
  set T₀ := 7 * (trank + 4)
  -- the last-rank indicator
  have hlast : (if Asg (kC C') (n - 1) then 0 else 1) +
      (if ¬ Asg (kC C) (n - 1) ∧ Asg K' (n - 1) then 1 else 0) ≤
      (if Asg (kC C) (n - 1) then 0 else 1) := by
    by_cases h1 : Asg (kC C) (n - 1)
    · rw [if_pos (hmono _ h1), if_pos h1]; simp [h1]
    · rw [if_neg h1]
      by_cases h2 : Asg K' (n - 1)
      · rw [if_pos ((hA _).mpr h2)]; simp [h1, h2]
      · rw [if_neg (fun h3 => h2 ((hA _).mp h3))]; simp [h2]
  unfold tExp
  by_cases hm : ∃ w, MedAt (C' w).1
  · obtain ⟨w, hw⟩ := hm
    have e := medTimer_eq (T₀ := T₀) hTC' hw
    have := hmt w hw
    rw [e]
    split_ifs at this hlast ⊢ <;> omega
  · rw [medTimer_none (fun w hw => hm ⟨w, hw⟩)]
    split_ifs at hlast ⊢ <;> omega

end Step

end Ripple.PopulationProtocol.SSEM
