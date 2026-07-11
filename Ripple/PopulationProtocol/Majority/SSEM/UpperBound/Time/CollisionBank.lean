import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.ResetBudget
import Mathlib.Tactic

namespace SSEM

open scoped BigOperators

variable {n : ℕ}

/-- Agents still in the ranking protocol's unsettled role. -/
def unsettledAgents (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun w => (C w).1.role = .Unsettled

/-- Number of unsettled agents. -/
def unsettledCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (unsettledAgents C).card

/-- Collision bank: current same-rank collision budget plus a slack account
prepaying the possible same-rank pairs created when an Unsettled agent is
recruited. -/
def collisionBank (C : Config (AgentState n) Opinion n) : ℕ :=
  resetBudget C + 2 * n * unsettledCount C

theorem unsettledCount_le (C : Config (AgentState n) Opinion n) :
    unsettledCount C ≤ n := by
  classical
  unfold unsettledCount unsettledAgents
  calc
    ((Finset.univ : Finset (Fin n)).filter
        (fun w : Fin n => (C w).1.role = .Unsettled)).card
        ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_filter_le _ _
    _ = n := by simp

theorem collisionBank_le (C : Config (AgentState n) Opinion n) :
    collisionBank C ≤ 3 * n * n := by
  have hReset := resetBudget_le_quadratic (C := C)
  have hUn := unsettledCount_le (C := C)
  have hSlack : 2 * n * unsettledCount C ≤ 2 * n * n :=
    Nat.mul_le_mul_left (2 * n) hUn
  unfold collisionBank
  calc
    resetBudget C + 2 * n * unsettledCount C
        ≤ n * n + 2 * n * n := Nat.add_le_add hReset hSlack
    _ = 3 * n * n := by ring

theorem unsettledAgents_eq_of_role_iff
    {C C' : Config (AgentState n) Opinion n}
    (hiff : ∀ w : Fin n, (C' w).1.role = .Unsettled ↔
      (C w).1.role = .Unsettled) :
    unsettledAgents C' = unsettledAgents C := by
  classical
  unfold unsettledAgents
  ext w
  simp [hiff w]

theorem unsettledCount_eq_of_role_iff
    {C C' : Config (AgentState n) Opinion n}
    (hiff : ∀ w : Fin n, (C' w).1.role = .Unsettled ↔
      (C w).1.role = .Unsettled) :
    unsettledCount C' = unsettledCount C := by
  unfold unsettledCount
  rw [unsettledAgents_eq_of_role_iff (C := C) (C' := C') hiff]

theorem unsettledAgents_eq_erase_of_removed
    {C C' : Config (AgentState n) Opinion n} {w : Fin n}
    (hwPre : (C w).1.role = .Unsettled)
    (hwPost : (C' w).1.role ≠ .Unsettled)
    (hiff : ∀ u : Fin n, u ≠ w →
      ((C' u).1.role = .Unsettled ↔ (C u).1.role = .Unsettled)) :
    unsettledAgents C' = (unsettledAgents C).erase w := by
  classical
  unfold unsettledAgents
  ext u
  by_cases huw : u = w
  · subst u
    simp [hwPre, hwPost]
  · simp [huw, hiff u huw]

theorem unsettledCount_eq_succ_of_removed
    {C C' : Config (AgentState n) Opinion n} {w : Fin n}
    (hwPre : (C w).1.role = .Unsettled)
    (hwPost : (C' w).1.role ≠ .Unsettled)
    (hiff : ∀ u : Fin n, u ≠ w →
      ((C' u).1.role = .Unsettled ↔ (C u).1.role = .Unsettled)) :
    unsettledCount C = unsettledCount C' + 1 := by
  classical
  have hset := unsettledAgents_eq_erase_of_removed
    (C := C) (C' := C') (w := w) hwPre hwPost hiff
  have hwMem : w ∈ unsettledAgents C := by
    unfold unsettledAgents
    simp [hwPre]
  unfold unsettledCount
  rw [hset, Finset.card_erase_of_mem hwMem]
  have hpos : 0 < (unsettledAgents C).card :=
    Finset.card_pos.mpr ⟨w, hwMem⟩
  omega

theorem unsettledAgents_eq_insert_of_added
    {C C' : Config (AgentState n) Opinion n} {w : Fin n}
    (_hwPre : (C w).1.role ≠ .Unsettled)
    (hwPost : (C' w).1.role = .Unsettled)
    (hiff : ∀ u : Fin n, u ≠ w →
      ((C' u).1.role = .Unsettled ↔ (C u).1.role = .Unsettled)) :
    unsettledAgents C' = insert w (unsettledAgents C) := by
  classical
  unfold unsettledAgents
  ext u
  by_cases huw : u = w
  · subst u
    simp [hwPost]
  · simp [huw, hiff u huw]

theorem unsettledCount_eq_succ_of_added
    {C C' : Config (AgentState n) Opinion n} {w : Fin n}
    (hwPre : (C w).1.role ≠ .Unsettled)
    (hwPost : (C' w).1.role = .Unsettled)
    (hiff : ∀ u : Fin n, u ≠ w →
      ((C' u).1.role = .Unsettled ↔ (C u).1.role = .Unsettled)) :
    unsettledCount C' = unsettledCount C + 1 := by
  classical
  have hset := unsettledAgents_eq_insert_of_added
    (C := C) (C' := C') (w := w) hwPre hwPost hiff
  have hwNotMem : w ∉ unsettledAgents C := by
    unfold unsettledAgents
    simp [hwPre]
  unfold unsettledCount
  rw [hset]
  simp [hwNotMem]

theorem collisionBank_nonincrease_of_recruit_accounting
    {C C' : Config (AgentState n) Opinion n}
    (hReset : resetBudget C' ≤ resetBudget C + 2 * (n - 1))
    (hUn : unsettledCount C = unsettledCount C' + 1) :
    collisionBank C' ≤ collisionBank C := by
  have hTwo : 2 * (n - 1) ≤ 2 * n := by
    exact Nat.mul_le_mul_left 2 (Nat.sub_le n 1)
  unfold collisionBank
  rw [hUn]
  calc
    resetBudget C' + 2 * n * unsettledCount C'
        ≤ resetBudget C + 2 * (n - 1) + 2 * n * unsettledCount C' := by
          exact Nat.add_le_add_right hReset _
    _ ≤ resetBudget C + 2 * n + 2 * n * unsettledCount C' := by
          exact Nat.add_le_add_right (Nat.add_le_add_left hTwo _) _
    _ = resetBudget C + 2 * n * (unsettledCount C' + 1) := by ring

/-- Role/rank version of `resetBudget_le_add_single_changed`.  It permits
irrelevant field changes, e.g. a recruiting parent's `children` counter. -/
theorem resetBudget_le_add_single_role_rank_changed
    (C C' : Config (AgentState n) Opinion n) (w : Fin n)
    (hOther : ∀ u : Fin n, u ≠ w →
      (C' u).1.role = (C u).1.role ∧ (C' u).1.rank = (C u).1.rank) :
    resetBudget C' ≤ resetBudget C + 2 * (n - 1) := by
  classical
  let I := offdiagPairsIncident w
  have hsubset : sameRankSettledPairs C' ⊆ sameRankSettledPairs C ∪ I := by
    intro p hp
    rw [sameRankSettledPairs, Finset.mem_filter] at hp
    rcases hp with ⟨_, hpne, hp1Set, hp2Set, hprank⟩
    by_cases htouch : p.1 = w ∨ p.2 = w
    · apply Finset.mem_union_right
      simp [I, offdiagPairsIncident, hpne, htouch]
    · have hp1_ne : p.1 ≠ w := by
        intro h
        exact htouch (Or.inl h)
      have hp2_ne : p.2 ≠ w := by
        intro h
        exact htouch (Or.inr h)
      have hstate1 := hOther p.1 hp1_ne
      have hstate2 := hOther p.2 hp2_ne
      apply Finset.mem_union_left
      rw [sameRankSettledPairs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hpne, ?_, ?_, ?_⟩
      · rw [← hstate1.1]
        exact hp1Set
      · rw [← hstate2.1]
        exact hp2Set
      · rw [← hstate1.2, ← hstate2.2]
        exact hprank
  have hcard := Finset.card_le_card hsubset
  have hUnion : (sameRankSettledPairs C ∪ I).card ≤
      (sameRankSettledPairs C).card + I.card :=
    Finset.card_union_le _ _
  have hI : I.card ≤ 2 * (n - 1) := by
    simpa [I] using offdiagPairsIncident_card_le (n := n) w
  unfold resetBudget
  exact hcard.trans (hUnion.trans (Nat.add_le_add_left hI _))

/-- Key recruit amortization lemma.  If one Unsettled endpoint leaves
`Unsettled`, and all other agents keep the same role/rank, the possible
new same-rank Settled pairs are incident to that endpoint and are paid by
the `2*n` slack drop. -/
theorem collisionBank_nonincrease_at_recruit
    (C C' : Config (AgentState n) Opinion n) (w : Fin n)
    (hwPre : (C w).1.role = .Unsettled)
    (hwPost : (C' w).1.role ≠ .Unsettled)
    (hOther : ∀ u : Fin n, u ≠ w →
      (C' u).1.role = (C u).1.role ∧ (C' u).1.rank = (C u).1.rank) :
    collisionBank C' ≤ collisionBank C := by
  have hReset :=
    resetBudget_le_add_single_role_rank_changed (C := C) (C' := C') w hOther
  have hUn : unsettledCount C = unsettledCount C' + 1 := by
    apply unsettledCount_eq_succ_of_removed
    · exact hwPre
    · exact hwPost
    · intro u huw
      rw [(hOther u huw).1]
  exact collisionBank_nonincrease_of_recruit_accounting
    (C := C) (C' := C') hReset hUn

theorem collisionBank_strict_decrease_at_collision
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hi : (C i).1.role = .Settled)
    (hj : (C j).1.role = .Settled)
    (hrank : (C i).1.rank = (C j).1.rank) :
    collisionBank
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) <
      collisionBank C := by
  classical
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P i j
  have hReset := resetBudget_strict_decrease_at_collision
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C hij hi hj hrank
  have hdelta :=
    transitionPEM_collision_roles
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C i).1) (t := (C j).1) (x := (C i).2) (y := (C j).2)
      hi hj hrank
  have hiReset : (C' i).1.role = .Resetting := by
    dsimp [C', P, protocolPEM, Config.step]
    simp [hij, hdelta.1]
  have hjReset : (C' j).1.role = .Resetting := by
    dsimp [C', P, protocolPEM, Config.step]
    simp [hij, hij.symm, hdelta.2]
  have hRoleIff : ∀ w : Fin n, (C' w).1.role = .Unsettled ↔
      (C w).1.role = .Unsettled := by
    intro w
    by_cases hwi : w = i
    · subst w
      rw [hiReset, hi]
      simp
    · by_cases hwj : w = j
      · subst w
        rw [hjReset, hj]
        simp
      · have hw : C' w = C w := by
          dsimp [C', P, Config.step]
          simp [hij, hwi, hwj]
        rw [hw]
  have hUn : unsettledCount C' = unsettledCount C :=
    unsettledCount_eq_of_role_iff (C := C) (C' := C') hRoleIff
  unfold collisionBank
  rw [hUn]
  exact Nat.add_lt_add_right hReset _

theorem sameRankSettledPairs_eq_of_role_rank
    {C C' : Config (AgentState n) Opinion n}
    (h : ∀ w : Fin n,
      (C' w).1.role = (C w).1.role ∧ (C' w).1.rank = (C w).1.rank) :
    sameRankSettledPairs C' = sameRankSettledPairs C := by
  classical
  unfold sameRankSettledPairs
  ext p
  simp [h p.1, h p.2]

theorem resetBudget_eq_of_role_rank
    {C C' : Config (AgentState n) Opinion n}
    (h : ∀ w : Fin n,
      (C' w).1.role = (C w).1.role ∧ (C' w).1.rank = (C w).1.rank) :
    resetBudget C' = resetBudget C := by
  unfold resetBudget
  rw [sameRankSettledPairs_eq_of_role_rank (C := C) (C' := C') h]

theorem sameRankSettledPairs_eq_of_single_nonsettled_change
    {C C' : Config (AgentState n) Opinion n} {w : Fin n}
    (hwPre : (C w).1.role ≠ .Settled)
    (hwPost : (C' w).1.role ≠ .Settled)
    (hOther : ∀ u : Fin n, u ≠ w →
      (C' u).1.role = (C u).1.role ∧ (C' u).1.rank = (C u).1.rank) :
    sameRankSettledPairs C' = sameRankSettledPairs C := by
  classical
  unfold sameRankSettledPairs
  ext p
  by_cases hp1w : p.1 = w
  · subst hp1w
    simp [hwPre, hwPost]
  · by_cases hp2w : p.2 = w
    · subst hp2w
      simp [hwPre, hwPost]
    · have h1 := hOther p.1 hp1w
      have h2 := hOther p.2 hp2w
      simp [h1, h2]

theorem resetBudget_eq_of_single_nonsettled_change
    {C C' : Config (AgentState n) Opinion n} {w : Fin n}
    (hwPre : (C w).1.role ≠ .Settled)
    (hwPost : (C' w).1.role ≠ .Settled)
    (hOther : ∀ u : Fin n, u ≠ w →
      (C' u).1.role = (C u).1.role ∧ (C' u).1.rank = (C u).1.rank) :
    resetBudget C' = resetBudget C := by
  unfold resetBudget
  rw [sameRankSettledPairs_eq_of_single_nonsettled_change
    (C := C) (C' := C') (w := w) hwPre hwPost hOther]

/-- Exact bank increase for one follower-style wake:
a non-`Settled`, non-`Unsettled` endpoint becomes `Unsettled`, all other
role/rank data are unchanged.  The collision budget is unchanged and the
slack account rises by exactly `2*n`. -/
theorem collisionBank_eq_add_two_n_of_single_unsettled_wake
    {C C' : Config (AgentState n) Opinion n} {w : Fin n}
    (hwPreNotSettled : (C w).1.role ≠ .Settled)
    (hwPreNotUnsettled : (C w).1.role ≠ .Unsettled)
    (hwPostUnsettled : (C' w).1.role = .Unsettled)
    (hOther : ∀ u : Fin n, u ≠ w →
      (C' u).1.role = (C u).1.role ∧ (C' u).1.rank = (C u).1.rank) :
    collisionBank C' = collisionBank C + 2 * n := by
  have hReset : resetBudget C' = resetBudget C := by
    apply resetBudget_eq_of_single_nonsettled_change
    · exact hwPreNotSettled
    · rw [hwPostUnsettled]
      decide
    · exact hOther
  have hUn : unsettledCount C' = unsettledCount C + 1 := by
    apply unsettledCount_eq_succ_of_added
    · exact hwPreNotUnsettled
    · exact hwPostUnsettled
    · intro u huw
      rw [(hOther u huw).1]
  unfold collisionBank
  rw [hReset, hUn]
  ring

theorem collisionBank_nonranking_unchanged
    {C C' : Config (AgentState n) Opinion n}
    (h : ∀ w : Fin n,
      (C' w).1.role = (C w).1.role ∧ (C' w).1.rank = (C w).1.rank) :
    collisionBank C' = collisionBank C := by
  have hReset := resetBudget_eq_of_role_rank (C := C) (C' := C') h
  have hUn : unsettledCount C' = unsettledCount C := by
    apply unsettledCount_eq_of_role_iff
    intro w
    rw [(h w).1]
  unfold collisionBank
  rw [hReset, hUn]

theorem collisionBank_nonincrease_nonranking
    {C C' : Config (AgentState n) Opinion n}
    (h : ∀ w : Fin n,
      (C' w).1.role = (C w).1.role ∧ (C' w).1.rank = (C w).1.rank) :
    collisionBank C' ≤ collisionBank C := by
  rw [collisionBank_nonranking_unchanged (C := C) (C' := C') h]

end SSEM
