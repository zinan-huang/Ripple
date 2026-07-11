import Ripple.PopulationProtocol.Majority.SSEM.Defs.Config
import Ripple.PopulationProtocol.Majority.SSEM.Protocol.RankDelta
import Ripple.PopulationProtocol.Majority.SSEM.Protocol.Transition
import Mathlib.Tactic

namespace SSEM

open scoped BigOperators

variable {n : ℕ}

/-- Ordered pairs of distinct settled agents with the same rank.  This is the
collision part of the reset budget: a collision reset removes at least the
scheduled ordered pair from this set. -/
def sameRankSettledPairs (C : Config (AgentState n) Opinion n) :
    Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter fun p =>
    p.1 ≠ p.2 ∧
      (C p.1).1.role = .Settled ∧
      (C p.2).1.role = .Settled ∧
      (C p.1).1.rank = (C p.2).1.rank

/-- Reset budget currently certified in this file: the number of ordered
same-rank settled collisions. -/
def resetBudget (C : Config (AgentState n) Opinion n) : ℕ :=
  (sameRankSettledPairs C).card

/-- Agents currently detected by the error-monitoring branch: Unsettled
endpoints whose counter will hit zero on this interaction. -/
def structuralErrorAgents (C : Config (AgentState n) Opinion n) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun w =>
    (C w).1.role = .Unsettled ∧ (C w).1.errorcount ≤ 1

/-- Error-reset budget certified here.  It deliberately counts the timed-out
Unsettled endpoints, not the raw sum of error counters. -/
def structuralErrorBudget (C : Config (AgentState n) Opinion n) : ℕ :=
  (structuralErrorAgents C).card

/-- Unweighted combined budget used for the variation analysis. -/
def budgetTot (C : Config (AgentState n) Opinion n) : ℕ :=
  resetBudget C + structuralErrorBudget C

theorem resetBudget_le_quadratic (C : Config (AgentState n) Opinion n) :
    resetBudget C ≤ n * n := by
  classical
  unfold resetBudget sameRankSettledPairs
  calc
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p : Fin n × Fin n =>
          p.1 ≠ p.2 ∧
            (C p.1).1.role = .Settled ∧
            (C p.2).1.role = .Settled ∧
            (C p.1).1.rank = (C p.2).1.rank)).card
        ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
          Finset.card_filter_le _ _
    _ = n * n := by simp

theorem structuralErrorBudget_le_linear
    (C : Config (AgentState n) Opinion n) :
    structuralErrorBudget C ≤ n := by
  classical
  unfold structuralErrorBudget structuralErrorAgents
  calc
    ((Finset.univ : Finset (Fin n)).filter
        (fun w : Fin n => (C w).1.role = .Unsettled ∧ (C w).1.errorcount ≤ 1)).card
        ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_filter_le _ _
    _ = n := by simp

/-- Ordered off-diagonal pairs touching a fixed endpoint. -/
def offdiagPairsIncident (w : Fin n) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter fun p =>
    p.1 ≠ p.2 ∧ (p.1 = w ∨ p.2 = w)

theorem offdiagPairsIncident_card_le (w : Fin n) :
    (offdiagPairsIncident w).card ≤ 2 * (n - 1) := by
  classical
  let A : Finset (Fin n × Fin n) :=
    ({w} : Finset (Fin n)).product ((Finset.univ : Finset (Fin n)).erase w)
  let B : Finset (Fin n × Fin n) :=
    ((Finset.univ : Finset (Fin n)).erase w).product ({w} : Finset (Fin n))
  have hsub : offdiagPairsIncident w ⊆ A ∪ B := by
    intro p hp
    rcases p with ⟨p₁, p₂⟩
    rw [offdiagPairsIncident, Finset.mem_filter] at hp
    rcases hp with ⟨_, hpne, htouch⟩
    dsimp at hpne
    rcases htouch with hpw | hpw
    · apply Finset.mem_union_left
      dsimp at hpw
      have hp₂ : p₂ ∈ (Finset.univ : Finset (Fin n)).erase w := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hpne (hpw.trans h.symm), Finset.mem_univ _⟩
      exact Finset.mem_product.mpr ⟨by simp [hpw], hp₂⟩
    · apply Finset.mem_union_right
      dsimp at hpw
      have hp₁ : p₁ ∈ (Finset.univ : Finset (Fin n)).erase w := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hpne (h.trans hpw.symm), Finset.mem_univ _⟩
      exact Finset.mem_product.mpr ⟨hp₁, by simp [hpw]⟩
  have hcardSub : (offdiagPairsIncident w).card ≤ (A ∪ B).card :=
    Finset.card_le_card hsub
  have hcardUnion : (A ∪ B).card ≤ A.card + B.card :=
    Finset.card_union_le A B
  have hA : A.card = n - 1 := by
    simp [A]
  have hB : B.card = n - 1 := by
    simp [B]
  calc
    (offdiagPairsIncident w).card ≤ (A ∪ B).card := hcardSub
    _ ≤ A.card + B.card := hcardUnion
    _ = 2 * (n - 1) := by simp [hA, hB, two_mul]

/-- If a configuration changes only one endpoint, the collision budget can
increase only through ordered pairs incident to that endpoint. -/
theorem resetBudget_le_add_single_changed
    (C C' : Config (AgentState n) Opinion n) (w : Fin n)
    (hOther : ∀ u : Fin n, u ≠ w → C' u = C u) :
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
      have hstate1 : C' p.1 = C p.1 := hOther p.1 hp1_ne
      have hstate2 : C' p.2 = C p.2 := hOther p.2 hp2_ne
      apply Finset.mem_union_left
      rw [sameRankSettledPairs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hpne, ?_, ?_, ?_⟩
      · rw [← hstate1]
        exact hp1Set
      · rw [← hstate2]
        exact hp2Set
      · rw [← hstate1, ← hstate2]
        exact hprank
  have hcard := Finset.card_le_card hsubset
  have hUnion : (sameRankSettledPairs C ∪ I).card ≤
      (sameRankSettledPairs C).card + I.card :=
    Finset.card_union_le _ _
  have hI : I.card ≤ 2 * (n - 1) := by
    simpa [I] using offdiagPairsIncident_card_le (n := n) w
  unfold resetBudget
  exact hcard.trans (hUnion.trans (Nat.add_le_add_left hI _))

/-- Two changed endpoints give the corresponding crude endpoint-touch bound. -/
theorem resetBudget_le_add_two_changed
    (C C' : Config (AgentState n) Opinion n) {i j : Fin n}
    (_hij : i ≠ j)
    (hOther : ∀ u : Fin n, u ≠ i → u ≠ j → C' u = C u) :
    resetBudget C' ≤ resetBudget C + (2 * (n - 1) + 2 * (n - 1)) := by
  classical
  let Ii := offdiagPairsIncident i
  let Ij := offdiagPairsIncident j
  have hsubset : sameRankSettledPairs C' ⊆ sameRankSettledPairs C ∪ Ii ∪ Ij := by
    intro p hp
    rw [sameRankSettledPairs, Finset.mem_filter] at hp
    rcases hp with ⟨_, hpne, hp1Set, hp2Set, hprank⟩
    by_cases htouchi : p.1 = i ∨ p.2 = i
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      simp [Ii, offdiagPairsIncident, hpne, htouchi]
    · by_cases htouchj : p.1 = j ∨ p.2 = j
      · apply Finset.mem_union_right
        simp [Ij, offdiagPairsIncident, hpne, htouchj]
      · have hp1_ne_i : p.1 ≠ i := by
          intro h
          exact htouchi (Or.inl h)
        have hp2_ne_i : p.2 ≠ i := by
          intro h
          exact htouchi (Or.inr h)
        have hp1_ne_j : p.1 ≠ j := by
          intro h
          exact htouchj (Or.inl h)
        have hp2_ne_j : p.2 ≠ j := by
          intro h
          exact htouchj (Or.inr h)
        have hstate1 : C' p.1 = C p.1 := hOther p.1 hp1_ne_i hp1_ne_j
        have hstate2 : C' p.2 = C p.2 := hOther p.2 hp2_ne_i hp2_ne_j
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        rw [sameRankSettledPairs, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hpne, ?_, ?_, ?_⟩
        · rw [← hstate1]
          exact hp1Set
        · rw [← hstate2]
          exact hp2Set
        · rw [← hstate1, ← hstate2]
          exact hprank
  have hcard := Finset.card_le_card hsubset
  have hUnion₁ :
      ((sameRankSettledPairs C ∪ Ii) ∪ Ij).card ≤
        (sameRankSettledPairs C ∪ Ii).card + Ij.card :=
    Finset.card_union_le _ _
  have hUnion₀ :
      (sameRankSettledPairs C ∪ Ii).card ≤
        (sameRankSettledPairs C).card + Ii.card :=
    Finset.card_union_le _ _
  have hIi : Ii.card ≤ 2 * (n - 1) := by
    simpa [Ii] using offdiagPairsIncident_card_le (n := n) i
  have hIj : Ij.card ≤ 2 * (n - 1) := by
    simpa [Ij] using offdiagPairsIncident_card_le (n := n) j
  have hmain :
      (sameRankSettledPairs C ∪ Ii ∪ Ij).card ≤
        (sameRankSettledPairs C).card + (2 * (n - 1) + 2 * (n - 1)) := by
    calc
      (sameRankSettledPairs C ∪ Ii ∪ Ij).card
          ≤ (sameRankSettledPairs C ∪ Ii).card + Ij.card := hUnion₁
      _ ≤ ((sameRankSettledPairs C).card + Ii.card) + Ij.card :=
          Nat.add_le_add_right hUnion₀ _
      _ ≤ ((sameRankSettledPairs C).card + 2 * (n - 1)) + 2 * (n - 1) :=
          Nat.add_le_add (Nat.add_le_add_left hIi _) hIj
      _ = (sameRankSettledPairs C).card + (2 * (n - 1) + 2 * (n - 1)) := by
          omega
  unfold resetBudget
  exact hcard.trans hmain

/-- Structural-error budget is monotone whenever every post-step structural
error endpoint was already a structural-error endpoint before the step. -/
theorem structuralErrorBudget_le_of_endpoint_imp
    (C C' : Config (AgentState n) Opinion n) {i j : Fin n}
    (_hij : i ≠ j)
    (hOther : ∀ u : Fin n, u ≠ i → u ≠ j → C' u = C u)
    (hi : (C' i).1.role = .Unsettled ∧ (C' i).1.errorcount ≤ 1 →
      (C i).1.role = .Unsettled ∧ (C i).1.errorcount ≤ 1)
    (hj : (C' j).1.role = .Unsettled ∧ (C' j).1.errorcount ≤ 1 →
      (C j).1.role = .Unsettled ∧ (C j).1.errorcount ≤ 1) :
    structuralErrorBudget C' ≤ structuralErrorBudget C := by
  classical
  have hsubset : structuralErrorAgents C' ⊆ structuralErrorAgents C := by
    intro u hu
    rw [structuralErrorAgents, Finset.mem_filter] at hu
    rcases hu with ⟨_, huRole, huErr⟩
    by_cases hui : u = i
    · subst u
      have hpre := hi ⟨huRole, huErr⟩
      rw [structuralErrorAgents, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hpre.1, hpre.2⟩
    · by_cases huj : u = j
      · subst u
        have hpre := hj ⟨huRole, huErr⟩
        rw [structuralErrorAgents, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hpre.1, hpre.2⟩
      · have hstate : C' u = C u := hOther u hui huj
        rw [structuralErrorAgents, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · rw [← hstate]
          exact huRole
        · rw [← hstate]
          exact huErr
  unfold structuralErrorBudget
  exact Finset.card_le_card hsubset

theorem resetBudget_step_le_add_two_changed
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j) :
    resetBudget (C.step P i j) ≤
      resetBudget C + (2 * (n - 1) + 2 * (n - 1)) := by
  apply resetBudget_le_add_two_changed (C := C) (C' := C.step P i j) hij
  intro u hui huj
  dsimp [Config.step]
  simp [hij, hui, huj]

theorem structuralErrorBudget_step_le_of_endpoint_imp
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hi : (C.step P i j i).1.role = .Unsettled ∧
        (C.step P i j i).1.errorcount ≤ 1 →
      (C i).1.role = .Unsettled ∧ (C i).1.errorcount ≤ 1)
    (hj : (C.step P i j j).1.role = .Unsettled ∧
        (C.step P i j j).1.errorcount ≤ 1 →
      (C j).1.role = .Unsettled ∧ (C j).1.errorcount ≤ 1) :
    structuralErrorBudget (C.step P i j) ≤ structuralErrorBudget C := by
  apply structuralErrorBudget_le_of_endpoint_imp
      (C := C) (C' := C.step P i j) hij
  · intro u hui huj
    dsimp [Config.step]
    simp [hij, hui, huj]
  · exact hi
  · exact hj

theorem budgetTot_step_le_add_two_changed_of_endpoint_imp
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hi : (C.step P i j i).1.role = .Unsettled ∧
        (C.step P i j i).1.errorcount ≤ 1 →
      (C i).1.role = .Unsettled ∧ (C i).1.errorcount ≤ 1)
    (hj : (C.step P i j j).1.role = .Unsettled ∧
        (C.step P i j j).1.errorcount ≤ 1 →
      (C j).1.role = .Unsettled ∧ (C j).1.errorcount ≤ 1) :
    budgetTot (C.step P i j) ≤
      budgetTot C + (2 * (n - 1) + 2 * (n - 1)) := by
  have hReset := resetBudget_step_le_add_two_changed
      (P := P) (C := C) hij
  have hStruct := structuralErrorBudget_step_le_of_endpoint_imp
      (P := P) (C := C) hij hi hj
  unfold budgetTot
  omega

theorem resetOSSR_not_structural_error_of_Emax_gt_one
    {Emax : ℕ} {hn : 0 < n} {s : AgentState n}
    (hEmax : 1 < Emax) :
    ¬ ((resetOSSR Emax hn s).role = .Unsettled ∧
      (resetOSSR Emax hn s).errorcount ≤ 1) := by
  unfold resetOSSR
  cases s.leader <;> simp [hEmax]

theorem rankDeltaOSSR_collision_roles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hrank : s.rank = t.rank) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
      (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting := by
  unfold rankDeltaOSSR
  simp [hs, ht, hrank]

theorem transitionPEM_collision_roles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hrank : s.rank = t.rank) :
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).1.role = .Resetting ∧
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).2.role = .Resetting := by
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 rankDeltaOSSR
  simp [hs, ht, hrank]

lemma transitionPEM_prePhase4_roles
    {trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion} :
    let p := transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁
    let r := rankDelta (s₀, s₁)
    p.1.role = r.1.role ∧ p.2.role = r.2.role := by
  unfold transitionPEM_prePhase4
  generalize hr : rankDelta (s₀, s₁) = r
  rcases r with ⟨r₀, r₁⟩
  simp
  split_ifs <;> simp

theorem rankDeltaOSSR_recruit_ab_roles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hRecruit : s.role = .Settled ∧ t.role = .Unsettled ∧
      s.children < 2 ∧ 2 * s.rank.val + s.children + 1 < n) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled ∧
      (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled := by
  unfold rankDeltaOSSR
  simp [hRecruit.1, hRecruit.2.1, hRecruit]

theorem rankDeltaOSSR_recruit_ab_child_rank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hRecruit : s.role = .Settled ∧ t.role = .Unsettled ∧
      s.children < 2 ∧ 2 * s.rank.val + s.children + 1 < n) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.rank.val =
      2 * s.rank.val + s.children + 1 := by
  unfold rankDeltaOSSR
  simp [hRecruit.1, hRecruit.2.1, hRecruit]

theorem rankDeltaOSSR_recruit_ba_roles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hRecruit : t.role = .Settled ∧ s.role = .Unsettled ∧
      t.children < 2 ∧ 2 * t.rank.val + t.children + 1 < n) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled ∧
      (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled := by
  unfold rankDeltaOSSR
  simp [hRecruit.1, hRecruit.2.1, hRecruit]

theorem rankDeltaOSSR_recruit_ba_child_rank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hRecruit : t.role = .Settled ∧ s.role = .Unsettled ∧
      t.children < 2 ∧ 2 * t.rank.val + t.children + 1 < n) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.rank.val =
      2 * t.rank.val + t.children + 1 := by
  unfold rankDeltaOSSR
  simp [hRecruit.1, hRecruit.2.1, hRecruit]

theorem transitionPEM_recruit_ab_not_unsettled
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hRecruit : s.role = .Settled ∧ t.role = .Unsettled ∧
      s.children < 2 ∧ 2 * s.rank.val + s.children + 1 < n) :
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).1.role ≠ .Unsettled ∧
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).2.role ≠ .Unsettled := by
  let rankDelta : AgentState n × AgentState n → AgentState n × AgentState n :=
    rankDeltaOSSR Rmax Emax Dmax hn
  let pre := transitionPEM_prePhase4 n Rmax rankDelta s t x y
  have hrd := rankDeltaOSSR_recruit_ab_roles
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := s) (t := t) hRecruit
  have hpre := transitionPEM_prePhase4_roles
    (n := n) (trank := Rmax) (rankDelta := rankDelta)
    (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y)
  have hpre₁ : pre.1.role = .Settled := by
    dsimp [pre]
    rw [hpre.1]
    exact hrd.1
  have hpre₂ : pre.2.role = .Settled := by
    dsimp [pre]
    rw [hpre.2]
    exact hrd.2
  have hnot := transitionPEM_phase4_not_unsettled_of_both_settled
      (n := n) (Rmax := Rmax) (a := pre) (x₀ := x) (x₁ := y)
      hpre₁ hpre₂
  unfold transitionPEM
  change (transitionPEM_phase4 n Rmax pre x y).1.role ≠ .Unsettled ∧
    (transitionPEM_phase4 n Rmax pre x y).2.role ≠ .Unsettled
  exact hnot

theorem transitionPEM_recruit_ba_not_unsettled
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hRecruit : t.role = .Settled ∧ s.role = .Unsettled ∧
      t.children < 2 ∧ 2 * t.rank.val + t.children + 1 < n) :
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).1.role ≠ .Unsettled ∧
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).2.role ≠ .Unsettled := by
  let rankDelta : AgentState n × AgentState n → AgentState n × AgentState n :=
    rankDeltaOSSR Rmax Emax Dmax hn
  let pre := transitionPEM_prePhase4 n Rmax rankDelta s t x y
  have hrd := rankDeltaOSSR_recruit_ba_roles
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := s) (t := t) hRecruit
  have hpre := transitionPEM_prePhase4_roles
    (n := n) (trank := Rmax) (rankDelta := rankDelta)
    (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y)
  have hpre₁ : pre.1.role = .Settled := by
    dsimp [pre]
    rw [hpre.1]
    exact hrd.1
  have hpre₂ : pre.2.role = .Settled := by
    dsimp [pre]
    rw [hpre.2]
    exact hrd.2
  have hnot := transitionPEM_phase4_not_unsettled_of_both_settled
      (n := n) (Rmax := Rmax) (a := pre) (x₀ := x) (x₁ := y)
      hpre₁ hpre₂
  unfold transitionPEM
  change (transitionPEM_phase4 n Rmax pre x y).1.role ≠ .Unsettled ∧
    (transitionPEM_phase4 n Rmax pre x y).2.role ≠ .Unsettled
  exact hnot

theorem structuralErrorBudget_le_at_recruit_ab
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hRecruit : (C i).1.role = .Settled ∧ (C j).1.role = .Unsettled ∧
      (C i).1.children < 2 ∧
      2 * (C i).1.rank.val + (C i).1.children + 1 < n) :
    structuralErrorBudget
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) ≤
      structuralErrorBudget C := by
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hnot := transitionPEM_recruit_ab_not_unsettled
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C i).1) (t := (C j).1) (x := (C i).2) (y := (C j).2)
      hRecruit
  have hiNot : (C.step P i j i).1.role ≠ .Unsettled := by
    dsimp [P, protocolPEM, Config.step]
    simp [hij, hnot.1]
  have hjNot : (C.step P i j j).1.role ≠ .Unsettled := by
    dsimp [P, protocolPEM, Config.step]
    simp [hij, hij.symm, hnot.2]
  apply structuralErrorBudget_step_le_of_endpoint_imp
      (P := P) (C := C) hij
  · intro h
    exact False.elim (hiNot h.1)
  · intro h
    exact False.elim (hjNot h.1)

theorem structuralErrorBudget_le_at_recruit_ba
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hRecruit : (C j).1.role = .Settled ∧ (C i).1.role = .Unsettled ∧
      (C j).1.children < 2 ∧
      2 * (C j).1.rank.val + (C j).1.children + 1 < n) :
    structuralErrorBudget
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) ≤
      structuralErrorBudget C := by
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hnot := transitionPEM_recruit_ba_not_unsettled
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C i).1) (t := (C j).1) (x := (C i).2) (y := (C j).2)
      hRecruit
  have hiNot : (C.step P i j i).1.role ≠ .Unsettled := by
    dsimp [P, protocolPEM, Config.step]
    simp [hij, hnot.1]
  have hjNot : (C.step P i j j).1.role ≠ .Unsettled := by
    dsimp [P, protocolPEM, Config.step]
    simp [hij, hij.symm, hnot.2]
  apply structuralErrorBudget_step_le_of_endpoint_imp
      (P := P) (C := C) hij
  · intro h
    exact False.elim (hiNot h.1)
  · intro h
    exact False.elim (hjNot h.1)

theorem budgetTot_le_add_two_at_recruit_ab
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hRecruit : (C i).1.role = .Settled ∧ (C j).1.role = .Unsettled ∧
      (C i).1.children < 2 ∧
      2 * (C i).1.rank.val + (C i).1.children + 1 < n) :
    budgetTot
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) ≤
      budgetTot C + (2 * (n - 1) + 2 * (n - 1)) := by
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hReset := resetBudget_step_le_add_two_changed
      (P := P) (C := C) hij
  have hStruct := structuralErrorBudget_le_at_recruit_ab
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C hij hRecruit
  have hStructP : structuralErrorBudget (C.step P i j) ≤ structuralErrorBudget C := by
    simpa [P] using hStruct
  change budgetTot (C.step P i j) ≤
    budgetTot C + (2 * (n - 1) + 2 * (n - 1))
  unfold budgetTot
  omega

theorem budgetTot_le_add_two_at_recruit_ba
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hRecruit : (C j).1.role = .Settled ∧ (C i).1.role = .Unsettled ∧
      (C j).1.children < 2 ∧
      2 * (C j).1.rank.val + (C j).1.children + 1 < n) :
    budgetTot
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) ≤
      budgetTot C + (2 * (n - 1) + 2 * (n - 1)) := by
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hReset := resetBudget_step_le_add_two_changed
      (P := P) (C := C) hij
  have hStruct := structuralErrorBudget_le_at_recruit_ba
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C hij hRecruit
  have hStructP : structuralErrorBudget (C.step P i j) ≤ structuralErrorBudget C := by
    simpa [P] using hStruct
  change budgetTot (C.step P i j) ≤
    budgetTot C + (2 * (n - 1) + 2 * (n - 1))
  unfold budgetTot
  omega

theorem transitionPEM_settled_distinct_not_unsettled
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (hne : s.rank ≠ t.rank) :
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).1.role ≠ .Unsettled ∧
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).2.role ≠ .Unsettled := by
  let rankDelta : AgentState n × AgentState n → AgentState n × AgentState n :=
    rankDeltaOSSR Rmax Emax Dmax hn
  let pre := transitionPEM_prePhase4 n Rmax rankDelta s t x y
  have hrdEq :
      rankDeltaOSSR Rmax Emax Dmax hn (s, t) = (s, t) :=
    rankDeltaOSSR_settled_distinct_ranks hs ht hne
  have hrd₁ : (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled := by
    rw [hrdEq]
    exact hs
  have hrd₂ : (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled := by
    rw [hrdEq]
    exact ht
  have hpre := transitionPEM_prePhase4_roles
    (n := n) (trank := Rmax) (rankDelta := rankDelta)
    (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y)
  have hpre₁ : pre.1.role = .Settled := by
    dsimp [pre]
    rw [hpre.1]
    exact hrd₁
  have hpre₂ : pre.2.role = .Settled := by
    dsimp [pre]
    rw [hpre.2]
    exact hrd₂
  have hnot := transitionPEM_phase4_not_unsettled_of_both_settled
      (n := n) (Rmax := Rmax) (a := pre) (x₀ := x) (x₁ := y)
      hpre₁ hpre₂
  unfold transitionPEM
  change (transitionPEM_phase4 n Rmax pre x y).1.role ≠ .Unsettled ∧
    (transitionPEM_phase4 n Rmax pre x y).2.role ≠ .Unsettled
  exact hnot

theorem structuralErrorBudget_le_at_settled_distinct
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hiSet : (C i).1.role = .Settled)
    (hjSet : (C j).1.role = .Settled)
    (hrank : (C i).1.rank ≠ (C j).1.rank) :
    structuralErrorBudget
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) ≤
      structuralErrorBudget C := by
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hnot := transitionPEM_settled_distinct_not_unsettled
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C i).1) (t := (C j).1) (x := (C i).2) (y := (C j).2)
      hiSet hjSet hrank
  have hiNot : (C.step P i j i).1.role ≠ .Unsettled := by
    dsimp [P, protocolPEM, Config.step]
    simp [hij, hnot.1]
  have hjNot : (C.step P i j j).1.role ≠ .Unsettled := by
    dsimp [P, protocolPEM, Config.step]
    simp [hij, hij.symm, hnot.2]
  apply structuralErrorBudget_step_le_of_endpoint_imp
      (P := P) (C := C) hij
  · intro h
    exact False.elim (hiNot h.1)
  · intro h
    exact False.elim (hjNot h.1)

theorem rankDeltaOSSR_error_timeout_roles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hsNotReset : s.role ≠ .Resetting)
    (htNotReset : t.role ≠ .Resetting)
    (hNoRecruitST : ¬(s.role = .Settled ∧ t.role = .Unsettled ∧
       s.children < 2 ∧ 2 * s.rank.val + s.children + 1 < n))
    (hNoRecruitTS : ¬(t.role = .Settled ∧ s.role = .Unsettled ∧
       t.children < 2 ∧ 2 * t.rank.val + t.children + 1 < n))
    (hTimeout : (s.role = .Unsettled ∧ s.errorcount ≤ 1) ∨
      (t.role = .Unsettled ∧ t.errorcount ≤ 1)) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
      (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting := by
  unfold rankDeltaOSSR
  rcases hTimeout with hsTimeout | htTimeout
  · rcases hsTimeout with ⟨hsRole, hsErr⟩
    have hsDec : s.errorcount - 1 = 0 := by omega
    simp [htNotReset, hsRole, hsDec]
    split_ifs with h
    · exfalso
      exact hNoRecruitTS ⟨h.1, hsRole, by omega, h.2.2⟩
    all_goals constructor <;> rfl
  · rcases htTimeout with ⟨htRole, htErr⟩
    have htDec : t.errorcount - 1 = 0 := by omega
    simp [hsNotReset, htRole, htDec]
    split_ifs with h
    · exfalso
      exact hNoRecruitST ⟨h.1, htRole, by omega, h.2.2⟩
    all_goals constructor <;> rfl

theorem transitionPEM_error_timeout_roles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n} {x y : Opinion}
    (hsNotReset : s.role ≠ .Resetting)
    (htNotReset : t.role ≠ .Resetting)
    (hNoRecruitST : ¬(s.role = .Settled ∧ t.role = .Unsettled ∧
       s.children < 2 ∧ 2 * s.rank.val + s.children + 1 < n))
    (hNoRecruitTS : ¬(t.role = .Settled ∧ s.role = .Unsettled ∧
       t.children < 2 ∧ 2 * t.rank.val + t.children + 1 < n))
    (hTimeout : (s.role = .Unsettled ∧ s.errorcount ≤ 1) ∨
      (t.role = .Unsettled ∧ t.errorcount ≤ 1)) :
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).1.role = .Resetting ∧
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((s, x), (t, y))).2.role = .Resetting := by
  let rankDelta : AgentState n × AgentState n → AgentState n × AgentState n :=
    rankDeltaOSSR Rmax Emax Dmax hn
  let p := transitionPEM_prePhase4 n Rmax rankDelta s t x y
  have hrd := rankDeltaOSSR_error_timeout_roles
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := s) (t := t) hsNotReset htNotReset hNoRecruitST hNoRecruitTS hTimeout
  have hpre := transitionPEM_prePhase4_roles
    (n := n) (trank := Rmax) (rankDelta := rankDelta)
    (s₀ := s) (s₁ := t) (x₀ := x) (x₁ := y)
  have hp₁ : p.1.role = .Resetting := by
    dsimp [p]
    rw [hpre.1]
    exact hrd.1
  have hp₂ : p.2.role = .Resetting := by
    dsimp [p]
    rw [hpre.2]
    exact hrd.2
  have hnot : ¬(p.1.role = .Settled ∧ p.2.role = .Settled) := by
    intro h
    rw [hp₁] at h
    cases h.1
  unfold transitionPEM
  change (transitionPEM_phase4 n Rmax p x y).1.role = .Resetting ∧
    (transitionPEM_phase4 n Rmax p x y).2.role = .Resetting
  rw [transitionPEM_phase4_of_not_both_settled hnot]
  exact ⟨hp₁, hp₂⟩

/-- A fresh collision reset strictly decreases the certified collision budget.

The theorem is for the concrete coupled PEM transition using `rankDeltaOSSR`.
The two scheduled agents are Settled with the same rank, so the ranking
subprotocol makes both Resetting; phase 4 is then disabled, and every other
agent is unchanged. -/
theorem resetBudget_strict_decrease_at_collision
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hi : (C i).1.role = .Settled)
    (hj : (C j).1.role = .Settled)
    (hrank : (C i).1.rank = (C j).1.rank) :
    resetBudget
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) <
      resetBudget C := by
  classical
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P i j
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
  have hOther : ∀ w : Fin n, w ≠ i → w ≠ j → C' w = C w := by
    intro w hwi hwj
    dsimp [C', P, Config.step]
    simp [hij, hwi, hwj]
  have hsubset : sameRankSettledPairs C' ⊆ (sameRankSettledPairs C).erase (i, j) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    rcases hp' with ⟨hpne, hp1Set, hp2Set, hprank⟩
    have hp1_ne_i : p.1 ≠ i := by
      intro h
      rw [h] at hp1Set
      rw [hiReset] at hp1Set
      cases hp1Set
    have hp1_ne_j : p.1 ≠ j := by
      intro h
      rw [h] at hp1Set
      rw [hjReset] at hp1Set
      cases hp1Set
    have hp2_ne_i : p.2 ≠ i := by
      intro h
      rw [h] at hp2Set
      rw [hiReset] at hp2Set
      cases hp2Set
    have hp2_ne_j : p.2 ≠ j := by
      intro h
      rw [h] at hp2Set
      rw [hjReset] at hp2Set
      cases hp2Set
    have hp_ne_pair : p ≠ (i, j) := by
      intro h
      exact hp1_ne_i (congrArg Prod.fst h)
    have hstate1 : C' p.1 = C p.1 := hOther p.1 hp1_ne_i hp1_ne_j
    have hstate2 : C' p.2 = C p.2 := hOther p.2 hp2_ne_i hp2_ne_j
    apply Finset.mem_erase.mpr
    constructor
    · exact hp_ne_pair
    · rw [sameRankSettledPairs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hpne, ?_, ?_, ?_⟩
      · rw [← hstate1]
        exact hp1Set
      · rw [← hstate2]
        exact hp2Set
      · rw [← hstate1, ← hstate2]
        exact hprank
  have hijmem : (i, j) ∈ sameRankSettledPairs C := by
    rw [sameRankSettledPairs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hij, hi, hj, hrank⟩
  have hle := Finset.card_le_card hsubset
  have herase :
      ((sameRankSettledPairs C).erase (i, j)).card =
        (sameRankSettledPairs C).card - 1 :=
    Finset.card_erase_of_mem hijmem
  change (sameRankSettledPairs C').card < (sameRankSettledPairs C).card
  rw [herase] at hle
  have hpos : 0 < (sameRankSettledPairs C).card :=
    Finset.card_pos.mpr ⟨(i, j), hijmem⟩
  omega

theorem structuralErrorBudget_strict_decrease_of_endpoint_reset
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j w : Fin n}
    (hij : i ≠ j)
    (hwEndpoint : w = i ∨ w = j)
    (hwTimeout : (C w).1.role = .Unsettled ∧ (C w).1.errorcount ≤ 1)
    (hiReset : (C.step P i j i).1.role = .Resetting)
    (hjReset : (C.step P i j j).1.role = .Resetting) :
    structuralErrorBudget (C.step P i j) < structuralErrorBudget C := by
  classical
  let C' : Config (AgentState n) Opinion n := C.step P i j
  have hiReset' : (C' i).1.role = .Resetting := hiReset
  have hjReset' : (C' j).1.role = .Resetting := hjReset
  have hOther : ∀ u : Fin n, u ≠ i → u ≠ j → C' u = C u := by
    intro u hui huj
    dsimp [C', Config.step]
    simp [hij, hui, huj]
  have hsubset : structuralErrorAgents C' ⊆ (structuralErrorAgents C).erase w := by
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).2
    rcases hu' with ⟨huRole, huErr⟩
    have hu_ne_i : u ≠ i := by
      intro h
      rw [h] at huRole
      rw [hiReset'] at huRole
      cases huRole
    have hu_ne_j : u ≠ j := by
      intro h
      rw [h] at huRole
      rw [hjReset'] at huRole
      cases huRole
    have hu_ne_w : u ≠ w := by
      rcases hwEndpoint with rfl | rfl
      · exact hu_ne_i
      · exact hu_ne_j
    have hstate : C' u = C u := hOther u hu_ne_i hu_ne_j
    apply Finset.mem_erase.mpr
    constructor
    · exact hu_ne_w
    · rw [structuralErrorAgents, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← hstate]
        exact huRole
      · rw [← hstate]
        exact huErr
  have hwmem : w ∈ structuralErrorAgents C := by
    rw [structuralErrorAgents, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hwTimeout.1, hwTimeout.2⟩
  have hle := Finset.card_le_card hsubset
  have herase :
      ((structuralErrorAgents C).erase w).card =
        (structuralErrorAgents C).card - 1 :=
    Finset.card_erase_of_mem hwmem
  change (structuralErrorAgents C').card < (structuralErrorAgents C).card
  rw [herase] at hle
  have hpos : 0 < (structuralErrorAgents C).card :=
    Finset.card_pos.mpr ⟨w, hwmem⟩
  omega

/-- The error-monitoring reset branch strictly decreases the structural error
budget.  These hypotheses are the Part 4 guard: no endpoint is already
Resetting, neither recruitment direction is enabled, and some Unsettled
endpoint has counter `0` or `1`. -/
theorem structuralErrorBudget_strict_decrease_at_error
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) {i j : Fin n}
    (hij : i ≠ j)
    (hiNotReset : (C i).1.role ≠ .Resetting)
    (hjNotReset : (C j).1.role ≠ .Resetting)
    (hNoRecruitIJ : ¬((C i).1.role = .Settled ∧ (C j).1.role = .Unsettled ∧
       (C i).1.children < 2 ∧ 2 * (C i).1.rank.val + (C i).1.children + 1 < n))
    (hNoRecruitJI : ¬((C j).1.role = .Settled ∧ (C i).1.role = .Unsettled ∧
       (C j).1.children < 2 ∧ 2 * (C j).1.rank.val + (C j).1.children + 1 < n))
    (hTimeout : ((C i).1.role = .Unsettled ∧ (C i).1.errorcount ≤ 1) ∨
      ((C j).1.role = .Unsettled ∧ (C j).1.errorcount ≤ 1)) :
    structuralErrorBudget
        (C.step
          (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) i j) <
      structuralErrorBudget C := by
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hdelta := transitionPEM_error_timeout_roles
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C i).1) (t := (C j).1) (x := (C i).2) (y := (C j).2)
      hiNotReset hjNotReset hNoRecruitIJ hNoRecruitJI hTimeout
  have hiReset : (C.step P i j i).1.role = .Resetting := by
    dsimp [P, protocolPEM, Config.step]
    simp [hij, hdelta.1]
  have hjReset : (C.step P i j j).1.role = .Resetting := by
    dsimp [P, protocolPEM, Config.step]
    simp [hij, hij.symm, hdelta.2]
  rcases hTimeout with hiTimeout | hjTimeout
  · exact structuralErrorBudget_strict_decrease_of_endpoint_reset
      (P := P) (C := C) (i := i) (j := j) (w := i) hij (Or.inl rfl)
      hiTimeout hiReset hjReset
  · exact structuralErrorBudget_strict_decrease_of_endpoint_reset
      (P := P) (C := C) (i := i) (j := j) (w := j) hij (Or.inr rfl)
      hjTimeout hiReset hjReset

end SSEM
