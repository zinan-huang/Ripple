import Mathlib.Data.Nat.Log
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal

namespace SSEM

variable {τ : ℕ}

def FreshResettingAt {n : ℕ} (Dmax : ℕ)
    (C : Config (AgentState n) Opinion n) (w : Fin n) : Prop :=
  (C w).1.role = .Resetting ∧
  (C w).1.resetcount = 0 ∧
  (C w).1.delaytimer = Dmax

def pairEndpoints {n : ℕ} : List (Fin n × Fin n) → Finset (Fin n)
  | [] => ∅
  | (u, v) :: ps => insert u (insert v (pairEndpoints ps))

def PairListDisjoint {n : ℕ} : List (Fin n × Fin n) → Prop
  | [] => True
  | (u, v) :: ps =>
      u ≠ v ∧ u ∉ pairEndpoints ps ∧ v ∉ pairEndpoints ps ∧ PairListDisjoint ps

def pairSources {n : ℕ} : List (Fin n × Fin n) → Finset (Fin n)
  | [] => ∅
  | (u, _) :: ps => insert u (pairSources ps)

def pairTargets {n : ℕ} : List (Fin n × Fin n) → Finset (Fin n)
  | [] => ∅
  | (_, v) :: ps => insert v (pairTargets ps)

theorem pairEndpoints_eq_sources_union_targets {n : ℕ}
    (pairs : List (Fin n × Fin n)) :
    pairEndpoints pairs = pairSources pairs ∪ pairTargets pairs := by
  induction pairs with
  | nil => simp [pairEndpoints, pairSources, pairTargets]
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      ext x
      simp [pairEndpoints, pairSources, pairTargets, ih, or_left_comm]

theorem pairSources_subset_endpoints {n : ℕ}
    (pairs : List (Fin n × Fin n)) :
    pairSources pairs ⊆ pairEndpoints pairs := by
  intro x hx
  rw [pairEndpoints_eq_sources_union_targets]
  exact Finset.mem_union_left _ hx

theorem pairTargets_subset_endpoints {n : ℕ}
    (pairs : List (Fin n × Fin n)) :
    pairTargets pairs ⊆ pairEndpoints pairs := by
  intro x hx
  rw [pairEndpoints_eq_sources_union_targets]
  exact Finset.mem_union_right _ hx

theorem runPairs_eq_of_not_pairEndpoints
    {n : ℕ} {Q X Y : Type*}
    (P : Protocol Q X Y) (C : Config Q X n)
    (pairs : List (Fin n × Fin n)) {w : Fin n}
    (hw : w ∉ pairEndpoints pairs) :
    runPairs P C pairs w = C w := by
  induction pairs generalizing C with
  | nil =>
      simp [runPairs]
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      have hwu : w ≠ u := by
        intro h
        subst w
        exact hw (by simp [pairEndpoints])
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw (by simp [pairEndpoints])
      have hnot_tail : w ∉ pairEndpoints ps := by
        intro htail
        exact hw (by simp [pairEndpoints, htail])
      rw [runPairs_cons]
      rw [ih (C.step P u v) hnot_tail]
      by_cases huv : u = v
      · simp [Config.step, huv]
      · simp [Config.step, huv, hwu, hwv]

def highSet {n : ℕ} (C : Config (AgentState n) Opinion n) (k : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun w : Fin n =>
    (C w).1.role = .Resetting ∧ k ≤ (C w).1.resetcount

def leaderSet {n : ℕ} (C : Config (AgentState n) Opinion n) :
    Finset (Fin n) :=
  Finset.univ.filter fun w : Fin n => (C w).1.leader = .L

theorem mem_highSet {n : ℕ} {C : Config (AgentState n) Opinion n}
    {k : ℕ} {w : Fin n} :
    w ∈ highSet C k ↔
      (C w).1.role = .Resetting ∧ k ≤ (C w).1.resetcount := by
  simp [highSet]

theorem mem_leaderSet {n : ℕ} {C : Config (AgentState n) Opinion n}
    {w : Fin n} :
    w ∈ leaderSet C ↔ (C w).1.leader = .L := by
  simp [leaderSet]

theorem highSet_mono_threshold {n : ℕ} (C : Config (AgentState n) Opinion n)
    {k l : ℕ} (hkl : k ≤ l) :
    highSet C l ⊆ highSet C k := by
  intro w hw
  rw [mem_highSet] at hw ⊢
  exact ⟨hw.1, Nat.le_trans hkl hw.2⟩

theorem highSet_card_eq_n_all {n : ℕ}
    {C : Config (AgentState n) Opinion n} {k : ℕ}
    (hcard : (highSet C k).card = n) :
    ∀ w : Fin n, (C w).1.role = .Resetting ∧ k ≤ (C w).1.resetcount := by
  classical
  intro w
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ highSet C k := by
    intro x hx
    by_contra hxhigh
    have hproper : (highSet C k).card < (Finset.univ : Finset (Fin n)).card := by
      have hssub : highSet C k ⊂ (Finset.univ : Finset (Fin n)) := by
        exact Finset.ssubset_iff.mpr
          ⟨x, hxhigh, by intro y hy; exact Finset.mem_univ y⟩
      exact Finset.card_lt_card hssub
    simp [hcard] at hproper
  have hw : w ∈ highSet C k := hsub (Finset.mem_univ w)
  exact mem_highSet.mp hw

theorem highSet_card_le_n {n : ℕ}
    (C : Config (AgentState n) Opinion n) (k : ℕ) :
    (highSet C k).card ≤ n := by
  simpa [Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_univ (highSet C k))

theorem card_add_min_complement_eq_min_double {a n : ℕ}
    (ha : a ≤ n) :
    a + Nat.min a (n - a) = Nat.min n (2 * a) := by
  by_cases hdouble : 2 * a ≤ n
  · have hleft : a ≤ n - a := by omega
    have hmin₂ : Nat.min n (2 * a) = 2 * a := Nat.min_eq_right hdouble
    simp [Nat.min_eq_left hleft, hmin₂]
    omega
  · have hright : n - a ≤ a := by omega
    have hmin₂ : Nat.min n (2 * a) = n := Nat.min_eq_left (by omega)
    simp [Nat.min_eq_right hright, hmin₂]
    omega

theorem min_pow_succ_mul_le_min_pow_mul_min_double
    {n m g : ℕ} (_hn : 0 < n) :
    Nat.min n (2 ^ (g + 1) * m) ≤
      Nat.min n (2 ^ g * Nat.min n (2 * m)) := by
  by_cases hdouble : 2 * m ≤ n
  · have hmin : Nat.min n (2 * m) = 2 * m := Nat.min_eq_right hdouble
    have hpow :
        2 ^ (g + 1) * m = 2 ^ g * (2 * m) := by
      rw [pow_succ]
      simp [Nat.mul_assoc]
    simp [hmin, hpow]
  · have hn_le : n ≤ 2 * m := by omega
    have hmin : Nat.min n (2 * m) = n := Nat.min_eq_left hn_le
    have hpow_ge : 1 ≤ 2 ^ g := by
      induction g with
      | zero => simp
      | succ g ih =>
          rw [pow_succ]
          have hmul : 1 * 1 ≤ 2 ^ g * 2 :=
            Nat.mul_le_mul ih (by omega : 1 ≤ 2)
          simpa using hmul
    have hn_le_mul : n ≤ 2 ^ g * n := by
      simpa using Nat.mul_le_mul_right n hpow_ge
    have hrhs : Nat.min n (2 ^ g * Nat.min n (2 * m)) = n := by
      simp [hmin, Nat.min_eq_left hn_le_mul]
    rw [hrhs]
    exact Nat.min_le_left _ _

theorem exists_pair_list_of_disjoint_eq_card
    {n : ℕ} (A T : Finset (Fin n))
    (hcard : A.card = T.card)
    (hdis : Disjoint A T) :
    ∃ pairs : List (Fin n × Fin n),
      PairListDisjoint pairs ∧
      pairSources pairs = A ∧
      pairTargets pairs = T := by
  classical
  revert T
  refine Finset.induction_on A ?base ?step
  · intro T hcard hdis
    have hT : T = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa using hcard.symm
    refine ⟨[], ?_, ?_, ?_⟩
    · trivial
    · simp [pairSources]
    · simp [pairTargets, hT]
  · intro a A ha ih T hcard hdis
    have hTpos : 0 < T.card := by
      rw [Finset.card_insert_of_notMem ha] at hcard
      omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hTpos
    have hcard_tail : A.card = (T.erase t).card := by
      rw [Finset.card_erase_of_mem ht]
      rw [Finset.card_insert_of_notMem ha] at hcard
      omega
    have hdis_tail : Disjoint A (T.erase t) := by
      rw [Finset.disjoint_left]
      intro x hxA hxT
      exact (Finset.disjoint_left.mp hdis) (Finset.mem_insert_of_mem hxA)
        (Finset.mem_of_mem_erase hxT)
    obtain ⟨pairs, hpair_dis, hsources, htargets⟩ := ih (T.erase t) hcard_tail hdis_tail
    have hat : a ≠ t := by
      intro h
      subst t
      exact (Finset.disjoint_left.mp hdis) (Finset.mem_insert_self a A) ht
    have ha_not_T : a ∉ T := by
      intro haT
      exact (Finset.disjoint_left.mp hdis) (Finset.mem_insert_self a A) haT
    have ht_not_A : t ∉ A := by
      intro htA
      exact (Finset.disjoint_left.mp hdis) (Finset.mem_insert_of_mem htA) ht
    have ha_not_end : a ∉ pairEndpoints pairs := by
      rw [pairEndpoints_eq_sources_union_targets, hsources, htargets]
      simp [ha, ha_not_T]
    have ht_not_end : t ∉ pairEndpoints pairs := by
      rw [pairEndpoints_eq_sources_union_targets, hsources, htargets]
      simp [ht_not_A]
    refine ⟨(a, t) :: pairs, ?_, ?_, ?_⟩
    · exact ⟨hat, ha_not_end, ht_not_end, hpair_dis⟩
    · simp [pairSources, hsources]
    · simp [pairTargets, htargets, ht]

theorem exists_pair_list_with_optional_leftover
    {n : ℕ} (A : Finset (Fin n)) :
    ∃ pairs : List (Fin n × Fin n), ∃ leftover : Option (Fin n),
      PairListDisjoint pairs ∧
      (∀ w : Fin n, w ∈ pairEndpoints pairs → w ∈ A) ∧
      (∀ w : Fin n, leftover = some w → w ∈ A ∧ w ∉ pairEndpoints pairs) ∧
      (∀ w : Fin n, w ∈ A → w ∈ pairEndpoints pairs ∨ leftover = some w) := by
  classical
  refine Finset.induction_on A ?base ?step
  · refine ⟨[], none, ?_, ?_, ?_, ?_⟩
    · trivial
    · intro w hw
      simp [pairEndpoints] at hw
    · intro w h
      cases h
    · intro w hw
      simp at hw
  · intro a A ha ih
    obtain ⟨pairs, leftover, hdis, hend_sub, hleft, hcover⟩ := ih
    cases leftover with
    | none =>
        have ha_not_end : a ∉ pairEndpoints pairs := by
          intro ha_end
          exact ha (hend_sub a ha_end)
        refine ⟨pairs, some a, hdis, ?_, ?_, ?_⟩
        · intro w hw
          exact Finset.mem_insert_of_mem (hend_sub w hw)
        · intro w hsome
          injection hsome with hw
          subst w
          exact ⟨Finset.mem_insert_self a A, ha_not_end⟩
        · intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with hwa | hwA
          · subst w
            exact Or.inr rfl
          · rcases hcover w hwA with hwEnd | hnone
            · exact Or.inl hwEnd
            · cases hnone
    | some b =>
        have hbA_end := hleft b rfl
        have hab : a ≠ b := by
          intro h
          subst b
          exact ha hbA_end.1
        have ha_not_end : a ∉ pairEndpoints pairs := by
          intro ha_end
          exact ha (hend_sub a ha_end)
        refine ⟨(a, b) :: pairs, none, ?_, ?_, ?_, ?_⟩
        · exact ⟨hab, ha_not_end, hbA_end.2, hdis⟩
        · intro w hw
          simp only [pairEndpoints, Finset.mem_insert] at hw
          rcases hw with hwa | hwb_or_tail
          · subst w
            exact Finset.mem_insert_self a A
          · rcases hwb_or_tail with hwb | hwTail
            · subst w
              exact Finset.mem_insert_of_mem hbA_end.1
            · exact Finset.mem_insert_of_mem (hend_sub w hwTail)
        · intro w h
          cases h
        · intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with hwa | hwA
          · subst w
            exact Or.inl (by simp [pairEndpoints])
          · rcases hcover w hwA with hwEnd | hsome
            · exact Or.inl (by simp [pairEndpoints, hwEnd])
            · injection hsome with hwb
              subst w
              exact Or.inl (by simp [pairEndpoints])

def optionCount {α : Type*} : Option α → ℕ
  | none => 0
  | some _ => 1

theorem exists_pair_list_with_optional_leftover_count
    {n : ℕ} (A : Finset (Fin n)) :
    ∃ pairs : List (Fin n × Fin n), ∃ leftover : Option (Fin n),
      PairListDisjoint pairs ∧
      (∀ w : Fin n, w ∈ pairEndpoints pairs → w ∈ A) ∧
      (∀ w : Fin n, leftover = some w → w ∈ A ∧ w ∉ pairEndpoints pairs) ∧
      (∀ w : Fin n, w ∈ A → w ∈ pairEndpoints pairs ∨ leftover = some w) ∧
      A.card = 2 * (pairTargets pairs).card + optionCount leftover := by
  classical
  refine Finset.induction_on A ?base ?step
  · refine ⟨[], none, ?_, ?_, ?_, ?_, ?_⟩
    · trivial
    · intro w hw
      simp [pairEndpoints] at hw
    · intro w h
      cases h
    · intro w hw
      simp at hw
    · simp [pairTargets, optionCount]
  · intro a A ha ih
    obtain ⟨pairs, leftover, hdis, hend_sub, hleft, hcover, hcount⟩ := ih
    cases leftover with
    | none =>
        have ha_not_end : a ∉ pairEndpoints pairs := by
          intro ha_end
          exact ha (hend_sub a ha_end)
        refine ⟨pairs, some a, hdis, ?_, ?_, ?_, ?_⟩
        · intro w hw
          exact Finset.mem_insert_of_mem (hend_sub w hw)
        · intro w hsome
          injection hsome with hw
          subst w
          exact ⟨Finset.mem_insert_self a A, ha_not_end⟩
        · intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with hwa | hwA
          · subst w
            exact Or.inr rfl
          · rcases hcover w hwA with hwEnd | hnone
            · exact Or.inl hwEnd
            · cases hnone
        · rw [Finset.card_insert_of_notMem ha, hcount]
          simp [optionCount]
    | some b =>
        have hbA_end := hleft b rfl
        have hab : a ≠ b := by
          intro h
          subst b
          exact ha hbA_end.1
        have ha_not_end : a ∉ pairEndpoints pairs := by
          intro ha_end
          exact ha (hend_sub a ha_end)
        have hb_not_target : b ∉ pairTargets pairs := by
          intro hbT
          exact hbA_end.2 (pairTargets_subset_endpoints pairs hbT)
        refine ⟨(a, b) :: pairs, none, ?_, ?_, ?_, ?_, ?_⟩
        · exact ⟨hab, ha_not_end, hbA_end.2, hdis⟩
        · intro w hw
          simp only [pairEndpoints, Finset.mem_insert] at hw
          rcases hw with hwa | hwb_or_tail
          · subst w
            exact Finset.mem_insert_self a A
          · rcases hwb_or_tail with hwb | hwTail
            · subst w
              exact Finset.mem_insert_of_mem hbA_end.1
            · exact Finset.mem_insert_of_mem (hend_sub w hwTail)
        · intro w h
          cases h
        · intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with hwa | hwA
          · subst w
            exact Or.inl (by simp [pairEndpoints])
          · rcases hcover w hwA with hwEnd | hsome
            · exact Or.inl (by simp [pairEndpoints, hwEnd])
            · injection hsome with hwb
              subst w
              exact Or.inl (by simp [pairEndpoints])
        · rw [Finset.card_insert_of_notMem ha, hcount]
          simp [pairTargets, hb_not_target, optionCount]
          omega

theorem rankDeltaOSSR_resetting_pos_resetting_zero
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 1 < s.resetcount) (ht_rc : t.resetcount = 0) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = s.resetcount - 1 := by
  have hpred : s.resetcount - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, ht_rc, hpred]
  by_cases hLL : s.leader = .L ∧ t.leader = .L <;> simp [hLL]

theorem step_resetting_pos_resetting_zero
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_resetting_pos_resetting_zero
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2

theorem propagate_reset_step_partner_rc_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting) (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C.step P r v v).1.role = .Resetting ∧
    (C.step P r v v).1.resetcount = (C r).1.resetcount - 1 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_propagate_reset_recruit_rc
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).2.role = .Settled) := by
    intro ⟨_, h2⟩
    rw [h_rd.1] at h2
    exact Role.noConfusion h2
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C r).2) (x₁ := (C v).2) h_not_both
  have h_snd := Config.step_snd_state P C hrv hrv.symm
  refine ⟨?_, ?_⟩
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2

theorem propagate_reset_step_sender_rc_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting) (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C.step P r v r).1.role = .Resetting ∧
    (C.step P r v r).1.resetcount = (C r).1.resetcount - 1 := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_propagate_reset_spreader_rc
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C r).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C hrv
  refine ⟨?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2

theorem propagate_reset_spreader_state_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C₀ r).1.role = .Resetting) (hr_rc : 0 < (C₀ r).1.resetcount)
    (hv_not : (C₀ v).1.role ≠ .Resetting) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C₀.step P r v r).1.role = .Resetting ∧
    (C₀.step P r v r).1.resetcount = (C₀ r).1.resetcount - 1 ∧
    (C₀.step P r v r).1.leader = (C₀ r).1.leader := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_propagate_reset_spreader
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_rd_leader := rankDeltaOSSR_propagate_reset_spreader_leader
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C₀ r).2) (x₁ := (C₀ v).2) h_not_both
  have h_fst := Config.step_fst_state P C₀ hrv
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd_leader

theorem propagate_reset_step_answer_trace_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n) {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting) (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting)
    (hr_ans : (C r).1.answer = majorityAnswer C) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ((C.step P r v) r).1.answer = majorityAnswer (C.step P r v) ∧
    ((C.step P r v) v).1.answer = majorityAnswer (C.step P r v) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have h_rd_snd := rankDeltaOSSR_propagate_reset_recruit_rc
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_rd_fst := rankDeltaOSSR_propagate_reset_spreader_rc
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_ans :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).1.answer =
          (C r).1.answer ∧
      (rankDeltaOSSR Rmax Emax Dmax hn ((C r).1, (C v).1)).2.answer =
          (C v).1.answer := by
    unfold rankDeltaOSSR
    simp only [hr_res, true_or, ite_true]
    have hpr := propagateReset_answer_preserved (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (C r).1 (C v).1
    refine ⟨?_, ?_⟩
    · exact hpr.1
    · split_ifs <;> exact hpr.2
  have h_pre := transitionPEM_prePhase4_propagate_answer
    (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := (C r).1) (s₁ := (C v).1) (x₀ := (C r).2) (x₁ := (C v).2)
    (ans := majorityAnswer C)
    hr_res hv_not h_rd_fst.1 h_rd_snd.1
    (hr_ans ▸ h_ans.1) h_ans.2 (majorityAnswer_ne_phi C)
  have h_pre_not_settled :
      ¬ ((transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C r).1 (C v).1 (C r).2 (C v).2).1.role = .Settled ∧
          (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C r).1 (C v).1 (C r).2 (C v).2).2.role = .Settled) := by
    have hpre_struct := transitionPEM_prePhase4_structural
      (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C r).1) (s₁ := (C v).1) (x₀ := (C r).2) (x₁ := (C v).2)
    rintro ⟨h1, _⟩
    rw [hpre_struct.1, h_rd_fst.1] at h1
    exact Role.noConfusion h1
  have h_delta_ans :
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C r).1, (C r).2), ((C v).1, (C v).2))).1.answer = majorityAnswer C ∧
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C r).1, (C r).2), ((C v).1, (C v).2))).2.answer = majorityAnswer C := by
    rw [transitionPEM_eq]
    rw [transitionPEM_phase4_of_not_both_settled h_pre_not_settled]
    exact h_pre
  have h_maj : majorityAnswer (C.step P r v) = majorityAnswer C := by
    rw [hP]
    exact majorityAnswer_step_eq C r v
  have h_fst := Config.step_fst_state P C hrv
  have h_snd := Config.step_snd_state P C hrv hrv.symm
  refine ⟨?_, ?_⟩
  · rw [h_maj]
    rw [congrArg AgentState.answer h_fst]
    show (P.δ (C r, C v)).1.answer = majorityAnswer C
    simp only [hP, protocolPEM]
    exact h_delta_ans.1
  · rw [h_maj]
    rw [congrArg AgentState.answer h_snd]
    show (P.δ (C r, C v)).2.answer = majorityAnswer C
    simp only [hP, protocolPEM]
    exact h_delta_ans.2

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = (C u).1.leader := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_role
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hu_res hv_res hu_rc hv_rc hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_LF_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_LF_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_FF_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_FF_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_F hv_F hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_LL_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_LL_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_L hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_pos_any_zero_gt_one_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_any_zero_gt_one_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

theorem transitionPEM_prePhase4_resetting_pair_answer
    {n trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion} {ans : Answer}
    (hs₀_res : s₀.role = .Resetting)
    (hs₁_res : s₁.role = .Resetting)
    (hr₀_res : (rankDelta (s₀, s₁)).1.role = .Resetting)
    (hr₁_res : (rankDelta (s₀, s₁)).2.role = .Resetting)
    (hr₀_ans : (rankDelta (s₀, s₁)).1.answer = ans)
    (hr₁_ans : (rankDelta (s₀, s₁)).2.answer = ans)
    (hans_ne : ans ≠ .phi) :
    (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1.answer = ans ∧
    (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2.answer = ans := by
  simp [transitionPEM_prePhase4, hs₀_res, hs₁_res, hr₀_res, hr₁_res,
    hr₀_ans, hr₁_ans, hans_ne]

theorem step_resetting_pair_majority_answer
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting)
    (hv_res : (C v).1.role = .Resetting)
    (hrd_u_res :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Resetting)
    (hrd_v_res :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Resetting)
    (hu_ans : (C u).1.answer = majorityAnswer C)
    (hv_ans : (C v).1.answer = majorityAnswer C) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C.step P u v u).1.answer = majorityAnswer (C.step P u v) ∧
    (C.step P u v v).1.answer = majorityAnswer (C.step P u v) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have h_rd_ans :=
    rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) (C u).1 (C v).1
  have h_pre :=
    transitionPEM_prePhase4_resetting_pair_answer
      (n := n) (trank := τ)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C u).1) (s₁ := (C v).1)
      (x₀ := (C u).2) (x₁ := (C v).2)
      (ans := majorityAnswer C)
      hu_res hv_res hrd_u_res hrd_v_res
      (by rw [h_rd_ans.1]; exact hu_ans)
      (by rw [h_rd_ans.2]; exact hv_ans)
      (majorityAnswer_ne_phi C)
  have h_pre_not_settled :
      ¬ ((transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C u).1 (C v).1 (C u).2 (C v).2).1.role = .Settled ∧
          (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C u).1 (C v).1 (C u).2 (C v).2).2.role = .Settled) := by
    have hstruct := transitionPEM_prePhase4_structural
      (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C u).1) (s₁ := (C v).1) (x₀ := (C u).2) (x₁ := (C v).2)
    rintro ⟨hsettled, _⟩
    rw [hstruct.1, hrd_u_res] at hsettled
    exact Role.noConfusion hsettled
  have h_delta :
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C u).1, (C u).2), ((C v).1, (C v).2))).1.answer = majorityAnswer C ∧
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C u).1, (C u).2), ((C v).1, (C v).2))).2.answer = majorityAnswer C := by
    rw [transitionPEM_eq]
    rw [transitionPEM_phase4_of_not_both_settled h_pre_not_settled]
    exact h_pre
  have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
    rw [hP]
    exact majorityAnswer_step_eq C u v
  have hfst := Config.step_fst_state P C huv
  have hsnd := Config.step_snd_state P C huv huv.symm
  constructor
  · rw [hmaj]
    rw [congrArg AgentState.answer hfst]
    show (P.δ (C u, C v)).1.answer = majorityAnswer C
    simpa [P] using h_delta.1
  · rw [hmaj]
    rw [congrArg AgentState.answer hsnd]
    show (P.δ (C u, C v)).2.answer = majorityAnswer C
    simpa [P] using h_delta.2

set_option maxHeartbeats 4000000 in
-- Splits the target into the three reset-propagation cases and normalizes all
-- of them to the next lower high-fuel threshold.
theorem step_high_source_any_target_next
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hk : 0 < k)
    (hu_high : u ∈ highSet C (k + 1)) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    k ≤ (C' u).1.resetcount ∧
    (C' v).1.role = .Resetting ∧
    k ≤ (C' v).1.resetcount ∧
    (∀ w : Fin n, w ≠ u → w ≠ v → C' w = C w) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hu_state := mem_highSet.mp hu_high
  have hu_res : (C u).1.role = .Resetting := hu_state.1
  have hu_floor : k + 1 ≤ (C u).1.resetcount := hu_state.2
  have hu_pos : 0 < (C u).1.resetcount := by omega
  have hu_gt_one : 1 < (C u).1.resetcount := by omega
  have hothers : ∀ w : Fin n, w ≠ u → w ≠ v → C.step P u v w = C w := by
    intro w hwu hwv
    simp [Config.step, huv, hwu, hwv]
  by_cases hv_res : (C v).1.role = .Resetting
  · by_cases hv_pos : 0 < (C v).1.resetcount
    · have hstep := step_both_rc_pos_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (by omega : 0 < Dmax) C huv hu_res hv_res hu_pos hv_pos
      refine ⟨hstep.1, ?_, hstep.2.1, ?_, hothers⟩
      · rw [hstep.2.2.1]
        exact le_max_of_le_left (by omega)
      · rw [hstep.2.2.2.1]
        exact le_max_of_le_left (by omega)
    · have hv_zero : (C v).1.resetcount = 0 := by omega
      have hstep := step_resetting_pos_resetting_zero
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C huv hu_res hv_res hu_gt_one hv_zero
      refine ⟨hstep.1, ?_, hstep.2.1, ?_, hothers⟩
      · rw [hstep.2.2.1]
        omega
      · rw [hstep.2.2.2]
        omega
  · have hsender := propagate_reset_step_sender_rc_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C huv hu_res hu_pos hv_res
    have hpartner := propagate_reset_step_partner_rc_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C huv hu_res hu_pos hv_res
    refine ⟨hsender.1, ?_, hpartner.1, ?_, hothers⟩
    · rw [hsender.2]
      omega
    · rw [hpartner.2]
      omega

set_option maxHeartbeats 8000000 in
-- Large case split over the PEM reset step and answer epidemic endpoint cases.
theorem step_high_source_any_target_answer_next
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hk : 0 < k)
    (hu_high : u ∈ highSet C (k + 1))
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    ∀ w : Fin n, (C' w).1.role = .Resetting →
      (C' w).1.answer = majorityAnswer C' := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have hstep_high := step_high_source_any_target_next
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hk hu_high
  have hu_state := mem_highSet.mp hu_high
  have hu_res : (C u).1.role = .Resetting := hu_state.1
  have hu_pos : 0 < (C u).1.resetcount := by omega
  have hu_gt_one : 1 < (C u).1.resetcount := by omega
  have hu_ans : (C u).1.answer = majorityAnswer C :=
    hAllAns u hu_res
  have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
    rw [hP]
    exact majorityAnswer_step_eq C u v
  have hendpoint :
      (C.step P u v u).1.answer = majorityAnswer (C.step P u v) ∧
      (C.step P u v v).1.answer = majorityAnswer (C.step P u v) := by
    by_cases hv_res : (C v).1.role = .Resetting
    · have hv_ans : (C v).1.answer = majorityAnswer C :=
        hAllAns v hv_res
      by_cases hv_pos : 0 < (C v).1.resetcount
      · have hrd := rankDeltaOSSR_both_rc_pos_role
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hu_res hv_res hu_pos hv_pos (by omega : 0 < Dmax)
        exact step_resetting_pair_majority_answer
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C huv hu_res hv_res hrd.1 hrd.2.1 hu_ans hv_ans
      · have hv_zero : (C v).1.resetcount = 0 := by omega
        have hrd := rankDeltaOSSR_resetting_pos_resetting_zero
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hu_res hv_res hu_gt_one hv_zero
        exact step_resetting_pair_majority_answer
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C huv hu_res hv_res hrd.1 hrd.2.1 hu_ans hv_ans
    · exact propagate_reset_step_answer_trace_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hu_pos hv_res hu_ans
  change ∀ w : Fin n, (C.step P u v w).1.role = .Resetting →
    (C.step P u v w).1.answer = majorityAnswer (C.step P u v)
  intro w hwres
  by_cases hwu : w = u
  · subst w
    exact hendpoint.1
  · by_cases hwv : w = v
    · subst w
      exact hendpoint.2
    · have hothers : C.step P u v w = C w := by
        simpa [P] using hstep_high.2.2.2.2 w hwu hwv
      rw [hothers] at hwres ⊢
      rw [hmaj]
      exact hAllAns w hwres

set_option maxHeartbeats 6000000 in
-- Large case split over the PEM reset step and leader dedup endpoint cases.
theorem step_high_source_any_target_source_leader_next
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hk : 0 < k)
    (hu_high : u ∈ highSet C (k + 1))
    (hu_L : (C u).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C.step P u v u).1.leader = .L := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hu_state := mem_highSet.mp hu_high
  have hu_res : (C u).1.role = .Resetting := hu_state.1
  have hu_pos : 0 < (C u).1.resetcount := by omega
  have hu_gt_one : 1 < (C u).1.resetcount := by omega
  by_cases hv_res : (C v).1.role = .Resetting
  · by_cases hv_pos : 0 < (C v).1.resetcount
    · have hstep := step_both_rc_pos_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (by omega : 0 < Dmax) C huv hu_res hv_res hu_pos hv_pos
      change (C.step P u v u).1.leader = .L
      rw [hstep.2.2.2.2]
      exact hu_L
    · have hv_zero : (C v).1.resetcount = 0 := by omega
      have hstep := step_L_pos_any_zero_gt_one_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C huv hu_res hv_res hu_gt_one hv_zero hu_L
      change (C.step P u v u).1.leader = .L
      exact hstep.2.2.2.2.1
  · have htrace := propagate_reset_spreader_state_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C huv hu_res hu_pos hv_res
    change (C.step P u v u).1.leader = .L
    rw [htrace.2.2]
    exact hu_L

set_option maxHeartbeats 8000000 in
-- A fueled `.L`/`.L` tournament match demotes exactly the target endpoint.
theorem step_LL_pos_floor_answer_leaderSet
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hAllFloor : ∀ w : Fin n,
      (C w).1.role = .Resetting ∧ d + 1 ≤ (C w).1.resetcount)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C)
    (hu_L : (C u).1.leader = .L)
    (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (∀ w : Fin n, (C' w).1.role = .Resetting ∧ d ≤ (C' w).1.resetcount) ∧
    (∀ w : Fin n, (C' w).1.role = .Resetting →
      (C' w).1.answer = majorityAnswer C') ∧
    leaderSet C' = (leaderSet C).erase v := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have hu_res : (C u).1.role = .Resetting := (hAllFloor u).1
  have hv_res : (C v).1.role = .Resetting := (hAllFloor v).1
  have hu_pos : 0 < (C u).1.resetcount := by
    have h := (hAllFloor u).2
    omega
  have hv_pos : 0 < (C v).1.resetcount := by
    have h := (hAllFloor v).2
    omega
  have hstep := step_both_rc_pos_LL_trank
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (by omega : 0 < Dmax) C huv hu_res hv_res hu_pos hv_pos hu_L hv_L
  change
    (∀ w : Fin n, (C.step P u v w).1.role = .Resetting ∧
      d ≤ (C.step P u v w).1.resetcount) ∧
    (∀ w : Fin n, (C.step P u v w).1.role = .Resetting →
      (C.step P u v w).1.answer = majorityAnswer (C.step P u v)) ∧
    leaderSet (C.step P u v) = (leaderSet C).erase v
  refine ⟨?_, ?_, ?_⟩
  · intro w
    by_cases hwu : w = u
    · subst w
      refine ⟨hstep.1, ?_⟩
      rw [hstep.2.2.1]
      have hu_floor := (hAllFloor u).2
      have hv_floor := (hAllFloor v).2
      exact le_max_of_le_left (by omega)
    · by_cases hwv : w = v
      · subst w
        refine ⟨hstep.2.1, ?_⟩
        rw [hstep.2.2.2.1]
        have hu_floor := (hAllFloor u).2
        have hv_floor := (hAllFloor v).2
        exact le_max_of_le_right (by omega)
      · have hkeep : C.step P u v w = C w := by
          simp [Config.step, huv, hwu, hwv]
        rw [hkeep]
        have hw_floor := (hAllFloor w).2
        exact ⟨(hAllFloor w).1, by omega⟩
  · exact step_high_source_any_target_answer_next
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C huv hd
      (by
        rw [mem_highSet]
        exact ⟨hu_res, (hAllFloor u).2⟩)
      hAllAns
  · ext w
    rw [mem_leaderSet]
    rw [Finset.mem_erase, mem_leaderSet]
    by_cases hwu : w = u
    · subst w
      rw [hstep.2.2.2.2.1]
      constructor
      · intro _
        exact ⟨huv, hu_L⟩
      · intro _
        rfl
    · by_cases hwv : w = v
      · subst w
        rw [hstep.2.2.2.2.2]
        constructor
        · intro h
          cases h
        · intro h
          exact False.elim (h.1 rfl)
      · have hkeep : C.step P u v w = C w := by
          simp [Config.step, huv, hwu, hwv]
        rw [hkeep]
        constructor
        · intro hwL
          exact ⟨hwv, hwL⟩
        · intro h
          exact h.2

set_option maxHeartbeats 6000000 in
-- The leader component of a fueled `.L`/`.L` match does not need floor data.
theorem step_LL_pos_leaderSet
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting)
    (hv_res : (C v).1.role = .Resetting)
    (hu_pos : 0 < (C u).1.resetcount)
    (hv_pos : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L)
    (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    leaderSet (C.step P u v) = (leaderSet C).erase v := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_both_rc_pos_LL_trank
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_pos hv_pos hu_L hv_L
  change leaderSet (C.step P u v) = (leaderSet C).erase v
  ext w
  rw [mem_leaderSet]
  rw [Finset.mem_erase, mem_leaderSet]
  by_cases hwu : w = u
  · subst w
    rw [hstep.2.2.2.2.1]
    constructor
    · intro _
      exact ⟨huv, hu_L⟩
    · intro _
      rfl
  · by_cases hwv : w = v
    · subst w
      rw [hstep.2.2.2.2.2]
      constructor
      · intro h
        cases h
      · intro h
        exact False.elim (h.1 rfl)
    · have hkeep : C.step P u v w = C w := by
        simp [Config.step, huv, hwu, hwv]
      rw [hkeep]
      constructor
      · intro hwL
        exact ⟨hwv, hwL⟩
      · intro h
        exact h.2

theorem rankDeltaOSSR_both_rc_pos_FL_trace
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hs_F : s.leader = .F) (ht_L : t.leader = .L)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .L := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  have h_role := propagateReset_both_rc_pos_stay
    (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_rc := propagateReset_both_rc_pos_rc
    (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader₁ := propagateReset_both_rc_pos_leader_fst
    (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader₂ := propagateReset_both_rc_pos_leader_snd
    (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have hnot_dedup :
      ¬((propagateReset Emax Dmax hn s t).1.leader = .L ∧
        (propagateReset Emax Dmax hn s t).2.leader = .L ∧
        (propagateReset Emax Dmax hn s t).1.role = .Resetting ∧
        (propagateReset Emax Dmax hn s t).2.role = .Resetting) := by
    intro h
    have hF : (propagateReset Emax Dmax hn s t).1.leader = .F := by
      rw [h_leader₁, hs_F]
    rw [h.1] at hF
    cases hF
  simp only [hnot_dedup, ite_false]
  exact ⟨h_role.1, h_role.2, h_rc.1, h_rc.2,
    by rw [h_leader₁, hs_F], by rw [h_leader₂, ht_L]⟩

set_option maxHeartbeats 4000000 in
-- Lifting the missing F/L positive-resetcount trace through `transitionPEM`
-- exposes the same nested structural tuple as the existing LF/LL cases.
theorem step_both_rc_pos_FL
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_F : (C u).1.leader = .F) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .L := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_FL_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_F hv_L hDmax
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 12000000 in
-- If the scheduled positive-resetcount pair does not contain two leaders,
-- the unique leader invariant is preserved.
theorem step_both_rc_pos_preserves_uniqueLeader
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃! ℓ : Fin n, (C.step P u v ℓ).1.leader = .L := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  rcases hUnique with ⟨ℓ, hℓL, huniq⟩
  have hothers : ∀ w : Fin n, w ≠ u → w ≠ v → C.step P u v w = C w := by
    intro w hwu hwv
    simp [Config.step, huv, hwu, hwv]
  have unique_of_leaderSet_eq
      (hEq : leaderSet (C.step P u v) = leaderSet C) :
      ∃! x : Fin n, (C.step P u v x).1.leader = .L := by
    refine ⟨ℓ, ?_, ?_⟩
    · have hmem : ℓ ∈ leaderSet (C.step P u v) := by
        rw [hEq, mem_leaderSet]
        exact hℓL
      exact mem_leaderSet.mp hmem
    · intro x hx
      apply huniq
      have hmem : x ∈ leaderSet C := by
        rw [← hEq, mem_leaderSet]
        exact hx
      exact mem_leaderSet.mp hmem
  cases hu_leader : (C u).1.leader with
  | L =>
      cases hv_leader : (C v).1.leader with
      | L =>
          have hu_eq : u = ℓ := huniq u hu_leader
          have hv_eq : v = ℓ := huniq v hv_leader
          exact False.elim (huv (by rw [hu_eq, hv_eq]))
      | F =>
          have hstep := step_both_rc_pos_LF_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C huv hu_res hv_res hu_rc hv_rc hu_leader hv_leader
          have hEq : leaderSet (C.step P u v) = leaderSet C := by
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwu : w = u
            · subst w
              rw [hstep.2.2.2.2.1]
              rw [hu_leader]
            · by_cases hwv : w = v
              · subst w
                rw [hstep.2.2.2.2.2]
                rw [hv_leader]
              · rw [hothers w hwu hwv]
          exact unique_of_leaderSet_eq hEq
  | F =>
      cases hv_leader : (C v).1.leader with
      | L =>
          have hstep := step_both_rc_pos_FL
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C huv hu_res hv_res hu_rc hv_rc hu_leader hv_leader
          have hEq : leaderSet (C.step P u v) = leaderSet C := by
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwu : w = u
            · subst w
              rw [hstep.2.2.2.2.1]
              rw [hu_leader]
            · by_cases hwv : w = v
              · subst w
                rw [hstep.2.2.2.2.2]
                rw [hv_leader]
              · rw [hothers w hwu hwv]
          exact unique_of_leaderSet_eq hEq
      | F =>
          have hstep := step_both_rc_pos_FF_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C huv hu_res hv_res hu_rc hv_rc hu_leader hv_leader
          have hEq : leaderSet (C.step P u v) = leaderSet C := by
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwu : w = u
            · subst w
              rw [hstep.2.2.2.2.1]
              rw [hu_leader]
            · by_cases hwv : w = v
              · subst w
                rw [hstep.2.2.2.2.2]
                rw [hv_leader]
              · rw [hothers w hwu hwv]
          exact unique_of_leaderSet_eq hEq

theorem step_preserves_uniform_answer_of_no_reset_entry_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer} (_hm : m ≠ .phi)
    {C : Config (AgentState n) Opinion n} {a b : Fin n} (hab : a ≠ b)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (h_no_entry₀ :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).1.role = .Resetting ∧
         (C a).1.role ≠ .Resetting))
    (h_no_entry₁ :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).2.role = .Resetting ∧
         (C b).1.role ≠ .Resetting))
    (h_not_both_settled :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).1.role = .Settled ∧
         (rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).2.role = .Settled)) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) a b)
        w).1.answer = m := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  have h_rd_ans :=
    rankDeltaOSSR_answer_preserved (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) (C a).1 (C b).1
  have hrd0_m :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).1.answer = m := by
    rw [h_rd_ans.1]
    exact hAllM a
  have hrd1_m :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C a).1, (C b).1)).2.answer = m := by
    rw [h_rd_ans.2]
    exact hAllM b
  have h_pre :
      (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
          (C a).1 (C b).1 (C a).2 (C b).2).1.answer = m ∧
      (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
          (C a).1 (C b).1 (C a).2 (C b).2).2.answer = m := by
    simp only [transitionPEM_prePhase4]
    rw [if_neg h_no_entry₀]
    rw [if_neg h_no_entry₁]
    split_ifs <;>
      simp_all
  have h_pre_not_settled :
      ¬ ((transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C a).1 (C b).1 (C a).2 (C b).2).1.role = .Settled ∧
          (transitionPEM_prePhase4 n τ (rankDeltaOSSR Rmax Emax Dmax hn)
            (C a).1 (C b).1 (C a).2 (C b).2).2.role = .Settled) := by
    have hstruct := transitionPEM_prePhase4_structural
      (trank := τ) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C a).1) (s₁ := (C b).1) (x₀ := (C a).2) (x₁ := (C b).2)
    rw [hstruct.1, hstruct.2.2.2.2.2.2.1]
    exact h_not_both_settled
  have h_delta :
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C a).1, (C a).2), ((C b).1, (C b).2))).1.answer = m ∧
      (transitionPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (((C a).1, (C a).2), ((C b).1, (C b).2))).2.answer = m := by
    rw [transitionPEM_eq, transitionPEM_phase4_of_not_both_settled h_pre_not_settled]
    exact h_pre
  intro w
  by_cases hwa : w = a
  · subst hwa
    rw [Config.step_fst_state P C hab]
    show (P.δ (C w, C b)).1.answer = m
    simp only [hP, protocolPEM]
    exact h_delta.1
  · by_cases hwb : w = b
    · subst hwb
      rw [Config.step_snd_state P C hab (fun h => hab h.symm)]
      show (P.δ (C a, C w)).2.answer = m
      simp only [hP, protocolPEM]
      exact h_delta.2
    · have : (C.step P a b) w = C w := by
        simp [Config.step, hab, hwa, hwb]
      rw [this]
      exact hAllM w

theorem step_resetting_pos_zero_preserves_uniform_answer
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    (hm : m ≠ .phi)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (hu_res : (C u).1.role = .Resetting)
    (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount)
    (hv_rc : (C v).1.resetcount = 0) :
    ∀ w : Fin n,
      (C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1.answer = m := by
  refine
    step_preserves_uniform_answer_of_no_reset_entry_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hm huv hAllM
      (by rintro ⟨_, hu_not⟩; exact hu_not hu_res)
      (by rintro ⟨_, hv_not⟩; exact hv_not hv_res)
      ?_
  have hrd := rankDeltaOSSR_resetting_pos_resetting_zero
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc
  intro hboth
  rw [hrd.1] at hboth
  exact Role.noConfusion hboth.1

set_option maxHeartbeats 4000000 in
theorem step_L_pos_F_zero_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F ∧
    (C' v).1.delaytimer =
      (if (C u).1.resetcount = 1 then (C v).1.delaytimer - 1 else (C v).1.delaytimer) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_F_zero_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F hv_dt hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_F_pos_F_zero_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_F_zero_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_F hv_F hv_dt hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

theorem step_both_resetting_pos_preserves_uniform_answer_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer} (hm : m ≠ .phi)
    {C : Config (AgentState n) Opinion n} {a b : Fin n} (hab : a ≠ b)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (ha_role : (C a).1.role = .Resetting)
    (hb_role : (C b).1.role = .Resetting)
    (ha_rc : 0 < (C a).1.resetcount)
    (hb_rc : 0 < (C b).1.resetcount)
    (hDmax : 0 < Dmax) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) a b)
        w).1.answer = m := by
  exact
    step_preserves_uniform_answer_of_no_reset_entry_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hm hab hAllM
      (by
        rintro ⟨_, ha_not⟩
        exact ha_not ha_role)
      (by
        rintro ⟨_, hb_not⟩
        exact hb_not hb_role)
      (rankDeltaOSSR_both_resetting_pos_not_both_settled
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        ha_role hb_role ha_rc hb_rc hDmax)

set_option maxHeartbeats 4000000 in
theorem step_L_zero_F_pos_gt_one_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 1 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_zero_F_pos_gt_one_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

theorem step_L_zero_any_pos_preserves_uniform_answer_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer} (hm : m ≠ .phi)
    {C : Config (AgentState n) Opinion n} {u v : Fin n} (huv : u ≠ v)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (hu_res : (C u).1.role = .Resetting)
    (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0)
    (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L)
    (hu_dt : 1 < (C u).1.delaytimer)
    (hDmax : 0 < Dmax) :
    ∀ w : Fin n,
      ((C.step (protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) w).1.answer = m := by
  classical
  refine
    step_preserves_uniform_answer_of_no_reset_entry_trank
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hm huv hAllM
      (by rintro ⟨_, hu_not⟩; exact hu_not hu_res)
      (by rintro ⟨_, hv_not⟩; exact hv_not hv_res)
      ?_
  cases hv_leader : (C v).1.leader with
  | L =>
      have h :=
        rankDeltaOSSR_L_zero_L_pos_trace
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hu_res hv_res hu_rc hv_rc hu_L hv_leader hu_dt hDmax
      rintro ⟨h1, _⟩
      rw [h.1] at h1
      cases h1
  | F =>
      have h :=
        rankDeltaOSSR_L_zero_F_pos_trace
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hu_res hv_res hu_rc hv_rc hu_L hv_leader hu_dt hDmax
      rintro ⟨h1, _⟩
      rw [h.1] at h1
      cases h1

set_option maxHeartbeats 8000000 in
-- A disjoint list of `.L`/`.L` fueled matches demotes exactly its targets.
theorem leader_tournament_pair_list_leaderSet
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (pairs : List (Fin n × Fin n))
    (hdis : PairListDisjoint pairs)
    (hEndLeader :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → w ∈ leaderSet C)
    (hEndReset :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting)
    (hEndPos :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    leaderSet (runPairs P C pairs) = leaderSet C \ pairTargets pairs := by
  classical
  induction pairs generalizing C with
  | nil =>
      intro
      simp [runPairs, pairTargets]
  | cons p ps ih =>
      intro
      rcases p with ⟨u, v⟩
      rcases hdis with ⟨huv, hu_not_tail, hv_not_tail, hdis_tail⟩
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hu_mem : u ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      have hv_mem : v ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      have hstep_set : leaderSet (C.step P u v) = (leaderSet C).erase v :=
        step_LL_pos_leaderSet
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C huv
          (hEndReset u hu_mem) (hEndReset v hv_mem)
          (hEndPos u hu_mem) (hEndPos v hv_mem)
          (mem_leaderSet.mp (hEndLeader u hu_mem))
          (mem_leaderSet.mp (hEndLeader v hv_mem))
      have hothers :
          ∀ w : Fin n, w ≠ u → w ≠ v → C.step P u v w = C w := by
        intro w hwu hwv
        simp [Config.step, huv, hwu, hwv]
      have hEndLeader_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps →
            w ∈ leaderSet (C.step P u v) := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        rw [mem_leaderSet]
        rw [hothers w hwu hwv]
        exact mem_leaderSet.mp (hEndLeader w (by simp [pairEndpoints, hw]))
      have hEndReset_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps →
            (C.step P u v w).1.role = .Resetting := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        rw [hothers w hwu hwv]
        exact hEndReset w (by simp [pairEndpoints, hw])
      have hEndPos_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps →
            0 < (C.step P u v w).1.resetcount := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        rw [hothers w hwu hwv]
        exact hEndPos w (by simp [pairEndpoints, hw])
      have htail := ih (C.step P u v) hdis_tail
        hEndLeader_tail hEndReset_tail hEndPos_tail
      change leaderSet (runPairs P (C.step P u v) ps) =
        leaderSet C \ pairTargets ((u, v) :: ps)
      rw [htail, hstep_set]
      ext w
      simp only [pairTargets, Finset.mem_sdiff, Finset.mem_erase,
        Finset.mem_insert, ne_eq, not_or]
      constructor
      · intro h
        exact ⟨h.1.2, h.1.1, h.2⟩
      · intro h
        exact ⟨⟨h.2.1, h.1⟩, h.2.2⟩

set_option maxHeartbeats 8000000 in
-- A whole disjoint generation can be run sequentially because every later
-- endpoint is outside the earlier pair endpoints and is therefore unchanged.
theorem generation_pair_list_high
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (pairs : List (Fin n × Fin n))
    (U : Finset (Fin n))
    (hdis : PairListDisjoint pairs)
    (hk : 0 < k)
    (hU_high : ∀ w : Fin n, w ∈ U → w ∈ highSet C (k + 1))
    (hSrc_high :
      ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C (k + 1))
    (hU_untouched : ∀ w : Fin n, w ∈ U → w ∉ pairEndpoints pairs) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (∀ w : Fin n, w ∈ U → w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∈ pairSources pairs →
      w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∈ pairTargets pairs →
      w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C pairs w = C w) := by
  classical
  induction pairs generalizing C U with
  | nil =>
      intro
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w hwU
        simpa using (highSet_mono_threshold C (by omega : k ≤ k + 1)
          (hU_high w hwU))
      · intro w hw
        simp [pairSources] at hw
      · intro w hw
        simp [pairTargets] at hw
      · intro w _hw
        simp [runPairs]
  | cons p ps ih =>
      intro
      rcases p with ⟨u, v⟩
      rcases hdis with ⟨huv, hu_not_tail, hv_not_tail, hdis_tail⟩
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hu_source : u ∈ pairSources ((u, v) :: ps) := by
        simp [pairSources]
      have hstep := step_high_source_any_target_next
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hk (hSrc_high u hu_source)
      have hu_step : u ∈ highSet (C.step P u v) k := by
        rw [mem_highSet]
        exact ⟨by simpa [P] using hstep.1,
          by simpa [P] using hstep.2.1⟩
      have hv_step : v ∈ highSet (C.step P u v) k := by
        rw [mem_highSet]
        exact ⟨by simpa [P] using hstep.2.2.1,
          by simpa [P] using hstep.2.2.2.1⟩
      have hothers :
          ∀ w : Fin n, w ≠ u → w ≠ v → C.step P u v w = C w := by
        intro w hwu hwv
        simpa [P] using hstep.2.2.2.2 w hwu hwv
      have hU_high₁ :
          ∀ w : Fin n, w ∈ U → w ∈ highSet (C.step P u v) (k + 1) := by
        intro w hwU
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hU_untouched u hwU (by simp [pairEndpoints])
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hU_untouched v hwU (by simp [pairEndpoints])
        rw [mem_highSet]
        rw [hothers w hwu hwv]
        exact mem_highSet.mp (hU_high w hwU)
      have hSrc_high₁ :
          ∀ w : Fin n, w ∈ pairSources ps →
            w ∈ highSet (C.step P u v) (k + 1) := by
        intro w hwSrc
        have hwEnd : w ∈ pairEndpoints ps :=
          pairSources_subset_endpoints ps hwSrc
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hwEnd
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hwEnd
        rw [mem_highSet]
        rw [hothers w hwu hwv]
        exact mem_highSet.mp (hSrc_high w (by simp [pairSources, hwSrc]))
      have hU_untouched₁ :
          ∀ w : Fin n, w ∈ U → w ∉ pairEndpoints ps := by
        intro w hwU hwEnd
        exact hU_untouched w hwU (by simp [pairEndpoints, hwEnd])
      obtain ⟨hU_fin, hSrc_fin, hTgt_fin, hunch_fin⟩ :=
        ih (C.step P u v) U hdis_tail hU_high₁ hSrc_high₁ hU_untouched₁
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w hwU
        change w ∈ highSet (runPairs P (C.step P u v) ps) k
        exact hU_fin w hwU
      · intro w hwSrc
        change w ∈ highSet (runPairs P (C.step P u v) ps) k
        simp only [pairSources, Finset.mem_insert] at hwSrc
        rcases hwSrc with hwu_eq | hwSrcTail
        · subst w
          rw [mem_highSet] at hu_step ⊢
          rw [hunch_fin u hu_not_tail]
          exact hu_step
        · exact hSrc_fin w hwSrcTail
      · intro w hwTgt
        change w ∈ highSet (runPairs P (C.step P u v) ps) k
        simp only [pairTargets, Finset.mem_insert] at hwTgt
        rcases hwTgt with hwv_eq | hwTgtTail
        · subst w
          rw [mem_highSet] at hv_step ⊢
          rw [hunch_fin v hv_not_tail]
          exact hv_step
        · exact hTgt_fin w hwTgtTail
      · intro w hwNotEnd
        change runPairs P (C.step P u v) ps w = C w
        have hnot_tail : w ∉ pairEndpoints ps := by
          intro hwTail
          exact hwNotEnd (by simp [pairEndpoints, hwTail])
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hwNotEnd (by simp [pairEndpoints])
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hwNotEnd (by simp [pairEndpoints])
        rw [hunch_fin w hnot_tail]
        exact hothers w hwu hwv

set_option maxHeartbeats 8000000 in
-- List induction repeatedly transports the answer invariant through disjoint pairs.
theorem generation_pair_list_answer
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (pairs : List (Fin n × Fin n))
    (hdis : PairListDisjoint pairs)
    (hk : 0 < k)
    (hSrc_high :
      ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C (k + 1))
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∀ w : Fin n, ((runPairs P C pairs) w).1.role = .Resetting →
      ((runPairs P C pairs) w).1.answer =
        majorityAnswer (runPairs P C pairs) := by
  classical
  induction pairs generalizing C with
  | nil =>
      intro
      change ∀ w : Fin n, (C w).1.role = .Resetting →
        (C w).1.answer = majorityAnswer C
      exact hAllAns
  | cons p ps ih =>
      intro
      rcases p with ⟨u, v⟩
      rcases hdis with ⟨huv, hu_not_tail, hv_not_tail, hdis_tail⟩
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hu_source : u ∈ pairSources ((u, v) :: ps) := by
        simp [pairSources]
      have hstep_high := step_high_source_any_target_next
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hk (hSrc_high u hu_source)
      have hstep_ans := step_high_source_any_target_answer_next
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hk (hSrc_high u hu_source) hAllAns
      have hothers :
          ∀ w : Fin n, w ≠ u → w ≠ v → C.step P u v w = C w := by
        intro w hwu hwv
        simpa [P] using hstep_high.2.2.2.2 w hwu hwv
      have hSrc_high₁ :
          ∀ w : Fin n, w ∈ pairSources ps →
            w ∈ highSet (C.step P u v) (k + 1) := by
        intro w hwSrc
        have hwEnd : w ∈ pairEndpoints ps :=
          pairSources_subset_endpoints ps hwSrc
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hwEnd
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hwEnd
        rw [mem_highSet]
        rw [hothers w hwu hwv]
        exact mem_highSet.mp (hSrc_high w (by simp [pairSources, hwSrc]))
      obtain hAns_tail :=
        ih (C.step P u v) hdis_tail hSrc_high₁ (by
          simpa [P] using hstep_ans)
      change ∀ w : Fin n,
        ((runPairs P (C.step P u v) ps) w).1.role = .Resetting →
          ((runPairs P (C.step P u v) ps) w).1.answer =
            majorityAnswer (runPairs P (C.step P u v) ps)
      exact hAns_tail

set_option maxHeartbeats 16000000 in
-- One tournament round pairs the current leaders and leaves at most half
-- rounded up as leaders, while spending one unit of reset fuel.
theorem leader_tournament_round
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d)
    (C : Config (AgentState n) Opinion n)
    (hAllFloor : ∀ w : Fin n,
      (C w).1.role = .Resetting ∧ d + 1 ≤ (C w).1.resetcount)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    ∃ Lround : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := runPairs P C Lround
      (∀ w : Fin n, (C' w).1.role = .Resetting ∧ d ≤ (C' w).1.resetcount) ∧
      (∀ w : Fin n, (C' w).1.role = .Resetting →
        (C' w).1.answer = majorityAnswer C') ∧
      (leaderSet C').card ≤ ((leaderSet C).card + 1) / 2 ∧
      (0 < (leaderSet C).card → 0 < (leaderSet C').card) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let A : Finset (Fin n) := leaderSet C
  obtain ⟨pairs, leftover, hdis, hend_sub, hleft, hcover, hcount⟩ :=
    exists_pair_list_with_optional_leftover_count (A := A)
  refine ⟨pairs, ?_, ?_, ?_, ?_⟩
  · let U : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ pairEndpoints pairs
    have hU_high : ∀ w : Fin n, w ∈ U → w ∈ highSet C (d + 1) := by
      intro w _hw
      rw [mem_highSet]
      exact hAllFloor w
    have hSrc_high :
        ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C (d + 1) := by
      intro w hwSrc
      rw [mem_highSet]
      exact hAllFloor w
    have hU_untouched :
        ∀ w : Fin n, w ∈ U → w ∉ pairEndpoints pairs := by
      intro w hw
      exact (Finset.mem_sdiff.mp hw).2
    have hgen := generation_pair_list_high
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C pairs U hdis hd hU_high hSrc_high hU_untouched
    change
      (∀ w : Fin n, w ∈ U → w ∈ highSet (runPairs P C pairs) d) ∧
      (∀ w : Fin n, w ∈ pairSources pairs →
        w ∈ highSet (runPairs P C pairs) d) ∧
      (∀ w : Fin n, w ∈ pairTargets pairs →
        w ∈ highSet (runPairs P C pairs) d) ∧
      (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C pairs w = C w) at hgen
    obtain ⟨hU_fin, hSrc_fin, hTgt_fin, hunchanged⟩ := hgen
    change ∀ w : Fin n,
      ((runPairs P C pairs) w).1.role = .Resetting ∧
        d ≤ ((runPairs P C pairs) w).1.resetcount
    intro w
    by_cases hwEnd : w ∈ pairEndpoints pairs
    · have hwUnion : w ∈ pairSources pairs ∪ pairTargets pairs := by
        simpa [pairEndpoints_eq_sources_union_targets pairs] using hwEnd
      rcases Finset.mem_union.mp hwUnion with hwSrc | hwTgt
      · exact mem_highSet.mp (hSrc_fin w hwSrc)
      · exact mem_highSet.mp (hTgt_fin w hwTgt)
    · have hwU : w ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwEnd⟩
      exact mem_highSet.mp (hU_fin w hwU)
  · exact generation_pair_list_answer
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C pairs hdis hd
      (by
        intro w hwSrc
        rw [mem_highSet]
        exact hAllFloor w)
      hAllAns
  · have hEndLeader :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → w ∈ leaderSet C := by
      intro w hw
      exact hend_sub w hw
    have hEndReset :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting := by
      intro w _hw
      exact (hAllFloor w).1
    have hEndPos :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount := by
      intro w _hw
      have hw := (hAllFloor w).2
      omega
    have hLeader := leader_tournament_pair_list_leaderSet
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (by omega : 0 < Dmax) C pairs hdis hEndLeader hEndReset hEndPos
    change leaderSet (runPairs P C pairs) = leaderSet C \ pairTargets pairs at hLeader
    have hTsub : pairTargets pairs ⊆ A := by
      intro w hw
      exact hend_sub w (pairTargets_subset_endpoints pairs hw)
    have hcard_sdiff :
        (A \ pairTargets pairs).card = A.card - (pairTargets pairs).card :=
      Finset.card_sdiff_of_subset hTsub
    have hleader_card :
        (leaderSet (runPairs P C pairs)).card =
          A.card - (pairTargets pairs).card := by
      rw [hLeader]
      exact hcard_sdiff
    rw [hleader_card]
    change A.card - (pairTargets pairs).card ≤ (A.card + 1) / 2
    cases leftover with
    | none =>
        simp only [optionCount, add_zero] at hcount
        rw [hcount]
        omega
    | some z =>
        simp only [optionCount] at hcount
        rw [hcount]
        omega
  · intro hposA
    have hEndLeader :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → w ∈ leaderSet C := by
      intro w hw
      exact hend_sub w hw
    have hEndReset :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting := by
      intro w _hw
      exact (hAllFloor w).1
    have hEndPos :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount := by
      intro w _hw
      have hw := (hAllFloor w).2
      omega
    have hLeader := leader_tournament_pair_list_leaderSet
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (by omega : 0 < Dmax) C pairs hdis hEndLeader hEndReset hEndPos
    change leaderSet (runPairs P C pairs) = leaderSet C \ pairTargets pairs at hLeader
    have hTsub : pairTargets pairs ⊆ A := by
      intro w hw
      exact hend_sub w (pairTargets_subset_endpoints pairs hw)
    have hcard_sdiff :
        (A \ pairTargets pairs).card = A.card - (pairTargets pairs).card :=
      Finset.card_sdiff_of_subset hTsub
    have hleader_card :
        (leaderSet (runPairs P C pairs)).card =
          A.card - (pairTargets pairs).card := by
      rw [hLeader]
      exact hcard_sdiff
    rw [hleader_card]
    have hposA' : 0 < A.card := by
      simpa [A] using hposA
    change 0 < A.card - (pairTargets pairs).card
    cases leftover with
    | none =>
        simp only [optionCount, add_zero] at hcount
        rw [hcount]
        omega
    | some z =>
        simp only [optionCount] at hcount
        rw [hcount]
        omega

set_option maxHeartbeats 16000000 in
-- Iterating tournament rounds for `g` generations leaves at most one leader.
theorem leader_tournament_iter
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d) :
    ∀ g (C : Config (AgentState n) Opinion n),
      (∀ w : Fin n, (C w).1.role = .Resetting ∧
        d + g ≤ (C w).1.resetcount) →
      (∀ w : Fin n, (C w).1.role = .Resetting →
        (C w).1.answer = majorityAnswer C) →
      (leaderSet C).card ≤ 2 ^ g →
      0 < (leaderSet C).card →
      ∃ Ltourn : List (Fin n × Fin n),
        let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        let C' := runPairs P C Ltourn
        (∀ w : Fin n, (C' w).1.role = .Resetting ∧
          d ≤ (C' w).1.resetcount) ∧
        (∀ w : Fin n, (C' w).1.role = .Resetting →
          (C' w).1.answer = majorityAnswer C') ∧
        (leaderSet C').card ≤ 1 ∧
        0 < (leaderSet C').card := by
  intro g
  induction g with
  | zero =>
      intro C hAllFloor hAllAns hBound hPos
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · change ∀ w : Fin n, (C w).1.role = .Resetting ∧
          d ≤ (C w).1.resetcount
        intro w
        have hw := hAllFloor w
        simpa using hw
      · change ∀ w : Fin n, (C w).1.role = .Resetting →
          (C w).1.answer = majorityAnswer C
        exact hAllAns
      · simpa using hBound
      · simpa using hPos
  | succ g ih =>
      intro C hAllFloor hAllAns hBound hPos
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hRoundFloor :
          ∀ w : Fin n, (C w).1.role = .Resetting ∧
            (d + g) + 1 ≤ (C w).1.resetcount := by
        intro w
        have hw := hAllFloor w
        refine ⟨hw.1, ?_⟩
        omega
      obtain ⟨L₁, hFloor₁, hAns₁, hCard₁, hPos₁⟩ :=
        leader_tournament_round
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (d := d + g) hDmax (by omega : 0 < d + g)
          C hRoundFloor hAllAns
      let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
      have hFloor₁' :
          ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
            d + g ≤ (C₁ w).1.resetcount := by
        simpa [C₁, P] using hFloor₁
      have hAns₁' :
          ∀ w : Fin n, (C₁ w).1.role = .Resetting →
            (C₁ w).1.answer = majorityAnswer C₁ := by
        simpa [C₁, P] using hAns₁
      have hBound₁ : (leaderSet C₁).card ≤ 2 ^ g := by
        have hCard₁' : (leaderSet C₁).card ≤
            ((leaderSet C).card + 1) / 2 := by
          simpa [C₁, P] using hCard₁
        have hhalf : ((leaderSet C).card + 1) / 2 ≤ 2 ^ g := by
          have hpow : 2 ^ (g + 1) = 2 * 2 ^ g := by
            rw [pow_succ]
            omega
          rw [hpow] at hBound
          omega
        exact Nat.le_trans hCard₁' hhalf
      have hPos₁' : 0 < (leaderSet C₁).card := by
        simpa [C₁, P] using hPos₁ hPos
      obtain ⟨L₂, hFloor₂, hAns₂, hCard₂, hPos₂⟩ :=
        ih C₁ hFloor₁' hAns₁' hBound₁ hPos₁'
      refine ⟨L₁ ++ L₂, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_append]
        change ∀ w : Fin n, (runPairs P C₁ L₂ w).1.role = .Resetting ∧
          d ≤ (runPairs P C₁ L₂ w).1.resetcount
        exact hFloor₂
      · rw [runPairs_append]
        change ∀ w : Fin n, (runPairs P C₁ L₂ w).1.role = .Resetting →
          (runPairs P C₁ L₂ w).1.answer = majorityAnswer (runPairs P C₁ L₂)
        exact hAns₂
      · rw [runPairs_append]
        change (leaderSet (runPairs P C₁ L₂)).card ≤ 1
        exact hCard₂
      · rw [runPairs_append]
        change 0 < (leaderSet (runPairs P C₁ L₂)).card
        exact hPos₂

set_option maxHeartbeats 16000000 in
-- Answer-free tournament round: pair current `.L` leaders, spend one unit of
-- reset fuel, and halve the leader count.
theorem leader_tournament_round_no_answer
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d)
    (C : Config (AgentState n) Opinion n)
    (hAllFloor : ∀ w : Fin n,
      (C w).1.role = .Resetting ∧ d + 1 ≤ (C w).1.resetcount) :
    ∃ Lround : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := runPairs P C Lround
      (∀ w : Fin n, (C' w).1.role = .Resetting ∧ d ≤ (C' w).1.resetcount) ∧
      (leaderSet C').card ≤ ((leaderSet C).card + 1) / 2 ∧
      (0 < (leaderSet C).card → 0 < (leaderSet C').card) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let A : Finset (Fin n) := leaderSet C
  obtain ⟨pairs, leftover, hdis, hend_sub, hleft, hcover, hcount⟩ :=
    exists_pair_list_with_optional_leftover_count (A := A)
  refine ⟨pairs, ?_, ?_, ?_⟩
  · let U : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ pairEndpoints pairs
    have hU_high : ∀ w : Fin n, w ∈ U → w ∈ highSet C (d + 1) := by
      intro w _hw
      rw [mem_highSet]
      exact hAllFloor w
    have hSrc_high :
        ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C (d + 1) := by
      intro w _hw
      rw [mem_highSet]
      exact hAllFloor w
    have hU_untouched :
        ∀ w : Fin n, w ∈ U → w ∉ pairEndpoints pairs := by
      intro w hw
      exact (Finset.mem_sdiff.mp hw).2
    have hgen := generation_pair_list_high
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C pairs U hdis hd hU_high hSrc_high hU_untouched
    change
      (∀ w : Fin n, w ∈ U → w ∈ highSet (runPairs P C pairs) d) ∧
      (∀ w : Fin n, w ∈ pairSources pairs →
        w ∈ highSet (runPairs P C pairs) d) ∧
      (∀ w : Fin n, w ∈ pairTargets pairs →
        w ∈ highSet (runPairs P C pairs) d) ∧
      (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C pairs w = C w) at hgen
    obtain ⟨hU_fin, hSrc_fin, hTgt_fin, _hunchanged⟩ := hgen
    change ∀ w : Fin n,
      ((runPairs P C pairs) w).1.role = .Resetting ∧
        d ≤ ((runPairs P C pairs) w).1.resetcount
    intro w
    by_cases hwEnd : w ∈ pairEndpoints pairs
    · have hwUnion : w ∈ pairSources pairs ∪ pairTargets pairs := by
        simpa [pairEndpoints_eq_sources_union_targets pairs] using hwEnd
      rcases Finset.mem_union.mp hwUnion with hwSrc | hwTgt
      · exact mem_highSet.mp (hSrc_fin w hwSrc)
      · exact mem_highSet.mp (hTgt_fin w hwTgt)
    · have hwU : w ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwEnd⟩
      exact mem_highSet.mp (hU_fin w hwU)
  · have hEndLeader :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → w ∈ leaderSet C := by
      intro w hw
      exact hend_sub w hw
    have hEndReset :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting := by
      intro w _hw
      exact (hAllFloor w).1
    have hEndPos :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount := by
      intro w _hw
      have hw := (hAllFloor w).2
      omega
    have hLeader := leader_tournament_pair_list_leaderSet
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (by omega : 0 < Dmax) C pairs hdis hEndLeader hEndReset hEndPos
    change leaderSet (runPairs P C pairs) = leaderSet C \ pairTargets pairs at hLeader
    have hTsub : pairTargets pairs ⊆ A := by
      intro w hw
      exact hend_sub w (pairTargets_subset_endpoints pairs hw)
    have hcard_sdiff :
        (A \ pairTargets pairs).card = A.card - (pairTargets pairs).card :=
      Finset.card_sdiff_of_subset hTsub
    have hleader_card :
        (leaderSet (runPairs P C pairs)).card =
          A.card - (pairTargets pairs).card := by
      rw [hLeader]
      exact hcard_sdiff
    rw [hleader_card]
    change A.card - (pairTargets pairs).card ≤ (A.card + 1) / 2
    cases leftover with
    | none =>
        simp only [optionCount, add_zero] at hcount
        rw [hcount]
        omega
    | some z =>
        simp only [optionCount] at hcount
        rw [hcount]
        omega
  · intro hposA
    have hEndLeader :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → w ∈ leaderSet C := by
      intro w hw
      exact hend_sub w hw
    have hEndReset :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting := by
      intro w _hw
      exact (hAllFloor w).1
    have hEndPos :
        ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount := by
      intro w _hw
      have hw := (hAllFloor w).2
      omega
    have hLeader := leader_tournament_pair_list_leaderSet
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (by omega : 0 < Dmax) C pairs hdis hEndLeader hEndReset hEndPos
    change leaderSet (runPairs P C pairs) = leaderSet C \ pairTargets pairs at hLeader
    have hTsub : pairTargets pairs ⊆ A := by
      intro w hw
      exact hend_sub w (pairTargets_subset_endpoints pairs hw)
    have hcard_sdiff :
        (A \ pairTargets pairs).card = A.card - (pairTargets pairs).card :=
      Finset.card_sdiff_of_subset hTsub
    have hleader_card :
        (leaderSet (runPairs P C pairs)).card =
          A.card - (pairTargets pairs).card := by
      rw [hLeader]
      exact hcard_sdiff
    rw [hleader_card]
    have hposA' : 0 < A.card := by
      simpa [A] using hposA
    change 0 < A.card - (pairTargets pairs).card
    cases leftover with
    | none =>
        simp only [optionCount, add_zero] at hcount
        rw [hcount]
        omega
    | some z =>
        simp only [optionCount] at hcount
        rw [hcount]
        omega

set_option maxHeartbeats 16000000 in
-- Answer-free iteration of fueled leader tournament rounds.
theorem leader_tournament_iter_no_answer
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d) :
    ∀ g (C : Config (AgentState n) Opinion n),
      (∀ w : Fin n, (C w).1.role = .Resetting ∧
        d + g ≤ (C w).1.resetcount) →
      (leaderSet C).card ≤ 2 ^ g →
      0 < (leaderSet C).card →
      ∃ Ltourn : List (Fin n × Fin n),
        let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        let C' := runPairs P C Ltourn
        (∀ w : Fin n, (C' w).1.role = .Resetting ∧
          d ≤ (C' w).1.resetcount) ∧
        (leaderSet C').card ≤ 1 ∧
        0 < (leaderSet C').card := by
  intro g
  induction g with
  | zero =>
      intro C hAllFloor hBound hPos
      refine ⟨[], ?_, ?_, ?_⟩
      · change ∀ w : Fin n, (C w).1.role = .Resetting ∧
          d ≤ (C w).1.resetcount
        intro w
        have hw := hAllFloor w
        simpa using hw
      · simpa using hBound
      · simpa using hPos
  | succ g ih =>
      intro C hAllFloor hBound hPos
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hRoundFloor :
          ∀ w : Fin n, (C w).1.role = .Resetting ∧
            (d + g) + 1 ≤ (C w).1.resetcount := by
        intro w
        have hw := hAllFloor w
        refine ⟨hw.1, ?_⟩
        omega
      obtain ⟨L₁, hFloor₁, hCard₁, hPos₁⟩ :=
        leader_tournament_round_no_answer
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (d := d + g) hDmax (by omega : 0 < d + g)
          C hRoundFloor
      let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
      have hFloor₁' :
          ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
            d + g ≤ (C₁ w).1.resetcount := by
        simpa [C₁, P] using hFloor₁
      have hBound₁ : (leaderSet C₁).card ≤ 2 ^ g := by
        have hCard₁' : (leaderSet C₁).card ≤
            ((leaderSet C).card + 1) / 2 := by
          simpa [C₁, P] using hCard₁
        have hhalf : ((leaderSet C).card + 1) / 2 ≤ 2 ^ g := by
          have hpow : 2 ^ (g + 1) = 2 * 2 ^ g := by
            rw [pow_succ]
            omega
          rw [hpow] at hBound
          omega
        exact Nat.le_trans hCard₁' hhalf
      have hPos₁' : 0 < (leaderSet C₁).card := by
        simpa [C₁, P] using hPos₁ hPos
      obtain ⟨L₂, hFloor₂, hCard₂, hPos₂⟩ :=
        ih C₁ hFloor₁' hBound₁ hPos₁'
      refine ⟨L₁ ++ L₂, ?_, ?_, ?_⟩
      · rw [runPairs_append]
        change ∀ w : Fin n, (runPairs P C₁ L₂ w).1.role = .Resetting ∧
          d ≤ (runPairs P C₁ L₂ w).1.resetcount
        exact hFloor₂
      · rw [runPairs_append]
        change (leaderSet (runPairs P C₁ L₂)).card ≤ 1
        exact hCard₂
      · rw [runPairs_append]
        change 0 < (leaderSet (runPairs P C₁ L₂)).card
        exact hPos₂

theorem uniqueLeader_of_leaderSet_card_pos_le_one
    {n : ℕ} {C : Config (AgentState n) Opinion n}
    (hpos : 0 < (leaderSet C).card)
    (hle : (leaderSet C).card ≤ 1) :
    ∃! ℓ : Fin n, (C ℓ).1.leader = .L := by
  classical
  have hcard : (leaderSet C).card = 1 := by omega
  obtain ⟨ℓ, hsingleton⟩ := Finset.card_eq_one.mp hcard
  refine ⟨ℓ, ?_, ?_⟩
  · have hmem : ℓ ∈ leaderSet C := by
      rw [hsingleton]
      simp
    exact mem_leaderSet.mp hmem
  · intro x hx
    have hxmem : x ∈ leaderSet C := mem_leaderSet.mpr hx
    rw [hsingleton] at hxmem
    simpa using hxmem

set_option maxHeartbeats 8000000 in
-- List induction keeps the chosen root out of all target endpoints.
theorem generation_pair_list_root_leader
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (pairs : List (Fin n × Fin n))
    (root : Fin n)
    (hdis : PairListDisjoint pairs)
    (hk : 0 < k)
    (hRoot_high : root ∈ highSet C (k + 1))
    (hRoot_L : (C root).1.leader = .L)
    (hSrc_high :
      ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C (k + 1))
    (hRoot_not_target : root ∉ pairTargets pairs) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ((runPairs P C pairs) root).1.leader = .L := by
  classical
  induction pairs generalizing C with
  | nil =>
      intro
      change (C root).1.leader = .L
      exact hRoot_L
  | cons p ps ih =>
      intro
      rcases p with ⟨u, v⟩
      rcases hdis with ⟨huv, hu_not_tail, hv_not_tail, hdis_tail⟩
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hu_source : u ∈ pairSources ((u, v) :: ps) := by
        simp [pairSources]
      have hRoot_not_target_tail : root ∉ pairTargets ps := by
        intro htail
        exact hRoot_not_target (by simp [pairTargets, htail])
      by_cases hrootu : root = u
      · subst root
        have hstep_L := step_high_source_any_target_source_leader_next
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C huv hk (hSrc_high u hu_source) hRoot_L
        rw [runPairs_cons]
        have hkeep : runPairs P (C.step P u v) ps u = C.step P u v u :=
          runPairs_eq_of_not_pairEndpoints P (C.step P u v) ps hu_not_tail
        rw [hkeep]
        exact hstep_L
      · have hrootv : root ≠ v := by
          intro h
          subst root
          exact hRoot_not_target (by simp [pairTargets])
        have hstep_root : C.step P u v root = C root := by
          simp [Config.step, huv, hrootu, hrootv]
        have hRoot_high₁ : root ∈ highSet (C.step P u v) (k + 1) := by
          rw [mem_highSet]
          rw [hstep_root]
          exact mem_highSet.mp hRoot_high
        have hRoot_L₁ : (C.step P u v root).1.leader = .L := by
          rw [hstep_root]
          exact hRoot_L
        have hstep_high := step_high_source_any_target_next
          (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C huv hk (hSrc_high u hu_source)
        have hothers :
            ∀ w : Fin n, w ≠ u → w ≠ v → C.step P u v w = C w := by
          intro w hwu hwv
          simpa [P] using hstep_high.2.2.2.2 w hwu hwv
        have hSrc_high₁ :
            ∀ w : Fin n, w ∈ pairSources ps →
              w ∈ highSet (C.step P u v) (k + 1) := by
          intro w hwSrc
          have hwEnd : w ∈ pairEndpoints ps :=
            pairSources_subset_endpoints ps hwSrc
          have hwu : w ≠ u := by
            intro h
            subst w
            exact hu_not_tail hwEnd
          have hwv : w ≠ v := by
            intro h
            subst w
            exact hv_not_tail hwEnd
          rw [mem_highSet]
          rw [hothers w hwu hwv]
          exact mem_highSet.mp (hSrc_high w (by simp [pairSources, hwSrc]))
        obtain htail :=
          ih (C.step P u v) hdis_tail hRoot_high₁ hRoot_L₁
            hSrc_high₁ hRoot_not_target_tail
        rw [runPairs_cons]
        exact htail

set_option maxHeartbeats 10000000 in
-- Choose a maximal same-size source/target matching from the current high set
-- into its complement; the generation lemma then gives the cardinal doubling.
theorem balanced_tree_generation
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hk : 0 < k) :
    ∃ Lgrow : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      Nat.min n (2 * (highSet C (k + 1)).card) ≤
        (highSet (runPairs P C Lgrow) k).card := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let S : Finset (Fin n) := highSet C (k + 1)
  let O : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ S
  let q : ℕ := Nat.min S.card O.card
  have hqS : q ≤ S.card := by
    dsimp [q]
    exact Nat.min_le_left _ _
  have hqO : q ≤ O.card := by
    dsimp [q]
    exact Nat.min_le_right _ _
  obtain ⟨A, hA_sub, hA_card⟩ :=
    Finset.exists_subset_card_eq (s := S) hqS
  obtain ⟨T, hT_sub, hT_card⟩ :=
    Finset.exists_subset_card_eq (s := O) hqO
  have hdisAT : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro x hxA hxT
    have hxS : x ∈ S := hA_sub hxA
    have hxO : x ∈ O := hT_sub hxT
    exact (Finset.mem_sdiff.mp hxO).2 hxS
  have hcardAT : A.card = T.card := by
    rw [hA_card, hT_card]
  obtain ⟨pairs, hpair_dis, hsources, htargets⟩ :=
    exists_pair_list_of_disjoint_eq_card A T hcardAT hdisAT
  let U : Finset (Fin n) := S \ A
  have hU_high :
      ∀ w : Fin n, w ∈ U → w ∈ highSet C (k + 1) := by
    intro w hw
    exact (Finset.mem_sdiff.mp hw).1
  have hSrc_high :
      ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C (k + 1) := by
    intro w hw
    have hwA : w ∈ A := by
      simpa [hsources] using hw
    exact hA_sub hwA
  have hU_untouched : ∀ w : Fin n, w ∈ U → w ∉ pairEndpoints pairs := by
    intro w hwU hwEnd
    have hwS : w ∈ S := (Finset.mem_sdiff.mp hwU).1
    have hwNotA : w ∉ A := (Finset.mem_sdiff.mp hwU).2
    have hwEnd' : w ∈ A ∪ T := by
      simpa [pairEndpoints_eq_sources_union_targets pairs, hsources, htargets]
        using hwEnd
    rcases Finset.mem_union.mp hwEnd' with hwA | hwT
    · exact hwNotA hwA
    · have hwO : w ∈ O := hT_sub hwT
      exact (Finset.mem_sdiff.mp hwO).2 hwS
  have hgen := generation_pair_list_high
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C pairs U hpair_dis hk hU_high hSrc_high hU_untouched
  change
    (∀ w : Fin n, w ∈ U → w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∈ pairSources pairs →
      w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∈ pairTargets pairs →
      w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C pairs w = C w) at hgen
  obtain ⟨hU_fin, hSrc_fin, hTgt_fin, _hunch_fin⟩ := hgen
  have hsubsetST : S ∪ T ⊆ highSet (runPairs P C pairs) k := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwS | hwT
    · by_cases hwA : w ∈ A
      · have hwSrc : w ∈ pairSources pairs := by
          simpa [hsources] using hwA
        exact hSrc_fin w hwSrc
      · have hwU : w ∈ U := by
          exact Finset.mem_sdiff.mpr ⟨hwS, hwA⟩
        exact hU_fin w hwU
    · have hwTgt : w ∈ pairTargets pairs := by
        simpa [htargets] using hwT
      exact hTgt_fin w hwTgt
  have hdisST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hxO : x ∈ O := hT_sub hxT
    exact (Finset.mem_sdiff.mp hxO).2 hxS
  have hST_card : (S ∪ T).card = S.card + q := by
    rw [Finset.card_union_of_disjoint hdisST, hT_card]
  have hSle : S.card ≤ n := by
    simpa [S] using highSet_card_le_n C (k + 1)
  have hOcard : O.card = n - S.card := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [Finset.card_univ, Fintype.card_fin]
  have htarget_eq : S.card + q = Nat.min n (2 * S.card) := by
    dsimp [q]
    rw [hOcard]
    exact card_add_min_complement_eq_min_double hSle
  refine ⟨pairs, ?_⟩
  change Nat.min n (2 * (highSet C (k + 1)).card) ≤
    (highSet (runPairs P C pairs) k).card
  calc
    Nat.min n (2 * (highSet C (k + 1)).card)
        = Nat.min n (2 * S.card) := by simp [S]
    _ = S.card + q := htarget_eq.symm
    _ = (S ∪ T).card := hST_card.symm
    _ ≤ (highSet (runPairs P C pairs) k).card :=
      Finset.card_le_card hsubsetST

set_option maxHeartbeats 16000000 in
-- Finset pairing/cardinality bookkeeping plus answer-invariant transport.
theorem balanced_tree_generation_answer
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hk : 0 < k)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    ∃ Lgrow : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      Nat.min n (2 * (highSet C (k + 1)).card) ≤
        (highSet (runPairs P C Lgrow) k).card ∧
      (∀ w : Fin n, ((runPairs P C Lgrow) w).1.role = .Resetting →
        ((runPairs P C Lgrow) w).1.answer =
          majorityAnswer (runPairs P C Lgrow)) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let S : Finset (Fin n) := highSet C (k + 1)
  let O : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ S
  let q : ℕ := Nat.min S.card O.card
  have hqS : q ≤ S.card := by
    dsimp [q]
    exact Nat.min_le_left _ _
  have hqO : q ≤ O.card := by
    dsimp [q]
    exact Nat.min_le_right _ _
  obtain ⟨A, hA_sub, hA_card⟩ :=
    Finset.exists_subset_card_eq (s := S) hqS
  obtain ⟨T, hT_sub, hT_card⟩ :=
    Finset.exists_subset_card_eq (s := O) hqO
  have hdisAT : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro x hxA hxT
    have hxS : x ∈ S := hA_sub hxA
    have hxO : x ∈ O := hT_sub hxT
    exact (Finset.mem_sdiff.mp hxO).2 hxS
  have hcardAT : A.card = T.card := by
    rw [hA_card, hT_card]
  obtain ⟨pairs, hpair_dis, hsources, htargets⟩ :=
    exists_pair_list_of_disjoint_eq_card A T hcardAT hdisAT
  let U : Finset (Fin n) := S \ A
  have hU_high :
      ∀ w : Fin n, w ∈ U → w ∈ highSet C (k + 1) := by
    intro w hw
    exact (Finset.mem_sdiff.mp hw).1
  have hSrc_high :
      ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C (k + 1) := by
    intro w hw
    have hwA : w ∈ A := by
      simpa [hsources] using hw
    exact hA_sub hwA
  have hU_untouched : ∀ w : Fin n, w ∈ U → w ∉ pairEndpoints pairs := by
    intro w hwU hwEnd
    have hwS : w ∈ S := (Finset.mem_sdiff.mp hwU).1
    have hwNotA : w ∉ A := (Finset.mem_sdiff.mp hwU).2
    have hwEnd' : w ∈ A ∪ T := by
      simpa [pairEndpoints_eq_sources_union_targets pairs, hsources, htargets]
        using hwEnd
    rcases Finset.mem_union.mp hwEnd' with hwA | hwT
    · exact hwNotA hwA
    · have hwO : w ∈ O := hT_sub hwT
      exact (Finset.mem_sdiff.mp hwO).2 hwS
  have hgen := generation_pair_list_high
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C pairs U hpair_dis hk hU_high hSrc_high hU_untouched
  change
    (∀ w : Fin n, w ∈ U → w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∈ pairSources pairs →
      w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∈ pairTargets pairs →
      w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C pairs w = C w) at hgen
  obtain ⟨hU_fin, hSrc_fin, hTgt_fin, _hunch_fin⟩ := hgen
  have hAns_fin := generation_pair_list_answer
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C pairs hpair_dis hk hSrc_high hAllAns
  change ∀ w : Fin n, ((runPairs P C pairs) w).1.role = .Resetting →
    ((runPairs P C pairs) w).1.answer =
      majorityAnswer (runPairs P C pairs) at hAns_fin
  have hsubsetST : S ∪ T ⊆ highSet (runPairs P C pairs) k := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwS | hwT
    · by_cases hwA : w ∈ A
      · have hwSrc : w ∈ pairSources pairs := by
          simpa [hsources] using hwA
        exact hSrc_fin w hwSrc
      · have hwU : w ∈ U := by
          exact Finset.mem_sdiff.mpr ⟨hwS, hwA⟩
        exact hU_fin w hwU
    · have hwTgt : w ∈ pairTargets pairs := by
        simpa [htargets] using hwT
      exact hTgt_fin w hwTgt
  have hdisST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hxO : x ∈ O := hT_sub hxT
    exact (Finset.mem_sdiff.mp hxO).2 hxS
  have hST_card : (S ∪ T).card = S.card + q := by
    rw [Finset.card_union_of_disjoint hdisST, hT_card]
  have hSle : S.card ≤ n := by
    simpa [S] using highSet_card_le_n C (k + 1)
  have hOcard : O.card = n - S.card := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [Finset.card_univ, Fintype.card_fin]
  have htarget_eq : S.card + q = Nat.min n (2 * S.card) := by
    dsimp [q]
    rw [hOcard]
    exact card_add_min_complement_eq_min_double hSle
  refine ⟨pairs, ?_, ?_⟩
  · change Nat.min n (2 * (highSet C (k + 1)).card) ≤
      (highSet (runPairs P C pairs) k).card
    calc
      Nat.min n (2 * (highSet C (k + 1)).card)
          = Nat.min n (2 * S.card) := by simp [S]
      _ = S.card + q := htarget_eq.symm
      _ = (S ∪ T).card := hST_card.symm
      _ ≤ (highSet (runPairs P C pairs) k).card :=
        Finset.card_le_card hsubsetST
  · exact hAns_fin

set_option maxHeartbeats 20000000 in
-- Finset pairing/cardinality bookkeeping plus root-leader preservation.
theorem balanced_tree_generation_answer_root
    {n Rmax Emax Dmax k : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hk : 0 < k)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C)
    (root : Fin n)
    (hRoot_high : root ∈ highSet C (k + 1))
    (hRoot_L : (C root).1.leader = .L) :
    ∃ Lgrow : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      Nat.min n (2 * (highSet C (k + 1)).card) ≤
        (highSet (runPairs P C Lgrow) k).card ∧
      (∀ w : Fin n, ((runPairs P C Lgrow) w).1.role = .Resetting →
        ((runPairs P C Lgrow) w).1.answer =
          majorityAnswer (runPairs P C Lgrow)) ∧
      root ∈ highSet (runPairs P C Lgrow) k ∧
      ((runPairs P C Lgrow) root).1.leader = .L := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let S : Finset (Fin n) := highSet C (k + 1)
  let O : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ S
  let q : ℕ := Nat.min S.card O.card
  have hrootS : root ∈ S := hRoot_high
  have hqS : q ≤ S.card := by
    dsimp [q]
    exact Nat.min_le_left _ _
  have hqO : q ≤ O.card := by
    dsimp [q]
    exact Nat.min_le_right _ _
  obtain ⟨A, hA_sub, hA_card⟩ :=
    Finset.exists_subset_card_eq (s := S) hqS
  obtain ⟨T, hT_sub, hT_card⟩ :=
    Finset.exists_subset_card_eq (s := O) hqO
  have hdisAT : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro x hxA hxT
    have hxS : x ∈ S := hA_sub hxA
    have hxO : x ∈ O := hT_sub hxT
    exact (Finset.mem_sdiff.mp hxO).2 hxS
  have hcardAT : A.card = T.card := by
    rw [hA_card, hT_card]
  obtain ⟨pairs, hpair_dis, hsources, htargets⟩ :=
    exists_pair_list_of_disjoint_eq_card A T hcardAT hdisAT
  let U : Finset (Fin n) := S \ A
  have hU_high :
      ∀ w : Fin n, w ∈ U → w ∈ highSet C (k + 1) := by
    intro w hw
    exact (Finset.mem_sdiff.mp hw).1
  have hSrc_high :
      ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C (k + 1) := by
    intro w hw
    have hwA : w ∈ A := by
      simpa [hsources] using hw
    exact hA_sub hwA
  have hRoot_not_target : root ∉ pairTargets pairs := by
    intro hrt
    have hrootT : root ∈ T := by
      simpa [htargets] using hrt
    have hrootO : root ∈ O := hT_sub hrootT
    exact (Finset.mem_sdiff.mp hrootO).2 hrootS
  have hU_untouched : ∀ w : Fin n, w ∈ U → w ∉ pairEndpoints pairs := by
    intro w hwU hwEnd
    have hwS : w ∈ S := (Finset.mem_sdiff.mp hwU).1
    have hwNotA : w ∉ A := (Finset.mem_sdiff.mp hwU).2
    have hwEnd' : w ∈ A ∪ T := by
      simpa [pairEndpoints_eq_sources_union_targets pairs, hsources, htargets]
        using hwEnd
    rcases Finset.mem_union.mp hwEnd' with hwA | hwT
    · exact hwNotA hwA
    · have hwO : w ∈ O := hT_sub hwT
      exact (Finset.mem_sdiff.mp hwO).2 hwS
  have hgen := generation_pair_list_high
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C pairs U hpair_dis hk hU_high hSrc_high hU_untouched
  change
    (∀ w : Fin n, w ∈ U → w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∈ pairSources pairs →
      w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∈ pairTargets pairs →
      w ∈ highSet (runPairs P C pairs) k) ∧
    (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C pairs w = C w) at hgen
  obtain ⟨hU_fin, hSrc_fin, hTgt_fin, _hunch_fin⟩ := hgen
  have hAns_fin := generation_pair_list_answer
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C pairs hpair_dis hk hSrc_high hAllAns
  change ∀ w : Fin n, ((runPairs P C pairs) w).1.role = .Resetting →
    ((runPairs P C pairs) w).1.answer =
      majorityAnswer (runPairs P C pairs) at hAns_fin
  have hRoot_L_fin := generation_pair_list_root_leader
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C pairs root hpair_dis hk hRoot_high hRoot_L
    hSrc_high hRoot_not_target
  change ((runPairs P C pairs) root).1.leader = .L at hRoot_L_fin
  have hsubsetST : S ∪ T ⊆ highSet (runPairs P C pairs) k := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwS | hwT
    · by_cases hwA : w ∈ A
      · have hwSrc : w ∈ pairSources pairs := by
          simpa [hsources] using hwA
        exact hSrc_fin w hwSrc
      · have hwU : w ∈ U := by
          exact Finset.mem_sdiff.mpr ⟨hwS, hwA⟩
        exact hU_fin w hwU
    · have hwTgt : w ∈ pairTargets pairs := by
        simpa [htargets] using hwT
      exact hTgt_fin w hwTgt
  have hRoot_high_fin : root ∈ highSet (runPairs P C pairs) k := by
    exact hsubsetST (Finset.mem_union_left T hrootS)
  have hdisST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hxO : x ∈ O := hT_sub hxT
    exact (Finset.mem_sdiff.mp hxO).2 hxS
  have hST_card : (S ∪ T).card = S.card + q := by
    rw [Finset.card_union_of_disjoint hdisST, hT_card]
  have hSle : S.card ≤ n := by
    simpa [S] using highSet_card_le_n C (k + 1)
  have hOcard : O.card = n - S.card := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [Finset.card_univ, Fintype.card_fin]
  have htarget_eq : S.card + q = Nat.min n (2 * S.card) := by
    dsimp [q]
    rw [hOcard]
    exact card_add_min_complement_eq_min_double hSle
  refine ⟨pairs, ?_, ?_, ?_, ?_⟩
  · change Nat.min n (2 * (highSet C (k + 1)).card) ≤
      (highSet (runPairs P C pairs) k).card
    calc
      Nat.min n (2 * (highSet C (k + 1)).card)
          = Nat.min n (2 * S.card) := by simp [S]
      _ = S.card + q := htarget_eq.symm
      _ = (S ∪ T).card := hST_card.symm
      _ ≤ (highSet (runPairs P C pairs) k).card :=
        Finset.card_le_card hsubsetST
  · exact hAns_fin
  · exact hRoot_high_fin
  · exact hRoot_L_fin

set_option maxHeartbeats 12000000 in
-- Iterating the one-generation matching lemma keeps only the cardinal lower
-- bound needed at the final logarithmic depth.
theorem balanced_tree_growth_card_iter
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) :
    ∀ g k (C : Config (AgentState n) Opinion n) (m : ℕ),
      0 < k →
      m ≤ n →
      m ≤ (highSet C (k + g)).card →
      ∃ Lgrow : List (Fin n × Fin n),
        let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        Nat.min n (2 ^ g * m) ≤
          (highSet (runPairs P C Lgrow) k).card := by
  classical
  intro g
  induction g with
  | zero =>
      intro k C m _hk hm_n hm_card
      refine ⟨[], ?_⟩
      change Nat.min n (2 ^ 0 * m) ≤ (highSet C k).card
      have hmin : Nat.min n m = m := Nat.min_eq_right hm_n
      simpa [hmin] using hm_card
  | succ g ih =>
      intro k C m hk hm_n hm_card
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hkg : 0 < k + g := by omega
      obtain ⟨L₁, hgen⟩ :=
        balanced_tree_generation
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C hkg
      change Nat.min n (2 * (highSet C ((k + g) + 1)).card) ≤
        (highSet (runPairs P C L₁) (k + g)).card at hgen
      have hm_card' : m ≤ (highSet C ((k + g) + 1)).card := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm_card
      have hmin_m_le :
          Nat.min n (2 * m) ≤
            Nat.min n (2 * (highSet C ((k + g) + 1)).card) := by
        exact min_le_min_left n (Nat.mul_le_mul_left 2 hm_card')
      have hm₁_card : Nat.min n (2 * m) ≤
          (highSet (runPairs P C L₁) (k + g)).card :=
        Nat.le_trans hmin_m_le hgen
      have hm₁_n : Nat.min n (2 * m) ≤ n := Nat.min_le_left _ _
      obtain ⟨L₂, hih⟩ := ih k (runPairs P C L₁)
        (Nat.min n (2 * m)) hk hm₁_n hm₁_card
      change Nat.min n (2 ^ g * Nat.min n (2 * m)) ≤
        (highSet (runPairs P (runPairs P C L₁) L₂) k).card at hih
      refine ⟨L₁ ++ L₂, ?_⟩
      change Nat.min n (2 ^ (g + 1) * m) ≤
        (highSet (runPairs P C (L₁ ++ L₂)) k).card
      rw [runPairs_append]
      exact Nat.le_trans
        (min_pow_succ_mul_le_min_pow_mul_min_double
          (n := n) (m := m) (g := g) hn)
        hih

set_option maxHeartbeats 16000000 in
-- Iterated doubling carries both cardinal growth and answer invariants.
theorem balanced_tree_growth_card_iter_answer
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) :
    ∀ g k (C : Config (AgentState n) Opinion n) (m : ℕ),
      0 < k →
      m ≤ n →
      m ≤ (highSet C (k + g)).card →
      (∀ w : Fin n, (C w).1.role = .Resetting →
        (C w).1.answer = majorityAnswer C) →
      ∃ Lgrow : List (Fin n × Fin n),
        let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        Nat.min n (2 ^ g * m) ≤
          (highSet (runPairs P C Lgrow) k).card ∧
        (∀ w : Fin n, ((runPairs P C Lgrow) w).1.role = .Resetting →
          ((runPairs P C Lgrow) w).1.answer =
            majorityAnswer (runPairs P C Lgrow)) := by
  classical
  intro g
  induction g with
  | zero =>
      intro k C m _hk hm_n hm_card hAllAns
      refine ⟨[], ?_, ?_⟩
      · change Nat.min n (2 ^ 0 * m) ≤ (highSet C k).card
        have hmin : Nat.min n m = m := Nat.min_eq_right hm_n
        simpa [hmin] using hm_card
      · change ∀ w : Fin n, (C w).1.role = .Resetting →
          (C w).1.answer = majorityAnswer C
        exact hAllAns
  | succ g ih =>
      intro k C m hk hm_n hm_card hAllAns
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hkg : 0 < k + g := by omega
      obtain ⟨L₁, hgen_card, hgen_ans⟩ :=
        balanced_tree_generation_answer
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C hkg hAllAns
      change Nat.min n (2 * (highSet C ((k + g) + 1)).card) ≤
        (highSet (runPairs P C L₁) (k + g)).card at hgen_card
      change ∀ w : Fin n, ((runPairs P C L₁) w).1.role = .Resetting →
        ((runPairs P C L₁) w).1.answer =
          majorityAnswer (runPairs P C L₁) at hgen_ans
      have hm_card' : m ≤ (highSet C ((k + g) + 1)).card := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm_card
      have hmin_m_le :
          Nat.min n (2 * m) ≤
            Nat.min n (2 * (highSet C ((k + g) + 1)).card) := by
        exact min_le_min_left n (Nat.mul_le_mul_left 2 hm_card')
      have hm₁_card : Nat.min n (2 * m) ≤
          (highSet (runPairs P C L₁) (k + g)).card :=
        Nat.le_trans hmin_m_le hgen_card
      have hm₁_n : Nat.min n (2 * m) ≤ n := Nat.min_le_left _ _
      obtain ⟨L₂, hih_card, hih_ans⟩ := ih k (runPairs P C L₁)
        (Nat.min n (2 * m)) hk hm₁_n hm₁_card hgen_ans
      change Nat.min n (2 ^ g * Nat.min n (2 * m)) ≤
        (highSet (runPairs P (runPairs P C L₁) L₂) k).card at hih_card
      change ∀ w : Fin n,
        ((runPairs P (runPairs P C L₁) L₂) w).1.role = .Resetting →
          ((runPairs P (runPairs P C L₁) L₂) w).1.answer =
            majorityAnswer (runPairs P (runPairs P C L₁) L₂) at hih_ans
      refine ⟨L₁ ++ L₂, ?_, ?_⟩
      · change Nat.min n (2 ^ (g + 1) * m) ≤
          (highSet (runPairs P C (L₁ ++ L₂)) k).card
        rw [runPairs_append]
        exact Nat.le_trans
          (min_pow_succ_mul_le_min_pow_mul_min_double
            (n := n) (m := m) (g := g) hn)
          hih_card
      · rw [runPairs_append]
        exact hih_ans

set_option maxHeartbeats 20000000 in
-- Iterated doubling carries answer invariants and root-leader preservation.
theorem balanced_tree_growth_card_iter_answer_root
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) :
    ∀ g k (C : Config (AgentState n) Opinion n) (m : ℕ) (root : Fin n),
      0 < k →
      m ≤ n →
      m ≤ (highSet C (k + g)).card →
      (∀ w : Fin n, (C w).1.role = .Resetting →
        (C w).1.answer = majorityAnswer C) →
      root ∈ highSet C (k + g) →
      (C root).1.leader = .L →
      ∃ Lgrow : List (Fin n × Fin n),
        let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        Nat.min n (2 ^ g * m) ≤
          (highSet (runPairs P C Lgrow) k).card ∧
        (∀ w : Fin n, ((runPairs P C Lgrow) w).1.role = .Resetting →
          ((runPairs P C Lgrow) w).1.answer =
            majorityAnswer (runPairs P C Lgrow)) ∧
        root ∈ highSet (runPairs P C Lgrow) k ∧
        ((runPairs P C Lgrow) root).1.leader = .L := by
  classical
  intro g
  induction g with
  | zero =>
      intro k C m root _hk hm_n hm_card hAllAns hRoot_high hRoot_L
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · change Nat.min n (2 ^ 0 * m) ≤ (highSet C k).card
        have hmin : Nat.min n m = m := Nat.min_eq_right hm_n
        simpa [hmin] using hm_card
      · change ∀ w : Fin n, (C w).1.role = .Resetting →
          (C w).1.answer = majorityAnswer C
        exact hAllAns
      · change root ∈ highSet C k
        simpa using hRoot_high
      · change (C root).1.leader = .L
        exact hRoot_L
  | succ g ih =>
      intro k C m root hk hm_n hm_card hAllAns hRoot_high hRoot_L
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hkg : 0 < k + g := by omega
      have hRoot_high_gen : root ∈ highSet C ((k + g) + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRoot_high
      obtain ⟨L₁, hgen_card, hgen_ans, hroot_high₁, hroot_L₁⟩ :=
        balanced_tree_generation_answer_root
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C hkg hAllAns root hRoot_high_gen hRoot_L
      change Nat.min n (2 * (highSet C ((k + g) + 1)).card) ≤
        (highSet (runPairs P C L₁) (k + g)).card at hgen_card
      change ∀ w : Fin n, ((runPairs P C L₁) w).1.role = .Resetting →
        ((runPairs P C L₁) w).1.answer =
          majorityAnswer (runPairs P C L₁) at hgen_ans
      change root ∈ highSet (runPairs P C L₁) (k + g) at hroot_high₁
      change ((runPairs P C L₁) root).1.leader = .L at hroot_L₁
      have hm_card' : m ≤ (highSet C ((k + g) + 1)).card := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm_card
      have hmin_m_le :
          Nat.min n (2 * m) ≤
            Nat.min n (2 * (highSet C ((k + g) + 1)).card) := by
        exact min_le_min_left n (Nat.mul_le_mul_left 2 hm_card')
      have hm₁_card : Nat.min n (2 * m) ≤
          (highSet (runPairs P C L₁) (k + g)).card :=
        Nat.le_trans hmin_m_le hgen_card
      have hm₁_n : Nat.min n (2 * m) ≤ n := Nat.min_le_left _ _
      obtain ⟨L₂, hih_card, hih_ans, hroot_high₂, hroot_L₂⟩ :=
        ih k (runPairs P C L₁) (Nat.min n (2 * m)) root
          hk hm₁_n hm₁_card hgen_ans hroot_high₁ hroot_L₁
      change Nat.min n (2 ^ g * Nat.min n (2 * m)) ≤
        (highSet (runPairs P (runPairs P C L₁) L₂) k).card at hih_card
      change ∀ w : Fin n,
        ((runPairs P (runPairs P C L₁) L₂) w).1.role = .Resetting →
          ((runPairs P (runPairs P C L₁) L₂) w).1.answer =
            majorityAnswer (runPairs P (runPairs P C L₁) L₂) at hih_ans
      change root ∈ highSet (runPairs P (runPairs P C L₁) L₂) k at hroot_high₂
      change ((runPairs P (runPairs P C L₁) L₂) root).1.leader = .L at hroot_L₂
      refine ⟨L₁ ++ L₂, ?_, ?_, ?_, ?_⟩
      · change Nat.min n (2 ^ (g + 1) * m) ≤
          (highSet (runPairs P C (L₁ ++ L₂)) k).card
        rw [runPairs_append]
        exact Nat.le_trans
          (min_pow_succ_mul_le_min_pow_mul_min_double
            (n := n) (m := m) (g := g) hn)
          hih_card
      · rw [runPairs_append]
        exact hih_ans
      · rw [runPairs_append]
        exact hroot_high₂
      · rw [runPairs_append]
        exact hroot_L₂

set_option maxHeartbeats 20000000 in
-- Iterated doubling carrying only cardinal growth and root-leader
-- preservation; no answer invariant is assumed or produced.
theorem balanced_tree_growth_card_iter_root
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) :
    ∀ g k (C : Config (AgentState n) Opinion n) (m : ℕ) (root : Fin n),
      0 < k →
      m ≤ n →
      m ≤ (highSet C (k + g)).card →
      root ∈ highSet C (k + g) →
      (C root).1.leader = .L →
      ∃ Lgrow : List (Fin n × Fin n),
        let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        Nat.min n (2 ^ g * m) ≤
          (highSet (runPairs P C Lgrow) k).card ∧
        root ∈ highSet (runPairs P C Lgrow) k ∧
        ((runPairs P C Lgrow) root).1.leader = .L := by
  classical
  intro g
  induction g with
  | zero =>
      intro k C m root _hk hm_n hm_card hRoot_high hRoot_L
      refine ⟨[], ?_, ?_, ?_⟩
      · change Nat.min n (2 ^ 0 * m) ≤ (highSet C k).card
        have hmin : Nat.min n m = m := Nat.min_eq_right hm_n
        simpa [hmin] using hm_card
      · change root ∈ highSet C k
        simpa using hRoot_high
      · change (C root).1.leader = .L
        exact hRoot_L
  | succ g ih =>
      intro k C m root hk hm_n hm_card hRoot_high hRoot_L
      set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      have hkg : 0 < k + g := by omega
      have hRoot_high_gen : root ∈ highSet C ((k + g) + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRoot_high
      set S : Finset (Fin n) := highSet C ((k + g) + 1)
      set O : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ S
      let q : ℕ := Nat.min S.card O.card
      have hrootS : root ∈ S := by
        simpa [S] using hRoot_high_gen
      have hqS : q ≤ S.card := by
        dsimp [q]
        exact Nat.min_le_left _ _
      have hqO : q ≤ O.card := by
        dsimp [q]
        exact Nat.min_le_right _ _
      obtain ⟨A, hA_sub, hA_card⟩ :=
        Finset.exists_subset_card_eq (s := S) hqS
      obtain ⟨T, hT_sub, hT_card⟩ :=
        Finset.exists_subset_card_eq (s := O) hqO
      have hdisAT : Disjoint A T := by
        rw [Finset.disjoint_left]
        intro x hxA hxT
        have hxS : x ∈ S := hA_sub hxA
        have hxO : x ∈ O := hT_sub hxT
        exact (Finset.mem_sdiff.mp hxO).2 hxS
      have hcardAT : A.card = T.card := by
        rw [hA_card, hT_card]
      obtain ⟨pairs, hpair_dis, hsources, htargets⟩ :=
        exists_pair_list_of_disjoint_eq_card A T hcardAT hdisAT
      let U : Finset (Fin n) := S \ A
      have hU_high :
          ∀ w : Fin n, w ∈ U → w ∈ highSet C ((k + g) + 1) := by
        intro w hw
        exact (Finset.mem_sdiff.mp hw).1
      have hSrc_high :
          ∀ w : Fin n, w ∈ pairSources pairs → w ∈ highSet C ((k + g) + 1) := by
        intro w hw
        have hwA : w ∈ A := by
          simpa [hsources] using hw
        exact hA_sub hwA
      have hRoot_not_target : root ∉ pairTargets pairs := by
        intro hrt
        have hrootT : root ∈ T := by
          simpa [htargets] using hrt
        have hrootO : root ∈ O := hT_sub hrootT
        exact (Finset.mem_sdiff.mp hrootO).2 hrootS
      have hU_untouched : ∀ w : Fin n, w ∈ U → w ∉ pairEndpoints pairs := by
        intro w hwU hwEnd
        have hwS : w ∈ S := (Finset.mem_sdiff.mp hwU).1
        have hwNotA : w ∉ A := (Finset.mem_sdiff.mp hwU).2
        have hwEnd' : w ∈ A ∪ T := by
          simpa [pairEndpoints_eq_sources_union_targets pairs, hsources, htargets]
            using hwEnd
        rcases Finset.mem_union.mp hwEnd' with hwA | hwT
        · exact hwNotA hwA
        · have hwO : w ∈ O := hT_sub hwT
          exact (Finset.mem_sdiff.mp hwO).2 hwS
      have hgen := generation_pair_list_high
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C pairs U hpair_dis hkg hU_high hSrc_high hU_untouched
      change
        (∀ w : Fin n, w ∈ U → w ∈ highSet (runPairs P C pairs) (k + g)) ∧
        (∀ w : Fin n, w ∈ pairSources pairs →
          w ∈ highSet (runPairs P C pairs) (k + g)) ∧
        (∀ w : Fin n, w ∈ pairTargets pairs →
          w ∈ highSet (runPairs P C pairs) (k + g)) ∧
        (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C pairs w = C w) at hgen
      obtain ⟨hU_fin, hSrc_fin, hTgt_fin, _hunch_fin⟩ := hgen
      have hRoot_L_fin := generation_pair_list_root_leader
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C pairs root hpair_dis hkg hRoot_high_gen hRoot_L
        hSrc_high hRoot_not_target
      change ((runPairs P C pairs) root).1.leader = .L at hRoot_L_fin
      have hsubsetST : S ∪ T ⊆ highSet (runPairs P C pairs) (k + g) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hwS | hwT
        · by_cases hwA : w ∈ A
          · have hwSrc : w ∈ pairSources pairs := by
              simpa [hsources] using hwA
            exact hSrc_fin w hwSrc
          · have hwU : w ∈ U := by
              exact Finset.mem_sdiff.mpr ⟨hwS, hwA⟩
            exact hU_fin w hwU
        · have hwTgt : w ∈ pairTargets pairs := by
            simpa [htargets] using hwT
          exact hTgt_fin w hwTgt
      have hRoot_high₁ : root ∈ highSet (runPairs P C pairs) (k + g) := by
        exact hsubsetST (Finset.mem_union_left T hrootS)
      have hdisST : Disjoint S T := by
        rw [Finset.disjoint_left]
        intro x hxS hxT
        have hxO : x ∈ O := hT_sub hxT
        exact (Finset.mem_sdiff.mp hxO).2 hxS
      have hST_card : (S ∪ T).card = S.card + q := by
        rw [Finset.card_union_of_disjoint hdisST, hT_card]
      have hSle : S.card ≤ n := by
        simpa [S] using highSet_card_le_n C ((k + g) + 1)
      have hOcard : O.card = n - S.card := by
        dsimp [O]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simp [Finset.card_univ, Fintype.card_fin]
      have htarget_eq : S.card + q = Nat.min n (2 * S.card) := by
        dsimp [q]
        rw [hOcard]
        exact card_add_min_complement_eq_min_double hSle
      have hgen_card : Nat.min n (2 * (highSet C ((k + g) + 1)).card) ≤
          (highSet (runPairs P C pairs) (k + g)).card := by
        calc
          Nat.min n (2 * (highSet C ((k + g) + 1)).card)
              = Nat.min n (2 * S.card) := by simp [S]
          _ = S.card + q := htarget_eq.symm
          _ = (S ∪ T).card := hST_card.symm
          _ ≤ (highSet (runPairs P C pairs) (k + g)).card :=
            Finset.card_le_card hsubsetST
      have hm_card' : m ≤ (highSet C ((k + g) + 1)).card := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm_card
      have hmin_m_le :
          Nat.min n (2 * m) ≤
            Nat.min n (2 * (highSet C ((k + g) + 1)).card) := by
        exact min_le_min_left n (Nat.mul_le_mul_left 2 hm_card')
      have hm₁_card : Nat.min n (2 * m) ≤
          (highSet (runPairs P C pairs) (k + g)).card :=
        Nat.le_trans hmin_m_le hgen_card
      have hm₁_n : Nat.min n (2 * m) ≤ n := Nat.min_le_left _ _
      obtain ⟨L₂, hih_card, hroot_high₂, hroot_L₂⟩ :=
        ih k (runPairs P C pairs) (Nat.min n (2 * m)) root
          hk hm₁_n hm₁_card hRoot_high₁ hRoot_L_fin
      change Nat.min n (2 ^ g * Nat.min n (2 * m)) ≤
        (highSet (runPairs P (runPairs P C pairs) L₂) k).card at hih_card
      change root ∈ highSet (runPairs P (runPairs P C pairs) L₂) k at hroot_high₂
      change ((runPairs P (runPairs P C pairs) L₂) root).1.leader = .L at hroot_L₂
      refine ⟨pairs ++ L₂, ?_, ?_, ?_⟩
      · change Nat.min n (2 ^ (g + 1) * m) ≤
          (highSet (runPairs P C (pairs ++ L₂)) k).card
        rw [runPairs_append]
        exact Nat.le_trans
          (min_pow_succ_mul_le_min_pow_mul_min_double
            (n := n) (m := m) (g := g) hn)
          hih_card
      · rw [runPairs_append]
        exact hroot_high₂
      · rw [runPairs_append]
        exact hroot_L₂

set_option maxHeartbeats 12000000 in
-- Logarithmic balanced growth with a surviving root leader, without answer
-- assumptions.
theorem balanced_tree_growth_floor_leader_no_answer
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : Nat.clog 2 n + d ≤ (C r).1.resetcount)
    (hr_L : (C r).1.leader = .L) :
    ∃ Lgrow : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C₁ := runPairs P C Lgrow
      (∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
        d ≤ (C₁ w).1.resetcount) ∧
      (C₁ r).1.leader = .L := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hseed : r ∈ highSet C (Nat.clog 2 n + d) := by
    rw [mem_highSet]
    exact ⟨hr_role, hr_log⟩
  have hcard_one : 1 ≤ (highSet C (d + Nat.clog 2 n)).card := by
    have hpos : 0 < (highSet C (Nat.clog 2 n + d)).card :=
      Finset.card_pos.mpr ⟨r, hseed⟩
    have hpos' : 0 < (highSet C (d + Nat.clog 2 n)).card := by
      simpa [Nat.add_comm] using hpos
    omega
  have hroot_high : r ∈ highSet C (d + Nat.clog 2 n) := by
    simpa [Nat.add_comm] using hseed
  have hm_n : 1 ≤ n := by omega
  obtain ⟨Lgrow, hiter_card, hroot_high_fin, hroot_L_fin⟩ :=
    balanced_tree_growth_card_iter_root
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax (Nat.clog 2 n) d C 1 r hd hm_n hcard_one
      hroot_high hr_L
  change Nat.min n (2 ^ Nat.clog 2 n * 1) ≤
    (highSet (runPairs P C Lgrow) d).card at hiter_card
  change r ∈ highSet (runPairs P C Lgrow) d at hroot_high_fin
  change ((runPairs P C Lgrow) r).1.leader = .L at hroot_L_fin
  have hlepow : n ≤ 2 ^ Nat.clog 2 n :=
    Nat.le_pow_clog (by omega : 1 < 2) n
  have hminclog : Nat.min n (2 ^ Nat.clog 2 n * 1) = n := by
    apply le_antisymm
    · exact Nat.min_le_left _ _
    · apply le_min
      · exact le_rfl
      · simpa [mul_one] using hlepow
  have hn_le_card : n ≤ (highSet (runPairs P C Lgrow) d).card := by
    rw [hminclog] at hiter_card
    exact hiter_card
  have hcard_eq : (highSet (runPairs P C Lgrow) d).card = n :=
    le_antisymm (highSet_card_le_n (runPairs P C Lgrow) d) hn_le_card
  refine ⟨Lgrow, ?_, ?_⟩
  · change ∀ w : Fin n,
      ((runPairs P C Lgrow) w).1.role = .Resetting ∧
        d ≤ ((runPairs P C Lgrow) w).1.resetcount
    intro w
    exact highSet_card_eq_n_all
      (C := runPairs P C Lgrow) (k := d) hcard_eq w
  · exact hroot_L_fin

set_option maxHeartbeats 12000000 in
-- A log-fueled seed can recruit through balanced generations until every
-- agent is Resetting with strictly positive resetcount.
theorem balanced_tree_growth
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : Nat.clog 2 n + 1 ≤ (C r).1.resetcount) :
    ∃ Lgrow : List (Fin n × Fin n),
      let C₁ := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C Lgrow
      ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧ 0 < (C₁ w).1.resetcount := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hseed : r ∈ highSet C (Nat.clog 2 n + 1) := by
    rw [mem_highSet]
    exact ⟨hr_role, hr_log⟩
  have hcard_one : 1 ≤ (highSet C (1 + Nat.clog 2 n)).card := by
    have hpos : 0 < (highSet C (Nat.clog 2 n + 1)).card :=
      Finset.card_pos.mpr ⟨r, hseed⟩
    have hpos' : 0 < (highSet C (1 + Nat.clog 2 n)).card := by
      simpa [Nat.add_comm] using hpos
    omega
  have hm_n : 1 ≤ n := by omega
  obtain ⟨Lgrow, hiter⟩ :=
    balanced_tree_growth_card_iter
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax (Nat.clog 2 n) 1 C 1 (by omega) hm_n hcard_one
  change Nat.min n (2 ^ Nat.clog 2 n * 1) ≤
    (highSet (runPairs P C Lgrow) 1).card at hiter
  have hlepow : n ≤ 2 ^ Nat.clog 2 n :=
    Nat.le_pow_clog (by omega : 1 < 2) n
  have hminclog : Nat.min n (2 ^ Nat.clog 2 n * 1) = n := by
    apply le_antisymm
    · exact Nat.min_le_left _ _
    · apply le_min
      · exact le_rfl
      · simpa [mul_one] using hlepow
  have hn_le_card : n ≤ (highSet (runPairs P C Lgrow) 1).card := by
    rw [hminclog] at hiter
    exact hiter
  have hcard_eq : (highSet (runPairs P C Lgrow) 1).card = n :=
    le_antisymm (highSet_card_le_n (runPairs P C Lgrow) 1) hn_le_card
  refine ⟨Lgrow, ?_⟩
  change ∀ w : Fin n,
    ((runPairs P C Lgrow) w).1.role = .Resetting ∧
      0 < ((runPairs P C Lgrow) w).1.resetcount
  intro w
  have hw := highSet_card_eq_n_all
    (C := runPairs P C Lgrow) (k := 1) hcard_eq w
  exact ⟨hw.1, by omega⟩

set_option maxHeartbeats 12000000 in
-- The same logarithmic growth proof with an arbitrary positive fuel floor.
-- This is needed for odd-size final drains: a lone leftover must have at
-- least two units of fuel before it is paired with an already-fresh partner.
theorem balanced_tree_growth_floor
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : Nat.clog 2 n + d ≤ (C r).1.resetcount) :
    ∃ Lgrow : List (Fin n × Fin n),
      let C₁ := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C Lgrow
      ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
        d ≤ (C₁ w).1.resetcount := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hseed : r ∈ highSet C (Nat.clog 2 n + d) := by
    rw [mem_highSet]
    exact ⟨hr_role, hr_log⟩
  have hcard_one : 1 ≤ (highSet C (d + Nat.clog 2 n)).card := by
    have hpos : 0 < (highSet C (Nat.clog 2 n + d)).card :=
      Finset.card_pos.mpr ⟨r, hseed⟩
    have hpos' : 0 < (highSet C (d + Nat.clog 2 n)).card := by
      simpa [Nat.add_comm] using hpos
    omega
  have hm_n : 1 ≤ n := by omega
  obtain ⟨Lgrow, hiter⟩ :=
    balanced_tree_growth_card_iter
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax (Nat.clog 2 n) d C 1 hd hm_n hcard_one
  change Nat.min n (2 ^ Nat.clog 2 n * 1) ≤
    (highSet (runPairs P C Lgrow) d).card at hiter
  have hlepow : n ≤ 2 ^ Nat.clog 2 n :=
    Nat.le_pow_clog (by omega : 1 < 2) n
  have hminclog : Nat.min n (2 ^ Nat.clog 2 n * 1) = n := by
    apply le_antisymm
    · exact Nat.min_le_left _ _
    · apply le_min
      · exact le_rfl
      · simpa [mul_one] using hlepow
  have hn_le_card : n ≤ (highSet (runPairs P C Lgrow) d).card := by
    rw [hminclog] at hiter
    exact hiter
  have hcard_eq : (highSet (runPairs P C Lgrow) d).card = n :=
    le_antisymm (highSet_card_le_n (runPairs P C Lgrow) d) hn_le_card
  refine ⟨Lgrow, ?_⟩
  change ∀ w : Fin n,
    ((runPairs P C Lgrow) w).1.role = .Resetting ∧
      d ≤ ((runPairs P C Lgrow) w).1.resetcount
  intro w
  exact highSet_card_eq_n_all
    (C := runPairs P C Lgrow) (k := d) hcard_eq w

set_option maxHeartbeats 16000000 in
-- Final cardinal saturation packages the floor and answer invariant.
theorem balanced_tree_growth_floor_answer
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : Nat.clog 2 n + d ≤ (C r).1.resetcount)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    ∃ Lgrow : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C₁ := runPairs P C Lgrow
      (∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
        d ≤ (C₁ w).1.resetcount) ∧
      (∀ w : Fin n, (C₁ w).1.role = .Resetting →
        (C₁ w).1.answer = majorityAnswer C₁) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hseed : r ∈ highSet C (Nat.clog 2 n + d) := by
    rw [mem_highSet]
    exact ⟨hr_role, hr_log⟩
  have hcard_one : 1 ≤ (highSet C (d + Nat.clog 2 n)).card := by
    have hpos : 0 < (highSet C (Nat.clog 2 n + d)).card :=
      Finset.card_pos.mpr ⟨r, hseed⟩
    have hpos' : 0 < (highSet C (d + Nat.clog 2 n)).card := by
      simpa [Nat.add_comm] using hpos
    omega
  have hm_n : 1 ≤ n := by omega
  obtain ⟨Lgrow, hiter_card, hiter_ans⟩ :=
    balanced_tree_growth_card_iter_answer
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax (Nat.clog 2 n) d C 1 hd hm_n hcard_one hAllAns
  change Nat.min n (2 ^ Nat.clog 2 n * 1) ≤
    (highSet (runPairs P C Lgrow) d).card at hiter_card
  change ∀ w : Fin n, ((runPairs P C Lgrow) w).1.role = .Resetting →
    ((runPairs P C Lgrow) w).1.answer =
      majorityAnswer (runPairs P C Lgrow) at hiter_ans
  have hlepow : n ≤ 2 ^ Nat.clog 2 n :=
    Nat.le_pow_clog (by omega : 1 < 2) n
  have hminclog : Nat.min n (2 ^ Nat.clog 2 n * 1) = n := by
    apply le_antisymm
    · exact Nat.min_le_left _ _
    · apply le_min
      · exact le_rfl
      · simpa [mul_one] using hlepow
  have hn_le_card : n ≤ (highSet (runPairs P C Lgrow) d).card := by
    rw [hminclog] at hiter_card
    exact hiter_card
  have hcard_eq : (highSet (runPairs P C Lgrow) d).card = n :=
    le_antisymm (highSet_card_le_n (runPairs P C Lgrow) d) hn_le_card
  refine ⟨Lgrow, ?_, ?_⟩
  · change ∀ w : Fin n,
      ((runPairs P C Lgrow) w).1.role = .Resetting ∧
        d ≤ ((runPairs P C Lgrow) w).1.resetcount
    intro w
    exact highSet_card_eq_n_all
      (C := runPairs P C Lgrow) (k := d) hcard_eq w
  · exact hiter_ans

set_option maxHeartbeats 16000000 in
-- Final cardinal saturation packages the floor, answer invariant, and root leader.
theorem balanced_tree_growth_floor_answer_leader
    {n Rmax Emax Dmax d : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hd : 0 < d)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : Nat.clog 2 n + d ≤ (C r).1.resetcount)
    (hr_L : (C r).1.leader = .L)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    ∃ Lgrow : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C₁ := runPairs P C Lgrow
      (∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
        d ≤ (C₁ w).1.resetcount) ∧
      (∀ w : Fin n, (C₁ w).1.role = .Resetting →
        (C₁ w).1.answer = majorityAnswer C₁) ∧
      (C₁ r).1.leader = .L := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hseed : r ∈ highSet C (Nat.clog 2 n + d) := by
    rw [mem_highSet]
    exact ⟨hr_role, hr_log⟩
  have hcard_one : 1 ≤ (highSet C (d + Nat.clog 2 n)).card := by
    have hpos : 0 < (highSet C (Nat.clog 2 n + d)).card :=
      Finset.card_pos.mpr ⟨r, hseed⟩
    have hpos' : 0 < (highSet C (d + Nat.clog 2 n)).card := by
      simpa [Nat.add_comm] using hpos
    omega
  have hroot_high : r ∈ highSet C (d + Nat.clog 2 n) := by
    simpa [Nat.add_comm] using hseed
  have hm_n : 1 ≤ n := by omega
  obtain ⟨Lgrow, hiter_card, hiter_ans, hroot_high_fin, hroot_L_fin⟩ :=
    balanced_tree_growth_card_iter_answer_root
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax (Nat.clog 2 n) d C 1 r hd hm_n hcard_one
      hAllAns hroot_high hr_L
  change Nat.min n (2 ^ Nat.clog 2 n * 1) ≤
    (highSet (runPairs P C Lgrow) d).card at hiter_card
  change ∀ w : Fin n, ((runPairs P C Lgrow) w).1.role = .Resetting →
    ((runPairs P C Lgrow) w).1.answer =
      majorityAnswer (runPairs P C Lgrow) at hiter_ans
  change r ∈ highSet (runPairs P C Lgrow) d at hroot_high_fin
  change ((runPairs P C Lgrow) r).1.leader = .L at hroot_L_fin
  have hlepow : n ≤ 2 ^ Nat.clog 2 n :=
    Nat.le_pow_clog (by omega : 1 < 2) n
  have hminclog : Nat.min n (2 ^ Nat.clog 2 n * 1) = n := by
    apply le_antisymm
    · exact Nat.min_le_left _ _
    · apply le_min
      · exact le_rfl
      · simpa [mul_one] using hlepow
  have hn_le_card : n ≤ (highSet (runPairs P C Lgrow) d).card := by
    rw [hminclog] at hiter_card
    exact hiter_card
  have hcard_eq : (highSet (runPairs P C Lgrow) d).card = n :=
    le_antisymm (highSet_card_le_n (runPairs P C Lgrow) d) hn_le_card
  refine ⟨Lgrow, ?_, ?_, ?_⟩
  · change ∀ w : Fin n,
      ((runPairs P C Lgrow) w).1.role = .Resetting ∧
        d ≤ ((runPairs P C Lgrow) w).1.resetcount
    intro w
    exact highSet_card_eq_n_all
      (C := runPairs P C Lgrow) (k := d) hcard_eq w
  · exact hiter_ans
  · exact hroot_L_fin

theorem rankDeltaOSSR_both_rc_pos_snd_delay_final
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hnew : Nat.max (s.resetcount - 1) (t.resetcount - 1) = 0)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer = Dmax := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hnew, show (Dmax : ℕ) ≠ 0 from by omega]
  by_cases hLL : s.leader = .L ∧ t.leader = .L <;> simp [hLL]

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_fst_delay_final_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hnew : Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) = 0) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.delaytimer = Dmax := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd_role := rankDeltaOSSR_both_rc_pos_role
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hDmax
  have h_rd_delay := rankDeltaOSSR_both_rc_pos_fst_delay_final
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hnew hDmax
  have h_not_both :
      ¬ ((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd_role.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough
    (trank := τ) (Rmax := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  change (C.step P u v u).1.delaytimer = Dmax
  rw [congrArg AgentState.delaytimer h_fst]
  exact h_pass.2.2.2.2.2.1 ▸ h_rd_delay

set_option maxHeartbeats 4000000 in
-- Transporting the rank-delta delay trace through `transitionPEM` exposes a
-- deeply nested structural passthrough tuple.
theorem step_both_rc_pos_snd_delay_final
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hnew : Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) = 0) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' v).1.delaytimer = Dmax := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd_role := rankDeltaOSSR_both_rc_pos_role (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hDmax
  have h_rd_delay := rankDeltaOSSR_both_rc_pos_snd_delay_final
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hnew hDmax
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd_role.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := τ) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_snd := Config.step_snd_state P C huv huv.symm
  change (C.step P u v v).1.delaytimer = Dmax
  rw [congrArg AgentState.delaytimer h_snd]
  exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd_delay

set_option maxHeartbeats 8000000 in
-- The proof mirrors the existing one-sided pair-drain induction while carrying
-- the extra symmetric delaytimer endpoint.
theorem drain_pair_rc_with_both_delay
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      FreshResettingAt Dmax (runPairs P C L) u ∧
      FreshResettingAt Dmax (runPairs P C L) v ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      ∃ L,
        FreshResettingAt Dmax (runPairs P C' L) u ∧
        FreshResettingAt Dmax (runPairs P C' L) v ∧
        ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc le_rfl
  intro k
  induction k with
  | zero =>
      intros C' _ _ hu_rc' _ hmax
      exfalso
      have hle : (C' u).1.resetcount ≤
          Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
        Nat.le_max_left _ _
      omega
  | succ k ih =>
      intros C' hu_res' hv_res' hu_rc' hv_rc' hmax
      have h_step := step_both_rc_pos_trank (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc'
      have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
      have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
      have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) :=
        h_step.2.2.1
      have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) :=
        h_step.2.2.2.1
      have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
        intro w hwu hwv
        simp [Config.step, huv, hwu, hwv]
      have hM_le :
          Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) ≤ k := by
        have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
          have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
            Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
          omega
        have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
          have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
            Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
          omega
        have hpred :
            Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
          max_le hu_pred_le hv_pred_le
        rw [hu_rc₁_eq, hv_rc₁_eq]
        exact max_le hpred hpred
      by_cases hdone :
          Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
      · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
          have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount)
          exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
        have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
          have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount)
          exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
        have hnew :
            Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) = 0 := by
          have hdone' := hdone
          rw [hu_rc₁_eq, hv_rc₁_eq] at hdone'
          simpa using hdone'
        have hu_delay₁ : (C'.step P u v u).1.delaytimer = Dmax :=
          step_both_rc_pos_fst_delay_final_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
        have hv_delay₁ : (C'.step P u v v).1.delaytimer = Dmax :=
          step_both_rc_pos_snd_delay_final
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
        refine ⟨[(u, v)], ?_, ?_, ?_⟩
        · change FreshResettingAt Dmax (C'.step P u v) u
          exact ⟨hu_role₁, hu_zero, hu_delay₁⟩
        · change FreshResettingAt Dmax (C'.step P u v) v
          exact ⟨hv_role₁, hv_zero, hv_delay₁⟩
        · intro w hwu hwv
          change C'.step P u v w = C' w
          exact h_others w hwu hwv
      · have hu_pos₁ : 0 < (C'.step P u v u).1.resetcount := by
          have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
              ((C'.step P u v v).1.resetcount) :=
            Nat.pos_of_ne_zero hdone
          simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
        have hv_pos₁ : 0 < (C'.step P u v v).1.resetcount := by
          have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
              ((C'.step P u v v).1.resetcount) :=
            Nat.pos_of_ne_zero hdone
          simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
        obtain ⟨Ltail, hu_fresh_t, hv_fresh_t, h_others_t⟩ :=
          ih (C'.step P u v) hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hM_le
        refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_⟩
        · rw [runPairs_append]
          change FreshResettingAt Dmax (runPairs P (C'.step P u v) Ltail) u
          simpa [runPairs] using hu_fresh_t
        · rw [runPairs_append]
          change FreshResettingAt Dmax (runPairs P (C'.step P u v) Ltail) v
          simpa [runPairs] using hv_fresh_t
        · intro w hwu hwv
          rw [runPairs_append]
          change runPairs P (C'.step P u v) Ltail w = C' w
          rw [h_others_t w hwu hwv]
          exact h_others w hwu hwv

set_option maxHeartbeats 16000000 in
-- Pair drain with the invariants needed by the faithful log endpoint.
theorem drain_pair_rc_with_both_delay_uniform_unique
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    (hm : m ≠ .phi)
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      FreshResettingAt Dmax (runPairs P C L) u ∧
      FreshResettingAt Dmax (runPairs P C L) v ∧
      (∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w) ∧
      (∀ w : Fin n, (runPairs P C L w).1.answer = m) ∧
      (∃! ℓ : Fin n, (runPairs P C L ℓ).1.leader = .L) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      (∀ w : Fin n, (C' w).1.answer = m) →
      (∃! ℓ : Fin n, (C' ℓ).1.leader = .L) →
      ∃ L,
        FreshResettingAt Dmax (runPairs P C' L) u ∧
        FreshResettingAt Dmax (runPairs P C' L) v ∧
        (∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w) ∧
        (∀ w : Fin n, (runPairs P C' L w).1.answer = m) ∧
        (∃! ℓ : Fin n, (runPairs P C' L ℓ).1.leader = .L) by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc le_rfl hAllM hUnique
  intro k
  induction k with
  | zero =>
      intros C' _ _ hu_rc' _ hmax _ _
      exfalso
      have hle : (C' u).1.resetcount ≤
          Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
        Nat.le_max_left _ _
      omega
  | succ k ih =>
      intros C' hu_res' hv_res' hu_rc' hv_rc' hmax hAllM' hUnique'
      have h_step := step_both_rc_pos_trank (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc'
      have hAllM₁ :
          ∀ w : Fin n, (C'.step P u v w).1.answer = m := by
        simpa [P] using
          step_both_resetting_pos_preserves_uniform_answer_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (m := m) hm (C := C') (a := u) (b := v) huv
            hAllM' hu_res' hv_res' hu_rc' hv_rc' (by omega : 0 < Dmax)
      have hUnique₁ :
          ∃! ℓ : Fin n, (C'.step P u v ℓ).1.leader = .L := by
        simpa [P] using
          step_both_rc_pos_preserves_uniqueLeader
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hUnique'
      have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
      have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
      have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) :=
        h_step.2.2.1
      have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) :=
        h_step.2.2.2.1
      have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
        intro w hwu hwv
        simp [Config.step, huv, hwu, hwv]
      have hM_le :
          Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) ≤ k := by
        have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
          have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
            Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
          omega
        have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
          have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
            Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
          omega
        have hpred :
            Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
          max_le hu_pred_le hv_pred_le
        rw [hu_rc₁_eq, hv_rc₁_eq]
        exact max_le hpred hpred
      by_cases hdone :
          Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
      · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
          have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount)
          exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
        have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
          have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount)
          exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
        have hnew :
            Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) = 0 := by
          have hdone' := hdone
          rw [hu_rc₁_eq, hv_rc₁_eq] at hdone'
          simpa using hdone'
        have hu_delay₁ : (C'.step P u v u).1.delaytimer = Dmax :=
          step_both_rc_pos_fst_delay_final_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
        have hv_delay₁ : (C'.step P u v v).1.delaytimer = Dmax :=
          step_both_rc_pos_snd_delay_final
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
        refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_⟩
        · change FreshResettingAt Dmax (C'.step P u v) u
          exact ⟨hu_role₁, hu_zero, hu_delay₁⟩
        · change FreshResettingAt Dmax (C'.step P u v) v
          exact ⟨hv_role₁, hv_zero, hv_delay₁⟩
        · intro w hwu hwv
          change C'.step P u v w = C' w
          exact h_others w hwu hwv
        · change ∀ w : Fin n, (C'.step P u v w).1.answer = m
          exact hAllM₁
        · change ∃! ℓ : Fin n, (C'.step P u v ℓ).1.leader = .L
          exact hUnique₁
      · have hu_pos₁ : 0 < (C'.step P u v u).1.resetcount := by
          have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
              ((C'.step P u v v).1.resetcount) :=
            Nat.pos_of_ne_zero hdone
          simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
        have hv_pos₁ : 0 < (C'.step P u v v).1.resetcount := by
          have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
              ((C'.step P u v v).1.resetcount) :=
            Nat.pos_of_ne_zero hdone
          simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
        obtain ⟨Ltail, hu_fresh_t, hv_fresh_t, h_others_t, hAllM_t, hUnique_t⟩ :=
          ih (C'.step P u v) hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hM_le
            hAllM₁ hUnique₁
        refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_⟩
        · rw [runPairs_append]
          change FreshResettingAt Dmax (runPairs P (C'.step P u v) Ltail) u
          simpa [runPairs] using hu_fresh_t
        · rw [runPairs_append]
          change FreshResettingAt Dmax (runPairs P (C'.step P u v) Ltail) v
          simpa [runPairs] using hv_fresh_t
        · intro w hwu hwv
          rw [runPairs_append]
          change runPairs P (C'.step P u v) Ltail w = C' w
          rw [h_others_t w hwu hwv]
          exact h_others w hwu hwv
        · rw [runPairs_append]
          change ∀ w : Fin n, (runPairs P (C'.step P u v) Ltail w).1.answer = m
          exact hAllM_t
        · rw [runPairs_append]
          change ∃! ℓ : Fin n, (runPairs P (C'.step P u v) Ltail ℓ).1.leader = .L
          exact hUnique_t

set_option maxHeartbeats 12000000 in
-- Pair drain preserving the unique leader, without assuming anything about
-- answers.
theorem drain_pair_rc_with_both_delay_unique
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      FreshResettingAt Dmax (runPairs P C L) u ∧
      FreshResettingAt Dmax (runPairs P C L) v ∧
      (∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w) ∧
      (∃! ℓ : Fin n, (runPairs P C L ℓ).1.leader = .L) := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      (∃! ℓ : Fin n, (C' ℓ).1.leader = .L) →
      ∃ L,
        FreshResettingAt Dmax (runPairs P C' L) u ∧
        FreshResettingAt Dmax (runPairs P C' L) v ∧
        (∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w) ∧
        (∃! ℓ : Fin n, (runPairs P C' L ℓ).1.leader = .L) by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc le_rfl hUnique
  intro k
  induction k with
  | zero =>
      intros C' _ _ hu_rc' _ hmax _
      exfalso
      have hle : (C' u).1.resetcount ≤
          Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
        Nat.le_max_left _ _
      omega
  | succ k ih =>
      intros C' hu_res' hv_res' hu_rc' hv_rc' hmax hUnique'
      have h_step := step_both_rc_pos_trank (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc'
      have hUnique₁ :
          ∃! ℓ : Fin n, (C'.step P u v ℓ).1.leader = .L := by
        simpa [P] using
          step_both_rc_pos_preserves_uniqueLeader
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hUnique'
      have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
      have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
      have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) :=
        h_step.2.2.1
      have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) :=
        h_step.2.2.2.1
      have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
        intro w hwu hwv
        simp [Config.step, huv, hwu, hwv]
      have hM_le :
          Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) ≤ k := by
        have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
          have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
            Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
          omega
        have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
          have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
            Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
          omega
        have hpred :
            Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
          max_le hu_pred_le hv_pred_le
        rw [hu_rc₁_eq, hv_rc₁_eq]
        exact max_le hpred hpred
      by_cases hdone :
          Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
      · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
          have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount)
          exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
        have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
          have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount)
          exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
        have hnew :
            Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) = 0 := by
          have hdone' := hdone
          rw [hu_rc₁_eq, hv_rc₁_eq] at hdone'
          simpa using hdone'
        have hu_delay₁ : (C'.step P u v u).1.delaytimer = Dmax :=
          step_both_rc_pos_fst_delay_final_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
        have hv_delay₁ : (C'.step P u v v).1.delaytimer = Dmax :=
          step_both_rc_pos_snd_delay_final
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
        refine ⟨[(u, v)], ?_, ?_, ?_, ?_⟩
        · change FreshResettingAt Dmax (C'.step P u v) u
          exact ⟨hu_role₁, hu_zero, hu_delay₁⟩
        · change FreshResettingAt Dmax (C'.step P u v) v
          exact ⟨hv_role₁, hv_zero, hv_delay₁⟩
        · intro w hwu hwv
          change C'.step P u v w = C' w
          exact h_others w hwu hwv
        · change ∃! ℓ : Fin n, (C'.step P u v ℓ).1.leader = .L
          exact hUnique₁
      · have hu_pos₁ : 0 < (C'.step P u v u).1.resetcount := by
          have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
              ((C'.step P u v v).1.resetcount) :=
            Nat.pos_of_ne_zero hdone
          simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
        have hv_pos₁ : 0 < (C'.step P u v v).1.resetcount := by
          have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
              ((C'.step P u v v).1.resetcount) :=
            Nat.pos_of_ne_zero hdone
          simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
        obtain ⟨Ltail, hu_fresh_t, hv_fresh_t, h_others_t, hUnique_t⟩ :=
          ih (C'.step P u v) hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hM_le hUnique₁
        refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_⟩
        · rw [runPairs_append]
          change FreshResettingAt Dmax (runPairs P (C'.step P u v) Ltail) u
          simpa [runPairs] using hu_fresh_t
        · rw [runPairs_append]
          change FreshResettingAt Dmax (runPairs P (C'.step P u v) Ltail) v
          simpa [runPairs] using hv_fresh_t
        · intro w hwu hwv
          rw [runPairs_append]
          change runPairs P (C'.step P u v) Ltail w = C' w
          rw [h_others_t w hwu hwv]
          exact h_others w hwu hwv
        · rw [runPairs_append]
          change ∃! ℓ : Fin n, (runPairs P (C'.step P u v) Ltail ℓ).1.leader = .L
          exact hUnique_t

theorem drain_positive_with_fresh_partner
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount)
    (hv_fresh : FreshResettingAt Dmax C v) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      FreshResettingAt Dmax (runPairs P C L) u ∧
      FreshResettingAt Dmax (runPairs P C L) v ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hstep := step_resetting_pos_resetting_zero
    (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    C huv hu_res hv_fresh.1 hu_rc hv_fresh.2.1
  have hu_res₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_res₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
    have hrc := hstep.2.2.1
    dsimp [C₁, P]
    rw [hrc]
    omega
  have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
    have hrc := hstep.2.2.2
    dsimp [C₁, P]
    rw [hrc]
    omega
  obtain ⟨Ltail, hu_fresh, hv_fresh_tail, htail⟩ :=
    drain_pair_rc_with_both_delay
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C₁ huv hu_res₁ hv_res₁ hu_pos₁ hv_pos₁
  refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_⟩
  · rw [runPairs_append]
    change FreshResettingAt Dmax (runPairs P C₁ Ltail) u
    exact hu_fresh
  · rw [runPairs_append]
    change FreshResettingAt Dmax (runPairs P C₁ Ltail) v
    exact hv_fresh_tail
  · intro w hwu hwv
    rw [runPairs_append]
    change runPairs P C₁ Ltail w = C w
    rw [htail w hwu hwv]
    dsimp [C₁, P]
    simp [Config.step, huv, hwu, hwv]

set_option maxHeartbeats 20000000 in
-- Odd-leftover drain preserving only the unique leader.
theorem drain_positive_with_fresh_partner_unique
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount)
    (hv_fresh : FreshResettingAt Dmax C v)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      FreshResettingAt Dmax (runPairs P C L) u ∧
      FreshResettingAt Dmax (runPairs P C L) v ∧
      (∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w) ∧
      (∃! ℓ : Fin n, (runPairs P C L ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hv_res : (C v).1.role = .Resetting := hv_fresh.1
  have hv_rc0 : (C v).1.resetcount = 0 := hv_fresh.2.1
  have hv_dt : 1 < (C v).1.delaytimer := by
    rw [hv_fresh.2.2]
    exact hDmax
  have hothers_uv : ∀ w : Fin n, w ≠ u → w ≠ v → C.step P u v w = C w := by
    intro w hwu hwv
    simp [Config.step, huv, hwu, hwv]
  have hothers_vu : ∀ w : Fin n, w ≠ v → w ≠ u → C.step P v u w = C w := by
    intro w hwv hwu
    simp [Config.step, huv.symm, hwv, hwu]
  have unique_of_leaderSet_eq {C' : Config (AgentState n) Opinion n}
      (hEq : leaderSet C' = leaderSet C) :
      ∃! ℓ : Fin n, (C' ℓ).1.leader = .L := by
    rcases hUnique with ⟨ℓ, hℓL, huniq⟩
    refine ⟨ℓ, ?_, ?_⟩
    · have hmem : ℓ ∈ leaderSet C' := by
        rw [hEq, mem_leaderSet]
        exact hℓL
      exact mem_leaderSet.mp hmem
    · intro x hx
      apply huniq
      have hmem : x ∈ leaderSet C := by
        rw [← hEq, mem_leaderSet]
        exact hx
      exact mem_leaderSet.mp hmem
  cases hu_leader : (C u).1.leader with
  | L =>
      cases hv_leader : (C v).1.leader with
      | L =>
          rcases hUnique with ⟨ℓ, _hℓ, huniq⟩
          have hu_eq : u = ℓ := huniq u hu_leader
          have hv_eq : v = ℓ := huniq v hv_leader
          exact False.elim (huv (by rw [hu_eq, hv_eq]))
      | F =>
          have hstep := step_L_pos_F_zero_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C huv hu_res hv_res
            (by omega : 0 < (C u).1.resetcount) hv_rc0 hu_leader hv_leader hv_dt
          let C₁ : Config (AgentState n) Opinion n := C.step P u v
          have hEq : leaderSet C₁ = leaderSet C := by
            dsimp [C₁]
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwu : w = u
            · subst w
              rw [hstep.2.2.2.2.1, hu_leader]
            · by_cases hwv : w = v
              · subst w
                rw [hstep.2.2.2.2.2.1, hv_leader]
              · rw [hothers_uv w hwu hwv]
          have hUnique₁ : ∃! ℓ : Fin n, (C₁ ℓ).1.leader = .L :=
            unique_of_leaderSet_eq hEq
          have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.1]
            omega
          have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.2.1]
            omega
          obtain ⟨Ltail, hu_fresh, hv_fresh_tail, htail, hUnique_tail⟩ :=
            drain_pair_rc_with_both_delay_unique
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax C₁ huv
              (by simpa [C₁] using hstep.1)
              (by simpa [C₁] using hstep.2.1)
              hu_pos₁ hv_pos₁ hUnique₁
          refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_⟩
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) u
            exact hu_fresh
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) v
            exact hv_fresh_tail
          · intro w hwu hwv
            rw [runPairs_append]
            change runPairs P C₁ Ltail w = C w
            rw [htail w hwu hwv]
            dsimp [C₁]
            exact hothers_uv w hwu hwv
          · rw [runPairs_append]
            change ∃! ℓ : Fin n, (runPairs P C₁ Ltail ℓ).1.leader = .L
            exact hUnique_tail
  | F =>
      cases hv_leader : (C v).1.leader with
      | F =>
          have hstep := step_F_pos_F_zero_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C huv hu_res hv_res
            (by omega : 0 < (C u).1.resetcount) hv_rc0 hu_leader hv_leader hv_dt
          let C₁ : Config (AgentState n) Opinion n := C.step P u v
          have hEq : leaderSet C₁ = leaderSet C := by
            dsimp [C₁]
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwu : w = u
            · subst w
              rw [hstep.2.2.2.2.1, hu_leader]
            · by_cases hwv : w = v
              · subst w
                rw [hstep.2.2.2.2.2, hv_leader]
              · rw [hothers_uv w hwu hwv]
          have hUnique₁ : ∃! ℓ : Fin n, (C₁ ℓ).1.leader = .L :=
            unique_of_leaderSet_eq hEq
          have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.1]
            omega
          have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.2.1]
            omega
          obtain ⟨Ltail, hu_fresh, hv_fresh_tail, htail, hUnique_tail⟩ :=
            drain_pair_rc_with_both_delay_unique
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax C₁ huv
              (by simpa [C₁] using hstep.1)
              (by simpa [C₁] using hstep.2.1)
              hu_pos₁ hv_pos₁ hUnique₁
          refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_⟩
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) u
            exact hu_fresh
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) v
            exact hv_fresh_tail
          · intro w hwu hwv
            rw [runPairs_append]
            change runPairs P C₁ Ltail w = C w
            rw [htail w hwu hwv]
            dsimp [C₁]
            exact hothers_uv w hwu hwv
          · rw [runPairs_append]
            change ∃! ℓ : Fin n, (runPairs P C₁ Ltail ℓ).1.leader = .L
            exact hUnique_tail
      | L =>
          have hstep := step_L_zero_F_pos_gt_one_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C huv.symm hv_res hu_res hv_rc0 hu_rc hv_leader hu_leader
          let C₁ : Config (AgentState n) Opinion n := C.step P v u
          have hEq : leaderSet C₁ = leaderSet C := by
            dsimp [C₁]
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwv : w = v
            · subst w
              rw [hstep.2.2.2.2.1, hv_leader]
            · by_cases hwu : w = u
              · subst w
                rw [hstep.2.2.2.2.2, hu_leader]
              · rw [hothers_vu w hwv hwu]
          have hUnique₁ : ∃! ℓ : Fin n, (C₁ ℓ).1.leader = .L :=
            unique_of_leaderSet_eq hEq
          have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.1]
            omega
          have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.2.1]
            omega
          obtain ⟨Ltail, hv_fresh_tail, hu_fresh, htail, hUnique_tail⟩ :=
            drain_pair_rc_with_both_delay_unique
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax C₁ huv.symm
              (by simpa [C₁] using hstep.1)
              (by simpa [C₁] using hstep.2.1)
              hv_pos₁ hu_pos₁ hUnique₁
          refine ⟨[(v, u)] ++ Ltail, ?_, ?_, ?_, ?_⟩
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) u
            exact hu_fresh
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) v
            exact hv_fresh_tail
          · intro w hwu hwv
            rw [runPairs_append]
            change runPairs P C₁ Ltail w = C w
            rw [htail w hwv hwu]
            dsimp [C₁]
            exact hothers_vu w hwv hwu
          · rw [runPairs_append]
            change ∃! ℓ : Fin n, (runPairs P C₁ Ltail ℓ).1.leader = .L
            exact hUnique_tail

set_option maxHeartbeats 24000000 in
-- Odd-leftover drain preserving uniform answer and the unique leader.
theorem drain_positive_with_fresh_partner_uniform_unique
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    (hm : m ≠ .phi)
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount)
    (hv_fresh : FreshResettingAt Dmax C v)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      FreshResettingAt Dmax (runPairs P C L) u ∧
      FreshResettingAt Dmax (runPairs P C L) v ∧
      (∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w) ∧
      (∀ w : Fin n, (runPairs P C L w).1.answer = m) ∧
      (∃! ℓ : Fin n, (runPairs P C L ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hv_res : (C v).1.role = .Resetting := hv_fresh.1
  have hv_rc0 : (C v).1.resetcount = 0 := hv_fresh.2.1
  have hv_dt : 1 < (C v).1.delaytimer := by
    rw [hv_fresh.2.2]
    exact hDmax
  have hothers_uv : ∀ w : Fin n, w ≠ u → w ≠ v → C.step P u v w = C w := by
    intro w hwu hwv
    simp [Config.step, huv, hwu, hwv]
  have hothers_vu : ∀ w : Fin n, w ≠ v → w ≠ u → C.step P v u w = C w := by
    intro w hwv hwu
    simp [Config.step, huv.symm, hwv, hwu]
  have unique_of_leaderSet_eq {C' : Config (AgentState n) Opinion n}
      (hEq : leaderSet C' = leaderSet C) :
      ∃! ℓ : Fin n, (C' ℓ).1.leader = .L := by
    rcases hUnique with ⟨ℓ, hℓL, huniq⟩
    refine ⟨ℓ, ?_, ?_⟩
    · have hmem : ℓ ∈ leaderSet C' := by
        rw [hEq, mem_leaderSet]
        exact hℓL
      exact mem_leaderSet.mp hmem
    · intro x hx
      apply huniq
      have hmem : x ∈ leaderSet C := by
        rw [← hEq, mem_leaderSet]
        exact hx
      exact mem_leaderSet.mp hmem
  cases hu_leader : (C u).1.leader with
  | L =>
      cases hv_leader : (C v).1.leader with
      | L =>
          rcases hUnique with ⟨ℓ, _hℓ, huniq⟩
          have hu_eq : u = ℓ := huniq u hu_leader
          have hv_eq : v = ℓ := huniq v hv_leader
          exact False.elim (huv (by rw [hu_eq, hv_eq]))
      | F =>
          have hstep := step_L_pos_F_zero_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C huv hu_res hv_res
            (by omega : 0 < (C u).1.resetcount) hv_rc0 hu_leader hv_leader hv_dt
          let C₁ : Config (AgentState n) Opinion n := C.step P u v
          have hAllM₁ : ∀ w : Fin n, (C₁ w).1.answer = m := by
            intro w
            dsimp [C₁]
            simpa [P] using
              step_resetting_pos_zero_preserves_uniform_answer
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (m := m) hm C huv hAllM hu_res hv_res hu_rc hv_rc0 w
          have hEq : leaderSet C₁ = leaderSet C := by
            dsimp [C₁]
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwu : w = u
            · subst w
              rw [hstep.2.2.2.2.1, hu_leader]
            · by_cases hwv : w = v
              · subst w
                rw [hstep.2.2.2.2.2.1, hv_leader]
              · rw [hothers_uv w hwu hwv]
          have hUnique₁ : ∃! ℓ : Fin n, (C₁ ℓ).1.leader = .L :=
            unique_of_leaderSet_eq hEq
          have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.1]
            omega
          have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.2.1]
            omega
          obtain ⟨Ltail, hu_fresh, hv_fresh_tail, htail, hAllM_tail, hUnique_tail⟩ :=
            drain_pair_rc_with_both_delay_uniform_unique
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (m := m) hm hDmax C₁ huv
              (by simpa [C₁] using hstep.1)
              (by simpa [C₁] using hstep.2.1)
              hu_pos₁ hv_pos₁ hAllM₁ hUnique₁
          refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_⟩
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) u
            exact hu_fresh
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) v
            exact hv_fresh_tail
          · intro w hwu hwv
            rw [runPairs_append]
            change runPairs P C₁ Ltail w = C w
            rw [htail w hwu hwv]
            dsimp [C₁]
            exact hothers_uv w hwu hwv
          · rw [runPairs_append]
            change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.answer = m
            exact hAllM_tail
          · rw [runPairs_append]
            change ∃! ℓ : Fin n, (runPairs P C₁ Ltail ℓ).1.leader = .L
            exact hUnique_tail
  | F =>
      cases hv_leader : (C v).1.leader with
      | F =>
          have hstep := step_F_pos_F_zero_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (by omega : 0 < Dmax) C huv hu_res hv_res
            (by omega : 0 < (C u).1.resetcount) hv_rc0 hu_leader hv_leader hv_dt
          let C₁ : Config (AgentState n) Opinion n := C.step P u v
          have hAllM₁ : ∀ w : Fin n, (C₁ w).1.answer = m := by
            intro w
            dsimp [C₁]
            simpa [P] using
              step_resetting_pos_zero_preserves_uniform_answer
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (m := m) hm C huv hAllM hu_res hv_res hu_rc hv_rc0 w
          have hEq : leaderSet C₁ = leaderSet C := by
            dsimp [C₁]
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwu : w = u
            · subst w
              rw [hstep.2.2.2.2.1, hu_leader]
            · by_cases hwv : w = v
              · subst w
                rw [hstep.2.2.2.2.2, hv_leader]
              · rw [hothers_uv w hwu hwv]
          have hUnique₁ : ∃! ℓ : Fin n, (C₁ ℓ).1.leader = .L :=
            unique_of_leaderSet_eq hEq
          have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.1]
            omega
          have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.2.1]
            omega
          obtain ⟨Ltail, hu_fresh, hv_fresh_tail, htail, hAllM_tail, hUnique_tail⟩ :=
            drain_pair_rc_with_both_delay_uniform_unique
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (m := m) hm hDmax C₁ huv
              (by simpa [C₁] using hstep.1)
              (by simpa [C₁] using hstep.2.1)
              hu_pos₁ hv_pos₁ hAllM₁ hUnique₁
          refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_⟩
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) u
            exact hu_fresh
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) v
            exact hv_fresh_tail
          · intro w hwu hwv
            rw [runPairs_append]
            change runPairs P C₁ Ltail w = C w
            rw [htail w hwu hwv]
            dsimp [C₁]
            exact hothers_uv w hwu hwv
          · rw [runPairs_append]
            change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.answer = m
            exact hAllM_tail
          · rw [runPairs_append]
            change ∃! ℓ : Fin n, (runPairs P C₁ Ltail ℓ).1.leader = .L
            exact hUnique_tail
      | L =>
          have hstep := step_L_zero_F_pos_gt_one_trank
            (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C huv.symm hv_res hu_res hv_rc0 hu_rc hv_leader hu_leader
          let C₁ : Config (AgentState n) Opinion n := C.step P v u
          have hAllM₁ : ∀ w : Fin n, (C₁ w).1.answer = m := by
            intro w
            dsimp [C₁]
            simpa [P] using
              step_L_zero_any_pos_preserves_uniform_answer_trank
                (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (m := m) hm (C := C) (u := v) (v := u) huv.symm hAllM
                hv_res hu_res hv_rc0 (by omega : 0 < (C u).1.resetcount)
                hv_leader hv_dt (by omega : 0 < Dmax) w
          have hEq : leaderSet C₁ = leaderSet C := by
            dsimp [C₁]
            ext w
            rw [mem_leaderSet, mem_leaderSet]
            by_cases hwv : w = v
            · subst w
              rw [hstep.2.2.2.2.1, hv_leader]
            · by_cases hwu : w = u
              · subst w
                rw [hstep.2.2.2.2.2, hu_leader]
              · rw [hothers_vu w hwv hwu]
          have hUnique₁ : ∃! ℓ : Fin n, (C₁ ℓ).1.leader = .L :=
            unique_of_leaderSet_eq hEq
          have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.1]
            omega
          have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
            dsimp [C₁]
            rw [hstep.2.2.2.1]
            omega
          obtain ⟨Ltail, hv_fresh_tail, hu_fresh, htail, hAllM_tail, hUnique_tail⟩ :=
            drain_pair_rc_with_both_delay_uniform_unique
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (m := m) hm hDmax C₁ huv.symm
              (by simpa [C₁] using hstep.1)
              (by simpa [C₁] using hstep.2.1)
              hv_pos₁ hu_pos₁ hAllM₁ hUnique₁
          refine ⟨[(v, u)] ++ Ltail, ?_, ?_, ?_, ?_, ?_⟩
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) u
            exact hu_fresh
          · rw [runPairs_append]
            change FreshResettingAt Dmax (runPairs P C₁ Ltail) v
            exact hv_fresh_tail
          · intro w hwu hwv
            rw [runPairs_append]
            change runPairs P C₁ Ltail w = C w
            rw [htail w hwv hwu]
            dsimp [C₁]
            exact hothers_vu w hwv hwu
          · rw [runPairs_append]
            change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.answer = m
            exact hAllM_tail
          · rw [runPairs_append]
            change ∃! ℓ : Fin n, (runPairs P C₁ Ltail ℓ).1.leader = .L
            exact hUnique_tail

theorem drain_pair_list_to_fresh_on_endpoints
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (pairs : List (Fin n × Fin n))
    (C : Config (AgentState n) Opinion n)
    (hdis : PairListDisjoint pairs)
    (hAllReset : ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n, w ∈ pairEndpoints pairs →
        FreshResettingAt Dmax (runPairs P C L) w) ∧
      (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C L w = C w) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  induction pairs generalizing C with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · intro w hw
        simp [pairEndpoints] at hw
      · intro w _hw
        simp only [runPairs_nil]
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      rcases hdis with ⟨huv, hu_not_tail, hv_not_tail, hdis_tail⟩
      have hu_mem : u ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      have hv_mem : v ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      obtain ⟨Luv, hu_fresh, hv_fresh, hothers⟩ :=
        drain_pair_rc_with_both_delay
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C huv (hAllReset u hu_mem) (hAllReset v hv_mem)
          (hAllPos u hu_mem) (hAllPos v hv_mem)
      let C₁ : Config (AgentState n) Opinion n := runPairs P C Luv
      have hAllReset_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps → (C₁ w).1.role = .Resetting := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        have hw_cons : w ∈ pairEndpoints ((u, v) :: ps) := by
          simp [pairEndpoints, hw]
        dsimp [C₁]
        rw [hothers w hwu hwv]
        exact hAllReset w hw_cons
      have hAllPos_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps → 0 < (C₁ w).1.resetcount := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        have hw_cons : w ∈ pairEndpoints ((u, v) :: ps) := by
          simp [pairEndpoints, hw]
        dsimp [C₁]
        rw [hothers w hwu hwv]
        exact hAllPos w hw_cons
      obtain ⟨Ltail, hfresh_tail, hunchanged_tail⟩ :=
        ih C₁ hdis_tail hAllReset_tail hAllPos_tail
      refine ⟨Luv ++ Ltail, ?_, ?_⟩
      · intro w hw
        rw [runPairs_append]
        change FreshResettingAt Dmax (runPairs P C₁ Ltail) w
        have hw' := hw
        simp only [pairEndpoints, Finset.mem_insert] at hw'
        rcases hw' with hwu_eq | hv_or_tail
        · subst w
          have hkeep := hunchanged_tail _ hu_not_tail
          unfold FreshResettingAt
          rw [hkeep]
          simpa [FreshResettingAt, C₁, P] using hu_fresh
        · rcases hv_or_tail with hwv_eq | htail
          · subst w
            have hkeep := hunchanged_tail _ hv_not_tail
            unfold FreshResettingAt
            rw [hkeep]
            simpa [FreshResettingAt, C₁, P] using hv_fresh
          · exact hfresh_tail w htail
      · intro w hw
        rw [runPairs_append]
        change runPairs P C₁ Ltail w = C w
        have hnot_tail : w ∉ pairEndpoints ps := by
          intro htail
          exact hw (by simp [pairEndpoints, htail])
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hw (by simp [pairEndpoints])
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw (by simp [pairEndpoints])
        rw [hunchanged_tail w hnot_tail]
        exact hothers w hwu hwv

set_option maxHeartbeats 24000000 in
-- Disjoint pair-list drain preserving uniform answer and unique leader.
theorem drain_pair_list_to_fresh_on_endpoints_uniform_unique
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    (hm : m ≠ .phi)
    (hDmax : 1 < Dmax)
    (pairs : List (Fin n × Fin n))
    (C : Config (AgentState n) Opinion n)
    (hdis : PairListDisjoint pairs)
    (hAllReset : ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n, w ∈ pairEndpoints pairs →
        FreshResettingAt Dmax (runPairs P C L) w) ∧
      (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C L w = C w) ∧
      (∀ w : Fin n, (runPairs P C L w).1.answer = m) ∧
      (∃! ℓ : Fin n, (runPairs P C L ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  induction pairs generalizing C with
  | nil =>
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · intro w hw
        simp [pairEndpoints] at hw
      · intro w _hw
        simp only [runPairs_nil]
      · simpa [runPairs] using hAllM
      · simpa [runPairs] using hUnique
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      rcases hdis with ⟨huv, hu_not_tail, hv_not_tail, hdis_tail⟩
      have hu_mem : u ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      have hv_mem : v ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      obtain ⟨Luv, hu_fresh, hv_fresh, hothers, hAllM₁, hUnique₁⟩ :=
        drain_pair_rc_with_both_delay_uniform_unique
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (m := m) hm hDmax C huv
          (hAllReset u hu_mem) (hAllReset v hv_mem)
          (hAllPos u hu_mem) (hAllPos v hv_mem)
          hAllM hUnique
      let C₁ : Config (AgentState n) Opinion n := runPairs P C Luv
      have hAllReset_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps → (C₁ w).1.role = .Resetting := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        have hw_cons : w ∈ pairEndpoints ((u, v) :: ps) := by
          simp [pairEndpoints, hw]
        dsimp [C₁]
        rw [hothers w hwu hwv]
        exact hAllReset w hw_cons
      have hAllPos_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps → 0 < (C₁ w).1.resetcount := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        have hw_cons : w ∈ pairEndpoints ((u, v) :: ps) := by
          simp [pairEndpoints, hw]
        dsimp [C₁]
        rw [hothers w hwu hwv]
        exact hAllPos w hw_cons
      obtain ⟨Ltail, hfresh_tail, hunchanged_tail, hAllM_tail, hUnique_tail⟩ :=
        ih C₁ hdis_tail hAllReset_tail hAllPos_tail
          (by simpa [C₁, P] using hAllM₁)
          (by simpa [C₁, P] using hUnique₁)
      refine ⟨Luv ++ Ltail, ?_, ?_, ?_, ?_⟩
      · intro w hw
        rw [runPairs_append]
        change FreshResettingAt Dmax (runPairs P C₁ Ltail) w
        have hw' := hw
        simp only [pairEndpoints, Finset.mem_insert] at hw'
        rcases hw' with hwu_eq | hv_or_tail
        · subst w
          have hkeep := hunchanged_tail _ hu_not_tail
          unfold FreshResettingAt
          rw [hkeep]
          simpa [FreshResettingAt, C₁, P] using hu_fresh
        · rcases hv_or_tail with hwv_eq | htail
          · subst w
            have hkeep := hunchanged_tail _ hv_not_tail
            unfold FreshResettingAt
            rw [hkeep]
            simpa [FreshResettingAt, C₁, P] using hv_fresh
          · exact hfresh_tail w htail
      · intro w hw
        rw [runPairs_append]
        change runPairs P C₁ Ltail w = C w
        have hnot_tail : w ∉ pairEndpoints ps := by
          intro htail
          exact hw (by simp [pairEndpoints, htail])
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hw (by simp [pairEndpoints])
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw (by simp [pairEndpoints])
        rw [hunchanged_tail w hnot_tail]
        exact hothers w hwu hwv
      · rw [runPairs_append]
        change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.answer = m
        exact hAllM_tail
      · rw [runPairs_append]
        change ∃! ℓ : Fin n, (runPairs P C₁ Ltail ℓ).1.leader = .L
        exact hUnique_tail

set_option maxHeartbeats 24000000 in
theorem drain_pair_list_to_fresh_on_endpoints_unique
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (pairs : List (Fin n × Fin n))
    (C : Config (AgentState n) Opinion n)
    (hdis : PairListDisjoint pairs)
    (hAllReset : ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n, w ∈ pairEndpoints pairs →
        FreshResettingAt Dmax (runPairs P C L) w) ∧
      (∀ w : Fin n, w ∉ pairEndpoints pairs → runPairs P C L w = C w) ∧
      (∃! ℓ : Fin n, (runPairs P C L ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  induction pairs generalizing C with
  | nil =>
      refine ⟨[], ?_, ?_, ?_⟩
      · intro w hw
        simp [pairEndpoints] at hw
      · intro w _hw
        simp only [runPairs_nil]
      · simpa [runPairs] using hUnique
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      rcases hdis with ⟨huv, hu_not_tail, hv_not_tail, hdis_tail⟩
      have hu_mem : u ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      have hv_mem : v ∈ pairEndpoints ((u, v) :: ps) := by
        simp [pairEndpoints]
      obtain ⟨Luv, hu_fresh, hv_fresh, hothers, hUnique₁⟩ :=
        drain_pair_rc_with_both_delay_unique
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C huv
          (hAllReset u hu_mem) (hAllReset v hv_mem)
          (hAllPos u hu_mem) (hAllPos v hv_mem)
          hUnique
      let C₁ : Config (AgentState n) Opinion n := runPairs P C Luv
      have hAllReset_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps → (C₁ w).1.role = .Resetting := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        have hw_cons : w ∈ pairEndpoints ((u, v) :: ps) := by
          simp [pairEndpoints, hw]
        dsimp [C₁]
        rw [hothers w hwu hwv]
        exact hAllReset w hw_cons
      have hAllPos_tail :
          ∀ w : Fin n, w ∈ pairEndpoints ps → 0 < (C₁ w).1.resetcount := by
        intro w hw
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hu_not_tail hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hv_not_tail hw
        have hw_cons : w ∈ pairEndpoints ((u, v) :: ps) := by
          simp [pairEndpoints, hw]
        dsimp [C₁]
        rw [hothers w hwu hwv]
        exact hAllPos w hw_cons
      obtain ⟨Ltail, hfresh_tail, hunchanged_tail, hUnique_tail⟩ :=
        ih C₁ hdis_tail hAllReset_tail hAllPos_tail
          (by simpa [C₁, P] using hUnique₁)
      refine ⟨Luv ++ Ltail, ?_, ?_, ?_⟩
      · intro w hw
        rw [runPairs_append]
        change FreshResettingAt Dmax (runPairs P C₁ Ltail) w
        have hw' := hw
        simp only [pairEndpoints, Finset.mem_insert] at hw'
        rcases hw' with hwu_eq | hv_or_tail
        · subst w
          have hkeep := hunchanged_tail _ hu_not_tail
          unfold FreshResettingAt
          rw [hkeep]
          simpa [FreshResettingAt, C₁, P] using hu_fresh
        · rcases hv_or_tail with hwv_eq | htail
          · subst w
            have hkeep := hunchanged_tail _ hv_not_tail
            unfold FreshResettingAt
            rw [hkeep]
            simpa [FreshResettingAt, C₁, P] using hv_fresh
          · exact hfresh_tail w htail
      · intro w hw
        rw [runPairs_append]
        change runPairs P C₁ Ltail w = C w
        have hnot_tail : w ∉ pairEndpoints ps := by
          intro htail
          exact hw (by simp [pairEndpoints, htail])
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hw (by simp [pairEndpoints])
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw (by simp [pairEndpoints])
        rw [hunchanged_tail w hnot_tail]
        exact hothers w hwu hwv
      · rw [runPairs_append]
        change ∃! ℓ : Fin n, (runPairs P C₁ Ltail ℓ).1.leader = .L
        exact hUnique_tail

theorem exists_fin_ne_of_two_le {n : ℕ} (hn2 : 2 ≤ n) (z : Fin n) :
    ∃ y : Fin n, y ≠ z := by
  by_cases hz : z.val = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    intro h
    have hv := congrArg Fin.val h
    simp [hz] at hv
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    exact hz hv.symm

theorem drain_all_floor_two_to_fresh
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hn2 : 2 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAll : ∀ w : Fin n,
      (C w).1.role = .Resetting ∧ 2 ≤ (C w).1.resetcount) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      ∀ w : Fin n, FreshResettingAt Dmax (runPairs P C L) w := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨pairs, leftover, hdis, hend_sub, hleft, hcover⟩ :=
    exists_pair_list_with_optional_leftover (A := (Finset.univ : Finset (Fin n)))
  have hAllReset_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting := by
    intro w _hw
    exact (hAll w).1
  have hAllPos_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount := by
    intro w _hw
    have hw_floor := (hAll w).2
    omega
  obtain ⟨Lpairs, hfresh_pairs, hunchanged_pairs⟩ :=
    drain_pair_list_to_fresh_on_endpoints
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax pairs C hdis hAllReset_pairs hAllPos_pairs
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lpairs
  cases leftover with
  | none =>
      refine ⟨Lpairs, ?_⟩
      intro w
      have hwEnd : w ∈ pairEndpoints pairs := by
        rcases hcover w (Finset.mem_univ w) with hwEnd | hnone
        · exact hwEnd
        · cases hnone
      exact hfresh_pairs w hwEnd
  | some z =>
      have hz_info := hleft z rfl
      obtain ⟨y, hyz⟩ := exists_fin_ne_of_two_le hn2 z
      have hyEnd : y ∈ pairEndpoints pairs := by
        rcases hcover y (Finset.mem_univ y) with hyEnd | hyLeft
        · exact hyEnd
        · injection hyLeft with hzy
          exact False.elim (hyz hzy.symm)
      have hz_unchanged : C₁ z = C z := by
        dsimp [C₁]
        exact hunchanged_pairs z hz_info.2
      have hz_res : (C₁ z).1.role = .Resetting := by
        rw [hz_unchanged]
        exact (hAll z).1
      have hz_rc : 1 < (C₁ z).1.resetcount := by
        rw [hz_unchanged]
        have hz_floor := (hAll z).2
        omega
      have hy_fresh : FreshResettingAt Dmax C₁ y := by
        dsimp [C₁]
        exact hfresh_pairs y hyEnd
      have hzy : z ≠ y := by
        intro h
        exact hyz h.symm
      obtain ⟨Llast, hz_fresh, hy_fresh_last, hlast⟩ :=
        drain_positive_with_fresh_partner
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C₁ hzy hz_res hz_rc hy_fresh
      refine ⟨Lpairs ++ Llast, ?_⟩
      intro w
      rw [runPairs_append]
      change FreshResettingAt Dmax (runPairs P C₁ Llast) w
      by_cases hwz : w = z
      · subst w
        exact hz_fresh
      · by_cases hwy : w = y
        · subst w
          exact hy_fresh_last
        · have hkeep : runPairs P C₁ Llast w = C₁ w :=
            hlast w hwz hwy
          have hwEnd : w ∈ pairEndpoints pairs := by
            rcases hcover w (Finset.mem_univ w) with hwEnd | hwLeft
            · exact hwEnd
            · injection hwLeft with hzw
              exact False.elim (hwz hzw.symm)
          unfold FreshResettingAt
          rw [hkeep]
          simpa [C₁, P, FreshResettingAt] using hfresh_pairs w hwEnd

set_option maxHeartbeats 24000000 in
-- This packages the strengthened pair-list drain with the odd-leftover repair
-- while carrying answer and unique-leader invariants through both phases.
theorem drain_all_floor_two_to_fresh_uniform_unique
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {m : Answer}
    (hm : m ≠ .phi)
    (hDmax : 1 < Dmax)
    (hn2 : 2 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAll : ∀ w : Fin n,
      (C w).1.role = .Resetting ∧ 2 ≤ (C w).1.resetcount)
    (hAllM : ∀ w : Fin n, (C w).1.answer = m)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n, FreshResettingAt Dmax (runPairs P C L) w) ∧
      (∀ w : Fin n, (runPairs P C L w).1.answer = m) ∧
      (∃! ℓ : Fin n, (runPairs P C L ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨pairs, leftover, hdis, hend_sub, hleft, hcover⟩ :=
    exists_pair_list_with_optional_leftover (A := (Finset.univ : Finset (Fin n)))
  have hAllReset_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting := by
    intro w _hw
    exact (hAll w).1
  have hAllPos_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount := by
    intro w _hw
    have hw_floor := (hAll w).2
    omega
  obtain ⟨Lpairs, hfresh_pairs, hunchanged_pairs, hAllM_pairs, hUnique_pairs⟩ :=
    drain_pair_list_to_fresh_on_endpoints_uniform_unique
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m := m) hm hDmax pairs C hdis hAllReset_pairs hAllPos_pairs hAllM hUnique
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lpairs
  cases leftover with
  | none =>
      refine ⟨Lpairs, ?_, ?_, ?_⟩
      · intro w
        have hwEnd : w ∈ pairEndpoints pairs := by
          rcases hcover w (Finset.mem_univ w) with hwEnd | hnone
          · exact hwEnd
          · cases hnone
        exact hfresh_pairs w hwEnd
      · simpa [C₁, P] using hAllM_pairs
      · simpa [C₁, P] using hUnique_pairs
  | some z =>
      have hz_info := hleft z rfl
      obtain ⟨y, hyz⟩ := exists_fin_ne_of_two_le hn2 z
      have hyEnd : y ∈ pairEndpoints pairs := by
        rcases hcover y (Finset.mem_univ y) with hyEnd | hyLeft
        · exact hyEnd
        · injection hyLeft with hzy
          exact False.elim (hyz hzy.symm)
      have hz_unchanged : C₁ z = C z := by
        dsimp [C₁]
        exact hunchanged_pairs z hz_info.2
      have hz_res : (C₁ z).1.role = .Resetting := by
        rw [hz_unchanged]
        exact (hAll z).1
      have hz_rc : 1 < (C₁ z).1.resetcount := by
        rw [hz_unchanged]
        have hz_floor := (hAll z).2
        omega
      have hy_fresh : FreshResettingAt Dmax C₁ y := by
        dsimp [C₁]
        exact hfresh_pairs y hyEnd
      have hzy : z ≠ y := by
        intro h
        exact hyz h.symm
      obtain ⟨Llast, hz_fresh, hy_fresh_last, hlast, hAllM_last, hUnique_last⟩ :=
        drain_positive_with_fresh_partner_uniform_unique
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (m := m) hm hDmax C₁ hzy hz_res hz_rc hy_fresh
          (by simpa [C₁, P] using hAllM_pairs)
          (by simpa [C₁, P] using hUnique_pairs)
      refine ⟨Lpairs ++ Llast, ?_, ?_, ?_⟩
      · intro w
        rw [runPairs_append]
        change FreshResettingAt Dmax (runPairs P C₁ Llast) w
        by_cases hwz : w = z
        · subst w
          exact hz_fresh
        · by_cases hwy : w = y
          · subst w
            exact hy_fresh_last
          · have hkeep : runPairs P C₁ Llast w = C₁ w :=
              hlast w hwz hwy
            have hwEnd : w ∈ pairEndpoints pairs := by
              rcases hcover w (Finset.mem_univ w) with hwEnd | hwLeft
              · exact hwEnd
              · injection hwLeft with hzw
                exact False.elim (hwz hzw.symm)
            unfold FreshResettingAt
            rw [hkeep]
            simpa [C₁, P, FreshResettingAt] using hfresh_pairs w hwEnd
      · rw [runPairs_append]
        change ∀ w : Fin n, (runPairs P C₁ Llast w).1.answer = m
        exact hAllM_last
      · rw [runPairs_append]
        change ∃! ℓ : Fin n, (runPairs P C₁ Llast ℓ).1.leader = .L
        exact hUnique_last

set_option maxHeartbeats 24000000 in
theorem drain_all_floor_two_to_fresh_unique
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hn2 : 2 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAll : ∀ w : Fin n,
      (C w).1.role = .Resetting ∧ 2 ≤ (C w).1.resetcount)
    (hUnique : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n, FreshResettingAt Dmax (runPairs P C L) w) ∧
      (∃! ℓ : Fin n, (runPairs P C L ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨pairs, leftover, hdis, hend_sub, hleft, hcover⟩ :=
    exists_pair_list_with_optional_leftover (A := (Finset.univ : Finset (Fin n)))
  have hAllReset_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → (C w).1.role = .Resetting := by
    intro w _hw
    exact (hAll w).1
  have hAllPos_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C w).1.resetcount := by
    intro w _hw
    have hw_floor := (hAll w).2
    omega
  obtain ⟨Lpairs, hfresh_pairs, hunchanged_pairs, hUnique_pairs⟩ :=
    drain_pair_list_to_fresh_on_endpoints_unique
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax pairs C hdis hAllReset_pairs hAllPos_pairs hUnique
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lpairs
  cases leftover with
  | none =>
      refine ⟨Lpairs, ?_, ?_⟩
      · intro w
        have hwEnd : w ∈ pairEndpoints pairs := by
          rcases hcover w (Finset.mem_univ w) with hwEnd | hnone
          · exact hwEnd
          · cases hnone
        exact hfresh_pairs w hwEnd
      · simpa [C₁, P] using hUnique_pairs
  | some z =>
      have hz_info := hleft z rfl
      obtain ⟨y, hyz⟩ := exists_fin_ne_of_two_le hn2 z
      have hyEnd : y ∈ pairEndpoints pairs := by
        rcases hcover y (Finset.mem_univ y) with hyEnd | hyLeft
        · exact hyEnd
        · injection hyLeft with hzy
          exact False.elim (hyz hzy.symm)
      have hz_unchanged : C₁ z = C z := by
        dsimp [C₁]
        exact hunchanged_pairs z hz_info.2
      have hz_res : (C₁ z).1.role = .Resetting := by
        rw [hz_unchanged]
        exact (hAll z).1
      have hz_rc : 1 < (C₁ z).1.resetcount := by
        rw [hz_unchanged]
        have hz_floor := (hAll z).2
        omega
      have hy_fresh : FreshResettingAt Dmax C₁ y := by
        dsimp [C₁]
        exact hfresh_pairs y hyEnd
      have hzy : z ≠ y := by
        intro h
        exact hyz h.symm
      obtain ⟨Llast, hz_fresh, hy_fresh_last, hlast, hUnique_last⟩ :=
        drain_positive_with_fresh_partner_unique
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax C₁ hzy hz_res hz_rc hy_fresh
          (by simpa [C₁, P] using hUnique_pairs)
      refine ⟨Lpairs ++ Llast, ?_, ?_⟩
      · intro w
        rw [runPairs_append]
        change FreshResettingAt Dmax (runPairs P C₁ Llast) w
        by_cases hwz : w = z
        · subst w
          exact hz_fresh
        · by_cases hwy : w = y
          · subst w
            exact hy_fresh_last
          · have hkeep : runPairs P C₁ Llast w = C₁ w :=
              hlast w hwz hwy
            have hwEnd : w ∈ pairEndpoints pairs := by
              rcases hcover w (Finset.mem_univ w) with hwEnd | hwLeft
              · exact hwEnd
              · injection hwLeft with hzw
                exact False.elim (hwz hzw.symm)
            unfold FreshResettingAt
            rw [hkeep]
            simpa [C₁, P, FreshResettingAt] using hfresh_pairs w hwEnd
      · rw [runPairs_append]
        change ∃! ℓ : Fin n, (runPairs P C₁ Llast ℓ).1.leader = .L
        exact hUnique_last

theorem majorityAnswer_runPairs_eq_trank
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n) (L : List (Fin n × Fin n)) :
    majorityAnswer (runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L) = majorityAnswer C := by
  induction L generalizing C with
  | nil => simp
  | cons ij L ih =>
    rw [runPairs_cons, ih]
    exact majorityAnswer_step_eq C ij.1 ij.2

set_option maxHeartbeats 24000000 in
theorem all_fresh_unique_from_log_seed_no_answer
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hn2 : 2 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : 2 * Nat.clog 2 n + 2 ≤ (C r).1.resetcount)
    (hr_L : (C r).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := runPairs P C L
      (∀ w : Fin n, FreshResettingAt Dmax C' w) ∧
      (∃! ℓ : Fin n, (C' ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let g : ℕ := Nat.clog 2 n
  have hd_growth : 0 < g + 2 := by omega
  have hr_growth : Nat.clog 2 n + (g + 2) ≤ (C r).1.resetcount := by
    dsimp [g]
    omega
  obtain ⟨Lgrow, hAllFloorGrow, hLeaderGrow⟩ :=
    balanced_tree_growth_floor_leader_no_answer
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (d := g + 2) (hn := hn)
      hDmax hd_growth C r hr_role hr_growth hr_L
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lgrow
  have hAllFloorTourn :
      ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
        2 + g ≤ (C₁ w).1.resetcount := by
    intro w
    have hw := hAllFloorGrow w
    simpa [C₁, hP, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hw
  have hLeaderPos₁ : 0 < (leaderSet C₁).card := by
    apply Finset.card_pos.mpr
    refine ⟨r, ?_⟩
    rw [mem_leaderSet]
    simpa [C₁, hP] using hLeaderGrow
  have hLeaderBound₁ : (leaderSet C₁).card ≤ 2 ^ g := by
    have hcard_n : (leaderSet C₁).card ≤ n := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_le_univ (leaderSet C₁))
    have hn_pow : n ≤ 2 ^ g := by
      dsimp [g]
      exact Nat.le_pow_clog (by omega : 1 < 2) n
    exact Nat.le_trans hcard_n hn_pow
  obtain ⟨Ltourn, hFloorTourn, hLeaderLe, hLeaderPos⟩ :=
    leader_tournament_iter_no_answer
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (d := 2) (hn := hn)
      hDmax (by omega : 0 < 2) g C₁ hAllFloorTourn hLeaderBound₁ hLeaderPos₁
  let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ Ltourn
  have hFloor₂ : ∀ w : Fin n, (C₂ w).1.role = .Resetting ∧
      2 ≤ (C₂ w).1.resetcount := by
    simpa [C₂, P] using hFloorTourn
  have hUnique₂ : ∃! ℓ : Fin n, (C₂ ℓ).1.leader = .L :=
    uniqueLeader_of_leaderSet_card_pos_le_one
      (C := C₂)
      (by simpa [C₂, P] using hLeaderPos)
      (by simpa [C₂, P] using hLeaderLe)
  obtain ⟨Ldrain, hFreshDrain, hUniqueDrain⟩ :=
    drain_all_floor_two_to_fresh_unique
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax hn2 C₂ hFloor₂ hUnique₂
  let C₃ : Config (AgentState n) Opinion n := runPairs P C₂ Ldrain
  refine ⟨Lgrow ++ Ltourn ++ Ldrain, ?_, ?_⟩
  · intro w
    rw [List.append_assoc, runPairs_append, runPairs_append]
    change FreshResettingAt Dmax C₃ w
    exact hFreshDrain w
  · rw [List.append_assoc, runPairs_append, runPairs_append]
    change ∃! ℓ : Fin n, (C₃ ℓ).1.leader = .L
    exact hUniqueDrain

set_option maxHeartbeats 24000000 in
-- Growth uses `clog2 n`, the fueled leader tournament uses another
-- `clog2 n`, and the final exact drain needs floor `2`.
theorem all_fresh_uniform_unique_from_log_seed
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hn2 : 2 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (r : Fin n)
    (hr_role : (C r).1.role = .Resetting)
    (hr_log : 2 * Nat.clog 2 n + 2 ≤ (C r).1.resetcount)
    (hr_L : (C r).1.leader = .L)
    (hAllAns : ∀ w : Fin n, (C w).1.role = .Resetting →
      (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      let P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := runPairs P C L
      (∀ w : Fin n, FreshResettingAt Dmax C' w) ∧
      (∀ w : Fin n, (C' w).1.answer = majorityAnswer C') ∧
      (∃! ℓ : Fin n, (C' ℓ).1.leader = .L) ∧
      majorityAnswer C' = majorityAnswer C := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  let g : ℕ := Nat.clog 2 n
  have hd_growth : 0 < g + 2 := by omega
  have hr_growth : Nat.clog 2 n + (g + 2) ≤ (C r).1.resetcount := by
    dsimp [g]
    omega
  obtain ⟨Lgrow, hAllFloorGrow, hAnsGrow, hLeaderGrow⟩ :=
    balanced_tree_growth_floor_answer_leader
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (d := g + 2) (hn := hn)
      hDmax hd_growth C r hr_role hr_growth hr_L hAllAns
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lgrow
  have hAllFloorTourn :
      ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
        2 + g ≤ (C₁ w).1.resetcount := by
    intro w
    have hw := hAllFloorGrow w
    simpa [C₁, hP, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hw
  have hAns₁ :
      ∀ w : Fin n, (C₁ w).1.role = .Resetting →
        (C₁ w).1.answer = majorityAnswer C₁ := by
    simpa [C₁, hP] using hAnsGrow
  have hLeaderPos₁ : 0 < (leaderSet C₁).card := by
    apply Finset.card_pos.mpr
    refine ⟨r, ?_⟩
    rw [mem_leaderSet]
    simpa [C₁, hP] using hLeaderGrow
  have hLeaderBound₁ : (leaderSet C₁).card ≤ 2 ^ g := by
    have hcard_n : (leaderSet C₁).card ≤ n := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_le_univ (leaderSet C₁))
    have hn_pow : n ≤ 2 ^ g := by
      dsimp [g]
      exact Nat.le_pow_clog (by omega : 1 < 2) n
    exact Nat.le_trans hcard_n hn_pow
  obtain ⟨Ltourn, hFloorTourn, hAnsTourn, hLeaderLe, hLeaderPos⟩ :=
    leader_tournament_iter
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (d := 2) (hn := hn)
      hDmax (by omega : 0 < 2) g C₁ hAllFloorTourn hAns₁ hLeaderBound₁ hLeaderPos₁
  let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ Ltourn
  have hFloor₂ : ∀ w : Fin n, (C₂ w).1.role = .Resetting ∧
      2 ≤ (C₂ w).1.resetcount := by
    simpa [C₂, P] using hFloorTourn
  have hAns₂ :
      ∀ w : Fin n, (C₂ w).1.role = .Resetting →
        (C₂ w).1.answer = majorityAnswer C₂ := by
    simpa [C₂, P] using hAnsTourn
  have hUnique₂ : ∃! ℓ : Fin n, (C₂ ℓ).1.leader = .L :=
    uniqueLeader_of_leaderSet_card_pos_le_one
      (C := C₂)
      (by simpa [C₂, P] using hLeaderPos)
      (by simpa [C₂, P] using hLeaderLe)
  have hAllM₂ : ∀ w : Fin n, (C₂ w).1.answer = majorityAnswer C₂ := by
    intro w
    exact hAns₂ w (hFloor₂ w).1
  have hm_ne_phi : majorityAnswer C₂ ≠ .phi := majorityAnswer_ne_phi C₂
  obtain ⟨Ldrain, hFreshDrain, hAllMDrain, hUniqueDrain⟩ :=
    drain_all_floor_two_to_fresh_uniform_unique
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (m := majorityAnswer C₂) hm_ne_phi hDmax hn2 C₂ hFloor₂ hAllM₂ hUnique₂
  let C₃ : Config (AgentState n) Opinion n := runPairs P C₂ Ldrain
  have hMaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, hP] using
      majorityAnswer_runPairs_eq_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) C Lgrow
  have hMaj₂ : majorityAnswer C₂ = majorityAnswer C₁ := by
    simpa [C₂, P] using
      majorityAnswer_runPairs_eq_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) C₁ Ltourn
  have hMaj₃ : majorityAnswer C₃ = majorityAnswer C₂ := by
    simpa [C₃, P] using
      majorityAnswer_runPairs_eq_trank
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) C₂ Ldrain
  refine ⟨Lgrow ++ Ltourn ++ Ldrain, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [List.append_assoc, runPairs_append, runPairs_append]
    change FreshResettingAt Dmax C₃ w
    exact hFreshDrain w
  · intro w
    rw [List.append_assoc, runPairs_append, runPairs_append]
    change (C₃ w).1.answer = majorityAnswer C₃
    rw [hMaj₃]
    exact hAllMDrain w
  · rw [List.append_assoc, runPairs_append, runPairs_append]
    change ∃! ℓ : Fin n, (C₃ ℓ).1.leader = .L
    exact hUniqueDrain
  · rw [List.append_assoc, runPairs_append, runPairs_append]
    change majorityAnswer C₃ = majorityAnswer C
    rw [hMaj₃, hMaj₂, hMaj₁]

/-- Log-fuel reset drain from an explicit balanced-growth certificate.

The theorem discharges the deterministic Phase B exactly: once a Phase A
schedule grown from a log-fueled seed has made every agent Resetting with
positive resetcount, any disjoint covering pair list can be drained without
selecting dormant agents again, ending with every agent Resetting, resetcount
zero, and delaytimer exactly `Dmax`.

The remaining Phase A combinatorics are isolated in `hBalancedTreeGrowth`;
this is the explicit precondition that a later balanced-doubling construction
must remove. -/
theorem all_fresh_from_log_seed
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax R : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hfuel : Nat.clog 2 n + 1 ≤ R)
    (C : Config (AgentState n) Opinion n)
    (hseed : ∃ r : Fin n, (C r).1.role = .Resetting ∧ R ≤ (C r).1.resetcount)
    (hBalancedTreeGrowth :
      ∀ r : Fin n,
        (C r).1.role = .Resetting →
        Nat.clog 2 n + 1 ≤ (C r).1.resetcount →
        ∃ Lgrow : List (Fin n × Fin n),
          let C₁ := runPairs (protocolPEM n τ Rmax
            (rankDeltaOSSR Rmax Emax Dmax hn)) C Lgrow
          ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧ 0 < (C₁ w).1.resetcount)
    (pairs : List (Fin n × Fin n))
    (hdis : PairListDisjoint pairs)
    (hcover : ∀ w : Fin n, w ∈ pairEndpoints pairs) :
    ∃ L : List (Fin n × Fin n),
      let C₂ := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, FreshResettingAt Dmax C₂ w := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨r, hr_role, hr_fuel⟩ := hseed
  have hr_log : Nat.clog 2 n + 1 ≤ (C r).1.resetcount :=
    Nat.le_trans hfuel hr_fuel
  obtain ⟨Lgrow, hAllPositive⟩ := hBalancedTreeGrowth r hr_role hr_log
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lgrow
  have hAllReset_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → (C₁ w).1.role = .Resetting := by
    intro w _
    exact (hAllPositive w).1
  have hAllPos_pairs :
      ∀ w : Fin n, w ∈ pairEndpoints pairs → 0 < (C₁ w).1.resetcount := by
    intro w _
    exact (hAllPositive w).2
  obtain ⟨Ldrain, hfresh, _hunchanged⟩ :=
    drain_pair_list_to_fresh_on_endpoints
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax pairs C₁ hdis hAllReset_pairs hAllPos_pairs
  refine ⟨Lgrow ++ Ldrain, ?_⟩
  change ∀ w : Fin n, FreshResettingAt Dmax (runPairs P C (Lgrow ++ Ldrain)) w
  intro w
  rw [runPairs_append]
  exact hfresh w (hcover w)

theorem all_fresh_from_log_seed_via_balanced_growth
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax R : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hfuel : Nat.clog 2 n + 1 ≤ R)
    (C : Config (AgentState n) Opinion n)
    (hseed : ∃ r : Fin n, (C r).1.role = .Resetting ∧ R ≤ (C r).1.resetcount)
    (pairs : List (Fin n × Fin n))
    (hdis : PairListDisjoint pairs)
    (hcover : ∀ w : Fin n, w ∈ pairEndpoints pairs) :
    ∃ L : List (Fin n × Fin n),
      let C₂ := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, FreshResettingAt Dmax C₂ w := by
  exact all_fresh_from_log_seed
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (R := R) (hn := hn)
    hDmax hfuel C hseed
    (fun r hr_role hr_log =>
      balanced_tree_growth
        (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C r hr_role hr_log)
    pairs hdis hcover

theorem all_fresh_from_log_seed_unconditional
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax R : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (hn2 : 2 ≤ n)
    (hfuel : Nat.clog 2 n + 2 ≤ R)
    (C : Config (AgentState n) Opinion n)
    (hseed : ∃ r : Fin n, (C r).1.role = .Resetting ∧ R ≤ (C r).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      let C₂ := runPairs (protocolPEM n τ Rmax
        (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, FreshResettingAt Dmax C₂ w := by
  classical
  set P := protocolPEM n τ Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨r, hr_role, hr_fuel⟩ := hseed
  have hr_floor : Nat.clog 2 n + 2 ≤ (C r).1.resetcount :=
    Nat.le_trans hfuel hr_fuel
  obtain ⟨Lgrow, hAllFloor⟩ :=
    balanced_tree_growth_floor
      (τ := τ) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax (by omega : 0 < 2) C r hr_role hr_floor
  let C₁ : Config (AgentState n) Opinion n := runPairs P C Lgrow
  have hAll₂ :
      ∀ w : Fin n, (C₁ w).1.role = .Resetting ∧
        2 ≤ (C₁ w).1.resetcount := by
    intro w
    exact hAllFloor w
  obtain ⟨Ldrain, hfresh⟩ :=
    drain_all_floor_two_to_fresh
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax hn2 C₁ hAll₂
  refine ⟨Lgrow ++ Ldrain, ?_⟩
  change ∀ w : Fin n, FreshResettingAt Dmax (runPairs P C (Lgrow ++ Ldrain)) w
  intro w
  rw [runPairs_append]
  change FreshResettingAt Dmax (runPairs P C₁ Ldrain) w
  exact hfresh w

end SSEM
