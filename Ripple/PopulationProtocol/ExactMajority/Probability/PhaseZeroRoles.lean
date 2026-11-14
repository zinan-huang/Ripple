/-
Phase-0 role continuation on the physical-label pair log.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroEntry
import Ripple.PopulationProtocol.ExactMajority.Probability.PairLogAuxiliary
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Martingale.OptionalStopping

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseZeroRoles

open TimeTheorem PairLog PairLogAuxiliary PhaseZeroEntry RoleSplitConcentration
open PhaseThreeModel.OccurrenceScheduler

attribute [local instance] Classical.propDecidable

variable {L K n : ℕ}

/-! ## The full-state auxiliary rule and its generic coupling -/

/-- Continue the Phase-0 dispatcher, including its genuine counter update. -/
def phaseZeroRoleRule (L K : ℕ) : PairRule L K := fun s t =>
  let out := Phase0Transition L K s t
  (finishPhase10Entry L K s out.1, finishPhase10Entry L K t out.2)

@[simp] theorem phaseZeroRoleRule_left_role (s t : AgentState L K) :
    (phaseZeroRoleRule L K s t).1.role = (Phase0Transition L K s t).1.role := by
  simp [phaseZeroRoleRule]

@[simp] theorem phaseZeroRoleRule_right_role (s t : AgentState L K) :
    (phaseZeroRoleRule L K s t).2.role = (Phase0Transition L K s t).2.role := by
  simp [phaseZeroRoleRule]

@[simp] theorem phaseZeroRoleRule_left_assigned (s t : AgentState L K) :
    (phaseZeroRoleRule L K s t).1.assigned =
      (Phase0Transition L K s t).1.assigned := by
  simp [phaseZeroRoleRule]

@[simp] theorem phaseZeroRoleRule_right_assigned (s t : AgentState L K) :
    (phaseZeroRoleRule L K s t).2.assigned =
      (Phase0Transition L K s t).2.assigned := by
  simp [phaseZeroRoleRule]

theorem phaseZeroRoleRule_eq_transition (s t : AgentState L K)
    (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    phaseZeroRoleRule L K s t = (NonuniformMajority L K).δ s t := by
  change _ = Transition L K s t
  unfold Transition
  rw [phaseEpidemicUpdate_eq_self_of_both_phase0 s t hs ht]
  have hsphase : s.phase = (⟨0, by decide⟩ : Fin 11) := Fin.ext hs
  dsimp only
  rw [hsphase] <;> rfl

def phaseZeroRegion (f : Fin n → AgentState L K) : Prop :=
  ∀ i, (f i).phase.val = 0

theorem phaseZeroRoleRule_agree (f : Fin n → AgentState L K)
    (hf : phaseZeroRegion f) (i j : Fin n) (_hij : i ≠ j) :
    phaseZeroRoleRule L K (f i) (f j) =
      (NonuniformMajority L K).δ (f i) (f j) :=
  phaseZeroRoleRule_eq_transition (f i) (f j) (hf i) (hf j)

noncomputable def roleLabels (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    Fin init.card → AgentState L K :=
  auxLabels init (phaseZeroRoleRule L K) ω t

noncomputable def roleCfg (init : Cfg L K) (ω : Ω L K) (t : ℕ) : Cfg L K :=
  labelCfg (roleLabels init ω t)

@[simp] theorem roleLabels_zero (init : Cfg L K) (ω : Ω L K) :
    roleLabels init ω 0 = initialLabels init := rfl

theorem roleLabels_succ (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    roleLabels init ω (t + 1) =
      auxStep (phaseZeroRoleRule L K) (roleLabels init ω t)
        (drawLabels init ω (t + 1)) :=
  auxLabels_succ init (phaseZeroRoleRule L K) ω t

@[simp] theorem roleCfg_zero (init : Cfg L K) (ω : Ω L K) :
    roleCfg init ω 0 = init := initialLabels_config init

@[simp] theorem roleCfg_card (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    (roleCfg init ω t).card = init.card := labelCfg_card _

theorem role_label_mem (f : Fin n → AgentState L K) (i : Fin n) :
    f i ∈ labelCfg f := by
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

theorem phaseZeroRegion_of_allPhaseZero (f : Fin n → AgentState L K)
    (hf : Phase0Window.allPhase0 (labelCfg f)) :
    phaseZeroRegion f := by
  intro i
  exact congrArg Fin.val (hf (f i) (role_label_mem f i))

theorem roleLabels_eq_labelsAt (init : Cfg L K) (ω : Ω L K) (T : ℕ)
    (hT : ∀ t < T, phaseZeroRegion (labelsAt init ω t)) :
    ∀ t ≤ T, roleLabels init ω t = labelsAt init ω t :=
  auxLabels_eq_labelsAt_of_agree init (phaseZeroRoleRule L K)
    phaseZeroRegion phaseZeroRoleRule_agree ω T hT

theorem roleLabels_eq_labelsAt_before_exit (init : Cfg L K) (ω : Ω L K)
    (hexit : ∃ t, ¬ phaseZeroRegion (labelsAt init ω t)) :
    ∀ t ≤ Nat.find hexit, roleLabels init ω t = labelsAt init ω t :=
  auxLabels_eq_labelsAt_before_exit init (phaseZeroRoleRule L K)
    phaseZeroRegion phaseZeroRoleRule_agree ω hexit

theorem roleLabels_eq_labelsAt_until_seed (init : Cfg L K)
    (ω : Ω L K) (S : ℕ) (hseed : firstPhaseSeed init 1 S ω) :
    ∀ t ≤ S, roleLabels init ω t = labelsAt init ω t := by
  apply roleLabels_eq_labelsAt init ω S
  intro t ht
  apply phaseZeroRegion_of_allPhaseZero
  rw [show labelCfg (labelsAt init ω t) = trace init ω t from
    labelsAt_config init ω t]
  exact phaseZero_allPhaseZero_before_seed init ω S hseed t ht

theorem roleCfg_eq_trace_until_seed (init : Cfg L K)
    (ω : Ω L K) (S : ℕ) (hseed : firstPhaseSeed init 1 S ω)
    (t : ℕ) (ht : t ≤ S) :
    roleCfg init ω t = trace init ω t := by
  unfold roleCfg
  rw [roleLabels_eq_labelsAt_until_seed init ω S hseed t ht]
  exact labelsAt_config init ω t

theorem role_event_eq_actual_event (init : Cfg L K) (T : ℕ)
    (P : ((t : Finset.Iic T) → Fin init.card → AgentState L K) → Prop) :
    {ω | (∀ t < T, phaseZeroRegion (labelsAt init ω t)) ∧
        P (fun t => roleLabels init ω t.val)} =
      {ω | (∀ t < T, phaseZeroRegion (labelsAt init ω t)) ∧
        P (fun t => labelsAt init ω t.val)} :=
  aux_event_eq_actual_event init (phaseZeroRoleRule L K)
    phaseZeroRegion phaseZeroRoleRule_agree T P

theorem measurable_roleLabels (init : Cfg L K) (t : ℕ) :
    Measurable[pairLogFiltration L K t] (fun ω => roleLabels init ω t) :=
  measurable_auxLabels init (phaseZeroRoleRule L K) t

theorem measurable_role_potential (init : Cfg L K)
    (φ : (Fin init.card → AgentState L K) → ℝ) (t : ℕ) :
    Measurable[pairLogFiltration L K t] (fun ω => φ (roleLabels init ω t)) :=
  measurable_aux_potential init (phaseZeroRoleRule L K) φ t

/-! ## Pathwise count updates on the same physical labels -/

theorem role_pair_split (f : Fin n → AgentState L K)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ rest : Cfg L K,
      labelCfg f = rest + {f i, f j} ∧
      labelCfg (ruleUpdate (phaseZeroRoleRule L K) f i j) =
        rest + {(phaseZeroRoleRule L K (f i) (f j)).1,
                (phaseZeroRoleRule L K (f i) (f j)).2} := by
  let rest : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hj : j ∉ rest := by simp [rest]
  have hi : i ∉ Finset.cons j rest hj := by simp [rest, hij]
  have hfin :
      Finset.cons i (Finset.cons j rest hj) hi = Finset.univ := by
    ext k
    by_cases hki : k = i
    · subst k
      simp
    · by_cases hkj : k = j
      · subst k
        simp
      · simp [rest, hki, hkj]
  have hsplit : (Finset.univ : Finset (Fin n)).val =
      i ::ₘ j ::ₘ rest.val := (congrArg Finset.val hfin).symm
  have hrest :
      rest.val.map (ruleUpdate (phaseZeroRoleRule L K) f i j) = rest.val.map f := by
    apply Multiset.map_congr rfl
    intro k hk
    have hk' : k ∈ rest := hk
    have hki : k ≠ i :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk').2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk').1
    simp [ruleUpdate, hki, hkj]
  refine ⟨rest.val.map f, ?_, ?_⟩
  · unfold labelCfg
    rw [hsplit]
    simp [add_comm, add_left_comm, add_assoc]
    exact (Multiset.singleton_add (f j) (rest.val.map f)).symm.trans
      (add_comm _ _)
  · unfold labelCfg
    rw [hsplit]
    simp only [Multiset.map_cons, hrest]
    simp [ruleUpdate, hij, Ne.symm hij, add_comm, add_left_comm, add_assoc]
    exact (Multiset.singleton_add
      (phaseZeroRoleRule L K (f i) (f j)).2
      (rest.val.map f)).symm.trans (add_comm _ _)

theorem role_count_update (P : AgentState L K → Prop)
    (f : Fin n → AgentState L K) (i j : Fin n) (hij : i ≠ j) :
    Multiset.countP P (labelCfg (ruleUpdate (phaseZeroRoleRule L K) f i j)) +
        Multiset.countP P ({f i, f j} : Cfg L K) =
      Multiset.countP P (labelCfg f) +
        Multiset.countP P
          ({(phaseZeroRoleRule L K (f i) (f j)).1,
            (phaseZeroRoleRule L K (f i) (f j)).2} : Cfg L K) := by
  obtain ⟨rest, hbefore, hafter⟩ := role_pair_split f i j hij
  rw [hbefore, hafter]
  simp only [Multiset.countP_add]
  omega

theorem role_noAssigned_update (f : Fin n → AgentState L K)
    (hf : ∀ k, NotAssignedMcr (f k)) (i j : Fin n) :
    ∀ k, NotAssignedMcr (ruleUpdate (phaseZeroRoleRule L K) f i j k) := by
  have hout :
      NotAssignedMcr (phaseZeroRoleRule L K (f i) (f j)).1 ∧
      NotAssignedMcr (phaseZeroRoleRule L K (f i) (f j)).2 := by
    simpa only [NotAssignedMcr, phaseZeroRoleRule_left_role,
      phaseZeroRoleRule_right_role, phaseZeroRoleRule_left_assigned,
      phaseZeroRoleRule_right_assigned] using
      (Phase0Transition_outputs_notAssignedMcr (f i) (f j) (hf i) (hf j))
  intro k
  by_cases hkj : k = j
  · subst k
    simpa [ruleUpdate] using hout.2
  · by_cases hki : k = i
    · subst k
      simpa [ruleUpdate, hkj] using hout.1
    · simpa [ruleUpdate, hki, hkj] using hf k

theorem role_noAssigned_labels (init : Cfg L K)
    (hinit : Phase0InitialFresh n init) (ω : Ω L K) (t : ℕ) :
    ∀ i, NotAssignedMcr (roleLabels init ω t i) := by
  induction t with
  | zero =>
      intro i
      have hi : initialLabels init i ∈ init := by
        simpa only [initialLabels_config] using role_label_mem (initialLabels init) i
      exact noAssignedMcrConfig_of_phase0InitialFresh hinit _ hi
  | succ t ih =>
      intro k
      rw [roleLabels_succ]
      cases hd : drawLabels init ω (t + 1) with
      | none => simpa only [auxStep] using ih k
      | some ij =>
          rcases ij with ⟨i, j⟩
          exact role_noAssigned_update _ ih i j k

theorem role_noAssigned (init : Cfg L K)
    (hinit : Phase0InitialFresh n init) (ω : Ω L K) (t : ℕ) :
    NoAssignedMcrConfig (roleCfg init ω t) := by
  intro a ha
  change a ∈ Finset.univ.val.map (roleLabels init ω t) at ha
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ha
  exact role_noAssigned_labels init hinit ω t i

theorem role_freeTarget_initial {init : Cfg L K}
    (hinit : Phase0Initial n init) :
    freeTargetCount init = 0 := by
  unfold freeTargetCount
  rw [Multiset.countP_eq_zero]
  intro a ha hfree
  exact hfree.1 ((hinit.2 a ha).2)

theorem role_freeTarget_pair_balance (s t : AgentState L K)
    (hs : NotAssignedMcr s) (ht : NotAssignedMcr t) :
    freeTargetCount
        ({(phaseZeroRoleRule L K s t).1,
          (phaseZeroRoleRule L K s t).2} : Cfg L K) =
      freeTargetCount ({s, t} : Cfg L K) + phaseZeroFreshGain s t := by
  have hbalance := phaseZero_freeTarget_pair_balance s t hs ht
  change Multiset.countP freeTargetPred
      ((Phase0Transition L K s t).1 ::ₘ
        (Phase0Transition L K s t).2 ::ₘ 0) =
    Multiset.countP freeTargetPred (s ::ₘ t ::ₘ 0) +
      phaseZeroFreshGain s t at hbalance
  change Multiset.countP freeTargetPred
      ((phaseZeroRoleRule L K s t).1 ::ₘ
        (phaseZeroRoleRule L K s t).2 ::ₘ 0) =
    Multiset.countP freeTargetPred (s ::ₘ t ::ₘ 0) +
      phaseZeroFreshGain s t
  simpa only [Multiset.countP_cons, Multiset.countP_zero,
    freeTargetPred, phaseZeroRoleRule_left_role, phaseZeroRoleRule_right_role,
    phaseZeroRoleRule_left_assigned, phaseZeroRoleRule_right_assigned] using
    hbalance

theorem role_freeTarget_update (f : Fin n → AgentState L K)
    (hf : ∀ k, NotAssignedMcr (f k)) (i j : Fin n) (hij : i ≠ j) :
    freeTargetCount (labelCfg (ruleUpdate (phaseZeroRoleRule L K) f i j)) =
      freeTargetCount (labelCfg f) + phaseZeroFreshGain (f i) (f j) := by
  have hcount := role_count_update (freeTargetPred (L := L) (K := K)) f i j hij
  change freeTargetCount (labelCfg (ruleUpdate (phaseZeroRoleRule L K) f i j)) +
      freeTargetCount ({f i, f j} : Cfg L K) =
    freeTargetCount (labelCfg f) +
      freeTargetCount
        ({(phaseZeroRoleRule L K (f i) (f j)).1,
          (phaseZeroRoleRule L K (f i) (f j)).2} : Cfg L K) at hcount
  rw [role_freeTarget_pair_balance (f i) (f j) (hf i) (hf j)] at hcount
  omega

theorem role_freeTarget_step (init : Cfg L K)
    (hinit : Phase0InitialFresh n init) (ω : Ω L K) (t : ℕ) :
    freeTargetCount (roleCfg init ω (t + 1)) =
      freeTargetCount (roleCfg init ω t) +
        match drawLabels init ω (t + 1) with
        | none => 0
        | some (i, j) =>
            phaseZeroFreshGain (roleLabels init ω t i) (roleLabels init ω t j) := by
  unfold roleCfg
  rw [roleLabels_succ]
  cases hd : drawLabels init ω (t + 1) with
  | none => simp only [auxStep, Nat.add_zero]
  | some ij =>
      rcases ij with ⟨i, j⟩
      exact role_freeTarget_update _ (role_noAssigned_labels init hinit ω t)
        i j (labelsAt_selected_transition init ω t i j hd).1

theorem role_freeTarget_mono (init : Cfg L K)
    (hinit : Phase0InitialFresh n init) (ω : Ω L K) :
    Monotone (fun t => freeTargetCount (roleCfg init ω t)) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [role_freeTarget_step init hinit ω t]
  exact Nat.le_add_right _ _

theorem role_freeTarget_even (init : Cfg L K)
    (hinit : Phase0InitialFresh n init) (ω : Ω L K) (t : ℕ) :
    Even (freeTargetCount (roleCfg init ω t)) := by
  induction t with
  | zero =>
      rw [roleCfg_zero, role_freeTarget_initial hinit.1]
      norm_num
  | succ t ih =>
      rw [role_freeTarget_step init hinit ω t]
      apply Even.add ih
      cases hd : drawLabels init ω (t + 1) with
      | none => norm_num
      | some ij =>
          rcases ij with ⟨i, j⟩
          change Even (phaseZeroFreshGain
            (roleLabels init ω t i) (roleLabels init ω t j))
          unfold phaseZeroFreshGain
          split_ifs <;> norm_num

theorem role_freeTarget_add_mcr_le_card (c : Cfg L K) :
    freeTargetCount c + roleMCRCount c ≤ c.card := by
  induction c using Multiset.induction with
  | empty => simp [freeTargetCount, roleMCRCount]
  | cons a c ih =>
      change freeTargetCount c + roleMCRCount c ≤ c.card at ih
      simp only [freeTargetCount, roleMCRCount, Multiset.countP_cons,
        Multiset.card_cons]
      change
        freeTargetCount c + (if freeTargetPred a then 1 else 0) +
          (roleMCRCount c + (if a.role = .mcr then 1 else 0)) ≤ c.card + 1
      by_cases hm : a.role = .mcr
      · have hf : ¬ freeTargetPred a := fun h => h.1 hm
        simp only [if_pos hm, if_neg hf]
        omega
      · simp only [if_neg hm]
        split_ifs <;> omega


/-! ## The diagonal and the full two-orientation fresh-target rectangle -/

variable {m : ℕ}

def roleBirthPair (s t : AgentState L K) : Prop :=
  s.role = .mcr ∧ t.role = .mcr

def roleOneSidedPair (s t : AgentState L K) : Prop :=
  (s.role = .mcr ∧ freeTargetPred t) ∨
    (freeTargetPred s ∧ t.role = .mcr)

noncomputable def roleMcrLabels (f : Fin m → AgentState L K) : ℕ :=
  roleMCRCount (labelCfg f)

noncomputable def roleFreeLabels (f : Fin m → AgentState L K) : ℕ :=
  freeTargetCount (labelCfg f)

theorem roleMcrLabels_eq_countP (f : Fin m → AgentState L K) :
    roleMcrLabels f =
      Multiset.countP (fun a : AgentState L K => a.role = .mcr) (labelCfg f) := by
  rfl

theorem roleMcrLabels_eq_mcrCount (f : Fin m → AgentState L K) :
    roleMcrLabels f = mcrCount (labelCfg f) := by
  rw [roleMcrLabels_eq_countP, Multiset.countP_eq_card_filter] <;> rfl

theorem role_filter_card (P : AgentState L K → Prop)
    (f : Fin m → AgentState L K) :
    (Finset.univ.filter (fun i : Fin m => P (f i))).card =
      Multiset.countP P (labelCfg f) := by
  rw [Multiset.countP_eq_card_filter]
  unfold labelCfg
  rw [Multiset.filter_map, Multiset.card_map] <;> rfl

theorem role_mcr_filter_card (f : Fin m → AgentState L K) :
    (Finset.univ.filter (fun i : Fin m => (f i).role = .mcr)).card =
      roleMcrLabels f := by
  unfold roleMcrLabels roleMCRCount labelCfg
  exact (Multiset.countP_map f (Finset.univ : Finset (Fin m)).val
    (fun a : AgentState L K => a.role = .mcr)).symm

theorem role_free_filter_card (f : Fin m → AgentState L K) :
    (Finset.univ.filter (fun i : Fin m => freeTargetPred (f i))).card =
      roleFreeLabels f :=
  role_filter_card freeTargetPred f

theorem roleMcrLabels_le (f : Fin m → AgentState L K) :
    roleMcrLabels f ≤ m := by
  rw [roleMcrLabels_eq_countP]
  exact (Multiset.countP_le_card _ _).trans (labelCfg_card f).le

theorem role_birth_goodPairs_card (f : Fin m → AgentState L K) :
    (goodPairs (fun g i j => roleBirthPair (g i) (g j)) f).card =
      roleMcrLabels f * (roleMcrLabels f - 1) := by
  let A : Finset (Fin m) :=
    Finset.univ.filter fun i => (f i).role = .mcr
  have hset :
      goodPairs (fun g i j => roleBirthPair (g i) (g j)) f = A.offDiag := by
    ext ij
    simp [goodPairs, roleBirthPair, A, Finset.mem_offDiag,
      and_assoc, and_left_comm, and_comm]
  have hA : A.card = roleMcrLabels f := role_mcr_filter_card f
  rw [hset, Finset.offDiag_card, hA, Nat.mul_sub_one]

theorem role_one_sided_goodPairs_card (f : Fin m → AgentState L K) :
    (goodPairs (fun g i j => roleOneSidedPair (g i) (g j)) f).card =
      2 * roleMcrLabels f * roleFreeLabels f := by
  let A : Finset (Fin m) :=
    Finset.univ.filter fun i => (f i).role = .mcr
  let B : Finset (Fin m) :=
    Finset.univ.filter fun i => freeTargetPred (f i)
  have hAB : ∀ i ∈ A, ∀ j ∈ B, i ≠ j := by
    intro i hi j hj hij
    have hi' : (f i).role = .mcr := (Finset.mem_filter.mp hi).2
    have hj' : (f j).role ≠ .mcr := (Finset.mem_filter.mp hj).2.1
    exact hj' (hij ▸ hi')
  have hdisj : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    apply Finset.disjoint_left.mpr
    intro ij hleft hright
    exact hAB ij.1 (Finset.mem_product.mp hleft).1
      ij.1 (Finset.mem_product.mp hright).1 rfl
  have hset :
      goodPairs (fun g i j => roleOneSidedPair (g i) (g j)) f =
        (A ×ˢ B) ∪ (B ×ˢ A) := by
    ext ij
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_product, A, B, roleOneSidedPair]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · intro hij
        exact hj.1 (hij ▸ hi)
      · intro hij
        exact hi.1 (hij.symm ▸ hj)
  have hA : A.card = roleMcrLabels f := role_mcr_filter_card f
  have hB : B.card = roleFreeLabels f := role_free_filter_card f
  rw [hset, Finset.card_union_of_disjoint hdisj,
    Finset.card_product, Finset.card_product, hA, hB]
  ring

theorem role_count_pair (P : AgentState L K → Prop) (s t : AgentState L K) :
    Multiset.countP P ({s, t} : Cfg L K) =
      (if P s then 1 else 0) + (if P t then 1 else 0) := by
  change Multiset.countP P (s ::ₘ t ::ₘ 0) = _
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  omega

-- The one-sided cases split the five roles and two assigned values.
-- Keep the exhaustive transition simplification's allowance local.
set_option maxHeartbeats 800000 in
theorem role_mcr_pair_accounting (s t : AgentState L K) :
    (if (phaseZeroRoleRule L K s t).1.role = .mcr then (1 : ℕ) else 0) +
      (if (phaseZeroRoleRule L K s t).2.role = .mcr then 1 else 0) +
      2 * (if roleBirthPair s t then 1 else 0) +
      (if roleOneSidedPair s t then 1 else 0) =
      (if s.role = .mcr then 1 else 0) +
        (if t.role = .mcr then 1 else 0) := by
  by_cases hs : s.role = .mcr
  · by_cases ht : t.role = .mcr
    · simp [roleBirthPair, roleOneSidedPair, freeTargetPred,
        phaseZeroRoleRule, Phase0Transition, hs, ht]
    · cases hrole : t.role <;> cases hassigned : t.assigned <;>
        simp_all [roleBirthPair, roleOneSidedPair, freeTargetPred,
          phaseZeroRoleRule, Phase0Transition]
  · by_cases ht : t.role = .mcr
    · cases hrole : s.role <;> cases hassigned : s.assigned <;>
        simp_all [roleBirthPair, roleOneSidedPair, freeTargetPred,
          phaseZeroRoleRule, Phase0Transition]
    · have hleft : (phaseZeroRoleRule L K s t).1.role ≠ .mcr := by
        simpa only [phaseZeroRoleRule, finishPhase10Entry_role] using
          Phase0Transition_first_no_mcr s t hs
      have hright : (phaseZeroRoleRule L K s t).2.role ≠ .mcr := by
        simpa only [phaseZeroRoleRule, finishPhase10Entry_role] using
          Phase0Transition_second_no_mcr s t ht
      rw [if_neg hleft, if_neg hright]
      simp [roleBirthPair, roleOneSidedPair, hs, ht]

theorem role_mcr_update (f : Fin m → AgentState L K)
    (i j : Fin m) (hij : i ≠ j) :
    roleMcrLabels (ruleUpdate (phaseZeroRoleRule L K) f i j) +
      2 * (if roleBirthPair (f i) (f j) then 1 else 0) +
      (if roleOneSidedPair (f i) (f j) then 1 else 0) =
      roleMcrLabels f := by
  obtain ⟨rest, hbefore, hafter⟩ := role_pair_split f i j hij
  unfold roleMcrLabels
  rw [hafter, hbefore, roleMCRCount_add, roleMCRCount_add,
    roleMCRCount_pair', roleMCRCount_pair']
  have hpair := role_mcr_pair_accounting (f i) (f j)
  omega


theorem roleOneSidedPair_iff (s t : AgentState L K) :
    roleOneSidedPair s t ↔
      (s.role = .mcr ∧ (freeMainPred t ∨ freeSidePred t)) ∨
        ((freeMainPred s ∨ freeSidePred s) ∧ t.role = .mcr) := by
  simp only [roleOneSidedPair, freeTargetPred_iff]

/-- When only one MCR remains, a genuine one-sided reaction removes it. -/
theorem role_last_mcr_removed (f : Fin m → AgentState L K)
    (i j : Fin m) (hij : i ≠ j) (hU : roleMcrLabels f = 1)
    (hone : roleOneSidedPair (f i) (f j)) :
    roleMcrLabels (ruleUpdate (phaseZeroRoleRule L K) f i j) = 0 := by
  have h := role_mcr_update f i j hij
  rw [if_pos hone, hU] at h
  omega


/-! ## Conditional expectations from the compiled pair-count law -/

noncomputable def role_aux_pair_indicator
    (init : Cfg L K) (F : PairRule L K)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (t : ℕ) (ω : Ω L K) : ℝ :=
  @ite ℝ (∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      A (auxLabels init F ω t) i j) (Classical.propDecidable _) 1 0

theorem role_aux_pair_indicator_stronglyMeasurable
    (init : Cfg L K) (F : PairRule L K)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)]
      (role_aux_pair_indicator init F A t) := by
  let restrict : ((k : Finset.Iic (t + 1)) → Draw L K) →
      ((k : Finset.Iic t) → Draw L K) :=
    fun p k => p ⟨k.val, Finset.mem_Iic.mpr
      (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩
  let H : ((k : Finset.Iic (t + 1)) → Draw L K) → ℝ := fun p =>
    @ite ℝ (∃ i j,
        selectLabels (prefixLabels init t (restrict p))
          (p ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩) = some (i, j) ∧
        A (auxPrefix init F t (restrict p)) i j) (Classical.propDecidable _) 1 0
  have hH : Measurable H := by
    intro C _
    exact (Set.to_countable _).measurableSet
  exact (hH.comp (measurable_pairLog_prefix L K (t + 1))).stronglyMeasurable

theorem role_aux_pair_indicator_zero_one
    (init : Cfg L K) (F : PairRule L K)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (t : ℕ) (ω : Ω L K) :
    role_aux_pair_indicator init F A t ω = 0 ∨
      role_aux_pair_indicator init F A t ω = 1 := by
  unfold role_aux_pair_indicator
  split_ifs <;> simp

theorem role_aux_pair_indicator_integrable
    (init : Cfg L K) (F : PairRule L K)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (t : ℕ) :
    Integrable (role_aux_pair_indicator init F A t) (law init) :=
  PhaseThreeScalar.bernoulli_integrable
    (role_aux_pair_indicator_stronglyMeasurable init F A)
    (fun s => ae_of_all _ (role_aux_pair_indicator_zero_one init F A s)) t

/-- The conditional law of the auxiliary pair indicator, stated for the indicator as
defined here (its `if` uses the classical instance). -/
theorem role_aux_pair_condExp (init : Cfg L K) (hc : 2 ≤ init.card) (F : PairRule L K)
    (C : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop) (t : ℕ) :
    (law init)[role_aux_pair_indicator init F C t | pairLogFiltration L K t] =ᵐ[law init]
      fun ω => ((goodPairs C (auxLabels init F ω t)).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  refine Filter.EventuallyEq.trans
    (condExp_congr_ae (Filter.Eventually.of_forall fun ω' => ?_))
    (aux_pair_conditional_probability init hc F C t)
  dsimp only [role_aux_pair_indicator]
  split_ifs <;> rfl

theorem role_aux_two_event_condExp_le
    (init : Cfg L K) (hc : 2 ≤ init.card) (F : PairRule L K)
    (A B : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (φ a b : (Fin init.card → AgentState L K) → ℝ)
    (hstep : ∀ t ω,
      φ (auxLabels init F ω (t + 1)) ≤
        φ (auxLabels init F ω t) +
          a (auxLabels init F ω t) * role_aux_pair_indicator init F A t ω +
          b (auxLabels init F ω t) * role_aux_pair_indicator init F B t ω)
    (t : ℕ) :
    (law init)[fun ω => φ (auxLabels init F ω (t + 1)) |
        pairLogFiltration L K t] ≤ᵐ[law init]
      fun ω => φ (auxLabels init F ω t) +
        a (auxLabels init F ω t) *
          (((goodPairs A (auxLabels init F ω t)).card : ℝ) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1))) +
        b (auxLabels init F ω t) *
          (((goodPairs B (auxLabels init F ω t)).card : ℝ) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1))) := by
  let V : Ω L K → ℝ := fun ω => φ (auxLabels init F ω t)
  let aState : Ω L K → ℝ := fun ω => a (auxLabels init F ω t)
  let bState : Ω L K → ℝ := fun ω => b (auxLabels init F ω t)
  let IA := role_aux_pair_indicator init F A t
  let IB := role_aux_pair_indicator init F B t
  let VA : Ω L K → ℝ := aState * IA
  let VB : Ω L K → ℝ := bState * IB
  have hV : Integrable V (law init) := integrable_aux_potential init F φ t
  have hIA : Integrable IA (law init) :=
    role_aux_pair_indicator_integrable init F A t
  have hIB : Integrable IB (law init) :=
    role_aux_pair_indicator_integrable init F B t
  have hnorm (C :
      (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop) :
      ∀ᵐ ω ∂law init, ‖role_aux_pair_indicator init F C t ω‖ ≤ 1 := by
    exact ae_of_all _ fun ω => by
      rcases role_aux_pair_indicator_zero_one init F C t ω with h | h <;>
        rw [h] <;> norm_num
  have hVA : Integrable VA (law init) :=
    (integrable_aux_potential init F a t).mul_bdd (c := 1)
      ((role_aux_pair_indicator_stronglyMeasurable init F A t).mono
        ((pairLogFiltration L K).le (t + 1))).aestronglyMeasurable (hnorm A)
  have hVB : Integrable VB (law init) :=
    (integrable_aux_potential init F b t).mul_bdd
      ((role_aux_pair_indicator_stronglyMeasurable init F B t).mono
        ((pairLogFiltration L K).le (t + 1))).aestronglyMeasurable (hnorm B)
  have hmono := condExp_mono (m := pairLogFiltration L K t)
    (integrable_aux_potential init F φ (t + 1))
    ((hV.add hVA).add hVB) (ae_of_all _ (hstep t))
  have hadd := condExp_add (hV.add hVA) hVB (pairLogFiltration L K t)
  have haddVA := condExp_add hV hVA (pairLogFiltration L K t)
  have hpullA := condExp_mul_of_stronglyMeasurable_left
    (measurable_aux_potential init F a t).stronglyMeasurable hVA hIA
  have hpullB := condExp_mul_of_stronglyMeasurable_left
    (measurable_aux_potential init F b t).stronglyMeasurable hVB hIB
  have hfixed : (law init)[V | pairLogFiltration L K t] = V :=
    condExp_of_stronglyMeasurable ((pairLogFiltration L K).le t)
      (measurable_aux_potential init F φ t).stronglyMeasurable hV
  have hprobA :
      (law init)[IA | pairLogFiltration L K t] =ᵐ[law init]
        fun ω => ((goodPairs A (auxLabels init F ω t)).card : ℝ) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
    exact role_aux_pair_condExp init hc F A t
  have hprobB :
      (law init)[IB | pairLogFiltration L K t] =ᵐ[law init]
        fun ω => ((goodPairs B (auxLabels init F ω t)).card : ℝ) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
    exact role_aux_pair_condExp init hc F B t
  filter_upwards [hmono, hadd, haddVA, hpullA, hpullB, hprobA, hprobB]
    with ω hm ha hav hpa hpb hqa hqb
  calc
    ((law init)[fun ω => φ (auxLabels init F ω (t + 1)) |
        pairLogFiltration L K t]) ω
        ≤ ((law init)[V + VA + VB | pairLogFiltration L K t]) ω := hm
    _ = ((law init)[V + VA | pairLogFiltration L K t]) ω +
          ((law init)[VB | pairLogFiltration L K t]) ω := ha
    _ = ((law init)[V | pairLogFiltration L K t]) ω +
          ((law init)[VA | pairLogFiltration L K t]) ω +
          ((law init)[VB | pairLogFiltration L K t]) ω := by rw [hav]; rfl
    _ = _ := by
      rw [hfixed, hpa, hpb]
      change V ω + aState ω * ((law init)[IA | pairLogFiltration L K t]) ω +
        bState ω * ((law init)[IB | pairLogFiltration L K t]) ω = _
      rw [hqa, hqb]


/-! ## Births, top reactions, and the two stopped probability floors -/

noncomputable def roleBirths (f : Fin n → AgentState L K) : ℕ :=
  roleFreeLabels f / 2

noncomputable def roleReactions (f : Fin n → AgentState L K) : ℕ :=
  n - roleMcrLabels f - roleBirths f

theorem role_birth_reaction_balance (f : Fin n → AgentState L K) :
    roleMcrLabels f + roleReactions f + roleBirths f = n ∧
      roleBirths f ≤ roleReactions f ∧ 2 * roleBirths f ≤ roleFreeLabels f := by
  have hc := role_freeTarget_add_mcr_le_card (labelCfg f)
  change roleFreeLabels f + roleMcrLabels f ≤ (labelCfg f).card at hc
  rw [labelCfg_card] at hc
  dsimp only [roleBirths, roleReactions]
  omega

theorem role_birth_reaction_initial (init : Cfg L K)
    (hinit : Phase0Initial n init) :
    roleBirths (initialLabels init) = 0 ∧
      roleReactions (initialLabels init) = 0 := by
  have hf : roleFreeLabels (initialLabels init) = 0 := by
    change freeTargetCount (labelCfg (initialLabels init)) = 0
    rw [initialLabels_config]
    exact role_freeTarget_initial hinit
  have hu : roleMcrLabels (initialLabels init) = init.card := by
    change roleMCRCount (labelCfg (initialLabels init)) = init.card
    rw [initialLabels_config]
    apply Multiset.countP_eq_card.mpr
    intro a ha
    exact (hinit.2 a ha).2
  simp [roleBirths, roleReactions, hf, hu]

theorem role_birth_not_one (s t : AgentState L K)
    (hbirth : roleBirthPair s t) : ¬ roleOneSidedPair s t := by
  rintro (⟨_, hf⟩ | ⟨hf, _⟩)
  · exact hf.1 hbirth.2
  · exact hf.1 hbirth.1

theorem role_births_update (f : Fin n → AgentState L K)
    (hf : ∀ k, NotAssignedMcr (f k)) (i j : Fin n) (hij : i ≠ j) :
    roleBirths (ruleUpdate (phaseZeroRoleRule L K) f i j) =
      roleBirths f + if roleBirthPair (f i) (f j) then 1 else 0 := by
  have h := role_freeTarget_update f hf i j hij
  unfold roleBirths roleFreeLabels
  rw [h]
  unfold PhaseZeroEntry.phaseZeroFreshGain roleBirthPair
  split_ifs <;> omega

theorem role_reactions_update (f : Fin n → AgentState L K)
    (hf : ∀ k, NotAssignedMcr (f k)) (i j : Fin n) (hij : i ≠ j) :
    roleReactions (ruleUpdate (phaseZeroRoleRule L K) f i j) =
      roleReactions f + (if roleBirthPair (f i) (f j) then 1 else 0) +
        (if roleOneSidedPair (f i) (f j) then 1 else 0) := by
  have hb := role_births_update f hf i j hij
  have hu := role_mcr_update f i j hij
  have hbefore := (role_birth_reaction_balance f).1
  have hafter :=
    (role_birth_reaction_balance (ruleUpdate (phaseZeroRoleRule L K) f i j)).1
  omega

theorem role_fresh_pool_bounds_before_reactions
    (f : Fin n → AgentState L K) (hR : roleReactions f < n / 8) :
    4 * roleMcrLabels f ≥ 3 * n ∧
      2 * roleFreeLabels f + 1 ≤ roleMcrLabels f := by
  obtain ⟨hbal, hbr, _⟩ := role_birth_reaction_balance f
  have hfloor : roleFreeLabels f ≤ 2 * roleBirths f + 1 := by
    dsimp [roleBirths]
    omega
  omega

theorem role_birth_rate_lower
    (f : Fin n → AgentState L K) (hn : 8 ≤ n)
    (hR : roleReactions f < n / 8) :
    (1 / 2 : ℝ) ≤
      ((goodPairs (fun g i j => roleBirthPair (g i) (g j)) f).card : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1)) := by
  obtain ⟨hU, _⟩ := role_fresh_pool_bounds_before_reactions f hR
  have hnreal : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (3 / 4 : ℝ) * n ≤ roleMcrLabels f := by
    have hcast : (3 : ℝ) * n ≤ 4 * (roleMcrLabels f : ℝ) := by
      exact_mod_cast hU
    linarith
  have huone : 1 ≤ roleMcrLabels f := by omega
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  rw [role_birth_goodPairs_card]
  apply (le_div_iff₀ hden).2
  rw [Nat.cast_mul, Nat.cast_sub huone, Nat.cast_one]
  have hsq :
      0 ≤ ((roleMcrLabels f : ℝ) - (3 / 4 : ℝ) * n) *
        ((roleMcrLabels f : ℝ) + (3 / 4 : ℝ) * n - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hnquad : 0 ≤ (n : ℝ) * ((n : ℝ) - 4) :=
    mul_nonneg (Nat.cast_nonneg n) (by linarith)
  nlinarith

theorem role_one_rate_le_birth
    (f : Fin n → AgentState L K) (hn : 8 ≤ n)
    (hR : roleReactions f < n / 8) :
    ((goodPairs (fun g i j => roleOneSidedPair (g i) (g j)) f).card : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1)) ≤
      ((goodPairs (fun g i j => roleBirthPair (g i) (g j)) f).card : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1)) := by
  obtain ⟨_, hU⟩ := role_fresh_pool_bounds_before_reactions f hR
  have hnat : 2 * roleMcrLabels f * roleFreeLabels f ≤
      roleMcrLabels f * (roleMcrLabels f - 1) := by
    have h := Nat.mul_le_mul_left (roleMcrLabels f)
      (show 2 * roleFreeLabels f ≤ roleMcrLabels f - 1 by omega)
    nlinarith
  apply div_le_div_of_nonneg_right
  · rw [role_one_sided_goodPairs_card, role_birth_goodPairs_card]
    exact_mod_cast hnat
  · have hnreal : (8 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (Nat.cast_nonneg n) (by linarith)


/-! ## Scalar calibrations for the two stopped comparisons -/

private theorem role_log_three_halves_upper :
    Real.log (3 / 2 : ℝ) ≤ (41 / 100 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem role_log_six_fifths_lower :
    (2 / 11 : ℝ) ≤ Real.log (6 / 5 : ℝ) := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 11 : ℝ)) (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The reaction-count exponential estimate, with the integer floor retained. -/
theorem role_reaction_exponent_le {n : ℕ} (hn : 200 ≤ n) :
    (n : ℝ) / 20 * Real.log (3 / 2 : ℝ) -
        ((n / 8 : ℕ) : ℝ) * Real.log (6 / 5 : ℝ) ≤
      -(n : ℝ) / 1000 := by
  have hnR : (200 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdiv : n < 8 * (n / 8) + 8 := by omega
  have hdivR : (n : ℝ) < 8 * ((n / 8 : ℕ) : ℝ) + 8 := by
    exact_mod_cast hdiv
  have hfirst := mul_le_mul_of_nonneg_left role_log_three_halves_upper
    (show 0 ≤ (n : ℝ) / 20 by positivity)
  have hsecond := mul_le_mul_of_nonneg_left role_log_six_fifths_lower
    (show 0 ≤ ((n / 8 : ℕ) : ℝ) by positivity)
  nlinarith only [hnR, hdivR, hfirst, hsecond]

/-- The raw-time hitting estimate at n interactions. -/
theorem role_raw_exponent_le (n : ℕ) :
    ((n / 8 : ℕ) : ℝ) * Real.log 2 - (n : ℝ) / 4 ≤
      -(n : ℝ) / 1000 := by
  have hdiv : 8 * (n / 8) ≤ n := by omega
  have hdivR : 8 * ((n / 8 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hdiv
  have hlog := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le
    (show 0 ≤ ((n / 8 : ℕ) : ℝ) by positivity)
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith only [hdivR, hlog, hnR]

/-- The twenty-logarithmic-window geometric contraction is at most n⁻³. -/
theorem role_mcr_window_scalar {n : ℕ} (hn : 1 ≤ n) :
    (1 - 1 / (5 * (n : ℝ))) ^ logWindow n 20 * (n : ℝ) ≤
      1 / (n : ℝ) ^ 3 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by linarith only [hnR]
  have hbase : 0 ≤ 1 - 1 / (5 * (n : ℝ)) := by
    have hsmall : 1 / (5 * (n : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 5 * (n : ℝ))).2
      linarith only [hnR]
    exact sub_nonneg.mpr hsmall
  have hexpbase :
      1 - 1 / (5 * (n : ℝ)) ≤ Real.exp (-(1 / (5 * (n : ℝ)))) := by
    linarith only [Real.add_one_le_exp (-(1 / (5 * (n : ℝ))))]
  have hgeom :
      (1 - 1 / (5 * (n : ℝ))) ^ logWindow n 20 ≤
        Real.exp (-((logWindow n 20 : ℕ) : ℝ) / (5 * (n : ℝ))) := by
    calc
      _ ≤ (Real.exp (-(1 / (5 * (n : ℝ))))) ^ logWindow n 20 :=
        pow_le_pow_left₀ hbase hexpbase _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hwindow : 20 * (n : ℝ) * Real.log (n : ℝ) ≤
      ((logWindow n 20 : ℕ) : ℝ) := by
    simpa only [logWindow, Nat.cast_ofNat] using
      (Nat.le_ceil (20 * (n : ℝ) * Real.log (n : ℝ)))
  have htime :
      -((logWindow n 20 : ℕ) : ℝ) / (5 * (n : ℝ)) ≤
        -(4 * Real.log (n : ℝ)) := by
    apply (div_le_iff₀ (by positivity : 0 < 5 * (n : ℝ))).2
    nlinarith only [hwindow]
  have hfour :
      Real.exp (-(4 * Real.log (n : ℝ))) = 1 / (n : ℝ) ^ 4 := by
    have hpower :
        Real.exp (4 * Real.log (n : ℝ)) =
          (Real.exp (Real.log (n : ℝ))) ^ (4 : ℕ) := by
      simpa only [Nat.cast_ofNat] using
        (Real.exp_nat_mul (Real.log (n : ℝ)) 4)
    rw [Real.exp_neg, hpower, Real.exp_log hnp, one_div]
  calc
    _ ≤ Real.exp (-((logWindow n 20 : ℕ) : ℝ) / (5 * (n : ℝ))) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hgeom hnp.le
    _ ≤ Real.exp (-(4 * Real.log (n : ℝ))) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htime) hnp.le
    _ = 1 / (n : ℝ) ^ 3 := by
      rw [hfour]
      field_simp [hnp.ne'] <;> ring


/-! ## Potentials for the stopped reaction and raw-time comparisons -/

theorem role_count_potential_step
    (init : Cfg L K) (hinit : Phase0InitialFresh n init)
    (ψ a b : ℕ → ℕ → ℝ)
    (hbirth : ∀ r k, ψ (r + 1) (k + 1) ≤ ψ r k + a r k)
    (hone : ∀ r k, ψ (r + 1) k ≤ ψ r k + b r k)
    (t : ℕ) (ω : Ω L K) :
    ψ (roleReactions (roleLabels init ω (t + 1)))
        (roleBirths (roleLabels init ω (t + 1))) ≤
      ψ (roleReactions (roleLabels init ω t))
          (roleBirths (roleLabels init ω t)) +
        a (roleReactions (roleLabels init ω t))
            (roleBirths (roleLabels init ω t)) *
          role_aux_pair_indicator init (phaseZeroRoleRule L K)
            (fun g i j => roleBirthPair (g i) (g j)) t ω +
        b (roleReactions (roleLabels init ω t))
            (roleBirths (roleLabels init ω t)) *
          role_aux_pair_indicator init (phaseZeroRoleRule L K)
            (fun g i j => roleOneSidedPair (g i) (g j)) t ω := by
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have hnext : roleLabels init ω (t + 1) = roleLabels init ω t := by
        change auxLabels init (phaseZeroRoleRule L K) ω (t + 1) = _
        rw [auxLabels_succ, hd] <;> rfl
      rw [hnext]
      simp [role_aux_pair_indicator, hd]
  | some ij =>
      obtain ⟨i, j⟩ := ij
      have hij := (labelsAt_selected_transition init ω t i j hd).1
      have hf := role_noAssigned_labels init hinit ω t
      have hnext : roleLabels init ω (t + 1) =
          ruleUpdate (phaseZeroRoleRule L K) (roleLabels init ω t) i j := by
        change auxLabels init (phaseZeroRoleRule L K) ω (t + 1) = _
        rw [auxLabels_succ, hd] <;> rfl
      have hA :
          role_aux_pair_indicator init (phaseZeroRoleRule L K)
            (fun g i j => roleBirthPair (g i) (g j)) t ω =
          if roleBirthPair (roleLabels init ω t i) (roleLabels init ω t j)
            then (1 : ℝ) else 0 := by
        simp [role_aux_pair_indicator, hd, Prod.mk.injEq, roleLabels]
      have hB :
          role_aux_pair_indicator init (phaseZeroRoleRule L K)
            (fun g i j => roleOneSidedPair (g i) (g j)) t ω =
          if roleOneSidedPair (roleLabels init ω t i) (roleLabels init ω t j)
            then (1 : ℝ) else 0 := by
        simp [role_aux_pair_indicator, hd, Prod.mk.injEq, roleLabels]
      rw [hA, hB, hnext, role_births_update _ hf _ _ hij,
        role_reactions_update _ hf _ _ hij]
      by_cases hb : roleBirthPair (roleLabels init ω t i) (roleLabels init ω t j)
      · have ho := role_birth_not_one _ _ hb
        simpa [hb, ho] using
          hbirth (roleReactions (roleLabels init ω t))
            (roleBirths (roleLabels init ω t))
      · by_cases ho :
          roleOneSidedPair (roleLabels init ω t i) (roleLabels init ω t j)
        · simpa [hb, ho] using
            hone (roleReactions (roleLabels init ω t))
              (roleBirths (roleLabels init ω t))
        · simp [hb, ho]

noncomputable def roleReactionPotential (m J r k : ℕ) : ℝ :=
  Real.exp ((m : ℝ) / 20 * Real.log (3 / 2 : ℝ) -
      (J : ℝ) * Real.log (6 / 5 : ℝ)) *
    (6 / 5 : ℝ) ^ min r J * (2 / 3 : ℝ) ^ k

theorem role_reaction_potential_nonneg (m J r k : ℕ) :
    0 ≤ roleReactionPotential m J r k := by
  unfold roleReactionPotential
  positivity

theorem role_reaction_birth_step (m J r k : ℕ) :
    roleReactionPotential m J (r + 1) (k + 1) =
      roleReactionPotential m J r k +
        roleReactionPotential m J r k *
          (if r < J then (-1 / 5 : ℝ) else (-1 / 3 : ℝ)) := by
  by_cases hr : r < J
  · simp only [roleReactionPotential, min_eq_left hr.le,
      min_eq_left (Nat.succ_le_iff.mpr hr), if_pos hr, pow_succ]
    ring
  · have hJr : J ≤ r := le_of_not_gt hr
    have hJnext : J ≤ r + 1 := by omega
    simp only [roleReactionPotential, min_eq_right hJr,
      min_eq_right hJnext, if_neg hr, pow_succ]
    ring

theorem role_reaction_one_step (m J r k : ℕ) :
    roleReactionPotential m J (r + 1) k =
      roleReactionPotential m J r k +
        roleReactionPotential m J r k *
          (if r < J then (1 / 5 : ℝ) else 0) := by
  by_cases hr : r < J
  · simp only [roleReactionPotential, min_eq_left hr.le,
      min_eq_left (Nat.succ_le_iff.mpr hr), if_pos hr, pow_succ]
    ring
  · have hJr : J ≤ r := le_of_not_gt hr
    have hJnext : J ≤ r + 1 := by omega
    simp only [roleReactionPotential, min_eq_right hJr,
      min_eq_right hJnext, if_neg hr, mul_zero, add_zero]

theorem role_reaction_potential_detects
    (m J r k : ℕ) (hr : J ≤ r) (hk : (k : ℝ) < (m : ℝ) / 20) :
    1 ≤ roleReactionPotential m J r k := by
  have hfirst : (6 / 5 : ℝ) ^ J =
      Real.exp ((J : ℝ) * Real.log (6 / 5 : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 6 / 5)]
  have hsecond : (2 / 3 : ℝ) ^ k =
      Real.exp (-(k : ℝ) * Real.log (3 / 2 : ℝ)) := by
    have hbase : Real.exp (-Real.log (3 / 2 : ℝ)) = (2 / 3 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
      norm_num
    calc
      (2 / 3 : ℝ) ^ k = (Real.exp (-Real.log (3 / 2 : ℝ))) ^ k := by rw [hbase]
      _ = Real.exp ((k : ℝ) * (-Real.log (3 / 2 : ℝ))) :=
        (Real.exp_nat_mul _ _).symm
      _ = _ := by congr 1; ring
  rw [roleReactionPotential, min_eq_right hr, hfirst, hsecond,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.one_le_exp_iff.mpr
  have hlog : 0 ≤ Real.log (3 / 2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg hlog (sub_nonneg.mpr hk.le)]

noncomputable def roleRawPotential (J r : ℕ) : ℝ :=
  (2 : ℝ) ^ J * if r < J then (1 / 2 : ℝ) ^ r else 0

theorem role_raw_potential_nonneg (J r : ℕ) :
    0 ≤ roleRawPotential J r := by
  unfold roleRawPotential
  split_ifs <;> positivity

theorem role_raw_potential_progress (J r : ℕ) :
    roleRawPotential J (r + 1) ≤
      roleRawPotential J r + (-roleRawPotential J r / 2) := by
  by_cases hr : r < J
  · by_cases hn : r + 1 < J
    · simp only [roleRawPotential, if_pos hr, if_pos hn, pow_succ]
      nlinarith
    · have hzero : roleRawPotential J (r + 1) = 0 := by
        simp [roleRawPotential, hn]
      rw [hzero]
      linarith [role_raw_potential_nonneg J r]
  · have hn : ¬ r + 1 < J := by omega
    simp [roleRawPotential, hr, hn]

theorem role_raw_potential_detects (J r : ℕ) (hr : r < J) :
    1 ≤ roleRawPotential J r := by
  have hpow : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) hr.le
  calc
    1 = (2 : ℝ) ^ r * (1 / 2 : ℝ) ^ r := by
      rw [← mul_pow]
      norm_num
    _ ≤ (2 : ℝ) ^ J * (1 / 2 : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = roleRawPotential J r := by simp [roleRawPotential, hr]

theorem role_raw_scalar_power (n : ℕ) :
    (1 - (1 / 4 : ℝ)) ^ n * (2 : ℝ) ^ (n / 8) ≤
      Real.exp ((n / 8 : ℕ) * Real.log 2 - (n : ℝ) / 4) := by
  have hbase : (1 - (1 / 4 : ℝ)) ≤ Real.exp (-1 / 4 : ℝ) := by
    linarith [Real.add_one_le_exp (-1 / 4 : ℝ)]
  calc
    (1 - (1 / 4 : ℝ)) ^ n * (2 : ℝ) ^ (n / 8) ≤
        (Real.exp (-1 / 4 : ℝ)) ^ n * (2 : ℝ) ^ (n / 8) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by norm_num) hbase n) (by positivity)
    _ = Real.exp ((n : ℝ) * (-1 / 4 : ℝ)) *
        Real.exp (((n / 8 : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem role_reaction_potential_drift
    (init : Cfg L K) (hinit : Phase0InitialFresh n init) (hn : 8 ≤ n)
    (t : ℕ) :
    (law init)[fun ω =>
      roleReactionPotential n (n / 8)
        (roleReactions (roleLabels init ω (t + 1)))
        (roleBirths (roleLabels init ω (t + 1))) |
      pairLogFiltration L K t] ≤ᵐ[law init]
    fun ω => roleReactionPotential n (n / 8)
      (roleReactions (roleLabels init ω t))
      (roleBirths (roleLabels init ω t)) := by
  have hcard : init.card = n := hinit.1.1
  have hc : 2 ≤ init.card := by omega
  have hcLarge : 8 ≤ init.card := by omega
  let ψ := roleReactionPotential n (n / 8)
  let α : ℕ → ℕ → ℝ := fun r k =>
    ψ r k * if r < n / 8 then (-1 / 5 : ℝ) else (-1 / 3 : ℝ)
  let β : ℕ → ℕ → ℝ := fun r k =>
    ψ r k * if r < n / 8 then (1 / 5 : ℝ) else 0
  let φ : (Fin init.card → AgentState L K) → ℝ := fun f =>
    ψ (roleReactions f) (roleBirths f)
  let a : (Fin init.card → AgentState L K) → ℝ := fun f =>
    α (roleReactions f) (roleBirths f)
  let b : (Fin init.card → AgentState L K) → ℝ := fun f =>
    β (roleReactions f) (roleBirths f)
  have hstep := role_count_potential_step init hinit ψ α β
    (fun r k => (role_reaction_birth_step n (n / 8) r k).le)
    (fun r k => (role_reaction_one_step n (n / 8) r k).le)
  have hce := role_aux_two_event_condExp_le init hc (phaseZeroRoleRule L K)
    (fun g i j => roleBirthPair (g i) (g j))
    (fun g i j => roleOneSidedPair (g i) (g j)) φ a b hstep t
  filter_upwards [hce] with ω hω
  let f := roleLabels init ω t
  let pBirth : ℝ :=
    ((goodPairs (fun g i j => roleBirthPair (g i) (g j)) f).card : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1))
  let pOne : ℝ :=
    ((goodPairs (fun g i j => roleOneSidedPair (g i) (g j)) f).card : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1))
  have hω' :
      ((law init)[fun ω => φ (roleLabels init ω (t + 1)) |
        pairLogFiltration L K t]) ω ≤ φ f + a f * pBirth + b f * pOne := hω
  change ((law init)[fun ω => φ (roleLabels init ω (t + 1)) |
    pairLogFiltration L K t]) ω ≤ φ f
  have hv : 0 ≤ φ f := role_reaction_potential_nonneg _ _ _ _
  by_cases hr : roleReactions f < n / 8
  · have hrCard : roleReactions f < init.card / 8 := by
      calc
        roleReactions f < n / 8 := hr
        _ = init.card / 8 := congrArg (fun m : ℕ => m / 8) hcard.symm
    have hcomparison : pOne ≤ pBirth :=
      role_one_rate_le_birth f hcLarge hrCard
    have ha : a f = φ f * (-1 / 5 : ℝ) := by
      simp only [a, α, φ, if_pos hr]
    have hb : b f = φ f * (1 / 5 : ℝ) := by
      simp only [b, β, φ, if_pos hr]
    rw [ha, hb] at hω'
    have hmul := mul_nonneg hv (sub_nonneg.mpr hcomparison)
    nlinarith
  · have hnreal : (8 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hcLarge
    have hp : 0 ≤ pBirth := by
      dsimp [pBirth]
      apply div_nonneg (Nat.cast_nonneg _)
      exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have ha : a f = φ f * (-1 / 3 : ℝ) := by
      simp only [a, α, φ, if_neg hr]
    have hb : b f = 0 := by
      simp only [b, β, if_neg hr, mul_zero]
    rw [ha, hb] at hω'
    have hmul := mul_nonneg hv hp
    nlinarith

theorem role_raw_potential_drift
    (init : Cfg L K) (hinit : Phase0InitialFresh n init) (hn : 8 ≤ n)
    (t : ℕ) :
    (law init)[fun ω =>
      roleRawPotential (n / 8) (roleReactions (roleLabels init ω (t + 1))) |
      pairLogFiltration L K t] ≤ᵐ[law init]
    fun ω => (1 - (1 / 4 : ℝ)) *
      roleRawPotential (n / 8) (roleReactions (roleLabels init ω t)) := by
  have hcard : init.card = n := hinit.1.1
  have hc : 2 ≤ init.card := by omega
  have hcLarge : 8 ≤ init.card := by omega
  let ψ : ℕ → ℕ → ℝ := fun r _ => roleRawPotential (n / 8) r
  let α : ℕ → ℕ → ℝ := fun r _ => -roleRawPotential (n / 8) r / 2
  let φ : (Fin init.card → AgentState L K) → ℝ := fun f =>
    roleRawPotential (n / 8) (roleReactions f)
  let a : (Fin init.card → AgentState L K) → ℝ := fun f => -φ f / 2
  have hstep := role_count_potential_step init hinit ψ α α
    (fun r _ => role_raw_potential_progress (n / 8) r)
    (fun r _ => role_raw_potential_progress (n / 8) r)
  have hce := role_aux_two_event_condExp_le init hc (phaseZeroRoleRule L K)
    (fun g i j => roleBirthPair (g i) (g j))
    (fun g i j => roleOneSidedPair (g i) (g j)) φ a a hstep t
  filter_upwards [hce] with ω hω
  let f := roleLabels init ω t
  let pBirth : ℝ :=
    ((goodPairs (fun g i j => roleBirthPair (g i) (g j)) f).card : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1))
  let pOne : ℝ :=
    ((goodPairs (fun g i j => roleOneSidedPair (g i) (g j)) f).card : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1))
  have hω' :
      ((law init)[fun ω => φ (roleLabels init ω (t + 1)) |
        pairLogFiltration L K t]) ω ≤
      φ f + (-φ f / 2) * pBirth + (-φ f / 2) * pOne := hω
  change ((law init)[fun ω => φ (roleLabels init ω (t + 1)) |
    pairLogFiltration L K t]) ω ≤ (1 - (1 / 4 : ℝ)) * φ f
  have hv : 0 ≤ φ f := role_raw_potential_nonneg _ _
  by_cases hr : roleReactions f < n / 8
  · have hrCard : roleReactions f < init.card / 8 := by
      calc
        roleReactions f < n / 8 := hr
        _ = init.card / 8 := congrArg (fun m : ℕ => m / 8) hcard.symm
    have hp : (1 / 2 : ℝ) ≤ pBirth :=
      role_birth_rate_lower f hcLarge hrCard
    have hnreal : (8 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hcLarge
    have hq : 0 ≤ pOne := by
      dsimp [pOne]
      apply div_nonneg (Nat.cast_nonneg _)
      exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hmul := mul_nonneg hv (show 0 ≤ pBirth + pOne - 1 / 2 by linarith)
    nlinarith
  · have hzero : φ f = 0 := by simp [φ, roleRawPotential, hr]
    simpa only [hzero, neg_zero, zero_div, zero_mul, add_zero, mul_zero] using hω'


/-- The reaction-count comparison with reaction reward frozen at floor(n/8). -/
theorem role_fresh_reaction_tail_of_initial
    (init : Cfg L K) (hinit : Phase0InitialFresh n init)
    (hn : 200 ≤ n) (T : ℕ) :
    (law init).real {ω |
      n / 8 ≤ roleReactions (roleLabels init ω T) ∧
        (roleBirths (roleLabels init ω T) : ℝ) < (n : ℝ) / 20} ≤
      Real.exp (-(n : ℝ) / 1000) := by
  let φ : (Fin init.card → AgentState L K) → ℝ := fun f =>
    roleReactionPotential n (n / 8) (roleReactions f) (roleBirths f)
  have hdrift : ∀ t,
      (law init)[fun ω => φ (auxLabels init (phaseZeroRoleRule L K) ω (t + 1)) |
        pairLogFiltration L K t] ≤ᵐ[law init]
      fun ω => (1 - (0 : ℝ)) * φ (auxLabels init (phaseZeroRoleRule L K) ω t) := by
    intro t
    simpa only [sub_zero, one_mul] using
      role_reaction_potential_drift init hinit (by omega) t
  have htail := aux_drift_tail_le init (phaseZeroRoleRule L K) φ
    (fun f => role_reaction_potential_nonneg _ _ _ _)
    (c := 0) (by norm_num) hdrift T
  have hsub : {ω |
      n / 8 ≤ roleReactions (roleLabels init ω T) ∧
        (roleBirths (roleLabels init ω T) : ℝ) < (n : ℝ) / 20} ⊆
      {ω | 1 ≤ φ (auxLabels init (phaseZeroRoleRule L K) ω T)} := by
    intro ω hω
    exact role_reaction_potential_detects n (n / 8) _ _ hω.1 hω.2
  obtain ⟨hb, hr⟩ := role_birth_reaction_initial init hinit.1
  calc
    (law init).real {ω |
        n / 8 ≤ roleReactions (roleLabels init ω T) ∧
          (roleBirths (roleLabels init ω T) : ℝ) < (n : ℝ) / 20}
        ≤ (law init).real
          {ω | 1 ≤ φ (auxLabels init (phaseZeroRoleRule L K) ω T)} :=
      measureReal_mono hsub
    _ ≤ (1 - (0 : ℝ)) ^ T * φ (initialLabels init) := htail
    _ = Real.exp ((n : ℝ) / 20 * Real.log (3 / 2 : ℝ) -
        ((n / 8 : ℕ) : ℝ) * Real.log (6 / 5 : ℝ)) := by
      simp [φ, roleReactionPotential, hb, hr]
    _ ≤ Real.exp (-(n : ℝ) / 1000) :=
      Real.exp_le_exp.mpr (role_reaction_exponent_le hn)

/-- The raw-time comparison killed at the first floor(n/8) top reactions. -/
theorem role_fresh_raw_tail_of_initial
    (init : Cfg L K) (hinit : Phase0InitialFresh n init)
    (hn : 200 ≤ n) :
    (law init).real {ω | roleReactions (roleLabels init ω n) < n / 8} ≤
      Real.exp (-(n : ℝ) / 1000) := by
  let φ : (Fin init.card → AgentState L K) → ℝ := fun f =>
    roleRawPotential (n / 8) (roleReactions f)
  have hdrift : ∀ t,
      (law init)[fun ω => φ (auxLabels init (phaseZeroRoleRule L K) ω (t + 1)) |
        pairLogFiltration L K t] ≤ᵐ[law init]
      fun ω => (1 - (1 / 4 : ℝ)) *
        φ (auxLabels init (phaseZeroRoleRule L K) ω t) :=
    fun t => role_raw_potential_drift init hinit (by omega) t
  have htail := aux_drift_tail_le init (phaseZeroRoleRule L K) φ
    (fun f => role_raw_potential_nonneg _ _)
    (c := (1 / 4 : ℝ)) (by norm_num) hdrift n
  have hsub : {ω | roleReactions (roleLabels init ω n) < n / 8} ⊆
      {ω | 1 ≤ φ (auxLabels init (phaseZeroRoleRule L K) ω n)} := by
    intro ω hω
    exact role_raw_potential_detects _ _ hω
  obtain ⟨_, hr⟩ := role_birth_reaction_initial init hinit.1
  have hJ : 0 < n / 8 := by omega
  calc
    (law init).real {ω | roleReactions (roleLabels init ω n) < n / 8} ≤
        (law init).real
          {ω | 1 ≤ φ (auxLabels init (phaseZeroRoleRule L K) ω n)} :=
      measureReal_mono hsub
    _ ≤ (1 - (1 / 4 : ℝ)) ^ n * φ (initialLabels init) := htail
    _ = (1 - (1 / 4 : ℝ)) ^ n * (2 : ℝ) ^ (n / 8) := by
      simp [φ, roleRawPotential, hr, hJ]
    _ ≤ Real.exp (((n / 8 : ℕ) : ℝ) * Real.log 2 - (n : ℝ) / 4) :=
      role_raw_scalar_power n
    _ ≤ Real.exp (-(n : ℝ) / 1000) :=
      Real.exp_le_exp.mpr (role_raw_exponent_le n)

theorem role_fresh_pool_tail_of_initial
    (init : Cfg L K) (hinit : Phase0InitialFresh n init)
    (hn : 200 ≤ n) :
    (law init).real {ω |
      (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10} ≤
      2 * Real.exp (-(n : ℝ) / 1000) := by
  let A : Set (Ω L K) :=
    {ω | roleReactions (roleLabels init ω n) < n / 8}
  let B : Set (Ω L K) := {ω |
    n / 8 ≤ roleReactions (roleLabels init ω n) ∧
      (roleBirths (roleLabels init ω n) : ℝ) < (n : ℝ) / 20}
  have hsub : {ω |
      (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10} ⊆ A ∪ B := by
    intro ω hω
    by_cases hr : roleReactions (roleLabels init ω n) < n / 8
    · exact Or.inl hr
    · right
      refine ⟨le_of_not_gt hr, ?_⟩
      have hb :
          (2 : ℝ) * (roleBirths (roleLabels init ω n) : ℝ) ≤
            (roleFreeLabels (roleLabels init ω n) : ℝ) := by
        exact_mod_cast (role_birth_reaction_balance (roleLabels init ω n)).2.2
      change (roleFreeLabels (roleLabels init ω n) : ℝ) < (n : ℝ) / 10 at hω
      linarith
  calc
    (law init).real {ω |
        (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10}
        ≤ (law init).real (A ∪ B) := measureReal_mono hsub
    _ ≤ (law init).real A + (law init).real B := measureReal_union_le A B
    _ ≤ Real.exp (-(n : ℝ) / 1000) + Real.exp (-(n : ℝ) / 1000) :=
      add_le_add (role_fresh_raw_tail_of_initial init hinit hn)
        (role_fresh_reaction_tail_of_initial init hinit hn n)
    _ = 2 * Real.exp (-(n : ℝ) / 1000) := by ring

theorem role_fresh_reaction_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (T : ℕ) :
    (law init).real {ω |
      n / 8 ≤ roleReactions (roleLabels init ω T) ∧
        (roleBirths (roleLabels init ω T) : ℝ) < (n : ℝ) / 20} ≤
      Real.exp (-(n : ℝ) / 1000) := by
  have hinit := phase0InitialFresh_of_validInitial n init hinput.2.1 hinput.2.2
  have hnlarge := PhaseZeroEntry.phase_zero_population_lower hinput.1
  exact role_fresh_reaction_tail_of_initial init hinit
    ((by norm_num : 200 ≤ 2 ^ 24).trans hnlarge) T

theorem role_fresh_raw_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    (law init).real {ω | roleReactions (roleLabels init ω n) < n / 8} ≤
      Real.exp (-(n : ℝ) / 1000) := by
  have hinit := phase0InitialFresh_of_validInitial n init hinput.2.1 hinput.2.2
  have hnlarge := PhaseZeroEntry.phase_zero_population_lower hinput.1
  exact role_fresh_raw_tail_of_initial init hinit
    ((by norm_num : 200 ≤ 2 ^ 24).trans hnlarge)

theorem role_fresh_pool_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    (law init).real {ω |
      (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10} ≤
      2 * Real.exp (-(n : ℝ) / 1000) := by
  have hinit := phase0InitialFresh_of_validInitial n init hinput.2.1 hinput.2.2
  have hnlarge := PhaseZeroEntry.phase_zero_population_lower hinput.1
  exact role_fresh_pool_tail_of_initial init hinit
    ((by norm_num : 200 ≤ 2 ^ 24).trans hnlarge)


/-! ## Maximal bounds for the existing auxiliary trajectory -/

theorem role_aux_maximal_tail
    (init : Cfg L K) (F : PairRule L K)
    (φ : (Fin init.card → AgentState L K) → ℝ)
    (hφ : ∀ f, 0 ≤ φ f)
    (hstep : ∀ t,
      (law init)[fun ω => φ (auxLabels init F ω (t + 1)) |
          pairLogFiltration L K t] ≤ᵐ[law init]
        (fun ω => φ (auxLabels init F ω t)))
    (T : ℕ) :
    (law init).real {ω | ∃ t ≤ T, 1 ≤ φ (auxLabels init F ω t)} ≤
      φ (initialLabels init) := by
  let Y : ℕ → Ω L K → ℝ := fun t ω => φ (auxLabels init F ω t)
  have hY : Supermartingale Y (pairLogFiltration L K) (law init) :=
    supermartingale_nat
      (fun t => (measurable_aux_potential init F φ t).stronglyMeasurable)
      (integrable_aux_potential init F φ) hstep
  let τ : Ω L K → ℕ∞ := fun ω =>
    (hittingBtwn Y (Set.Ici (1 : ℝ)) 0 T ω : ℕ)
  have hτ : IsStoppingTime (pairLogFiltration L K) τ := by
    exact hY.stronglyAdapted.adapted.isStoppingTime_hittingBtwn
      measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ (T : ℕ∞) := by
    intro ω
    dsimp only [τ]
    exact_mod_cast
      (hittingBtwn_le (u := Y) (s := Set.Ici (1 : ℝ))
        (n := 0) (m := T) ω)
  have hint : Integrable (stoppedValue Y τ) (law init) :=
    integrable_stoppedValue ℕ hτ hY.integrable hbdd
  have hnonneg : ∀ ω, 0 ≤ stoppedValue Y τ ω := by
    intro ω
    exact hφ _
  have hstop :
      (∫ ω, stoppedValue Y τ ω ∂law init) ≤ ∫ ω, Y 0 ω ∂law init := by
    have hneg := hY.neg.expected_stoppedValue_mono
      (isStoppingTime_const (pairLogFiltration L K) 0) hτ
      (fun ω => bot_le) hbdd
    change (∫ ω, -Y 0 ω ∂law init) ≤
      ∫ ω, -stoppedValue Y τ ω ∂law init at hneg
    simpa only [integral_neg, neg_le_neg_iff] using hneg
  have hsubset :
      {ω | ∃ t ≤ T, 1 ≤ φ (auxLabels init F ω t)} ⊆
        {ω | 1 ≤ stoppedValue Y τ ω} := by
    rintro ω ⟨t, ht, hval⟩
    exact stoppedValue_hittingBtwn_mem
      (u := Y) (s := Set.Ici (1 : ℝ)) (n := 0) (m := T)
      ⟨t, ⟨Nat.zero_le t, ht⟩, hval⟩
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ hnonneg) hint (1 : ℝ)
  calc
    (law init).real {ω | ∃ t ≤ T, 1 ≤ φ (auxLabels init F ω t)} ≤
        (law init).real {ω | 1 ≤ stoppedValue Y τ ω} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
    _ ≤ ∫ ω, stoppedValue Y τ ω ∂law init := by
      simpa only [one_mul] using hmarkov
    _ ≤ ∫ ω, Y 0 ω ∂law init := hstop
    _ = φ (initialLabels init) := by
      change (∫ _ω, φ (initialLabels init) ∂law init) = _
      simp

theorem role_aux_ever_tail
    (init : Cfg L K) (F : PairRule L K)
    (φ : (Fin init.card → AgentState L K) → ℝ)
    (hφ : ∀ f, 0 ≤ φ f)
    (hstep : ∀ t,
      (law init)[fun ω => φ (auxLabels init F ω (t + 1)) |
          pairLogFiltration L K t] ≤ᵐ[law init]
        (fun ω => φ (auxLabels init F ω t))) :
    (law init).real {ω | ∃ t, 1 ≤ φ (auxLabels init F ω t)} ≤
      φ (initialLabels init) := by
  let A : ℕ → Set (Ω L K) := fun T =>
    {ω | ∃ t ≤ T, 1 ≤ φ (auxLabels init F ω t)}
  have hmono : Monotone A := by
    intro i j hij ω hω
    rcases hω with ⟨t, ht, hval⟩
    exact ⟨t, ht.trans hij, hval⟩
  have hunion :
      {ω | ∃ t, 1 ≤ φ (auxLabels init F ω t)} = ⋃ T, A T := by
    ext ω
    simp only [A, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, t, le_rfl, ht⟩
    · rintro ⟨T, t, _, ht⟩
      exact ⟨t, ht⟩
  have hbound :
      (law init) {ω | ∃ t, 1 ≤ φ (auxLabels init F ω t)} ≤
        ENNReal.ofReal (φ (initialLabels init)) := by
    rw [hunion, hmono.measure_iUnion]
    refine iSup_le fun T => ?_
    calc
      (law init) (A T) =
          ENNReal.ofReal ((law init).real (A T)) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (φ (initialLabels init)) :=
        ENNReal.ofReal_le_ofReal
          (role_aux_maximal_tail init F φ hφ hstep T)
  have hreal := ENNReal.toReal_mono
    (show ENNReal.ofReal (φ (initialLabels init)) ≠ ∞ by simp) hbound
  simpa only [ENNReal.toReal_ofReal (hφ (initialLabels init))] using hreal


/-! ## The genuine first-J reaction and the two stopped comparisons -/

/-- The genuine first time the top-reaction counter reaches J. -/
def IsFirstRoleReactions (init : Cfg L K) (J : ℕ) (ω : Ω L K) (s : ℕ) : Prop :=
  roleReactions (roleLabels init ω s) = J ∧
    ∀ u < s, roleReactions (roleLabels init ω u) < J

theorem role_reactions_step_bounds
    (init : Cfg L K) (hinit : Phase0InitialFresh n init) (ω : Ω L K) (t : ℕ) :
    roleReactions (roleLabels init ω t) ≤ roleReactions (roleLabels init ω (t + 1)) ∧
      roleReactions (roleLabels init ω (t + 1)) ≤ roleReactions (roleLabels init ω t) + 1 := by
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have hnext : roleLabels init ω (t + 1) = roleLabels init ω t := by
        change auxLabels init (phaseZeroRoleRule L K) ω (t + 1) = _
        rw [auxLabels_succ, hd] <;> rfl
      rw [hnext]
      omega
  | some ij =>
      obtain ⟨i, j⟩ := ij
      have hij := (labelsAt_selected_transition init ω t i j hd).1
      have hf := role_noAssigned_labels init hinit ω t
      have hnext : roleLabels init ω (t + 1) =
          ruleUpdate (phaseZeroRoleRule L K) (roleLabels init ω t) i j := by
        change auxLabels init (phaseZeroRoleRule L K) ω (t + 1) = _
        rw [auxLabels_succ, hd] <;> rfl
      rw [hnext, role_reactions_update _ hf _ _ hij]
      by_cases hb : roleBirthPair (roleLabels init ω t i) (roleLabels init ω t j)
      · have ho := role_birth_not_one _ _ hb
        simp [hb, ho]
      · by_cases ho :
          roleOneSidedPair (roleLabels init ω t i) (roleLabels init ω t j)
        · simp [hb, ho]
        · simp [hb, ho]

theorem role_reactions_mono
    (init : Cfg L K) (hinit : Phase0InitialFresh n init) (ω : Ω L K) :
    Monotone (fun t => roleReactions (roleLabels init ω t)) :=
  monotone_nat_of_le_succ fun t => (role_reactions_step_bounds init hinit ω t).1

theorem role_first_reactions_exists_le
    (init : Cfg L K) (hinit : Phase0InitialFresh n init)
    (J T : ℕ) (hJ : 0 < J) (ω : Ω L K)
    (hT : J ≤ roleReactions (roleLabels init ω T)) :
    ∃ s ≤ T, IsFirstRoleReactions init J ω s := by
  have hex : ∃ s, J ≤ roleReactions (roleLabels init ω s) := ⟨T, hT⟩
  let s := Nat.find hex
  have hs : J ≤ roleReactions (roleLabels init ω s) := Nat.find_spec hex
  have hsT : s ≤ T := Nat.find_min' hex hT
  have hzero : roleReactions (roleLabels init ω 0) = 0 := by
    change roleReactions (auxLabels init (phaseZeroRoleRule L K) ω 0) = 0
    rw [auxLabels_zero_eq_initialLabels]
    exact (role_birth_reaction_initial init hinit.1).2
  have hspos : 0 < s := by
    by_contra h
    have hsnull : s = 0 := by omega
    rw [hsnull, hzero] at hs
    omega
  have hprev : roleReactions (roleLabels init ω (s - 1)) < J :=
    lt_of_not_ge (Nat.find_min hex (show s - 1 < s by omega))
  have hstep := (role_reactions_step_bounds init hinit ω (s - 1)).2
  have hsuc : s - 1 + 1 = s := by omega
  rw [hsuc] at hstep
  refine ⟨s, hsT, ?_, ?_⟩
  · omega
  · intro u hu
    exact lt_of_not_ge (Nat.find_min hex hu)

/-- First-J bad-event comparison over the entire trajectory. -/
theorem role_fresh_first_reactions_tail_of_initial
    (init : Cfg L K) (hinit : Phase0InitialFresh n init) (hn : 200 ≤ n) :
    (law init).real {ω | ∃ s,
      IsFirstRoleReactions init (n / 8) ω s ∧
        (roleBirths (roleLabels init ω s) : ℝ) < (n : ℝ) / 20} ≤
      Real.exp (-(n : ℝ) / 1000) := by
  let φ : (Fin init.card → AgentState L K) → ℝ := fun f =>
    roleReactionPotential n (n / 8) (roleReactions f) (roleBirths f)
  have htail := role_aux_ever_tail init (phaseZeroRoleRule L K) φ
    (fun f => role_reaction_potential_nonneg _ _ _ _)
    (fun t => role_reaction_potential_drift init hinit (by omega) t)
  have hsub : {ω | ∃ s,
      IsFirstRoleReactions init (n / 8) ω s ∧
        (roleBirths (roleLabels init ω s) : ℝ) < (n : ℝ) / 20} ⊆
      {ω | ∃ s, 1 ≤ φ (auxLabels init (phaseZeroRoleRule L K) ω s)} := by
    rintro ω ⟨s, hfirst, hsmall⟩
    exact ⟨s, role_reaction_potential_detects _ _ _ _ hfirst.1.ge hsmall⟩
  obtain ⟨hb, hr⟩ := role_birth_reaction_initial init hinit.1
  calc
    (law init).real {ω | ∃ s,
        IsFirstRoleReactions init (n / 8) ω s ∧
          (roleBirths (roleLabels init ω s) : ℝ) < (n : ℝ) / 20}
        ≤ (law init).real
          {ω | ∃ s, 1 ≤ φ (auxLabels init (phaseZeroRoleRule L K) ω s)} :=
      measureReal_mono hsub
    _ ≤ φ (initialLabels init) := htail
    _ = Real.exp ((n : ℝ) / 20 * Real.log (3 / 2 : ℝ) -
        ((n / 8 : ℕ) : ℝ) * Real.log (6 / 5 : ℝ)) := by
      simp [φ, roleReactionPotential, hb, hr]
    _ ≤ Real.exp (-(n : ℝ) / 1000) :=
      Real.exp_le_exp.mpr (role_reaction_exponent_le hn)

/-- Literal raw-time comparison: no first-J reaction by time n. -/
theorem role_fresh_raw_stopped_tail_of_initial
    (init : Cfg L K) (hinit : Phase0InitialFresh n init) (hn : 200 ≤ n) :
    (law init).real {ω | ¬ ∃ s ≤ n,
      IsFirstRoleReactions init (n / 8) ω s} ≤
      Real.exp (-(n : ℝ) / 1000) := by
  have hsub : {ω | ¬ ∃ s ≤ n, IsFirstRoleReactions init (n / 8) ω s} ⊆
      {ω | roleReactions (roleLabels init ω n) < n / 8} := by
    intro ω hω
    by_contra h
    exact hω (role_first_reactions_exists_le init hinit (n / 8) n
      (by omega) ω (le_of_not_gt h))
  exact (measureReal_mono hsub).trans (role_fresh_raw_tail_of_initial init hinit hn)

theorem role_fresh_first_reactions_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    (law init).real {ω | ∃ s,
      IsFirstRoleReactions init (n / 8) ω s ∧
        (roleBirths (roleLabels init ω s) : ℝ) < (n : ℝ) / 20} ≤
      Real.exp (-(n : ℝ) / 1000) := by
  have hinit := phase0InitialFresh_of_validInitial n init hinput.2.1 hinput.2.2
  have hnlarge := PhaseZeroEntry.phase_zero_population_lower hinput.1
  exact role_fresh_first_reactions_tail_of_initial init hinit
    ((by norm_num : 200 ≤ 2 ^ 24).trans hnlarge)

theorem role_fresh_raw_stopped_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    (law init).real {ω | ¬ ∃ s ≤ n,
      IsFirstRoleReactions init (n / 8) ω s} ≤
      Real.exp (-(n : ℝ) / 1000) := by
  have hinit := phase0InitialFresh_of_validInitial n init hinput.2.1 hinput.2.2
  have hnlarge := PhaseZeroEntry.phase_zero_population_lower hinput.1
  exact role_fresh_raw_stopped_tail_of_initial init hinit
    ((by norm_num : 200 ≤ 2 ^ 24).trans hnlarge)

/-- Fresh-pool estimate assembled from both genuine stopped comparisons. -/
theorem role_fresh_pool_tail_stopped {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    (law init).real {ω |
      (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10} ≤
      2 * Real.exp (-(n : ℝ) / 1000) := by
  have hinit := phase0InitialFresh_of_validInitial n init hinput.2.1 hinput.2.2
  let A : Set (InputLog n) := {ω | ¬ ∃ s ≤ n,
    IsFirstRoleReactions init (n / 8) ω s}
  let B : Set (InputLog n) := {ω | ∃ s,
    IsFirstRoleReactions init (n / 8) ω s ∧
      (roleBirths (roleLabels init ω s) : ℝ) < (n : ℝ) / 20}
  have hsub : {ω |
      (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10} ⊆ A ∪ B := by
    intro ω hω
    by_cases hhit : ∃ s ≤ n, IsFirstRoleReactions init (n / 8) ω s
    · obtain ⟨s, hs, hfirst⟩ := hhit
      right
      refine ⟨s, hfirst, ?_⟩
      have hmono :
          (freeTargetCount (roleCfg init ω s) : ℝ) ≤
            (freeTargetCount (roleCfg init ω n) : ℝ) := by
        exact_mod_cast (role_freeTarget_mono init hinit ω hs)
      have hbirth :
          (2 : ℝ) * (roleBirths (roleLabels init ω s) : ℝ) ≤
            (freeTargetCount (roleCfg init ω s) : ℝ) := by
        exact_mod_cast (role_birth_reaction_balance (roleLabels init ω s)).2.2
      change (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10 at hω
      linarith only [hω, hmono, hbirth]
    · exact Or.inl hhit
  calc
    (law init).real {ω |
        (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10}
        ≤ (law init).real (A ∪ B) := measureReal_mono hsub
    _ ≤ (law init).real A + (law init).real B := measureReal_union_le A B
    _ ≤ Real.exp (-(n : ℝ) / 1000) + Real.exp (-(n : ℝ) / 1000) :=
      add_le_add (role_fresh_raw_stopped_tail init hinput)
        (role_fresh_first_reactions_tail init hinput)
    _ = 2 * Real.exp (-(n : ℝ) / 1000) := by ring


/-! ## Exact conditional rectangles and multiplicative MCR drift -/

theorem role_one_sided_conditional_probability
    (init : Cfg L K) (hc : 2 ≤ init.card) (t : ℕ) :
    (law init)[role_aux_pair_indicator init (phaseZeroRoleRule L K)
        (fun g i j => roleOneSidedPair (g i) (g j)) t |
        pairLogFiltration L K t] =ᵐ[law init]
      fun ω =>
        (2 * (roleMcrLabels (roleLabels init ω t) : ℝ) *
            (roleFreeLabels (roleLabels init ω t) : ℝ)) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  simpa only [roleLabels, role_one_sided_goodPairs_card,
    Nat.cast_mul, Nat.cast_ofNat] using
    (role_aux_pair_condExp init hc (phaseZeroRoleRule L K)
      (fun g i j => roleOneSidedPair (g i) (g j)) t)

theorem role_birth_conditional_probability
    (init : Cfg L K) (hc : 2 ≤ init.card) (t : ℕ) :
    (law init)[role_aux_pair_indicator init (phaseZeroRoleRule L K)
        (fun g i j => roleBirthPair (g i) (g j)) t |
        pairLogFiltration L K t] =ᵐ[law init]
      fun ω =>
        ((roleMcrLabels (roleLabels init ω t) *
            (roleMcrLabels (roleLabels init ω t) - 1) : ℕ) : ℝ) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  simpa only [roleLabels, role_birth_goodPairs_card] using
    (role_aux_pair_condExp init hc (phaseZeroRoleRule L K)
      (fun g i j => roleBirthPair (g i) (g j)) t)

theorem role_mcr_step_accounting (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    (roleMcrLabels (roleLabels init ω (t + 1)) : ℝ) +
      2 * role_aux_pair_indicator init (phaseZeroRoleRule L K)
        (fun g i j => roleBirthPair (g i) (g j)) t ω +
      role_aux_pair_indicator init (phaseZeroRoleRule L K)
        (fun g i j => roleOneSidedPair (g i) (g j)) t ω =
      (roleMcrLabels (roleLabels init ω t) : ℝ) := by
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have hstate : roleLabels init ω (t + 1) = roleLabels init ω t := by
        change auxLabels init (phaseZeroRoleRule L K) ω (t + 1) = _
        simp only [auxLabels_succ, hd, auxStep, roleLabels]
      rw [hstate]
      simp [role_aux_pair_indicator, hd]
  | some ij =>
      obtain ⟨i, j⟩ := ij
      have hij := (labelsAt_selected_transition init ω t i j hd).1
      have hstate : roleLabels init ω (t + 1) =
          ruleUpdate (phaseZeroRoleRule L K) (roleLabels init ω t) i j := by
        change auxLabels init (phaseZeroRoleRule L K) ω (t + 1) = _
        simp only [auxLabels_succ, hd, auxStep, roleLabels]
      have hb :
          role_aux_pair_indicator init (phaseZeroRoleRule L K)
            (fun g i j => roleBirthPair (g i) (g j)) t ω =
          (if roleBirthPair (roleLabels init ω t i) (roleLabels init ω t j)
            then (1 : ℝ) else 0) := by
        simp [role_aux_pair_indicator, hd, roleLabels]
      have ho :
          role_aux_pair_indicator init (phaseZeroRoleRule L K)
            (fun g i j => roleOneSidedPair (g i) (g j)) t ω =
          (if roleOneSidedPair (roleLabels init ω t i) (roleLabels init ω t j)
            then (1 : ℝ) else 0) := by
        simp [role_aux_pair_indicator, hd, roleLabels]
      have hupdate := role_mcr_update (roleLabels init ω t) i j hij
      rw [hstate, hb, ho]
      by_cases hbirth :
          roleBirthPair (roleLabels init ω t i) (roleLabels init ω t j) <;>
        by_cases hone :
          roleOneSidedPair (roleLabels init ω t i) (roleLabels init ω t j) <;>
        simp only [hbirth, hone, if_true, if_false] at hupdate ⊢ <;>
        exact_mod_cast hupdate

theorem role_mcr_conditional_decrease
    (init : Cfg L K) (hc : 2 ≤ init.card) (t : ℕ) :
    (law init)[fun ω => (roleMcrLabels (roleLabels init ω (t + 1)) : ℝ) |
        pairLogFiltration L K t] ≤ᵐ[law init]
      fun ω =>
        (roleMcrLabels (roleLabels init ω t) : ℝ) -
          2 * (((roleMcrLabels (roleLabels init ω t) *
              (roleMcrLabels (roleLabels init ω t) - 1) : ℕ) : ℝ) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1))) -
          (2 * (roleMcrLabels (roleLabels init ω t) : ℝ) *
              (roleFreeLabels (roleLabels init ω t) : ℝ)) /
            ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have h := role_aux_two_event_condExp_le init hc (phaseZeroRoleRule L K)
    (fun g i j => roleBirthPair (g i) (g j))
    (fun g i j => roleOneSidedPair (g i) (g j))
    (fun g => (roleMcrLabels g : ℝ)) (fun _ => -2) (fun _ => -1)
    (fun t ω => by
      have hstep := role_mcr_step_accounting init ω t
      dsimp only [roleLabels] at hstep ⊢
      linarith only [hstep])
    t
  filter_upwards [h] with ω hω
  rw [role_birth_goodPairs_card, role_one_sided_goodPairs_card] at hω
  simpa only [roleLabels, Nat.cast_mul, Nat.cast_ofNat,
    neg_mul, one_mul, sub_eq_add_neg] using hω

theorem role_one_sided_rate_floor {n U F : ℕ}
    (hn : 2 ≤ n) (hF : (n : ℝ) / 10 ≤ (F : ℝ)) :
    (U : ℝ) / (5 * (n : ℝ)) ≤
      (2 * (U : ℝ) * (F : ℝ)) /
        ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    nlinarith
  have hcore : (n : ℝ) - 1 ≤ 10 * (F : ℝ) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcore
    (mul_nonneg (Nat.cast_nonneg U : (0 : ℝ) ≤ U) hnpos.le)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (n : ℝ)) hden).2
  nlinarith only [hscaled]

theorem role_mcr_conditional_drift
    (init : Cfg L K) (hc : 2 ≤ init.card) (t : ℕ) :
    ∀ᵐ ω ∂law init,
      (init.card : ℝ) / 10 ≤ (roleFreeLabels (roleLabels init ω t) : ℝ) →
      ((law init)[fun ω =>
        (roleMcrLabels (roleLabels init ω (t + 1)) : ℝ) |
        pairLogFiltration L K t]) ω ≤
      (1 - 1 / (5 * (init.card : ℝ))) *
        (roleMcrLabels (roleLabels init ω t) : ℝ) := by
  have hnR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hden : (0 : ℝ) < (init.card : ℝ) * ((init.card : ℝ) - 1) := by
    nlinarith
  filter_upwards [role_mcr_conditional_decrease init hc t] with ω hω hF
  have hfloor := role_one_sided_rate_floor
    (U := roleMcrLabels (roleLabels init ω t)) hc hF
  have hdiag : 0 ≤
      (((roleMcrLabels (roleLabels init ω t) *
          (roleMcrLabels (roleLabels init ω t) - 1) : ℕ) : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1))) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hid :
      (roleMcrLabels (roleLabels init ω t) : ℝ) -
        (roleMcrLabels (roleLabels init ω t) : ℝ) /
          (5 * (init.card : ℝ)) =
      (1 - 1 / (5 * (init.card : ℝ))) *
        (roleMcrLabels (roleLabels init ω t) : ℝ) := by ring
  rw [← hid]
  linarith


/-! ## A frozen past event and a shifted integral recursion -/

theorem aux_past_event_drift_expectation_le
    (init : Cfg L K) (F : PairRule L K)
    (φ : (Fin init.card → AgentState L K) → ℝ)
    (s : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    {c : ℝ} (hc : c ≤ 1)
    (hdrift : ∀ t, ∀ᵐ ω ∂law init, ω ∈ E →
      ((law init)[fun ω => φ (auxLabels init F ω (s + (t + 1))) |
          pairLogFiltration L K (s + t)]) ω ≤
        (1 - c) * φ (auxLabels init F ω (s + t)))
    (k : ℕ) :
    (∫ ω, E.indicator
        (fun ω => φ (auxLabels init F ω (s + k))) ω ∂law init) ≤
      (1 - c) ^ k *
        ∫ ω, E.indicator
          (fun ω => φ (auxLabels init F ω s)) ω ∂law init := by
  let Y : ℕ → Ω L K → ℝ := fun t =>
    E.indicator (fun ω => φ (auxLabels init F ω (s + t)))
  let B : Ω L K → ℝ := fun ω => if ω ∈ E then 1 else 0
  have hEambient : MeasurableSet E :=
    ((pairLogFiltration L K).le s) E hE
  have hYint (t : ℕ) : Integrable (Y t) (law init) :=
    (integrable_aux_potential init F φ (s + t)).indicator hEambient
  have hYeq (t : ℕ) :
      Y t = B * (fun ω => φ (auxLabels init F ω (s + t))) := by
    funext ω
    by_cases hω : ω ∈ E <;>
      simp [Y, B, Set.indicator, hω, Pi.mul_apply]
  have hstep (t : ℕ) :
      (∫ ω, Y (t + 1) ω ∂law init) ≤
        (1 - c) * ∫ ω, Y t ω ∂law init := by
    have hEt : MeasurableSet[pairLogFiltration L K (s + t)] E :=
      ((pairLogFiltration L K).mono (Nat.le_add_right s t)) E hE
    have hBsm : StronglyMeasurable[pairLogFiltration L K (s + t)] B :=
      (Measurable.ite hEt measurable_const measurable_const).stronglyMeasurable
    have hproduct :
        Integrable
          (B * (fun ω => φ (auxLabels init F ω (s + (t + 1)))))
          (law init) := by
      rw [← hYeq (t + 1)]
      exact hYint (t + 1)
    have hpull := condExp_mul_of_stronglyMeasurable_left hBsm hproduct
      (integrable_aux_potential init F φ (s + (t + 1)))
    have hce :
        (law init)[Y (t + 1) | pairLogFiltration L K (s + t)] =ᵐ[law init]
          B * (law init)[fun ω =>
            φ (auxLabels init F ω (s + (t + 1))) |
              pairLogFiltration L K (s + t)] := by
      rw [hYeq (t + 1)]
      exact hpull
    have hweighted :
        (law init)[Y (t + 1) | pairLogFiltration L K (s + t)] ≤ᵐ[law init]
          fun ω => (1 - c) * Y t ω := by
      filter_upwards [hce, hdrift t] with ω hceω hd
      rw [hceω]
      by_cases hω : ω ∈ E
      · simpa only [Pi.mul_apply, B, if_pos hω, one_mul,
          Y, Set.indicator_of_mem hω] using hd hω
      · simp only [Pi.mul_apply, B, if_neg hω, zero_mul,
          Y, Set.indicator_of_notMem hω, mul_zero, le_refl]
    calc
      (∫ ω, Y (t + 1) ω ∂law init) =
          ∫ ω, ((law init)[Y (t + 1) |
            pairLogFiltration L K (s + t)]) ω ∂law init :=
        (integral_condExp ((pairLogFiltration L K).le (s + t))).symm
      _ ≤ ∫ ω, (1 - c) * Y t ω ∂law init :=
        integral_mono_ae integrable_condExp ((hYint t).const_mul _) hweighted
      _ = (1 - c) * ∫ ω, Y t ω ∂law init := integral_const_mul _ _
  have hc0 : 0 ≤ 1 - c := by linarith
  have hiter (t : ℕ) :
      (∫ ω, Y t ω ∂law init) ≤
        (1 - c) ^ t * ∫ ω, Y 0 ω ∂law init := by
    induction t with
    | zero => simp
    | succ t ih =>
        calc
          (∫ ω, Y (t + 1) ω ∂law init) ≤
              (1 - c) * ∫ ω, Y t ω ∂law init := hstep t
          _ ≤ (1 - c) * ((1 - c) ^ t * ∫ ω, Y 0 ω ∂law init) :=
            mul_le_mul_of_nonneg_left ih hc0
          _ = (1 - c) ^ (t + 1) * ∫ ω, Y 0 ω ∂law init := by ring
  simpa only [Y, Nat.add_zero] using hiter k

theorem aux_past_event_drift_tail_le
    (init : Cfg L K) (F : PairRule L K)
    (φ : (Fin init.card → AgentState L K) → ℝ)
    (hφ : ∀ f, 0 ≤ φ f)
    (s : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    {c : ℝ} (hc : c ≤ 1)
    (hdrift : ∀ t, ∀ᵐ ω ∂law init, ω ∈ E →
      ((law init)[fun ω => φ (auxLabels init F ω (s + (t + 1))) |
          pairLogFiltration L K (s + t)]) ω ≤
        (1 - c) * φ (auxLabels init F ω (s + t)))
    (k : ℕ) :
    (law init).real {ω | ω ∈ E ∧ 1 ≤ φ (auxLabels init F ω (s + k))} ≤
      (1 - c) ^ k *
        ∫ ω, E.indicator
          (fun ω => φ (auxLabels init F ω s)) ω ∂law init := by
  have hEambient : MeasurableSet E :=
    ((pairLogFiltration L K).le s) E hE
  let Y : Ω L K → ℝ :=
    E.indicator (fun ω => φ (auxLabels init F ω (s + k)))
  have hYnonneg : ∀ ω, 0 ≤ Y ω := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa only [Y, Set.indicator_of_mem hω] using
        hφ (auxLabels init F ω (s + k))
    · simp only [Y, Set.indicator_of_notMem hω, le_refl]
  have hYint : Integrable Y (law init) :=
    (integrable_aux_potential init F φ (s + k)).indicator hEambient
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ hYnonneg) hYint 1
  rw [one_mul] at hmarkov
  have hevent : {ω | 1 ≤ Y ω} =
      {ω | ω ∈ E ∧ 1 ≤ φ (auxLabels init F ω (s + k))} := by
    ext ω
    by_cases hω : ω ∈ E <;>
      simp [Y, hω]
  rw [hevent] at hmarkov
  exact hmarkov.trans
    (aux_past_event_drift_expectation_le init F φ s E hE hc hdrift k)

/-! ## The joint last-MCR tail from the genuine input -/

theorem role_mcr_joint_geometric_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (k : ℕ) :
    (law init).real
        {ω | 0 < roleMcrLabels (roleLabels init ω (n + k)) ∧
          (n : ℝ) / 10 ≤ (roleFreeLabels (roleLabels init ω n) : ℝ)} ≤
      (1 - 1 / (5 * (n : ℝ))) ^ k * (n : ℝ) := by
  rcases hinput with ⟨hpop, hvalid, hcard⟩
  have hnlarge := (time_population_bounds hpop).2
  clear hpop
  have hn : 2 ≤ n := le_trans (by decide : 2 ≤ 40) hnlarge
  have hc : 2 ≤ init.card := by simpa only [hcard] using hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hcle : 1 / (5 * (n : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < 5 * (n : ℝ))).2
    linarith
  have hc0 : 0 ≤ 1 - 1 / (5 * (n : ℝ)) := sub_nonneg.mpr hcle
  have hinit := phase0InitialFresh_of_validInitial n init hvalid hcard
  let E : Set (InputLog n) :=
    {ω | (n : ℝ) / 10 ≤ (roleFreeLabels (roleLabels init ω n) : ℝ)}
  let φ :
      (Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) → ℝ :=
    fun f => (roleMcrLabels f : ℝ)
  have hE : MeasurableSet[
      pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 n] E := by
    exact measurableSet_le measurable_const
      (measurable_aux_potential init (phaseZeroRoleRule _ _)
        (fun f => (roleFreeLabels f : ℝ)) n)
  have hEambient : MeasurableSet E :=
    ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le n) E hE
  have hdrift (t : ℕ) :
      ∀ᵐ ω ∂law init, ω ∈ E →
        ((law init)[fun ω =>
          φ (auxLabels init (phaseZeroRoleRule _ _) ω (n + (t + 1))) |
          pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 (n + t)]) ω ≤
        (1 - 1 / (5 * (n : ℝ))) *
          φ (auxLabels init (phaseZeroRoleRule _ _) ω (n + t)) := by
    filter_upwards [role_mcr_conditional_drift init hc (n + t)] with ω hω hEω
    have hstart :
        (n : ℝ) / 10 ≤ (roleFreeLabels (roleLabels init ω n) : ℝ) := hEω
    have hmono := role_freeTarget_mono init hinit ω (Nat.le_add_right n t)
    change roleFreeLabels (roleLabels init ω n) ≤
      roleFreeLabels (roleLabels init ω (n + t)) at hmono
    have hcurrent :
        (n : ℝ) / 10 ≤
          (roleFreeLabels (roleLabels init ω (n + t)) : ℝ) :=
      hstart.trans (by exact_mod_cast hmono)
    have hlocal := hω (by simpa only [hcard] using hcurrent)
    simpa only [φ, roleLabels, hcard, Nat.add_assoc] using hlocal
  have htail := aux_past_event_drift_tail_le init (phaseZeroRoleRule _ _) φ
    (fun f => Nat.cast_nonneg (roleMcrLabels f)) n E hE hcle hdrift k
  have hintegrable :
      Integrable
        (E.indicator (fun ω => φ (auxLabels init (phaseZeroRoleRule _ _) ω n)))
        (law init) :=
    (integrable_aux_potential init (phaseZeroRoleRule _ _) φ n).indicator hEambient
  have hinitial :
      (∫ ω, E.indicator
        (fun ω => φ (auxLabels init (phaseZeroRoleRule _ _) ω n)) ω ∂law init) ≤
        (n : ℝ) := by
    calc
      (∫ ω, E.indicator
          (fun ω => φ (auxLabels init (phaseZeroRoleRule _ _) ω n)) ω ∂law init) ≤
          ∫ _ω : InputLog n, (n : ℝ) ∂law init := by
        apply integral_mono_ae hintegrable (integrable_const _)
        exact ae_of_all _ fun ω => by
          by_cases hω : ω ∈ E
          · rw [Set.indicator_of_mem hω]
            dsimp only [φ]
            exact_mod_cast
              (show roleMcrLabels (auxLabels init (phaseZeroRoleRule _ _) ω n) ≤ n by
                simpa only [hcard] using
                  roleMcrLabels_le (auxLabels init (phaseZeroRoleRule _ _) ω n))
          · rw [Set.indicator_of_notMem hω]
            exact Nat.cast_nonneg n
      _ = (n : ℝ) := by simp
  have hevent :
      {ω : InputLog n | ω ∈ E ∧
          1 ≤ φ (auxLabels init (phaseZeroRoleRule _ _) ω (n + k))} =
      {ω | 0 < roleMcrLabels (roleLabels init ω (n + k)) ∧
          (n : ℝ) / 10 ≤ (roleFreeLabels (roleLabels init ω n) : ℝ)} := by
    ext ω
    constructor
    · rintro ⟨hEω, hU⟩
      refine ⟨?_, hEω⟩
      change (1 : ℝ) ≤ (roleMcrLabels (roleLabels init ω (n + k)) : ℝ) at hU
      have hnat : 1 ≤ roleMcrLabels (roleLabels init ω (n + k)) := by
        exact_mod_cast hU
      omega
    · rintro ⟨hU, hEω⟩
      refine ⟨hEω, ?_⟩
      change (1 : ℝ) ≤ (roleMcrLabels (roleLabels init ω (n + k)) : ℝ)
      exact_mod_cast (Nat.succ_le_iff.mpr hU)
  rw [hevent] at htail
  exact htail.trans (mul_le_mul_of_nonneg_left hinitial (pow_nonneg hc0 k))

theorem role_mcr_joint_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    (law init).real
        {ω | 0 < roleMcrLabels (roleLabels init ω (n + logWindow n 20)) ∧
          (n : ℝ) / 10 ≤ (roleFreeLabels (roleLabels init ω n) : ℝ)} ≤
      1 / (n : ℝ) ^ 3 := by
  have hn : 1 ≤ n :=
    le_trans (by decide : 1 ≤ 40) (time_population_bounds hinput.1).2
  exact (role_mcr_joint_geometric_tail init hinput (logWindow n 20)).trans
    (role_mcr_window_scalar hn)


/-! ## Event transfer to the actual protocol, under the original law -/

/-- The actual trace has not left Phase 0 before the displayed horizon. -/
def rolePhaseZeroPrefix (init : Cfg L K) (T : ℕ) (ω : Ω L K) : Prop :=
  ∀ t < T, Phase0Window.allPhase0 (trace init ω t)

theorem phaseZeroRegion_iff_allPhaseZero (f : Fin n → AgentState L K) :
    phaseZeroRegion f ↔ Phase0Window.allPhase0 (labelCfg f) := by
  constructor
  · intro hf a ha
    change a ∈ Finset.univ.val.map f at ha
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ha
    exact Fin.ext (hf i)
  · exact phaseZeroRegion_of_allPhaseZero f

theorem role_cfg_event_eq_actual_event (init : Cfg L K) (T : ℕ)
    (P : ((t : Finset.Iic T) → Cfg L K) → Prop) :
    {ω | rolePhaseZeroPrefix init T ω ∧
        P (fun t => roleCfg init ω t.val)} =
      {ω | rolePhaseZeroPrefix init T ω ∧
        P (fun t => trace init ω t.val)} := by
  have hcfg (ω : Ω L K) (s : ℕ) :
      labelCfg (labelsAt init ω s) = trace init ω s :=
    labelsAt_config init ω s
  have h := role_event_eq_actual_event init T
    (fun f => P (fun t => labelCfg (f t)))
  simpa only [rolePhaseZeroPrefix, roleCfg,
    phaseZeroRegion_iff_allPhaseZero, hcfg] using h

theorem role_cfg_two_endpoint_event_eq_actual_event
    (init : Cfg L K) (a T : ℕ) (ha : a ≤ T)
    (P : Cfg L K → Cfg L K → Prop) :
    {ω | rolePhaseZeroPrefix init T ω ∧
        P (roleCfg init ω a) (roleCfg init ω T)} =
      {ω | rolePhaseZeroPrefix init T ω ∧
        P (trace init ω a) (trace init ω T)} := by
  exact role_cfg_event_eq_actual_event init T
    (fun f => P (f ⟨a, Finset.mem_Iic.mpr ha⟩)
      (f ⟨T, Finset.mem_Iic.mpr le_rfl⟩))

theorem rolePhaseZeroPrefix_of_first_seed (init : Cfg L K)
    (ω : Ω L K) (T S : ℕ) (hTS : T ≤ S)
    (hseed : firstPhaseSeed init 1 S ω) :
    rolePhaseZeroPrefix init T ω := by
  intro t ht
  exact phaseZero_allPhaseZero_before_seed init ω S hseed t (ht.trans_le hTS)

/-- The fresh-pool failure on the actual no-exit prefix is a joint event. -/
theorem role_fresh_pool_actual_tail {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    (law init).real
      {ω | rolePhaseZeroPrefix init n ω ∧
        (freeTargetCount (trace init ω n) : ℝ) < (n : ℝ) / 10} ≤
      2 * Real.exp (-(n : ℝ) / 1000) := by
  have hevent := role_cfg_two_endpoint_event_eq_actual_event init n n le_rfl
    (fun _ c => (freeTargetCount c : ℝ) < (n : ℝ) / 10)
  rw [← hevent]
  exact (measureReal_mono (μ := law init)
    (fun ω hω => hω.2)).trans (role_fresh_pool_tail_stopped init hinput)

/-- The late survival bound, intersected with the already observed fresh pool
and the actual Phase-0 prefix. No law is conditioned on either event. -/
theorem role_mcr_joint_actual_tail {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    (law init).real
      {ω | rolePhaseZeroPrefix init (n + logWindow n 20) ω ∧
        0 < roleMCRCount (trace init ω (n + logWindow n 20)) ∧
        (n : ℝ) / 10 ≤ (freeTargetCount (trace init ω n) : ℝ)} ≤
      1 / (n : ℝ) ^ 3 := by
  have hevent := role_cfg_two_endpoint_event_eq_actual_event init n
    (n + logWindow n 20) (Nat.le_add_right _ _)
    (fun first last =>
      0 < roleMCRCount last ∧ (n : ℝ) / 10 ≤ (freeTargetCount first : ℝ))
  rw [← hevent]
  have htail := role_mcr_joint_tail init hinput
  exact (measureReal_mono (μ := law init)
    (fun ω hω => hω.2)).trans htail

private theorem role_measure_le_of_real_le (init : Cfg L K)
    (S : Set (Ω L K)) {b : ℝ} (h : (law init).real S ≤ b) :
    law init S ≤ ENNReal.ofReal b := by
  calc
    law init S = ENNReal.ofReal ((law init).real S) :=
      (ENNReal.ofReal_toReal (measure_ne_top (law init) S)).symm
    _ ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal h

theorem role_fresh_first_reactions_tail_ennreal {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω | ∃ s,
      IsFirstRoleReactions init (n / 8) ω s ∧
        (roleBirths (roleLabels init ω s) : ℝ) < (n : ℝ) / 20} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) :=
  role_measure_le_of_real_le init _ (role_fresh_first_reactions_tail init hinput)

theorem role_fresh_raw_stopped_tail_ennreal {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω | ¬ ∃ s ≤ n,
      IsFirstRoleReactions init (n / 8) ω s} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) :=
  role_measure_le_of_real_le init _ (role_fresh_raw_stopped_tail init hinput)

theorem role_fresh_reaction_tail_ennreal {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) (T : ℕ) :
    law init
      {ω | n / 8 ≤ roleReactions (roleLabels init ω T) ∧
        (roleBirths (roleLabels init ω T) : ℝ) < (n : ℝ) / 20} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) :=
  role_measure_le_of_real_le init _ (role_fresh_reaction_tail init hinput T)

theorem role_fresh_raw_tail_ennreal {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω | roleReactions (roleLabels init ω n) < n / 8} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) :=
  role_measure_le_of_real_le init _ (role_fresh_raw_tail init hinput)

theorem role_fresh_pool_tail_ennreal {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init
      {ω | (freeTargetCount (roleCfg init ω n) : ℝ) < (n : ℝ) / 10} ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) / 1000)) :=
  role_measure_le_of_real_le init _ (role_fresh_pool_tail_stopped init hinput)

theorem role_mcr_joint_tail_ennreal {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init
      {ω | 0 < roleMcrLabels (roleLabels init ω (n + logWindow n 20)) ∧
        (n : ℝ) / 10 ≤ (roleFreeLabels (roleLabels init ω n) : ℝ)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) :=
  role_measure_le_of_real_le init _ (role_mcr_joint_tail init hinput)

theorem role_fresh_pool_actual_tail_ennreal {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init
      {ω | rolePhaseZeroPrefix init n ω ∧
        (freeTargetCount (trace init ω n) : ℝ) < (n : ℝ) / 10} ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) / 1000)) :=
  role_measure_le_of_real_le init _ (role_fresh_pool_actual_tail init hinput)

theorem role_mcr_joint_actual_tail_ennreal {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init
      {ω | rolePhaseZeroPrefix init (n + logWindow n 20) ω ∧
        0 < roleMCRCount (trace init ω (n + logWindow n 20)) ∧
        (n : ℝ) / 10 ≤ (freeTargetCount (trace init ω n) : ℝ)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) :=
  role_measure_le_of_real_le init _ (role_mcr_joint_actual_tail init hinput)

end Ripple.PopulationProtocol.ExactMajority.PhaseZeroRoles

end
