import Ripple.sCRNUniversality.ClockedCTM.UnboundedError
import Ripple.sCRNUniversality.Stochastic.MassAction.Completion

/-!
Raw-law window analysis for FIX3-SCWB-T41.

The original declarations are retained. The final sections identify actual
work-entry flux and clock-neighbor inflows. The added total-mass identities
use those actual occupations, not an assumed balance law. The final
comparison with the standalone work-chain marginals and the one-window
probability headline are not asserted here.
-/

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction
open MeasureTheory
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace WindowAnalysis

open ProbabilityTheory Preorder

open Classical in
/-- The reaction actually used by the sanitized jump semantics. -/
noncomputable def windowLabel (C : XCTM Q)
    (z : State (Sp C)) (o : Option (Rx C)) : Option (Rx C) :=
  if hT : (net C).Terminal z then none
  else some (fireOptionSanitized (net C) z o hT)

theorem windowLabel_of_enabled (C : XCTM Q)
    (z : State (Sp C)) (r : Rx C) (he : (rxn C r).enabled z) :
    windowLabel C z (some r) = some r := by
  have hNT : ¬ (net C).Terminal z := fun hT => hT r he
  simp only [windowLabel, dif_neg hNT]
  exact congrArg (fun q : Rx C => some q)
    (fireOptionSanitized_of_enabled (net C) z r hNT he)

noncomputable def windowIncrement (C : XCTM Q)
    (z : State (Sp C)) (o : Option (Rx C)) : ℕ :=
  match windowLabel C z o with
  | none => 0
  | some r => if isClock r = false then 1 else 0

noncomputable def windowTick (C : XCTM Q)
    (z : State (Sp C)) (o : Option (Rx C)) : Bool :=
  match windowLabel C z o with
  | none => false
  | some r => isTick r

private theorem windowLabel_eq_pathFired (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) :
    windowLabel C (pathState (net C) z₀ ω n) (ω (n + 1)) =
      pathFired (net C) z₀ ω n := by
  classical
  by_cases hT : (net C).Terminal (pathState (net C) z₀ ω n)
  · simp only [windowLabel, pathFired, dif_pos hT] <;> rfl
  · simp only [windowLabel, pathFired, dif_neg hT] <;> rfl

private theorem windowTick_eq_firedTick (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) :
    windowTick C (pathState (net C) z₀ ω n) (ω (n + 1)) =
      firedTick C z₀ ω n := by
  unfold windowTick firedTick
  rw [windowLabel_eq_pathFired C z₀ n ω]
  cases pathFired (net C) z₀ ω n <;> rfl

theorem windowIncrement_le_one (C : XCTM Q)
    (z : State (Sp C)) (o : Option (Rx C)) :
    windowIncrement C z o ≤ 1 := by
  unfold windowIncrement
  split
  · omega
  · split_ifs <;> omega

theorem windowIncrement_of_work (C : XCTM Q)
    (z : State (Sp C)) (r : Rx C)
    (hr : isClock r = false) (he : (rxn C r).enabled z) :
    windowIncrement C z (some r) = 1 := by
  simp [windowIncrement, windowLabel_of_enabled C z r he, hr]

noncomputable def windowUpdate (C : XCTM Q)
    (a : ℕ × Bool) (z : State (Sp C)) (o : Option (Rx C)) :
    ℕ × Bool :=
  (a.1 + windowIncrement C z o, a.2 && !(windowTick C z o))

noncomputable def windowLaw (C : XCTM Q) (z₀ : State (Sp C)) :
    Measure (LabelPath C) :=
  rawLaw (net C) (net_hasPositiveRates C) z₀

instance windowLaw_isProbability (C : XCTM Q) (z₀ : State (Sp C)) :
    IsProbabilityMeasure (windowLaw C z₀) :=
  rawLaw_isProbabilityMeasure (net C) (net_hasPositiveRates C) z₀

noncomputable def windowExtended (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) :
    (ℕ × Bool) × State (Sp C) :=
  extState (net C) z₀ (windowUpdate C) (0, true) n ω

noncomputable def windowCount (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) : ℕ :=
  (windowExtended C z₀ n ω).1.1

noncomputable def windowState (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) : State (Sp C) :=
  (windowExtended C z₀ n ω).2

theorem windowState_eq_pathState (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) :
    windowState C z₀ n ω = pathState (net C) z₀ ω n :=
  (extState_snd (net C) z₀ (windowUpdate C) (0, true) n ω).trans
    (prefixToState_eq_pathState (net C) z₀ ω n)

theorem windowLive_iff_zero_tickCount (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) :
    (windowExtended C z₀ n ω).1.2 = true ↔ tickCount C z₀ ω n = 0 := by
  induction n with
  | zero => simp [windowExtended, extState, extOf, tickCount]
  | succ n ih =>
      have hstep :
          (windowExtended C z₀ (n + 1) ω).1.2 =
            ((windowExtended C z₀ n ω).1.2 && !(firedTick C z₀ ω n)) := by
        change
          ((windowExtended C z₀ n ω).1.2 &&
            !(windowTick C (windowState C z₀ n ω) (ω (n + 1)))) = _
        rw [windowState_eq_pathState, windowTick_eq_firedTick] <;> rfl
      rw [hstep]
      cases ht : firedTick C z₀ ω n <;>
        simp [tickCount, TickAt, ht, ih]

theorem windowCount_zero (C : XCTM Q)
    (z₀ : State (Sp C)) (ω : LabelPath C) :
    windowCount C z₀ 0 ω = 0 := rfl

theorem windowCount_succ (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) :
    windowCount C z₀ (n + 1) ω =
      windowCount C z₀ n ω +
        windowIncrement C (windowState C z₀ n ω) (ω (n + 1)) := rfl

theorem windowCount_mono (C : XCTM Q)
    (z₀ : State (Sp C)) (ω : LabelPath C) :
    Monotone (fun n => windowCount C z₀ n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [windowCount_succ]
  exact Nat.le_add_right _ _

theorem measurable_windowCount (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) :
    Measurable (fun ω => windowCount C z₀ n ω) :=
  measurable_extState_comp (net C) z₀ (windowUpdate C) (0, true) n
    (fun y => y.1.1)

def windowEvent (C : XCTM Q) (z₀ : State (Sp C))
    (n j : ℕ) (z : State (Sp C)) : Set (LabelPath C) :=
  {ω | windowExtended C z₀ n ω = ((j, true), z)}

theorem windowEvent_iff (C : XCTM Q) (z₀ : State (Sp C))
    (n j : ℕ) (z : State (Sp C)) (ω : LabelPath C) :
    ω ∈ windowEvent C z₀ n j z ↔
      windowCount C z₀ n ω = j ∧ tickCount C z₀ ω n = 0 ∧
        pathState (net C) z₀ ω n = z := by
  constructor
  · intro h
    refine ⟨congrArg (fun y => y.1.1) h, ?_, ?_⟩
    · exact (windowLive_iff_zero_tickCount C z₀ n ω).mp
        (congrArg (fun y => y.1.2) h)
    · rw [← windowState_eq_pathState C z₀ n ω]
      exact congrArg Prod.snd h
  · rintro ⟨hj, ht, hz⟩
    apply Prod.ext
    · exact Prod.ext hj ((windowLive_iff_zero_tickCount C z₀ n ω).mpr ht)
    · exact (windowState_eq_pathState C z₀ n ω).trans hz

theorem windowEvent_count (C : XCTM Q) (z₀ : State (Sp C))
    (n j : ℕ) (z : State (Sp C)) {ω : LabelPath C}
    (h : ω ∈ windowEvent C z₀ n j z) :
    windowCount C z₀ n ω = j :=
  congrArg (fun y => y.1.1) h

theorem windowEvent_state (C : XCTM Q) (z₀ : State (Sp C))
    (n j : ℕ) (z : State (Sp C)) {ω : LabelPath C}
    (h : ω ∈ windowEvent C z₀ n j z) :
    windowState C z₀ n ω = z :=
  congrArg Prod.snd h

theorem measurableSet_windowEvent (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (z : State (Sp C)) :
    MeasurableSet (windowEvent C z₀ n j z) := by
  classical
  let F : (ℕ × Bool) × State (Sp C) → ℕ :=
    fun y => if y = ((j, true), z) then 1 else 0
  have hm : Measurable (fun ω : LabelPath C => F (windowExtended C z₀ n ω)) :=
    measurable_extState_comp (net C) z₀ (windowUpdate C) (0, true) n F
  have hset :
      (fun ω : LabelPath C => F (windowExtended C z₀ n ω)) ⁻¹' ({1} : Set ℕ) =
        windowEvent C z₀ n j z := by
    ext ω
    change (if windowExtended C z₀ n ω = ((j, true), z) then (1 : ℕ) else 0) = 1 ↔
      windowExtended C z₀ n ω = ((j, true), z)
    by_cases h : windowExtended C z₀ n ω = ((j, true), z) <;> simp [h]
  rw [← hset]
  exact hm (measurableSet_singleton (1 : ℕ))

private theorem measurableSet_labelAt (C : XCTM Q) (n : ℕ)
    (o : Option (Rx C)) :
    MeasurableSet {ω : LabelPath C | ω (n + 1) = o} := by
  classical
  let f : LabelPath C → ℕ := fun ω => if ω (n + 1) = o then 1 else 0
  have hf : Measurable f := by
    apply measurable_of_frestrictLe (net C) (n + 1) f
    intro ω ω' hprefix
    have he := congrFun hprefix
      (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))
    change ω (n + 1) = ω' (n + 1) at he
    change (if ω (n + 1) = o then (1 : ℕ) else 0) =
      (if ω' (n + 1) = o then (1 : ℕ) else 0)
    rw [he]
  have hset : f ⁻¹' ({1} : Set ℕ) = {ω : LabelPath C | ω (n + 1) = o} := by
    ext ω
    change (if ω (n + 1) = o then (1 : ℕ) else 0) = 1 ↔ ω (n + 1) = o
    by_cases h : ω (n + 1) = o <;> simp [h]
  rw [← hset]
  exact hf (measurableSet_singleton (1 : ℕ))

theorem windowLaw_event_label (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (z : State (Sp C))
    (o : Option (Rx C)) :
    windowLaw C z₀
        (windowEvent C z₀ n j z ∩ {ω | ω (n + 1) = o}) =
      windowLaw C z₀ (windowEvent C z₀ n j z) *
        massActionPMF (net C) (net_hasPositiveRates C) z o := by
  let A : Set ((i : Finset.Iic n) → Option (Rx C)) :=
    {p | extOf (net C) z₀ (windowUpdate C) (0, true) n p =
      ((j, true), z)}
  have hA : ∀ p ∈ A, prefixToState (net C) z₀ n p = z := by
    intro p hp
    have hs := congrArg Prod.snd hp
    simpa only [extOf_snd] using hs
  have h := rawLaw_prefix_next (net C) (net_hasPositiveRates C) z₀
    n A z hA o
  simpa only [windowLaw, windowEvent, windowExtended, extState, A,
    Set.mem_inter_iff, Set.mem_setOf_eq] using h

noncomputable def windowOcc (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (z : State (Sp C)) : ℝ≥0∞ :=
  ∑' n, windowLaw C z₀ (windowEvent C z₀ n j z)

def windowEntryEvent (C : XCTM Q) (z₀ : State (Sp C))
    (n j : ℕ) (z : State (Sp C)) : Set (LabelPath C) :=
  windowEvent C z₀ n j z ∩
    {ω | n = 0 ∨ windowCount C z₀ (n - 1) ω < j}

noncomputable def windowEntries (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (z : State (Sp C)) : ℝ≥0∞ :=
  ∑' n, windowLaw C z₀ (windowEntryEvent C z₀ n j z)

theorem windowEntryEvent_zero (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (z : State (Sp C)) :
    windowEntryEvent C z₀ 0 j z = windowEvent C z₀ 0 j z := by
  ext ω
  simp [windowEntryEvent]

theorem measurableSet_windowEntryEvent (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (z : State (Sp C)) :
    MeasurableSet (windowEntryEvent C z₀ n j z) := by
  by_cases hn : n = 0
  · subst n
    rw [windowEntryEvent_zero]
    exact measurableSet_windowEvent C z₀ 0 j z
  · have hlt : MeasurableSet
        {ω | windowCount C z₀ (n - 1) ω < j} :=
      measurableSet_lt (measurable_windowCount C z₀ (n - 1)) measurable_const
    simpa only [windowEntryEvent, hn, false_or] using
      (measurableSet_windowEvent C z₀ n j z).inter hlt

theorem windowEntryEvents_pairwise (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (z : State (Sp C)) :
    Pairwise (Function.onFun Disjoint
      (fun n => windowEntryEvent C z₀ n j z)) := by
  intro n m hne
  refine Set.disjoint_left.mpr ?_
  rintro ω ⟨hn, hprevn⟩ ⟨hm, hprevm⟩
  have hcountn := windowEvent_count C z₀ n j z hn
  have hcountm := windowEvent_count C z₀ m j z hm
  rcases lt_trichotomy n m with hlt | heq | hgt
  · rcases hprevm with hmzero | hprev
    · omega
    · have hmono := windowCount_mono C z₀ ω (show n ≤ m - 1 by omega)
      change windowCount C z₀ n ω ≤ windowCount C z₀ (m - 1) ω at hmono
      rw [hcountn] at hmono
      omega
  · exact hne heq
  · rcases hprevn with hnzero | hprev
    · omega
    · have hmono := windowCount_mono C z₀ ω (show m ≤ n - 1 by omega)
      change windowCount C z₀ m ω ≤ windowCount C z₀ (n - 1) ω at hmono
      rw [hcountm] at hmono
      omega

theorem windowEntries_le_one (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (z : State (Sp C)) :
    windowEntries C z₀ j z ≤ 1 := by
  calc
    windowEntries C z₀ j z =
        windowLaw C z₀ (⋃ n, windowEntryEvent C z₀ n j z) :=
      (measure_iUnion (windowEntryEvents_pairwise C z₀ j z)
        (fun n => measurableSet_windowEntryEvent C z₀ n j z)).symm
    _ ≤ 1 := prob_le_one

theorem windowEntries_ne_top (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (z : State (Sp C)) :
    windowEntries C z₀ j z ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (windowEntries_le_one C z₀ j z)

def windowInternalEvent (C : XCTM Q) (z₀ : State (Sp C))
    (n j : ℕ) (z : State (Sp C)) : Set (LabelPath C) :=
  windowEvent C z₀ (n + 1) j z ∩
    {ω | windowCount C z₀ n ω = j}

noncomputable def windowInternalMass (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (z : State (Sp C)) : ℝ≥0∞ :=
  ∑' n, windowLaw C z₀ (windowInternalEvent C z₀ n j z)

theorem measurableSet_windowInternalEvent (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (z : State (Sp C)) :
    MeasurableSet (windowInternalEvent C z₀ n j z) :=
  (measurableSet_windowEvent C z₀ (n + 1) j z).inter
    (measurableSet_eq_fun (measurable_windowCount C z₀ n) measurable_const)

theorem windowLaw_event_succ_split (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (z : State (Sp C)) :
    windowLaw C z₀ (windowEvent C z₀ (n + 1) j z) =
      windowLaw C z₀ (windowEntryEvent C z₀ (n + 1) j z) +
      windowLaw C z₀ (windowInternalEvent C z₀ n j z) := by
  have hset : windowEvent C z₀ (n + 1) j z =
      windowEntryEvent C z₀ (n + 1) j z ∪
        windowInternalEvent C z₀ n j z := by
    ext ω
    constructor
    · intro hω
      have hc := windowEvent_count C z₀ (n + 1) j z hω
      have hm := windowCount_mono C z₀ ω (Nat.le_succ n)
      change windowCount C z₀ n ω ≤ windowCount C z₀ (n + 1) ω at hm
      rw [hc] at hm
      rcases lt_or_eq_of_le hm with hlt | heq
      · exact Or.inl ⟨hω, Or.inr (by simpa using hlt)⟩
      · exact Or.inr ⟨hω, heq⟩
    · rintro (hω | hω)
      · exact hω.1
      · exact hω.1
  have hdisj : Disjoint (windowEntryEvent C z₀ (n + 1) j z)
      (windowInternalEvent C z₀ n j z) := by
    refine Set.disjoint_left.mpr ?_
    rintro ω ⟨_, hentry⟩ ⟨_, hinternal⟩
    change windowCount C z₀ n ω = j at hinternal
    rcases hentry with hzero | hlt
    · omega
    · simp only [Nat.add_sub_cancel] at hlt
      omega
  rw [hset, measure_union hdisj
    (measurableSet_windowInternalEvent C z₀ n j z)]

theorem windowOcc_balance (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (z : State (Sp C)) :
    windowOcc C z₀ j z =
      windowEntries C z₀ j z + windowInternalMass C z₀ j z := by
  calc
    windowOcc C z₀ j z =
        windowLaw C z₀ (windowEvent C z₀ 0 j z) +
          ∑' n, windowLaw C z₀ (windowEvent C z₀ (n + 1) j z) := by
      unfold windowOcc
      exact tsum_eq_zero_add' ENNReal.summable
    _ =
        (windowLaw C z₀ (windowEntryEvent C z₀ 0 j z) +
          ∑' n, windowLaw C z₀ (windowEntryEvent C z₀ (n + 1) j z)) +
          ∑' n, windowLaw C z₀ (windowInternalEvent C z₀ n j z) := by
      simp_rw [windowLaw_event_succ_split]
      rw [ENNReal.tsum_add, windowEntryEvent_zero]
      exact (add_assoc _ _ _).symm
    _ = windowEntries C z₀ j z + windowInternalMass C z₀ j z := by
      exact congrArg
        (fun t : ℝ≥0∞ =>
          t + ∑' n, windowLaw C z₀ (windowInternalEvent C z₀ n j z))
        (tsum_eq_zero_add'
          (f := fun n => windowLaw C z₀ (windowEntryEvent C z₀ n j z))
          ENNReal.summable).symm

theorem windowOcc_mul_work_pmf_le_one (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (z : State (Sp C))
    (r : Rx C) (hr : isClock r = false)
    (he : (rxn C r).enabled z) :
    windowOcc C z₀ j z *
      massActionPMF (net C) (net_hasPositiveRates C) z (some r) ≤ 1 := by
  let F : ℕ → Set (LabelPath C) := fun n =>
    windowEvent C z₀ n j z ∩ {ω | ω (n + 1) = some r}
  have hmeas : ∀ n, MeasurableSet (F n) := fun n =>
    (measurableSet_windowEvent C z₀ n j z).inter
      (measurableSet_labelAt C n (some r))
  have hdisj : Pairwise (Function.onFun Disjoint F) := by
    intro n m hne
    refine Set.disjoint_left.mpr ?_
    rintro ω ⟨hn, hon⟩ ⟨hm, hom⟩
    have hcountn := windowEvent_count C z₀ n j z hn
    have hcountm := windowEvent_count C z₀ m j z hm
    have hstaten := windowEvent_state C z₀ n j z hn
    have hstatem := windowEvent_state C z₀ m j z hm
    rcases lt_trichotomy n m with hlt | heq | hgt
    · have hmono := windowCount_mono C z₀ ω (show n + 1 ≤ m by omega)
      change windowCount C z₀ (n + 1) ω ≤ windowCount C z₀ m ω at hmono
      rw [windowCount_succ, hcountn, hstaten, hon,
        windowIncrement_of_work C z r hr he, hcountm] at hmono
      omega
    · exact hne heq
    · have hmono := windowCount_mono C z₀ ω (show m + 1 ≤ n by omega)
      change windowCount C z₀ (m + 1) ω ≤ windowCount C z₀ n ω at hmono
      rw [windowCount_succ, hcountm, hstatem, hom,
        windowIncrement_of_work C z r hr he, hcountn] at hmono
      omega
  calc
    windowOcc C z₀ j z *
        massActionPMF (net C) (net_hasPositiveRates C) z (some r) =
        ∑' n, windowLaw C z₀ (F n) := by
      rw [windowOcc, ← ENNReal.tsum_mul_right]
      exact tsum_congr fun n =>
        (windowLaw_event_label C z₀ n j z (some r)).symm
    _ = windowLaw C z₀ (⋃ n, F n) :=
      (measure_iUnion hdisj hmeas).symm
    _ ≤ 1 := prob_le_one

theorem window_pmf_ne_zero_of_enabled (C : XCTM Q)
    (z : State (Sp C)) (r : Rx C) (he : (rxn C r).enabled z) :
    massActionPMF (net C) (net_hasPositiveRates C) z (some r) ≠ 0 := by
  have hNT : ¬ (net C).Terminal z := fun hT => hT r he
  have hp := Reaction.propensity_ne_zero_of_enabled_of_positive_rate
    he (net_hasPositiveRates C r)
  have ht := totalPropensity_ne_zero_of_nonTerminal
    (net C) (net_hasPositiveRates C) hNT
  have hj : jumpProbAt (net C) z r ≠ 0 := by
    unfold jumpProbAt
    exact div_ne_zero hp ht
  change massActionWeight (net C) (net_hasPositiveRates C) z (some r) ≠ 0
  simp only [massActionWeight, dif_neg hNT]
  rw [← ENNReal.coe_nnratCast, ENNReal.coe_ne_zero]
  exact_mod_cast hj

theorem windowOcc_ne_top (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (z : State (Sp C))
    (hn : ¬ WorkTerminal C z) :
    windowOcc C z₀ j z ≠ ⊤ := by
  classical
  have hex : ∃ r : Rx C, isClock r = false ∧ (rxn C r).enabled z := by
    by_contra hnone
    apply hn
    intro r hr he
    exact hnone ⟨r, hr, he⟩
  obtain ⟨r, hr, he⟩ := hex
  have hbound := windowOcc_mul_work_pmf_le_one C z₀ j z r hr he
  have hp := window_pmf_ne_zero_of_enabled C z r he
  have hfinite := ne_top_of_le_ne_top ENNReal.one_ne_top hbound
  intro htop
  apply hfinite
  rw [htop, ENNReal.top_mul hp]

def prematureTickEvent (C : XCTM Q) (z₀ : State (Sp C)) : Set (LabelPath C) :=
  ⋃ n : ℕ, {ω | tickCount C z₀ ω n = 0} ∩ {ω | BadTickAt C z₀ ω n}

theorem measurableSet_prematureTickEvent (C : XCTM Q) (z₀ : State (Sp C)) :
    MeasurableSet (prematureTickEvent C z₀) := by
  apply MeasurableSet.iUnion
  intro n
  exact
    (measurableSet_eq_fun (measurable_tickCount C z₀ n) measurable_const).inter
      (measurableSet_badTickAt C z₀ n)

end WindowAnalysis

namespace WindowAnalysis

abbrev ClocklessState (C : XCTM Q) :=
  {x : State (Sp C) // workView C x = x}

theorem clockless_clock_zero (C : XCTM Q) (x : ClocklessState C) (c : Fin 5) :
    x.val (.clock c) = 0 := by
  have h := congrFun x.property (.clock c)
  exact h.symm

def clockInsert (C : XCTM Q) (x : ClocklessState C) (c : Fin 5) :
    State (Sp C) :=
  x.val + unit (.clock c)

theorem clockInsert_clock (C : XCTM Q) (x : ClocklessState C) (c d : Fin 5) :
    clockInsert C x c (.clock d) = if d = c then 1 else 0 := by
  simp [clockInsert, unit, clockless_clock_zero]

theorem clockInsert_workView (C : XCTM Q) (x : ClocklessState C) (c : Fin 5) :
    workView C (clockInsert C x c) = x.val := by
  funext s
  cases s <;> simp [clockInsert, workView, unit, clockless_clock_zero]

theorem work_rate_clockInsert (C : XCTM Q) (x : ClocklessState C)
    (c : Fin 5) (r : Rx C) (hr : isClock r = false) :
    rate C r (clockInsert C x c) = rate C r x.val := by
  cases r <;>
    simp_all [isClock, rate, sourceLeft, sourceRight, clockInsert, unit]

theorem clockInsert_injective (C : XCTM Q) :
    Function.Injective
      (fun p : ClocklessState C × Fin 5 => clockInsert C p.1 p.2) := by
  intro p q h
  have hx : p.1 = q.1 := by
    apply Subtype.ext
    have hw := congrArg (workView C) h
    simpa only [clockInsert_workView] using hw
  have hc : p.2 = q.2 := by
    by_contra hne
    have hh := congrFun h (.clock p.2)
    simp [clockInsert_clock, hne] at hh
  exact Prod.ext hx hc

theorem workTerminal_clockInsert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) :
    WorkTerminal C (clockInsert C x c) ↔ WorkTerminal C x.val := by
  simpa only [clockInsert_workView] using
    (workTerminal_view C (clockInsert C x c)).symm

noncomputable def windowOccupation (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : Fin 5) : ℝ≥0∞ :=
  windowOcc C z₀ j (clockInsert C x c) /
    ((net C).totalPropensity (clockInsert C x c) : ℝ≥0∞)

noncomputable def windowEntry (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : Fin 5) : ℝ≥0∞ :=
  windowEntries C z₀ j (clockInsert C x c)

theorem windowEntry_le_one (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : Fin 5) :
    windowEntry C z₀ j x c ≤ 1 :=
  windowEntries_le_one C z₀ j (clockInsert C x c)

theorem windowEntry_ne_top (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : Fin 5) :
    windowEntry C z₀ j x c ≠ ⊤ :=
  windowEntries_ne_top C z₀ j (clockInsert C x c)

theorem windowOccupation_ne_top (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (hn : ¬ WorkTerminal C x.val) :
    windowOccupation C z₀ j x c ≠ ⊤ := by
  have hnz : ¬ WorkTerminal C (clockInsert C x c) :=
    fun ht => hn ((workTerminal_clockInsert C x c).mp ht)
  have hNT : ¬ (net C).Terminal (clockInsert C x c) := by
    intro ht
    apply hnz
    intro r _hr
    exact ht r
  have hB := totalPropensity_ne_zero_of_nonTerminal
    (net C) (net_hasPositiveRates C) hNT
  apply ENNReal.div_ne_top
    (windowOcc_ne_top C z₀ j (clockInsert C x c) hnz)
  rw [← ENNReal.coe_nnratCast, ENNReal.coe_ne_zero]
  exact_mod_cast hB

theorem windowEntries_initial_level (C : XCTM Q)
    (z₀ z : State (Sp C)) :
    windowEntries C z₀ 0 z = if z₀ = z then 1 else 0 := by
  classical
  have hzero : ∀ n : ℕ, n ≠ 0 →
      windowEntryEvent C z₀ n 0 z = ∅ := by
    intro n hn
    ext ω
    simp [windowEntryEvent, hn]
  have hinitial : windowEvent C z₀ 0 0 z =
      if z₀ = z then Set.univ else ∅ := by
    ext ω
    by_cases hz : z₀ = z <;>
      simp [windowEvent, windowExtended, extState, extOf, hz]
  calc
    windowEntries C z₀ 0 z =
        windowLaw C z₀ (windowEntryEvent C z₀ 0 0 z) := by
      unfold windowEntries
      apply tsum_eq_single 0
      intro n hn
      rw [hzero n hn, measure_empty]
    _ = if z₀ = z then 1 else 0 := by
      rw [windowEntryEvent_zero, hinitial]
      split_ifs <;> simp

end WindowAnalysis

namespace WindowAnalysis

open Ripple.sCRNUniversality.Stochastic.ClockOccupation

def PhysicalBalance (a f ρ : ℝ) (w e : ℕ → ℝ) : Prop :=
  ∀ c, c < 5 →
    (ρ + f + (if c + 1 < 5 then a else 0)) * w c =
      e c + (if 0 < c then a * w (c - 1) else 0) +
        (if c + 1 < 5 then f * w (c + 1) else 0)

theorem physicalBalance_normalize
    {a f ρ : ℝ} {w e : ℕ → ℝ}
    (hf : 0 < f) (h : PhysicalBalance a f ρ w e) :
    ClockBalance 5 (a / f) (ρ / f) 1 w (fun c => e c / f) := by
  intro c hc
  have hh := h c hc
  interval_cases c <;>
    norm_num [Ripple.sCRNUniversality.Stochastic.ClockOccupation.rate] at hh ⊢ <;>
    field_simp [ne_of_gt hf] <;>
    nlinarith [hh]

theorem physicalBalance_total
    {a f ρ : ℝ} {w e : ℕ → ℝ}
    (hf : 0 < f) (h : PhysicalBalance a f ρ w e) :
    ρ * psum w 5 + f * w 0 = psum e 5 := by
  have ht := ClockBalance.total (physicalBalance_normalize hf h) (by norm_num)
  have hsum : psum (fun c => e c / f) 5 = psum e 5 / f := by
    simp only [psum, Finset.sum_div]
  simp only [ClockBalance.u, one_mul, hsum] at ht
  field_simp [ne_of_gt hf] at ht
  nlinarith [ht]

theorem inCone_div
    {b f : ℝ} {e : ℕ → ℝ}
    (hf : 0 < f) (he : InCone 5 b e) :
    InCone 5 b (fun c => e c / f) := by
  intro c hc
  calc
    b * (e c / f) = (b * e c) / f := by ring
    _ ≤ e (c + 1) / f := div_le_div_of_nonneg_right (he c hc) hf.le

theorem physicalBalance_inCone
    {a f ρ b : ℝ} {w e : ℕ → ℝ}
    (hf : 0 < f) (h : PhysicalBalance a f ρ w e)
    (hb : 0 < b) (hba : b ≤ a / f) (hρ : 0 ≤ ρ)
    (hw : ∀ c, c < 5 → 0 ≤ w c) (he : InCone 5 b e) :
    InCone 5 b w := by
  exact clockBalance_inCone_of_lower_ratio
    (physicalBalance_normalize hf h) hb hba (div_nonneg hρ hf.le)
    hw (inCone_div hf he)

theorem entry_cone_of_work_edges
    {ι : Type*} {b : ℝ} (β : ι → ℝ) (w : ι → ℕ → ℝ)
    (hβ : ∀ x, 0 ≤ β x)
    (hw : ∀ x, InCone 5 b (w x))
    (hs : ∀ c, c < 5 → Summable (fun x => β x * w x c)) :
    InCone 5 b (fun c => ∑' x, β x * w x c) := by
  intro c hc
  have hcsmall : c < 5 := by omega
  rw [← tsum_mul_left]
  refine ((hs c hcsmall).mul_left b).tsum_le_tsum ?_ (hs (c + 1) hc)
  intro x
  calc
    b * (β x * w x c) = β x * (b * w x c) := by ring
    _ ≤ β x * w x (c + 1) :=
      mul_le_mul_of_nonneg_left (hw x c hc) (hβ x)

theorem entry_cone_at_top {b mass : ℝ} (hmass : 0 ≤ mass) :
    InCone 5 b (fun c => if c = 4 then mass else 0) := by
  intro c hc
  have hcne : c ≠ 4 := by omega
  simp only [if_neg hcne, mul_zero]
  split_ifs <;> positivity

theorem geometric_weight_pos {b : ℝ} (hb : 0 ≤ b) :
    0 < geomWeight b 5 := by
  have hone : (1 : ℝ) ≤ geomWeight b 5 := by
    calc
      (1 : ℝ) = b ^ 0 := by simp
      _ ≤ ∑ c ∈ Finset.range 5, b ^ c :=
        Finset.single_le_sum
          (fun c _ => pow_nonneg hb c) (by simp)
  linarith

theorem physicalBalance_tick_bound
    {a f F ρ b : ℝ} {w e : ℕ → ℝ}
    (hf : 0 < f) (hfF : f ≤ F) (h : PhysicalBalance a f ρ w e)
    (hb : 0 < b) (hba : b ≤ a / f) (hρ : 0 ≤ ρ)
    (hw : ∀ c, c < 5 → 0 ≤ w c) (he : InCone 5 b e) :
    f * w 0 ≤ (1 / geomWeight b 5) * F * psum w 5 ∧
      ρ * psum w 5 ≤ psum e 5 := by
  have hn := physicalBalance_normalize hf h
  have hlocal := clockBalance_tick_le_of_lower_ratio
    hn hb hba (div_nonneg hρ hf.le) hw (inCone_div hf he)
  have hG := geometric_weight_pos hb.le
  have hwzero := hw 0 (by norm_num)
  have hquot : w 0 ≤ psum w 5 / geomWeight b 5 :=
    (le_div_iff₀ hG).2 hlocal.1
  constructor
  · calc
      f * w 0 ≤ F * w 0 := mul_le_mul_of_nonneg_right hfF hwzero
      _ ≤ F * (psum w 5 / geomWeight b 5) :=
        mul_le_mul_of_nonneg_left hquot (hf.le.trans hfF)
      _ = (1 / geomWeight b 5) * F * psum w 5 := by ring
  · have ht := physicalBalance_total hf h
    have hz : 0 ≤ f * w 0 := mul_nonneg hf.le hwzero
    linarith

theorem ratio_eq_of_counts {a f α : ℕ} (hf : 0 < f)
    (ha : a = α * f) :
    (a : ℝ) / (f : ℝ) = (α : ℝ) := by
  apply (div_eq_iff (show (f : ℝ) ≠ 0 from ne_of_gt
    (show (0 : ℝ) < (f : ℝ) by exact_mod_cast hf))).2
  exact_mod_cast ha

theorem buffer_reachable_ratio
    (C : XCTM Q) (b : Buffer C)
    (hs : 3 ≤ (Buffer.before C b).tape.length)
    {z : State (Sp C)}
    (hreach : WorkReach C
      (Plan.workState C (Buffer.before C b) + unit .signal) z) :
    (forwardCount C z : ℝ) / backwardCount C z = (bufferAccuracy b : ℝ) := by
  have hclosed : ∀ x y, BufferWindow C b x → WorkStep C x y →
      BufferWindow C b y := by
    rintro x y hx ⟨r, hr, he, rfl⟩
    exact (buffer_fire C hx hr he).1
  have hz := workReach_invariant C (BufferWindow C b) hclosed
    hreach (buffer_start C b)
  exact ratio_eq_of_counts (buffer_parameters C b hs hz).1
    (buffer_clock_counts C b hz).1

theorem read_reachable_ratio
    (C : XCTM Q) (q : ReadState C) (w : List Bool) (a : ℕ)
    (hs : 3 ≤ w.length) {z : State (Sp C)}
    (hreach : WorkReach C
      (Plan.workState C (.third (.inl q) w a) + unit .signal) z) :
    (forwardCount C z : ℝ) / backwardCount C z = (a : ℝ) := by
  obtain ⟨ha, hf⟩ := read_reachable_clock_counts C q w a hs hreach
  have hd : 0 < stateCount w.length := by unfold stateCount; positivity
  apply ratio_eq_of_counts
  · simpa only [hf] using hd
  · simpa only [hf] using ha

theorem extension_reachable_ratio
    (C : XCTM Q) (e : ExtendState C) (w : List Bool) (a : ℕ)
    {z : State (Sp C)}
    (hreach : WorkReach C
      (Plan.workState C (.third (.inr e) w a) + unit .signal) z) :
    (forwardCount C z : ℝ) / backwardCount C z = (a : ℝ) := by
  have hstart :
      ExtensionInvariant C e (stateCount w.length) (tval w) (threshold w.length)
        (a * stateCount w.length) (stateCount w.length)
        (Plan.workState C (.third (.inr e) w a) + unit .signal) := by
    rw [← extension_start_payload]
    exact extension_start_invariant C e _ _ _ _ _ (fun _ => 0)
  have hz := workReach_invariant C
    (ExtensionInvariant C e (stateCount w.length) (tval w) (threshold w.length)
      (a * stateCount w.length) (stateCount w.length))
    (extension_work_closed C e _ _ _ _ _) hreach hstart
  have hd : 0 < stateCount w.length := by unfold stateCount; positivity
  have hf : backwardCount C z = stateCount w.length := hz.backward
  have ha : forwardCount C z = a * stateCount w.length := hz.forward
  apply ratio_eq_of_counts
  · simpa only [hf] using hd
  · simpa only [hf] using ha

noncomputable def nextLowerRatio {C : XCTM Q} : Plan C → ℝ
  | .first _ _ a _ => (a : ℝ) / 3
  | .second _ _ a | .third _ _ a
    | .write _ _ _ a | .extend _ _ a => a

theorem next_window_sharp_parameters
    (C : XCTM Q) (p : Plan C)
    (hs : 3 ≤ p.tape.length) (hh : Plan.halted C p = false)
    {z : State (Sp C)}
    (hreach : WorkReach C (Plan.workState C p + unit .signal) z) :
    0 < backwardCount C z ∧
      backwardCount C z ≤ stateCount p.tape.length ∧
      nextLowerRatio p ≤ (forwardCount C z : ℝ) / backwardCount C z := by
  have hp := next_window_parameters C p hs hh hreach
  refine ⟨hp.1, hp.2.1, ?_⟩
  cases p with
  | first q w a latent => exact hp.2.2.1
  | second q w a =>
      exact (buffer_reachable_ratio C (.toThird q w a) hs hreach).symm.le
  | third q w a =>
      cases q with
      | inl q => exact (read_reachable_ratio C q w a hs hreach).symm.le
      | inr e => exact (extension_reachable_ratio C e w a hreach).symm.le
  | write q b w a =>
      exact (buffer_reachable_ratio C (.fromRead q b w a) hs hreach).symm.le
  | extend e w a =>
      exact (buffer_reachable_ratio C (.fromExtension e w a) hs hreach).symm.le

end WindowAnalysis

namespace StandaloneWork

def workNet (C : XCTM Q) : Network (Sp C) where
  I := {r : Rx C // isClock r = false}
  rxn r := rxn C r.val

instance (C : XCTM Q) : DecidableEq (workNet C).I := by
  change DecidableEq {r : Rx C // isClock r = false}
  infer_instance

theorem workNet_hasPositiveRates (C : XCTM Q) :
    (workNet C).hasPositiveRates := by
  intro r
  exact net_hasPositiveRates C r.val

theorem workNet_terminal_iff (C : XCTM Q) (x : State (Sp C)) :
    (workNet C).Terminal x ↔ WorkTerminal C x := by
  constructor
  · intro ht r hr
    exact ht ⟨r, hr⟩
  · intro ht r
    exact ht r.val r.property

def totalWorkRate (C : XCTM Q) (x : State (Sp C)) : ℕ :=
  ∑ r : {r : Rx C // isClock r = false}, rate C r.val x

theorem workNet_totalPropensity (C : XCTM Q) (x : State (Sp C)) :
    (workNet C).totalPropensity x = (totalWorkRate C x : Rate) := by
  change (∑ r : {r : Rx C // isClock r = false},
    (rxn C r.val).propensity x) =
      ((∑ r : {r : Rx C // isClock r = false}, rate C r.val x : ℕ) : Rate)
  simp only [propensity_rxn, rate, Nat.cast_sum]

theorem totalWorkRate_pos (C : XCTM Q) (x : State (Sp C))
    (hx : ¬ WorkTerminal C x) : 0 < totalWorkRate C x := by
  classical
  by_contra hpos
  have hz : totalWorkRate C x = 0 := Nat.eq_zero_of_not_pos hpos
  apply hx
  intro r hr
  rw [enabled_iff]
  intro hne
  have hle : rate C r x ≤ totalWorkRate C x :=
    Finset.single_le_sum
      (f := fun i : {r : Rx C // isClock r = false} => rate C i.val x)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨r, hr⟩ : {r : Rx C // isClock r = false}))
  omega

theorem stateStep_of_terminal (C : XCTM Q) (x : State (Sp C))
    (o : Option (workNet C).I) (hx : WorkTerminal C x) :
    stateStep (workNet C) x o = x := by
  have ht := (workNet_terminal_iff C x).mpr hx
  simp [stateStep, ht]

theorem stateStep_is_workStep (C : XCTM Q) (x : State (Sp C))
    (o : Option (workNet C).I) (hx : ¬ WorkTerminal C x) :
    WorkStep C x (stateStep (workNet C) x o) := by
  classical
  have ht : ¬ (workNet C).Terminal x :=
    fun h => hx ((workNet_terminal_iff C x).mp h)
  let r := fireOptionSanitized (workNet C) x o ht
  refine ⟨r.val, r.property, ?_, ?_⟩
  · exact fireOptionSanitized_enabled (workNet C) x o ht
  · change stateStep (workNet C) x o =
      ((workNet C).rxn (fireOptionSanitized (workNet C) x o ht)).fire x
    simp only [stateStep, dif_neg ht] <;> rfl

theorem path_invariant (C : XCTM Q) {start target : State (Sp C)}
    (P : WorkCertificate C start target)
    (ω : ℕ → Option (workNet C).I) :
    ∀ n, P.inv (pathState (workNet C) start ω n) := by
  intro n
  induction n with
  | zero => exact P.initial
  | succ n ih =>
      change P.inv (stateStep (workNet C)
        (pathState (workNet C) start ω n) (ω (n + 1)))
      by_cases ht : WorkTerminal C (pathState (workNet C) start ω n)
      · rw [stateStep_of_terminal C _ _ ht]
        exact ih
      · exact P.closed _ _ ih (stateStep_is_workStep C _ _ ht)

theorem terminal_persists (C : XCTM Q) (start : State (Sp C))
    (ω : ℕ → Option (workNet C).I) {n m : ℕ}
    (hn : WorkTerminal C (pathState (workNet C) start ω n)) (hnm : n ≤ m) :
    WorkTerminal C (pathState (workNet C) start ω m) := by
  induction hnm with
  | refl => exact hn
  | @step m h ih =>
      change WorkTerminal C (stateStep (workNet C)
        (pathState (workNet C) start ω m) (ω (m + 1)))
      rw [stateStep_of_terminal C _ _ ih]
      exact ih

theorem rank_bound_before_terminal (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    (ω : ℕ → Option (workNet C).I) :
    ∀ n, ¬ WorkTerminal C (pathState (workNet C) start ω n) →
      P.rank (pathState (workNet C) start ω n) + n ≤ P.rank start
  | 0, _ => by simp [pathState]
  | n + 1, hn => by
      have hprev : ¬ WorkTerminal C (pathState (workNet C) start ω n) := by
        intro ht
        exact hn (terminal_persists C start ω ht (Nat.le_succ n))
      have hb := rank_bound_before_terminal C P ω n hprev
      have hd := P.decreases _ _ (path_invariant C P ω n)
        (stateStep_is_workStep C _ (ω (n + 1)) hprev)
      change P.rank (stateStep (workNet C)
        (pathState (workNet C) start ω n) (ω (n + 1))) + (n + 1) ≤ P.rank start
      omega

theorem terminal_at_rank (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    (ω : ℕ → Option (workNet C).I) :
    WorkTerminal C (pathState (workNet C) start ω (P.rank start)) := by
  by_contra hn
  have hb := rank_bound_before_terminal C P ω (P.rank start) hn
  have hd := P.decreases _ _ (path_invariant C P ω (P.rank start))
    (stateStep_is_workStep C _ (ω (P.rank start + 1)) hn)
  omega

noncomputable def holdingMean (C : XCTM Q) (x : State (Sp C)) : ℝ≥0∞ := by
  classical
  exact if WorkTerminal C x then 0 else (totalWorkRate C x : ℝ≥0∞)⁻¹

theorem holdingMean_le_one (C : XCTM Q) (x : State (Sp C)) :
    holdingMean C x ≤ 1 := by
  classical
  unfold holdingMean
  split_ifs with ht
  · exact bot_le
  · apply ENNReal.inv_le_one.mpr
    exact_mod_cast Nat.succ_le_of_lt (totalWorkRate_pos C x ht)

noncomputable def duration (C : XCTM Q) (start : State (Sp C))
    (ω : ℕ → Option (workNet C).I) : ℝ≥0∞ :=
  ∑' n, holdingMean C (pathState (workNet C) start ω n)

theorem measurable_holdingMean_at (C : XCTM Q) (start : State (Sp C)) (n : ℕ) :
    Measurable (fun ω : ℕ → Option (workNet C).I =>
      holdingMean C (pathState (workNet C) start ω n)) := by
  apply measurable_of_frestrictLe (workNet C) n
  intro ω ω' h
  have hz : pathState (workNet C) start ω n =
      pathState (workNet C) start ω' n := by
    rw [← prefixToState_eq_pathState (workNet C) start ω n,
      ← prefixToState_eq_pathState (workNet C) start ω' n]
    exact congrArg (prefixToState (workNet C) start n) h
  exact congrArg (holdingMean C) hz

theorem measurable_duration (C : XCTM Q) (start : State (Sp C)) :
    Measurable (duration C start) := by
  unfold duration
  exact Measurable.tsum (measurable_holdingMean_at C start)

noncomputable def meanDuration (C : XCTM Q) (start : State (Sp C)) : ℝ≥0∞ :=
  ∫⁻ ω, duration C start ω ∂rawLaw (workNet C) (workNet_hasPositiveRates C) start

theorem duration_le_rank (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    (ω : ℕ → Option (workNet C).I) :
    duration C start ω ≤ (P.rank start : ℝ≥0∞) := by
  classical
  unfold duration
  have hz : ∀ n ∉ Finset.range (P.rank start),
      holdingMean C (pathState (workNet C) start ω n) = 0 := by
    intro n hn
    have hle : P.rank start ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    have ht := terminal_persists C start ω (terminal_at_rank C P ω) hle
    simp [holdingMean, ht]
  rw [tsum_eq_sum (s := Finset.range (P.rank start)) hz]
  calc
    ∑ n ∈ Finset.range (P.rank start),
        holdingMean C (pathState (workNet C) start ω n)
      ≤ ∑ _n ∈ Finset.range (P.rank start), (1 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun n _ => holdingMean_le_one C _)
    _ = (P.rank start : ℝ≥0∞) := by simp

theorem meanDuration_le_rank (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target) :
    meanDuration C start ≤ (P.rank start : ℝ≥0∞) := by
  letI : IsProbabilityMeasure
      (rawLaw (workNet C) (workNet_hasPositiveRates C) start) :=
    rawLaw_isProbabilityMeasure _ _ _
  calc
    meanDuration C start
      ≤ ∫⁻ _ω : ℕ → Option (workNet C).I, (P.rank start : ℝ≥0∞)
          ∂rawLaw (workNet C) (workNet_hasPositiveRates C) start :=
        lintegral_mono (duration_le_rank C P)
    _ = (P.rank start : ℝ≥0∞) := by simp

theorem meanDuration_ne_top (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target) :
    meanDuration C start ≠ ∞ :=
  ne_top_of_le_ne_top (by simp) (meanDuration_le_rank C P)

theorem next_window_meanDuration_ne_top (C : XCTM Q) (p : Plan C)
    (hs : 3 ≤ p.tape.length) (hh : Plan.halted C p = false) :
    meanDuration C (Plan.workState C p + unit .signal) ≠ ∞ :=
  meanDuration_ne_top C (planCertificate C p hs hh)

end StandaloneWork

theorem entry_domination_of_exit_recursion
    {X : Type*} (K : X → X → ℝ≥0∞)
    (E D p : ℕ → X → ℝ≥0∞)
    (hzero : ∀ x, E 0 x ≤ p 0 x)
    (hexit : ∀ j x, D j x ≤ E j x)
    (hentry : ∀ j y, E (j + 1) y ≤ ∑' x, D j x * K x y)
    (hmarginal : ∀ j y, p (j + 1) y = ∑' x, p j x * K x y) :
    ∀ j x, E j x ≤ p j x := by
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      intro y
      calc
        E (j + 1) y ≤ ∑' x, D j x * K x y := hentry j y
        _ ≤ ∑' x, p j x * K x y := ENNReal.tsum_le_tsum (fun x =>
          mul_le_mul_right' ((hexit j x).trans (ih x)) (K x y))
        _ = p (j + 1) y := (hmarginal j y).symm

theorem occupation_domination_of_entry_bound
    {X : Type*} (E p S : ℕ → X → ℝ≥0∞) (H : X → ℝ≥0∞)
    (hentry : ∀ j x, E j x ≤ p j x)
    (hhold : ∀ j x, S j x ≤ E j x * H x) :
    (∑' j, ∑' x, S j x) ≤ ∑' j, ∑' x, p j x * H x :=
  ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun x =>
    (hhold j x).trans (mul_le_mul_right' (hentry j x) (H x))

def windowProductBound (C : XCTM Q) : ℕ :=
  ∑ r : Rx C, ∑ s : Sp C, products C r s

theorem products_le_windowProductBound
    (C : XCTM Q) (r : Rx C) (s : Sp C) :
    products C r s ≤ windowProductBound C := by
  unfold windowProductBound
  calc
    products C r s ≤ ∑ t : Sp C, products C r t :=
      Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    _ ≤ ∑ t : Sp C, ∑ u : Rx C, products C u t :=
      Finset.sum_le_sum (fun t _ =>
        Finset.single_le_sum (f := fun u : Rx C => products C u t)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ r))
    _ = ∑ u : Rx C, ∑ t : Sp C, products C u t := Finset.sum_comm

theorem workCertificate_reachable_budget
    (C : XCTM Q) {start target : State (Sp C)}
    (P : WorkCertificate C start target)
    {z : State (Sp C)} (hz : WorkReach C start z) :
    ∀ s : Sp C,
      z s + P.rank z * windowProductBound C ≤
        start s + P.rank start * windowProductBound C := by
  have hclosed :
      ∀ x y : State (Sp C),
        (P.inv x ∧
          ∀ s : Sp C,
            x s + P.rank x * windowProductBound C ≤
              start s + P.rank start * windowProductBound C) →
        WorkStep C x y →
        (P.inv y ∧
          ∀ s : Sp C,
            y s + P.rank y * windowProductBound C ≤
              start s + P.rank start * windowProductBound C) := by
    rintro x y ⟨hx, hbudget⟩ ⟨r, hr, he, rfl⟩
    have hstep : WorkStep C x ((rxn C r).fire x) := ⟨r, hr, he, rfl⟩
    refine ⟨P.closed _ _ hx hstep, ?_⟩
    intro s
    have hdrop : P.rank ((rxn C r).fire x) + 1 ≤ P.rank x :=
      Nat.succ_le_iff.mpr (P.decreases _ _ hx hstep)
    have hdropMul :
        P.rank ((rxn C r).fire x) * windowProductBound C +
            windowProductBound C ≤ P.rank x * windowProductBound C := by
      simpa only [Nat.add_mul, one_mul] using
        Nat.mul_le_mul_right (windowProductBound C) hdrop
    have hfire : (rxn C r).fire x s ≤ x s + windowProductBound C := by
      rw [fire_apply]
      exact
        (Nat.add_le_add_right (Nat.sub_le _ _) _).trans
          (Nat.add_le_add_left (products_le_windowProductBound C r s) _)
    have hb := hbudget s
    omega
  have hfinal :=
    workReach_invariant C
      (fun y : State (Sp C) =>
        P.inv y ∧ ∀ s : Sp C,
          y s + P.rank y * windowProductBound C ≤
            start s + P.rank start * windowProductBound C)
      hclosed hz ⟨P.initial, fun _ => le_rfl⟩
  exact hfinal.2

theorem workCertificate_reachable_species_bound
    (C : XCTM Q) {start target : State (Sp C)}
    (P : WorkCertificate C start target)
    {z : State (Sp C)} (hz : WorkReach C start z)
    (s : Sp C) :
    z s ≤ start s + P.rank start * windowProductBound C := by
  have hb := workCertificate_reachable_budget C P hz s
  omega

theorem workCertificate_finite_reachable
    (C : XCTM Q) {start target : State (Sp C)}
    (P : WorkCertificate C start target) :
    Set.Finite {z : State (Sp C) | WorkReach C start z} := by
  classical
  let bound : Sp C → ℕ :=
    fun s => start s + P.rank start * windowProductBound C
  let encode :
      {z : State (Sp C) // WorkReach C start z} →
        ((s : Sp C) → Fin (bound s + 1)) :=
    fun z s => ⟨z.val s, Nat.lt_succ_of_le
      (workCertificate_reachable_species_bound C P z.property s)⟩
  have hencode : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    funext s
    exact congrArg Fin.val (congrFun h s)
  exact Set.finite_coe_iff.mp (Finite.of_injective encode hencode)

theorem next_window_finite_workReach
    (C : XCTM Q) (p : Plan C)
    (hs : 3 ≤ p.tape.length) (hh : Plan.halted C p = false) :
    Set.Finite
      {z : State (Sp C) |
        WorkReach C (Plan.workState C p + unit .signal) z} :=
  workCertificate_finite_reachable C (planCertificate C p hs hh)

theorem rawLaw_ae_label_ne_zero
    (C : XCTM Q) (z₀ : State (Sp C)) :
    ∀ᵐ ω ∂rawLaw (net C) (net_hasPositiveRates C) z₀,
      ∀ n : ℕ,
        massActionPMF (net C) (net_hasPositiveRates C)
          (pathState (net C) z₀ ω n) (ω (n + 1)) ≠ 0 := by
  classical
  rw [ae_iff]
  refine measure_mono_null ?_
    (rawLaw_null_label (net C) (net_hasPositiveRates C) z₀)
  intro ω hω
  change ¬ (∀ n : ℕ,
    massActionPMF (net C) (net_hasPositiveRates C)
      (pathState (net C) z₀ ω n) (ω (n + 1)) ≠ 0) at hω
  push_neg at hω
  obtain ⟨n, hn⟩ := hω
  refine ⟨n, ?_⟩
  change massActionPMF (net C) (net_hasPositiveRates C)
    (prefixToState (net C) z₀ n
      (fun k : Finset.Iic n => ω k.val)) (ω (n + 1)) = 0
  rw [prefixToState_eq_pathState (net C) z₀ ω n]
  exact hn

theorem rawLaw_ae_fired_eq_label
    (C : XCTM Q) (z₀ : State (Sp C)) :
    ∀ᵐ ω ∂rawLaw (net C) (net_hasPositiveRates C) z₀,
      ∀ n : ℕ, pathFired (net C) z₀ ω n = ω (n + 1) := by
  classical
  filter_upwards [rawLaw_ae_label_ne_zero C z₀] with ω hω
  intro n
  by_cases ht : (net C).Terminal (pathState (net C) z₀ ω n)
  · cases ho : ω (n + 1) with
    | none => simp only [pathFired, dif_pos ht, ho] <;> rfl
    | some r =>
        exfalso
        apply hω n
        change massActionWeight (net C) (net_hasPositiveRates C)
          (pathState (net C) z₀ ω n) (ω (n + 1)) = 0
        rw [ho]
        simp only [massActionWeight, dif_pos ht] <;> rfl
  · cases ho : ω (n + 1) with
    | none =>
        exfalso
        apply hω n
        change massActionWeight (net C) (net_hasPositiveRates C)
          (pathState (net C) z₀ ω n) (ω (n + 1)) = 0
        rw [ho]
        simp only [massActionWeight, dif_neg ht] <;> rfl
    | some r =>
        have he : (rxn C r).enabled (pathState (net C) z₀ ω n) := by
          by_contra hne
          have hp := jumpProbAt_eq_zero_of_not_enabled (net C) hne
          apply hω n
          change massActionWeight (net C) (net_hasPositiveRates C)
            (pathState (net C) z₀ ω n) (ω (n + 1)) = 0
          rw [ho]
          simp only [massActionWeight, dif_neg ht, hp]
          rw [← ENNReal.coe_nnratCast]
          norm_num
        simp only [pathFired, dif_neg ht, ho]
        exact congrArg (fun q : Rx C => some q)
          (fireOptionSanitized_of_enabled (net C) _ r ht he)

/-! ## Actual work-entry flux -/

namespace WindowAnalysis

abbrev WorkLabel (C : XCTM Q) := {r : Rx C // isClock r = false}

private def erasedWorkState (C : XCTM Q) (z : State (Sp C)) : ClocklessState C :=
  ⟨workView C z, by funext s; cases s <;> rfl⟩

def workSuccessor (C : XCTM Q) (x : ClocklessState C)
    (r : WorkLabel C) : ClocklessState C :=
  ⟨(rxn C r.val).fire x.val, by
    have h := work_fire_view C r.val x.val r.property
    simpa only [x.property] using h⟩

private theorem work_not_tick (C : XCTM Q) (r : WorkLabel C) :
    isTick r.val = false := by
  have hr := r.property
  cases h : r.val <;> simp_all [isClock, isTick]

private theorem work_fire_clock (C : XCTM Q) (r : WorkLabel C)
    (z : State (Sp C)) (c : Fin 5) :
    (rxn C r.val).fire z (.clock c) = z (.clock c) := by
  have hr := r.property
  cases h : r.val <;>
    simp_all [isClock, fire_apply, sourceLeft, sourceRight, products,
      unit, Pi.add_apply, Pi.smul_apply]

private theorem state_eq_of_workView_and_clocks (C : XCTM Q)
    {z z' : State (Sp C)} (hv : workView C z = workView C z')
    (hc : ∀ c : Fin 5, z (.clock c) = z' (.clock c)) : z = z' := by
  funext s
  have hs := congrFun hv s
  cases s with
  | clock c => exact hc c
  | _ => simpa only [workView] using hs

private theorem work_enabled_insert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (r : WorkLabel C) :
    (rxn C r.val).enabled (clockInsert C x c) ↔
      (rxn C r.val).enabled x.val := by
  simpa only [clockInsert_workView] using
    (work_enabled_view C r.val (clockInsert C x c) r.property).symm

private theorem work_fire_insert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (r : WorkLabel C) :
    (rxn C r.val).fire (clockInsert C x c) =
      clockInsert C (workSuccessor C x r) c := by
  apply state_eq_of_workView_and_clocks C
  · rw [work_fire_view C r.val _ r.property,
      clockInsert_workView, clockInsert_workView]
    rfl
  · intro d
    rw [work_fire_clock, clockInsert_clock, clockInsert_clock]

noncomputable def workEdgeRate (C : XCTM Q)
    (x y : ClocklessState C) : ℝ≥0∞ := by
  classical
  exact ∑ r : WorkLabel C,
    if (rxn C r.val).enabled x.val ∧ workSuccessor C x r = y then
      (rate C r.val x.val : ℝ≥0∞)
    else 0

private theorem windowEvent_work_step (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (z : State (Sp C))
    (r : WorkLabel C) {ω : LabelPath C}
    (hE : ω ∈ windowEvent C z₀ n j z)
    (ho : ω (n + 1) = some r.val) (he : (rxn C r.val).enabled z) :
    ω ∈ windowEntryEvent C z₀ (n + 1) (j + 1) ((rxn C r.val).fire z) := by
  have hNT : ¬ (net C).Terminal z := fun hT => hT r.val he
  have hstate : stateStep (net C) z (some r.val) = (rxn C r.val).fire z := by
    simp only [stateStep, dif_neg hNT]
    exact congrArg (fun q : Rx C => (rxn C q).fire z)
      (fireOptionSanitized_of_enabled (net C) z r.val hNT he)
  have hi := windowIncrement_of_work C z r.val r.property he
  have ht : windowTick C z (some r.val) = false := by
    simp only [windowTick, windowLabel_of_enabled C z r.val he,
      work_not_tick C r] <;> rfl
  have hEq : windowExtended C z₀ n ω = ((j, true), z) := hE
  have hnext : windowExtended C z₀ (n + 1) ω =
      ((j + 1, true), (rxn C r.val).fire z) := by
    change
      (windowUpdate C (windowExtended C z₀ n ω).1
          (windowExtended C z₀ n ω).2 (ω (n + 1)),
        stateStep (net C) (windowExtended C z₀ n ω).2 (ω (n + 1))) = _
    rw [hEq, ho]
    refine Prod.ext ?_ hstate
    change (j + windowIncrement C z (some r.val),
      true && !(windowTick C z (some r.val))) = (j + 1, true)
    rw [hi, ht] <;> rfl
  refine ⟨hnext, Or.inr ?_⟩
  change windowCount C z₀ ((n + 1) - 1) ω < j + 1
  rw [Nat.add_sub_cancel, windowEvent_count C z₀ n j z hE]
  exact Nat.lt_succ_self j

private theorem entryEvent_succ_iff_work (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (target : State (Sp C))
    (ω : LabelPath C)
    (hlaw : ∀ m, pathFired (net C) z₀ ω m = ω (m + 1)) :
    ω ∈ windowEntryEvent C z₀ (n + 1) (j + 1) target ↔
      ∃ (z : State (Sp C)) (r : WorkLabel C),
        ω ∈ windowEvent C z₀ n j z ∧
        ω (n + 1) = some r.val ∧ (rxn C r.val).enabled z ∧
        (rxn C r.val).fire z = target := by
  constructor
  · rintro ⟨hE, hprev⟩
    obtain ⟨hnew, hzero, htarget⟩ :=
      (windowEvent_iff C z₀ (n + 1) (j + 1) target ω).mp hE
    have hprevlt : windowCount C z₀ n ω < j + 1 := by
      rcases hprev with hbad | hprev
      · omega
      · simpa only [Nat.add_sub_cancel] using hprev
    have hsucc := windowCount_succ C z₀ n ω
    have hbound := windowIncrement_le_one C
      (windowState C z₀ n ω) (ω (n + 1))
    have hcount : windowCount C z₀ n ω = j := by omega
    have hinc : windowIncrement C (windowState C z₀ n ω) (ω (n + 1)) = 1 := by
      omega
    cases hF : pathFired (net C) z₀ ω n with
    | none =>
        have hlabel : windowLabel C (windowState C z₀ n ω) (ω (n + 1)) = none := by
          rw [windowState_eq_pathState, windowLabel_eq_pathFired, hF] <;> rfl
        simp only [windowIncrement, hlabel] at hinc
        omega
    | some r =>
        have hlabel : windowLabel C (windowState C z₀ n ω) (ω (n + 1)) = some r := by
          rw [windowState_eq_pathState, windowLabel_eq_pathFired, hF] <;> rfl
        have hr : isClock r = false := by
          by_contra hr
          have hz : windowIncrement C (windowState C z₀ n ω) (ω (n + 1)) = 0 := by
            unfold windowIncrement
            rw [hlabel]
            exact if_neg hr
          omega
        have hv := pathFired_valid (net C) z₀ ω n
        rw [hF] at hv
        have ho : ω (n + 1) = some r := (hlaw n).symm.trans hF
        have hmono : tickCount C z₀ ω n ≤ tickCount C z₀ ω (n + 1) :=
          tickCount_mono C z₀ ω (Nat.le_succ n)
        have ht : tickCount C z₀ ω n = 0 := by omega
        refine ⟨pathState (net C) z₀ ω n, ⟨r, hr⟩, ?_, ho, hv.1,
          hv.2.symm.trans htarget⟩
        exact (windowEvent_iff C z₀ n j _ ω).mpr ⟨hcount, ht, rfl⟩
  · rintro ⟨z, r, hE, ho, he, htarget⟩
    have h := windowEvent_work_step C z₀ n j z r hE ho he
    simpa only [htarget] using h

private noncomputable def workArrivalEvent (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (y : ClocklessState C) (c : Fin 5)
    (p : ClocklessState C × WorkLabel C) : Set (LabelPath C) := by
  classical
  exact if (rxn C p.2.val).enabled p.1.val ∧ workSuccessor C p.1 p.2 = y then
    windowEvent C z₀ n j (clockInsert C p.1 c) ∩
      {ω | ω (n + 1) = some p.2.val}
  else ∅

private theorem measurableSet_workArrivalEvent (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (y : ClocklessState C) (c : Fin 5)
    (p : ClocklessState C × WorkLabel C) :
    MeasurableSet (workArrivalEvent C z₀ n j y c p) := by
  classical
  unfold workArrivalEvent
  split_ifs
  · exact (measurableSet_windowEvent C z₀ n j _).inter
      (measurableSet_labelAt C n (some p.2.val))
  · exact MeasurableSet.empty

private theorem workArrivalEvents_pairwise (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (y : ClocklessState C) (c : Fin 5) :
    Pairwise (Function.onFun Disjoint (workArrivalEvent C z₀ n j y c)) := by
  classical
  intro p q hpq
  refine Set.disjoint_left.mpr ?_
  intro ω hp hq
  have hpcond : (rxn C p.2.val).enabled p.1.val ∧
      workSuccessor C p.1 p.2 = y := by
    by_contra h
    simp [workArrivalEvent, h] at hp
  have hqcond : (rxn C q.2.val).enabled q.1.val ∧
      workSuccessor C q.1 q.2 = y := by
    by_contra h
    simp [workArrivalEvent, h] at hq
  rw [workArrivalEvent, if_pos hpcond] at hp
  rw [workArrivalEvent, if_pos hqcond] at hq
  have hi : clockInsert C p.1 c = clockInsert C q.1 c :=
    (windowEvent_state C z₀ n j _ hp.1).symm.trans
      (windowEvent_state C z₀ n j _ hq.1)
  have hx : p.1 = q.1 := by
    apply Subtype.ext
    have h := congrArg (workView C) hi
    simpa only [clockInsert_workView] using h
  have hr : p.2 = q.2 :=
    Subtype.ext (Option.some.inj (hp.2.symm.trans hq.2))
  exact hpq (Prod.ext hx hr)

private theorem entryEvent_succ_ae_arrivals (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (y : ClocklessState C) (c : Fin 5) :
    windowEntryEvent C z₀ (n + 1) (j + 1) (clockInsert C y c)
      =ᵐ[windowLaw C z₀] ⋃ p, workArrivalEvent C z₀ n j y c p := by
  classical
  have hlegal : ∀ᵐ ω ∂windowLaw C z₀,
      ∀ m, pathFired (net C) z₀ ω m = ω (m + 1) :=
    rawLaw_ae_fired_eq_label C z₀
  filter_upwards [hlegal] with ω hω
  apply propext
  constructor
  · intro hentry
    obtain ⟨z, r, hE, ho, he, hfire⟩ :=
      (entryEvent_succ_iff_work C z₀ n j (clockInsert C y c) ω hω).mp hentry
    let x := erasedWorkState C z
    have hx : clockInsert C x c = z := by
      apply state_eq_of_workView_and_clocks C
      · rw [clockInsert_workView]
        rfl
      · intro d
        rw [clockInsert_clock]
        calc
          (if d = c then 1 else 0) = clockInsert C y c (.clock d) :=
            (clockInsert_clock C y c d).symm
          _ = (rxn C r.val).fire z (.clock d) := (congrFun hfire _).symm
          _ = z (.clock d) := work_fire_clock C r z d
    have hex : (rxn C r.val).enabled x.val :=
      (work_enabled_view C r.val z r.property).mpr he
    have hxy : workSuccessor C x r = y := by
      apply Subtype.ext
      change (rxn C r.val).fire (workView C z) = y.val
      rw [← work_fire_view C r.val z r.property, hfire, clockInsert_workView]
    refine Set.mem_iUnion.mpr ⟨(x, r), ?_⟩
    rw [workArrivalEvent, if_pos ⟨hex, hxy⟩]
    refine ⟨?_, ho⟩
    rw [hx]
    exact hE
  · intro harrival
    obtain ⟨⟨x, r⟩, hp⟩ := Set.mem_iUnion.mp harrival
    by_cases hcond : (rxn C r.val).enabled x.val ∧ workSuccessor C x r = y
    · rw [workArrivalEvent, if_pos hcond] at hp
      have he : (rxn C r.val).enabled (clockInsert C x c) :=
        (work_enabled_insert C x c r).mpr hcond.1
      have hfire : (rxn C r.val).fire (clockInsert C x c) =
          clockInsert C y c := by
        rw [work_fire_insert, hcond.2]
      exact (entryEvent_succ_iff_work C z₀ n j (clockInsert C y c) ω hω).mpr
        ⟨clockInsert C x c, r, hp.1, hp.2, he, hfire⟩
    · simp [workArrivalEvent, hcond] at hp

private theorem entryEvent_succ_arrival_mass (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (y : ClocklessState C) (c : Fin 5) :
    windowLaw C z₀
        (windowEntryEvent C z₀ (n + 1) (j + 1) (clockInsert C y c)) =
      ∑' p : ClocklessState C × WorkLabel C,
        windowLaw C z₀ (workArrivalEvent C z₀ n j y c p) := by
  calc
    windowLaw C z₀
        (windowEntryEvent C z₀ (n + 1) (j + 1) (clockInsert C y c)) =
        windowLaw C z₀ (⋃ p, workArrivalEvent C z₀ n j y c p) :=
      measure_congr (entryEvent_succ_ae_arrivals C z₀ n j y c)
    _ = _ := measure_iUnion (workArrivalEvents_pairwise C z₀ n j y c)
      (measurableSet_workArrivalEvent C z₀ n j y c)

/-- PMF normalization, before any work/clock specialization. -/
private theorem pmf_eq_rate_div_total (C : XCTM Q)
    (z : State (Sp C)) (r : Rx C) (he : (rxn C r).enabled z) :
    massActionPMF (net C) (net_hasPositiveRates C) z (some r) =
      (rate C r z : ℝ≥0∞) / ((net C).totalPropensity z : ℝ≥0∞) := by
  have hNT : ¬ (net C).Terminal z := fun ht => ht r he
  have hB := totalPropensity_ne_zero_of_nonTerminal
    (net C) (net_hasPositiveRates C) hNT
  have hq : jumpProbAt (net C) z r * (net C).totalPropensity z =
      (rate C r z : Rate) := by
    rw [jumpProbAt, div_mul_cancel₀ _ hB]
    exact propensity_rxn C r z
  have hNN : (jumpProbAt (net C) z r : NNReal) *
      ((net C).totalPropensity z : NNReal) = (rate C r z : NNReal) := by
    exact_mod_cast hq
  have hE : (jumpProbAt (net C) z r : ℝ≥0∞) *
      ((net C).totalPropensity z : ℝ≥0∞) = (rate C r z : ℝ≥0∞) := by
    simpa only [ENNReal.coe_mul, ENNReal.coe_nnratCast, ENNReal.coe_natCast] using
      congrArg (fun q : NNReal => (q : ℝ≥0∞)) hNN
  have hBzero : ((net C).totalPropensity z : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.coe_nnratCast, ENNReal.coe_ne_zero]
    exact_mod_cast hB
  have hBtop : ((net C).totalPropensity z : ℝ≥0∞) ≠ ⊤ := by
    rw [← ENNReal.coe_nnratCast]
    exact ENNReal.coe_ne_top
  change massActionWeight (net C) (net_hasPositiveRates C) z (some r) = _
  simp only [massActionWeight, dif_neg hNT]
  calc
    (jumpProbAt (net C) z r : ℝ≥0∞) =
        ((jumpProbAt (net C) z r : ℝ≥0∞) *
          ((net C).totalPropensity z : ℝ≥0∞)) /
            ((net C).totalPropensity z : ℝ≥0∞) :=
      (ENNReal.mul_div_cancel_right hBzero hBtop).symm
    _ = _ := by rw [hE]

private theorem work_pmf_insert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (r : WorkLabel C)
    (he : (rxn C r.val).enabled x.val) :
    massActionPMF (net C) (net_hasPositiveRates C)
        (clockInsert C x c) (some r.val) =
      (rate C r.val x.val : ℝ≥0∞) /
        ((net C).totalPropensity (clockInsert C x c) : ℝ≥0∞) := by
  rw [pmf_eq_rate_div_total C _ r.val ((work_enabled_insert C x c r).mpr he),
    work_rate_clockInsert C x c r.val r.property]

open Classical in
private theorem windowEntry_work_edge_sum (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (y : ClocklessState C) (c : Fin 5) :
    windowEntry C z₀ (j + 1) y c =
      ∑' p : ClocklessState C × WorkLabel C,
        if (rxn C p.2.val).enabled p.1.val ∧ workSuccessor C p.1 p.2 = y then
          (rate C p.2.val p.1.val : ℝ≥0∞) * windowOccupation C z₀ j p.1 c
        else 0 := by
  classical
  have hzero : windowEntryEvent C z₀ 0 (j + 1) (clockInsert C y c) = ∅ := by
    ext ω
    simp [windowEntryEvent, windowEvent, windowExtended, extState, extOf]
  calc
    windowEntry C z₀ (j + 1) y c =
        ∑' n, windowLaw C z₀
          (windowEntryEvent C z₀ (n + 1) (j + 1) (clockInsert C y c)) := by
      unfold windowEntry windowEntries
      rw [tsum_eq_zero_add' ENNReal.summable, hzero, measure_empty, zero_add]
    _ = ∑' n, ∑' p : ClocklessState C × WorkLabel C,
        windowLaw C z₀ (workArrivalEvent C z₀ n j y c p) :=
      tsum_congr (fun n => entryEvent_succ_arrival_mass C z₀ n j y c)
    _ = ∑' p : ClocklessState C × WorkLabel C, ∑' n,
        windowLaw C z₀ (workArrivalEvent C z₀ n j y c p) := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro p
      by_cases hp : (rxn C p.2.val).enabled p.1.val ∧ workSuccessor C p.1 p.2 = y
      · simp only [workArrivalEvent, if_pos hp]
        calc
          (∑' n, windowLaw C z₀
              (windowEvent C z₀ n j (clockInsert C p.1 c) ∩
                {ω | ω (n + 1) = some p.2.val})) =
              windowOcc C z₀ j (clockInsert C p.1 c) *
                massActionPMF (net C) (net_hasPositiveRates C)
                  (clockInsert C p.1 c) (some p.2.val) := by
            simp_rw [windowLaw_event_label]
            rw [ENNReal.tsum_mul_right]
            rfl
          _ = (rate C p.2.val p.1.val : ℝ≥0∞) *
              windowOccupation C z₀ j p.1 c := by
            rw [work_pmf_insert C p.1 c p.2 hp.1]
            unfold windowOccupation
            simp only [div_eq_mul_inv]
            ac_rfl
      · simp [workArrivalEvent, hp]

/-- T41 §8.2 / Lemma 8.3: actual work-entry recurrence, with no flow premise. -/
theorem windowEntry_work_recurrence (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (y : ClocklessState C) (c : Fin 5) :
    windowEntry C z₀ (j + 1) y c =
      ∑' x : ClocklessState C, workEdgeRate C x y * windowOccupation C z₀ j x c := by
  classical
  rw [windowEntry_work_edge_sum C z₀ j y c]
  rw [ENNReal.tsum_prod' (f := fun p : ClocklessState C × WorkLabel C =>
    if (rxn C p.2.val).enabled p.1.val ∧ workSuccessor C p.1 p.2 = y then
      (rate C p.2.val p.1.val : ℝ≥0∞) * windowOccupation C z₀ j p.1 c
    else 0)]
  apply tsum_congr
  intro x
  change (∑' r : WorkLabel C,
    if (rxn C r.val).enabled x.val ∧ workSuccessor C x r = y then
      (rate C r.val x.val : ℝ≥0∞) * windowOccupation C z₀ j x c else 0) =
    workEdgeRate C x y * windowOccupation C z₀ j x c
  rw [tsum_fintype]
  unfold workEdgeRate
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : (rxn C r.val).enabled x.val ∧ workSuccessor C x r = y
  · simp only [if_pos h] <;> rfl
  · simp only [if_neg h, zero_mul] <;> rfl

theorem windowEntry_work_series_ne_top (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (y : ClocklessState C) (c : Fin 5) :
    (∑' x : ClocklessState C,
      workEdgeRate C x y * windowOccupation C z₀ j x c) ≠ ⊤ := by
  rw [← windowEntry_work_recurrence C z₀ j y c]
  exact windowEntry_ne_top C z₀ (j + 1) y c

/-! ## Clock support and exact incoming clock moves -/

/-- Total number of clock molecules, not a claimed clock position. -/
def clockMoleculeCount (C : XCTM Q) (z : State (Sp C)) : ℕ :=
  ∑ c : Fin 5, z (.clock c)

theorem clockMoleculeCount_fire (C : XCTM Q) (r : Rx C)
    (z : State (Sp C)) (he : (rxn C r).enabled z) :
    clockMoleculeCount C ((rxn C r).fire z) = clockMoleculeCount C z := by
  have hp := (enabled_iff C r z).mp he
  have hl : 0 < z (sourceLeft C r) := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hp
    simp [rate, hz]
  cases r with
  | tick latent =>
      cases latent <;>
        simp [sourceLeft] at hl <;>
        simp [clockMoleculeCount, Fin.sum_univ_succ, fire_apply,
          sourceLeft, sourceRight, products, unit, Pi.add_apply, Pi.smul_apply] <;>
        omega
  | up c latent =>
      fin_cases c <;> cases latent <;>
        simp [sourceLeft] at hl <;>
        simp [clockMoleculeCount, Fin.sum_univ_succ, fire_apply,
          sourceLeft, sourceRight, products, unit, Pi.add_apply, Pi.smul_apply] <;>
        omega
  | down c latent =>
      fin_cases c <;> cases latent <;>
        simp [sourceLeft] at hl <;>
        simp [clockMoleculeCount, Fin.sum_univ_succ, fire_apply,
          sourceLeft, sourceRight, products, unit, Pi.add_apply, Pi.smul_apply] <;>
        omega
  | _ =>
      simp [clockMoleculeCount, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.add_apply, Pi.smul_apply]

/-- Sanitization also preserves the clock count: it fires only enabled reactions. -/
theorem clockMoleculeCount_path (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (n : ℕ) :
    clockMoleculeCount C (pathState (net C) z₀ ω n) = clockMoleculeCount C z₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hv := pathFired_valid (net C) z₀ ω n
      cases hF : pathFired (net C) z₀ ω n with
      | none =>
          simp only [hF] at hv
          rw [hv.1]
          exact ih
      | some r =>
          simp only [hF] at hv
          rw [hv.2]
          change clockMoleculeCount C
            ((rxn C r).fire (pathState (net C) z₀ ω n)) = clockMoleculeCount C z₀
          exact (clockMoleculeCount_fire C r _ hv.1).trans ih

theorem clockMoleculeCount_path_one (C : XCTM Q) (z₀ : State (Sp C))
    (h₀ : clockMoleculeCount C z₀ = 1) (ω : LabelPath C) (n : ℕ) :
    clockMoleculeCount C (pathState (net C) z₀ ω n) = 1 := by
  rw [clockMoleculeCount_path, h₀]

private abbrev ClockMove := Bool × (Fin 4 × Bool)

private def clockMoveRx (C : XCTM Q) (p : ClockMove) : Rx C :=
  if p.1 then .up p.2.1 p.2.2 else .down p.2.1 p.2.2

private def clockMoveSource (p : ClockMove) : Fin 5 :=
  if p.1 then p.2.1.castSucc else p.2.1.succ

private def clockMoveTarget (p : ClockMove) : Fin 5 :=
  if p.1 then p.2.1.succ else p.2.1.castSucc

private def clockMoveCatalyst (C : XCTM Q) (p : ClockMove) : Sp C :=
  if p.1 then
    if p.2.2 then .forwardLatent else .forward
  else
    if p.2.2 then .backwardLatent else .backward

private theorem clockMove_isClock (C : XCTM Q) (p : ClockMove) :
    isClock (clockMoveRx C p) = true := by
  rcases p with ⟨b, i, latent⟩
  cases b <;> rfl

private theorem clockMove_notTick (C : XCTM Q) (p : ClockMove) :
    isTick (clockMoveRx C p) = false := by
  rcases p with ⟨b, i, latent⟩
  cases b <;> rfl

private theorem clockMoveRx_injective (C : XCTM Q) :
    Function.Injective (clockMoveRx C) := by
  rintro ⟨b, i, latent⟩ ⟨b', i', latent'⟩ h
  cases b <;> cases b' <;> simp [clockMoveRx] at h
  all_goals
    rcases h with ⟨rfl, rfl⟩
    rfl

private theorem clockMove_cases (C : XCTM Q) (r : Rx C)
    (hc : isClock r = true) (ht : isTick r = false) :
    ∃ p : ClockMove, r = clockMoveRx C p := by
  cases r with
  | up i latent => exact ⟨(true, i, latent), rfl⟩
  | down i latent => exact ⟨(false, i, latent), rfl⟩
  | _ => simp_all [isClock, isTick]

private theorem clockMove_rate (C : XCTM Q) (x : ClocklessState C)
    (p : ClockMove) :
    rate C (clockMoveRx C p) (clockInsert C x (clockMoveSource p)) =
      x.val (clockMoveCatalyst C p) := by
  rcases p with ⟨b, i, latent⟩
  cases b <;> cases latent <;>
    simp [clockMoveRx, clockMoveSource, clockMoveCatalyst, rate,
      sourceLeft, sourceRight, clockInsert, unit, clockless_clock_zero]

private theorem clockMove_enabled (C : XCTM Q) (x : ClocklessState C)
    (p : ClockMove) (hp : 0 < x.val (clockMoveCatalyst C p)) :
    (rxn C (clockMoveRx C p)).enabled (clockInsert C x (clockMoveSource p)) := by
  rw [enabled_iff, clockMove_rate]
  exact Nat.ne_of_gt hp

private theorem clockMove_fire (C : XCTM Q) (x : ClocklessState C)
    (p : ClockMove) (hp : 0 < x.val (clockMoveCatalyst C p)) :
    (rxn C (clockMoveRx C p)).fire (clockInsert C x (clockMoveSource p)) =
      clockInsert C x (clockMoveTarget p) := by
  rcases p with ⟨b, i, latent⟩
  cases b <;> cases latent <;>
    simp [clockMoveCatalyst] at hp
  all_goals
    funext s
    cases s <;>
      simp [clockMoveRx, clockMoveSource, clockMoveTarget, clockInsert,
        fire_apply, sourceLeft, sourceRight, products, unit,
        clockless_clock_zero, Pi.add_apply, Pi.smul_apply] <;> omega

private theorem fire_injective_of_enabled (C : XCTM Q) (r : Rx C)
    {z z' : State (Sp C)} (hz : (rxn C r).enabled z)
    (hz' : (rxn C r).enabled z')
    (h : (rxn C r).fire z = (rxn C r).fire z') : z = z' := by
  funext s
  have hleft := hz s
  have hright := hz' s
  have heq := congrFun h s
  change (rxn C r).l s ≤ z s at hleft
  change (rxn C r).l s ≤ z' s at hright
  change z s - (rxn C r).l s + (rxn C r).r s =
    z' s - (rxn C r).l s + (rxn C r).r s at heq
  omega

/-- Reverse identification of a one-clock destination; no assumption on z₀. -/
private theorem clockMove_predecessor (C : XCTM Q) (x : ClocklessState C)
    (c : Fin 5) (p : ClockMove) (z : State (Sp C))
    (he : (rxn C (clockMoveRx C p)).enabled z)
    (hfire : (rxn C (clockMoveRx C p)).fire z = clockInsert C x c) :
    clockMoveTarget p = c ∧ z = clockInsert C x (clockMoveSource p) ∧
      0 < x.val (clockMoveCatalyst C p) := by
  have hv : workView C z = x.val := by
    calc
      workView C z = workView C ((rxn C (clockMoveRx C p)).fire z) :=
        (clock_move_workView C _ z (clockMove_isClock C p)
          (clockMove_notTick C p) he).symm
      _ = x.val := by rw [hfire, clockInsert_workView]
  have hcatEq : z (clockMoveCatalyst C p) = x.val (clockMoveCatalyst C p) := by
    have h := congrFun hv (clockMoveCatalyst C p)
    rcases p with ⟨b, i, latent⟩
    cases b <;> cases latent <;> simpa [clockMoveCatalyst, workView] using h
  have hr : rate C (clockMoveRx C p) z =
      z (.clock (clockMoveSource p)) * z (clockMoveCatalyst C p) := by
    rcases p with ⟨b, i, latent⟩
    cases b <;> cases latent <;> rfl
  have hp := (enabled_iff C (clockMoveRx C p) z).mp he
  rw [hr] at hp
  have hcat : 0 < x.val (clockMoveCatalyst C p) := by
    rw [← hcatEq]
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hp (by simp [hzero])
  have hout : 0 < (rxn C (clockMoveRx C p)).fire z (.clock (clockMoveTarget p)) := by
    rcases p with ⟨b, i, latent⟩
    cases b <;> cases latent <;>
      simp [clockMoveRx, clockMoveTarget, fire_apply, sourceLeft,
        sourceRight, products, unit, Pi.add_apply] <;> omega
  have hc : clockMoveTarget p = c := by
    by_contra hne
    have h := congrFun hfire (.clock (clockMoveTarget p))
    rw [clockInsert_clock, if_neg hne] at h
    omega
  have hsame : (rxn C (clockMoveRx C p)).fire z =
      (rxn C (clockMoveRx C p)).fire (clockInsert C x (clockMoveSource p)) := by
    rw [clockMove_fire C x p hcat, hc]
    exact hfire
  exact ⟨hc, fire_injective_of_enabled C _ he (clockMove_enabled C x p hcat) hsame, hcat⟩

private theorem windowEvent_clock_step (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (x : ClocklessState C) (p : ClockMove)
    (hp : 0 < x.val (clockMoveCatalyst C p)) {ω : LabelPath C}
    (hE : ω ∈ windowEvent C z₀ n j (clockInsert C x (clockMoveSource p)))
    (ho : ω (n + 1) = some (clockMoveRx C p)) :
    ω ∈ windowInternalEvent C z₀ n j (clockInsert C x (clockMoveTarget p)) := by
  let z := clockInsert C x (clockMoveSource p)
  have he : (rxn C (clockMoveRx C p)).enabled z := clockMove_enabled C x p hp
  have hNT : ¬ (net C).Terminal z := fun ht => ht _ he
  have hs : stateStep (net C) z (some (clockMoveRx C p)) =
      clockInsert C x (clockMoveTarget p) := by
    simp only [stateStep, dif_neg hNT]
    calc
      (rxn C (fireOptionSanitized (net C) z (some (clockMoveRx C p)) hNT)).fire z =
          (rxn C (clockMoveRx C p)).fire z :=
        congrArg (fun r : Rx C => (rxn C r).fire z)
          (fireOptionSanitized_of_enabled (net C) z _ hNT he)
      _ = _ := clockMove_fire C x p hp
  have hi : windowIncrement C z (some (clockMoveRx C p)) = 0 := by
    simp [windowIncrement, windowLabel_of_enabled C z _ he, clockMove_isClock]
  have ht : windowTick C z (some (clockMoveRx C p)) = false := by
    simp [windowTick, windowLabel_of_enabled C z _ he, clockMove_notTick]
  have hEq : windowExtended C z₀ n ω = ((j, true), z) := hE
  refine ⟨?_, windowEvent_count C z₀ n j z hE⟩
  change
    (windowUpdate C (windowExtended C z₀ n ω).1
        (windowExtended C z₀ n ω).2 (ω (n + 1)),
      stateStep (net C) (windowExtended C z₀ n ω).2 (ω (n + 1))) = _
  rw [hEq, ho]
  refine Prod.ext ?_ hs
  change (j + windowIncrement C z (some (clockMoveRx C p)),
    true && !(windowTick C z (some (clockMoveRx C p)))) = (j, true)
  rw [hi, ht] <;> rfl

private noncomputable def clockArrivalEvent (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (p : ClockMove) : Set (LabelPath C) := by
  classical
  exact if clockMoveTarget p = c ∧ 0 < x.val (clockMoveCatalyst C p) then
    windowEvent C z₀ n j (clockInsert C x (clockMoveSource p)) ∩
      {ω | ω (n + 1) = some (clockMoveRx C p)}
  else ∅

private theorem measurableSet_clockArrivalEvent (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (p : ClockMove) : MeasurableSet (clockArrivalEvent C z₀ n j x c p) := by
  classical
  unfold clockArrivalEvent
  split_ifs
  · exact (measurableSet_windowEvent C z₀ n j _).inter
      (measurableSet_labelAt C n (some (clockMoveRx C p)))
  · exact MeasurableSet.empty

private theorem clockArrivalEvents_pairwise (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (x : ClocklessState C) (c : Fin 5) :
    Pairwise (Function.onFun Disjoint (clockArrivalEvent C z₀ n j x c)) := by
  classical
  intro p q hpq
  refine Set.disjoint_left.mpr ?_
  intro ω hp hq
  have hpcond : clockMoveTarget p = c ∧ 0 < x.val (clockMoveCatalyst C p) := by
    by_contra h
    simp [clockArrivalEvent, h] at hp
  have hqcond : clockMoveTarget q = c ∧ 0 < x.val (clockMoveCatalyst C q) := by
    by_contra h
    simp [clockArrivalEvent, h] at hq
  rw [clockArrivalEvent, if_pos hpcond] at hp
  rw [clockArrivalEvent, if_pos hqcond] at hq
  exact hpq (clockMoveRx_injective C (Option.some.inj (hp.2.symm.trans hq.2)))

private theorem internalEvent_ae_clockArrivals (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (hn : ¬ WorkTerminal C x.val) :
    windowInternalEvent C z₀ n j (clockInsert C x c)
      =ᵐ[windowLaw C z₀] ⋃ p, clockArrivalEvent C z₀ n j x c p := by
  classical
  have hlegal : ∀ᵐ ω ∂windowLaw C z₀,
      ∀ m, pathFired (net C) z₀ ω m = ω (m + 1) :=
    rawLaw_ae_fired_eq_label C z₀
  filter_upwards [hlegal] with ω hω
  apply propext
  constructor
  · rintro ⟨hE, hj⟩
    change windowCount C z₀ n ω = j at hj
    obtain ⟨hnext, hzero, hstate⟩ :=
      (windowEvent_iff C z₀ (n + 1) j (clockInsert C x c) ω).mp hE
    have hinc : windowIncrement C (windowState C z₀ n ω) (ω (n + 1)) = 0 := by
      have hs := windowCount_succ C z₀ n ω
      rw [hj, hnext] at hs
      omega
    have hv := pathFired_valid (net C) z₀ ω n
    cases hF : pathFired (net C) z₀ ω n with
    | none =>
        simp only [hF] at hv
        have heq : pathState (net C) z₀ ω n = clockInsert C x c :=
          hv.1.symm.trans hstate
        have hterminal : (net C).Terminal (clockInsert C x c) := by
          rw [← heq]
          exact hv.2
        have hwork : WorkTerminal C (clockInsert C x c) :=
          fun r _ => hterminal r
        exact False.elim (hn ((workTerminal_clockInsert C x c).mp hwork))
    | some r =>
        simp only [hF] at hv
        have hlabel : windowLabel C (windowState C z₀ n ω) (ω (n + 1)) = some r := by
          rw [windowState_eq_pathState, windowLabel_eq_pathFired, hF] <;> rfl
        have hc : isClock r = true := by
          cases hclock : isClock r with
          | false =>
              have hi : windowIncrement C (windowState C z₀ n ω) (ω (n + 1)) = 1 := by
                simp only [windowIncrement, hlabel, hclock, if_true] <;> rfl
              omega
          | true => rfl
        have ht : isTick r = false := by
          cases htick : isTick r with
          | false => rfl
          | true =>
              have hTick : TickAt C z₀ ω n := by
                simp [TickAt, firedTick, hF, htick]
              have hsucc := tickCount_succ_of_tick C z₀ ω n hTick
              omega
        obtain ⟨p, rfl⟩ := clockMove_cases C r hc ht
        have hfire : (rxn C (clockMoveRx C p)).fire (pathState (net C) z₀ ω n) =
            clockInsert C x c := hv.2.symm.trans hstate
        obtain ⟨hp, hsrc, hcat⟩ := clockMove_predecessor C x c p _ hv.1 hfire
        have hmono : tickCount C z₀ ω n ≤ tickCount C z₀ ω (n + 1) :=
          tickCount_mono C z₀ ω (Nat.le_succ n)
        have hprevTick : tickCount C z₀ ω n = 0 := by omega
        have hprev : ω ∈ windowEvent C z₀ n j (clockInsert C x (clockMoveSource p)) :=
          (windowEvent_iff C z₀ n j _ ω).mpr ⟨hj, hprevTick, hsrc⟩
        have ho : ω (n + 1) = some (clockMoveRx C p) := (hω n).symm.trans hF
        refine Set.mem_iUnion.mpr ⟨p, ?_⟩
        rw [clockArrivalEvent, if_pos ⟨hp, hcat⟩]
        exact ⟨hprev, ho⟩
  · intro harrival
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp harrival
    by_cases hcond : clockMoveTarget p = c ∧ 0 < x.val (clockMoveCatalyst C p)
    · rw [clockArrivalEvent, if_pos hcond] at hp
      have h := windowEvent_clock_step C z₀ n j x p hcond.2 hp.1 hp.2
      simpa only [hcond.1] using h
    · simp [clockArrivalEvent, hcond] at hp

private theorem internalEvent_clock_arrival_mass (C : XCTM Q)
    (z₀ : State (Sp C)) (n j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (hn : ¬ WorkTerminal C x.val) :
    windowLaw C z₀ (windowInternalEvent C z₀ n j (clockInsert C x c)) =
      ∑' p : ClockMove, windowLaw C z₀ (clockArrivalEvent C z₀ n j x c p) := by
  calc
    windowLaw C z₀ (windowInternalEvent C z₀ n j (clockInsert C x c)) =
        windowLaw C z₀ (⋃ p, clockArrivalEvent C z₀ n j x c p) :=
      measure_congr (internalEvent_ae_clockArrivals C z₀ n j x c hn)
    _ = _ := measure_iUnion (clockArrivalEvents_pairwise C z₀ n j x c)
      (measurableSet_clockArrivalEvent C z₀ n j x c)

private theorem windowInternalMass_move_sum (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (hn : ¬ WorkTerminal C x.val) :
    windowInternalMass C z₀ j (clockInsert C x c) =
      ∑ p : ClockMove, if clockMoveTarget p = c then
        (x.val (clockMoveCatalyst C p) : ℝ≥0∞) *
          windowOccupation C z₀ j x (clockMoveSource p) else 0 := by
  classical
  calc
    windowInternalMass C z₀ j (clockInsert C x c) =
        ∑' n, ∑' p : ClockMove,
          windowLaw C z₀ (clockArrivalEvent C z₀ n j x c p) :=
      tsum_congr (fun n => internalEvent_clock_arrival_mass C z₀ n j x c hn)
    _ = ∑' p : ClockMove, ∑' n,
        windowLaw C z₀ (clockArrivalEvent C z₀ n j x c p) := ENNReal.tsum_comm
    _ = ∑' p : ClockMove, if clockMoveTarget p = c then
        (x.val (clockMoveCatalyst C p) : ℝ≥0∞) *
          windowOccupation C z₀ j x (clockMoveSource p) else 0 := by
      apply tsum_congr
      intro p
      by_cases hc : clockMoveTarget p = c
      · by_cases hp : 0 < x.val (clockMoveCatalyst C p)
        · have hcond : clockMoveTarget p = c ∧
              0 < x.val (clockMoveCatalyst C p) := ⟨hc, hp⟩
          simp only [clockArrivalEvent, if_pos hcond, if_pos hc]
          simp_rw [windowLaw_event_label]
          rw [ENNReal.tsum_mul_right]
          change windowOcc C z₀ j (clockInsert C x (clockMoveSource p)) *
            massActionPMF (net C) (net_hasPositiveRates C)
              (clockInsert C x (clockMoveSource p)) (some (clockMoveRx C p)) = _
          rw [pmf_eq_rate_div_total C _ _ (clockMove_enabled C x p hp), clockMove_rate]
          unfold windowOccupation
          simp only [div_eq_mul_inv]
          ac_rfl
        · have hz : x.val (clockMoveCatalyst C p) = 0 := Nat.eq_zero_of_not_pos hp
          simp [clockArrivalEvent, hc, hp, hz]
      · simp [clockArrivalEvent, hc]
    _ = _ := tsum_fintype _

/-- Zero extension gives the Nat-indexed vector expected by ClockBalance. -/
noncomputable def windowOccupationVector (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : ℕ) : ℝ≥0∞ :=
  if h : c < 5 then windowOccupation C z₀ j x ⟨c, h⟩ else 0

noncomputable def windowEntryVector (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : ℕ) : ℝ≥0∞ :=
  if h : c < 5 then windowEntry C z₀ j x ⟨c, h⟩ else 0

/-- Actual internal occupation mass is exactly the two neighboring clock inflows. -/
theorem windowInternalMass_clock_inflows (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (hn : ¬ WorkTerminal C x.val) :
    windowInternalMass C z₀ j (clockInsert C x c) =
      (if 0 < c.val then (forwardCount C x.val : ℝ≥0∞) *
        windowOccupationVector C z₀ j x (c.val - 1) else 0) +
      (if c.val + 1 < 5 then (backwardCount C x.val : ℝ≥0∞) *
        windowOccupationVector C z₀ j x (c.val + 1) else 0) := by
  rw [windowInternalMass_move_sum C z₀ j x c hn]
  fin_cases c <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
      clockMoveTarget, clockMoveSource, clockMoveCatalyst,
      windowOccupationVector, forwardCount, backwardCount,
      Nat.cast_add, add_mul] <;> ac_rfl

/-! ## Full-network rate decomposition -/

private def reactionSplitEquiv (C : XCTM Q) :
    (WorkLabel C ⊕ (Bool ⊕ ClockMove)) ≃ Rx C where
  toFun
    | .inl r => r.val
    | .inr (.inl b) => .tick b
    | .inr (.inr p) => clockMoveRx C p
  invFun r :=
    if h : isClock r = false then .inl ⟨r, h⟩ else
      match r with
      | .tick b => .inr (.inl b)
      | .up i b => .inr (.inr (true, i, b))
      | .down i b => .inr (.inr (false, i, b))
      | _ => .inr (.inl false)
  left_inv := by
    intro u
    rcases u with r | (b | ⟨b, i, latent⟩)
    · simp [r.property]
    · simp [isClock]
    · cases b <;> simp [clockMoveRx, isClock]
  right_inv := by
    intro r
    cases r <;> simp [isClock, clockMoveRx]

/-- Keep network syntax out of the subsequent finite clock summation. -/
private theorem tick_rate_clockInsert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (b : Bool) :
    rate C (.tick b) (clockInsert C x c) =
      if (0 : Fin 5) = c then
        x.val (if b then .backwardLatent else .backward) else 0 := by
  cases b <;>
    simp [rate, sourceLeft, sourceRight, clockInsert, unit,
      clockless_clock_zero, ite_mul]

private theorem clockMove_rate_at (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (p : ClockMove) :
    rate C (clockMoveRx C p) (clockInsert C x c) =
      if clockMoveSource p = c then x.val (clockMoveCatalyst C p) else 0 := by
  rcases p with ⟨b, i, latent⟩
  cases b <;> cases latent <;>
    simp [clockMoveRx, clockMoveSource, clockMoveCatalyst, rate,
      sourceLeft, sourceRight, clockInsert, unit, clockless_clock_zero, ite_mul]

private theorem tick_rate_clockInsert_val (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (b : Bool) :
    rate C (.tick b) (clockInsert C x c) =
      if 0 = c.val then x.val (if b then .backwardLatent else .backward) else 0 := by
  simpa only [Fin.ext_iff] using tick_rate_clockInsert C x c b

private theorem clockMove_rate_at_val (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (p : ClockMove) :
    rate C (clockMoveRx C p) (clockInsert C x c) =
      if (clockMoveSource p).val = c.val then x.val (clockMoveCatalyst C p) else 0 := by
  simpa only [Fin.ext_iff] using clockMove_rate_at C x c p

/-- A scalar identity: no reaction syntax or Fin-valued equality remains. -/
private theorem clock_channel_masks (a f c : ℕ) (hc : c < 5) :
    (if 0 = c then f else 0) +
      ((∑ i : Fin 4, if i.val = c then a else 0) +
        ∑ i : Fin 4, if i.val + 1 = c then f else 0) =
      f + (if c + 1 < 5 then a else 0) := by
  interval_cases c <;> norm_num [Fin.sum_univ_succ] <;> omega

/-- Evaluate the clock channels while the clock position is still generic. -/
private theorem clock_rates_total (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) :
    ((∑ b : Bool, rate C (.tick b) (clockInsert C x c)) +
      ∑ p : ClockMove, rate C (clockMoveRx C p) (clockInsert C x c)) =
      backwardCount C x.val +
        (if c.val + 1 < 5 then forwardCount C x.val else 0) := by
  classical
  have htick : (∑ b : Bool, rate C (.tick b) (clockInsert C x c)) =
      if 0 = c.val then backwardCount C x.val else 0 := by
    rw [Fintype.sum_bool, tick_rate_clockInsert_val, tick_rate_clockInsert_val]
    by_cases h : 0 = c.val <;> simp [h, backwardCount, add_comm]
  have hmove : (∑ p : ClockMove, rate C (clockMoveRx C p) (clockInsert C x c)) =
      (∑ i : Fin 4, if i.val = c.val then forwardCount C x.val else 0) +
        ∑ i : Fin 4, if i.val + 1 = c.val then backwardCount C x.val else 0 := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fintype.sum_prod_type]
    apply congrArg₂ (fun a b : ℕ => a + b)
    · apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool, clockMove_rate_at_val, clockMove_rate_at_val]
      change (if i.val = c.val then x.val .forwardLatent else 0) +
          (if i.val = c.val then x.val .forward else 0) =
        if i.val = c.val then forwardCount C x.val else 0
      by_cases h : i.val = c.val <;> simp [h, forwardCount, add_comm]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool, clockMove_rate_at_val, clockMove_rate_at_val]
      change (if i.val + 1 = c.val then x.val .backwardLatent else 0) +
          (if i.val + 1 = c.val then x.val .backward else 0) =
        if i.val + 1 = c.val then backwardCount C x.val else 0
      by_cases h : i.val + 1 = c.val <;> simp [h, backwardCount, add_comm]
  rw [htick, hmove]
  exact clock_channel_masks (forwardCount C x.val) (backwardCount C x.val) c.val c.isLt

/-- At a one-clock state: work rate + one backward channel + the upward channel. -/
theorem totalPropensity_clockInsert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) :
    (net C).totalPropensity (clockInsert C x c) =
      ((StandaloneWork.totalWorkRate C x.val + backwardCount C x.val +
        (if c.val + 1 < 5 then forwardCount C x.val else 0) : ℕ) : Rate) := by
  classical
  have hsplit : (∑ r : Rx C, rate C r (clockInsert C x c)) =
      (∑ r : WorkLabel C, rate C r.val (clockInsert C x c)) +
        ((∑ b : Bool, rate C (.tick b) (clockInsert C x c)) +
          ∑ p : ClockMove, rate C (clockMoveRx C p) (clockInsert C x c)) := by
    calc
      (∑ r : Rx C, rate C r (clockInsert C x c)) =
          ∑ u : WorkLabel C ⊕ (Bool ⊕ ClockMove),
            rate C ((reactionSplitEquiv C) u) (clockInsert C x c) :=
        ((reactionSplitEquiv C).sum_comp
          (fun r => rate C r (clockInsert C x c))).symm
      _ = _ := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type] <;> rfl
  have hwork : (∑ r : WorkLabel C, rate C r.val (clockInsert C x c)) =
      StandaloneWork.totalWorkRate C x.val := by
    change (∑ r : WorkLabel C, rate C r.val (clockInsert C x c)) =
      ∑ r : WorkLabel C, rate C r.val x.val
    apply Finset.sum_congr rfl
    intro r _
    exact work_rate_clockInsert C x c r.val r.property
  have hclock :
      ((∑ b : Bool, rate C (.tick b) (clockInsert C x c)) +
        ∑ p : ClockMove, rate C (clockMoveRx C p) (clockInsert C x c)) =
      backwardCount C x.val +
        (if c.val + 1 < 5 then forwardCount C x.val else 0) :=
    clock_rates_total C x c
  have hsum : (∑ r : Rx C, rate C r (clockInsert C x c)) =
      StandaloneWork.totalWorkRate C x.val + backwardCount C x.val +
        (if c.val + 1 < 5 then forwardCount C x.val else 0) := by
    rw [hsplit, hwork, hclock, add_assoc]
  change (∑ r : Rx C, (rxn C r).propensity (clockInsert C x c)) = _
  simp_rw [propensity_rxn]
  change (∑ r : Rx C, (rate C r (clockInsert C x c) : Rate)) = _
  rw [← Nat.cast_sum, hsum]

/-- The actual physical balance in extended nonnegative reals. -/
theorem windowOccupation_physical_balance_enn (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C)
    (hn : ¬ WorkTerminal C x.val) (c : ℕ) (hc : c < 5) :
    ((StandaloneWork.totalWorkRate C x.val + backwardCount C x.val +
      (if c + 1 < 5 then forwardCount C x.val else 0) : ℕ) : ℝ≥0∞) *
        windowOccupationVector C z₀ j x c =
      windowEntryVector C z₀ j x c +
        (if 0 < c then (forwardCount C x.val : ℝ≥0∞) *
          windowOccupationVector C z₀ j x (c - 1) else 0) +
        (if c + 1 < 5 then (backwardCount C x.val : ℝ≥0∞) *
          windowOccupationVector C z₀ j x (c + 1) else 0) := by
  let k : Fin 5 := ⟨c, hc⟩
  have hNT : ¬ (net C).Terminal (clockInsert C x k) := by
    intro ht
    apply hn
    apply (workTerminal_clockInsert C x k).mp
    intro r _
    exact ht r
  have hB := totalPropensity_ne_zero_of_nonTerminal
    (net C) (net_hasPositiveRates C) hNT
  have hBzero : ((net C).totalPropensity (clockInsert C x k) : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.coe_nnratCast, ENNReal.coe_ne_zero]
    exact_mod_cast hB
  have hBtop : ((net C).totalPropensity (clockInsert C x k) : ℝ≥0∞) ≠ ⊤ := by
    rw [← ENNReal.coe_nnratCast]
    exact ENNReal.coe_ne_top
  have hocc : windowOcc C z₀ j (clockInsert C x k) =
      ((net C).totalPropensity (clockInsert C x k) : ℝ≥0∞) *
        windowOccupation C z₀ j x k :=
    (ENNReal.mul_div_cancel hBzero hBtop).symm
  have hrateNN : ((net C).totalPropensity (clockInsert C x k) : NNReal) =
      ((StandaloneWork.totalWorkRate C x.val + backwardCount C x.val +
        (if k.val + 1 < 5 then forwardCount C x.val else 0) : ℕ) : NNReal) := by
    rw [totalPropensity_clockInsert C x k]
    try simp
    try (split_ifs <;> simp)
  have hrateE : ((net C).totalPropensity (clockInsert C x k) : ℝ≥0∞) =
      ((StandaloneWork.totalWorkRate C x.val + backwardCount C x.val +
        (if k.val + 1 < 5 then forwardCount C x.val else 0) : ℕ) : ℝ≥0∞) := by
    simpa only [ENNReal.coe_nnratCast, ENNReal.coe_natCast] using
      congrArg (fun q : NNReal => (q : ℝ≥0∞)) hrateNN
  have hbal := windowOcc_balance C z₀ j (clockInsert C x k)
  rw [hocc, hrateE, windowInternalMass_clock_inflows C z₀ j x k hn] at hbal
  simpa only [k, windowOccupationVector, windowEntryVector, dif_pos hc,
    windowEntry, add_assoc] using hbal

noncomputable def windowOccupationReal (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : ℕ) : ℝ :=
  (windowOccupationVector C z₀ j x c).toReal

noncomputable def windowEntryReal (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (c : ℕ) : ℝ :=
  (windowEntryVector C z₀ j x c).toReal

/-- No toReal-of-infinity shortcut: finiteness is proved before converting the balance. -/
theorem windowOccupation_physical_balance (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C)
    (hn : ¬ WorkTerminal C x.val) :
    PhysicalBalance (forwardCount C x.val : ℝ) (backwardCount C x.val : ℝ)
      (StandaloneWork.totalWorkRate C x.val : ℝ)
      (windowOccupationReal C z₀ j x) (windowEntryReal C z₀ j x) := by
  have hwfin : ∀ k, windowOccupationVector C z₀ j x k ≠ ⊤ := by
    intro k
    by_cases hk : k < 5
    · simpa only [windowOccupationVector, dif_pos hk] using
        windowOccupation_ne_top C z₀ j x ⟨k, hk⟩ hn
    · simp [windowOccupationVector, hk]
  have hefin : ∀ k, windowEntryVector C z₀ j x k ≠ ⊤ := by
    intro k
    by_cases hk : k < 5
    · simpa only [windowEntryVector, dif_pos hk] using
        windowEntry_ne_top C z₀ j x ⟨k, hk⟩
    · simp [windowEntryVector, hk]
  intro c hc
  let L : ℝ≥0∞ := if 0 < c then (forwardCount C x.val : ℝ≥0∞) *
    windowOccupationVector C z₀ j x (c - 1) else 0
  let R : ℝ≥0∞ := if c + 1 < 5 then (backwardCount C x.val : ℝ≥0∞) *
    windowOccupationVector C z₀ j x (c + 1) else 0
  have hLfin : L ≠ ⊤ := by
    dsimp [L]
    split_ifs
    · exact ENNReal.mul_ne_top (by simp) (hwfin _)
    · simp
  have hRfin : R ≠ ⊤ := by
    dsimp [R]
    split_ifs
    · exact ENNReal.mul_ne_top (by simp) (hwfin _)
    · simp
  have heLfin : windowEntryVector C z₀ j x c + L ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hefin c, hLfin⟩
  have hcoef :
      (((StandaloneWork.totalWorkRate C x.val + backwardCount C x.val +
        (if c + 1 < 5 then forwardCount C x.val else 0) : ℕ) : ℝ≥0∞)).toReal =
      (StandaloneWork.totalWorkRate C x.val : ℝ) + (backwardCount C x.val : ℝ) +
        (if c + 1 < 5 then (forwardCount C x.val : ℝ) else 0) := by
    rw [ENNReal.toReal_natCast]
    by_cases h : c + 1 < 5 <;> simp [h]
  have hLreal : L.toReal = if 0 < c then (forwardCount C x.val : ℝ) *
      windowOccupationReal C z₀ j x (c - 1) else 0 := by
    dsimp [L]
    split_ifs <;> simp [ENNReal.toReal_mul, windowOccupationReal]
  have hRreal : R.toReal = if c + 1 < 5 then (backwardCount C x.val : ℝ) *
      windowOccupationReal C z₀ j x (c + 1) else 0 := by
    dsimp [R]
    split_ifs <;> simp [ENNReal.toReal_mul, windowOccupationReal]
  have h := congrArg ENNReal.toReal
    (windowOccupation_physical_balance_enn C z₀ j x hn c hc)
  change
    (((StandaloneWork.totalWorkRate C x.val + backwardCount C x.val +
      (if c + 1 < 5 then forwardCount C x.val else 0) : ℕ) : ℝ≥0∞) *
        windowOccupationVector C z₀ j x c).toReal =
      (windowEntryVector C z₀ j x c + L + R).toReal at h
  rw [ENNReal.toReal_mul, hcoef,
    ENNReal.toReal_add heLfin hRfin,
    ENNReal.toReal_add (hefin c) hLfin,
    hLreal, hRreal] at h
  simpa only [windowOccupationReal, windowEntryReal] using h

open Ripple.sCRNUniversality.Stochastic.ClockOccupation

/-- T41 §8.2: ClockBalance for the actual window occupation and entry vectors.
There is no assumed balance, incoming-flux, support, or summability identity.
The two domain hypotheses are exactly nonterminal work and f(x) > 0. -/
theorem windowOccupation_normalized_balance (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C)
    (hn : ¬ WorkTerminal C x.val) (hf : 0 < backwardCount C x.val) :
    ClockBalance 5
      ((forwardCount C x.val : ℝ) / (backwardCount C x.val : ℝ))
      ((StandaloneWork.totalWorkRate C x.val : ℝ) / (backwardCount C x.val : ℝ))
      1 (windowOccupationReal C z₀ j x)
      (fun c => windowEntryReal C z₀ j x c / (backwardCount C x.val : ℝ)) := by
  exact physicalBalance_normalize (by exact_mod_cast hf)
    (windowOccupation_physical_balance C z₀ j x hn)

/-! ## Actual total masses for Lemma 8.3 -/

noncomputable def windowOccupationTotal (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) : ℝ≥0∞ :=
  ∑ c : Fin 5, windowOccupation C z₀ j x c

noncomputable def windowEntryTotal (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) : ℝ≥0∞ :=
  ∑ c : Fin 5, windowEntry C z₀ j x c

/-- D(j,x) = rho(x) times the actual total occupation. -/
noncomputable def windowWorkExit (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) : ℝ≥0∞ :=
  (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞) * windowOccupationTotal C z₀ j x

/-- The work-edge kernel, with a zero row at a work-terminal state.
This is the killed work kernel, not the absorbing extension of rawLaw. -/
noncomputable def workEdgeKernel (C : XCTM Q) (x y : ClocklessState C) : ℝ≥0∞ :=
  workEdgeRate C x y / (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞)

theorem windowOccupationTotal_ne_top (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (hn : ¬ WorkTerminal C x.val) :
    windowOccupationTotal C z₀ j x ≠ ⊤ := by
  exact ENNReal.sum_ne_top.mpr
    (fun c _ => windowOccupation_ne_top C z₀ j x c hn)

theorem windowEntryTotal_ne_top (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) : windowEntryTotal C z₀ j x ≠ ⊤ := by
  exact ENNReal.sum_ne_top.mpr (fun c _ => windowEntry_ne_top C z₀ j x c)

private theorem windowOccupationTotal_toReal (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (hn : ¬ WorkTerminal C x.val) :
    (windowOccupationTotal C z₀ j x).toReal =
      psum (windowOccupationReal C z₀ j x) 5 := by
  rw [windowOccupationTotal,
    ENNReal.toReal_sum (fun c _ => windowOccupation_ne_top C z₀ j x c hn)]
  simp [Fin.sum_univ_succ, psum, Finset.sum_range_succ,
    windowOccupationReal, windowOccupationVector, add_assoc]

private theorem windowEntryTotal_toReal (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) :
    (windowEntryTotal C z₀ j x).toReal = psum (windowEntryReal C z₀ j x) 5 := by
  rw [windowEntryTotal,
    ENNReal.toReal_sum (fun c _ => windowEntry_ne_top C z₀ j x c)]
  simp [Fin.sum_univ_succ, psum, Finset.sum_range_succ,
    windowEntryReal, windowEntryVector, add_assoc]

/-- Sum the five physical rows without dividing by the backward rate. -/
private theorem physicalBalance_total_without_division
    {a f ρ : ℝ} {w e : ℕ → ℝ} (h : PhysicalBalance a f ρ w e) :
    ρ * psum w 5 + f * w 0 = psum e 5 := by
  have hzero := h 0 (by norm_num)
  have hone := h 1 (by norm_num)
  have htwo := h 2 (by norm_num)
  have hthree := h 3 (by norm_num)
  have hfour := h 4 (by norm_num)
  norm_num at hzero hone htwo hthree hfour
  norm_num [psum, Finset.sum_range_succ]
  nlinarith [hzero, hone, htwo, hthree, hfour]

/-- Actual total balance: work-exit mass plus tick-exit mass equals entry mass. -/
theorem windowOccupation_total_balance (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C)
    (hn : ¬ WorkTerminal C x.val) :
    windowWorkExit C z₀ j x +
      (backwardCount C x.val : ℝ≥0∞) * windowOccupation C z₀ j x (0 : Fin 5) =
      windowEntryTotal C z₀ j x := by
  have hD : windowWorkExit C z₀ j x ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (windowOccupationTotal_ne_top C z₀ j x hn)
  have hT : (backwardCount C x.val : ℝ≥0∞) *
      windowOccupation C z₀ j x (0 : Fin 5) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (windowOccupation_ne_top C z₀ j x 0 hn)
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.add_ne_top.mpr ⟨hD, hT⟩) (windowEntryTotal_ne_top C z₀ j x)).mp
  rw [ENNReal.toReal_add hD hT]
  simp only [windowWorkExit, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    windowOccupationTotal_toReal C z₀ j x hn, windowEntryTotal_toReal C z₀ j x]
  have h := physicalBalance_total_without_division
    (windowOccupation_physical_balance C z₀ j x hn)
  simpa only [windowOccupationReal, windowOccupationVector,
    dif_pos (show (0 : ℕ) < 5 by norm_num)] using h

/-- Lemma 8.3's actual D <= E, including the zero-work-rate case. -/
theorem windowWorkExit_le_entry (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) :
    windowWorkExit C z₀ j x ≤ windowEntryTotal C z₀ j x := by
  classical
  by_cases ht : WorkTerminal C x.val
  · have hr : StandaloneWork.totalWorkRate C x.val = 0 := by
      unfold StandaloneWork.totalWorkRate
      apply Finset.sum_eq_zero
      intro r _
      exact (workTerminal_iff C x.val).mp ht r.val r.property
    simp [windowWorkExit, hr]
  · calc
      windowWorkExit C z₀ j x ≤ windowWorkExit C z₀ j x +
          (backwardCount C x.val : ℝ≥0∞) * windowOccupation C z₀ j x (0 : Fin 5) :=
        le_self_add
      _ = windowEntryTotal C z₀ j x := windowOccupation_total_balance C z₀ j x ht

theorem windowWorkExit_ne_top (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) : windowWorkExit C z₀ j x ≠ ⊤ :=
  ne_top_of_le_ne_top (windowEntryTotal_ne_top C z₀ j x)
    (windowWorkExit_le_entry C z₀ j x)

/-- Sum the actual vector-valued work-entry recurrence over clock positions. -/
theorem windowEntryTotal_work_recurrence (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (y : ClocklessState C) :
    windowEntryTotal C z₀ (j + 1) y =
      ∑' x : ClocklessState C, workEdgeRate C x y * windowOccupationTotal C z₀ j x := by
  calc
    windowEntryTotal C z₀ (j + 1) y =
        ∑' c : Fin 5, windowEntry C z₀ (j + 1) y c := (tsum_fintype _).symm
    _ = ∑' c : Fin 5, ∑' x : ClocklessState C,
        workEdgeRate C x y * windowOccupation C z₀ j x c :=
      tsum_congr (fun c => windowEntry_work_recurrence C z₀ j y c)
    _ = ∑' x : ClocklessState C, ∑' c : Fin 5,
        workEdgeRate C x y * windowOccupation C z₀ j x c := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro x
      rw [ENNReal.tsum_mul_left, tsum_fintype] <;> rfl

private theorem workEdgeRate_zero_of_totalWorkRate_zero (C : XCTM Q)
    (x y : ClocklessState C) (hzero : StandaloneWork.totalWorkRate C x.val = 0) :
    workEdgeRate C x y = 0 := by
  classical
  unfold workEdgeRate
  apply Finset.sum_eq_zero
  intro r _
  have hle : rate C r.val x.val ≤ StandaloneWork.totalWorkRate C x.val :=
    Finset.single_le_sum (f := fun q : WorkLabel C => rate C q.val x.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have hr : rate C r.val x.val = 0 := by omega
  split_ifs <;> simp [hr]

/-- Zero-rate rows are handled before cancellation, even if occupation is infinite. -/
theorem windowWorkExit_mul_kernel (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x y : ClocklessState C) :
    windowWorkExit C z₀ j x * workEdgeKernel C x y =
      workEdgeRate C x y * windowOccupationTotal C z₀ j x := by
  by_cases hzero : StandaloneWork.totalWorkRate C x.val = 0
  · have hβ := workEdgeRate_zero_of_totalWorkRate_zero C x y hzero
    simp [windowWorkExit, workEdgeKernel, hzero, hβ]
  · have hρ : (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hzero
    calc
      windowWorkExit C z₀ j x * workEdgeKernel C x y =
          ((StandaloneWork.totalWorkRate C x.val : ℝ≥0∞) *
            (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞)⁻¹) *
              (workEdgeRate C x y * windowOccupationTotal C z₀ j x) := by
        unfold windowWorkExit workEdgeKernel
        simp only [div_eq_mul_inv]
        ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hρ (by simp), one_mul]

/-- Lemma 8.3's exact E(j+1,y) = sum_x D(j,x) K(x,y), on the defined objects. -/
theorem windowEntryTotal_exit_recurrence (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (y : ClocklessState C) :
    windowEntryTotal C z₀ (j + 1) y =
      ∑' x : ClocklessState C, windowWorkExit C z₀ j x * workEdgeKernel C x y := by
  rw [windowEntryTotal_work_recurrence]
  apply tsum_congr
  intro x
  exact (windowWorkExit_mul_kernel C z₀ j x y).symm

end WindowAnalysis

namespace StandaloneWork

/-- The actual work-only jump-chain marginal, including its absorbing terminal states. -/
noncomputable def stateMass (C : XCTM Q) (start : State (Sp C))
    (j : ℕ) (x : State (Sp C)) : ℝ≥0∞ :=
  rawLaw (workNet C) (workNet_hasPositiveRates C) start
    {ω | pathState (workNet C) start ω j = x}

private theorem measurableSet_workStateAt (C : XCTM Q)
    (start : State (Sp C)) (j : ℕ) (x : State (Sp C)) :
    MeasurableSet {ω : ℕ → Option (workNet C).I |
      pathState (workNet C) start ω j = x} := by
  have hm : Measurable (fun ω : ℕ → Option (workNet C).I =>
      pathState (workNet C) start ω j) := by
    apply measurable_of_frestrictLe (workNet C) j
    intro ω ω' h
    rw [← prefixToState_eq_pathState (workNet C) start ω j,
      ← prefixToState_eq_pathState (workNet C) start ω' j]
    exact congrArg (prefixToState (workNet C) start j) h
  exact hm (measurableSet_singleton x)

/-- Exact raw-law marginal expansion of the existing standalone mean duration.
Terminal states contribute zero through the existing holdingMean definition. -/
theorem meanDuration_eq_stateMass_sum (C : XCTM Q) (start : State (Sp C)) :
    meanDuration C start =
      ∑' j : ℕ, ∑' x : State (Sp C), stateMass C start j x * holdingMean C x := by
  classical
  change (∫⁻ ω, ∑' j : ℕ, holdingMean C (pathState (workNet C) start ω j)
    ∂rawLaw (workNet C) (workNet_hasPositiveRates C) start) = _
  rw [lintegral_tsum (fun j => (measurable_holdingMean_at C start j).aemeasurable)]
  apply tsum_congr
  intro j
  let E : State (Sp C) → Set (ℕ → Option (workNet C).I) :=
    fun x => {ω | pathState (workNet C) start ω j = x}
  have hE : ∀ x, MeasurableSet (E x) := measurableSet_workStateAt C start j
  have hsplit : ∀ ω : ℕ → Option (workNet C).I,
      holdingMean C (pathState (workNet C) start ω j) =
        ∑' x : State (Sp C), (E x).indicator (fun _ => holdingMean C x) ω := by
    intro ω
    symm
    calc
      (∑' x : State (Sp C), (E x).indicator (fun _ => holdingMean C x) ω) =
          (E (pathState (workNet C) start ω j)).indicator
            (fun _ => holdingMean C (pathState (workNet C) start ω j)) ω := by
        apply tsum_eq_single (pathState (workNet C) start ω j)
        intro x hx
        simp [E, Set.indicator_apply, Ne.symm hx]
      _ = _ := by simp [E]
  calc
    (∫⁻ ω, holdingMean C (pathState (workNet C) start ω j)
        ∂rawLaw (workNet C) (workNet_hasPositiveRates C) start) =
        ∫⁻ ω, ∑' x : State (Sp C), (E x).indicator (fun _ => holdingMean C x) ω
          ∂rawLaw (workNet C) (workNet_hasPositiveRates C) start := by
      congr 1
      funext ω
      exact hsplit ω
    _ = ∑' x : State (Sp C), ∫⁻ ω, (E x).indicator (fun _ => holdingMean C x) ω
          ∂rawLaw (workNet C) (workNet_hasPositiveRates C) start :=
      lintegral_tsum (fun x => (measurable_const.indicator (hE x)).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro x
      rw [lintegral_indicator_const (hE x)]
      change holdingMean C x *
          rawLaw (workNet C) (workNet_hasPositiveRates C) start (E x) =
        rawLaw (workNet C) (workNet_hasPositiveRates C) start (E x) * holdingMean C x
      exact mul_comm _ _

end StandaloneWork

end Ripple.sCRNUniversality.ClockedCTM.Unbounded
