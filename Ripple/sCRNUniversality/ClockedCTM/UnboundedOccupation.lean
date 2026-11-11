import Ripple.sCRNUniversality.ClockedCTM.UnboundedWindow

/-!
# Occupation comparison for the unbounded-space clocked CTM

Soloveichik--Cook--Winfree--Bruck, as repaired in
docs/audit/FIX3-SCWB-T41.md, Sections 8.2 and 8.3.

The killed work marginals below are measured under the actual standalone
raw law. They retain first terminal entry and kill the outgoing terminal
row. The occupation comparison charges nonterminal work states; terminal
clock waiting is a separate contribution to Section 14.4.
-/

noncomputable section

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction MeasureTheory ProbabilityTheory Classical
open Ripple.sCRNUniversality.Stochastic.ClockOccupation
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace WindowAnalysis

open Classical

/-- The zero row of the killed work kernel is forced by work terminality. -/
theorem totalWorkRate_eq_zero_of_terminal (C : XCTM Q)
    (x : State (Sp C)) (hx : WorkTerminal C x) :
    StandaloneWork.totalWorkRate C x = 0 := by
  unfold StandaloneWork.totalWorkRate
  apply Finset.sum_eq_zero
  intro r _
  exact (workTerminal_iff C x).mp hx r.val r.property

theorem workEdgeKernel_eq_zero_of_terminal (C : XCTM Q)
    (x y : ClocklessState C) (hx : WorkTerminal C x.val) :
    workEdgeKernel C x y = 0 := by
  classical
  have hβ : workEdgeRate C x y = 0 := by
    unfold workEdgeRate
    apply Finset.sum_eq_zero
    intro r _
    have hr := (workTerminal_iff C x.val).mp hx r.val r.property
    split_ifs <;> simp [hr]
  simp [workEdgeKernel, hβ,
    totalWorkRate_eq_zero_of_terminal C x.val hx]

/-- The work-only jump chain preserves the clockless state space on every
sanitized path, including labels that have probability zero. -/
theorem standalone_path_clockless (C : XCTM Q) (x₀ : ClocklessState C)
    (ω : ℕ → Option (StandaloneWork.workNet C).I) :
    ∀ j, workView C
      (pathState (StandaloneWork.workNet C) x₀.val ω j) =
        pathState (StandaloneWork.workNet C) x₀.val ω j := by
  intro j
  induction j with
  | zero => exact x₀.property
  | succ j ih =>
      change workView C
        (stateStep (StandaloneWork.workNet C)
          (pathState (StandaloneWork.workNet C) x₀.val ω j) (ω (j + 1))) =
        stateStep (StandaloneWork.workNet C)
          (pathState (StandaloneWork.workNet C) x₀.val ω j) (ω (j + 1))
      by_cases ht : WorkTerminal C
          (pathState (StandaloneWork.workNet C) x₀.val ω j)
      · rw [StandaloneWork.stateStep_of_terminal C _ _ ht]
        exact ih
      · obtain ⟨r, hr, _, hstep⟩ :=
          StandaloneWork.stateStep_is_workStep C _ (ω (j + 1)) ht
        rw [hstep, work_fire_view C r _ hr, ih]

theorem stateMass_eq_zero_of_not_clockless (C : XCTM Q)
    (x₀ : ClocklessState C) (j : ℕ) (x : State (Sp C))
    (hx : workView C x ≠ x) :
    StandaloneWork.stateMass C x₀.val j x = 0 := by
  have hset : {ω : ℕ → Option (StandaloneWork.workNet C).I |
      pathState (StandaloneWork.workNet C) x₀.val ω j = x} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    apply hx
    rw [← hω]
    exact standalone_path_clockless C x₀ ω j
  unfold StandaloneWork.stateMass
  rw [hset, measure_empty]

/-- Initial entry mass for a single-clock start, at any clock position. -/
theorem windowEntryTotal_initial (C : XCTM Q)
    (x₀ x : ClocklessState C) (c₀ : Fin 5) :
    windowEntryTotal C (clockInsert C x₀ c₀) 0 x =
      if x₀ = x then 1 else 0 := by
  classical
  unfold windowEntryTotal windowEntry
  simp_rw [windowEntries_initial_level]
  have hinj : ∀ c : Fin 5,
      clockInsert C x₀ c₀ = clockInsert C x c ↔ x₀ = x ∧ c₀ = c := by
    intro c
    constructor
    · intro h
      have hh : (x₀, c₀) = (x, c) := clockInsert_injective C h
      exact ⟨congrArg (fun p : ClocklessState C × Fin 5 => p.1) hh,
        congrArg (fun p : ClocklessState C × Fin 5 => p.2) hh⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp_rw [hinj]
  by_cases hx : x₀ = x
  · simp [hx, eq_comm]
  · simp [hx]

/-- Once a terminal work state has been entered, the next step kills the
chain. The terminal entry itself is retained. -/
noncomputable def killedWorkUpdate (C : XCTM Q) (live : Bool)
    (x : State (Sp C)) (_o : Option (StandaloneWork.workNet C).I) : Bool := by
  classical
  exact if WorkTerminal C x then false else live

noncomputable def killedWorkExtended (C : XCTM Q) (x₀ : ClocklessState C)
    (j : ℕ) (ω : ℕ → Option (StandaloneWork.workNet C).I) :
    Bool × State (Sp C) :=
  extState (StandaloneWork.workNet C) x₀.val (killedWorkUpdate C) true j ω

theorem killedWorkExtended_state (C : XCTM Q) (x₀ : ClocklessState C)
    (j : ℕ) (ω : ℕ → Option (StandaloneWork.workNet C).I) :
    (killedWorkExtended C x₀ j ω).2 =
      pathState (StandaloneWork.workNet C) x₀.val ω j :=
  (extState_snd (StandaloneWork.workNet C) x₀.val
    (killedWorkUpdate C) true j ω).trans
      (prefixToState_eq_pathState (StandaloneWork.workNet C) x₀.val ω j)

/-- The live flag means that no strictly earlier state was work-terminal. -/
theorem killedWorkLive_iff (C : XCTM Q) (x₀ : ClocklessState C)
    (ω : ℕ → Option (StandaloneWork.workNet C).I) :
    ∀ j, (killedWorkExtended C x₀ j ω).1 = true ↔
      ∀ i < j, ¬ WorkTerminal C
        (pathState (StandaloneWork.workNet C) x₀.val ω i) := by
  classical
  intro j
  induction j with
  | zero => simp [killedWorkExtended, extState, extOf]
  | succ j ih =>
      have hu : (killedWorkExtended C x₀ (j + 1) ω).1 =
          if WorkTerminal C
              (pathState (StandaloneWork.workNet C) x₀.val ω j)
          then false else (killedWorkExtended C x₀ j ω).1 := by
        change killedWorkUpdate C (killedWorkExtended C x₀ j ω).1
          (killedWorkExtended C x₀ j ω).2 (ω (j + 1)) = _
        rw [killedWorkUpdate, killedWorkExtended_state]
      rw [hu]
      by_cases ht : WorkTerminal C
          (pathState (StandaloneWork.workNet C) x₀.val ω j)
      · rw [if_pos ht]
        constructor
        · intro h
          cases h
        · intro h
          exact False.elim (h j (Nat.lt_succ_self j) ht)
      · rw [if_neg ht, ih]
        constructor
        · intro h i hi
          by_cases hij : i = j
          · simpa only [hij] using ht
          · exact h i (by omega)
        · intro h i hi
          exact h i (by omega)

def killedWorkEvent (C : XCTM Q) (x₀ : ClocklessState C)
    (j : ℕ) (x : ClocklessState C) :
    Set (ℕ → Option (StandaloneWork.workNet C).I) :=
  {ω | (killedWorkExtended C x₀ j ω).1 = true ∧
    (killedWorkExtended C x₀ j ω).2 = x.val}

theorem killedWorkEvent_iff (C : XCTM Q) (x₀ : ClocklessState C)
    (j : ℕ) (x : ClocklessState C)
    (ω : ℕ → Option (StandaloneWork.workNet C).I) :
    ω ∈ killedWorkEvent C x₀ j x ↔
      (∀ i < j, ¬ WorkTerminal C
        (pathState (StandaloneWork.workNet C) x₀.val ω i)) ∧
      pathState (StandaloneWork.workNet C) x₀.val ω j = x.val := by
  simp only [killedWorkEvent, Set.mem_setOf_eq,
    killedWorkLive_iff, killedWorkExtended_state]

theorem measurableSet_killedWorkEvent (C : XCTM Q)
    (x₀ : ClocklessState C) (j : ℕ) (x : ClocklessState C) :
    MeasurableSet (killedWorkEvent C x₀ j x) := by
  classical
  let f : Bool × State (Sp C) → ℕ :=
    fun a => if a.1 = true ∧ a.2 = x.val then 1 else 0
  have hm : Measurable (fun ω => f (killedWorkExtended C x₀ j ω)) :=
    measurable_extState_comp (StandaloneWork.workNet C) x₀.val
      (killedWorkUpdate C) true j f
  have hs : (fun ω => f (killedWorkExtended C x₀ j ω)) ⁻¹' {1} =
      killedWorkEvent C x₀ j x := by
    ext ω
    by_cases h : (killedWorkExtended C x₀ j ω).1 = true ∧
        (killedWorkExtended C x₀ j ω).2 = x.val <;>
      simp [f, killedWorkEvent, h]
  rw [← hs]
  exact hm (measurableSet_singleton (1 : ℕ))

/-- Actual killed marginal, measured under the existing standalone raw law. -/
noncomputable def killedWorkMass (C : XCTM Q) (x₀ : ClocklessState C)
    (j : ℕ) (x : ClocklessState C) : ℝ≥0∞ :=
  rawLaw (StandaloneWork.workNet C)
    (StandaloneWork.workNet_hasPositiveRates C) x₀.val
      (killedWorkEvent C x₀ j x)

theorem killedWorkMass_eq_lintegral (C : XCTM Q)
    (x₀ : ClocklessState C) (j : ℕ) (x : ClocklessState C) :
    killedWorkMass C x₀ j x =
      ∫⁻ ω, if (killedWorkExtended C x₀ j ω).1 = true ∧
          (killedWorkExtended C x₀ j ω).2 = x.val then 1 else 0
        ∂rawLaw (StandaloneWork.workNet C)
          (StandaloneWork.workNet_hasPositiveRates C) x₀.val := by
  classical
  have h := lintegral_indicator_const
    (μ := rawLaw (StandaloneWork.workNet C)
      (StandaloneWork.workNet_hasPositiveRates C) x₀.val)
    (measurableSet_killedWorkEvent C x₀ j x) (1 : ℝ≥0∞)
  simpa only [one_mul, Set.indicator_apply, killedWorkEvent,
    Set.mem_setOf_eq, killedWorkMass] using h.symm

theorem killedWorkMass_initial (C : XCTM Q) (x₀ x : ClocklessState C) :
    killedWorkMass C x₀ 0 x = if x₀ = x then 1 else 0 := by
  classical
  letI : IsProbabilityMeasure
      (rawLaw (StandaloneWork.workNet C)
        (StandaloneWork.workNet_hasPositiveRates C) x₀.val) :=
    rawLaw_isProbabilityMeasure _ _ _
  rw [killedWorkMass_eq_lintegral]
  by_cases hx : x₀ = x
  · subst x
    simp [killedWorkExtended, extState, extOf]
  · have hv : x₀.val ≠ x.val := fun h => hx (Subtype.ext h)
    simp [killedWorkExtended, extState, extOf, hx, hv]

/-- Killed marginals are bounded by the original absorbing raw-law marginals. -/
theorem killedWorkMass_le_stateMass (C : XCTM Q)
    (x₀ : ClocklessState C) (j : ℕ) (x : ClocklessState C) :
    killedWorkMass C x₀ j x ≤ StandaloneWork.stateMass C x₀.val j x.val := by
  apply measure_mono
  intro ω hω
  exact (killedWorkExtended_state C x₀ j ω).symm.trans hω.2

private theorem work_pmf_eq_rate_div_total (C : XCTM Q)
    (x : State (Sp C)) (r : WorkLabel C) (hn : ¬ WorkTerminal C x) :
    massActionPMF (StandaloneWork.workNet C)
        (StandaloneWork.workNet_hasPositiveRates C) x (some r) =
      (rate C r.val x : ℝ≥0∞) /
        (StandaloneWork.totalWorkRate C x : ℝ≥0∞) := by
  have hNT : ¬ (StandaloneWork.workNet C).Terminal x :=
    fun ht => hn ((StandaloneWork.workNet_terminal_iff C x).mp ht)
  have hB := totalPropensity_ne_zero_of_nonTerminal
    (StandaloneWork.workNet C)
      (StandaloneWork.workNet_hasPositiveRates C) hNT
  have hq : jumpProbAt (StandaloneWork.workNet C) x r *
      (StandaloneWork.workNet C).totalPropensity x =
        (rate C r.val x : Rate) := by
    rw [jumpProbAt, div_mul_cancel₀ _ hB]
    exact propensity_rxn C r.val x
  have hNN : (jumpProbAt (StandaloneWork.workNet C) x r : NNReal) *
      ((StandaloneWork.workNet C).totalPropensity x : NNReal) =
        (rate C r.val x : NNReal) := by
    exact_mod_cast hq
  have hE : (jumpProbAt (StandaloneWork.workNet C) x r : ℝ≥0∞) *
      ((StandaloneWork.workNet C).totalPropensity x : ℝ≥0∞) =
        (rate C r.val x : ℝ≥0∞) := by
    simpa only [ENNReal.coe_mul, ENNReal.coe_nnratCast,
      ENNReal.coe_natCast] using
        congrArg (fun q : NNReal => (q : ℝ≥0∞)) hNN
  have hBzero :
      ((StandaloneWork.workNet C).totalPropensity x : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.coe_nnratCast, ENNReal.coe_ne_zero]
    exact_mod_cast hB
  have hBtop :
      ((StandaloneWork.workNet C).totalPropensity x : ℝ≥0∞) ≠ ⊤ := by
    rw [← ENNReal.coe_nnratCast]
    exact ENNReal.coe_ne_top
  change massActionWeight (StandaloneWork.workNet C)
    (StandaloneWork.workNet_hasPositiveRates C) x (some r) = _
  simp only [massActionWeight, dif_neg hNT]
  calc
    (jumpProbAt (StandaloneWork.workNet C) x r : ℝ≥0∞) =
        ((jumpProbAt (StandaloneWork.workNet C) x r : ℝ≥0∞) *
          ((StandaloneWork.workNet C).totalPropensity x : ℝ≥0∞)) /
            ((StandaloneWork.workNet C).totalPropensity x : ℝ≥0∞) :=
      (ENNReal.mul_div_cancel_right hBzero hBtop).symm
    _ = (rate C r.val x : ℝ≥0∞) /
        ((StandaloneWork.workNet C).totalPropensity x : ℝ≥0∞) := by rw [hE]
    _ = _ := by
      rw [StandaloneWork.workNet_totalPropensity] <;> norm_cast

/-- The killed edge kernel is the actual one-step work law with terminal
outgoing transitions removed. -/
theorem workEdgeKernel_eq_sum_step (C : XCTM Q)
    (x y : ClocklessState C) :
    workEdgeKernel C x y =
      ∑ o : Option (StandaloneWork.workNet C).I,
        massActionPMF (StandaloneWork.workNet C)
          (StandaloneWork.workNet_hasPositiveRates C) x.val o *
          (if ¬ WorkTerminal C x.val ∧
              stateStep (StandaloneWork.workNet C) x.val o = y.val
            then 1 else 0) := by
  classical
  by_cases ht : WorkTerminal C x.val
  · simp [workEdgeKernel_eq_zero_of_terminal C x y ht, ht]
  · have hNT : ¬ (StandaloneWork.workNet C).Terminal x.val :=
      fun h => ht ((StandaloneWork.workNet_terminal_iff C x.val).mp h)
    have hnone : massActionPMF (StandaloneWork.workNet C)
        (StandaloneWork.workNet_hasPositiveRates C) x.val none = 0 := by
      change massActionWeight (StandaloneWork.workNet C)
        (StandaloneWork.workNet_hasPositiveRates C) x.val none = 0
      simp only [massActionWeight, dif_neg hNT]
    rw [Fintype.sum_option]
    simp only [hnone, zero_mul, zero_add, add_zero]
    unfold workEdgeKernel workEdgeRate
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [work_pmf_eq_rate_div_total C x.val r ht]
    by_cases he : (rxn C r.val).enabled x.val
    · have hstep : stateStep (StandaloneWork.workNet C) x.val (some r) =
          (workSuccessor C x r).val := by
        simp only [stateStep, dif_neg hNT]
        exact congrArg (fun q : (StandaloneWork.workNet C).I =>
          ((StandaloneWork.workNet C).rxn q).fire x.val)
            (fireOptionSanitized_of_enabled (StandaloneWork.workNet C)
              x.val r hNT he)
      have hxy : (workSuccessor C x r).val = y.val ↔
          workSuccessor C x r = y :=
        ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
      rw [hstep]
      by_cases h : workSuccessor C x r = y
      · simp [he, ht, h, hxy, div_eq_mul_inv]
      · simp [he, ht, h, hxy]
    · have hr : rate C r.val x.val = 0 := by
        by_contra h
        exact he ((enabled_iff C r.val x.val).mpr h)
      simp [he, hr]

private theorem killedWork_step_sum (C : XCTM Q)
    (a : Bool × State (Sp C)) (ha : workView C a.2 = a.2)
    (y : ClocklessState C) :
    (∑ o : Option (StandaloneWork.workNet C).I,
      massActionPMF (StandaloneWork.workNet C)
        (StandaloneWork.workNet_hasPositiveRates C) a.2 o *
        (if killedWorkUpdate C a.1 a.2 o = true ∧
            stateStep (StandaloneWork.workNet C) a.2 o = y.val
          then 1 else 0)) =
      ∑' x : ClocklessState C,
        (if a.1 = true ∧ a.2 = x.val then 1 else 0) *
          workEdgeKernel C x y := by
  classical
  let current : ClocklessState C := ⟨a.2, ha⟩
  have hsum :
      (∑' x : ClocklessState C,
        (if a.1 = true ∧ a.2 = x.val then 1 else 0) *
          workEdgeKernel C x y) =
        (if a.1 = true ∧ a.2 = current.val then 1 else 0) *
          workEdgeKernel C current y := by
    apply tsum_eq_single current
    intro x hx
    have hv : a.2 ≠ x.val := by
      intro h
      apply hx
      exact Subtype.ext h.symm
    simp [hv]
  rw [hsum]
  by_cases ht : WorkTerminal C a.2
  · have hk := workEdgeKernel_eq_zero_of_terminal C current y ht
    simp [killedWorkUpdate, ht, hk]
  · by_cases hl : a.1 = true
    · simpa [killedWorkUpdate, ht, hl, current] using
        (workEdgeKernel_eq_sum_step C current y).symm
    · simp [killedWorkUpdate, ht, hl]

/-- The convolution recursion is proved from the actual standalone raw law,
not postulated as an abstract marginal identity. -/
theorem killedWorkMass_recurrence (C : XCTM Q)
    (x₀ : ClocklessState C) (j : ℕ) (y : ClocklessState C) :
    killedWorkMass C x₀ (j + 1) y =
      ∑' x : ClocklessState C,
        killedWorkMass C x₀ j x * workEdgeKernel C x y := by
  classical
  let F : Bool × State (Sp C) → ℝ≥0∞ :=
    fun a => if a.1 = true ∧ a.2 = y.val then 1 else 0
  have hm : ∀ x : ClocklessState C, Measurable
      (fun ω : ℕ → Option (StandaloneWork.workNet C).I =>
        if (killedWorkExtended C x₀ j ω).1 = true ∧
            (killedWorkExtended C x₀ j ω).2 = x.val
          then (1 : ℝ≥0∞) else 0) :=
    fun x => measurable_extState_comp (StandaloneWork.workNet C) x₀.val
      (killedWorkUpdate C) true j
      (fun a => if a.1 = true ∧ a.2 = x.val then (1 : ℝ≥0∞) else 0)
  rw [killedWorkMass_eq_lintegral]
  change (∫⁻ ω, F (extState (StandaloneWork.workNet C) x₀.val
    (killedWorkUpdate C) true (j + 1) ω)
    ∂rawLaw (StandaloneWork.workNet C)
      (StandaloneWork.workNet_hasPositiveRates C) x₀.val) = _
  rw [lintegral_extState_succ]
  calc
    (∫⁻ ω, ∑ o : Option (StandaloneWork.workNet C).I,
        massActionPMF (StandaloneWork.workNet C)
          (StandaloneWork.workNet_hasPositiveRates C)
          (killedWorkExtended C x₀ j ω).2 o *
          F (killedWorkUpdate C (killedWorkExtended C x₀ j ω).1
              (killedWorkExtended C x₀ j ω).2 o,
            stateStep (StandaloneWork.workNet C)
              (killedWorkExtended C x₀ j ω).2 o)
      ∂rawLaw (StandaloneWork.workNet C)
        (StandaloneWork.workNet_hasPositiveRates C) x₀.val) =
      ∫⁻ ω, ∑' x : ClocklessState C,
        (if (killedWorkExtended C x₀ j ω).1 = true ∧
            (killedWorkExtended C x₀ j ω).2 = x.val
          then (1 : ℝ≥0∞) else 0) * workEdgeKernel C x y
      ∂rawLaw (StandaloneWork.workNet C)
        (StandaloneWork.workNet_hasPositiveRates C) x₀.val := by
      apply lintegral_congr
      intro ω
      apply killedWork_step_sum C (killedWorkExtended C x₀ j ω)
      rw [killedWorkExtended_state]
      exact standalone_path_clockless C x₀ ω j
    _ = ∑' x : ClocklessState C,
        ∫⁻ ω,
          (if (killedWorkExtended C x₀ j ω).1 = true ∧
              (killedWorkExtended C x₀ j ω).2 = x.val
            then (1 : ℝ≥0∞) else 0) * workEdgeKernel C x y
        ∂rawLaw (StandaloneWork.workNet C)
          (StandaloneWork.workNet_hasPositiveRates C) x₀.val :=
      lintegral_tsum (fun x => ((hm x).mul_const _).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro x
      rw [lintegral_mul_const _ (hm x), ← killedWorkMass_eq_lintegral]

/-- At nonterminal states killing has not yet occurred, so the killed and
absorbing standalone marginals are exactly equal. -/
theorem killedWorkMass_eq_stateMass_of_nonterminal (C : XCTM Q)
    (x₀ : ClocklessState C) (j : ℕ) (x : ClocklessState C)
    (hx : ¬ WorkTerminal C x.val) :
    killedWorkMass C x₀ j x = StandaloneWork.stateMass C x₀.val j x.val := by
  have hset : killedWorkEvent C x₀ j x =
      {ω : ℕ → Option (StandaloneWork.workNet C).I |
        pathState (StandaloneWork.workNet C) x₀.val ω j = x.val} := by
    ext ω
    rw [killedWorkEvent_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      intro i hi ht
      apply hx
      rw [← h]
      exact StandaloneWork.terminal_persists C x₀.val ω ht hi.le
  unfold killedWorkMass StandaloneWork.stateMass
  rw [hset]

/-- FIX3-SCWB-T41 Lemma 8.3: actual window entries are dominated by the killed
standalone work-chain marginals, including terminal entry states. -/
theorem windowEntryTotal_le_killedWorkMass (C : XCTM Q)
    (x₀ : ClocklessState C) (c₀ : Fin 5) :
    ∀ j x, windowEntryTotal C (clockInsert C x₀ c₀) j x ≤
      killedWorkMass C x₀ j x := by
  apply entry_domination_of_exit_recursion (workEdgeKernel C)
    (windowEntryTotal C (clockInsert C x₀ c₀))
    (windowWorkExit C (clockInsert C x₀ c₀)) (killedWorkMass C x₀)
  · intro x
    rw [windowEntryTotal_initial, killedWorkMass_initial]
  · exact windowWorkExit_le_entry C (clockInsert C x₀ c₀)
  · intro j y
    exact (windowEntryTotal_exit_recurrence C (clockInsert C x₀ c₀) j y).le
  · exact killedWorkMass_recurrence C x₀

/-- The literal probability bound against the existing absorbing work law. -/
theorem windowEntryTotal_le_stateMass (C : XCTM Q)
    (x₀ : ClocklessState C) (c₀ : Fin 5) (j : ℕ) (x : ClocklessState C) :
    windowEntryTotal C (clockInsert C x₀ c₀) j x ≤
      StandaloneWork.stateMass C x₀.val j x.val :=
  (windowEntryTotal_le_killedWorkMass C x₀ c₀ j x).trans
    (killedWorkMass_le_stateMass C x₀ j x)

/-- The duration comparison only charges nonterminal work states. Terminal
clock waiting is a distinct contribution in FIX3-SCWB-T41 Lemma 14.4. -/
theorem windowOccupation_le_entry_mul_holdingMean (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C)
    (hx : ¬ WorkTerminal C x.val) :
    windowOccupationTotal C z₀ j x ≤
      windowEntryTotal C z₀ j x * StandaloneWork.holdingMean C x.val := by
  have hρzero : (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (StandaloneWork.totalWorkRate_pos C x.val hx).ne'
  have hρtop : (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞) ≠ ⊤ := by simp
  calc
    windowOccupationTotal C z₀ j x =
        (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞)⁻¹ *
          windowWorkExit C z₀ j x := by
      rw [windowWorkExit, ← mul_assoc,
        ENNReal.inv_mul_cancel hρzero hρtop, one_mul]
    _ ≤ (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞)⁻¹ *
        windowEntryTotal C z₀ j x :=
      mul_le_mul_left' (windowWorkExit_le_entry C z₀ j x) _
    _ = _ := by
      rw [StandaloneWork.holdingMean, if_neg hx]
      exact mul_comm _ _

/-- FIX3-SCWB-T41 Lemma 8.3 on the actual occupations and actual standalone law.
The sum excludes terminal clock-waiting occupation. -/
theorem windowOccupation_nonterminal_sum_le_meanDuration (C : XCTM Q)
    (x₀ : ClocklessState C) (c₀ : Fin 5) :
    (∑' j : ℕ, ∑' x : ClocklessState C,
      if WorkTerminal C x.val then 0
      else windowOccupationTotal C (clockInsert C x₀ c₀) j x) ≤
      StandaloneWork.meanDuration C x₀.val := by
  classical
  rw [StandaloneWork.meanDuration_eq_stateMass_sum]
  apply ENNReal.tsum_le_tsum
  intro j
  calc
    (∑' x : ClocklessState C,
        if WorkTerminal C x.val then 0
        else windowOccupationTotal C (clockInsert C x₀ c₀) j x) ≤
        ∑' x : ClocklessState C,
          StandaloneWork.stateMass C x₀.val j x.val *
            StandaloneWork.holdingMean C x.val := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases ht : WorkTerminal C x.val
      · simp [ht]
      · rw [if_neg ht]
        exact (windowOccupation_le_entry_mul_holdingMean C
          (clockInsert C x₀ c₀) j x ht).trans
            (mul_le_mul_right'
              (windowEntryTotal_le_stateMass C x₀ c₀ j x)
              (StandaloneWork.holdingMean C x.val))
    _ ≤ ∑' x : State (Sp C),
        StandaloneWork.stateMass C x₀.val j x * StandaloneWork.holdingMean C x :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (Subtype.coe_injective : Function.Injective
          (fun x : ClocklessState C => x.val))
        (fun x => StandaloneWork.stateMass C x₀.val j x *
          StandaloneWork.holdingMean C x)

end WindowAnalysis

namespace WindowAnalysis

/-! ## Reachable support and the clock cone -/

open Ripple.sCRNUniversality.Stochastic.ClockOccupation
open Classical

/-- A work edge cannot connect states which are not related by a work step. -/
theorem workEdgeRate_zero_of_no_step (C : XCTM Q)
    (x y : ClocklessState C) (hxy : ¬ WorkStep C x.val y.val) :
    workEdgeRate C x y = 0 := by
  classical
  unfold workEdgeRate
  apply Finset.sum_eq_zero
  intro r _
  have hcond : ¬ ((rxn C r.val).enabled x.val ∧ workSuccessor C x r = y) := by
    rintro ⟨he, hs⟩
    apply hxy
    refine ⟨r.val, r.property, he, ?_⟩
    exact (congrArg Subtype.val hs).symm
  simp only [if_neg hcond]

theorem workEdgeRate_zero_of_terminal_source (C : XCTM Q)
    (x y : ClocklessState C) (hx : WorkTerminal C x.val) :
    workEdgeRate C x y = 0 := by
  apply workEdgeRate_zero_of_no_step C x y
  rintro ⟨r, hr, he, _⟩
  exact hx r hr he

/-- Actual entries have support in the work-reachable set. -/
theorem windowEntryTotal_zero_of_not_workReach (C : XCTM Q)
    (x₀ : ClocklessState C) (c₀ : Fin 5) (j : ℕ) (y : ClocklessState C)
    (hy : ¬ WorkReach C x₀.val y.val) :
    windowEntryTotal C (clockInsert C x₀ c₀) j y = 0 := by
  classical
  induction j generalizing y with
  | zero =>
      rw [windowEntryTotal_initial C x₀ y c₀]
      have hne : x₀ ≠ y := by
        rintro rfl
        exact hy .refl
      exact if_neg hne
  | succ j ih =>
      rw [windowEntryTotal_exit_recurrence]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      by_cases hx : WorkReach C x₀.val x.val
      · have hstep : ¬ WorkStep C x.val y.val :=
          fun h => hy (.tail hx h)
        have hzero := workEdgeRate_zero_of_no_step C x y hstep
        simp [workEdgeKernel, hzero]
      · have hzero : windowWorkExit C (clockInsert C x₀ c₀) j x = 0 := by
          apply le_antisymm
          · exact (windowWorkExit_le_entry C _ j x).trans_eq (ih x hx)
          · exact bot_le
        rw [hzero, zero_mul]

theorem windowOccupation_zero_of_entryTotal_zero (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C)
    (hn : ¬ WorkTerminal C x.val)
    (he : windowEntryTotal C z₀ j x = 0) (c : Fin 5) :
    windowOccupation C z₀ j x c = 0 := by
  have hD : windowWorkExit C z₀ j x = 0 :=
    le_antisymm ((windowWorkExit_le_entry C z₀ j x).trans_eq he) bot_le
  have hρ : (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (StandaloneWork.totalWorkRate_pos C x.val hn)
  change (StandaloneWork.totalWorkRate C x.val : ℝ≥0∞) *
    windowOccupationTotal C z₀ j x = 0 at hD
  have hS : windowOccupationTotal C z₀ j x = 0 :=
    (mul_eq_zero.mp hD).resolve_left hρ
  apply le_antisymm
  · calc
      windowOccupation C z₀ j x c ≤ windowOccupationTotal C z₀ j x :=
        Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ c)
      _ = 0 := hS
  · exact bot_le

theorem windowOccupation_zero_of_not_workReach (C : XCTM Q)
    (x₀ : ClocklessState C) (c₀ : Fin 5) (j : ℕ) (x : ClocklessState C)
    (hn : ¬ WorkTerminal C x.val) (hx : ¬ WorkReach C x₀.val x.val)
    (c : Fin 5) :
    windowOccupation C (clockInsert C x₀ c₀) j x c = 0 :=
  windowOccupation_zero_of_entryTotal_zero C _ j x hn
    (windowEntryTotal_zero_of_not_workReach C x₀ c₀ j x hx) c

/-- The zero-downward-rate case is triangular and needs no division by f.
It is included so the one-window bound has exactly the paper's rate hypotheses. -/
theorem physicalBalance_inCone_of_zero_backward
    {a ρ b : ℝ} {w e : ℕ → ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hb : 0 ≤ b)
    (h : PhysicalBalance a 0 ρ w e)
    (hw : ∀ c, c < 5 → 0 ≤ w c) (he : InCone 5 b e) :
    InCone 5 b w := by
  have hzero := h 0 (by norm_num)
  have hone := h 1 (by norm_num)
  have htwo := h 2 (by norm_num)
  have hthree := h 3 (by norm_num)
  have hfour := h 4 (by norm_num)
  norm_num at hzero hone htwo hthree hfour
  have hbzero := congrArg (fun v : ℝ => b * v) hzero
  have hbone := congrArg (fun v : ℝ => b * v) hone
  have hbtwo := congrArg (fun v : ℝ => b * v) htwo
  have hbthree := congrArg (fun v : ℝ => b * v) hthree
  have hdiag : 0 < ρ + a := add_pos_of_pos_of_nonneg hρ ha
  have hfirst : b * w 0 ≤ w 1 := by
    apply (mul_le_mul_iff_right₀ hdiag).mp
    have hezero := he 0 (by norm_num)
    have hnonneg := mul_nonneg ha (hw 0 (by norm_num))
    nlinarith only [hbzero, hone, hezero, hnonneg]
  have hsecond : b * w 1 ≤ w 2 := by
    apply (mul_le_mul_iff_right₀ hdiag).mp
    have heone := he 1 (by norm_num)
    have hprevious := mul_le_mul_of_nonneg_left hfirst ha
    nlinarith only [hbone, htwo, heone, hprevious]
  have hthird : b * w 2 ≤ w 3 := by
    apply (mul_le_mul_iff_right₀ hdiag).mp
    have hetwo := he 2 (by norm_num)
    have hprevious := mul_le_mul_of_nonneg_left hsecond ha
    nlinarith only [hbtwo, hthree, hetwo, hprevious]
  have hlast : b * w 3 ≤ w 4 := by
    apply (mul_le_mul_iff_right₀ hρ).mp
    have hethree := he 3 (by norm_num)
    have hprevious := mul_le_mul_of_nonneg_left hthird ha
    have hnonneg := mul_nonneg (mul_nonneg hb ha) (hw 3 (by norm_num))
    nlinarith only [hbthree, hfour, hethree, hprevious, hnonneg]
  intro c hc
  have hcsmall : c ≤ 3 := by omega
  interval_cases c <;> assumption

/-- Cone preservation allowing a zero downward clock rate. -/
theorem physicalBalance_inCone_of_rate_bound
    {a f ρ b : ℝ} {w e : ℕ → ℝ}
    (ha : 0 ≤ a) (hf : 0 ≤ f) (hρ : 0 < ρ) (hb : 0 < b)
    (hba : b * f ≤ a) (h : PhysicalBalance a f ρ w e)
    (hw : ∀ c, c < 5 → 0 ≤ w c) (he : InCone 5 b e) :
    InCone 5 b w := by
  by_cases hfzero : f = 0
  · subst f
    exact physicalBalance_inCone_of_zero_backward ha hρ hb.le h hw he
  · have hfpos : 0 < f := lt_of_le_of_ne hf (Ne.symm hfzero)
    exact physicalBalance_inCone hfpos h hb
      ((le_div_iff₀ hfpos).2 hba) hρ.le hw he

theorem windowEntryReal_initial_top (C : XCTM Q)
    (x₀ x : ClocklessState C) (c : ℕ) :
    windowEntryReal C (clockInsert C x₀ 4) 0 x c =
      if c = 4 then (if x₀ = x then 1 else 0) else 0 := by
  classical
  by_cases hc : c < 5
  · have heq :
        clockInsert C x₀ 4 = clockInsert C x ⟨c, hc⟩ ↔ x₀ = x ∧ c = 4 := by
      constructor
      · intro h
        have hp : (x₀, (4 : Fin 5)) = (x, ⟨c, hc⟩) :=
          clockInsert_injective C h
        have hfirst := congrArg Prod.fst hp
        have hsecond := congrArg (fun p : ClocklessState C × Fin 5 => p.2.val) hp
        exact ⟨hfirst, hsecond.symm⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [windowEntryReal, windowEntryVector, dif_pos hc, windowEntry,
      windowEntries_initial_level, heq]
    by_cases hx : x₀ = x <;> by_cases hfour : c = 4 <;> simp [hx, hfour]
  · have hfour : c ≠ 4 := by omega
    simp [windowEntryReal, windowEntryVector, hc, hfour]

/-- Conversion of the actual nonnegative incoming series to real coefficients.
Finiteness comes from the already-proved actual entry-mass bound. -/
theorem windowEntryReal_work_recurrence (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (y : ClocklessState C)
    (c : ℕ) (hc : c < 5) :
    windowEntryReal C z₀ (j + 1) y c =
      ∑' x : ClocklessState C,
        (workEdgeRate C x y).toReal * windowOccupationReal C z₀ j x c := by
  have hfin := windowEntry_work_series_ne_top C z₀ j y ⟨c, hc⟩
  simp only [windowEntryReal, windowEntryVector, dif_pos hc]
  rw [windowEntry_work_recurrence,
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hfin)]
  apply tsum_congr
  intro x
  simp only [ENNReal.toReal_mul, windowOccupationReal,
    windowOccupationVector, dif_pos hc]

theorem windowEntryReal_work_series_summable (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (y : ClocklessState C)
    (c : ℕ) (hc : c < 5) :
    Summable (fun x : ClocklessState C =>
      (workEdgeRate C x y).toReal * windowOccupationReal C z₀ j x c) := by
  have hs := ENNReal.summable_toReal
    (windowEntry_work_series_ne_top C z₀ j y ⟨c, hc⟩)
  simpa only [ENNReal.toReal_mul, windowOccupationReal,
    windowOccupationVector, dif_pos hc] using hs

/-- T41 §8.2: the actual occupation vectors are in the lower-ratio cone.
The rate bound is needed only on states reachable by work from the start. -/
theorem windowOccupationReal_inCone (C : XCTM Q)
    (x₀ : ClocklessState C) {b : ℝ} (hb : 0 < b)
    (hba : ∀ x : ClocklessState C, WorkReach C x₀.val x.val →
      b * (backwardCount C x.val : ℝ) ≤ (forwardCount C x.val : ℝ)) :
    ∀ (j : ℕ) (x : ClocklessState C), ¬ WorkTerminal C x.val →
      InCone 5 b (windowOccupationReal C (clockInsert C x₀ 4) j x) := by
  classical
  intro j
  induction j with
  | zero =>
      intro x hn
      by_cases hx : WorkReach C x₀.val x.val
      · have he : InCone 5 b
            (windowEntryReal C (clockInsert C x₀ 4) 0 x) := by
          intro c hc
          have htop := entry_cone_at_top (b := b)
            (mass := if x₀ = x then (1 : ℝ) else 0) (by split_ifs <;> positivity)
          simpa only [windowEntryReal_initial_top] using htop c hc
        exact physicalBalance_inCone_of_rate_bound
          (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          (by exact_mod_cast StandaloneWork.totalWorkRate_pos C x.val hn)
          hb (hba x hx) (windowOccupation_physical_balance C _ 0 x hn)
          (fun _ _ => ENNReal.toReal_nonneg) he
      · have hz : ∀ c, windowOccupationReal C (clockInsert C x₀ 4) 0 x c = 0 := by
          intro c
          by_cases hc : c < 5
          · simp only [windowOccupationReal, windowOccupationVector, dif_pos hc,
              windowOccupation_zero_of_not_workReach C x₀ 4 0 x hn hx,
              ENNReal.toReal_zero]
          · simp [windowOccupationReal, windowOccupationVector, hc]
        intro c _
        simp only [hz, mul_zero, le_refl]
  | succ j ih =>
      intro y hn
      by_cases hy : WorkReach C x₀.val y.val
      · let β : ClocklessState C → ℝ := fun x => (workEdgeRate C x y).toReal
        let w : ClocklessState C → ℕ → ℝ := fun x c =>
          if WorkTerminal C x.val then 0
          else windowOccupationReal C (clockInsert C x₀ 4) j x c
        have hterm : ∀ x c, β x * w x c =
            (workEdgeRate C x y).toReal *
              windowOccupationReal C (clockInsert C x₀ 4) j x c := by
          intro x c
          by_cases hx : WorkTerminal C x.val
          · have hzero := workEdgeRate_zero_of_terminal_source C x y hx
            simp [β, w, hx, hzero]
          · simp only [β, w, if_neg hx]
        have hw : ∀ x, InCone 5 b (w x) := by
          intro x
          by_cases hx : WorkTerminal C x.val
          · intro c _
            simp only [w, if_pos hx, mul_zero, le_refl]
          · simpa only [w, if_neg hx] using ih x hx
        have hs : ∀ c, c < 5 → Summable (fun x => β x * w x c) := by
          intro c hc
          simpa only [hterm] using
            windowEntryReal_work_series_summable C (clockInsert C x₀ 4) j y c hc
        have heSum := entry_cone_of_work_edges β w
          (fun _ => ENNReal.toReal_nonneg) hw hs
        have he : InCone 5 b
            (windowEntryReal C (clockInsert C x₀ 4) (j + 1) y) := by
          intro c hc
          rw [windowEntryReal_work_recurrence C _ j y c (by omega),
            windowEntryReal_work_recurrence C _ j y (c + 1) hc]
          simpa only [hterm] using heSum c hc
        exact physicalBalance_inCone_of_rate_bound
          (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          (by exact_mod_cast StandaloneWork.totalWorkRate_pos C y.val hn)
          hb (hba y hy) (windowOccupation_physical_balance C _ (j + 1) y hn)
          (fun _ _ => ENNReal.toReal_nonneg) he
      · have hz : ∀ c, windowOccupationReal C (clockInsert C x₀ 4) (j + 1) y c = 0 := by
          intro c
          by_cases hc : c < 5
          · simp only [windowOccupationReal, windowOccupationVector, dif_pos hc,
              windowOccupation_zero_of_not_workReach C x₀ 4 (j + 1) y hn hy,
              ENNReal.toReal_zero]
          · simp [windowOccupationReal, windowOccupationVector, hc]
        intro c _
        simp only [hz, mul_zero, le_refl]

/-- Explicit conversion of the finite five-coordinate total. -/
theorem windowOccupationTotal_toReal_eq_psum (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C)
    (hn : ¬ WorkTerminal C x.val) :
    (windowOccupationTotal C z₀ j x).toReal =
      psum (windowOccupationReal C z₀ j x) 5 := by
  rw [windowOccupationTotal,
    ENNReal.toReal_sum (fun c _ => windowOccupation_ne_top C z₀ j x c hn)]
  simp [Fin.sum_univ_succ, psum, Finset.sum_range_succ,
    windowOccupationReal, windowOccupationVector, add_assoc]

/-- Each actual premature tick flux is at most mu(b) F times occupation. -/
theorem window_tick_flux_le (C : XCTM Q)
    (x₀ : ClocklessState C) {b F : ℝ} (hb : 0 < b)
    (hparams : ∀ x : ClocklessState C, WorkReach C x₀.val x.val →
      b * (backwardCount C x.val : ℝ) ≤ (forwardCount C x.val : ℝ) ∧
        (backwardCount C x.val : ℝ) ≤ F)
    (j : ℕ) (x : ClocklessState C) (hn : ¬ WorkTerminal C x.val) :
    (backwardCount C x.val : ℝ≥0∞) *
        windowOccupation C (clockInsert C x₀ 4) j x 0 ≤
      ENNReal.ofReal ((1 / geomWeight b 5) * F) *
        windowOccupationTotal C (clockInsert C x₀ 4) j x := by
  by_cases hx : WorkReach C x₀.val x.val
  · have hcone := windowOccupationReal_inCone C x₀ hb
      (fun y hy => (hparams y hy).1) j x hn
    have hG := geometric_weight_pos hb.le
    have hF : 0 ≤ F := (Nat.cast_nonneg (backwardCount C x.val)).trans
      (hparams x hx).2
    have hwzero : 0 ≤ windowOccupationReal C (clockInsert C x₀ 4) j x 0 :=
      ENNReal.toReal_nonneg
    have hgeom :
        windowOccupationReal C (clockInsert C x₀ 4) j x 0 * geomWeight b 5 ≤
          psum (windowOccupationReal C (clockInsert C x₀ 4) j x) 5 := by
      unfold geomWeight psum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c hc
      rw [mul_comm]
      exact ClockBalance.pow_mul_le_of_inCone hcone hb.le c (Finset.mem_range.mp hc)
    have hquot := (le_div_iff₀ hG).2 hgeom
    have hreal :
        (backwardCount C x.val : ℝ) *
            windowOccupationReal C (clockInsert C x₀ 4) j x 0 ≤
          ((1 / geomWeight b 5) * F) *
            psum (windowOccupationReal C (clockInsert C x₀ 4) j x) 5 := by
      calc
        (backwardCount C x.val : ℝ) *
            windowOccupationReal C (clockInsert C x₀ 4) j x 0 ≤
            F * windowOccupationReal C (clockInsert C x₀ 4) j x 0 :=
          mul_le_mul_of_nonneg_right (hparams x hx).2 hwzero
        _ ≤ F *
            (psum (windowOccupationReal C (clockInsert C x₀ 4) j x) 5 /
              geomWeight b 5) := mul_le_mul_of_nonneg_left hquot hF
        _ = _ := by ring
    have hcoef : 0 ≤ (1 / geomWeight b 5) * F :=
      mul_nonneg (div_nonneg zero_le_one hG.le) hF
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (by simp)
        (windowOccupation_ne_top C _ j x 0 hn))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (windowOccupationTotal_ne_top C _ j x hn))).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hcoef, windowOccupationTotal_toReal_eq_psum C _ j x hn]
    simpa only [windowOccupationReal, windowOccupationVector,
      dif_pos (show (0 : ℕ) < 5 by norm_num)] using hreal
  · rw [windowOccupation_zero_of_not_workReach C x₀ 4 j x hn hx 0, mul_zero]
    exact bot_le

/-- T41 §8.2, summed tick estimate before the standalone-work comparison. -/
theorem window_tick_flux_sum_le (C : XCTM Q)
    (x₀ : ClocklessState C) {b F : ℝ} (hb : 0 < b)
    (hparams : ∀ x : ClocklessState C, WorkReach C x₀.val x.val →
      b * (backwardCount C x.val : ℝ) ≤ (forwardCount C x.val : ℝ) ∧
        (backwardCount C x.val : ℝ) ≤ F) :
    (∑' j : ℕ, ∑' x : ClocklessState C,
      if ¬ WorkTerminal C x.val then
        (backwardCount C x.val : ℝ≥0∞) *
          windowOccupation C (clockInsert C x₀ 4) j x 0
      else 0) ≤
      ENNReal.ofReal ((1 / geomWeight b 5) * F) *
        (∑' j : ℕ, ∑' x : ClocklessState C,
          if ¬ WorkTerminal C x.val then
            windowOccupationTotal C (clockInsert C x₀ 4) j x
          else 0) := by
  classical
  calc
    _ ≤ ∑' j : ℕ, ∑' x : ClocklessState C,
        ENNReal.ofReal ((1 / geomWeight b 5) * F) *
          (if ¬ WorkTerminal C x.val then
            windowOccupationTotal C (clockInsert C x₀ 4) j x else 0) := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hn : ¬ WorkTerminal C x.val
      · simpa only [if_pos hn] using window_tick_flux_le C x₀ hb hparams j x hn
      · simp only [if_neg hn, mul_zero, le_refl]
    _ = _ := by
      simp_rw [ENNReal.tsum_mul_left]

end WindowAnalysis

namespace WindowAnalysis

/-- A single inserted clock molecule has total clock count one. -/
theorem clockMoleculeCount_clockInsert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) :
    clockMoleculeCount C (clockInsert C x c) = 1 := by
  classical
  simp [clockMoleculeCount, clockInsert_clock]

/-- Two different jump indices cannot both be the first premature tick. -/
theorem prematureTickEvents_pairwise (C : XCTM Q) (z₀ : State (Sp C)) :
    Pairwise (Function.onFun Disjoint
      (fun n : ℕ => {ω | tickCount C z₀ ω n = 0} ∩
        {ω | BadTickAt C z₀ ω n})) := by
  intro n m hne
  refine Set.disjoint_left.mpr ?_
  intro ω hn hm
  have hzeron : tickCount C z₀ ω n = 0 := hn.1
  have hzerom : tickCount C z₀ ω m = 0 := hm.1
  have hsuccn := tickCount_succ_of_tick C z₀ ω n hn.2.1
  have hsuccm := tickCount_succ_of_tick C z₀ ω m hm.2.1
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hmono := tickCount_mono C z₀ ω (show n + 1 ≤ m by omega)
    change tickCount C z₀ ω (n + 1) ≤ tickCount C z₀ ω m at hmono
    omega
  · exact hne heq
  · have hmono := tickCount_mono C z₀ ω (show m + 1 ≤ n by omega)
    change tickCount C z₀ ω (m + 1) ≤ tickCount C z₀ ω n at hmono
    omega

theorem prematureTickEvent_measure_eq_sum (C : XCTM Q) (z₀ : State (Sp C)) :
    windowLaw C z₀ (prematureTickEvent C z₀) =
      ∑' n : ℕ, windowLaw C z₀
        ({ω | tickCount C z₀ ω n = 0} ∩ {ω | BadTickAt C z₀ ω n}) := by
  apply measure_iUnion (prematureTickEvents_pairwise C z₀)
  intro n
  exact
    (measurableSet_eq_fun (measurable_tickCount C z₀ n) measurable_const).inter
      (measurableSet_badTickAt C z₀ n)

private theorem measurableSet_tickLabelAt (C : XCTM Q) (n : ℕ) (b : Bool) :
    MeasurableSet {ω : LabelPath C | ω (n + 1) = some (.tick b)} := by
  classical
  let f : LabelPath C → ℕ :=
    fun ω => if ω (n + 1) = some (.tick b) then 1 else 0
  have hf : Measurable f := by
    apply measurable_of_frestrictLe (net C) (n + 1) f
    intro ω ω' hprefix
    have he := congrFun hprefix
      (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))
    change ω (n + 1) = ω' (n + 1) at he
    change (if ω (n + 1) = some (.tick b) then (1 : ℕ) else 0) =
      (if ω' (n + 1) = some (.tick b) then (1 : ℕ) else 0)
    rw [he]
  have hset : f ⁻¹' ({1} : Set ℕ) =
      {ω : LabelPath C | ω (n + 1) = some (.tick b)} := by
    ext ω
    change (if ω (n + 1) = some (.tick b) then (1 : ℕ) else 0) = 1 ↔
      ω (n + 1) = some (.tick b)
    by_cases h : ω (n + 1) = some (.tick b) <;> simp [h]
  rw [← hset]
  exact hf (measurableSet_singleton (1 : ℕ))

private def tickErasedState (C : XCTM Q) (z : State (Sp C)) :
    ClocklessState C :=
  ⟨workView C z, by funext s; cases s <;> rfl⟩

private theorem state_eq_clockInsert_zero (C : XCTM Q)
    (z : State (Sp C)) (hcount : clockMoleculeCount C z = 1)
    (hzero : 0 < z (.clock 0)) :
    z = clockInsert C (tickErasedState C z) 0 := by
  have hsum :
      z (.clock 0) + z (.clock 1) + z (.clock 2) +
        z (.clock 3) + z (.clock 4) = 1 := by
    simpa [clockMoleculeCount, Fin.sum_univ_succ, add_assoc] using hcount
  have hclock : ∀ c : Fin 5, z (.clock c) = if c = 0 then 1 else 0 := by
    intro c
    fin_cases c <;> norm_num
    · change z (.clock 0) = 1
      omega
    · change z (.clock 1) = 0
      omega
    · change z (.clock 2) = 0
      omega
    · change z (.clock 3) = 0
      omega
    · change z (.clock 4) = 0
      omega
  funext s
  cases s with
  | clock c =>
      rw [clockInsert_clock]
      exact hclock c
  | _ => simp [clockInsert, tickErasedState, workView, unit]

/-- The raw label of a first tick, partitioned by its work count, erased
state, and choice of the two backward catalysts. -/
private noncomputable def tickExitPiece (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ)
    (p : ℕ × (ClocklessState C × Bool)) : Set (LabelPath C) := by
  classical
  exact if ¬ WorkTerminal C p.2.1.val ∧
      0 < p.2.1.val (if p.2.2 then .backwardLatent else .backward) then
    windowEvent C z₀ n p.1 (clockInsert C p.2.1 0) ∩
      {ω | ω (n + 1) = some (.tick p.2.2)}
  else ∅

private theorem measurableSet_tickExitPiece (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (p : ℕ × (ClocklessState C × Bool)) :
    MeasurableSet (tickExitPiece C z₀ n p) := by
  classical
  by_cases hcond : ¬ WorkTerminal C p.2.1.val ∧
      0 < p.2.1.val (if p.2.2 then .backwardLatent else .backward)
  · rw [tickExitPiece, if_pos hcond]
    exact (measurableSet_windowEvent C z₀ n _ _).inter
      (measurableSet_tickLabelAt C n p.2.2)
  · rw [tickExitPiece, if_neg hcond]
    exact MeasurableSet.empty

private theorem tickExitPieces_pairwise (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) :
    Pairwise (Function.onFun Disjoint (tickExitPiece C z₀ n)) := by
  classical
  intro p q hpq
  refine Set.disjoint_left.mpr ?_
  intro ω hp hq
  have hpcond : ¬ WorkTerminal C p.2.1.val ∧
      0 < p.2.1.val (if p.2.2 then .backwardLatent else .backward) := by
    by_contra h
    simp [tickExitPiece, h] at hp
  have hqcond : ¬ WorkTerminal C q.2.1.val ∧
      0 < q.2.1.val (if q.2.2 then .backwardLatent else .backward) := by
    by_contra h
    simp [tickExitPiece, h] at hq
  rw [tickExitPiece, if_pos hpcond] at hp
  rw [tickExitPiece, if_pos hqcond] at hq
  have hj : p.1 = q.1 :=
    (windowEvent_count C z₀ n _ _ hp.1).symm.trans
      (windowEvent_count C z₀ n _ _ hq.1)
  have hz : clockInsert C p.2.1 0 = clockInsert C q.2.1 0 :=
    (windowEvent_state C z₀ n _ _ hp.1).symm.trans
      (windowEvent_state C z₀ n _ _ hq.1)
  have hpairs : (p.2.1, (0 : Fin 5)) = (q.2.1, (0 : Fin 5)) :=
    clockInsert_injective C hz
  have hx : p.2.1 = q.2.1 :=
    congrArg (fun r : ClocklessState C × Fin 5 => r.1) hpairs
  have hr : (.tick p.2.2 : Rx C) = .tick q.2.2 :=
    Option.some.inj (hp.2.symm.trans hq.2)
  have hb : p.2.2 = q.2.2 := by injection hr
  exact hpq (Prod.ext hj (Prod.ext hx hb))

private theorem firstPrematureTick_ae_pieces (C : XCTM Q)
    (z₀ : State (Sp C)) (hclock : clockMoleculeCount C z₀ = 1) (n : ℕ) :
    (({ω | tickCount C z₀ ω n = 0} ∩ {ω | BadTickAt C z₀ ω n}) :
      Set (LabelPath C)) =ᵐ[windowLaw C z₀]
        (⋃ p, tickExitPiece C z₀ n p : Set (LabelPath C)) := by
  classical
  have hlegal : ∀ᵐ ω ∂windowLaw C z₀,
      ∀ m, pathFired (net C) z₀ ω m = ω (m + 1) :=
    rawLaw_ae_fired_eq_label C z₀
  filter_upwards [hlegal] with ω hω
  apply propext
  constructor
  · rintro ⟨hcount, htick, hnonterminal⟩
    cases hF : pathFired (net C) z₀ ω n with
    | none => simp [TickAt, firedTick, hF] at htick
    | some r =>
        have hr : isTick r = true := by
          simpa [TickAt, firedTick, hF] using htick
        obtain ⟨b, rfl⟩ : ∃ b : Bool, r = .tick b := by
          cases r <;> simp_all [isTick]
        have hv := pathFired_valid (net C) z₀ ω n
        simp only [hF] at hv
        let z := pathState (net C) z₀ ω n
        let x := tickErasedState C z
        have hrate : rate C (.tick b) z ≠ 0 :=
          (enabled_iff C (.tick b) z).mp hv.1
        have hzpos : 0 < z (.clock 0) := by
          apply Nat.pos_of_ne_zero
          intro hz
          apply hrate
          cases b <;> simp [rate, sourceLeft, sourceRight, hz]
        have hcpos : 0 < z (if b then .backwardLatent else .backward) := by
          apply Nat.pos_of_ne_zero
          intro hz
          apply hrate
          cases b <;> simp_all [rate, sourceLeft, sourceRight]
        have hx : z = clockInsert C x 0 :=
          state_eq_clockInsert_zero C z
            (clockMoleculeCount_path_one C z₀ hclock ω n) hzpos
        have hcat : 0 < x.val (if b then .backwardLatent else .backward) := by
          cases b <;> simpa [x, tickErasedState, workView] using hcpos
        have hnt : ¬ WorkTerminal C x.val := by
          intro ht
          apply hnonterminal
          change WorkTerminal C z
          rw [hx]
          exact (workTerminal_clockInsert C x 0).mpr ht
        refine Set.mem_iUnion.mpr ⟨(windowCount C z₀ n ω, x, b), ?_⟩
        rw [tickExitPiece, if_pos ⟨hnt, hcat⟩]
        refine ⟨?_, (hω n).symm.trans hF⟩
        exact (windowEvent_iff C z₀ n _ _ ω).mpr ⟨rfl, hcount, hx⟩
  · intro hpiece
    obtain ⟨⟨j, x, b⟩, hp⟩ := Set.mem_iUnion.mp hpiece
    by_cases hcond : ¬ WorkTerminal C x.val ∧
        0 < x.val (if b then .backwardLatent else .backward)
    · rw [tickExitPiece, if_pos hcond] at hp
      obtain ⟨_, hcount, hstate⟩ :=
        (windowEvent_iff C z₀ n j (clockInsert C x 0) ω).mp hp.1
      have hF : pathFired (net C) z₀ ω n = some (.tick b) :=
        (hω n).trans hp.2
      have htick : TickAt C z₀ ω n := by
        simp [TickAt, firedTick, hF, isTick]
      have hnt : ¬ WorkTerminal C (pathState (net C) z₀ ω n) := by
        rw [hstate]
        exact fun ht => hcond.1 ((workTerminal_clockInsert C x 0).mp ht)
      exact ⟨hcount, htick, hnt⟩
    · simp [tickExitPiece, hcond] at hp

private theorem firstPrematureTick_measure_eq_pieces (C : XCTM Q)
    (z₀ : State (Sp C)) (hclock : clockMoleculeCount C z₀ = 1) (n : ℕ) :
    windowLaw C z₀
        ({ω | tickCount C z₀ ω n = 0} ∩ {ω | BadTickAt C z₀ ω n}) =
      ∑' p, windowLaw C z₀ (tickExitPiece C z₀ n p) := by
  calc
    windowLaw C z₀
        ({ω | tickCount C z₀ ω n = 0} ∩ {ω | BadTickAt C z₀ ω n}) =
        windowLaw C z₀ (⋃ p, tickExitPiece C z₀ n p) :=
      measure_congr (firstPrematureTick_ae_pieces C z₀ hclock n)
    _ = _ := measure_iUnion (tickExitPieces_pairwise C z₀ n)
      (measurableSet_tickExitPiece C z₀ n)

private theorem tick_pmf_eq_rate_div_total (C : XCTM Q)
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

private theorem tick_pmf_clockInsert_zero (C : XCTM Q)
    (x : ClocklessState C) (b : Bool)
    (hb : 0 < x.val (if b then .backwardLatent else .backward)) :
    massActionPMF (net C) (net_hasPositiveRates C)
        (clockInsert C x 0) (some (.tick b)) =
      (x.val (if b then .backwardLatent else .backward) : ℝ≥0∞) /
        ((net C).totalPropensity (clockInsert C x 0) : ℝ≥0∞) := by
  have hr : rate C (.tick b) (clockInsert C x 0) =
      x.val (if b then .backwardLatent else .backward) := by
    cases b <;>
      simp [rate, sourceLeft, sourceRight, clockInsert, unit, clockless_clock_zero]
  have he : (rxn C (.tick b)).enabled (clockInsert C x 0) := by
    rw [enabled_iff, hr]
    exact Nat.ne_of_gt hb
  rw [tick_pmf_eq_rate_div_total C _ _ he, hr]

private theorem tickExitPiece_sum (C : XCTM Q) (z₀ : State (Sp C))
    (j : ℕ) (x : ClocklessState C) (b : Bool) :
    (∑' n, windowLaw C z₀ (tickExitPiece C z₀ n (j, x, b))) =
      if ¬ WorkTerminal C x.val then
        (x.val (if b then .backwardLatent else .backward) : ℝ≥0∞) *
          windowOccupation C z₀ j x 0
      else 0 := by
  classical
  by_cases hnt : ¬ WorkTerminal C x.val
  · by_cases hb : 0 < x.val (if b then .backwardLatent else .backward)
    · have hcond : ¬ WorkTerminal C x.val ∧
          0 < x.val (if b then .backwardLatent else .backward) := ⟨hnt, hb⟩
      simp only [tickExitPiece, if_pos hcond, if_pos hnt]
      simp_rw [windowLaw_event_label]
      rw [ENNReal.tsum_mul_right]
      change windowOcc C z₀ j (clockInsert C x 0) *
        massActionPMF (net C) (net_hasPositiveRates C)
          (clockInsert C x 0) (some (.tick b)) = _
      rw [tick_pmf_clockInsert_zero C x b hb]
      unfold windowOccupation
      simp only [div_eq_mul_inv]
      ac_rfl
    · have hz : x.val (if b then .backwardLatent else .backward) = 0 :=
        Nat.eq_zero_of_not_pos hb
      simp [tickExitPiece, hnt, hb, hz]
  · simp [tickExitPiece, hnt]

/-- FIX3-SCWB-T41 §8.2: the actual first-premature-tick probability is the
sum of tick-exit fluxes from nonterminal work states. This identity needs
only one clock molecule, not a cone or a work-duration estimate. -/
theorem prematureTickEvent_measure_eq_flux (C : XCTM Q)
    (z₀ : State (Sp C)) (hclock : clockMoleculeCount C z₀ = 1) :
    windowLaw C z₀ (prematureTickEvent C z₀) =
      ∑' j : ℕ, ∑' x : ClocklessState C,
        if ¬ WorkTerminal C x.val then
          (backwardCount C x.val : ℝ≥0∞) * windowOccupation C z₀ j x 0
        else 0 := by
  classical
  calc
    windowLaw C z₀ (prematureTickEvent C z₀) =
        ∑' n : ℕ, windowLaw C z₀
          ({ω | tickCount C z₀ ω n = 0} ∩ {ω | BadTickAt C z₀ ω n}) :=
      prematureTickEvent_measure_eq_sum C z₀
    _ = ∑' n : ℕ, ∑' p : ℕ × (ClocklessState C × Bool),
        windowLaw C z₀ (tickExitPiece C z₀ n p) :=
      tsum_congr (fun n => firstPrematureTick_measure_eq_pieces C z₀ hclock n)
    _ = ∑' p : ℕ × (ClocklessState C × Bool), ∑' n : ℕ,
        windowLaw C z₀ (tickExitPiece C z₀ n p) := ENNReal.tsum_comm
    _ = ∑' p : ℕ × (ClocklessState C × Bool),
        if ¬ WorkTerminal C p.2.1.val then
          (p.2.1.val (if p.2.2 then .backwardLatent else .backward) : ℝ≥0∞) *
            windowOccupation C z₀ p.1 p.2.1 0
        else 0 := by
      apply tsum_congr
      rintro ⟨j, x, b⟩
      exact tickExitPiece_sum C z₀ j x b
    _ = _ := by
      simp_rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro j
      apply tsum_congr
      intro x
      rw [tsum_fintype]
      by_cases hnt : ¬ WorkTerminal C x.val
      · simp [hnt, Fintype.sum_bool, backwardCount, Nat.cast_add, add_mul]
        <;> ac_rfl
      · simp [hnt]

end WindowAnalysis

namespace WindowAnalysis

/-- FIX3-SCWB-T41 Lemma 8.2 on the actual raw law. Only the paper's
reachable-state clock bounds are premises; flux and work domination are
proved in this file. The work duration may be infinite. -/
theorem prematureTickEvent_le_meanDuration (C : XCTM Q)
    (x₀ : ClocklessState C) {b F : ℝ} (hb : 0 < b)
    (hparams : ∀ x : ClocklessState C, WorkReach C x₀.val x.val →
      b * (backwardCount C x.val : ℝ) ≤ (forwardCount C x.val : ℝ) ∧
        (backwardCount C x.val : ℝ) ≤ F) :
    windowLaw C (clockInsert C x₀ 4)
        (prematureTickEvent C (clockInsert C x₀ 4)) ≤
      ENNReal.ofReal ((1 / geomWeight b 5) * F) *
        StandaloneWork.meanDuration C x₀.val := by
  rw [prematureTickEvent_measure_eq_flux C _
    (clockMoleculeCount_clockInsert C x₀ 4)]
  have hwork :
      (∑' j : ℕ, ∑' x : ClocklessState C,
        if ¬ WorkTerminal C x.val then
          windowOccupationTotal C (clockInsert C x₀ 4) j x else 0) ≤
        StandaloneWork.meanDuration C x₀.val := by
    simpa only [ite_not] using
      windowOccupation_nonterminal_sum_le_meanDuration C x₀ 4
  exact (window_tick_flux_sum_le C x₀ hb hparams).trans
    (mul_le_mul_left' hwork _)

/-- The clockless work start of the next window of the clean schedule. -/
def nextWindowWork (C : XCTM Q) (p : Plan C) : ClocklessState C :=
  ⟨Plan.workState C p + unit .signal, by
    cases p <;> funext s <;> cases s <;>
      simp [workView, Plan.workState, payload, unit]⟩

theorem nextLowerRatio_pos (C : XCTM Q) (p : Plan C)
    (ha : 0 < p.accuracy) : 0 < nextLowerRatio p := by
  cases p <;> simp only [Plan.accuracy, nextLowerRatio] at * <;> positivity

/-- The one-window bound with the actual clean-schedule parameters.
The sharper lower ratio is alpha/3 only for the restoration window. -/
theorem next_window_prematureTick_le_meanDuration (C : XCTM Q)
    (p : Plan C) (hs : 3 ≤ p.tape.length) (hh : Plan.halted C p = false)
    (ha : 0 < p.accuracy) :
    windowLaw C (clockInsert C (nextWindowWork C p) 4)
        (prematureTickEvent C (clockInsert C (nextWindowWork C p) 4)) ≤
      ENNReal.ofReal ((1 / geomWeight (nextLowerRatio p) 5) *
        (stateCount p.tape.length : ℝ)) *
        StandaloneWork.meanDuration C (Plan.workState C p + unit .signal) := by
  apply prematureTickEvent_le_meanDuration C (nextWindowWork C p)
    (nextLowerRatio_pos C p ha)
  intro x hx
  have hp := next_window_sharp_parameters C p hs hh hx
  have hf : (0 : ℝ) < (backwardCount C x.val : ℝ) := by
    exact_mod_cast hp.1
  refine ⟨(le_div_iff₀ hf).mp hp.2.2, ?_⟩
  exact_mod_cast hp.2.1

end WindowAnalysis

namespace StandaloneWork

/-- A work-terminal starting state has zero standalone work duration. -/
theorem meanDuration_eq_zero_of_terminal (C : XCTM Q) (start : State (Sp C))
    (ht : WorkTerminal C start) :
    meanDuration C start = 0 := by
  have hd : ∀ ω : ℕ → Option (workNet C).I, duration C start ω = 0 := by
    intro ω
    unfold duration
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    have hn : WorkTerminal C (pathState (workNet C) start ω n) :=
      terminal_persists C start ω (n := 0) ht (Nat.zero_le n)
    simp [holdingMean, hn]
  simp only [meanDuration, hd, lintegral_zero]

end StandaloneWork

namespace WindowAnalysis

/-- The work part of a two-molecule counterexample: one backward catalyst. -/
def terminalClockWork (C : XCTM Q) : ClocklessState C :=
  ⟨unit .backward, by
    funext s
    cases s <;> simp [workView, unit]⟩

theorem terminalClockWork_terminal (C : XCTM Q) :
    WorkTerminal C (terminalClockWork C).val := by
  rw [workTerminal_iff]
  intro r hr
  cases r <;>
    simp_all [terminalClockWork, isClock, rate, sourceLeft, sourceRight, unit]

theorem terminalClockWork_totalWorkRate (C : XCTM Q) :
    StandaloneWork.totalWorkRate C (terminalClockWork C).val = 0 := by
  unfold StandaloneWork.totalWorkRate
  apply Finset.sum_eq_zero
  intro r _
  exact (workTerminal_iff C _).mp (terminalClockWork_terminal C) r.val r.property

/-- One backward catalyst and one top-clock molecule have positive window
occupation even though no work reaction is enabled. -/
theorem terminalClockWork_occupation_ge_one (C : XCTM Q) :
    1 ≤ windowOccupation C
      (clockInsert C (terminalClockWork C) (Fin.last 4))
      0 (terminalClockWork C) (Fin.last 4) := by
  have hprop : (net C).totalPropensity
      (clockInsert C (terminalClockWork C) (Fin.last 4)) = 1 := by
    rw [totalPropensity_clockInsert, terminalClockWork_totalWorkRate]
    simp [terminalClockWork, backwardCount, unit]
  have hinitial : windowEvent C
      (clockInsert C (terminalClockWork C) (Fin.last 4)) 0 0
      (clockInsert C (terminalClockWork C) (Fin.last 4)) = Set.univ := by
    ext ω
    simp [windowEvent, windowExtended, extState, extOf]
  have hvisit : 1 ≤ windowOcc C
      (clockInsert C (terminalClockWork C) (Fin.last 4)) 0
      (clockInsert C (terminalClockWork C) (Fin.last 4)) := by
    change 1 ≤ ∑' n, windowLaw C
      (clockInsert C (terminalClockWork C) (Fin.last 4))
      (windowEvent C (clockInsert C (terminalClockWork C) (Fin.last 4)) n 0
        (clockInsert C (terminalClockWork C) (Fin.last 4)))
    calc
      1 = windowLaw C
          (clockInsert C (terminalClockWork C) (Fin.last 4))
          (windowEvent C (clockInsert C (terminalClockWork C) (Fin.last 4)) 0 0
            (clockInsert C (terminalClockWork C) (Fin.last 4))) := by
        rw [hinitial]
        simp
      _ ≤ _ := ENNReal.le_tsum 0
  unfold windowOccupation
  rw [hprop]
  have hone : ((1 : Rate) : ℝ≥0∞) = 1 := by
    change (((1 : Rate) : NNReal) : ℝ≥0∞) = 1
    first
    | rw [NNRat.cast_one, ENNReal.coe_one]
    | simp
    | norm_num
  rw [hone, div_one]
  exact hvisit

/-- Counterexample to an unrestricted all-state occupation bound.
The note's restriction to nonterminal work states is essential. -/
theorem terminalClockWork_not_all_occupation_le_meanDuration (C : XCTM Q) :
    ¬ (∑' j : ℕ, ∑' x : ClocklessState C,
        windowOccupationTotal C
          (clockInsert C (terminalClockWork C) (Fin.last 4)) j x) ≤
      StandaloneWork.meanDuration C (terminalClockWork C).val := by
  have hfirst :
      windowOccupation C
          (clockInsert C (terminalClockWork C) (Fin.last 4))
          0 (terminalClockWork C) (Fin.last 4) ≤
        windowOccupationTotal C
          (clockInsert C (terminalClockWork C) (Fin.last 4))
          0 (terminalClockWork C) := by
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ _)
  have hstate :
      windowOccupationTotal C
          (clockInsert C (terminalClockWork C) (Fin.last 4))
          0 (terminalClockWork C) ≤
        ∑' x : ClocklessState C, windowOccupationTotal C
          (clockInsert C (terminalClockWork C) (Fin.last 4)) 0 x :=
    ENNReal.le_tsum (terminalClockWork C)
  have htime :
      (∑' x : ClocklessState C, windowOccupationTotal C
          (clockInsert C (terminalClockWork C) (Fin.last 4)) 0 x) ≤
        ∑' j : ℕ, ∑' x : ClocklessState C, windowOccupationTotal C
          (clockInsert C (terminalClockWork C) (Fin.last 4)) j x :=
    ENNReal.le_tsum 0
  intro hbad
  have hzero := StandaloneWork.meanDuration_eq_zero_of_terminal C _
    (terminalClockWork_terminal C)
  rw [hzero] at hbad
  have hone : (1 : ℝ≥0∞) ≤ 0 :=
    (terminalClockWork_occupation_ge_one C).trans
      (hfirst.trans (hstate.trans (htime.trans hbad)))
  exact (by norm_num : ¬ ((1 : ℝ≥0∞) ≤ 0)) hone

end WindowAnalysis

end Ripple.sCRNUniversality.ClockedCTM.Unbounded
