-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingEarlyRoles.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6RoleArrivals
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCounterTail
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCalibration
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingFirstHit

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators
namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingEarlyRoles
open TimeTheorem PairLog LateF6Acceptance LateF6Hazards
open AveragingRecordedExpectation LateSamplingCounterTail LateSamplingCalibration LateSamplingFirstHit
variable {L K n : ℕ}

def RoleWindow (M R : ℕ) (f : Fin n → AgentState L K) : Prop :=
  (∀ i, Window (f i)) ∧ mainCount f = M ∧ reserveCount f = R

def RoleCapEvent (init : Cfg L K) (s M R c : ℕ) : Set (Ω L K) :=
  {ω | nonclockFrozenCount (labelsAt init ω s) = 0 ∧
    reserveFrozenCount (labelsAt init ω s) = 0 ∧
    ∃ T, s ≤ T ∧
      (∀ t, s ≤ t → t < T →
        RoleWindow M R (labelsAt init ω t) ∧
          nonclockFrozenCount (labelsAt init ω t) < c ∧
          reserveFrozenCount (labelsAt init ω t) ≤ R) ∧
      nonclockFrozenCount (labelsAt init ω T) = c ∧
      ((R : ℝ) / ((M + R : ℕ) : ℝ) + 1 / 10) * c ≤ reserveFrozenCount (labelsAt init ω T)}

def EarlyRoleEvent (init : Cfg L K) (s M R k : ℕ) : Set (Ω L K) :=
  {ω | nonclockFrozenCount (labelsAt init ω s) = 0 ∧
    reserveFrozenCount (labelsAt init ω s) = 0 ∧
    ∃ T, s ≤ T ∧
      (∀ t, s ≤ t → t < T → RoleWindow M R (labelsAt init ω t)) ∧
      frozenCount (labelsAt init ω T) < k ∧ k ≤ reserveFrozenCount (labelsAt init ω T)}

theorem reserve_frozen_le (f : Fin n → AgentState L K) :
    reserveFrozenCount f ≤ reserveCount f :=
  pool_mono f (TrackedFrozen reserveRole) (fun a => reserveRole a.role)
    (fun _ h => h.1)

theorem nonclock_frozen_le (f : Fin n → AgentState L K) :
    nonclockFrozenCount f ≤ nonclockCount f :=
  pool_mono f (TrackedFrozen mainOrReserve) (fun a => mainOrReserve a.role)
    (fun _ h => h.1)

theorem role_ratio_eq (f : Fin n → AgentState L K) {M R : ℕ}
    (hw : RoleWindow M R f) :
    reserveArrivalRatio f =
      ((R : ℝ) - reserveFrozenCount f) /
        (((M + R : ℕ) : ℝ) - nonclockFrozenCount f) := by
  have htotal : nonclockCount f = M + R := by
    rw [nonclockCount_eq, hw.2.1, hw.2.2]
  have hb : reserveFrozenCount f ≤ R := (reserve_frozen_le f).trans_eq hw.2.2
  have hc : nonclockFrozenCount f ≤ M + R :=
    (nonclock_frozen_le f).trans_eq htotal
  unfold reserveArrivalRatio
  rw [hw.2.2, htotal, Nat.cast_sub hb, Nat.cast_sub hc]

theorem role_kernel (init : Cfg L K) (hn : 2 ≤ init.card)
    (f : Fin init.card → AgentState L K) {M R : ℕ} (hw : RoleWindow M R f) :
    pairMass init reserveArrival f ≤
      ((R : ℝ) - reserveFrozenCount f) /
        (((M + R : ℕ) : ℝ) - nonclockFrozenCount f) *
          pairMass init nonclockArrival f := by
  have h := reserve_arrival_fraction f hn
  rw [role_ratio_eq f hw] at h
  exact h

theorem role_cap_tail (init : Cfg L K) (hn : 2 ≤ init.card)
    (s M R c : ℕ) (hc : c < M + R)
    (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p (RoleCapEvent init s M R c) ≤
      ENNReal.ofReal (Real.exp (-(c : ℝ) / 50)) := by
  have hC : ∀ f : Fin init.card → AgentState L K, RoleWindow M R f → ∀ d,
      nonclockFrozenCount (stepLabels f d) = nonclockFrozenCount f +
        bitNat (chosen nonclockArrival f d) := by
    intro f hf d
    exact trackedFrozenCount_step mainOrReserve mainOrReserve_ne_clock f hf.1 d
  have hB : ∀ f : Fin init.card → AgentState L K, RoleWindow M R f → ∀ d,
      reserveFrozenCount (stepLabels f d) = reserveFrozenCount f +
        bitNat (chosen reserveArrival f d) := by
    intro f hf d
    exact trackedFrozenCount_step reserveRole reserveRole_ne_clock f hf.1 d
  have h := actual_urn_tail init hn s c R (M + R) hc
    (RoleWindow M R) nonclockFrozenCount reserveFrozenCount
    nonclockArrival reserveArrival reserveArrival_implies hC hB
    (fun f hf _ _ => role_kernel init hn f hf) p (1 / 10) (by norm_num)
  change recordedFuture init s p (RoleCapEvent init s M R c) ≤
    ENNReal.ofReal (Real.exp (-2 * (1 / 10 : ℝ) ^ 2 * c)) at h
  have he : -2 * (1 / 10 : ℝ) ^ 2 * c = -(c : ℝ) / 50 := by ring
  simpa only [he] using h

theorem role_cap_union_tail (init : Cfg L K) (hn : 2 ≤ init.card)
    (s M R k : ℕ) (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p
      (⋃ c : Fin (M + R), {ω | k ≤ c.val ∧ ω ∈ RoleCapEvent init s M R c.val}) ≤
      ENNReal.ofReal (((M + R : ℕ) : ℝ) * Real.exp (-(k : ℝ) / 50)) := by
  have hc (c : Fin (M + R)) :
      recordedFuture init s p {ω | k ≤ c.val ∧ ω ∈ RoleCapEvent init s M R c.val} ≤
        ENNReal.ofReal (Real.exp (-(k : ℝ) / 50)) := by
    by_cases hk : k ≤ c.val
    · have he : {ω | k ≤ c.val ∧ ω ∈ RoleCapEvent init s M R c.val} =
          RoleCapEvent init s M R c.val := by ext ω; simp only [hk, true_and, Set.mem_setOf_eq]
      rw [he]
      refine (role_cap_tail init hn s M R c.val c.isLt p).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
      have hk' : (k : ℝ) ≤ c.val := by exact_mod_cast hk
      linarith
    · simp [hk]
  calc
    recordedFuture init s p
        (⋃ c : Fin (M + R), {ω | k ≤ c.val ∧ ω ∈ RoleCapEvent init s M R c.val}) ≤
        ∑' c : Fin (M + R),
          recordedFuture init s p {ω | k ≤ c.val ∧ ω ∈ RoleCapEvent init s M R c.val} :=
      measure_iUnion_le _
    _ ≤ ∑' _ : Fin (M + R), ENNReal.ofReal (Real.exp (-(k : ℝ) / 50)) :=
      ENNReal.tsum_le_tsum hc
    _ = _ := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
        ← ENNReal.ofReal_nsmul]
      simp only [Fintype.card_fin, nsmul_eq_mul]

theorem role_density_ratio {n M R : ℕ}
    (hn : 0 < n) (hM : 12 * n ≤ 25 * M) (hR : 25 * R ≤ 7 * n) :
    (R : ℝ) / ((M + R : ℕ) : ℝ) + 1 / 10 ≤ 1 / 2 := by
  have hMpos : 0 < M := by omega
  have htotal : (0 : ℝ) < ((M + R : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + R)
  have hrel : 12 * R ≤ 7 * M := by omega
  have hrel' : (12 : ℝ) * R ≤ 7 * M := by exact_mod_cast hrel
  have hr : (R : ℝ) / ((M + R : ℕ) : ℝ) ≤ 7 / 19 := by
    apply (div_le_iff₀ htotal).2
    push_cast
    linarith
  linarith

theorem early_capacity {n M R : ℕ} (hn : 1000000 ≤ n)
    (hM : 12 * n ≤ 25 * M) :
    0 < Nat.ceil ((n : ℝ) / 1000000) ∧
      2 * Nat.ceil ((n : ℝ) / 1000000) ≤ M + R := by
  have hn' : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hM' : (12 : ℝ) * n ≤ 25 * M := by exact_mod_cast hM
  have hlo := Nat.le_ceil ((n : ℝ) / 1000000)
  have hhi := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (n : ℝ) / 1000000 by positivity)
  have hpos : (0 : ℝ) < (Nat.ceil ((n : ℝ) / 1000000) : ℝ) := by nlinarith
  have hsmall : (2 : ℝ) * (Nat.ceil ((n : ℝ) / 1000000) : ℝ) ≤ M := by nlinarith
  constructor
  · exact_mod_cast hpos
  · have hs : 2 * Nat.ceil ((n : ℝ) / 1000000) ≤ M := by exact_mod_cast hsmall
    omega

theorem early_cap_union_factor {n H k : ℕ} (hH : H ≤ n)
    (hlog : (1000000000000 : ℝ) < Real.log (n : ℝ))
    (hk : (n : ℝ) / 800000000000000 ≤ (k : ℝ) / 100) :
    (H : ℝ) * Real.exp (-(k : ℝ) / 50) ≤
      Real.exp (-(n : ℝ) / 800000000000000) := by
  have hn : 0 < n := by have h := logarithm_population_lower hlog; omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdecay := late_exponential_dominates_logarithm hlog
  rw [Real.exp_log hn'] at hdecay
  have hlogk : Real.log (n : ℝ) ≤ (k : ℝ) / 100 := by linarith
  have hH' : (H : ℝ) ≤ n := by exact_mod_cast hH
  calc
    (H : ℝ) * Real.exp (-(k : ℝ) / 50) ≤
        (n : ℝ) * Real.exp (-(k : ℝ) / 50) :=
      mul_le_mul_of_nonneg_right hH' (Real.exp_nonneg _)
    _ = Real.exp (Real.log (n : ℝ) - (k : ℝ) / 50) := by
      calc
        (n : ℝ) * Real.exp (-(k : ℝ) / 50) =
            Real.exp (Real.log (n : ℝ)) * Real.exp (-(k : ℝ) / 50) := by
          rw [Real.exp_log hn']
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(k : ℝ) / 100) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ Real.exp (-(n : ℝ) / 800000000000000) := Real.exp_le_exp.mpr (by linarith)

theorem label_event_measurable (init : Cfg L K) (t : ℕ)
    (P : (Fin init.card → AgentState L K) → Prop) :
    MeasurableSet {ω | P (labelsAt init ω t)} :=
  (Set.to_countable {q : (i : Finset.Iic t) → Draw L K |
    P (prefixLabels init t q)}).measurableSet.preimage
      ((measurable_pairLog_prefix L K t).mono
        ((pairLogFiltration L K).le t) le_rfl)

theorem role_prefix_measurable (init : Cfg L K) (s M R T : ℕ) :
    MeasurableSet {ω | ∀ t, s ≤ t → t < T → RoleWindow M R (labelsAt init ω t)} := by
  have ht (t : ℕ) :
      MeasurableSet {ω | s ≤ t → t < T → RoleWindow M R (labelsAt init ω t)} := by
    by_cases hs : s ≤ t
    · by_cases hT : t < T
      · simpa only [hs, hT, true_implies] using
          label_event_measurable init t (RoleWindow M R)
      · simpa only [hT, false_implies, implies_true, Set.setOf_true] using
          (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Ω L K)))
    · simpa only [hs, false_implies, Set.setOf_true] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Ω L K)))
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter ht

theorem earlyRoleEvent_measurable (init : Cfg L K) (s M R k : ℕ) :
    MeasurableSet (EarlyRoleEvent init s M R k) := by
  have hT (T : ℕ) : MeasurableSet {ω | s ≤ T ∧
      (∀ t, s ≤ t → t < T → RoleWindow M R (labelsAt init ω t)) ∧
      frozenCount (labelsAt init ω T) < k ∧ k ≤ reserveFrozenCount (labelsAt init ω T)} := by
    by_cases hs : s ≤ T
    · simpa only [hs, true_and] using
        (role_prefix_measurable init s M R T).inter
          ((label_event_measurable init T (fun f => frozenCount f < k)).inter
            (label_event_measurable init T (fun f => k ≤ reserveFrozenCount f)))
    · simpa only [hs, false_and, Set.setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set (Ω L K)))
  have hex : MeasurableSet {ω | ∃ T, s ≤ T ∧
      (∀ t, s ≤ t → t < T → RoleWindow M R (labelsAt init ω t)) ∧
      frozenCount (labelsAt init ω T) < k ∧ k ≤ reserveFrozenCount (labelsAt init ω T)} := by
    have he : {ω : Ω L K | ∃ T, s ≤ T ∧
        (∀ t, s ≤ t → t < T → RoleWindow M R (labelsAt init ω t)) ∧
        frozenCount (labelsAt init ω T) < k ∧ k ≤ reserveFrozenCount (labelsAt init ω T)} =
        ⋃ T, {ω | s ≤ T ∧
          (∀ t, s ≤ t → t < T → RoleWindow M R (labelsAt init ω t)) ∧
          frozenCount (labelsAt init ω T) < k ∧ k ≤ reserveFrozenCount (labelsAt init ω T)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [he]
    exact MeasurableSet.iUnion hT
  exact (label_event_measurable init s (fun f => nonclockFrozenCount f = 0)).inter
    ((label_event_measurable init s (fun f => reserveFrozenCount f = 0)).inter hex)

theorem role_unit_steps (init : Cfg L K) (ω : Ω L K) (s T M R : ℕ)
    (hw : ∀ t, s ≤ t → t < T → RoleWindow M R (labelsAt init ω t)) :
    UnitSteps (fun t => nonclockFrozenCount (labelsAt init ω t))
      (fun t => reserveFrozenCount (labelsAt init ω t)) s T := by
  intro t hst htT
  let f := labelsAt init ω t
  let d := ω (t + 1)
  refine ⟨bitNat (chosen nonclockArrival f d), bitNat (chosen reserveArrival f d),
    ?_, ?_, ?_, ?_⟩
  · beta_reduce
    rw [labelsAt_succ]
    exact trackedFrozenCount_step mainOrReserve mainOrReserve_ne_clock f (hw t hst htT).1 d
  · beta_reduce
    rw [labelsAt_succ]
    exact trackedFrozenCount_step reserveRole reserveRole_ne_clock f (hw t hst htT).1 d
  · have h := bitNat_zero_one (chosen nonclockArrival f d)
    omega
  · apply bitNat_mono
    rintro ⟨i, j, hs, he⟩
    exact ⟨i, j, hs, reserveArrival_implies f i j he⟩

theorem early_role_subset_cap_union (init : Cfg L K) (s M R k : ℕ)
    (hn : 0 < init.card) (hM : 12 * init.card ≤ 25 * M)
    (hR : 25 * R ≤ 7 * init.card) (hk : 0 < k) (hcap : 2 * k ≤ M + R) :
    EarlyRoleEvent init s M R k ⊆
      ⋃ c : Fin (M + R), {ω | k ≤ c.val ∧ ω ∈ RoleCapEvent init s M R c.val} := by
  rintro ω ⟨hzeroC, hzeroB, T, hsT, hw, hmain, hbad⟩
  have hsteps := role_unit_steps init ω s T M R hw
  have hgap : nonclockFrozenCount (labelsAt init ω T) -
      reserveFrozenCount (labelsAt init ω T) < k := by
    have he := nonclockFrozenCount_eq (labelsAt init ω T)
    omega
  obtain ⟨v, hsv, hvT, hBv, hlow, hhigh, hbefore⟩ :=
    first_bad_hit_cap hsteps hzeroC hzeroB hsT hk hbad hgap
  let c : Fin (M + R) :=
    ⟨nonclockFrozenCount (labelsAt init ω v), lt_of_lt_of_le hhigh hcap⟩
  refine Set.mem_iUnion.mpr ⟨c, ?_⟩
  refine ⟨hlow, hzeroC, hzeroB, v, hsv, ?_, rfl, ?_⟩
  · intro t hst htv
    have hwt := hw t hst (lt_of_lt_of_le htv hvT)
    exact ⟨hwt, hbefore t hst htv, (reserve_frozen_le _).trans_eq hwt.2.2⟩
  · have hr := role_density_ratio hn hM hR
    have hc : (nonclockFrozenCount (labelsAt init ω v) : ℝ) ≤ 2 * k := by
      exact_mod_cast (le_of_lt hhigh)
    rw [hBv]
    calc
      ((R : ℝ) / ((M + R : ℕ) : ℝ) + 1 / 10) * c.val ≤
          (1 / 2 : ℝ) * c.val :=
        mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)
      _ ≤ k := by dsimp only [c]; nlinarith

/-- One shared early-role test. The finite cap union is paid using the stronger
exp(-k/50) bound; it does not enlarge the review's final test prefactor. -/
theorem recorded_early_role_tail (init : Cfg L K) (s M R : ℕ)
    (hM : 12 * init.card ≤ 25 * M) (hR : 25 * R ≤ 7 * init.card)
    (hsize : M + R ≤ init.card)
    (hlog : (1000000000000 : ℝ) < Real.log (init.card : ℝ))
    (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p
      (EarlyRoleEvent init s M R (Nat.ceil ((init.card : ℝ) / 1000000))) ≤
        ENNReal.ofReal (Real.exp (-(init.card : ℝ) / 800000000000000)) := by
  have hnlarge := logarithm_population_lower hlog
  have hn : 2 ≤ init.card := by omega
  have hcap := early_capacity (R := R) hnlarge hM
  calc
    recordedFuture init s p
        (EarlyRoleEvent init s M R (Nat.ceil ((init.card : ℝ) / 1000000))) ≤
        recordedFuture init s p
          (⋃ c : Fin (M + R), {ω | Nat.ceil ((init.card : ℝ) / 1000000) ≤ c.val ∧
            ω ∈ RoleCapEvent init s M R c.val}) :=
      measure_mono (early_role_subset_cap_union init s M R _ (by omega)
        hM hR hcap.1 hcap.2)
    _ ≤ ENNReal.ofReal (((M + R : ℕ) : ℝ) *
        Real.exp (-(Nat.ceil ((init.card : ℝ) / 1000000) : ℝ) / 50)) :=
      role_cap_union_tail init hn s M R _ p
    _ ≤ ENNReal.ofReal (Real.exp (-(init.card : ℝ) / 800000000000000)) :=
      ENNReal.ofReal_le_ofReal (early_cap_union_factor hsize hlog
        (early_role_exponent init.card))

end Ripple.PopulationProtocol.ExactMajority.LateSamplingEarlyRoles
end
