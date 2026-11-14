import Ripple.PopulationProtocol.ExactMajority.Probability.PairLog
import Ripple.PopulationProtocol.ExactMajority.Probability.ScalarTails
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceJansonDrift
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Sharp phase-threshold epidemic tails

Node N08 of DOTY-LEAN-PLAN. Both ordered mixed-pair orientations are counted.
The labeled next-draw estimate and its conditional-expectation version identify
the actual adapted SI progress rate. The milestone engine implements the same
comparison by a killed remaining-work moment; its full product is evaluated on
an auxiliary independent geometric product space using ScalarTails.

The final estimate is under the original pair-log law. It retains the mass of
each genuine first-seed prefix before applying the disjoint seed splice.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.ThresholdEpidemic

open TimeTheorem PairLog

open AdvanceEpidemics RoleSplitConcentration
attribute [local instance] Classical.propDecidable

private theorem threshold_pair_advances {L K : ℕ} (q : ℕ)
    (a b : AgentState L K)
    (hmixed : (geP q a ∧ ¬ geP q b) ∨ (¬ geP q a ∧ geP q b)) :
    Multiset.countP (geP q) ({a, b} : Multiset (AgentState L K)) + 1 ≤
      Multiset.countP (geP q)
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) := by
  have hmax : q ≤ max a.phase.val b.phase.val := by
    rcases hmixed with ⟨ha, _⟩ | ⟨_, hb⟩
    · exact ha.trans (le_max_left _ _)
    · exact hb.trans (le_max_right _ _)
  have ha' : geP q (Transition L K a b).1 :=
    hmax.trans (Transition_left_phase_ge_pair_max a b)
  have hb' : geP q (Transition L K a b).2 :=
    hmax.trans (Transition_right_phase_ge_pair_max a b)
  rw [countP_geP_pair, countP_geP_pair, if_pos ha', if_pos hb']
  rcases hmixed with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [if_pos ha, if_neg hb]
  · rw [if_neg ha, if_pos hb]

private theorem threshold_count_advances {L K : ℕ} (q : ℕ)
    (c : Config (AgentState L K)) (a b : AgentState L K)
    (happ : Protocol.Applicable c a b)
    (hmixed : (geP q a ∧ ¬ geP q b) ∨ (¬ geP q a ∧ geP q b)) :
    geCount q c + 1 ≤
      geCount q (Protocol.stepOrSelf (NonuniformMajority L K) c a b) := by
  have hsub : ({a, b} : Multiset (AgentState L K)) ≤ c := happ
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  unfold geCount
  rw [hstep, Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair : Multiset.countP (geP q) ({a, b} : Multiset (AgentState L K)) ≤
      Multiset.countP (geP q) c := Multiset.countP_le_of_le _ hsub
  have hadv := threshold_pair_advances q a b hmixed
  have key : Multiset.countP (geP q) c + 1 ≤
      Multiset.countP (geP q) c - Multiset.countP (geP q) ({a, b} : Multiset (AgentState L K)) +
        Multiset.countP (geP q)
          ({(Transition L K a b).1, (Transition L K a b).2} : Multiset (AgentState L K)) := by
    omega
  convert key

private theorem sum_count_predicate {L K : ℕ}
    (c : Config (AgentState L K)) (P : AgentState L K → Prop) :
    (∑ a ∈ Finset.univ.filter P, c.count a) =
      Multiset.countP P c := by
  rw [Multiset.countP_eq_card_filter]
  have hcount : ∀ a ∈ Finset.univ.filter P,
      c.count a = Multiset.count a (c.filter P) := by
    intro a ha
    rw [Config.count, Multiset.count_filter, if_pos (Finset.mem_filter.mp ha).2]
  rw [Finset.sum_congr rfl hcount, Multiset.sum_count_eq_card]
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Multiset.mem_filter.mp ha).2⟩

private theorem threshold_applicable_of_mem_distinct {L K : ℕ}
    {c : Config (AgentState L K)} {x y : AgentState L K}
    (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
    Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]
    omega
  · by_cases hay : a = y
    · subst hay
      rw [if_neg hax, if_pos rfl]
      omega
    · rw [if_neg hax, if_neg hay]
      omega

/-- Both ordered mixed rectangles contribute, even when the lower-phase
member is several phases below the threshold. -/
private theorem threshold_advance_probability {L K n : ℕ}
    (hn : 2 ≤ n) (q : ℕ) (hq : 1 ≤ q)
    (c : Config (AgentState L K)) (hcard : c.card = n) :
    ENNReal.ofReal
        (((2 * geCount q c * (n - geCount q c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {d | geCount q c + 1 ≤ geCount q d} := by
  let A := Finset.univ.filter (fun a : AgentState L K => geP q a)
  let B := Finset.univ.filter (fun a : AgentState L K => ¬ geP q a)
  let R := (A ×ˢ B) ∪ (B ×ˢ A)
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b := by
    intro a ha b hb hab
    have ha' : geP q a := (Finset.mem_filter.mp ha).2
    have hb' : ¬ geP q b := (Finset.mem_filter.mp hb).2
    exact hb' (hab ▸ ha')
  have hBA : ∀ b ∈ B, ∀ a ∈ A, b ≠ a :=
    fun b hb a ha => (hAB a ha b hb).symm
  have hdisj : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    refine Finset.disjoint_left.mpr ?_
    intro pr hpr hpr'
    exact hAB pr.1 (Finset.mem_product.mp hpr).1
      pr.1 (Finset.mem_product.mp hpr').1 rfl
  have hA : (∑ a ∈ A, c.count a) = geCount q c :=
    sum_count_geP q c
  have hB : (∑ a ∈ B, c.count a) = n - geCount q c := by
    have h1 : (∑ a ∈ B, c.count a) = Multiset.countP (fun a => ¬ geP q a) c := by
      convert sum_count_predicate c (fun a => ¬ geP q a)
    have hsplit : Multiset.card c = geCount q c + Multiset.countP (fun a => ¬ geP q a) c := by
      unfold geCount
      convert Multiset.card_eq_countP_add_countP (geP q) c
    rw [hcard] at hsplit
    rw [h1]
    omega
  have hsum : (∑ pr ∈ R, c.interactionCount pr.1 pr.2) =
      2 * geCount q c * (n - geCount q c) := by
    rw [show R = (A ×ˢ B) ∪ (B ×ˢ A) from rfl, Finset.sum_union hdisj,
      sum_interactionCount_cross_disjoint c A B hAB,
      sum_interactionCount_cross_disjoint c B A hBA, hA, hB]
    ring
  have hqpred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hadv := advance_prob_of_rect (q - 1) n hn c hcard R
    (2 * geCount q c * (n - geCount q c))
    (by
      rintro ⟨a, b⟩ hpr ha hb _
      have hmixed :
          (geP q a ∧ ¬ geP q b) ∨ (¬ geP q a ∧ geP q b) := by
        rcases Finset.mem_union.mp hpr with hpr | hpr
        · exact Or.inl ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hpr).1).2,
            (Finset.mem_filter.mp (Finset.mem_product.mp hpr).2).2⟩
        · exact Or.inr ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hpr).1).2,
            (Finset.mem_filter.mp (Finset.mem_product.mp hpr).2).2⟩
      have hab : a ≠ b := by
        intro hab
        rcases hmixed with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
        · exact hb' (hab ▸ ha')
        · exact ha' (hab.symm ▸ hb')
      have happ : Protocol.Applicable c a b :=
        threshold_applicable_of_mem_distinct (Multiset.one_le_count_iff_mem.mp ha)
          (Multiset.one_le_count_iff_mem.mp hb) hab
      simpa only [hqpred] using threshold_count_advances q c a b happ hmixed)
    (by rw [hsum])
  simpa only [hqpred] using hadv

private noncomputable def thresholdRate (n : ℕ) (i : Fin (n - 1)) : ℝ :=
  2 * ((i.val : ℝ) + 1) *
    ((n : ℝ) - ((i.val : ℝ) + 1)) /
    ((n : ℝ) * ((n : ℝ) - 1))

private theorem thresholdRate_bounds {n : ℕ} (hn : 2 ≤ n)
    (i : Fin (n - 1)) :
    0 < thresholdRate n i ∧ thresholdRate n i ≤ 1 ∧
      1 / (n : ℝ) < thresholdRate n i := by
  have hi : i.val + 1 < n := by have := i.isLt; omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (i.val : ℝ) + 1 < n := by exact_mod_cast hi
  have hiRpos : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
  have hnRpos : (0 : ℝ) < n := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hnum : 0 < 2 * ((i.val : ℝ) + 1) *
      ((n : ℝ) - ((i.val : ℝ) + 1)) :=
    mul_pos (mul_pos (by norm_num) hiRpos) (sub_pos.mpr hiR)
  refine ⟨div_pos hnum hden, ?_, ?_⟩
  · unfold thresholdRate
    rw [div_le_one hden]
    nlinarith [sq_nonneg ((n : ℝ) - 2 * ((i.val : ℝ) + 1)),
      mul_nonneg hnRpos.le (sub_nonneg.mpr hnR)]
  · have hfloorN := sub_one_le_mul_sub n (i.val + 1) (by omega) hi
    have hfloor : (n : ℝ) - 1 ≤
        ((i.val : ℝ) + 1) * ((n : ℝ) - ((i.val : ℝ) + 1)) := by
      have hcast : ((n - 1 : ℕ) : ℝ) ≤
          (((i.val + 1) * (n - (i.val + 1)) : ℕ) : ℝ) := by
        exact_mod_cast hfloorN
      simpa only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one,
        Nat.cast_mul, Nat.cast_sub hi.le, Nat.cast_add] using hcast
    have hcancel :
        (1 / (n : ℝ)) * ((n : ℝ) * ((n : ℝ) - 1)) = (n : ℝ) - 1 := by
      field_simp [hnRpos.ne']
    unfold thresholdRate
    rw [lt_div_iff₀ hden, hcancel]
    nlinarith

private theorem thresholdRate_converges {n : ℕ} (hn : 2 ≤ n)
    (i : Fin (n - 1)) :
    (1 - thresholdRate n i) * Real.exp (1 / (n : ℝ)) < 1 :=
  shifted_geometric_mgf_converges_of_nonneg_lt
    (thresholdRate_bounds hn i).1 (by positivity)
    (thresholdRate_bounds hn i).2.2

private noncomputable def thresholdMilestones {L K : ℕ}
    (n : ℕ) (hn : 2 ≤ n) (q : ℕ) (hq : 1 ≤ q) :
    MilestonePhaseOn (NonuniformMajority L K) where
  k := n - 1
  milestone i c := i.val + 2 ≤ geCount q c
  p := thresholdRate n
  hp_pos i := (thresholdRate_bounds hn i).1
  hp_le_one i := (thresholdRate_bounds hn i).2.1
  milestone_monotone i c d h hsupp :=
    geCount_ge_monotone q (i.val + 2) c d h hsupp
  Inv c := c.card = n ∧ 1 ≤ geCount q c
  inv_closed := by
    intro c hInv
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {d | ¬ (d.card = n ∧ 1 ≤ geCount q d)} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
    intro d hsupp hbad
    apply hbad
    exact ⟨(Protocol.stepDistOrSelf_support_card_eq
      (NonuniformMajority L K) c d hsupp).trans hInv.1,
      geCount_ge_monotone q 1 c d hInv.2 hsupp⟩
  progress_on := by
    intro i c hInv hprev hcur
    have hcount : geCount q c = i.val + 1 := by
      have hlt : geCount q c < i.val + 2 := Nat.lt_of_not_ge hcur
      have hle : i.val + 1 ≤ geCount q c := by
        by_cases hi : i.val = 0
        · have := hInv.2
          omega
        · have hh := hprev ⟨i.val - 1, by omega⟩ (by
            exact Fin.mk_lt_mk.mpr (by omega))
          dsimp at hh
          omega
      omega
    have hbound := threshold_advance_probability hn q hq c hInv.1
    have hi : i.val + 1 ≤ n := by have := i.isLt; omega
    have heq :
        (((2 * geCount q c * (n - geCount q c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) = thresholdRate n i := by
      rw [hcount]
      simp only [thresholdRate, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    rw [heq] at hbound
    refine hbound.trans (measure_mono ?_)
    intro d hd
    simp only [Set.mem_setOf_eq] at hd ⊢
    omega

/-- A selected persistent pair propagates every phase threshold carried by
either endpoint. -/
theorem selected_labels_threshold_infection {L K : ℕ}
    (init : TimeTheorem.Cfg L K) (ω : TimeTheorem.Ω L K)
    (t q : ℕ) (i j : Fin init.card)
    (hsel : PairLog.drawLabels init ω (t + 1) = some (i, j))
    (hseed : q ≤ (PairLog.labelsAt init ω t i).phase.val ∨
      q ≤ (PairLog.labelsAt init ω t j).phase.val) :
    q ≤ (PairLog.labelsAt init ω (t + 1) i).phase.val ∧
      q ≤ (PairLog.labelsAt init ω (t + 1) j).phase.val := by
  obtain ⟨_, hi, hj, _⟩ := PairLog.labelsAt_selected_transition init ω t i j hsel
  have hmax : q ≤ max (PairLog.labelsAt init ω t i).phase.val
      (PairLog.labelsAt init ω t j).phase.val := by
    rcases hseed with h | h
    · exact h.trans (le_max_left _ _)
    · exact h.trans (le_max_right _ _)
  rw [hi, hj]
  change q ≤ (Transition L K (PairLog.labelsAt init ω t i)
      (PairLog.labelsAt init ω t j)).1.phase.val ∧
    q ≤ (Transition L K (PairLog.labelsAt init ω t i)
      (PairLog.labelsAt init ω t j)).2.phase.val
  exact ⟨hmax.trans (Transition_left_phase_ge_pair_max _ _),
    hmax.trans (Transition_right_phase_ge_pair_max _ _)⟩

/-- The two-orientation SI advancement rate on the actual labeled next-draw
kernel. This applies to the persistent labeling at every recorded past. -/
theorem labeled_threshold_advance_probability {L K n : ℕ}
    (hn : 2 ≤ n) (q : ℕ) (hq : 1 ≤ q)
    (f : Fin n → AgentState L K) :
    ENNReal.ofReal
        (((2 * geCount q (PairLog.labelCfg f) *
          (n - geCount q (PairLog.labelCfg f)) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      (TimeTheorem.drawLaw (PairLog.labelCfg f)).toMeasure
        {d | geCount q (PairLog.labelCfg f) + 1 ≤
          geCount q (PairLog.labelCfg (PairLog.stepLabels f d))} := by
  have h := threshold_advance_probability hn q hq
    (PairLog.labelCfg f) (PairLog.labelCfg_card f)
  rw [← TimeTheorem.drawLaw_projects (PairLog.labelCfg f),
    PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete
      (DiscreteMeasurableSpace.forall_measurableSet _)] at h
  simpa only [Set.preimage_setOf_eq, PairLog.stepLabels_config] using h

private theorem pairLog_condExp_indicator_of_nextMass
    {L K : ℕ} (init : Cfg L K) (t : ℕ)
    (A : ((i : Finset.Iic t) → Draw L K) → Draw L K → Prop)
    (q : ((i : Finset.Iic t) → Draw L K) → ℝ≥0∞)
    (hmass : ∀ p,
      (drawLaw (prefixCfg init t p)).toMeasure {d | A p d} = q p) :
    (law init)[fun ω =>
      if A (frestrictLe t ω) (ω (t + 1)) then (1 : ℝ) else 0
      | pairLogFiltration L K t] =ᵐ[law init]
      (fun ω => (q (frestrictLe t ω)).toReal) := by
  classical
  let κ := fun s => pairKernel init s
  let f : Ω L K → ℝ := fun ω =>
    if A (frestrictLe t ω) (ω (t + 1)) then 1 else 0
  have hA :
      MeasurableSet {z : ((i : Finset.Iic t) → Draw L K) × Draw L K |
        A z.1 z.2} :=
    (Set.to_countable _).measurableSet
  have hpair :
      Measurable (fun ω : Ω L K =>
        (frestrictLe (π := fun _ : ℕ => Draw L K) t ω, ω (t + 1))) :=
    (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) t).prodMk
      (measurable_pi_apply (t + 1))
  have hEvent :
      MeasurableSet {ω : Ω L K | A (frestrictLe t ω) (ω (t + 1))} :=
    hA.preimage hpair
  have hfm : Measurable f :=
    Measurable.ite hEvent measurable_const measurable_const
  have hfi : Integrable f (law init) :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        dsimp [f]
        split_ifs <;> norm_num)
  have hlaw : law init =
      Kernel.traj (X := fun _ => Draw L K) (fun s => pairKernel init s) 0 (fun _ => none) :=
    (Kernel.traj_apply _ _).symm
  have hce :
      (law init)[f | pairLogFiltration L K t] =ᵐ[law init]
        (fun ω => ∫ y, f y ∂Kernel.traj κ t (frestrictLe t ω)) := by
    rw [hlaw] at hfi ⊢
    rw [show (pairLogFiltration L K t : MeasurableSpace (Ω L K)) =
      Filtration.piLE (X := fun _ : ℕ => Draw L K) t from rfl]
    exact Kernel.condExp_traj (X := fun _ => Draw L K)
      (κ := fun s => pairKernel init s) (a := 0) (b := t)
      (x₀ := fun _ => none) (Nat.zero_le t) hfi
  have hlocal (p : (i : Finset.Iic t) → Draw L K) :
      (∫ d, (if A p d then (1 : ℝ) else 0) ∂pairKernel init t p) =
        (q p).toReal := by
    have hp : MeasurableSet {d : Draw L K | A p d} :=
      (Set.to_countable _).measurableSet
    calc
      (∫ d, (if A p d then (1 : ℝ) else 0) ∂pairKernel init t p) =
          (pairKernel init t p).real {d | A p d} := by
        simpa only [Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using
          (integral_indicator_one (μ := pairKernel init t p) hp)
      _ = (q p).toReal := by
        change ((drawLaw (prefixCfg init t p)).toMeasure {d | A p d}).toReal = _
        rw [hmass p]
  have htraj (p : (i : Finset.Iic t) → Draw L K) :
      (∫ y, f y ∂Kernel.traj κ t p) = (q p).toReal := by
    have hfreeze :
        (fun y : Ω L K =>
          f (Function.updateFinset y (Finset.Iic t) p)) =
        (fun y => if A p (y (t + 1)) then (1 : ℝ) else 0) := by
      funext y
      dsimp [f]
      rw [frestrictLe_updateFinset]
      simp [Function.updateFinset, Finset.mem_Iic, Nat.not_succ_le_self]
    have hmap :
        Measure.map (fun y : Ω L K => y (t + 1)) (Kernel.traj κ t p) =
          pairKernel init t p := by
      change (Kernel.traj (X := fun _ => Draw L K) κ t p).map
        (fun y : Ω L K => y (t + 1)) = κ t p
      rw [← Kernel.map_apply _ (measurable_pi_apply (t + 1)),
        Kernel.map_traj_succ_self]
    have hnext :
        Measurable (fun d : Draw L K =>
          if A p d then (1 : ℝ) else 0) :=
      Measurable.ite (Set.to_countable _).measurableSet
        measurable_const measurable_const
    calc
      (∫ y, f y ∂Kernel.traj κ t p) =
          ∫ y, f (Function.updateFinset y (Finset.Iic t) p)
            ∂Kernel.traj κ t p :=
        Kernel.integral_traj (X := fun _ => Draw L K) (κ := κ) p hfm.aestronglyMeasurable
      _ = ∫ y : Ω L K, (if A p (y (t + 1)) then (1 : ℝ) else 0)
          ∂Kernel.traj (X := fun _ => Draw L K) κ t p := by rw [hfreeze]
      _ = ∫ d, (if A p d then (1 : ℝ) else 0)
          ∂pairKernel init t p := by
        rw [← hmap]
        exact (integral_map (μ := Kernel.traj (X := fun _ => Draw L K) κ t p)
          (f := fun d : Draw L K => if A p d then (1 : ℝ) else 0)
          (measurable_pi_apply (t + 1)).aemeasurable
          hnext.aestronglyMeasurable).symm
      _ = (q p).toReal := hlocal p
  filter_upwards [hce] with ω hω
  exact hω.trans (htraj (frestrictLe t ω))

/-- Given the entire recorded past, the actual threshold count advances with
at least the two-orientation SI probability. -/
theorem threshold_conditional_advance_probability {L K : ℕ}
    (init : Cfg L K) (hc : 2 ≤ init.card) (q : ℕ) (hq : 1 ≤ q) (t : ℕ) :
    (fun ω =>
      (((2 * geCount q (trace init ω t) *
          (init.card - geCount q (trace init ω t)) : ℕ) : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)))) ≤ᵐ[law init]
      (law init)[fun ω =>
        if geCount q (trace init ω t) + 1 ≤
          geCount q (trace init ω (t + 1)) then (1 : ℝ) else 0
        | pairLogFiltration L K t] := by
  let A : ((i : Finset.Iic t) → Draw L K) → Draw L K → Prop :=
    fun p d => geCount q (prefixCfg init t p) + 1 ≤
      geCount q (applyDraw (prefixCfg init t p) d)
  let mass : ((i : Finset.Iic t) → Draw L K) → ℝ≥0∞ :=
    fun p => (drawLaw (prefixCfg init t p)).toMeasure {d | A p d}
  let rate : ((i : Finset.Iic t) → Draw L K) → ℝ := fun p =>
    (((2 * geCount q (prefixCfg init t p) *
        (init.card - geCount q (prefixCfg init t p)) : ℕ) : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1)))
  have hden : (0 : ℝ) < (init.card : ℝ) * ((init.card : ℝ) - 1) := by
    have hcR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
    nlinarith
  have hnonneg : ∀ p, 0 ≤ rate p := fun p =>
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hbound : ∀ p, ENNReal.ofReal (rate p) ≤ mass p := by
    intro p
    simpa only [rate, mass, A, PairLog.stepLabels_config,
      PairLog.prefixLabels_config] using
      labeled_threshold_advance_probability hc q hq (PairLog.prefixLabels init t p)
  have hce := pairLog_condExp_indicator_of_nextMass init t A mass (fun _ => rfl)
  have hfun : (fun ω : Ω L K => @ite ℝ (A (frestrictLe t ω) (ω (t + 1)))
      (Classical.propDecidable _) 1 0) =
      (fun ω : Ω L K => if geCount q (trace init ω t) + 1 ≤
        geCount q (trace init ω (t + 1)) then (1 : ℝ) else 0) :=
    funext fun ω => by
      split_ifs with h1 h2 h2 <;>
        first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  have hce' : (law init)[fun ω =>
      if geCount q (trace init ω t) + 1 ≤ geCount q (trace init ω (t + 1))
        then (1 : ℝ) else 0 | pairLogFiltration L K t] =ᵐ[law init]
      (fun ω => (mass (frestrictLe t ω)).toReal) := by
    rw [← hfun]
    exact hce
  filter_upwards [hce'] with ω hω
  rw [hω]
  have h := ENNReal.toReal_mono
    (show mass (frestrictLe t ω) ≠ ⊤ from measure_ne_top _ _)
    (hbound (frestrictLe t ω))
  simpa only [ENNReal.toReal_ofReal (hnonneg (frestrictLe t ω))] using h

/-- The milestone factors are precisely the moments of independent SI phases.
This auxiliary product space is a comparison law, not the law of actual
protocol holding times. -/
private theorem threshold_mgf_product_le {n : ℕ} (hn : 2 ≤ n) :
    (∏ i : Fin (n - 1),
      thresholdRate n i * Real.exp (1 / (n : ℝ)) /
        (1 - (1 - thresholdRate n i) * Real.exp (1 / (n : ℝ)))) ≤
      Real.exp 3 * (n : ℝ) := by
  let p : Fin (n - 1) → unitInterval := fun i =>
    ⟨thresholdRate n i,
      (thresholdRate_bounds hn i).1.le, (thresholdRate_bounds hn i).2.1⟩
  let μ : Measure (Fin (n - 1) → ℕ) :=
    Measure.pi (fun i => ProbabilityTheory.geometricMeasure (p i))
  let G : Fin (n - 1) → (Fin (n - 1) → ℕ) → ℕ :=
    fun i ω => ω i
  have hG : ∀ i, Measurable (G i) := fun i => measurable_pi_apply i
  have hIndep : iIndepFun G μ := by
    exact iIndepFun_pi
      (μ := fun i => ProbabilityTheory.geometricMeasure (p i))
      (X := fun (_ : Fin (n - 1)) (k : ℕ) => k)
      (fun _ => measurable_id.aemeasurable)
  have hLaw : ∀ i, Measure.map (G i) μ =
      ProbabilityTheory.geometricMeasure (p i) :=
    fun i => (measurePreserving_eval
      (fun i => ProbabilityTheory.geometricMeasure (p i)) i).map_eq
  have hScalar := ScalarTails.epidemic_geometric_exp_moment
    (μ := μ) hn G p hG hIndep hLaw (fun _ => rfl)
  have hmoment :
      (∫ ω : Fin (n - 1) → ℕ,
        Real.exp ((∑ i : Fin (n - 1), ((ω i : ℝ) + 1)) / (n : ℝ)) ∂μ) =
        ∏ i : Fin (n - 1),
          thresholdRate n i * Real.exp (1 / (n : ℝ)) /
            (1 - (1 - thresholdRate n i) * Real.exp (1 / (n : ℝ))) := by
    calc
      _ = ∫ ω : Fin (n - 1) → ℕ,
          ∏ i : Fin (n - 1), Real.exp ((1 / (n : ℝ)) * ((ω i : ℝ) + 1)) ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        dsimp only
        rw [← Real.exp_sum, ← Finset.mul_sum]
        congr 1
        ring
      _ = ∏ i : Fin (n - 1),
          ∫ k : ℕ, Real.exp ((1 / (n : ℝ)) * ((k : ℝ) + 1))
            ∂ProbabilityTheory.geometricMeasure (p i) :=
        integral_fintype_prod_eq_prod
          (fun (_ : Fin (n - 1)) (k : ℕ) =>
            Real.exp ((1 / (n : ℝ)) * ((k : ℝ) + 1)))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        simpa only [p, geometricMeasure', div_eq_mul_inv,
          mul_comm, mul_left_comm, mul_assoc] using
          shifted_geometric_exp_integral_geometricMeasure
            (thresholdRate_bounds hn i).1
            (thresholdRate_bounds hn i).2.1
            (thresholdRate_converges hn i)
  rw [← hmoment]
  exact hScalar.2

/-- Sharp epidemic comparison from any seeded size-n configuration.
Additional threshold seeds and skipped milestones can only improve the bound. -/
theorem threshold_kernel_sharp_tail {L K n : ℕ}
    (hn : 2 ≤ n) (q : ℕ) (hq : 1 ≤ q)
    (c : Config (AgentState L K)) (hcard : c.card = n)
    (hseed : ∃ a ∈ c, q ≤ a.phase.val) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {d | ¬ ∀ a ∈ d, q ≤ a.phase.val} ≤
      ENNReal.ofReal
        (Real.exp (-(t : ℝ) / (n : ℝ)) * (Real.exp 3 * (n : ℝ))) := by
  let mp := thresholdMilestones (L := L) (K := K) n hn q hq
  have hInv : mp.Inv c := by
    refine ⟨hcard, ?_⟩
    exact (Multiset.countP_pos.mpr hseed)
  have hpos : (0 : ℝ) < 1 / (n : ℝ) :=
    one_div_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hvalid : ∀ i, (1 - mp.p i) * Real.exp (1 / (n : ℝ)) < 1 :=
    fun i => thresholdRate_converges hn i
  have htail := mp.milestone_tail_bound_via_mgf_on_partial c hInv hpos hvalid t
  have hprod : (∏ i : Fin mp.k, mp.mgfFactor (1 / (n : ℝ)) i) ≤
      Real.exp 3 * (n : ℝ) :=
    threshold_mgf_product_le hn
  have htail' :
      ((NonuniformMajority L K).transitionKernel ^ t) c {d | ¬ mp.Post d} ≤
        ENNReal.ofReal
          (Real.exp (-(t : ℝ) / (n : ℝ)) * (Real.exp 3 * (n : ℝ))) := by
    refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : -(1 / (n : ℝ)) * (t : ℝ) = -(t : ℝ) / (n : ℝ) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
  have hcard_zero :
      ((NonuniformMajority L K).transitionKernel ^ t) c
        {d : Config (AgentState L K) | d.card ≠ n} = 0 :=
    Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
      (NonuniformMajority L K) (fun d : Config (AgentState L K) => d.card = n)
      (fun a b ha hsupp =>
        (Protocol.stepDistOrSelf_support_card_eq
          (NonuniformMajority L K) a b hsupp).trans ha)
      c hcard t
  have hsub : {d : Config (AgentState L K) | ¬ ∀ a ∈ d, q ≤ a.phase.val} ⊆
      {d | ¬ mp.Post d} ∪ {d | d.card ≠ n} := by
    intro d hbad
    by_cases hPost : mp.Post d
    · right
      intro hdcard
      apply hbad
      have hncount : n ≤ geCount q d := by
        have hi := hPost ⟨n - 2, by change n - 2 < n - 1; omega⟩
        change n - 2 + 2 ≤ geCount q d at hi
        omega
      have heq : Multiset.countP (geP q) d = d.card :=
        le_antisymm (Multiset.countP_le_card _ _)
          (by change d.card ≤ geCount q d; rw [hdcard]; exact hncount)
      exact Multiset.countP_eq_card.mp heq
    · exact Or.inl hPost
  calc
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {d | ¬ ∀ a ∈ d, q ≤ a.phase.val}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          ({d | ¬ mp.Post d} ∪ {d | d.card ≠ n}) := measure_mono hsub
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c {d | ¬ mp.Post d} +
          ((NonuniformMajority L K).transitionKernel ^ t) c {d | d.card ≠ n} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal
        (Real.exp (-(t : ℝ) / (n : ℝ)) * (Real.exp 3 * (n : ℝ))) := by
      rw [hcard_zero, add_zero]
      exact htail'

private theorem seeded_partial_endpoint_kernel {L K : ℕ} (s t : ℕ) :
    (Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s (s + t)).map
        (fun x : Finset.Iic (s + t) → Cfg L K =>
          x ⟨s + t, Finset.mem_Iic.mpr le_rfl⟩) =
      (((NonuniformMajority L K).transitionKernel ^ t).comap
        (fun x : Finset.Iic s → Cfg L K =>
          x ⟨s, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _)) := by
  induction t with
  | zero =>
      simp only [Nat.add_zero]
      ext x A hA
      rw [Kernel.map_apply _ (measurable_pi_apply _) x,
        Kernel.partialTraj_self, Kernel.id_apply,
        Measure.map_dirac' (measurable_pi_apply _) x,
        Kernel.comap_apply, pow_zero]
      change (Measure.dirac (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩)) A =
        (Kernel.id (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩)) A
      rw [Kernel.id_apply]
  | succ t ih =>
      let P : Kernel (Cfg L K) (Cfg L K) :=
        (NonuniformMajority L K).transitionKernel
      let coordStart : (Finset.Iic s → Cfg L K) → Cfg L K :=
        fun x => x ⟨s, Finset.mem_Iic.mpr le_rfl⟩
      let coordNow : (Finset.Iic (s + t) → Cfg L K) → Cfg L K :=
        fun x => x ⟨s + t, Finset.mem_Iic.mpr le_rfl⟩
      let coordNext : (Finset.Iic (s + t + 1) → Cfg L K) → Cfg L K :=
        fun x => x ⟨s + t + 1, Finset.mem_Iic.mpr le_rfl⟩
      change (Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
          s (s + t + 1)).map coordNext =
        ((P ^ (t + 1)).comap coordStart (measurable_pi_apply _))
      calc
        (Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
            s (s + t + 1)).map coordNext =
            ((Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                (s + t) (s + t + 1) ∘ₖ
              Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                s (s + t))).map coordNext := by
          rw [Kernel.partialTraj_succ_eq_comp (Nat.le_add_right s t)]
        _ = ((Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                (s + t) (s + t + 1)).map coordNext) ∘ₖ
              Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                s (s + t) := by rw [Kernel.map_comp]
        _ = ProtocolTraceLaw.kfamily (L := L) (K := K) (s + t) ∘ₖ
              Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                s (s + t) := by rw [Kernel.map_partialTraj_succ_self]
        _ = (P.comap coordNow (measurable_pi_apply _)) ∘ₖ
              Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                s (s + t) := rfl
        _ = P ∘ₖ ((Kernel.partialTraj
              (ProtocolTraceLaw.kfamily (L := L) (K := K)) s (s + t)).map
                coordNow) := by
          rw [← Kernel.comp_map (Kernel.partialTraj
            (ProtocolTraceLaw.kfamily (L := L) (K := K)) s (s + t)) P
            (measurable_pi_apply _)]
        _ = P ∘ₖ ((P ^ t).comap coordStart (measurable_pi_apply _)) := by
          simpa only [P, coordStart, coordNow] using
            congrArg (fun η => P ∘ₖ η) ih
        _ = (P ^ (t + 1)).comap coordStart (measurable_pi_apply _) := by
          ext x A hA
          rw [Kernel.comap_apply,
            Kernel.pow_succ_apply_eq_lintegral P t (coordStart x) hA,
            Kernel.comp_apply' _ _ _ hA, Kernel.comap_apply]

private theorem seeded_endpoint_law {L K : ℕ} (s t : ℕ)
    (x : Finset.Iic s → Cfg L K) :
    Measure.map (fun tr : ℕ → Cfg L K => tr (s + t))
        (Kernel.traj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s x) =
      ((NonuniformMajority L K).transitionKernel ^ t)
        (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) := by
  let coord : (Finset.Iic (s + t) → Cfg L K) → Cfg L K :=
    fun y => y ⟨s + t, Finset.mem_Iic.mpr le_rfl⟩
  calc
    Measure.map (fun tr : ℕ → Cfg L K => tr (s + t))
        (Kernel.traj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s x) =
      Measure.map (coord ∘ frestrictLe (π := fun _ : ℕ => Cfg L K) (s + t))
        (Kernel.traj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s x) := rfl
    _ = Measure.map coord (Measure.map (frestrictLe (π := fun _ : ℕ => Cfg L K) (s + t))
        (Kernel.traj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s x)) := by
      rw [← Measure.map_map (measurable_pi_apply _)
        (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) (s + t))]
    _ = Measure.map coord
        (Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
          s (s + t) x) := by rw [Kernel.traj_map_frestrictLe_apply]
    _ = ((NonuniformMajority L K).transitionKernel ^ t)
        (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) := by
      rw [← Kernel.map_apply _ (measurable_pi_apply _) x,
        seeded_partial_endpoint_kernel, Kernel.comap_apply]

private theorem prefix_event_future_bound {L K : ℕ}
    (init : Cfg L K) (s t : ℕ)
    (A : Set (Finset.Iic s → Cfg L K)) (hA : MeasurableSet A)
    (B : Set (Cfg L K)) (hB : MeasurableSet B) (ε : ℝ≥0∞)
    (hbound : ∀ x ∈ A,
      ((NonuniformMajority L K).transitionKernel ^ t)
        (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) B ≤ ε) :
    ProtocolTraceLaw.μ init
      ((frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' A ∩
        (fun tr => tr (s + t)) ⁻¹' B) ≤
      ε * ProtocolTraceLaw.μ init
        ((frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' A) := by
  classical
  let κ := ProtocolTraceLaw.kfamily (L := L) (K := K)
  let Γ := Kernel.traj κ s
  let ν : Measure (Finset.Iic s → Cfg L K) :=
    Kernel.partialTraj κ 0 s (fun _ => init)
  let E : Set (ℕ → Cfg L K) :=
    (frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' A
  let F : Set (ℕ → Cfg L K) := (fun tr => tr (s + t)) ⁻¹' B
  have hE : MeasurableSet E := hA.preimage
    (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) s)
  have hF : MeasurableSet F := hB.preimage (measurable_pi_apply _)
  have hsplit (D : Set (ℕ → Cfg L K)) (hD : MeasurableSet D) :
      ProtocolTraceLaw.μ init D = ∫⁻ x, Γ x D ∂ν := by
    change Kernel.traj κ 0 (fun _ => init) D =
      ∫⁻ x, Kernel.traj κ s x D ∂(Kernel.partialTraj κ 0 s (fun _ => init))
    rw [← Kernel.traj_comp_partialTraj (Nat.zero_le s),
      Kernel.comp_apply' _ _ _ hD]
  have hlocal (x : Finset.Iic s → Cfg L K) :
      Γ x (E ∩ F) ≤ ε * Γ x E := by
    have hfreeze : ∀ᵐ tr ∂Γ x,
        frestrictLe (π := fun _ : ℕ => Cfg L K) s tr = x := by
      rw [ae_iff]
      change (Kernel.traj κ s x)
        ((frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' ({x}ᶜ)) = 0
      rw [← Measure.map_apply
        (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) s)
        (measurableSet_singleton x).compl,
        Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
      simp
    by_cases hx : x ∈ A
    · have hwhole : Γ x E = 1 := by
        calc
          Γ x E = Γ x Set.univ := by
            apply measure_congr
            filter_upwards [hfreeze] with tr htr
            show (tr ∈ E) = (tr ∈ Set.univ)
            simp only [E, Set.mem_preimage, htr, hx, Set.mem_univ]
          _ = 1 := measure_univ
      have hinter : Γ x (E ∩ F) = Γ x F := by
        apply measure_congr
        filter_upwards [hfreeze] with tr htr
        show (tr ∈ E ∩ F) = (tr ∈ F)
        simp only [Set.mem_inter_iff, E, Set.mem_preimage, htr, hx, true_and]
      have hfuture : Γ x F =
          ((NonuniformMajority L K).transitionKernel ^ t)
            (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) B := by
        calc
          Γ x F =
              Measure.map (fun tr : ℕ → Cfg L K => tr (s + t))
                (Kernel.traj κ s x) B := by
            rw [Measure.map_apply
              (measurable_pi_apply (s + t) : Measurable fun tr : ℕ → Cfg L K => tr (s + t)) hB]
          _ = ((NonuniformMajority L K).transitionKernel ^ t)
                (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) B := by
            rw [seeded_endpoint_law]
      rw [hwhole, mul_one, hinter, hfuture]
      exact hbound x hx
    · have hzero : Γ x E = 0 := by
        calc
          Γ x E = Γ x ∅ := by
            apply measure_congr
            filter_upwards [hfreeze] with tr htr
            show (tr ∈ E) = (tr ∈ (∅ : Set _))
            simp only [E, Set.mem_preimage, htr, hx, Set.mem_empty_iff_false]
          _ = 0 := measure_empty
      rw [hzero, mul_zero]
      exact (measure_mono Set.inter_subset_left).trans_eq hzero
  change ProtocolTraceLaw.μ init (E ∩ F) ≤ ε * ProtocolTraceLaw.μ init E
  calc
    ProtocolTraceLaw.μ init (E ∩ F) = ∫⁻ x, Γ x (E ∩ F) ∂ν :=
      hsplit (E ∩ F) (hE.inter hF)
    _ ≤ ∫⁻ x, ε * Γ x E ∂ν := lintegral_mono hlocal
    _ = ε * ∫⁻ x, Γ x E ∂ν :=
      lintegral_const_mul ε (Kernel.measurable_coe Γ hE)
    _ = ε * ProtocolTraceLaw.μ init E := by rw [← hsplit E hE]

private theorem seed_time_unique {L K : ℕ} (init : Cfg L K) (q : ℕ)
    (ω : Ω L K) {s r : ℕ}
    (hs : firstPhaseSeed init q s ω) (hr : firstPhaseSeed init q r ω) :
    s = r := by
  rcases lt_trichotomy s r with hlt | heq | hgt
  · obtain ⟨a, ha, hphase⟩ := hs.1
    have hltphase := hr.2 s hlt a ha
    omega
  · exact heq
  · obtain ⟨a, ha, hphase⟩ := hr.1
    have hltphase := hs.2 r hgt a ha
    omega

/-- A uniform seeded-state tail remains valid after the genuine first seed. -/
theorem threshold_tail_after_first_seed {L K n : ℕ}
    (init : Cfg L K) (hcard : init.card = n) (q t : ℕ) (ε : ℝ≥0∞)
    (hbound : ∀ c : Cfg L K, c.card = n →
      (∃ a ∈ c, q ≤ a.phase.val) →
      ((NonuniformMajority L K).transitionKernel ^ t) c
        {d | ¬ ∀ a ∈ d, q ≤ a.phase.val} ≤ ε) :
    law init
      {ω | ∃ s : ℕ, firstPhaseSeed init q s ω ∧
        ¬ ∀ a ∈ trace init ω (s + t), q ≤ a.phase.val} ≤ ε := by
  classical
  let A (s : ℕ) : Set (Finset.Iic s → Cfg L K) :=
    {x | (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩).card = n ∧
      (∃ a ∈ x ⟨s, Finset.mem_Iic.mpr le_rfl⟩, a.phase.val = q) ∧
      ∀ u : Finset.Iic s, u.val < s → ∀ a ∈ x u, a.phase.val < q}
  let B : Set (Cfg L K) := {d | ¬ ∀ a ∈ d, q ≤ a.phase.val}
  have hA (s : ℕ) : MeasurableSet (A s) :=
    (Set.to_countable _).measurableSet
  have hB : MeasurableSet B := (Set.to_countable _).measurableSet
  have hpull (s : ℕ) :
      (trace init) ⁻¹'
        ((frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' A s) =
        {ω | firstPhaseSeed init q s ω} := by
    ext ω
    constructor
    · rintro ⟨_, hseed, hpast⟩
      refine ⟨hseed, ?_⟩
      intro u hu a ha
      exact hpast ⟨u, Finset.mem_Iic.mpr hu.le⟩ hu a ha
    · intro hseed
      refine ⟨?_, hseed.1, ?_⟩
      · have hc : (trace init ω s).card = init.card := by
          simpa only [trace_zero] using
            Protocol.reachable_card_eq
              (trace_reachable init ω (s := 0) (t := s) (Nat.zero_le s))
        exact hc.trans hcard
      · intro u hu a ha
        exact hseed.2 u.val hu a ha
  have hseedMeas (s : ℕ) :
      MeasurableSet {ω | firstPhaseSeed init q s ω} := by
    rw [← hpull s]
    exact ((hA s).preimage
      (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) s)).preimage
        (measurable_trace init)
  have hbadMeas (s : ℕ) :
      MeasurableSet {ω | ¬ ∀ a ∈ trace init ω (s + t), q ≤ a.phase.val} :=
    hB.preimage ((measurable_pi_apply _).comp (measurable_trace init))
  have hlocal (s : ℕ) :
      law init
        ({ω | firstPhaseSeed init q s ω} ∩
          {ω | ¬ ∀ a ∈ trace init ω (s + t), q ≤ a.phase.val}) ≤
        ε * law init {ω | firstPhaseSeed init q s ω} := by
    have hE : MeasurableSet
        ((frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' A s) :=
      (hA s).preimage (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) s)
    have hF : MeasurableSet
        ((fun tr : ℕ → Cfg L K => tr (s + t)) ⁻¹' B) :=
      hB.preimage (measurable_pi_apply _)
    have h := prefix_event_future_bound init s t (A s) (hA s) B hB ε
      (fun x hx => by
        apply hbound _ hx.1
        obtain ⟨a, ha, heq⟩ := hx.2.1
        exact ⟨a, ha, heq.ge⟩)
    rw [← PairLog.pair_log_projects init,
      Measure.map_apply (measurable_trace init) (hE.inter hF),
      Measure.map_apply (measurable_trace init) hE,
      Set.preimage_inter] at h
    simp only [hpull s] at h
    exact h
  let S (ω : Ω L K) : WithTop ℕ :=
    if h : ∃ s, firstPhaseSeed init q s ω then (Nat.find h : WithTop ℕ) else ⊤
  have hSiff (ω : Ω L K) (s : ℕ) :
      S ω = (s : WithTop ℕ) ↔ firstPhaseSeed init q s ω := by
    dsimp only [S]
    split_ifs with hex
    · constructor
      · intro h
        have hfind : Nat.find hex = s := WithTop.coe_injective h
        simpa only [hfind] using Nat.find_spec hex
      · intro hs
        exact congrArg (fun r : ℕ => (r : WithTop ℕ))
          (seed_time_unique init q ω (Nat.find_spec hex) hs)
    · constructor
      · intro h
        exact absurd h (by simp)
      · intro hs
        exact absurd ⟨s, hs⟩ hex
  let D : Set (Ω L K) :=
    {ω | ∃ s : ℕ, firstPhaseSeed init q s ω ∧
      ¬ ∀ a ∈ trace init ω (s + t), q ≤ a.phase.val}
  have hD : MeasurableSet D := by
    have heq : D = ⋃ s : ℕ,
        {ω | firstPhaseSeed init q s ω} ∩
          {ω | ¬ ∀ a ∈ trace init ω (s + t), q ≤ a.phase.val} := by
      ext ω
      simp only [D, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [heq]
    exact MeasurableSet.iUnion (fun s => (hseedMeas s).inter (hbadMeas s))
  have hSeq (s : ℕ) :
      {ω | S ω = (s : WithTop ℕ)} = {ω | firstPhaseSeed init q s ω} :=
    Set.ext fun ω => hSiff ω s
  apply PairLog.genuine_seed_splice (law init) S D ε hD
  · intro s
    rw [hSeq s]
    exact hseedMeas s
  · intro ω hω
    obtain ⟨s, hs, _⟩ := hω
    rw [(hSiff ω s).mpr hs]
    exact WithTop.coe_ne_top
  · intro s
    have heq :
        D ∩ {ω | S ω = (s : WithTop ℕ)} =
          {ω | firstPhaseSeed init q s ω} ∩
            {ω | ¬ ∀ a ∈ trace init ω (s + t), q ≤ a.phase.val} := by
      ext ω
      rw [hSeq s]
      constructor
      · rintro ⟨⟨r, hr, hbad⟩, hs⟩
        have hrs := seed_time_unique init q ω hr hs
        subst r
        exact ⟨hs, hbad⟩
      · rintro ⟨hs, hbad⟩
        exact ⟨⟨s, hs, hbad⟩, hs⟩
    rw [heq, hSeq s]
    exact hlocal s

/-- The common original-input contract from the plan. -/
def GoodInput (n : ℕ) (init : InputCfg n) : Prop :=
  timePopulationThreshold ≤ n ∧ validInitial init ∧ init.card = n

/-- The rounded raw-time window gives the requested power of the population. -/
theorem epidemic_logWindow_bound {n : ℕ} (hn : 0 < n) (u : ℕ) :
    Real.exp (-(logWindow n u : ℝ) / (n : ℝ)) *
        (Real.exp 3 * (n : ℝ)) ≤
      Real.exp 3 * Real.rpow (n : ℝ) (1 - (u : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hceil :
      (u : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
        (logWindow n u : ℝ) := by
    unfold logWindow
    exact Nat.le_ceil _
  have hquot :
      (u : ℝ) * Real.log (n : ℝ) ≤
        (logWindow n u : ℝ) / (n : ℝ) := by
    apply (le_div_iff₀ hnpos).2
    calc
      ((u : ℝ) * Real.log (n : ℝ)) * (n : ℝ) =
          (u : ℝ) * (n : ℝ) * Real.log (n : ℝ) := by ring
      _ ≤ _ := hceil
  have hneg :
      -(logWindow n u : ℝ) / (n : ℝ) ≤
        -(u : ℝ) * Real.log (n : ℝ) := by
    simpa only [neg_div, neg_mul] using neg_le_neg hquot
  calc
    Real.exp (-(logWindow n u : ℝ) / (n : ℝ)) *
        (Real.exp 3 * (n : ℝ)) ≤
      Real.exp (-(u : ℝ) * Real.log (n : ℝ)) *
        (Real.exp 3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hneg) (by positivity)
    _ = Real.exp 3 *
        (Real.exp (Real.log (n : ℝ)) *
          Real.exp (-(u : ℝ) * Real.log (n : ℝ))) := by
      rw [Real.exp_log hnpos]
      ring
    _ = Real.exp 3 *
        Real.exp (Real.log (n : ℝ) +
          (-(u : ℝ) * Real.log (n : ℝ))) := by
      rw [Real.exp_add]
    _ = Real.exp 3 *
        Real.exp (Real.log (n : ℝ) * (1 - (u : ℝ))) := by
      congr 2
      ring
    _ = Real.exp 3 * Real.rpow (n : ℝ) (1 - (u : ℝ)) := by
      rw [show Real.rpow (n : ℝ) (1 - (u : ℝ)) = (n : ℝ) ^ (1 - (u : ℝ)) from rfl,
        Real.rpow_def_of_pos hnpos]

/-- N08: sharp phase-threshold spread, summed over the genuine first-seed
events under the original pair-log law. -/
theorem threshold_spread_sharp_tail
    {n : ℕ} (init : InputCfg n) (hinput : GoodInput n init)
    (p : Fin 11) (hp : 1 ≤ p.val)
    (u : ℕ) (hu : 1 ≤ u) :
    law init
      {ω | ∃ s : ℕ, firstPhaseSeed init p.val s ω ∧
        ¬ (∀ a ∈ trace init ω (s + logWindow n u),
          p.val ≤ a.phase.val)} ≤
      ENNReal.ofReal
        (Real.exp 3 * Real.rpow (n : ℝ) (1 - (u : ℝ))) := by
  rcases hinput with ⟨hpop, hvalid, hcard⟩
  have hnlarge : 40 ≤ n := (time_population_bounds hpop).2
  clear hpop hvalid
  have hn : 2 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have htail := threshold_tail_after_first_seed init hcard p.val (logWindow n u)
    (ENNReal.ofReal
      (Real.exp (-(logWindow n u : ℝ) / (n : ℝ)) * (Real.exp 3 * (n : ℝ))))
    (fun c hc hs => threshold_kernel_sharp_tail hn p.val hp c hc hs (logWindow n u))
  exact htail.trans (ENNReal.ofReal_le_ofReal (epidemic_logWindow_bound hnpos u))

end Ripple.PopulationProtocol.ExactMajority.ThresholdEpidemic

end
