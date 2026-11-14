import Ripple.PopulationProtocol.ExactMajority.Probability.PairLog

/-!
# Auxiliary processes on the recorded pair log

An auxiliary process runs on the same physical-label scheduler as the protocol
but applies an arbitrary pair rule `F` to the drawn labels. The labels drawn at
step `t + 1` are those of the actual process (`drawLabels`); only the states
they act on differ. This is the object used when some rules of the protocol are
frozen or continued (Doty et al., exact majority, Phase 0--2 entry analysis).

Main results:
* `auxLabels_succ`: the one-step recursion of the auxiliary process.
* `measurable_auxLabels`: the auxiliary state at time `t` is measurable for the
  pair-log filtration at `t`.
* `auxLabels_eq_labelsAt_of_agree`: if `F` agrees with the protocol rule on the
  drawn pairs of every labelling in `G`, and the actual process stays in `G`
  before time `T`, the two processes coincide through time `T`.
* `aux_pair_conditional_probability`: given the pair log through `t`, the
  conditional probability that the next drawn pair satisfies a predicate of the
  current auxiliary state is the fraction of ordered distinct pairs satisfying it.
* `transitionKernel_labelCfg_eq_goodPairs`, `aux_conditional_kernel`: the protocol
  kernel at a labelled configuration is a label-pair count, so configuration kernel
  floors transfer to conditional probabilities of the auxiliary process.
* `trace_conditional_kernel`, `stronglyMeasurable_trace_step_indicator`,
  `trace_step_conditional_floor`: for the actual trace, the conditional law of the
  next configuration given the pair log is the protocol kernel, and a kernel floor
  becomes the adapted conditional floor used by the Bernoulli success tails.
* `aux_drift_expectation_le`, `aux_drift_tail_le`: a multiplicative drift of a
  potential of the auxiliary state gives a geometric expectation and tail bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PairLogAuxiliary

open TimeTheorem PairLog
open PhaseThreeModel.OccurrenceScheduler

attribute [local instance] Classical.propDecidable

variable {L K n : ℕ}

/-- A rule acting on an ordered (initiator, responder) pair of agent states. -/
abbrev PairRule (L K : ℕ) :=
  AgentState L K → AgentState L K → AgentState L K × AgentState L K

/-- Apply a pair rule to labels `i` (initiator) and `j` (responder). -/
def ruleUpdate (F : PairRule L K) (f : Fin n → AgentState L K) (i j : Fin n) :
    Fin n → AgentState L K :=
  Function.update (Function.update f i (F (f i) (f j)).1) j (F (f i) (f j)).2

/-- One auxiliary step driven by an optional drawn label pair. -/
def auxStep (F : PairRule L K) (f : Fin n → AgentState L K) :
    Option (Fin n × Fin n) → Fin n → AgentState L K
  | none => f
  | some (i, j) => ruleUpdate F f i j

/-- The auxiliary labelling as a function of a recorded prefix. -/
noncomputable def auxPrefix (init : Cfg L K) (F : PairRule L K) :
    (t : ℕ) → ((k : Finset.Iic t) → Draw L K) →
      Fin init.card → AgentState L K
  | 0, _ => initialLabels init
  | t + 1, p =>
      auxStep F
        (auxPrefix init F t (fun k =>
          p ⟨k.val, Finset.mem_Iic.mpr
            (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩))
        (selectLabels
          (prefixLabels init t (fun k =>
            p ⟨k.val, Finset.mem_Iic.mpr
              (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩))
          (p ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩))

/-- The auxiliary labelling at time `t` along the path `ω`. -/
noncomputable def auxLabels (init : Cfg L K) (F : PairRule L K)
    (ω : Ω L K) (t : ℕ) : Fin init.card → AgentState L K :=
  auxPrefix init F t (Preorder.frestrictLe t ω)

/-- The auxiliary configuration at time `t`. -/
noncomputable def auxCfg (init : Cfg L K) (F : PairRule L K)
    (ω : Ω L K) (t : ℕ) : Cfg L K :=
  labelCfg (auxLabels init F ω t)

theorem auxLabels_zero (init : Cfg L K) (F : PairRule L K) (ω : Ω L K) :
    auxLabels init F ω 0 = labelsAt init ω 0 := rfl

theorem auxLabels_zero_eq_initialLabels (init : Cfg L K) (F : PairRule L K)
    (ω : Ω L K) :
    auxLabels init F ω 0 = initialLabels init := rfl

theorem auxLabels_succ (init : Cfg L K) (F : PairRule L K) (ω : Ω L K)
    (t : ℕ) :
    auxLabels init F ω (t + 1) =
      auxStep F (auxLabels init F ω t) (drawLabels init ω (t + 1)) := rfl

/-- The actual labelled process is the auxiliary process of the protocol rule. -/
theorem labelsAt_succ_eq_auxStep (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    labelsAt init ω (t + 1) =
      auxStep (NonuniformMajority L K).δ (labelsAt init ω t)
        (drawLabels init ω (t + 1)) := by
  change stepLabels (labelsAt init ω t) (ω (t + 1)) =
    auxStep (NonuniformMajority L K).δ (labelsAt init ω t)
      (selectLabels (labelsAt init ω t) (ω (t + 1)))
  unfold stepLabels
  rcases selectLabels (labelsAt init ω t) (ω (t + 1)) with _ | ⟨i, j⟩ <;> rfl

theorem labelsAt_eq_auxLabels_delta (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    labelsAt init ω t = auxLabels init (NonuniformMajority L K).δ ω t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [labelsAt_succ_eq_auxStep, auxLabels_succ, ih]

/-! Adaptedness. -/

theorem measurable_auxPrefix (init : Cfg L K) (F : PairRule L K) (t : ℕ) :
    Measurable (auxPrefix init F t) := by
  intro A _
  exact (Set.to_countable _).measurableSet

theorem measurable_auxLabels (init : Cfg L K) (F : PairRule L K) (t : ℕ) :
    Measurable[pairLogFiltration L K t] (fun ω => auxLabels init F ω t) :=
  (measurable_auxPrefix init F t).comp (measurable_pairLog_prefix L K t)

theorem auxLabels_eq_of_frestrictLe_eq (init : Cfg L K) (F : PairRule L K)
    {ω ω' : Ω L K} (t : ℕ)
    (h : Preorder.frestrictLe t ω = Preorder.frestrictLe t ω') :
    auxLabels init F ω t = auxLabels init F ω' t := by
  unfold auxLabels
  rw [h]

/-- A real function of the auxiliary state at `t` is `pairLogFiltration t`-measurable. -/
theorem measurable_aux_potential (init : Cfg L K) (F : PairRule L K)
    (φ : (Fin init.card → AgentState L K) → ℝ) (t : ℕ) :
    Measurable[pairLogFiltration L K t] (fun ω => φ (auxLabels init F ω t)) := by
  have hp : Measurable (fun p : (k : Finset.Iic t) → Draw L K =>
      φ (auxPrefix init F t p)) := by
    intro A _
    exact (Set.to_countable _).measurableSet
  exact hp.comp (measurable_pairLog_prefix L K t)

/-! Agreement with the actual process up to the exit time. -/

/-- If `F` agrees with the protocol rule on every drawn (distinct) pair of a
labelling in `G`, and the actual process is in `G` at every time before `T`,
the auxiliary and actual processes coincide at every time through `T`. -/
theorem auxLabels_eq_labelsAt_of_agree (init : Cfg L K) (F : PairRule L K)
    (G : (Fin init.card → AgentState L K) → Prop)
    (hF : ∀ f, G f → ∀ i j : Fin init.card, i ≠ j →
      F (f i) (f j) = (NonuniformMajority L K).δ (f i) (f j))
    (ω : Ω L K) (T : ℕ) (hG : ∀ t < T, G (labelsAt init ω t)) :
    ∀ t ≤ T, auxLabels init F ω t = labelsAt init ω t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      rw [auxLabels_succ, labelsAt_succ_eq_auxStep, h1]
      cases hd : drawLabels init ω (t + 1) with
      | none => rfl
      | some ij =>
          obtain ⟨i, j⟩ := ij
          have hij := (labelsAt_selected_transition init ω t i j hd).1
          simp only [auxStep, ruleUpdate]
          rw [hF _ (hG t (by omega)) i j hij]

/-- First-exit form: before the first time the actual process leaves `G`, and
at that time, the two processes agree. -/
theorem auxLabels_eq_labelsAt_before_exit (init : Cfg L K) (F : PairRule L K)
    (G : (Fin init.card → AgentState L K) → Prop)
    (hF : ∀ f, G f → ∀ i j : Fin init.card, i ≠ j →
      F (f i) (f j) = (NonuniformMajority L K).δ (f i) (f j))
    (ω : Ω L K) (hexit : ∃ t, ¬ G (labelsAt init ω t)) :
    ∀ t ≤ Nat.find hexit, auxLabels init F ω t = labelsAt init ω t :=
  auxLabels_eq_labelsAt_of_agree init F G hF ω _
    (fun _ ht => not_not.mp (Nat.find_min hexit ht))

/-- Event transfer: on the event that the actual process stays in `G` before
`T`, any event about the auxiliary path through `T` is the same event about the
actual path through `T`. -/
theorem aux_event_eq_actual_event (init : Cfg L K) (F : PairRule L K)
    (G : (Fin init.card → AgentState L K) → Prop)
    (hF : ∀ f, G f → ∀ i j : Fin init.card, i ≠ j →
      F (f i) (f j) = (NonuniformMajority L K).δ (f i) (f j))
    (T : ℕ)
    (P : ((t : Finset.Iic T) → Fin init.card → AgentState L K) → Prop) :
    {ω | (∀ t < T, G (labelsAt init ω t)) ∧
        P (fun t => auxLabels init F ω t.val)} =
      {ω | (∀ t < T, G (labelsAt init ω t)) ∧
        P (fun t => labelsAt init ω t.val)} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hG, hP⟩
    refine ⟨hG, ?_⟩
    have hpath : (fun t : Finset.Iic T => auxLabels init F ω t.val) =
        (fun t => labelsAt init ω t.val) := by
      funext t
      exact auxLabels_eq_labelsAt_of_agree init F G hF ω T hG t.val
        (Finset.mem_Iic.mp t.property)
    rwa [hpath] at hP
  · rintro ⟨hG, hP⟩
    refine ⟨hG, ?_⟩
    have hpath : (fun t : Finset.Iic T => auxLabels init F ω t.val) =
        (fun t => labelsAt init ω t.val) := by
      funext t
      exact auxLabels_eq_labelsAt_of_agree init F G hF ω T hG t.val
        (Finset.mem_Iic.mp t.property)
    rwa [hpath]

/-! Conditional one-step law given the pair log. -/

/-- A one-step event whose kernel mass is a function `q` of the recorded past has
conditional expectation `q` of the past. -/
theorem pairLog_condExp_indicator_of_prefix_mass
    (init : Cfg L K) (t : ℕ)
    (A : ((i : Finset.Iic t) → Draw L K) → Draw L K → Prop)
    (q : ((i : Finset.Iic t) → Draw L K) → ℝ≥0∞)
    (hmass : ∀ p,
      (drawLaw (prefixCfg init t p)).toMeasure {d | A p d} = q p) :
    (law init)[fun ω =>
      if A (frestrictLe t ω) (ω (t + 1)) then (1 : ℝ) else 0
      | pairLogFiltration L K t] =ᵐ[law init]
      (fun ω => (q (frestrictLe t ω)).toReal) := by
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
      Kernel.traj (X := fun _ => Draw L K) (fun s => pairKernel init s) 0
        (fun _ => none) :=
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
        Kernel.integral_traj (X := fun _ => Draw L K) (κ := κ) p
          hfm.aestronglyMeasurable
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

/-- The ordered distinct label pairs satisfying `A` at the labelling `f`. -/
noncomputable def goodPairs {m : ℕ}
    (A : (Fin m → AgentState L K) → Fin m → Fin m → Prop)
    (f : Fin m → AgentState L K) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun ij => ij.1 ≠ ij.2 ∧ A f ij.1 ij.2

/-- Mass of the next-draw event "the drawn pair satisfies `A` at labelling `g`",
for the scheduler at labelling `f`. -/
theorem selected_pair_event_mass (f g : Fin n → AgentState L K)
    (hn : 2 ≤ n) (A : (Fin n → AgentState L K) → Fin n → Fin n → Prop) :
    (drawLaw (labelCfg f)).toMeasure
        {d | ∃ i j, selectLabels f d = some (i, j) ∧ A g i j} =
      ((goodPairs A g).card : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  have hset : {d | ∃ i j, selectLabels f d = some (i, j) ∧ A g i j} =
      ⋃ ij ∈ goodPairs A g, {d : Draw L K | selectLabels f d = some ij} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, goodPairs, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨i, j, hs, hA⟩
      exact ⟨(i, j), ⟨selectLabels_distinct f d i j hs, hA⟩, hs⟩
    · rintro ⟨⟨i, j⟩, ⟨_, hA⟩, hs⟩
      exact ⟨i, j, hs, hA⟩
  rw [hset, measure_biUnion_finset]
  · have hterm : ∀ ij ∈ goodPairs A g,
        (drawLaw (labelCfg f)).toMeasure {d : Draw L K | selectLabels f d = some ij} =
          ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
      rintro ⟨i, j⟩ hij
      have hne : i ≠ j := (Finset.mem_filter.mp hij).2.1
      rw [drawLaw_event_eq_map]
      exact selectLabels_drawLaw f hn i j hne
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  · intro a _ b _ hab
    exact Set.disjoint_left.mpr fun d ha hb => hab (Option.some.inj (ha.symm.trans hb))
  · intro ij _
    exact (Set.to_countable _).measurableSet

/-- Conditional one-step law of the auxiliary process: given the pair log
through `t`, the probability that the next drawn label pair satisfies `A` at the
current auxiliary labelling is the fraction of ordered distinct pairs satisfying
it. This holds on every path, including after the auxiliary process separates
from the actual one, because the drawn labels are uniform given the past. -/
theorem aux_pair_conditional_probability
    (init : Cfg L K) (hc : 2 ≤ init.card) (F : PairRule L K)
    (A : (Fin init.card → AgentState L K) → Fin init.card → Fin init.card → Prop)
    (t : ℕ) :
    (law init)[fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          A (auxLabels init F ω t) i j
      then (1 : ℝ) else 0 | pairLogFiltration L K t]
      =ᵐ[law init]
    (fun ω => ((goodPairs A (auxLabels init F ω t)).card : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1))) := by
  let A' : ((k : Finset.Iic t) → Draw L K) → Draw L K → Prop :=
    fun p d => ∃ i j, selectLabels (prefixLabels init t p) d = some (i, j) ∧
      A (auxPrefix init F t p) i j
  let q : ((k : Finset.Iic t) → Draw L K) → ℝ≥0∞ := fun p =>
    ((goodPairs A (auxPrefix init F t p)).card : ℝ≥0∞) *
      ((init.card * (init.card - 1) : ℕ) : ℝ≥0∞)⁻¹
  have hmass (p : (k : Finset.Iic t) → Draw L K) :
      (drawLaw (prefixCfg init t p)).toMeasure {d | A' p d} = q p := by
    rw [← prefixLabels_config]
    exact selected_pair_event_mass _ _ hc A
  have h := pairLog_condExp_indicator_of_prefix_mass init t A' q hmass
  have hfun : (fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          A (auxLabels init F ω t) i j
      then (1 : ℝ) else 0) =
      (fun ω => @ite ℝ (A' (frestrictLe t ω) (ω (t + 1)))
        (Classical.propDecidable _) 1 0) := by
    funext ω
    congr 1
  rw [hfun]
  filter_upwards [h] with ω hω
  refine hω.trans ?_
  change (((goodPairs A (auxLabels init F ω t)).card : ℝ≥0∞) *
      ((init.card * (init.card - 1) : ℕ) : ℝ≥0∞)⁻¹).toReal = _
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ init.card), Nat.cast_one,
    div_eq_mul_inv]

/-! The configuration kernel as a label-pair count. -/

theorem ruleUpdate_delta (f : Fin n → AgentState L K) (i j : Fin n) :
    ruleUpdate (NonuniformMajority L K).δ f i j = updateLabels f i j := rfl

theorem goodPairs_true_card {m : ℕ} (f : Fin m → AgentState L K) :
    (goodPairs (fun _ _ _ => True) f).card = m * (m - 1) := by
  have h : goodPairs (fun _ _ _ => True) f = (Finset.univ : Finset (Fin m)).offDiag := by
    ext ij
    simp [goodPairs, Finset.mem_offDiag]
  rw [h, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.mul_sub_one]

/-- The protocol kernel at a labelled configuration, evaluated on a set `S`, is the
fraction of ordered distinct label pairs whose protocol update lands in `S`. -/
theorem transitionKernel_labelCfg_eq_goodPairs (f : Fin n → AgentState L K)
    (hn : 2 ≤ n) (S : Set (Cfg L K)) :
    (NonuniformMajority L K).transitionKernel (labelCfg f) S =
      ((goodPairs (fun g i j => labelCfg (updateLabels g i j) ∈ S) f).card : ℝ≥0∞) *
        ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  set μ := (drawLaw (labelCfg f)).toMeasure with hμ
  have hm : Measurable (applyDraw (labelCfg f)) := by
    intro A _
    exact (Set.to_countable _).measurableSet
  have hk : (NonuniformMajority L K).transitionKernel (labelCfg f) S =
      μ {d | labelCfg (stepLabels f d) ∈ S} := by
    rw [← drawLaw_map_toMeasure, Measure.map_apply hm (Set.to_countable _).measurableSet]
    congr 1
    ext d
    simp only [Set.mem_preimage, Set.mem_setOf_eq, stepLabels_config]
  let E : Set (Draw L K) :=
    {d | ∃ i j, selectLabels f d = some (i, j) ∧ labelCfg (updateLabels f i j) ∈ S}
  let N : Set (Draw L K) := {d | selectLabels f d = none}
  have hE : μ E = ((goodPairs (fun g i j => labelCfg (updateLabels g i j) ∈ S) f).card :
      ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ :=
    selected_pair_event_mass f f hn (fun g i j => labelCfg (updateLabels g i j) ∈ S)
  have hall : μ {d | ∃ i j, selectLabels f d = some (i, j) ∧ True} = 1 := by
    rw [selected_pair_event_mass f f hn (fun _ _ _ => True), goodPairs_true_card]
    have hne : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
      have : n * (n - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      exact_mod_cast this
    exact ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _)
  have hN : μ N = 0 := by
    have hc : N = {d | ∃ i j, selectLabels f d = some (i, j) ∧ True}ᶜ := by
      ext d
      simp only [N, Set.mem_setOf_eq, Set.mem_compl_iff, and_true, not_exists]
      constructor
      · intro h i j h'
        rw [h] at h'
        cases h'
      · intro h
        cases hs : selectLabels f d with
        | none => rfl
        | some ij => exact absurd hs (h ij.1 ij.2)
    rw [hc, prob_compl_eq_zero_iff (Set.to_countable _).measurableSet]
    exact hall
  have hsub1 : {d | labelCfg (stepLabels f d) ∈ S} ⊆ E ∪ N := by
    intro d hd
    cases hs : selectLabels f d with
    | none => exact Or.inr hs
    | some ij =>
        obtain ⟨i, j⟩ := ij
        refine Or.inl ⟨i, j, hs, ?_⟩
        have : stepLabels f d = updateLabels f i j := by
          unfold stepLabels
          rw [hs]
        simpa only [Set.mem_setOf_eq, this] using hd
  have hsub2 : E ⊆ {d | labelCfg (stepLabels f d) ∈ S} := by
    rintro d ⟨i, j, hs, hS⟩
    have : stepLabels f d = updateLabels f i j := by
      unfold stepLabels
      rw [hs]
    simpa only [Set.mem_setOf_eq, this] using hS
  rw [hk, ← hE]
  refine le_antisymm ?_ (measure_mono hsub2)
  calc
    μ {d | labelCfg (stepLabels f d) ∈ S} ≤ μ (E ∪ N) := measure_mono hsub1
    _ ≤ μ E + μ N := measure_union_le E N
    _ = μ E := by rw [hN, add_zero]

/-- The conditional probability, given the pair log through `t`, that the next drawn
label pair, applied with the protocol rule to the current auxiliary labelling, lands
in `S` is the protocol kernel mass of `S` at the auxiliary configuration. Kernel
floors proved for configurations therefore transfer to the auxiliary process. -/
theorem aux_conditional_kernel
    (init : Cfg L K) (hc : 2 ≤ init.card) (F : PairRule L K)
    (S : Set (Cfg L K)) (t : ℕ) :
    (law init)[fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          labelCfg (updateLabels (auxLabels init F ω t) i j) ∈ S
      then (1 : ℝ) else 0 | pairLogFiltration L K t]
      =ᵐ[law init]
    (fun ω => ((NonuniformMajority L K).transitionKernel (auxCfg init F ω t) S).toReal) := by
  have h := aux_pair_conditional_probability init hc F
    (fun g i j => labelCfg (updateLabels g i j) ∈ S) t
  refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans (h.trans ?_)
  · change (if _ then (1 : ℝ) else 0) = (if _ then (1 : ℝ) else 0)
    congr 1
  · refine Filter.Eventually.of_forall fun ω => ?_
    change _ = ((NonuniformMajority L K).transitionKernel
      (labelCfg (auxLabels init F ω t)) S).toReal
    rw [transitionKernel_labelCfg_eq_goodPairs _ hc, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ init.card), Nat.cast_one,
      div_eq_mul_inv]

/-! The actual trace: conditional kernel law and adapted step indicators. -/

/-- Given the pair log through `t`, the probability that the next configuration lies
in a set chosen from the current configuration is the protocol kernel mass of that
set at the current configuration. -/
theorem trace_conditional_kernel (init : Cfg L K)
    (S : Cfg L K → Set (Cfg L K)) (t : ℕ) :
    (law init)[fun ω =>
      if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0
      | pairLogFiltration L K t]
      =ᵐ[law init]
    (fun ω => ((NonuniformMajority L K).transitionKernel (trace init ω t)
      (S (trace init ω t))).toReal) := by
  let A : ((k : Finset.Iic t) → Draw L K) → Draw L K → Prop :=
    fun p d => applyDraw (prefixCfg init t p) d ∈ S (prefixCfg init t p)
  let q : ((k : Finset.Iic t) → Draw L K) → ℝ≥0∞ := fun p =>
    (NonuniformMajority L K).transitionKernel (prefixCfg init t p) (S (prefixCfg init t p))
  have hmass (p : (k : Finset.Iic t) → Draw L K) :
      (drawLaw (prefixCfg init t p)).toMeasure {d | A p d} = q p := by
    have hm : Measurable (applyDraw (prefixCfg init t p)) := by
      intro B _
      exact (Set.to_countable _).measurableSet
    change _ = (NonuniformMajority L K).transitionKernel (prefixCfg init t p)
      (S (prefixCfg init t p))
    rw [← drawLaw_map_toMeasure, Measure.map_apply hm (Set.to_countable _).measurableSet]
    rfl
  have h := pairLog_condExp_indicator_of_prefix_mass init t A q hmass
  refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans h
  change (if _ then (1 : ℝ) else 0) = (if _ then (1 : ℝ) else 0)
  congr 1

/-- The indicator that step `t + 1` lands in a set chosen from the configuration at
`t` is a 0/1 function, strongly measurable for the pair log through `t + 1`. -/
theorem stronglyMeasurable_trace_step_indicator (init : Cfg L K)
    (S : Cfg L K → Set (Cfg L K)) (t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (t + 1)] (fun ω =>
      if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) := by
  have hpair : Measurable[pairLogFiltration L K (t + 1)]
      (fun ω => (trace init ω t, trace init ω (t + 1))) :=
    (measurable_trace_at_of_le init (Nat.le_succ t)).prodMk
      (measurable_trace_at init (t + 1))
  have hset : MeasurableSet[pairLogFiltration L K (t + 1)]
      {ω | trace init ω (t + 1) ∈ S (trace init ω t)} :=
    hpair ((Set.to_countable {z : Cfg L K × Cfg L K | z.2 ∈ S z.1}).measurableSet)
  exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable

theorem trace_step_indicator_zero_or_one (init : Cfg L K)
    (S : Cfg L K → Set (Cfg L K)) (t : ℕ) (ω : Ω L K) :
    (if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) = 0 ∨
      (if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) = 1 := by
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- A kernel floor on a set `G` of configurations gives the conditional floor of the
step indicator on the event that the current configuration lies in `G`. -/
theorem trace_step_conditional_floor (init : Cfg L K)
    (S : Cfg L K → Set (Cfg L K)) (G : Cfg L K → Prop) (r : ℝ≥0∞)
    (hr : r ≠ ⊤)
    (hfloor : ∀ c, G c → r ≤ (NonuniformMajority L K).transitionKernel c (S c))
    (t : ℕ) :
    ∀ᵐ ω ∂law init, G (trace init ω t) →
      r.toReal ≤ ((law init)[fun ω =>
        if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0
        | pairLogFiltration L K t]) ω := by
  filter_upwards [trace_conditional_kernel init S t] with ω hω hG
  rw [hω]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (hfloor _ hG)

/-! Multiplicative drift of a potential of the auxiliary state. -/

theorem integrable_aux_potential (init : Cfg L K) (F : PairRule L K)
    (φ : (Fin init.card → AgentState L K) → ℝ) (t : ℕ) :
    Integrable (fun ω => φ (auxLabels init F ω t)) (law init) := by
  refine (integrable_const (∑ g, |φ g|)).mono'
    ((measurable_aux_potential init F φ t).mono
      ((pairLogFiltration L K).le t) le_rfl).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun g => |φ g|) (fun g _ => abs_nonneg (φ g))
    (Finset.mem_univ _)

/-- If a potential of the auxiliary state contracts by the factor `1 - c` in
conditional expectation at every step, its expectation at time `t` is at most
`(1 - c) ^ t` times its initial value. -/
theorem aux_drift_expectation_le (init : Cfg L K) (F : PairRule L K)
    (φ : (Fin init.card → AgentState L K) → ℝ) {c : ℝ} (hc : c ≤ 1)
    (hdrift : ∀ t,
      (law init)[fun ω => φ (auxLabels init F ω (t + 1)) | pairLogFiltration L K t]
        ≤ᵐ[law init] fun ω => (1 - c) * φ (auxLabels init F ω t))
    (t : ℕ) :
    ∫ ω, φ (auxLabels init F ω t) ∂law init ≤
      (1 - c) ^ t * φ (initialLabels init) := by
  induction t with
  | zero =>
      simp only [pow_zero, one_mul]
      change ∫ _ω, φ (initialLabels init) ∂law init ≤ _
      simp
  | succ t ih =>
      have hc0 : 0 ≤ 1 - c := by linarith
      calc
        ∫ ω, φ (auxLabels init F ω (t + 1)) ∂law init =
            ∫ ω, ((law init)[fun ω => φ (auxLabels init F ω (t + 1)) |
              pairLogFiltration L K t]) ω ∂law init :=
          (integral_condExp ((pairLogFiltration L K).le t)).symm
        _ ≤ ∫ ω, (1 - c) * φ (auxLabels init F ω t) ∂law init :=
          integral_mono_ae integrable_condExp
            ((integrable_aux_potential init F φ t).const_mul _) (hdrift t)
        _ = (1 - c) * ∫ ω, φ (auxLabels init F ω t) ∂law init :=
          integral_const_mul _ _
        _ ≤ (1 - c) * ((1 - c) ^ t * φ (initialLabels init)) :=
          mul_le_mul_of_nonneg_left ih hc0
        _ = (1 - c) ^ (t + 1) * φ (initialLabels init) := by ring

/-- Markov form of the drift bound for a nonnegative potential. -/
theorem aux_drift_tail_le (init : Cfg L K) (F : PairRule L K)
    (φ : (Fin init.card → AgentState L K) → ℝ) (hφ : ∀ g, 0 ≤ φ g)
    {c : ℝ} (hc : c ≤ 1)
    (hdrift : ∀ t,
      (law init)[fun ω => φ (auxLabels init F ω (t + 1)) | pairLogFiltration L K t]
        ≤ᵐ[law init] fun ω => (1 - c) * φ (auxLabels init F ω t))
    (t : ℕ) :
    (law init).real {ω | 1 ≤ φ (auxLabels init F ω t)} ≤
      (1 - c) ^ t * φ (initialLabels init) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => hφ (auxLabels init F ω t))
    (integrable_aux_potential init F φ t) 1
  rw [one_mul] at hm
  exact hm.trans (aux_drift_expectation_le init F φ hc hdrift t)

end Ripple.PopulationProtocol.ExactMajority.PairLogAuxiliary

end
