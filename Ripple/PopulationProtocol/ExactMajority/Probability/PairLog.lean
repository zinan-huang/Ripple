import Ripple.PopulationProtocol.ExactMajority.Probability.TimeTheorem
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Recorded scheduler pairs, persistent labels, and the configuration path law

The execution space and scheduler law are those of TimeTheorem. Coordinate zero
is a dummy, and coordinate t + 1 drives the transition from t to t + 1.

The file proves finite configuration-prefix agreement and full path-law
projection, transports the recorded occurrence pairs to fixed physical labels,
and proves the conditional uniform pair law given the complete recorded past.

The transport preserves every supported recorded occurrence pair. Outside that
support, it follows a valid occurrence pair with the same ordered states if one
exists. This makes the configuration identity valid on every path.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PairLog

open TimeTheorem

attribute [local instance] Classical.propDecidable

variable {L K n : ℕ}

/-! Finite configuration prefixes and the full path-law projection. -/

private def projectionSnoc {α : Type*} (t : ℕ)
    (p : Finset.Iic t → α) (a : α) : Finset.Iic (t + 1) → α :=
  fun i => if hi : i.val ≤ t then p ⟨i.val, Finset.mem_Iic.mpr hi⟩ else a

private theorem projectionSnoc_last {α : Type*} (t : ℕ)
    (p : Finset.Iic t → α) (a : α) :
    projectionSnoc t p a ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩ = a := by
  simp [projectionSnoc]

private theorem projectionSnoc_restrict {α : Type*} {s t : ℕ}
    (hst : s ≤ t) (p : Finset.Iic t → α) (a : α) :
    frestrictLe₂ (π := fun _ => α) (hst.trans (Nat.le_succ t))
        (projectionSnoc t p a) =
      frestrictLe₂ (π := fun _ => α) hst p := by
  funext i
  exact dif_pos ((Finset.mem_Iic.mp i.property).trans hst)

private theorem measurable_projectionSnoc {α : Type*} [MeasurableSpace α] (t : ℕ) :
    Measurable (fun z : (Finset.Iic t → α) × α =>
      projectionSnoc t z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.val ≤ t
  · have heval : Measurable
        (fun z : (Finset.Iic t → α) × α =>
          z.1 ⟨i.val, Finset.mem_Iic.mpr hi⟩) :=
      (measurable_pi_apply
        (⟨i.val, Finset.mem_Iic.mpr hi⟩ : Finset.Iic t)).comp measurable_fst
    simpa only [projectionSnoc, dif_pos hi] using heval
  · simpa only [projectionSnoc, dif_neg hi] using measurable_snd

private theorem projectionSnoc_eq_glue {α : Type*} [MeasurableSpace α]
    (t : ℕ) (p : Finset.Iic t → α) (a : α) :
    IicProdIoc (X := fun _ => α) t (t + 1)
        (p, MeasurableEquiv.piSingleton (X := fun _ => α) t a) =
      projectionSnoc t p a := by
  funext i
  by_cases hi : i.val ≤ t
  · simp [IicProdIoc, projectionSnoc, hi]
  · have heq : i = ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply Subtype.ext
      change i.val = t + 1
      have hib : i.val ≤ t + 1 := Finset.mem_Iic.mp i.property
      omega
    subst i
    simp [IicProdIoc, projectionSnoc, MeasurableEquiv.piSingleton]

/-- The exact one-step finite-trajectory integral, specialized to a constant
state type. It retains the whole past prefix. -/
private theorem projection_partialTraj_step
    {α : Type*} [MeasurableSpace α]
    (κ : (t : ℕ) → Kernel (Finset.Iic t → α) α)
    [∀ t, IsMarkovKernel (κ t)]
    (t : ℕ) (p : Finset.Iic t → α)
    (f : (Finset.Iic (t + 1) → α) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q, f q ∂Kernel.partialTraj (X := fun _ => α) κ t (t + 1) p) =
      ∫⁻ a, f (projectionSnoc t p a) ∂κ t p := by
  have hglue : Measurable (IicProdIoc (X := fun _ => α) t (t + 1)) :=
    measurable_IicProdIoc
  have hsection : Measurable
      (fun y : Finset.Ioc t (t + 1) → α =>
        f (IicProdIoc (X := fun _ => α) t (t + 1) (p, y))) :=
    (hf.comp hglue).comp (measurable_const.prodMk measurable_id)
  rw [Kernel.partialTraj_succ_self (X := fun _ => α) (κ := κ) t]
  rw [Kernel.lintegral_map _ hglue p hf]
  rw [Kernel.lintegral_id_prod
    (f := fun z => f (IicProdIoc (X := fun _ => α) t (t + 1) z)) (hf.comp hglue) _ p]
  rw [Kernel.lintegral_map (κ t)
    (MeasurableEquiv.piSingleton (X := fun _ => α) t).measurable p
    hsection] <;>
    exact lintegral_congr (fun a =>
      congrArg f (projectionSnoc_eq_glue t p a))

private theorem projection_partialTraj_succ
    {α : Type*} [MeasurableSpace α]
    (κ : (t : ℕ) → Kernel (Finset.Iic t → α) α)
    [∀ t, IsMarkovKernel (κ t)]
    (t : ℕ) (p : Finset.Iic 0 → α)
    (f : (Finset.Iic (t + 1) → α) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q, f q ∂Kernel.partialTraj (X := fun _ => α) κ 0 (t + 1) p) =
      ∫⁻ q, ∫⁻ a, f (projectionSnoc t q a) ∂κ t q
        ∂Kernel.partialTraj (X := fun _ => α) κ 0 t p := by
  rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le t),
    Kernel.lintegral_comp _ _ _ hf]
  apply lintegral_congr
  intro q
  exact projection_partialTraj_step κ t q f hf

/-- Every configuration in a finite prefix is reconstructed from the
corresponding initial segment of the recorded draws. -/
noncomputable def cfgPrefix (init : Cfg L K) (t : ℕ)
    (p : Finset.Iic t → Draw L K) : Finset.Iic t → Cfg L K :=
  fun i => prefixCfg init i.val
    (frestrictLe₂ (π := fun _ => Draw L K) (Finset.mem_Iic.mp i.property) p)

theorem measurable_cfgPrefix (init : Cfg L K) (t : ℕ) :
    Measurable (cfgPrefix init t) := by
  intro A _
  exact (Set.to_countable _).measurableSet

theorem cfgPrefix_zero (init : Cfg L K) (p : Finset.Iic 0 → Draw L K) :
    cfgPrefix init 0 p = fun _ => init := by
  funext i
  have hi : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ :=
    Subtype.ext (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property))
  subst i
  simp only [cfgPrefix, prefixCfg]

theorem cfgPrefix_last (init : Cfg L K) (t : ℕ)
    (p : Finset.Iic t → Draw L K) :
    cfgPrefix init t p ⟨t, Finset.mem_Iic.mpr le_rfl⟩ =
      prefixCfg init t p := by
  have hrestrict :
      frestrictLe₂ (π := fun _ => Draw L K) (le_refl t) p = p := by
    funext i
    rfl
  change prefixCfg init t
      (frestrictLe₂ (π := fun _ => Draw L K) (le_refl t) p) =
    prefixCfg init t p
  exact congrArg (prefixCfg init t) hrestrict

theorem cfgPrefix_trace (init : Cfg L K) (t : ℕ) :
    frestrictLe t ∘ trace init =
      cfgPrefix init t ∘ frestrictLe t := by
  funext ω i
  change prefixCfg init i.val
      (frestrictLe (π := fun _ => Draw L K) i.val ω) =
    prefixCfg init i.val
      (frestrictLe₂ (π := fun _ => Draw L K)
        (Finset.mem_Iic.mp i.property)
        (frestrictLe (π := fun _ => Draw L K) t ω))
  exact congrArg (prefixCfg init i.val)
    (congrFun
      (frestrictLe₂_comp_frestrictLe (π := fun _ => Draw L K)
        (Finset.mem_Iic.mp i.property)) ω).symm

private theorem prefixCfg_projectionSnoc (init : Cfg L K) (t : ℕ)
    (p : Finset.Iic t → Draw L K) (d : Draw L K) :
    prefixCfg init (t + 1) (projectionSnoc t p d) =
      applyDraw (prefixCfg init t p) d := by
  change applyDraw
      (prefixCfg init t
        (frestrictLe₂ (π := fun _ => Draw L K)
          (Nat.le_succ t) (projectionSnoc t p d)))
      (projectionSnoc t p d ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩) = _
  rw [projectionSnoc_restrict le_rfl, projectionSnoc_last]
  rfl

private theorem cfgPrefix_projectionSnoc (init : Cfg L K) (t : ℕ)
    (p : Finset.Iic t → Draw L K) (d : Draw L K) :
    cfgPrefix init (t + 1) (projectionSnoc t p d) =
      projectionSnoc t (cfgPrefix init t p) (applyDraw (prefixCfg init t p) d) := by
  funext i
  by_cases hi : i.val ≤ t
  · change prefixCfg init i.val
        (frestrictLe₂ (π := fun _ => Draw L K)
          (Finset.mem_Iic.mp i.property) (projectionSnoc t p d)) =
      (if h : i.val ≤ t then
        cfgPrefix init t p ⟨i.val, Finset.mem_Iic.mpr h⟩
      else applyDraw (prefixCfg init t p) d)
    rw [dif_pos hi]
    exact congrArg (prefixCfg init i.val) (projectionSnoc_restrict hi p d)
  · have heq : i = ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply Subtype.ext
      change i.val = t + 1
      have hib := Finset.mem_Iic.mp i.property
      omega
    subst i
    rw [projectionSnoc_last, cfgPrefix_last]
    exact prefixCfg_projectionSnoc init t p d

theorem drawLaw_map_toMeasure (c : Cfg L K) :
    Measure.map (applyDraw c) (drawLaw c).toMeasure =
      (NonuniformMajority L K).transitionKernel c := by
  have hm : Measurable (applyDraw c) := by
    intro A _
    exact (Set.to_countable _).measurableSet
  rw [PMF.toMeasure_map (applyDraw c) (drawLaw c) hm, drawLaw_projects] <;> rfl

private theorem projection_lintegral_applyDraw
    (c : Cfg L K) (f : Cfg L K → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ d, f (applyDraw c d) ∂(drawLaw c).toMeasure) =
      ∫⁻ c', f c' ∂(NonuniformMajority L K).transitionKernel c := by
  have hm : Measurable (applyDraw c) := by
    intro A _
    exact (Set.to_countable _).measurableSet
  rw [← drawLaw_map_toMeasure c, lintegral_map hf hm]

/-- Finite configuration-prefix agreement, proved by induction on the number
of draws. The successor step uses the entire previous prefix and the one-step
projection, not just the endpoint marginal. -/
theorem cfgPrefix_law (init : Cfg L K) (t : ℕ) :
    Measure.map (cfgPrefix init t)
      (Kernel.partialTraj (X := fun _ => Draw L K)
        (fun s => pairKernel init s) 0 t (fun _ => none)) =
      Kernel.partialTraj (X := ProtocolTraceLaw.St L K)
        (ProtocolTraceLaw.kfamily (L := L) (K := K)) 0 t (fun _ => init) := by
  induction t with
  | zero =>
      simp only [Kernel.partialTraj_self, Kernel.id_apply,
        Measure.map_dirac' (measurable_cfgPrefix init 0), cfgPrefix_zero]
  | succ t ih =>
      apply Measure.ext_of_lintegral
      intro f hf
      rw [lintegral_map hf (measurable_cfgPrefix init (t + 1))]
      rw [projection_partialTraj_succ (α := Draw L K)
        (fun s => pairKernel init s) t
        (fun _ => none) (fun q => f (cfgPrefix init (t + 1) q))
        (hf.comp (measurable_cfgPrefix init (t + 1)))]
      rw [projection_partialTraj_succ (α := Cfg L K)
        (ProtocolTraceLaw.kfamily (L := L) (K := K)) t (fun _ => init) f hf]
      have hnext : Measurable
          (fun q : Finset.Iic t → Cfg L K =>
            ∫⁻ c', f (projectionSnoc t q c') ∂
              ProtocolTraceLaw.kfamily (L := L) (K := K) t q) := by
        intro A _
        exact (Set.to_countable _).measurableSet
      rw [← ih, lintegral_map hnext (measurable_cfgPrefix init t)]
      apply lintegral_congr
      intro q
      simp_rw [cfgPrefix_projectionSnoc]
      change (∫⁻ d,
          f (projectionSnoc t (cfgPrefix init t q)
            (applyDraw (prefixCfg init t q) d))
          ∂(drawLaw (prefixCfg init t q)).toMeasure) =
        ∫⁻ c', f (projectionSnoc t (cfgPrefix init t q) c') ∂
          (NonuniformMajority L K).transitionKernel (prefixCfg init t q)
      exact projection_lintegral_applyDraw (prefixCfg init t q)
        (fun c' => f (projectionSnoc t (cfgPrefix init t q) c'))
        (hf.comp ((measurable_projectionSnoc t).comp
          ((measurable_const (a := cfgPrefix init t q)).prodMk measurable_id)))

theorem pair_log_projects_prefix (init : Cfg L K) (t : ℕ) :
    Measure.map (frestrictLe (π := ProtocolTraceLaw.St L K) t)
      (Measure.map (trace init) (law init)) =
      PhaseThreeModel.OccurrenceScheduler.occurrencePrefixLaw init t := by
  have hdraw :
      Measure.map (frestrictLe (π := fun _ => Draw L K) t) (law init) =
        Kernel.partialTraj (X := fun _ => Draw L K)
          (fun s => pairKernel init s) 0 t (fun _ => none) := by
    ext A hA
    rw [Measure.map_apply
      (measurable_frestrictLe (X := fun _ => Draw L K) t) hA]
    exact law_prefix init t A
  rw [Measure.map_map
      (measurable_frestrictLe (X := ProtocolTraceLaw.St L K) t)
      (measurable_trace init),
    cfgPrefix_trace, ← Measure.map_map (measurable_cfgPrefix init t)
      (measurable_frestrictLe (X := fun _ => Draw L K) t),
    hdraw, cfgPrefix_law]
  unfold PhaseThreeModel.OccurrenceScheduler.occurrencePrefixLaw
  rw [PhaseThreeModel.OccurrenceScheduler.occurrenceKfamily_eq]

theorem pair_log_projects_cylinder (init : Cfg L K) (t : ℕ)
    (A : Set (Finset.Iic t → Cfg L K)) (hA : MeasurableSet A) :
    law init {ω | frestrictLe t (trace init ω) ∈ A} =
      ProtocolTraceLaw.μ init {tr | frestrictLe t tr ∈ A} := by
  have hprefix :
      Measure.map (frestrictLe (π := ProtocolTraceLaw.St L K) t)
        (Measure.map (trace init) (law init)) =
      Measure.map (frestrictLe (π := ProtocolTraceLaw.St L K) t)
        (ProtocolTraceLaw.μ init) := by
    rw [pair_log_projects_prefix,
      PhaseThreeModel.OccurrenceScheduler.labeled_scheduler_projects_prefix]
  have h := congrArg (fun ν => ν A) hprefix
  dsimp only at h
  rw [Measure.map_apply
      (measurable_frestrictLe (X := ProtocolTraceLaw.St L K) t) hA,
    Measure.map_apply (measurable_trace init)
      ((measurable_frestrictLe (X := ProtocolTraceLaw.St L K) t) hA),
    Measure.map_apply
      (measurable_frestrictLe (X := ProtocolTraceLaw.St L K) t) hA] at h
  exact h

/-- N05: the recorded scheduler projects to the full configuration path law. -/
theorem pair_log_projects (init : Cfg L K) :
    Measure.map (trace init) (law init) = ProtocolTraceLaw.μ init := by
  let κ := ProtocolTraceLaw.kfamily (L := L) (K := K)
  let xzero : Finset.Iic 0 → Cfg L K := fun _ => init
  have hsource :
      IsProjectiveLimit (Measure.map (trace init) (law init))
        (inducedFamily (fun t => Kernel.partialTraj κ 0 t xzero)) := by
    apply (isProjectiveLimit_nat_iff
      (Kernel.isProjectiveMeasureFamily_partialTraj κ xzero) _).2
    intro t
    rw [inducedFamily_Iic, pair_log_projects_prefix]
    unfold PhaseThreeModel.OccurrenceScheduler.occurrencePrefixLaw
    rw [PhaseThreeModel.OccurrenceScheduler.occurrenceKfamily_eq] <;> rfl
  have htarget := Kernel.isProjectiveLimit_trajFun κ 0 xzero
  exact hsource.unique htarget

/-- The hypothesis required by TimeTheorem's expectation bridge now holds for
every initial configuration. -/
theorem endpointProjection (init : Cfg L K) : EndpointProjection init :=
  endpointProjection_of_traceProjection init (pair_log_projects init)

/-- The actual path hitting-time expectation agrees with expectedHitting,
with the former projection premise discharged. -/
theorem expectation_eq_expectedHitting (init : Cfg L K) :
    (∫⁻ ω, τ_D init ω ∂law init) =
      expectedHitting (NonuniformMajority L K).transitionKernel
        init (StableDone L K init) :=
  TimeTheorem.expectation_eq_expectedHitting init (endpointProjection init)

/-- The existing recovery-split consumer is available on the pair-log law
without an additional projection hypothesis. -/
theorem pathwiseRecoverySplit (init : Cfg L K) : PathwiseRecoverySplit init :=
  pathwiseRecoverySplit_of_endpointProjection init (endpointProjection init)

/-! Persistent labels and the guarded occurrence transport. -/

open PhaseThreeModel.OccurrenceScheduler

def labelCfg (f : Fin n → AgentState L K) : Cfg L K :=
  Finset.univ.val.map f

@[simp] theorem labelCfg_card (f : Fin n → AgentState L K) :
    (labelCfg f).card = n := by
  simp [labelCfg]

private def labelUnivEquiv (n : ℕ) :
    Fin n ≃ (Finset.univ.val : Multiset (Fin n)) where
  toFun i := ⟨i, ⟨0, by simp⟩⟩
  invFun a := a.1
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨i, k, hk⟩
    have hk' : k = 0 := by
      have : k < 1 := by simpa using hk
      omega
    subst k
    rfl

/-- The current fixed labels are matched bijectively with the exact
state-occurrence enumeration used by the recorded draw. -/
noncomputable def labelOccurrenceEquiv (f : Fin n → AgentState L K) :
    Fin n ≃ (labelCfg f).toEnumFinset :=
  (labelUnivEquiv n).trans
    (((Finset.univ.val : Multiset (Fin n)).mapEquiv f).trans
      (Multiset.coeEquiv (labelCfg f)))

theorem labelOccurrenceEquiv_state (f : Fin n → AgentState L K)
    (i : Fin n) :
    (labelOccurrenceEquiv f i).val.1 = f i := by
  change
    ((Finset.univ.val : Multiset (Fin n)).mapEquiv f
      (labelUnivEquiv n i) : AgentState L K) = f i
  simpa only [labelUnivEquiv, Equiv.coe_fn_mk] using
    Multiset.mapEquiv_apply
      (Finset.univ.val : Multiset (Fin n)) f (labelUnivEquiv n i)

theorem labelOccurrenceEquiv_symm_state
    (f : Fin n → AgentState L K) (a : (labelCfg f).toEnumFinset) :
    f ((labelOccurrenceEquiv f).symm a) = a.val.1 := by
  have h := labelOccurrenceEquiv_state f ((labelOccurrenceEquiv f).symm a)
  simpa only [Equiv.apply_symm_apply] using h.symm

noncomputable def encodeLabelPair (f : Fin n → AgentState L K)
    (i j : Fin n) (hij : i ≠ j) : occurrencePairs (labelCfg f) :=
  ⟨((labelOccurrenceEquiv f i).val, (labelOccurrenceEquiv f j).val),
    Finset.mem_offDiag.mpr
      ⟨(labelOccurrenceEquiv f i).property,
       (labelOccurrenceEquiv f j).property, by
        intro h
        exact hij ((labelOccurrenceEquiv f).injective (Subtype.ext h))⟩⟩

noncomputable def decodeLabelPair (f : Fin n → AgentState L K)
    (p : occurrencePairs (labelCfg f)) : Fin n × Fin n :=
  ((labelOccurrenceEquiv f).symm
      ⟨p.val.1, (Finset.mem_offDiag.mp p.property).1⟩,
   (labelOccurrenceEquiv f).symm
      ⟨p.val.2, (Finset.mem_offDiag.mp p.property).2.1⟩)

theorem decodeLabelPair_distinct (f : Fin n → AgentState L K)
    (p : occurrencePairs (labelCfg f)) :
    (decodeLabelPair f p).1 ≠ (decodeLabelPair f p).2 := by
  intro h
  have he := congrArg (labelOccurrenceEquiv f) h
  have hv := congrArg Subtype.val he
  simp only [decodeLabelPair, Equiv.apply_symm_apply] at hv
  exact (Finset.mem_offDiag.mp p.property).2.2 hv

theorem decodeLabelPair_state (f : Fin n → AgentState L K)
    (p : occurrencePairs (labelCfg f)) :
    (f (decodeLabelPair f p).1, f (decodeLabelPair f p).2) =
      occurrenceStatePair p.val := by
  apply Prod.ext
  · exact labelOccurrenceEquiv_symm_state f _
  · exact labelOccurrenceEquiv_symm_state f _

@[simp] theorem decode_encode_labelPair (f : Fin n → AgentState L K)
    (i j : Fin n) (hij : i ≠ j) :
    decodeLabelPair f (encodeLabelPair f i j hij) = (i, j) := by
  simp [decodeLabelPair, encodeLabelPair]

theorem decodeLabelPair_injective (f : Fin n → AgentState L K) :
    Function.Injective (decodeLabelPair f) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg (fun z => (labelOccurrenceEquiv f z.1).val) hpq
    simpa only [decodeLabelPair, Equiv.apply_symm_apply] using h
  · have h := congrArg (fun z => (labelOccurrenceEquiv f z.2).val) hpq
    simpa only [decodeLabelPair, Equiv.apply_symm_apply] using h

private theorem occurrence_exists_of_applicable
    (c : Cfg L K) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) :
    ∃ p ∈ occurrencePairs c, occurrenceStatePair p = (s, t) := by
  have hcounts := Multiset.le_iff_count.mp happ
  have hpositive : 0 < c.interactionCount s t := by
    by_cases hst : s = t
    · subst t
      have hs : 2 ≤ c.count s := by
        simpa [Config.count] using hcounts s
      simp only [Config.interactionCount, if_pos rfl]
      exact Nat.mul_pos (by omega) (by omega)
    · have hs : 1 ≤ c.count s := by
        simpa [Config.count, hst] using hcounts s
      have ht : 1 ≤ c.count t := by
        simpa [Config.count, hst, Ne.symm hst] using hcounts t
      simp only [Config.interactionCount, if_neg hst]
      exact Nat.mul_pos hs ht
  have hnonempty :
      ((occurrencePairs c).filter
        (fun p => (s, t) = occurrenceStatePair p)).Nonempty := by
    apply Finset.card_pos.mp
    rw [occurrence_pair_fiber_card]
    exact hpositive
  obtain ⟨p, hp⟩ := hnonempty
  exact ⟨p, (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2.symm⟩

/-- Keep a supported record verbatim. Off support, use a valid occurrence
pair with the same state pair when there is one; otherwise do nothing. -/
noncomputable def guardedOccurrence (c : Cfg L K) :
    Draw L K → Option (occurrencePairs c)
  | none => none
  | some p =>
      if hp : p ∈ occurrencePairs c then some ⟨p, hp⟩
      else if hq : ∃ q : occurrencePairs c,
          occurrenceStatePair q.val = occurrenceStatePair p then
        some (Classical.choose hq)
      else none

theorem guardedOccurrence_of_mem (c : Cfg L K)
    (p : OccurrencePair (AgentState L K)) (hp : p ∈ occurrencePairs c) :
    guardedOccurrence c (some p) = some ⟨p, hp⟩ := by
  simp only [guardedOccurrence, dif_pos hp]

theorem guardedOccurrence_state (c : Cfg L K)
    (p : OccurrencePair (AgentState L K)) (q : occurrencePairs c)
    (h : guardedOccurrence c (some p) = some q) :
    occurrenceStatePair q.val = occurrenceStatePair p := by
  classical
  by_cases hp : p ∈ occurrencePairs c
  · simp only [guardedOccurrence, dif_pos hp, Option.some.injEq] at h
    subst q
    rfl
  · by_cases hq : ∃ r : occurrencePairs c,
        occurrenceStatePair r.val = occurrenceStatePair p
    · simp only [guardedOccurrence, dif_neg hp, dif_pos hq,
        Option.some.injEq] at h
      subst q
      exact Classical.choose_spec hq
    · simp only [guardedOccurrence, dif_neg hp, dif_neg hq,
        reduceCtorEq] at h

theorem guardedOccurrence_none_not_applicable (c : Cfg L K)
    (p : OccurrencePair (AgentState L K))
    (h : guardedOccurrence c (some p) = none) :
    ¬ Protocol.Applicable c p.1.1 p.2.1 := by
  intro happ
  obtain ⟨q, hq, hstate⟩ :=
    occurrence_exists_of_applicable c p.1.1 p.2.1 happ
  have hex : ∃ r : occurrencePairs c,
      occurrenceStatePair r.val = occurrenceStatePair p :=
    ⟨⟨q, hq⟩, hstate⟩
  by_cases hp : p ∈ occurrencePairs c <;>
    simp [guardedOccurrence, hp, hex] at h

noncomputable def selectLabels (f : Fin n → AgentState L K)
    (o : Draw L K) : Option (Fin n × Fin n) :=
  (guardedOccurrence (labelCfg f) o).map (decodeLabelPair f)

theorem selectLabels_of_mem (f : Fin n → AgentState L K)
    (p : OccurrencePair (AgentState L K))
    (hp : p ∈ occurrencePairs (labelCfg f)) :
    selectLabels f (some p) = some (decodeLabelPair f ⟨p, hp⟩) := by
  simp only [selectLabels,
    guardedOccurrence_of_mem (labelCfg f) p hp, Option.map_some]

theorem selectLabels_distinct (f : Fin n → AgentState L K)
    (o : Draw L K) (i j : Fin n)
    (h : selectLabels f o = some (i, j)) : i ≠ j := by
  unfold selectLabels at h
  cases hg : guardedOccurrence (labelCfg f) o with
  | none => simp only [hg, Option.map_none, reduceCtorEq] at h
  | some p =>
      have hpair : decodeLabelPair f p = (i, j) := by
        simpa only [hg, Option.map_some, Option.some.injEq] using h
      simpa only [hpair] using decodeLabelPair_distinct f p

def updateLabels (f : Fin n → AgentState L K) (i j : Fin n) :
    Fin n → AgentState L K :=
  Function.update (Function.update f i
    ((NonuniformMajority L K).δ (f i) (f j)).1) j
      ((NonuniformMajority L K).δ (f i) (f j)).2

theorem updateLabels_config (f : Fin n → AgentState L K)
    (i j : Fin n) (hij : i ≠ j) :
    labelCfg (updateLabels f i j) =
      labelCfg f - {f i, f j} +
        {((NonuniformMajority L K).δ (f i) (f j)).1,
         ((NonuniformMajority L K).δ (f i) (f j)).2} := by
  classical
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
  have hrest : rest.val.map (updateLabels f i j) = rest.val.map f := by
    apply Multiset.map_congr rfl
    intro k hk
    have hk' : k ∈ rest := hk
    have hki : k ≠ i := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hk').2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk').1
    simp [updateLabels, hki, hkj]
  have hbefore : labelCfg f = rest.val.map f + {f i, f j} := by
    unfold labelCfg
    rw [hsplit]
    simp [add_comm, add_left_comm, add_assoc]
    exact (Multiset.singleton_add (f j) (rest.val.map f)).symm.trans
      (add_comm _ _)
  have hafter : labelCfg (updateLabels f i j) =
      rest.val.map f +
        {((NonuniformMajority L K).δ (f i) (f j)).1,
         ((NonuniformMajority L K).δ (f i) (f j)).2} := by
    unfold labelCfg
    rw [hsplit]
    simp only [Multiset.map_cons, hrest]
    simp [updateLabels, hij, Ne.symm hij, add_comm, add_left_comm, add_assoc]
    exact (Multiset.singleton_add
      ((NonuniformMajority L K).δ (f i) (f j)).2
      (rest.val.map f)).symm.trans (add_comm _ _)
  rw [hbefore, add_tsub_cancel_right]
  exact hafter

noncomputable def stepLabels (f : Fin n → AgentState L K)
    (o : Draw L K) : Fin n → AgentState L K :=
  match selectLabels f o with
  | none => f
  | some (i, j) => updateLabels f i j

theorem stepLabels_config (f : Fin n → AgentState L K) (o : Draw L K) :
    labelCfg (stepLabels f o) = applyDraw (labelCfg f) o := by
  cases o with
  | none => rfl
  | some p =>
      cases hg : guardedOccurrence (labelCfg f) (some p) with
      | none =>
          have hnot := guardedOccurrence_none_not_applicable (labelCfg f) p hg
          have hsel : selectLabels f (some p) = none := by
            simp only [selectLabels, hg, Option.map_none]
          rw [stepLabels, hsel]
          exact (Protocol.stepOrSelf_eq_self_of_not_applicable
            (P := NonuniformMajority L K) hnot).symm
      | some q =>
          have hstate := guardedOccurrence_state (labelCfg f) p q hg
          have hsel : selectLabels f (some p) = some (decodeLabelPair f q) := by
            simp only [selectLabels, hg, Option.map_some]
          have hpair : (f (decodeLabelPair f q).1, f (decodeLabelPair f q).2) =
              occurrenceStatePair p :=
            (decodeLabelPair_state f q).trans hstate
          have hs : f (decodeLabelPair f q).1 = p.1.1 :=
            congrArg Prod.fst hpair
          have ht : f (decodeLabelPair f q).2 = p.2.1 :=
            congrArg Prod.snd hpair
          have happ : Protocol.Applicable (labelCfg f) p.1.1 p.2.1 := by
            have hq := occurrence_pair_applicable (labelCfg f) q.val q.property
            have hqs : q.val.1.1 = p.1.1 :=
              congrArg (fun z : AgentState L K × AgentState L K => z.1) hstate
            have hqt : q.val.2.1 = p.2.1 :=
              congrArg (fun z : AgentState L K × AgentState L K => z.2) hstate
            simpa only [hqs, hqt] using hq
          rw [stepLabels, hsel]
          rw [updateLabels_config f _ _ (decodeLabelPair_distinct f q), hs, ht]
          simp only [applyDraw, Protocol.scheduledStep, occurrenceStatePair,
            Protocol.stepOrSelf, if_pos happ]

private noncomputable def initialLabelEquiv (init : Cfg L K) :
    Fin init.card ≃ init :=
  Fintype.equivOfCardEq (by simp)

noncomputable def initialLabels (init : Cfg L K) :
    Fin init.card → AgentState L K :=
  fun i => (initialLabelEquiv init i : AgentState L K)

theorem initialLabels_config (init : Cfg L K) :
    labelCfg (initialLabels init) = init := by
  change (Finset.univ.val.map
    ((fun a : init => (a : AgentState L K)) ∘ initialLabelEquiv init)) = init
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv, Multiset.map_univ_coe]

noncomputable def prefixLabels (init : Cfg L K) :
    (t : ℕ) → ((k : Finset.Iic t) → Draw L K) →
      Fin init.card → AgentState L K
  | 0, _ => initialLabels init
  | t + 1, p =>
      stepLabels
        (prefixLabels init t (fun k =>
          p ⟨k.val, Finset.mem_Iic.mpr
            (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩))
        (p ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩)

theorem prefixLabels_config (init : Cfg L K) (t : ℕ)
    (p : (k : Finset.Iic t) → Draw L K) :
    labelCfg (prefixLabels init t p) = prefixCfg init t p := by
  induction t with
  | zero => exact initialLabels_config init
  | succ t ih =>
      change labelCfg (stepLabels _ _) = applyDraw _ _
      rw [stepLabels_config, ih]

theorem measurable_prefixLabels (init : Cfg L K) (t : ℕ) :
    Measurable (prefixLabels init t) := by
  intro A hA
  exact (Set.to_countable _).measurableSet

noncomputable def labelsAt (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    Fin init.card → AgentState L K :=
  prefixLabels init t (Preorder.frestrictLe t ω)

noncomputable def drawLabels (init : Cfg L K) (ω : Ω L K) :
    ℕ → Option (Fin init.card × Fin init.card)
  | 0 => none
  | t + 1 => selectLabels (labelsAt init ω t) (ω (t + 1))

theorem drawLabels_succ (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    drawLabels init ω (t + 1) =
      selectLabels (prefixLabels init t (Preorder.frestrictLe t ω))
        (ω (t + 1)) := rfl

theorem labelsAt_succ (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    labelsAt init ω (t + 1) =
      stepLabels (labelsAt init ω t) (ω (t + 1)) := rfl

theorem labelsAt_config (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    (Finset.univ.val.map (labelsAt init ω t)) = trace init ω t :=
  prefixLabels_config init t (Preorder.frestrictLe t ω)

theorem labelsAt_selected_transition
    (init : Cfg L K) (ω : Ω L K) (t : ℕ)
    (i j : Fin init.card)
    (h : drawLabels init ω (t + 1) = some (i, j)) :
    i ≠ j ∧
    labelsAt init ω (t + 1) i =
      ((NonuniformMajority L K).δ
        (labelsAt init ω t i) (labelsAt init ω t j)).1 ∧
    labelsAt init ω (t + 1) j =
      ((NonuniformMajority L K).δ
        (labelsAt init ω t i) (labelsAt init ω t j)).2 ∧
    ∀ k : Fin init.card, k ≠ i → k ≠ j →
      labelsAt init ω (t + 1) k = labelsAt init ω t k := by
  change selectLabels (labelsAt init ω t) (ω (t + 1)) = some (i, j) at h
  have hij := selectLabels_distinct (labelsAt init ω t) (ω (t + 1)) i j h
  have hu : labelsAt init ω (t + 1) = updateLabels (labelsAt init ω t) i j := by
    rw [labelsAt_succ, stepLabels, h]
  refine ⟨hij, ?_, ?_, ?_⟩
  · rw [hu]
    simp [updateLabels, hij]
  · rw [hu]
    simp [updateLabels]
  · intro k hki hkj
    rw [hu]
    simp [updateLabels, hki, hkj]

private theorem uniform_finset_map_mass
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (hs : s.Nonempty) (f : α → β) (b : β) :
    ((PMF.uniformOfFinset s hs).map f) b =
      (((s.filter fun a => b = f a).card : ℝ≥0∞) /
        (s.card : ℝ≥0∞)) := by
  classical
  calc
    ((PMF.uniformOfFinset s hs).map f) b =
        ∑' a, if b = f a then PMF.uniformOfFinset s hs a else 0 := by
      rw [PMF.map_apply]
      apply tsum_congr
      intro a
      by_cases h : b = f a
      · simp only [if_pos h]
      · simp only [if_neg h]
    _ = ∑ a ∈ s, if b = f a then PMF.uniformOfFinset s hs a else 0 := by
      exact tsum_eq_sum fun a ha => by
        simp [PMF.uniformOfFinset_apply_of_notMem hs ha]
    _ = ∑ a ∈ s, if b = f a then (s.card : ℝ≥0∞)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [PMF.uniformOfFinset_apply_of_mem hs ha]
    _ = ∑ a ∈ s.filter (fun a => b = f a), (s.card : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_filter]
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem selected_label_fiber (f : Fin n → AgentState L K)
    (i j : Fin n) (hij : i ≠ j) :
    ((occurrencePairs (labelCfg f)).filter
      (fun p => some (i, j) = selectLabels f (some p))) =
        {(encodeLabelPair f i j hij).val} := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hmem, hsel⟩ := Finset.mem_filter.mp hp
    have hdec : decodeLabelPair f ⟨p, hmem⟩ = (i, j) := by
      rw [selectLabels_of_mem f p hmem] at hsel
      exact (Option.some.inj hsel).symm
    have heq : (⟨p, hmem⟩ : occurrencePairs (labelCfg f)) =
        encodeLabelPair f i j hij :=
      decodeLabelPair_injective f (hdec.trans (decode_encode_labelPair f i j hij).symm)
    exact Finset.mem_singleton.mpr (congrArg Subtype.val heq)
  · intro hp
    have heq : p = (encodeLabelPair f i j hij).val := Finset.mem_singleton.mp hp
    subst p
    refine Finset.mem_filter.mpr ⟨(encodeLabelPair f i j hij).property, ?_⟩
    rw [selectLabels_of_mem f _ (encodeLabelPair f i j hij).property]
    change some (i, j) =
      some (decodeLabelPair f (encodeLabelPair f i j hij))
    exact (congrArg (fun p : Fin n × Fin n => some p)
      (decode_encode_labelPair f i j hij)).symm

/-- The state-dependent transport is a bijection on the actual support;
each distinct ordered physical pair therefore has exactly one preimage. -/
theorem selectLabels_drawLaw (f : Fin n → AgentState L K)
    (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ((drawLaw (labelCfg f)).map (selectLabels f)) (some (i, j)) =
      ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  have hc : 2 ≤ (labelCfg f).card := by simpa using hn
  simp only [drawLaw, dif_pos hc, PMF.map_comp]
  change ((PMF.uniformOfFinset (occurrencePairs (labelCfg f))
    (occurrencePairs_nonempty (labelCfg f) hc)).map
      (fun p => selectLabels f (some p))) (some (i, j)) = _
  rw [uniform_finset_map_mass, selected_label_fiber f i j hij]
  simp only [Finset.card_singleton, Nat.cast_one, one_div,
    occurrencePairs_card, Config.totalPairs, labelCfg_card]

/-! The sigma-algebra through time t retains every recorded draw through t,
including the dummy coordinate zero. -/

noncomputable def pairLogFiltration (L K : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Ω L K)) :=
  Filtration.piLE (X := fun _ : ℕ => Draw L K)

theorem pairLogFiltration_eq_comap (L K t : ℕ) :
    pairLogFiltration L K t =
      MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => Draw L K) t)
        (inferInstance : MeasurableSpace ((i : Finset.Iic t) → Draw L K)) := by
  exact Filtration.piLE_eq_comap_frestrictLe t

theorem measurable_pairLog_prefix (L K t : ℕ) :
    Measurable[pairLogFiltration L K t]
      (frestrictLe (π := fun _ : ℕ => Draw L K) t) := by
  rw [pairLogFiltration_eq_comap]
  exact Measurable.of_comap_le le_rfl

theorem measurable_trace_at (init : Cfg L K) (t : ℕ) :
    Measurable[pairLogFiltration L K t] (fun ω => trace init ω t) := by
  exact (measurable_prefixCfg init t).comp (measurable_pairLog_prefix L K t)

theorem measurable_trace_at_of_le (init : Cfg L K) {s t : ℕ}
    (hst : s ≤ t) :
    Measurable[pairLogFiltration L K t] (fun ω => trace init ω s) :=
  (measurable_trace_at init s).mono
    ((pairLogFiltration L K).mono hst) le_rfl

theorem firstPhaseSeed_measurableSet
    (init : Cfg L K) (p t : ℕ) :
    MeasurableSet[pairLogFiltration L K t]
      {ω | firstPhaseSeed init p t ω} := by
  have hnow : MeasurableSet[pairLogFiltration L K t]
      {ω | ∃ a ∈ trace init ω t, a.phase.val = p} :=
    (show MeasurableSet {c : Cfg L K | ∃ a ∈ c, a.phase.val = p} from
      (Set.to_countable _).measurableSet).preimage (measurable_trace_at init t)
  have hpast (u : ℕ) : MeasurableSet[pairLogFiltration L K t]
      {ω | u < t → ∀ a ∈ trace init ω u, a.phase.val < p} := by
    by_cases hu : u < t
    · simpa only [hu, true_implies] using
        (show MeasurableSet {c : Cfg L K | ∀ a ∈ c, a.phase.val < p} from
          (Set.to_countable _).measurableSet).preimage
            (measurable_trace_at_of_le init hu.le)
    · simp only [hu, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  have heq :
      {ω | firstPhaseSeed init p t ω} =
        {ω | ∃ a ∈ trace init ω t, a.phase.val = p} ∩
          ⋂ u : ℕ, {ω | u < t → ∀ a ∈ trace init ω u, a.phase.val < p} := by
    ext ω
    simp only [firstPhaseSeed, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  exact hnow.inter (MeasurableSet.iInter hpast)

/-- A one-step event with the same kernel mass at every recorded past has
that constant conditional expectation. The event may depend on the full past. -/
theorem pairLog_condExp_indicator_of_next_mass
    {L K : ℕ} (init : Cfg L K) (t : ℕ)
    (A : ((i : Finset.Iic t) → Draw L K) → Draw L K → Prop)
    (q : ℝ≥0∞)
    (hmass : ∀ p,
      (drawLaw (prefixCfg init t p)).toMeasure {d | A p d} = q) :
    (law init)[fun ω =>
      if A (frestrictLe t ω) (ω (t + 1)) then (1 : ℝ) else 0
      | pairLogFiltration L K t] =ᵐ[law init]
      (fun _ => q.toReal) := by
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
        q.toReal := by
    have hp : MeasurableSet {d : Draw L K | A p d} :=
      (Set.to_countable _).measurableSet
    calc
      (∫ d, (if A p d then (1 : ℝ) else 0) ∂pairKernel init t p) =
          (pairKernel init t p).real {d | A p d} := by
        simpa only [Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using
          (integral_indicator_one (μ := pairKernel init t p) hp)
      _ = q.toReal := by
        change ((drawLaw (prefixCfg init t p)).toMeasure {d | A p d}).toReal = _
        rw [hmass p]
  have htraj (p : (i : Finset.Iic t) → Draw L K) :
      (∫ y, f y ∂Kernel.traj κ t p) = q.toReal := by
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
      _ = q.toReal := hlocal p
  filter_upwards [hce] with ω hω
  exact hω.trans (htraj (frestrictLe t ω))

/-- The mass of a next-draw fibre is the corresponding mapped PMF value. -/
theorem drawLaw_event_eq_map
    {L K : ℕ} {β : Type*} (c : Cfg L K)
    (g : Draw L K → β) (b : β) :
    (drawLaw c).toMeasure {d | g d = b} = ((drawLaw c).map g) b := by
  have hs : MeasurableSet {d : Draw L K | g d = b} :=
    (Set.to_countable _).measurableSet
  rw [(drawLaw c).toMeasure_apply_eq_toOuterMeasure_apply hs]
  change (drawLaw c).toOuterMeasure (g ⁻¹' {b}) = _
  rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]

theorem selected_pair_conditional_probability {L K : ℕ}
    (init : Cfg L K) (hc : 2 ≤ init.card)
    (i j : Fin init.card) (hij : i ≠ j) (t : ℕ) :
    (law init)[fun ω =>
      if drawLabels init ω (t + 1) = some (i, j)
      then (1 : ℝ) else 0 | pairLogFiltration L K t]
      =ᵐ[law init]
    (fun _ => 1 / ((init.card : ℝ) * ((init.card : ℝ) - 1))) := by
  classical
  let A : ((k : Finset.Iic t) → Draw L K) → Draw L K → Prop :=
    fun p d => selectLabels (prefixLabels init t p) d = some (i, j)
  let q : ℝ≥0∞ := ((init.card * (init.card - 1) : ℕ) : ℝ≥0∞)⁻¹
  have hmass (p : (k : Finset.Iic t) → Draw L K) :
      (drawLaw (prefixCfg init t p)).toMeasure {d | A p d} = q := by
    change (drawLaw (prefixCfg init t p)).toMeasure
      {d | selectLabels (prefixLabels init t p) d = some (i, j)} = q
    rw [drawLaw_event_eq_map]
    have hu := selectLabels_drawLaw (prefixLabels init t p) hc i j hij
    simpa only [prefixLabels_config, q] using hu
  have h := pairLog_condExp_indicator_of_next_mass init t A q hmass
  have hq :
      q.toReal = 1 / ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
    change (((init.card * (init.card - 1) : ℕ) : ℝ≥0∞)⁻¹).toReal = _
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ init.card),
      Nat.cast_one, one_div]
  rw [hq] at h
  refine (condExp_congr_ae (μ := law init)
    (m := pairLogFiltration L K t) ?_).trans h
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hsel :
      selectLabels
        (prefixLabels init t
          (frestrictLe (π := fun _ : ℕ => Draw L K) t ω))
        (ω (t + 1)) = some (i, j)
  · simp only [A, drawLabels_succ, if_pos hsel]
  · simp only [A, drawLabels_succ, if_neg hsel]

/-- Sum estimates over the disjoint genuine seed times. Finiteness is
needed only on the bad event; no factor counting possible seed times occurs. -/
theorem genuine_seed_splice
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → WithTop ℕ) (B : Set Ω) (ε : ℝ≥0∞)
    (hB : MeasurableSet B)
    (hS : ∀ s : ℕ,
      MeasurableSet {ω | S ω = (s : WithTop ℕ)})
    (hfinite : ∀ ω ∈ B, S ω ≠ ⊤)
    (hlocal : ∀ s : ℕ,
      μ (B ∩ {ω | S ω = (s : WithTop ℕ)}) ≤
        ε * μ {ω | S ω = (s : WithTop ℕ)}) :
    μ B ≤ ε := by
  let E : ℕ → Set Ω := fun s => {ω | S ω = (s : WithTop ℕ)}
  have hdisj : Pairwise (fun s t => Disjoint (E s) (E t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro ω hs ht
    exact hst (WithTop.coe_injective (hs.symm.trans ht))
  have hcover : B ⊆ ⋃ s : ℕ, B ∩ E s := by
    intro ω hω
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hfinite ω hω)
    exact Set.mem_iUnion.mpr ⟨s, hω, hs.symm⟩
  have hmass : (∑' s : ℕ, μ (E s)) ≤ 1 := by
    rw [← measure_iUnion hdisj hS]
    exact prob_le_one
  calc
    μ B ≤ μ (⋃ s : ℕ, B ∩ E s) := measure_mono hcover
    _ ≤ ∑' s : ℕ, μ (B ∩ E s) := measure_iUnion_le _
    _ ≤ ∑' s : ℕ, ε * μ (E s) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ε * ∑' s : ℕ, μ (E s) := by rw [ENNReal.tsum_mul_left]
    _ ≤ ε * 1 := mul_le_mul_left' hmass ε
    _ = ε := mul_one ε

end Ripple.PopulationProtocol.ExactMajority.PairLog

end
