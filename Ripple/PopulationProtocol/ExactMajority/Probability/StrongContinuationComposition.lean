-- Ripple/PopulationProtocol/ExactMajority/Probability/StrongContinuationComposition.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongContinuationTimer
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongGapBackupTail

/-!
Original-law composition on recorded prefixes.  All intermediate good
sets are measurable at their own observed endpoints.  A future success
event is never used to alter the scheduler's law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.StrongContinuationComposition

open TimeTheorem PairLog TraceDrain StageEventSpec PhaseOneDrainStopping
  StrongContinuationTimer UniformRecovery

variable {L K : ℕ}

theorem prefix_reachable (init : Cfg L K) (s : ℕ)
    (a : (k : Finset.Iic s) → Draw L K) :
    (NonuniformMajority L K).Reachable init (prefixCfg init s a) := by
  induction s with
  | zero => exact Relation.ReflTransGen.refl
  | succ s ih =>
      let b := restrictPrefix (Nat.le_succ s) a
      change (NonuniformMajority L K).Reachable init
        (applyDraw (prefixCfg init s b) (a ⟨s + 1, Finset.mem_Iic.mpr le_rfl⟩))
      exact (ih b).trans (applyDraw_reachable _ _)

theorem prefix_card (init : Cfg L K) (s : ℕ)
    (a : (k : Finset.Iic s) → Draw L K) :
    (prefixCfg init s a).card = init.card :=
  Protocol.reachable_card_eq (prefix_reachable init s a)

theorem stable_persists (init : Cfg L K) (ω : Ω L K) (s t : ℕ)
    (hst : s ≤ t) (hs : trace init ω s ∈ StableDone L K init) :
    trace init ω t ∈ StableDone L K init :=
  (hitBy_iff_endpoint init ω t).1
    (hitBy_mono init hst ((hitBy_iff_endpoint init ω s).2 hs))

theorem seed_persists (init : Cfg L K) (ω : Ω L K) (p s t : ℕ)
    (hp : 1 ≤ p) (hst : s ≤ t)
    (hs : ∃ a ∈ trace init ω s, p ≤ a.phase.val) :
    ∃ a ∈ trace init ω t, p ≤ a.phase.val := by
  by_contra h
  have hupper : ∀ a ∈ trace init ω t, a.phase.val ≤ p - 1 := by
    intro a ha
    by_contra hu
    exact h ⟨a, ha, by omega⟩
  have hold := phase_upper_reachable (p - 1) _ _
    (trace_reachable init ω hst) hupper
  obtain ⟨a, ha, hphase⟩ := hs
  have := hold a ha
  omega

/-- An endpoint estimate with an arbitrary observed recorded prefix. -/
def PrefixEstimate (init : Cfg L K) (P Q : Cfg L K → Prop)
    (N : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ s (A : Set ((k : Finset.Iic s) → Draw L K)),
    (∀ a ∈ A, P (prefixCfg init s a)) →
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
      ¬ Q (trace init ω (s + N))} ≤
        ε * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}

theorem prefix_estimate_trans (init : Cfg L K) (P Q R : Cfg L K → Prop)
    (N M : ℕ) (ε δ : ℝ≥0∞)
    (hfirst : PrefixEstimate init P Q N ε)
    (hsecond : PrefixEstimate init Q R M δ) :
    PrefixEstimate init P R (N + M) (ε + δ) := by
  intro s A hA
  let t := s + N
  let B : Set ((k : Finset.Iic t) → Draw L K) :=
    {a | restrictPrefix (by dsimp [t]; omega : s ≤ t) a ∈ A ∧
      Q (prefixCfg init t a)}
  have hmass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ B} ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
    measure_mono fun ω hω => hω.1
  have htail := (hsecond t B (fun a ha => ha.2)).trans
    (mul_le_mul_left' hmass δ)
  have hsub :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ R (trace init ω (s + (N + M)))} ⊆
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ Q (trace init ω (s + N))} ∪
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ B ∧
        ¬ R (trace init ω (t + M))} := by
    rintro ω ⟨ha, hr⟩
    by_cases hq : Q (trace init ω (s + N))
    · exact Or.inr ⟨⟨ha, hq⟩, by simpa only [t, Nat.add_assoc] using hr⟩
    · exact Or.inl ⟨ha, hq⟩
  calc
    _ ≤ law init _ := measure_mono hsub
    _ ≤ law init _ + law init _ := measure_union_le _ _
    _ ≤ ε * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} +
        δ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
      add_le_add (hfirst s A hA) htail
    _ = _ := by rw [add_mul]

theorem prefix_estimate_mono (init : Cfg L K) (P P' Q Q' : Cfg L K → Prop)
    (N : ℕ) (ε δ : ℝ≥0∞) (h : PrefixEstimate init P Q N ε)
    (hP : ∀ c, P' c → P c) (hQ : ∀ c, Q c → Q' c) (hεδ : ε ≤ δ) :
    PrefixEstimate init P' Q' N δ := by
  intro s A hA
  apply (measure_mono ?_).trans
    ((h s A (fun a ha => hP _ (hA a ha))).trans (mul_le_mul_right' hεδ _))
  rintro ω ⟨ha, hbad⟩
  exact ⟨ha, fun hgood => hbad (hQ _ hgood)⟩

def StableOrAll (init : Cfg L K) (p : ℕ) (c : Cfg L K) : Prop :=
  c ∈ StableDone L K init ∨ ∀ a ∈ c, p ≤ a.phase.val

def StableOrSeed (init : Cfg L K) (p : ℕ) (c : Cfg L K) : Prop :=
  c ∈ StableDone L K init ∨ ∃ a ∈ c, p ≤ a.phase.val

theorem prefix_threshold (init : Cfg L K) {n : ℕ}
    (hn : 2 ≤ n) (hcard : init.card = n) (p : ℕ) (hp : 1 ≤ p) :
    PrefixEstimate init (StableOrSeed init p) (StableOrAll init p)
      (activationHorizon n) (ENNReal.ofReal (2 / (n : ℝ) ^ 5)) := by
  intro s A hA
  let B : Set ((k : Finset.Iic s) → Draw L K) :=
    {a | a ∈ A ∧ ∃ b ∈ prefixCfg init s a, p ≤ b.phase.val}
  have hb : ∀ a ∈ B, (prefixCfg init s a).card = n ∧
      ∃ b ∈ prefixCfg init s a, p ≤ b.phase.val :=
    fun a ha => ⟨(prefix_card init s a).trans hcard, ha.2⟩
  have ht := (PhaseTwoThresholds.threshold_spread_from_prefix init hn p hp
    s (activationHorizon n) B hb).trans
      (mul_le_mul_right' (PhaseTwoThresholds.activation_thresholdBudget_le hn) _)
  have hmass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ B} ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
    measure_mono fun ω hω => hω.1
  apply (measure_mono ?_).trans (ht.trans (mul_le_mul_left' hmass _))
  rintro ω ⟨ha, hbad⟩
  have hnotstable : trace init ω s ∉ StableDone L K init := by
    intro hs
    exact hbad (Or.inl (stable_persists init ω s _ (Nat.le_add_right _ _) hs))
  have hseed : ∃ b ∈ trace init ω s, p ≤ b.phase.val :=
    (hA _ ha).resolve_left hnotstable
  exact ⟨⟨ha, hseed⟩, fun hall => hbad (Or.inr hall)⟩

theorem prefix_timed {n : ℕ} (init : InputCfg n) (hinit : validInitial init)
    (hn : 2 ≤ n) (hcard : init.card = n) (p : ℕ) (hp : TimedPhase p) :
    PrefixEstimate init (StableOrAll init p) (StableOrSeed init (p + 1))
      (PhaseOneTimer.timerHorizon n) (ENNReal.ofReal (1 / (n : ℝ) ^ 5)) := by
  intro s A hA
  let B : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {a | a ∈ A ∧ PurePhase p (prefixCfg init s a)}
  have ht := timed_tail_calibrated init hinit p hp hn s B
    (fun a ha => ⟨(prefix_card init s a).trans hcard, ha.2⟩)
  have hmass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ B} ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A} :=
    measure_mono fun ω hω => hω.1
  apply (measure_mono ?_).trans (ht.trans (mul_le_mul_left' hmass _))
  rintro ω ⟨ha, hbad⟩
  have hnotstable : trace init ω s ∉ StableDone _ _ init := by
    intro hs
    exact hbad (Or.inl (stable_persists init ω s _ (Nat.le_add_right _ _) hs))
  have hlo := (hA _ ha).resolve_left hnotstable
  have hhi : ∀ a ∈ trace init ω s, a.phase.val ≤ p := by
    intro a ha'
    by_contra h
    have hseed : ∃ b ∈ trace init ω s, p + 1 ≤ b.phase.val :=
      ⟨a, ha', by omega⟩
    exact hbad (Or.inr (seed_persists init ω (p + 1) s _ (by omega)
      (Nat.le_add_right _ _) hseed))
  refine ⟨⟨ha, fun a ha' => le_antisymm (hhi a ha') (hlo a ha')⟩, ?_⟩
  rintro ⟨a, ha', hphase⟩
  exact hbad (Or.inr ⟨a, ha', by omega⟩)

theorem prefix_backup {n : ℕ} (init : InputCfg n) (hinit : validInitial init)
    (hn : 2 ≤ n) (hcard : init.card = n)
    (hstrong : n ≤ 120 * gapMagnitude init) :
    PrefixEstimate init (StableOrSeed init 10)
      (fun c => c ∈ StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init)
      (StrongGapBackup.backupHorizon n)
      (ENNReal.ofReal (5 / (n : ℝ) ^ 3)) := by
  intro s A hA
  let B : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {a | a ∈ A ∧ ∃ b ∈ prefixCfg init s a, 10 ≤ b.phase.val}
  have hb : ∀ a ∈ B, StrongGapBackup.BackupSeed n (prefixCfg init s a) := by
    intro a ha
    refine ⟨(prefix_card init s a).trans hcard, ?_⟩
    obtain ⟨b, hb, hphase⟩ := ha.2
    exact ⟨b, hb, by have := b.phase.isLt; omega⟩
  have ht := StrongGapBackup.backup_seed_tail_from_prefix init hinit hn hstrong s B hb
  have hmass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ B} ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A} :=
    measure_mono fun ω hω => hω.1
  apply (measure_mono ?_).trans (ht.trans (mul_le_mul_left' hmass _))
  rintro ω ⟨ha, hbad⟩
  have hs : trace init ω s ∉ StableDone _ _ init := by
    intro h
    exact hbad (stable_persists init ω s _ (Nat.le_add_right _ _) h)
  exact ⟨⟨ha, (hA _ ha).resolve_left hs⟩, hbad⟩

/-- Disjoint observed-time fibres retain their masses. -/
theorem prefix_estimate_at_past_time (init : Cfg L K)
    (P Q : Cfg L K → Prop) (N : ℕ) (ε : ℝ≥0∞)
    (h : PrefixEstimate init P Q N ε)
    (τ : Ω L K → WithTop ℕ) (hτ : PhaseOneDrain.PairLogPastTime τ) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
      P (trace init ω s) ∧ ¬ Q (trace init ω (s + N))} ≤ ε := by
  classical
  let D : Set (Ω L K) :=
    {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
      P (trace init ω s) ∧ ¬ Q (trace init ω (s + N))}
  have hmeas : MeasurableSet D := by
    have heq : D = ⋃ s : ℕ, {ω | τ ω = (s : WithTop ℕ)} ∩
        ({ω | P (trace init ω s)} ∩ {ω | ¬ Q (trace init ω (s + N))}) := by
      ext ω
      simp only [D, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [heq]
    refine MeasurableSet.iUnion (fun s => ?_)
    have ht : MeasurableSet {ω | τ ω = (s : WithTop ℕ)} :=
      (pairLogFiltration L K).le s _ (hτ s)
    have hp : MeasurableSet {ω | P (trace init ω s)} :=
      (Set.to_countable {c : Cfg L K | P c}).measurableSet.preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
    have hq : MeasurableSet {ω | ¬ Q (trace init ω (s + N))} :=
      (Set.to_countable {c : Cfg L K | ¬ Q c}).measurableSet.preimage
        ((measurable_pi_apply (s + N)).comp (measurable_trace init))
    exact ht.inter (hp.inter hq)
  apply genuine_seed_splice (law init) τ D ε hmeas
    (fun s => (pairLogFiltration L K).le s _ (hτ s))
  · rintro ω ⟨s, hs, -, -⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hτs := hτ s
    rw [pairLogFiltration_eq_comap] at hτs
    obtain ⟨Aτ, -, hAτ⟩ := hτs
    let A : Set ((k : Finset.Iic s) → Draw L K) :=
      {a | a ∈ Aτ ∧ P (prefixCfg init s a)}
    have hmem (ω : Ω L K) :
        frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ Aτ ↔
          τ ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ => Draw L K) s) ⁻¹' Aτ ↔
        ω ∈ {ω | τ ω = (s : WithTop ℕ)}
      rw [hAτ]
    have ht := h s A (fun a ha => ha.2)
    apply (measure_mono ?_).trans
      (ht.trans (mul_le_mul_left'
        (measure_mono (show
          {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} ⊆
            {ω | τ ω = (s : WithTop ℕ)} from
          fun ω hω => (hmem ω).1 hω.1)) ε))
    rintro ω ⟨⟨r, hr, hp, hq⟩, hs⟩
    have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
    subst r
    exact ⟨⟨(hmem ω).2 hs, hp⟩, hq⟩

end Ripple.PopulationProtocol.ExactMajority.StrongContinuationComposition

end
