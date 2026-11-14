-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingSplice.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6OriginalLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedSplice

/-!
# Original-law prefix selection at genuine stopping times

All parameters are selected from one observed prefix.  No union factor is
charged for observed counts, classes, or start times.  Continuations use the
ordinary recorded-future law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingSplice

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping
open AveragingRecordedExpectation AveragingRecordedSplice

variable {L K n : ℕ}

abbrev RecordedPrefix (L K s : ℕ) :=
  (i : Finset.Iic s) → Draw L K

def selectedFailure (s : ℕ) (A : Set (RecordedPrefix L K s))
    (E : RecordedPrefix L K s → Set (Ω L K)) : Set (Ω L K) :=
  {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
    ω ∈ E (frestrictLe (π := fun _ : ℕ => Draw L K) s ω)}

theorem selectedFailure_eq_union (s : ℕ) (A : Set (RecordedPrefix L K s))
    (E : RecordedPrefix L K s → Set (Ω L K)) :
    selectedFailure s A E =
      ⋃ p : A, {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω = p.1 ∧
        ω ∈ E p.1} := by
  ext ω
  constructor
  · rintro ⟨hA, hE⟩
    exact Set.mem_iUnion.mpr ⟨⟨_, hA⟩, rfl, hE⟩
  · intro h
    obtain ⟨p, hp, hE⟩ := Set.mem_iUnion.mp h
    change frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧ _
    rw [hp]
    exact ⟨p.2, hE⟩

/-- The choice of all parameters is made from one observed prefix. -/
theorem law_prefix_selected_bound (init : Cfg L K) (s : ℕ)
    (A : Set (RecordedPrefix L K s))
    (E : RecordedPrefix L K s → Set (Ω L K))
    (hE : ∀ p, MeasurableSet (E p)) (ε : ℝ≥0∞)
    (hlocal : ∀ p ∈ A, recordedFuture init s p (E p) ≤ ε) :
    law init (selectedFailure s A E) ≤
      ε * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  classical
  let P : A → Set (Ω L K) := fun p =>
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω = p.1}
  let F : A → Set (Ω L K) := fun p =>
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω = p.1 ∧ ω ∈ E p.1}
  have hbound (p : A) : law init (F p) ≤ ε * law init (P p) := by
    have h := law_prefix_joint_bound init s {p.1} (E p.1) (hE p.1) ε
      (by intro q hq; have hqp : q = p.1 := hq; subst q; exact hlocal p.1 p.2)
    simpa only [F, P, Set.mem_singleton_iff] using h
  have hmeas (p : A) : MeasurableSet (P p) :=
    ((Set.to_countable ({p.1} : Set (RecordedPrefix L K s))).measurableSet).preimage
      (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) s)
  have hdisj : Pairwise (fun p q : A => Disjoint (P p) (P q)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro ω hp hq
    exact hpq (Subtype.ext (hp.symm.trans hq))
  have hunion :
      (⋃ p : A, P p) =
        {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hω
      change frestrictLe (π := fun _ : ℕ => Draw L K) s ω = p.1 at hp
      change frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A
      rw [hp]
      exact p.2
    · intro hω
      exact Set.mem_iUnion.mpr ⟨⟨_, hω⟩, rfl⟩
  have hmass :
      (∑' p : A, law init (P p)) =
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
    rw [← measure_iUnion hdisj hmeas, hunion]
  rw [selectedFailure_eq_union]
  change law init (⋃ p : A, F p) ≤ _
  calc
    law init (⋃ p : A, F p) ≤ ∑' p : A, law init (F p) := measure_iUnion_le _
    _ ≤ ∑' p : A, ε * law init (P p) := ENNReal.tsum_le_tsum hbound
    _ = ε * ∑' p : A, law init (P p) := by rw [ENNReal.tsum_mul_left]
    _ = _ := by rw [hmass]

/-- Splicing at a genuine stopping time, with every other parameter selected
from the same observed prefix. No union over parameter values is charged. -/
theorem law_stopping_selected_bound (init : Cfg L K)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ)
    (A : (s : ℕ) → Set (RecordedPrefix L K s))
    (E : (s : ℕ) → RecordedPrefix L K s → Set (Ω L K))
    (hE : ∀ s p, MeasurableSet (E s p)) (ε : ℝ≥0∞)
    (hlocal : ∀ s p, p ∈ A s → recordedFuture init s p (E s p) ≤ ε) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      ω ∈ selectedFailure s (A s) (E s)} ≤ ε := by
  let B : Set (Ω L K) :=
    {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      ω ∈ selectedFailure s (A s) (E s)}
  apply PhaseThreeClockProducer.splice_of_local (law init) σ B ε
    (fun s => (pairLogFiltration L K).le s _ (hσ s))
  · rintro ω ⟨s, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hσs := hσ s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨D, hD, hEq⟩ := hσs
    have hmem (ω : Ω L K) :
        frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ D ↔
          σ ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ => Draw L K) s) ⁻¹' D ↔
        ω ∈ {ω | σ ω = (s : WithTop ℕ)}
      rw [hEq]
    have heq :
        B ∩ {ω | σ ω = (s : WithTop ℕ)} =
          selectedFailure s (A s ∩ D) (E s) := by
      ext ω
      constructor
      · rintro ⟨⟨r, hr, hA, hEω⟩, hs⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        exact ⟨⟨hA, (hmem ω).mpr hs⟩, hEω⟩
      · rintro ⟨⟨hA, hDω⟩, hEω⟩
        have hs := (hmem ω).mp hDω
        exact ⟨⟨s, hs, hA, hEω⟩, hs⟩
    rw [heq]
    have hb := law_prefix_selected_bound init s (A s ∩ D) (E s)
      (hE s) ε (fun p hp => hlocal s p hp.1)
    calc
      law init (selectedFailure s (A s ∩ D) (E s)) ≤
          ε * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A s ∩ D} := hb
      _ ≤ ε * law init {ω | σ ω = (s : WithTop ℕ)} := by
        gcongr
        exact fun hω => (hmem _).mp hω.2

end Ripple.PopulationProtocol.ExactMajority.LateSamplingSplice

end
