/-
  First-wrong-step decomposition bound for mass-action CRN trajectories.

  The bound P(firstWrongAt k) ≤ detStepError(k) holds WITHOUT requiring
  EnabledAt — it's a structural consequence of the Ionescu-Tulcea construction.
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.UniformRaceBound

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-! ### Deterministic prefix state -/

open Classical in
noncomputable def deterministicPrefixState (z0 : State S) (schedule : Nat → N.I) :
    Nat → State S
  | 0 => z0
  | k + 1 => stateStep N (deterministicPrefixState z0 schedule k) (some (schedule k))

/-! ### Good prefix events -/

def goodPrefix (schedule : Nat → N.I) (m : Nat) :
    Set ((n : Nat) → Option N.I) :=
  {ω | ∀ j, j < m → ω (j + 1) = some (schedule j)}

def firstWrongAt (schedule : Nat → N.I) (k : Nat) :
    Set ((n : Nat) → Option N.I) :=
  goodPrefix N schedule k ∩ {ω | ω (k + 1) ≠ some (schedule k)}

/-! ### Basic properties -/

theorem goodPrefix_zero (schedule : Nat → N.I) :
    goodPrefix N schedule 0 = Set.univ := by
  ext ω; simp [goodPrefix]

theorem goodPrefix_succ (schedule : Nat → N.I) (m : Nat) :
    goodPrefix N schedule (m + 1) =
    goodPrefix N schedule m ∩ {ω | ω (m + 1) = some (schedule m)} := by
  ext ω
  simp only [goodPrefix, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h m (Nat.lt_succ_self m)⟩
  · intro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact h1 j hlt
    · exact h2

theorem goodPrefix_complement_eq_union (schedule : Nat → N.I) (n : Nat) :
    (goodPrefix N schedule n)ᶜ =
    ⋃ k : Fin n, {ω | ω (k.val + 1) ≠ some (schedule k.val)} := by
  ext ω
  simp only [Set.mem_compl_iff, goodPrefix, Set.mem_setOf_eq, Set.mem_iUnion, not_forall]
  constructor
  · intro ⟨j, hj, hne⟩; exact ⟨⟨j, hj⟩, hne⟩
  · intro ⟨⟨j, hj⟩, hne⟩; exact ⟨j, hj, hne⟩

theorem measurableSet_goodPrefix (schedule : Nat → N.I) (m : Nat) :
    MeasurableSet (goodPrefix N schedule m) := by
  induction m with
  | zero => rw [goodPrefix_zero]; exact MeasurableSet.univ
  | succ k ih =>
    rw [goodPrefix_succ]
    exact ih.inter (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)

theorem complement_goodPrefix_subset_union_firstWrongAt
    (schedule : Nat → N.I) (n : Nat) :
    (goodPrefix N schedule n)ᶜ ⊆ ⋃ k : Fin n, firstWrongAt N schedule k := by
  intro ω hω
  simp only [Set.mem_compl_iff, goodPrefix, Set.mem_setOf_eq, not_forall] at hω
  obtain ⟨j, hj, hne⟩ := hω
  have hEx : ∃ m, m < n ∧ ω (m + 1) ≠ some (schedule m) := ⟨j, hj, hne⟩
  classical
  let m := Nat.find hEx
  have hm_spec := Nat.find_spec hEx
  have hm_min := fun i (hi : i < m) => Nat.find_min hEx hi
  simp only [Set.mem_iUnion]
  refine ⟨⟨m, hm_spec.1⟩, ?_, hm_spec.2⟩
  intro i hi
  by_contra h_ne
  exact hm_min i hi ⟨Nat.lt_trans hi hm_spec.1, h_ne⟩

/-! ### Deterministic path equality -/

theorem prefixToState_eq_deterministicPrefixState
    (z0 : State S) (schedule : Nat → N.I) :
    ∀ (k : Nat) (p : (i : Finset.Iic k) → Option N.I),
    (∀ (j : Nat) (hj : j < k),
      p ⟨j + 1, Finset.mem_Iic.mpr hj⟩ = some (schedule j)) →
    prefixToState N z0 k p = deterministicPrefixState N z0 schedule k := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro p hGood
    show stateStep N
      (prefixToState N z0 n (fun k => p ⟨k.val,
        Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ n))⟩))
      (p ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      stateStep N (deterministicPrefixState N z0 schedule n) (some (schedule n))
    congr 1
    · apply ih
      intro j hj
      have := hGood j (Nat.lt_succ_of_lt hj)
      convert this using 2
    · exact hGood n (Nat.lt_succ_self n)

/-! ### The first-wrong-step bound -/

section MainBound

variable (hPos : N.hasPositiveRates) (z0 : State S)

noncomputable def detStepError (schedule : Nat → N.I) (k : Nat) : ENNReal :=
  (massActionPMF N hPos (deterministicPrefixState N z0 schedule k)).toMeasure
    {some (schedule k)}ᶜ

set_option maxHeartbeats 8000000 in
theorem rawLaw_firstWrongAt_le
    (schedule : Nat → N.I) (k : Nat) :
    (rawLaw N hPos z0) (firstWrongAt N schedule k) ≤
      detStepError N hPos z0 schedule k := by
  set κ := fun n => stepKernel N hPos z0 n with κ_def
  set x₀ : (j : Finset.Iic 0) → Option N.I := fun _ => none with x₀_def
  -- Projected set in Iic(k+1) space
  let A : Set ((i : Finset.Iic (k + 1)) → Option N.I) :=
    {p | (∀ (j : Nat) (hj : j < k),
           p ⟨j + 1, Finset.mem_Iic.mpr (le_trans hj (Nat.le_succ k))⟩ = some (schedule j))
       ∧ p ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ ≠ some (schedule k)}
  have hEq : firstWrongAt N schedule k = frestrictLe (k + 1) ⁻¹' A := by
    ext ω
    simp only [firstWrongAt, goodPrefix, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_preimage, A, frestrictLe_apply]
  have hA₁ : MeasurableSet
      ({p : (i : Finset.Iic (k + 1)) → Option N.I |
        ∀ (j : Nat) (hj : j < k),
          p ⟨j + 1, Finset.mem_Iic.mpr (le_trans hj (Nat.le_succ k))⟩ =
            some (schedule j)} : Set _) := by
    simp_rw [Set.setOf_forall]
    apply MeasurableSet.iInter; intro j
    apply MeasurableSet.iInter; intro hj
    exact measurableSet_eq_fun
      (measurable_pi_apply
        (show Finset.Iic (k + 1) from ⟨j + 1, Finset.mem_Iic.mpr (le_trans hj (Nat.le_succ k))⟩))
      measurable_const
  have hA₂ : MeasurableSet
      ({p : (i : Finset.Iic (k + 1)) → Option N.I |
        p ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ ≠ some (schedule k)} : Set _) :=
    MeasurableSet.compl (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
  have hA : MeasurableSet A := hA₁.inter hA₂
  rw [hEq, ← Measure.map_apply (measurable_frestrictLe _) hA]
  have hRawTraj : rawLaw N hPos z0 = Kernel.traj (X := fun _ => Option N.I) κ 0 x₀ := rfl
  rw [hRawTraj, Kernel.traj_map_frestrictLe_apply (X := fun _ => Option N.I)]
  rw [Kernel.partialTraj_succ_eq_comp (X := fun _ => Option N.I) (Nat.zero_le k)]
  rw [Kernel.comp_apply' _ _ _ hA]
  have hms : MeasurableSet ({some (schedule k)}ᶜ : Set (Option N.I)) := trivial
  -- Pointwise bound
  calc ∫⁻ p, Kernel.partialTraj (X := fun _ => Option N.I) κ k (k + 1) p A
        ∂(Kernel.partialTraj (X := fun _ => Option N.I) κ 0 k x₀)
      ≤ ∫⁻ _, detStepError N hPos z0 schedule k
        ∂(Kernel.partialTraj (X := fun _ => Option N.I) κ 0 k x₀) := by
        apply MeasureTheory.lintegral_mono; intro p
        classical
        by_cases hp : ∀ (j : Nat) (hj : j < k),
            p ⟨j + 1, Finset.mem_Iic.mpr hj⟩ = some (schedule j)
        · -- On goodPrefix: bound by marginal pushforward
          calc Kernel.partialTraj (X := fun _ => Option N.I) κ k (k + 1) p A
              ≤ Kernel.partialTraj (X := fun _ => Option N.I) κ k (k + 1) p
                  ((fun q => q ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩) ⁻¹'
                    {some (schedule k)}ᶜ) :=
                measure_mono (fun q hq => hq.2)
            _ = detStepError N hPos z0 schedule k := by
                rw [← Kernel.map_apply'
                      (Kernel.partialTraj (X := fun _ => Option N.I) κ k (k + 1))
                      (measurable_pi_apply _) p hms]
                rw [Kernel.map_partialTraj_succ_self (X := fun _ => Option N.I)]
                change (massActionPMF N hPos (prefixToState N z0 k p)).toMeasure
                  {some (schedule k)}ᶜ = _
                have hp' : ∀ (j : Nat) (hj : j < k),
                    p ⟨j + 1, Finset.mem_Iic.mpr hj⟩ = some (schedule j) := hp
                rw [prefixToState_eq_deterministicPrefixState N z0 schedule k p hp']
                rfl
        · -- Off goodPrefix: Dirac concentration gives 0
          let GP : Set (Finset.Iic k → Option N.I) :=
            {p' | ∀ (j : Nat) (hj : j < k),
              p' ⟨j + 1, Finset.mem_Iic.mpr hj⟩ = some (schedule j)}
          have hGP : MeasurableSet GP := by
            show MeasurableSet {p' : Finset.Iic k → Option N.I |
              ∀ (j : Nat) (hj : j < k),
                p' ⟨j + 1, Finset.mem_Iic.mpr hj⟩ = some (schedule j)}
            simp_rw [Set.setOf_forall]
            apply MeasurableSet.iInter; intro j
            apply MeasurableSet.iInter; intro hj
            exact measurableSet_eq_fun
              (measurable_pi_apply
                (show Finset.Iic k from ⟨j + 1, Finset.mem_Iic.mpr hj⟩))
              measurable_const
          have hp' : p ∉ GP := hp
          have h_map : (Kernel.partialTraj (X := fun _ => Option N.I)
              κ k (k + 1) p).map
              (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ k)) =
              Measure.dirac p := by
            rw [← Kernel.map_apply _
              (measurable_frestrictLe₂ (Nat.le_succ k)) p]
            rw [Kernel.partialTraj_succ_map_frestrictLe₂ (X := fun _ => Option N.I)]
            rw [Kernel.partialTraj_self (X := fun _ => Option N.I)]
            exact Kernel.id_apply p
          calc Kernel.partialTraj (X := fun _ => Option N.I) κ k (k + 1) p A
              ≤ (Kernel.partialTraj (X := fun _ => Option N.I) κ k (k + 1) p).map
                  (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ k)) GP := by
                rw [Measure.map_apply (measurable_frestrictLe₂ _) hGP]
                apply measure_mono
                intro q ⟨hq, _⟩ j hj
                simp only [frestrictLe₂_apply]
                exact hq j hj
            _ = Measure.dirac p GP := by rw [h_map]
            _ = 0 := by
                rw [Measure.dirac_apply' _ hGP]
                exact Set.indicator_of_notMem hp' 1
            _ ≤ detStepError N hPos z0 schedule k := zero_le
    _ = detStepError N hPos z0 schedule k := by
        rw [MeasureTheory.lintegral_const, measure_univ, mul_one]

theorem rawLaw_deterministic_bound
    (schedule : Nat → N.I) (n : Nat)
    (ε : ENNReal)
    (hBound : ∀ k : Fin n, detStepError N hPos z0 schedule k ≤ ε) :
    (rawLaw N hPos z0)
      (⋃ k : Fin n, {ω | ω (k.val + 1) ≠ some (schedule k.val)}) ≤ n * ε := by
  rw [← goodPrefix_complement_eq_union]
  calc (rawLaw N hPos z0) (goodPrefix N schedule n)ᶜ
      ≤ (rawLaw N hPos z0) (⋃ k : Fin n, firstWrongAt N schedule k) :=
        measure_mono (complement_goodPrefix_subset_union_firstWrongAt N schedule n)
    _ ≤ ∑' k : Fin n, (rawLaw N hPos z0) (firstWrongAt N schedule k) :=
        measure_iUnion_le _
    _ = ∑ k : Fin n, (rawLaw N hPos z0) (firstWrongAt N schedule k) :=
        tsum_fintype _
    _ ≤ ∑ _k : Fin n, ε := by
        apply Finset.sum_le_sum; intro k _
        calc (rawLaw N hPos z0) (firstWrongAt N schedule k)
            ≤ detStepError N hPos z0 schedule k :=
              rawLaw_firstWrongAt_le N hPos z0 schedule k
          _ ≤ ε := hBound k
    _ = n * ε := by simp [Finset.sum_const]

end MainBound

end Ripple.sCRNUniversality.Stochastic.MassAction
