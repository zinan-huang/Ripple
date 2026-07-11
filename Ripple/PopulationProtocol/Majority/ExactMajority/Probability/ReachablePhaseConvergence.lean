import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak

/-!
# Reachable-scoped weak phase convergence

`PhaseConvergenceW` is a global interface: it asks for the phase tail from every
configuration satisfying `Pre`.  That is too strong for seam no-overshoot facts whose
honest statement is restricted to the deterministic reachability closure of the actual
start.  This file provides the reachable-scoped analogue and the same union-bound
composition theorem, with the only extra proof obligation being that the starting
configuration is reachable from the fixed root.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- A weak phase-convergence statement scoped to configs reachable from `init`. -/
structure PhaseConvergenceWR {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (init : Config Λ) where
  Pre : Config Λ → Prop
  Post : Config Λ → Prop
  t : ℕ
  ε : ℝ≥0
  convergence : ∀ x, P.Reachable init x → Pre x →
    (P.transitionKernel ^ t) x {y | ¬ Post y} ≤ (ε : ℝ≥0∞)

namespace PhaseConvergenceWR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable (P : Protocol Λ) (init : Config Λ)

/-- Lift a global weak phase into a reachable-scoped phase. -/
def ofW (phase : PhaseConvergenceW P.transitionKernel) :
    PhaseConvergenceWR P init where
  Pre := phase.Pre
  Post := phase.Post
  t := phase.t
  ε := phase.ε
  convergence := fun x _ hx => phase.convergence x hx

end PhaseConvergenceWR

private theorem kernel_pow_apply_le_one_reachable
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (t : ℕ) (x : Config Λ) (S : Set (Config Λ)) :
    (P.transitionKernel ^ t) x S ≤ 1 := by
  have h_univ : (P.transitionKernel ^ t) x Set.univ = 1 := by
    induction t with
    | zero =>
      simp only [pow_zero]
      change Kernel.id x Set.univ = 1
      rw [Kernel.id_apply]
      simp
    | succ t ih =>
      have h_meas_univ : MeasurableSet (Set.univ : Set (Config Λ)) := MeasurableSet.univ
      rw [Kernel.pow_succ_apply_eq_lintegral P.transitionKernel t x h_meas_univ]
      calc ∫⁻ y, P.transitionKernel y Set.univ ∂((P.transitionKernel ^ t) x)
          = ∫⁻ _ : Config Λ, (1 : ℝ≥0∞) ∂((P.transitionKernel ^ t) x) := by
            apply lintegral_congr_ae
            filter_upwards with y
            haveI : IsProbabilityMeasure (P.transitionKernel y) :=
              (inferInstance : IsMarkovKernel P.transitionKernel).isProbabilityMeasure y
            simpa using (measure_univ (μ := P.transitionKernel y))
        _ = 1 := by
            rw [lintegral_const, ih, one_mul]
  calc (P.transitionKernel ^ t) x S
      ≤ (P.transitionKernel ^ t) x Set.univ := measure_mono (Set.subset_univ S)
    _ = 1 := h_univ

private theorem ennreal_coe_nnreal_sum_reachable {ι : Type*} [Fintype ι] (f : ι → ℝ≥0) :
    ((∑ i, f i : ℝ≥0) : ℝ≥0∞) = ∑ i, (f i : ℝ≥0∞) := by
  classical
  exact_mod_cast (Finset.sum_congr rfl (fun _ _ => rfl) :
    ((∑ i, f i : ℝ≥0) : ℝ≥0) = ∑ i, f i)

/-- Two-phase reachable-scoped composition. -/
theorem composeWR_two_phases
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) {init : Config Λ}
    (phase1 phase2 : PhaseConvergenceWR P init)
    (h_chain : ∀ x, P.Reachable init x → phase1.Post x → phase2.Pre x)
    (x₀ : Config Λ) (hreach₀ : P.Reachable init x₀) (hx₀ : phase1.Pre x₀) :
    (P.transitionKernel ^ (phase1.t + phase2.t)) x₀ {y | ¬ phase2.Post y}
      ≤ (phase1.ε + phase2.ε : ℝ≥0∞) := by
  have h_decomp : (P.transitionKernel ^ (phase1.t + phase2.t)) x₀ {y | ¬phase2.Post y} =
      ∫⁻ y, (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
        ∂((P.transitionKernel ^ phase1.t) x₀) := by
    exact Kernel.pow_add_apply_eq_lintegral P.transitionKernel phase1.t phase2.t x₀
      (DiscreteMeasurableSpace.forall_measurableSet (α := Config Λ) _)
  rw [h_decomp]
  have h_meas : MeasurableSet {y | phase1.Post y} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have h_split : ∫⁻ y, (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
        ∂((P.transitionKernel ^ phase1.t) x₀) =
      (∫⁻ y in {y | phase1.Post y},
        (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
          ∂((P.transitionKernel ^ phase1.t) x₀)) +
      (∫⁻ y in {y | ¬phase1.Post y},
        (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
          ∂((P.transitionKernel ^ phase1.t) x₀)) := by
    have h_compl : {y | ¬phase1.Post y} = {y | phase1.Post y}ᶜ := Set.ext fun x => by simp
    rw [h_compl, ← lintegral_add_compl _ h_meas]
  rw [h_split]
  have hreach_ae : ∀ᵐ y ∂((P.transitionKernel ^ phase1.t) x₀), P.Reachable init y := by
    have hxy : ∀ᵐ y ∂((P.transitionKernel ^ phase1.t) x₀), P.Reachable x₀ y :=
      Protocol.ae_reachable_transitionKernel_pow P x₀ phase1.t
    filter_upwards [hxy] with y hy
    exact Relation.ReflTransGen.trans hreach₀ hy
  have h_bound1 : ∫⁻ y in {y | phase1.Post y},
      (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
        ∂((P.transitionKernel ^ phase1.t) x₀) ≤ phase2.ε := by
    calc ∫⁻ y in {y | phase1.Post y},
        (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
          ∂((P.transitionKernel ^ phase1.t) x₀)
      _ ≤ ∫⁻ _ in {y | phase1.Post y}, (phase2.ε : ℝ≥0∞)
          ∂((P.transitionKernel ^ phase1.t) x₀) := by
          apply lintegral_mono_ae
          rw [ae_restrict_iff' h_meas]
          filter_upwards [hreach_ae] with y hyreach hy
          exact phase2.convergence y hyreach (h_chain y hyreach hy)
      _ ≤ (phase2.ε : ℝ≥0∞) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          calc (phase2.ε : ℝ≥0∞) * ((P.transitionKernel ^ phase1.t) x₀ {y | phase1.Post y})
              ≤ (phase2.ε : ℝ≥0∞) * 1 := by
                gcongr
                exact kernel_pow_apply_le_one_reachable P phase1.t x₀ {y | phase1.Post y}
            _ = _ := mul_one _
  have h_bound2 : ∫⁻ y in {y | ¬phase1.Post y},
      (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
        ∂((P.transitionKernel ^ phase1.t) x₀) ≤ phase1.ε := by
    calc ∫⁻ y in {y | ¬phase1.Post y},
        (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
          ∂((P.transitionKernel ^ phase1.t) x₀)
      _ ≤ ∫⁻ _ in {y | ¬phase1.Post y}, 1 ∂((P.transitionKernel ^ phase1.t) x₀) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem h_meas.compl] with y _
          exact kernel_pow_apply_le_one_reachable P phase2.t y {y' | ¬phase2.Post y'}
      _ = ((P.transitionKernel ^ phase1.t) x₀ {y | ¬phase1.Post y}) := by
          rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
      _ ≤ (phase1.ε : ℝ≥0∞) := phase1.convergence x₀ hreach₀ hx₀
  have h_add : (phase2.ε : ℝ≥0∞) + (phase1.ε : ℝ≥0∞) =
      (phase1.ε + phase2.ε : ℝ≥0∞) := by
    push_cast
    exact add_comm _ _
  calc (∫⁻ y in {y | phase1.Post y},
        (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
          ∂((P.transitionKernel ^ phase1.t) x₀)) +
       (∫⁻ y in {y | ¬phase1.Post y},
        (P.transitionKernel ^ phase2.t) y {y' | ¬phase2.Post y'}
          ∂((P.transitionKernel ^ phase1.t) x₀))
    _ ≤ (phase2.ε : ℝ≥0∞) + (phase1.ε : ℝ≥0∞) := add_le_add h_bound1 h_bound2
    _ = (phase1.ε + phase2.ε : ℝ≥0∞) := h_add

/-- `n`-phase reachable-scoped composition. -/
theorem composeWR_n_phases
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) {init : Config Λ}
    {m : ℕ} (hm : m > 0)
    (phases : Fin m → PhaseConvergenceWR P init)
    (h_chain : ∀ (i : Fin m) (hi : i.val + 1 < m),
        ∀ x, P.Reachable init x →
          (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (x₀ : Config Λ) (hreach₀ : P.Reachable init x₀) (hx₀ : (phases ⟨0, hm⟩).Pre x₀) :
    (P.transitionKernel ^ (∑ i : Fin m, (phases i).t)) x₀
        {y | ¬(phases ⟨m - 1, by omega⟩).Post y}
      ≤ (∑ i : Fin m, ((phases i).ε : ℝ≥0∞)) := by
  revert hm phases h_chain x₀ hreach₀ hx₀
  induction m with
  | zero =>
      intro hm phases h_chain x₀ hreach₀ hx₀
      omega
  | succ m' ih =>
    intro hm phases h_chain x₀ hreach₀ hx₀
    by_cases hm'_pos : 0 < m'
    · let prefix_phases : Fin m' → PhaseConvergenceWR P init := fun i => phases i.castSucc
      let prefix_last : Fin m' := ⟨m' - 1, by omega⟩
      let last : Fin (Nat.succ m') := ⟨m', Nat.lt_succ_self m'⟩
      have h_prefix_chain :
          ∀ (i : Fin m') (hi : i.val + 1 < m'),
            ∀ x, P.Reachable init x → (prefix_phases i).Post x →
              (prefix_phases ⟨i.val + 1, hi⟩).Pre x := by
        intro i hi x hreach hx
        have hi' : (i.castSucc : Fin (Nat.succ m')).val + 1 < Nat.succ m' :=
          Nat.lt_trans hi (Nat.lt_succ_self m')
        have h := h_chain i.castSucc hi' x hreach (by simpa [prefix_phases] using hx)
        have hidx :
            (⟨(i.castSucc : Fin (Nat.succ m')).val + 1, hi'⟩ :
                Fin (Nat.succ m')) =
              Fin.castSucc (⟨i.val + 1, hi⟩ : Fin m') := by
          ext
          rfl
        simpa [prefix_phases, hidx] using h
      let prefix_conv : PhaseConvergenceWR P init := {
        Pre := (prefix_phases ⟨0, hm'_pos⟩).Pre
        Post := (prefix_phases prefix_last).Post
        t := ∑ i : Fin m', (prefix_phases i).t
        ε := ∑ i : Fin m', (prefix_phases i).ε
        convergence := by
          intro x hreach hx
          have h_ih := ih hm'_pos prefix_phases h_prefix_chain x hreach hx
          have hε :
              ((∑ i : Fin m', (prefix_phases i).ε : ℝ≥0) : ℝ≥0∞) =
                ∑ i : Fin m', ((prefix_phases i).ε : ℝ≥0∞) :=
            ennreal_coe_nnreal_sum_reachable (fun i : Fin m' => (prefix_phases i).ε)
          rw [hε]
          simpa [prefix_last] using h_ih
      }
      have hx_prefix : prefix_conv.Pre x₀ := by
        have hidx : (⟨0, hm⟩ : Fin (Nat.succ m')) =
            Fin.castSucc (⟨0, hm'_pos⟩ : Fin m') := by
          ext
          rfl
        change (phases (Fin.castSucc (⟨0, hm'_pos⟩ : Fin m'))).Pre x₀
        rw [← hidx]
        exact hx₀
      have h_last_chain :
          ∀ x, P.Reachable init x → prefix_conv.Post x → (phases last).Pre x := by
        intro x hreach hx
        let prev : Fin (Nat.succ m') := Fin.castSucc prefix_last
        have hprev_next : prev.val + 1 < Nat.succ m' := by
          simp [prev, prefix_last]
          omega
        have hprev_post : (phases prev).Post x := by
          change (phases (Fin.castSucc prefix_last)).Post x
          simpa [prefix_conv, prefix_phases, prev] using hx
        have h := h_chain prev hprev_next x hreach hprev_post
        have hidx : (⟨prev.val + 1, hprev_next⟩ : Fin (Nat.succ m')) = last := by
          ext
          simp [prev, prefix_last, last]
          omega
        simpa [hidx] using h
      have h_compose :=
        composeWR_two_phases P prefix_conv (phases last) h_last_chain x₀ hreach₀ hx_prefix
      have ht_split :
          (∑ i : Fin (Nat.succ m'), (phases i).t) =
            prefix_conv.t + (phases last).t := by
        simpa [prefix_conv, prefix_phases, last] using
          (Fin.sum_univ_castSucc (fun i : Fin (Nat.succ m') => (phases i).t))
      have he_split :
          (∑ i : Fin (Nat.succ m'), ((phases i).ε : ℝ≥0∞)) =
            (prefix_conv.ε : ℝ≥0∞) + ((phases last).ε : ℝ≥0∞) := by
        have hprefix_eps :
            ((∑ i : Fin m', (prefix_phases i).ε : ℝ≥0) : ℝ≥0∞) =
              ∑ i : Fin m', ((prefix_phases i).ε : ℝ≥0∞) :=
          ennreal_coe_nnreal_sum_reachable (fun i : Fin m' => (prefix_phases i).ε)
        simpa [prefix_conv, prefix_phases, last, hprefix_eps] using
          (Fin.sum_univ_castSucc
            (fun i : Fin (Nat.succ m') => ((phases i).ε : ℝ≥0∞)))
      have hpost :
          (phases ⟨Nat.succ m' - 1, by omega⟩).Post = (phases last).Post := by
        congr 1
      have h_compose' :
          (P.transitionKernel ^ (prefix_conv.t + (phases last).t)) x₀
              {y | ¬(phases last).Post y}
            ≤ (prefix_conv.ε : ℝ≥0∞) + ((phases last).ε : ℝ≥0∞) := by
        have hε_add :
            (prefix_conv.ε + (phases last).ε : ℝ≥0∞) =
              (prefix_conv.ε : ℝ≥0∞) + ((phases last).ε : ℝ≥0∞) := by
          push_cast
          rfl
        simpa [hε_add] using h_compose
      simpa [ht_split, he_split, hpost] using h_compose'
    · have hm1 : m' = 0 := by omega
      subst m'
      simpa using (phases ⟨0, hm⟩).convergence x₀ hreach₀ hx₀

#print axioms PhaseConvergenceWR.ofW
#print axioms composeWR_two_phases
#print axioms composeWR_n_phases

end ExactMajority
