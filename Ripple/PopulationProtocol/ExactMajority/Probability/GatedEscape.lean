import Ripple.PopulationProtocol.ExactMajority.Probability.GatedGeometricDrift

/-!
# GatedEscape — bounding the killed walk's ESCAPE MASS `(killK^t)(some x){none}`

The gated engine (`GatedGeometricDrift.lean`) bounds real-kernel tails BY the escape
mass (`gated_real_tail`: real tail ≤ `(killK^t)(some x){none}` + drift term), but
nothing bounds the escape mass itself.  This file supplies the generic bound: if every
gated state's one-step probability of LEAVING the gate is at most `η`, the escape mass
after `t` steps is at most `t·η`.

This is the `eB` residual's missing generic piece (the hour-escape
`(killK (markedK T θn) (taintedGate n) ^ (w·KK)) (some mc₀) {none}` of
`windowedFrontProfile_whp_packaged`): the tainted counter rises by at most one per step,
so on the gate (count ≤ threshold) the per-step breach probability is uniformly bounded,
and the escape mass is `horizon · per-step-breach`.

Note the one-step-lag convention of `killK`: a walker at `some x` with `x ∈ G` steps via
`K` into `some y` even when `y ∉ G`; the kill registers at the NEXT step.  The bound
`t·η` absorbs this lag.
-/

namespace Ripple.PopulationProtocol.ExactMajority

namespace GatedDrift

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

local instance instOptionMS' : MeasurableSpace (Option α) := ⊤
local instance instOptionDMS' : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

variable {K : Kernel α α} {G : Set α}

/-- For an ungated state `some y` (`y ∉ G`), the killed walk is at the cemetery from the
next step on: `(killK^t)(some y){none} = 1` for `1 ≤ t`. -/
theorem killed_none_of_ungated [IsMarkovKernel K] (y : α) (hy : y ∉ G) (t : ℕ)
    (ht : 1 ≤ t) :
    (killK K G ^ t) (some y) {(none : Option α)} = 1 := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, t = 1 + s := ⟨t - 1, by omega⟩
  have hdead : killK K G (some y) = Measure.dirac (none : Option α) := by
    unfold killK
    rw [Kernel.piecewise_apply, if_neg (fun h => hy ((some_mem_image_iff y).1 h)),
      Kernel.const_apply]
  rw [Kernel.pow_add_apply_eq_lintegral (killK K G) 1 s (some y)
      (DiscreteMeasurableSpace.forall_measurableSet _), pow_one, hdead,
    MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete), none_absorbing s,
    Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  simp

/-- **The escape-mass bound.**  If every gated state leaves the gate in one `K`-step with
probability at most `η` (`hesc`), then from a gated start the killed walk's cemetery mass
after `t` steps is at most `t·η`:

  `(killK^t)(some x₀){none} ≤ t·η`.

Induction on `t`; per step, the alive-and-gated mass pays at most `η` for stepping out of
`G`, the already-ungated mass was paid for at the step that produced it. -/
theorem killed_none_mass_le [IsMarkovKernel K] (η : ℝ≥0∞)
    (hesc : ∀ x ∈ G, K x Gᶜ ≤ η) (t : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (killK K G ^ t) (some x₀) {(none : Option α)} ≤ (t : ℝ≥0∞) * η := by
  classical
  induction t generalizing x₀ with
  | zero =>
      rw [pow_zero]
      have hid : (Kernel.id : Kernel (Option α) (Option α)) (some x₀)
          {(none : Option α)} = 0 := by
        rw [Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp
      calc ((1 : Kernel (Option α) (Option α))) (some x₀) {(none : Option α)}
          = 0 := hid
        _ ≤ ((0 : ℕ) : ℝ≥0∞) * η := zero_le'
  | succ t ih =>
      have hCK : (killK K G ^ (t + 1)) (some x₀) {(none : Option α)}
          = ∫⁻ o, (killK K G ^ t) o {(none : Option α)} ∂(killK K G (some x₀)) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK K G) 1 t (some x₀)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCK, killK_some_gated (K := K) (G := G) x₀ hx₀,
        MeasureTheory.lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
      -- ∫⁻ y, (killK^t)(some y){none} ∂(K x₀) split over G / Gᶜ.
      have hmeasG : MeasurableSet G := DiscreteMeasurableSpace.forall_measurableSet _
      rw [← lintegral_add_compl
        (fun y => (killK K G ^ t) (some y) {(none : Option α)}) hmeasG]
      have hbound1 : ∫⁻ y in G, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)
          ≤ (t : ℝ≥0∞) * η := by
        calc ∫⁻ y in G, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)
            ≤ ∫⁻ _ in G, (t : ℝ≥0∞) * η ∂(K x₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hmeasG] with y hy
              exact ih y hy
          _ = ((t : ℝ≥0∞) * η) * (K x₀) G := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ ≤ ((t : ℝ≥0∞) * η) * 1 := by
              gcongr
              calc (K x₀) G ≤ (K x₀) Set.univ := measure_mono (Set.subset_univ G)
                _ = 1 := measure_univ
          _ = (t : ℝ≥0∞) * η := mul_one _
      have hbound2 : ∫⁻ y in Gᶜ, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)
          ≤ η := by
        calc ∫⁻ y in Gᶜ, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)
            ≤ ∫⁻ _ in Gᶜ, (1 : ℝ≥0∞) ∂(K x₀) := by
              apply lintegral_mono_ae
              filter_upwards with y
              calc (killK K G ^ t) (some y) {(none : Option α)}
                  ≤ (killK K G ^ t) (some y) Set.univ := measure_mono (Set.subset_univ _)
                _ ≤ 1 := by
                    haveI : ∀ s : ℕ, IsMarkovKernel ((killK K G) ^ s) := by
                      intro s
                      induction s with
                      | zero =>
                          rw [pow_zero]
                          exact inferInstanceAs
                            (IsMarkovKernel (Kernel.id : Kernel (Option α) (Option α)))
                      | succ s ihs =>
                          haveI := ihs
                          rw [pow_succ]
                          exact inferInstanceAs
                            (IsMarkovKernel (((killK K G) ^ s) ∘ₖ (killK K G)))
                    haveI := this t
                    rw [measure_univ]
          _ = (K x₀) Gᶜ := by
              rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ ≤ η := hesc x₀ hx₀
      calc (∫⁻ y in G, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)) +
            (∫⁻ y in Gᶜ, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀))
          ≤ (t : ℝ≥0∞) * η + η := add_le_add hbound1 hbound2
        _ = ((t : ℝ≥0∞) + 1) * η := by ring
        _ = ((t + 1 : ℕ) : ℝ≥0∞) * η := by
            congr 1
            push_cast
            ring

/-- **Alive domination**: the killed walk's alive mass on a set is dominated by the real
walk's mass — killed alive trajectories are a subset of real trajectories.  The one-sided
companion of `real_le_killed`. -/
theorem killed_alive_le_real [IsMarkovKernel K] (A : Set α) (t : ℕ) (x₀ : α) :
    (killK K G ^ t) (some x₀) {o | ∃ y ∈ A, o = some y} ≤ (K ^ t) x₀ A := by
  classical
  induction t generalizing x₀ with
  | zero =>
      rw [pow_zero, pow_zero]
      have hl : (Kernel.id : Kernel (Option α) (Option α)) (some x₀)
            {o | ∃ y ∈ A, o = some y}
          = ({o | ∃ y ∈ A, o = some y} : Set (Option α)).indicator 1 (some x₀) := by
        rw [Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      have hr : (Kernel.id : Kernel α α) x₀ A = A.indicator 1 x₀ := by
        rw [Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [show ((1 : Kernel (Option α) (Option α))) = Kernel.id from rfl,
        show ((1 : Kernel α α)) = Kernel.id from rfl, hl, hr]
      by_cases hx : x₀ ∈ A
      · rw [Set.indicator_of_mem (show (some x₀) ∈ {o | ∃ y ∈ A, o = some y} from
            ⟨x₀, hx, rfl⟩), Set.indicator_of_mem hx]
        simp
      · rw [Set.indicator_of_notMem (show (some x₀) ∉ {o | ∃ y ∈ A, o = some y} from by
            rintro ⟨y, hy, h⟩
            exact hx ((Option.some.inj h) ▸ hy)),
          Set.indicator_of_notMem hx]
  | succ t ih =>
      have hCKk : (killK K G ^ (t + 1)) (some x₀) {o | ∃ y ∈ A, o = some y}
          = ∫⁻ o, (killK K G ^ t) o {o' | ∃ y ∈ A, o' = some y}
              ∂(killK K G (some x₀)) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK K G) 1 t (some x₀)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      have hCKr : (K ^ (t + 1)) x₀ A = ∫⁻ y, (K ^ t) y A ∂(K x₀) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral K 1 t x₀
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCKk, hCKr]
      by_cases hx : x₀ ∈ G
      · rw [killK_some_gated (K := K) (G := G) x₀ hx,
          MeasureTheory.lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
        exact lintegral_mono (fun y => ih y)
      · have hdead : killK K G (some x₀) = Measure.dirac (none : Option α) := by
          unfold killK
          rw [Kernel.piecewise_apply, if_neg (fun h => hx ((some_mem_image_iff x₀).1 h)),
            Kernel.const_apply]
        rw [hdead, MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete)]
        have hzero : (killK K G ^ t) (none : Option α) {o' | ∃ y ∈ A, o' = some y} = 0 := by
          rw [none_absorbing t,
            Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
          exact Set.indicator_of_notMem (by rintro ⟨y, _, h⟩; exact Option.some_ne_none y h.symm) _
        rw [hzero]
        exact zero_le'

/-- **The escape-mass PREFIX-UNION bound** (the run-long escape accounting).  If from
every gated state satisfying the side event `S`, the one-step probability of leaving the
gate is at most `q` (`hstep`), then the killed walk's cemetery mass after `M` steps is
bounded by the always-good budget `M·q` plus the REAL-kernel prefix failures of `S`:

  `(killK^M)(some x₀){none} ≤ M·q + ∑_{τ<M} (K^τ) x₀ Sᶜ`.

Escape at step `τ+1` requires the (real-trajectory) state at `τ` to be alive; it then
pays `q` if that state is in `S`, and is charged to the `(K^τ) x₀ Sᶜ` prefix-failure term
otherwise.  Instantiation: `S` = the §6 width event ∧ bulk-below ∧ side gates, with the
prefix failures supplied by the per-`τ` whp corollaries. -/
theorem kill_escape_le_prefix_union [IsMarkovKernel K] (S : Set α) (q : ℝ≥0∞)
    (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q)
    (M : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (killK K G ^ M) (some x₀) {(none : Option α)} ≤
      (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ τ) x₀ Sᶜ := by
  classical
  induction M generalizing x₀ with
  | zero =>
      rw [pow_zero]
      have hid : (Kernel.id : Kernel (Option α) (Option α)) (some x₀)
          {(none : Option α)} = 0 := by
        rw [Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp
      calc ((1 : Kernel (Option α) (Option α))) (some x₀) {(none : Option α)}
          = 0 := hid
        _ ≤ _ := zero_le'
  | succ M ih =>
      have hCK : (killK K G ^ (M + 1)) (some x₀) {(none : Option α)}
          = ∫⁻ o, (killK K G ^ M) o {(none : Option α)} ∂(killK K G (some x₀)) := by
        rw [show M + 1 = 1 + M from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK K G) 1 M (some x₀)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCK, killK_some_gated (K := K) (G := G) x₀ hx₀,
        MeasureTheory.lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
      have hmeasG : MeasurableSet G := DiscreteMeasurableSpace.forall_measurableSet _
      rw [← lintegral_add_compl
        (fun y => (killK K G ^ M) (some y) {(none : Option α)}) hmeasG]
      -- gated successors: IH pointwise, then push the prefix sum one step.
      have hbound1 : ∫⁻ y in G, (killK K G ^ M) (some y) {(none : Option α)} ∂(K x₀)
          ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ (τ + 1)) x₀ Sᶜ := by
        calc ∫⁻ y in G, (killK K G ^ M) (some y) {(none : Option α)} ∂(K x₀)
            ≤ ∫⁻ y in G, ((M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ τ) y Sᶜ)
                ∂(K x₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hmeasG] with y hy
              exact ih y hy
          _ ≤ ∫⁻ y, ((M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ τ) y Sᶜ)
                ∂(K x₀) := by
              exact MeasureTheory.setLIntegral_le_lintegral _ _
          _ = ∫⁻ y, (M : ℝ≥0∞) * q ∂(K x₀)
              + ∫⁻ y, (∑ τ ∈ Finset.range M, (K ^ τ) y Sᶜ) ∂(K x₀) := by
              rw [MeasureTheory.lintegral_add_left (by fun_prop)]
          _ ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ (τ + 1)) x₀ Sᶜ := by
              gcongr
              · rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
              · rw [MeasureTheory.lintegral_finset_sum _
                  (fun τ _ => by fun_prop)]
                refine Finset.sum_le_sum (fun τ _ => ?_)
                rw [show τ + 1 = 1 + τ from by ring,
                  Kernel.pow_add_apply_eq_lintegral K 1 τ x₀
                    (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      -- ungated successors: pay `q` (side event holds) or charge the `τ = 0` prefix term.
      have hbound2 : ∫⁻ y in Gᶜ, (killK K G ^ M) (some y) {(none : Option α)} ∂(K x₀)
          ≤ q + (K ^ 0) x₀ Sᶜ := by
        have hle1 : ∫⁻ y in Gᶜ, (killK K G ^ M) (some y) {(none : Option α)} ∂(K x₀)
            ≤ (K x₀) Gᶜ := by
          calc ∫⁻ y in Gᶜ, (killK K G ^ M) (some y) {(none : Option α)} ∂(K x₀)
              ≤ ∫⁻ _ in Gᶜ, (1 : ℝ≥0∞) ∂(K x₀) := by
                apply lintegral_mono_ae
                filter_upwards with y
                calc (killK K G ^ M) (some y) {(none : Option α)}
                    ≤ (killK K G ^ M) (some y) Set.univ :=
                      measure_mono (Set.subset_univ _)
                  _ ≤ 1 := by
                      haveI : ∀ s : ℕ, IsMarkovKernel ((killK K G) ^ s) := by
                        intro s
                        induction s with
                        | zero =>
                            rw [pow_zero]
                            exact inferInstanceAs
                              (IsMarkovKernel (Kernel.id : Kernel (Option α) (Option α)))
                        | succ s ihs =>
                            haveI := ihs
                            rw [pow_succ]
                            exact inferInstanceAs
                              (IsMarkovKernel (((killK K G) ^ s) ∘ₖ (killK K G)))
                      haveI := this M
                      rw [measure_univ]
            _ = (K x₀) Gᶜ := by
                rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, one_mul]
        have h0 : (K ^ 0) x₀ Sᶜ = Sᶜ.indicator 1 x₀ := by
          rw [pow_zero, show ((1 : Kernel α α)) = Kernel.id from rfl, Kernel.id_apply,
            Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        by_cases hxS : x₀ ∈ S
        · refine le_trans hle1 (le_trans (hstep x₀ hx₀ hxS) ?_)
          exact le_add_right le_rfl
        · refine le_trans hle1 ?_
          have h1 : (K x₀) Gᶜ ≤ 1 := by
            calc (K x₀) Gᶜ ≤ (K x₀) Set.univ := measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          have hind : (K ^ 0) x₀ Sᶜ = 1 := by
            rw [h0, Set.indicator_of_mem (show x₀ ∈ Sᶜ from hxS), Pi.one_apply]
          calc (K x₀) Gᶜ ≤ 1 := h1
            _ = (K ^ 0) x₀ Sᶜ := hind.symm
            _ ≤ q + (K ^ 0) x₀ Sᶜ := le_add_left le_rfl
      -- assemble: (M+1)·q + ∑_{τ<M+1} (K^τ) x₀ Sᶜ via peeling the τ=0 term.
      have hsum : ∑ τ ∈ Finset.range (M + 1), (K ^ τ) x₀ Sᶜ
          = (K ^ 0) x₀ Sᶜ + ∑ τ ∈ Finset.range M, (K ^ (τ + 1)) x₀ Sᶜ := by
        rw [Finset.sum_range_succ']
        exact add_comm _ _
      calc (∫⁻ y in G, (killK K G ^ M) (some y) {(none : Option α)} ∂(K x₀)) +
            (∫⁻ y in Gᶜ, (killK K G ^ M) (some y) {(none : Option α)} ∂(K x₀))
          ≤ ((M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ (τ + 1)) x₀ Sᶜ)
            + (q + (K ^ 0) x₀ Sᶜ) := add_le_add hbound1 hbound2
        _ = ((M : ℝ≥0∞) * q + q)
            + ((K ^ 0) x₀ Sᶜ + ∑ τ ∈ Finset.range M, (K ^ (τ + 1)) x₀ Sᶜ) := by
            rw [add_add_add_comm]
            exact congrArg (((M : ℝ≥0∞) * q + q) + ·) (add_comm _ _)
        _ = ((M + 1 : ℕ) : ℝ≥0∞) * q + ∑ τ ∈ Finset.range (M + 1), (K ^ τ) x₀ Sᶜ := by
            rw [hsum]
            congr 1
            push_cast
            ring

/-- **The fully-bounded gated real tail.**  Combining the escape-mass bound with
`gated_real_tail`: with a uniform per-step gate-leaving bound `η` on `G` and the drift
`r` on `G`, the REAL-kernel tail at the final potential is

  `(K^t) x {θ ≤ Φ} ≤ t·η + r^t·Φ x/θ`

— no killed-kernel quantity left in the statement. -/
theorem gated_real_tail_full [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (r : ℝ≥0∞) (hr : 1 ≤ r)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (η : ℝ≥0∞) (hesc : ∀ x ∈ G, K x Gᶜ ≤ η)
    (t : ℕ) (x : α) (hx : x ∈ G) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (K ^ t) x {y | θ ≤ Φ y} ≤ (t : ℝ≥0∞) * η + r ^ t * Φ x / θ := by
  refine le_trans (gated_real_tail (K := K) (G := G) Φ r hr hdrift_G t x θ hθ0 hθtop) ?_
  exact add_le_add (killed_none_mass_le η hesc t x hx) le_rfl

end GatedDrift

end Ripple.PopulationProtocol.ExactMajority
