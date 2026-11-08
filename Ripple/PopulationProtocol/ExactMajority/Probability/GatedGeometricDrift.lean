import Ripple.PopulationProtocol.ExactMajority.Probability.Supermartingale
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# GatedGeometricDrift — the killed-kernel gated geometric tail (Doty §6 brick 2)

The geometric-drift horizon tail (`geometric_drift_tail`) needs the one-step drift `∫⁻ Φ ∂(K x) ≤ r·Φ x` at
EVERY `x`.  For the early-drip the drift holds only on a gate `G` (feeder small = bulk not arrived), and the
gate is NOT maintained — the bulk eventually arrives, which is BENIGN (progress), not a breach.  To bound the
gated/survived walk we KILL the process when it leaves `G`: extend the state to `Option α` with cemetery
`none`, step via `K` on alive gated states `some x` (`x ∈ G`), and absorb at `none` otherwise.  With `r ≥ 1`
the killed drift holds UNCONDITIONALLY (off the gate the killed potential is `0`), so `geometric_drift_tail`
applies to the killed kernel directly.

This file builds the killed kernel and its unconditional drift (the core of brick 2).
-/

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

namespace GatedDrift

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

/-- The cemetery extension carries the discrete (`⊤`) measurable space. -/
local instance instOptionMS : MeasurableSpace (Option α) := ⊤
local instance instOptionDMS : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

/-- The killed kernel on `Option α`: alive gated states `some x` (`x ∈ G`) step via `K` (lifted to `some`);
the cemetery `none` and ungated states `some x` (`x ∉ G`) are absorbed at `none`. -/
noncomputable def killK (K : Kernel α α) (G : Set α) :
    Kernel (Option α) (Option α) :=
  Kernel.piecewise (s := (Option.some '' G))
    (DiscreteMeasurableSpace.forall_measurableSet _)
    ((K.map Option.some).comap (fun o => o.getD default) (Measurable.of_discrete))
    (Kernel.const _ (Measure.dirac (none : Option α)))

variable {K : Kernel α α} {G : Set α}

theorem some_mem_image_iff (x : α) : (some x ∈ Option.some '' G) ↔ x ∈ G :=
  ⟨fun ⟨a, ha, h⟩ => (Option.some.inj h) ▸ ha, fun h => ⟨x, h, rfl⟩⟩

theorem none_notMem_image : (none : Option α) ∉ Option.some '' G := by
  rintro ⟨a, _, h⟩; exact Option.some_ne_none a h

instance [IsMarkovKernel K] : IsMarkovKernel (killK K G) := by
  have hsome : Measurable (Option.some : α → Option α) := Measurable.of_discrete
  haveI : IsMarkovKernel (K.map (Option.some)) := Kernel.IsMarkovKernel.map K hsome
  unfold killK
  infer_instance

/-- The killed potential: `Φ` on alive states, `0` at the cemetery. -/
noncomputable def killΦ (Φ : α → ℝ≥0∞) : Option α → ℝ≥0∞ :=
  fun o => o.elim 0 Φ

theorem killΦ_measurable (Φ : α → ℝ≥0∞) : Measurable (killΦ Φ) :=
  Measurable.of_discrete

@[simp] theorem killΦ_none (Φ : α → ℝ≥0∞) : killΦ Φ none = 0 := rfl
@[simp] theorem killΦ_some (Φ : α → ℝ≥0∞) (x : α) : killΦ Φ (some x) = Φ x := rfl

/-- **The unconditional killed drift.**  If the original drift `∫⁻ Φ ∂(K x) ≤ r·Φ x` holds on the gate `G`
(`hdrift_G`) and `1 ≤ r`, then the KILLED drift `∫⁻ killΦ Φ ∂(killK K G o) ≤ r·killΦ Φ o` holds at EVERY
`o : Option α` — on alive gated states by `hdrift_G` (the killed integral equals `∫⁻ Φ ∂(K x)`), and elsewhere
trivially (the killed integral is `0` since the successor is the cemetery `none` where `killΦ = 0`). -/
theorem killK_drift [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (r : ℝ≥0∞) (hr : 1 ≤ r)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x) :
    ∀ o : Option α, ∫⁻ p, killΦ Φ p ∂(killK K G o) ≤ r * killΦ Φ o := by
  have hsome : Measurable (Option.some : α → Option α) := Measurable.of_discrete
  intro o
  unfold killK
  rw [Kernel.piecewise_apply]
  rcases o with _ | x
  · -- cemetery `none`: not in the alive set, dead branch, LHS = killΦ none = 0
    rw [if_neg none_notMem_image, Kernel.const_apply,
      MeasureTheory.lintegral_dirac' _ (killΦ_measurable Φ)]
    simp only [killΦ_none]; positivity
  · by_cases hx : x ∈ G
    · -- alive gated: ∫ killΦ over (K x).map some = ∫ Φ over K x ≤ r·Φ x
      rw [if_pos ((some_mem_image_iff x).2 hx), Kernel.comap_apply,
        Kernel.map_apply _ hsome,
        MeasureTheory.lintegral_map (killΦ_measurable Φ) hsome]
      simp only [Option.getD_some, killΦ_some]
      exact hdrift_G x hx
    · -- ungated `some x`, x ∉ G: dead branch, LHS = killΦ none = 0
      rw [if_neg (fun h => hx ((some_mem_image_iff x).1 h)), Kernel.const_apply,
        MeasureTheory.lintegral_dirac' _ (killΦ_measurable Φ)]
      simp only [killΦ_none]; positivity

/-- **The killed geometric tail** (brick 2b).  Feeding the unconditional killed drift `killK_drift` into the
generic `geometric_drift_tail` gives, for an alive start `some x`, the killed-walk tail:

  `(killK K G ^ t) (some x) {o | θ ≤ killΦ Φ o} ≤ r^t · Φ x / θ`.

The event `{θ ≤ killΦ Φ}` excludes the cemetery (`killΦ none = 0 < θ`), so the LHS is the mass of length-`t`
trajectories that STAY in the gate `G` and end with `θ ≤ Φ`.  This is the gated tail; `r ≥ 1` is required for
the killed drift to be unconditional. -/
theorem killed_geometric_tail [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (r : ℝ≥0∞) (hr : 1 ≤ r)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    ((killK K G) ^ t) (some x) {o | θ ≤ killΦ Φ o} ≤ r ^ t * Φ x / θ := by
  have h := geometric_drift_tail (killK K G) (killΦ Φ) (killΦ_measurable Φ) r
    (killK_drift Φ r hr hdrift_G) t (some x) θ hθ0 hθtop
  simpa using h

/-- The killed kernel at an alive gated state `some x` (`x ∈ G`) is the `K`-step pushed into `some`. -/
theorem killK_some_gated (x : α) (hx : x ∈ G) :
    killK K G (some x) = (K x).map Option.some := by
  unfold killK
  rw [Kernel.piecewise_apply, if_pos ((some_mem_image_iff x).2 hx),
    Kernel.comap_apply, Kernel.map_apply _ (Measurable.of_discrete)]
  simp only [Option.getD_some]

/-- The cemetery `none` is absorbing: `killK` sends it to `δ none`. -/
theorem killK_none : killK K G none = Measure.dirac (none : Option α) := by
  unfold killK
  rw [Kernel.piecewise_apply, if_neg none_notMem_image, Kernel.const_apply]

/-- The cemetery stays absorbing under iteration: `(killK^t) none = δ none`. -/
theorem none_absorbing [IsMarkovKernel K] (t : ℕ) :
    (killK K G ^ t) (none : Option α) = Measure.dirac (none : Option α) := by
  induction t with
  | zero => rw [pow_zero]; exact Kernel.id_apply none
  | succ t ih =>
      ext S hS
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral (killK K G) 1 t none hS, pow_one, killK_none,
        MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete), ih]

/-- **Brick 2c — the killed kernel dominates the real kernel's bad event.**  For any predicate `bad`, the
real `t`-step mass landing in `{bad}` is at most the killed `t`-step mass (from the alive start `some x`) of
`{none} ∪ {some y | bad y}`: every real trajectory either stays in the gate `G` throughout — tracked by
`killK` as a `some`-trajectory, contributing to `{some y | bad y}` when its endpoint is bad — or exits `G`,
sending `killK` to the cemetery `none` (always in the target set).  Since exiting-then-bad ⊆ exited, the
inequality holds.  PROVEN by induction on `t` (Chapman–Kolmogorov on both kernel powers; on the alive branch
`killK (some x) = (K x).map some` aligns the two integrals; on the dead branch the RHS is `1`). -/
theorem real_le_killed [IsMarkovKernel K] (bad : α → Prop) (t : ℕ) (x : α) :
    (K ^ t) x {y | bad y} ≤
      (killK K G ^ t) (some x) {o | o = none ∨ (∃ y, o = some y ∧ bad y)} := by
  classical
  have hMK : ∀ s : ℕ, IsMarkovKernel (K ^ s) := by
    intro s; induction s with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
    | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((K ^ s) ∘ₖ K))
  set Rset : Set (Option α) := {o | o = none ∨ (∃ y, o = some y ∧ bad y)} with hRset
  induction t generalizing x with
  | zero =>
      rw [pow_zero, pow_zero]
      show (Measure.dirac x) {y | bad y} ≤ (Measure.dirac (some x)) Rset
      rw [Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      by_cases hb : bad x
      · simp [Set.indicator_of_mem (show x ∈ {y | bad y} from hb),
          Set.indicator_of_mem (show (some x) ∈ Rset from Or.inr ⟨x, rfl, hb⟩)]
      · simp [Set.indicator_of_notMem (show x ∉ {y | bad y} from hb)]
  | succ t ih =>
      have hCKK : (K ^ (t + 1)) x {y | bad y}
          = ∫⁻ y, (K ^ t) y {y | bad y} ∂(K x) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral K 1 t x
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      have hCKkill : (killK K G ^ (t + 1)) (some x) Rset
          = ∫⁻ o, (killK K G ^ t) o Rset ∂(killK K G (some x)) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK K G) 1 t (some x)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCKK, hCKkill]
      by_cases hx : x ∈ G
      · rw [killK_some_gated (K := K) (G := G) x hx,
          MeasureTheory.lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
        exact lintegral_mono (fun y => ih y)
      · -- ungated start: killK (some x) = δ none, the RHS integral is `(killK^t)(none) Rset = 1`.
        have hdead : killK K G (some x) = Measure.dirac (none : Option α) := by
          unfold killK
          rw [Kernel.piecewise_apply, if_neg (fun h => hx ((some_mem_image_iff x).1 h)),
            Kernel.const_apply]
        rw [hdead, MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete)]
        -- RHS = (killK^t)(none) Rset = 1 (none absorbing, none ∈ Rset); LHS ≤ 1.
        have hrhs : (killK K G ^ t) (none : Option α) Rset = 1 := by
          rw [none_absorbing t, Measure.dirac_apply' _
            (DiscreteMeasurableSpace.forall_measurableSet _),
            Set.indicator_of_mem (show (none : Option α) ∈ Rset from Or.inl rfl),
            Pi.one_apply]
        rw [hrhs]
        haveI : IsMarkovKernel (K ^ t) := hMK t
        calc ∫⁻ y, (K ^ t) y {y | bad y} ∂(K x)
            ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(K x) := by
              refine lintegral_mono (fun y => ?_)
              exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
          _ = 1 := by rw [MeasureTheory.lintegral_one, measure_univ]

/-- **Brick 2d — the gated tail on the REAL kernel.**  Combining the coupling `real_le_killed` (2c) with the
killed geometric tail `killed_geometric_tail` (2b): on the real kernel `K`, the `t`-step probability that
`θ ≤ Φ` is at most the ESCAPE mass `(killK^t)(some x){none}` (the gate `G` was left — in the application, the
bulk arrived = benign progress) PLUS the killed geometric tail `r^t · Φ x / θ`.  This is the unconditional
gated tail: the drift hypothesis is required only on the gate `G` (`hdrift_G`), not everywhere. -/
theorem gated_real_tail [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (r : ℝ≥0∞) (hr : 1 ≤ r)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (K ^ t) x {y | θ ≤ Φ y} ≤
      (killK K G ^ t) (some x) {(none : Option α)} + r ^ t * Φ x / θ := by
  refine (real_le_killed (K := K) (G := G) (fun y => θ ≤ Φ y) t x).trans ?_
  have hsub : {o : Option α | o = none ∨ ∃ y, o = some y ∧ θ ≤ Φ y}
      ⊆ {(none : Option α)} ∪ {o | θ ≤ killΦ Φ o} := by
    rintro o (rfl | ⟨y, rfl, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr hy
  calc (killK K G ^ t) (some x) {o : Option α | o = none ∨ ∃ y, o = some y ∧ θ ≤ Φ y}
      ≤ (killK K G ^ t) (some x) ({(none : Option α)} ∪ {o | θ ≤ killΦ Φ o}) := measure_mono hsub
    _ ≤ (killK K G ^ t) (some x) {(none : Option α)}
          + (killK K G ^ t) (some x) {o | θ ≤ killΦ Φ o} := measure_union_le _ _
    _ ≤ (killK K G ^ t) (some x) {(none : Option α)} + r ^ t * Φ x / θ := by
        gcongr
        exact killed_geometric_tail Φ r hr hdrift_G t x θ hθ0 hθtop

/-! ## The STEP-INDEXED gated engine (Doty §6 brick 3.4c-i)

The constant-rate engine above cannot handle BRANCHING increments (rate ∝ the current count, as in
the epidemic-from-tainted term of the early-drip set): the worst-case constant rate over the window
overshoots.  The classical fix is a TIME-DEPENDENT exponential potential `Φ_j = exp(s_j·N + b_j)`
with `s_j` decreasing just fast enough to absorb the branching factor.  The engine here is the
supporting supermartingale machinery, generic over the potential family: if `∫ Φ_{j+1} dK ≤ Φ_j` on
the gate `G`, then the real-kernel tail at the FINAL potential `Φ_t` is bounded by the escape mass
plus `Φ_0 x / θ`.  (The constant-rate engine is the special case `Φ_j = r^j·Φ`.) -/

/-- The step-indexed decay: a potential family with one-step drift `∫ Φ_{j+1} dK ≤ Φ_j` at every
state contracts over the horizon: `∫ Φ_t d(K^t x) ≤ Φ_0 x`. -/
theorem lintegral_stepIndexed_decay {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] :
    ∀ (t : ℕ) (Φ : ℕ → α → ℝ≥0∞), (∀ j, Measurable (Φ j)) →
      (∀ (j : ℕ) (x : α), ∫⁻ y, Φ (j + 1) y ∂(K x) ≤ Φ j x) →
      ∀ x : α, ∫⁻ y, Φ t y ∂((K ^ t) x) ≤ Φ 0 x := by
  intro t
  induction t with
  | zero =>
      intro Φ hΦ _ x
      simp only [pow_zero]
      change ∫⁻ y, Φ 0 y ∂(Kernel.id x) ≤ Φ 0 x
      rw [Kernel.id_apply, lintegral_dirac' x (hΦ 0)]
  | succ t ih =>
      intro Φ hΦ hdrift x
      change ∫⁻ y, Φ (t + 1) y ∂(((K ^ t) ∘ₖ K) x) ≤ Φ 0 x
      rw [Kernel.lintegral_comp _ K x (hΦ _)]
      calc ∫⁻ b, ∫⁻ y, Φ (t + 1) y ∂((K ^ t) b) ∂(K x)
          ≤ ∫⁻ b, Φ 1 b ∂(K x) :=
            lintegral_mono (fun b =>
              ih (fun j => Φ (j + 1)) (fun j => hΦ _) (fun j y => hdrift (j + 1) y) b)
        _ ≤ Φ 0 x := hdrift 0 x

/-- **The step-indexed gated tail on the REAL kernel** (the time-dependent-MGF engine).  If the
potential family drifts on the gate `G` (`∫ Φ_{j+1} dK ≤ Φ_j` for `x ∈ G` — no factor, no `r ≥ 1`
side condition), then the real `t`-step tail at the FINAL potential is bounded by the escape mass
plus `Φ_0 x / θ`:

  `(K^t) x {θ ≤ Φ_t} ≤ (killK^t)(some x){none} + Φ_0 x / θ`. -/
theorem stepIndexed_gated_tail {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Inhabited α] {K : Kernel α α} {G : Set α} [IsMarkovKernel K]
    (Φ : ℕ → α → ℝ≥0∞)
    (hdrift_G : ∀ (j : ℕ), ∀ x ∈ G, ∫⁻ y, Φ (j + 1) y ∂(K x) ≤ Φ j x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (K ^ t) x {y | θ ≤ Φ t y} ≤
      (killK K G ^ t) (some x) {(none : Option α)} + Φ 0 x / θ := by
  classical
  -- the killed family drifts UNCONDITIONALLY (off-gate and at the cemetery the integral is 0).
  have hkill_drift : ∀ (j : ℕ) (o : Option α),
      ∫⁻ p, killΦ (Φ (j + 1)) p ∂(killK K G o) ≤ killΦ (Φ j) o := by
    intro j o
    rcases o with _ | x'
    · rw [killK_none, MeasureTheory.lintegral_dirac' _ (killΦ_measurable _)]
      simp
    · by_cases hx : x' ∈ G
      · rw [killK_some_gated x' hx,
          MeasureTheory.lintegral_map (killΦ_measurable _) (Measurable.of_discrete)]
        simp only [killΦ_some]
        exact hdrift_G j x' hx
      · have hdead : killK K G (some x') = Measure.dirac (none : Option α) := by
          unfold killK
          rw [Kernel.piecewise_apply, if_neg (fun h => hx ((some_mem_image_iff x').1 h)),
            Kernel.const_apply]
        rw [hdead, MeasureTheory.lintegral_dirac' _ (killΦ_measurable _)]
        simp
  -- killed decay + Markov.
  have hdecay := lintegral_stepIndexed_decay (killK K G) t (fun j => killΦ (Φ j))
    (fun j => killΦ_measurable _) hkill_drift (some x)
  simp only [killΦ_some] at hdecay
  have hMarkov : θ * (killK K G ^ t) (some x) {o | θ ≤ killΦ (Φ t) o} ≤ Φ 0 x :=
    le_trans (mul_meas_ge_le_lintegral₀ (hf := (killΦ_measurable _).aemeasurable) (ε := θ))
      hdecay
  have hkilled_tail : (killK K G ^ t) (some x) {o | θ ≤ killΦ (Φ t) o} ≤ Φ 0 x / θ := by
    calc (killK K G ^ t) (some x) {o | θ ≤ killΦ (Φ t) o}
        = (θ⁻¹ * θ) * (killK K G ^ t) (some x) {o | θ ≤ killΦ (Φ t) o} := by
          simp [ENNReal.inv_mul_cancel hθ0 hθtop]
      _ = θ⁻¹ * (θ * (killK K G ^ t) (some x) {o | θ ≤ killΦ (Φ t) o}) := by
          simp [mul_assoc]
      _ ≤ θ⁻¹ * Φ 0 x := by gcongr
      _ = Φ 0 x / θ := by rw [mul_comm]; rfl
  -- couple to the real kernel.
  refine (real_le_killed (K := K) (G := G) (fun y => θ ≤ Φ t y) t x).trans ?_
  have hsub : {o : Option α | o = none ∨ ∃ y, o = some y ∧ θ ≤ Φ t y}
      ⊆ {(none : Option α)} ∪ {o | θ ≤ killΦ (Φ t) o} := by
    rintro o (rfl | ⟨y, rfl, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr hy
  calc (killK K G ^ t) (some x) {o : Option α | o = none ∨ ∃ y, o = some y ∧ θ ≤ Φ t y}
      ≤ (killK K G ^ t) (some x) ({(none : Option α)} ∪ {o | θ ≤ killΦ (Φ t) o}) :=
        measure_mono hsub
    _ ≤ (killK K G ^ t) (some x) {(none : Option α)}
          + (killK K G ^ t) (some x) {o | θ ≤ killΦ (Φ t) o} := measure_union_le _ _
    _ ≤ (killK K G ^ t) (some x) {(none : Option α)} + Φ 0 x / θ := by
        gcongr

end GatedDrift

end Ripple.PopulationProtocol.ExactMajority
