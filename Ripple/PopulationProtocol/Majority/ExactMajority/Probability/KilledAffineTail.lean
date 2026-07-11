import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedKillNow
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RectangleResidualProof
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FloorPrefix

/-!
# KilledAffineTail — the AFFINE-IMMIGRATION killed-tail engine (Doty §6 generic brick)

This file builds the ONE generic engine three campaign lines are blocked on: the
`killK`/`killK_now` analogue of `Phase0Window.phase0_window_tail_affine`.  Informally:

* kernel `K`, gate `G`, potential `Φ`, AFFINE drift `∫⁻ Φ d(K x) ≤ a·Φ(x) + b` holding
  **for `x ∈ G` only** (`a ≥ 0` ARBITRARY — no `1 ≤ a` — and `b ≥ 0`, `b = 0` allowed);
* the KILLED kernel `killK_now K G` then satisfies the same affine tail on the alive
  start:  `(killK_now^t)(some x₀) {θ ≤ killΦ Φ} ≤ (aᵗ·Φ(x₀) + b·∑_{i<t}aⁱ)/θ`;
* the REAL chain satisfies `real ≤ killed-tail + escape` (`real_le_killed_now` +
  `gateMap` accounting), with the escape prefix itself bounded — INCLUDING the
  self-referential pattern where the per-step gate-exit event is contained in a
  Φ-threshold event (`{exit possible} ⊆ {Φ ≥ θ'}` via a deterministic bridge), so
  `escape ≤ ∑_τ (killed affine tail at τ)/θ'`.  We close that loop as a packaged
  theorem and instantiate it for Consumer 1 (the unconditional Phase-0 window).

## Why the old engine needed `1 ≤ r`, and why we drop it honestly

The multiplicative gated engine (`GatedGeometricDrift.killed_geometric_tail`,
`GatedEscape.gated_real_tail_full`) carries `hr : 1 ≤ r`.  Inspecting
`GatedGeometricDrift.killK_drift`, the hypothesis `hr` is **never used in the proof
body**: the killed potential is `killΦ Φ none = 0`, so on the cemetery / ungated branch
the killed drift LHS is `∫⁻ killΦ d(δ none) = 0 ≤ r·0`, true for ANY `r ≥ 0`; on the
alive-gated branch it is exactly `hdrift_G`.  Likewise the analytic core
`PopProtoCommon.lintegral_geometric_decay` takes arbitrary `r`.  So `1 ≤ r` was a
SPURIOUS convention carried from the supermartingale layer.  For the AFFINE case the
same holds with even less room for doubt: `killΦ none = 0`, so the affine killed drift
target on the dead branch is `a·killΦ none + b = b ≥ 0 ≥ 0 = LHS`.  We therefore build
the affine killed drift / tail with `a ≥ 0` arbitrary, and the resulting tail GENUINELY
decays when `a < 1` (the contractive mid-band regime Consumer 3 was blocked on).

The companion `GatedEscape.gated_real_tail_full` tail `t·η + rᵗ·Φx/θ` is NOT contractive
not because of any `killK` obstruction but because it bounds escape by the COARSE
`t·η`; here we instead bound escape by the SELF-REFERENTIAL prefix sum of killed affine
tails (Stage 3), which decays with the tail.

We use the IMMEDIATE-kill kernel `killK_now` (off-gate successors die in the SAME step),
matching `GatedKillNow.lean`'s conventions, so `alive_support_gate` holds and the escape
registers without lag.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators

namespace GatedDrift

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

local instance instOptionMSaff : MeasurableSpace (Option α) := ⊤
local instance instOptionDMSaff : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

variable {K : Kernel α α} {G : Set α}

/-! ## Stage 1 — the generic killed affine tail (no `1 ≤ a`).

`killΦ Φ` (`= Φ` on alive, `0` at the cemetery) makes the killed kernel a GENUINE
absorbing-window carrier for the affine drift: on `some x` with `x ∈ G` the killed
integral equals `∫⁻ Φ d(K x) ≤ a·Φ(x) + b`; on the cemetery / ungated states it is `0 ≤
a·0 + b`.  So the one-step affine drift holds UNCONDITIONALLY on `Option α` for the
killed kernel, with `a ≥ 0` arbitrary and `b ≥ 0`. -/

/-- **The unconditional killed AFFINE drift** (immediate-kill kernel).  If `∫⁻ Φ d(K x) ≤
a·Φ(x) + b` on the gate `G` (`hdrift_G`), then the KILLED affine drift `∫⁻ killΦ Φ
d(killK_now K G o) ≤ a·killΦ Φ o + b` holds at EVERY `o : Option α`.  No `1 ≤ a`: on the
dead branches the LHS is `0 ≤ a·0 + b = b`. -/
theorem killK_now_drift_affine [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (a b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ a * Φ x + b) :
    ∀ o : Option α, ∫⁻ p, killΦ Φ p ∂(killK_now K G o) ≤ a * killΦ Φ o + b := by
  intro o
  rcases o with _ | x
  · -- cemetery: killK_now none = δ none, ∫ killΦ = killΦ none = 0 ≤ a·0 + b
    rw [killK_now_none, MeasureTheory.lintegral_dirac' _ (killΦ_measurable Φ)]
    simp only [killΦ_none, mul_zero, zero_add]
    exact zero_le'
  · by_cases hx : x ∈ G
    · -- alive gated: ∫ killΦ over (K x).map (gateMap G) = ∫ Φ over K x (off-gate ↦ 0)
      rw [killK_now_some_gated x hx,
        MeasureTheory.lintegral_map (killΦ_measurable Φ) (gateMap_measurable G)]
      simp only [killΦ_some]
      refine le_trans (lintegral_mono (fun y => ?_)) (hdrift_G x hx)
      -- killΦ (gateMap G y) = Φ y if y ∈ G else 0 ≤ Φ y
      unfold gateMap
      by_cases hyG : y ∈ G
      · rw [if_pos hyG, killΦ_some]
      · rw [if_neg hyG]; simp only [killΦ_none]; exact zero_le'
    · -- ungated alive: killK_now (some x) = δ none, ∫ killΦ = 0 ≤ a·Φx + b
      rw [killK_now_ungated x hx, MeasureTheory.lintegral_dirac' _ (killΦ_measurable Φ)]
      simp only [killΦ_none]
      exact zero_le'

/-- **Affine lintegral decay for the killed kernel** (kernel-level, `a ≥ 0` arbitrary).
Iterating the unconditional killed affine drift `killK_now_drift_affine` gives
`∫⁻ killΦ Φ d(killK_now^t o) ≤ aᵗ·killΦ Φ(o) + b·∑_{i<t}aⁱ` at EVERY `o`.  This is the
`Option α` analogue of `Phase0Window.lintegral_decay_affine_on_absorbing` — but the
absorption is structural (`killΦ none = 0`), so it holds at every state with NO absorbing
window hypothesis. -/
theorem killed_now_lintegral_decay_affine [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (a b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ a * Φ x + b)
    (t : ℕ) (o : Option α) :
    ∫⁻ p, killΦ Φ p ∂((killK_now K G ^ t) o)
      ≤ a ^ t * killΦ Φ o + b * ∑ i ∈ Finset.range t, a ^ i := by
  have hMK : ∀ s : ℕ, IsMarkovKernel (killK_now K G ^ s) := by
    intro s; induction s with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (Option α) (Option α)))
    | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((killK_now K G ^ s) ∘ₖ killK_now K G))
  induction t generalizing o with
  | zero =>
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    change ∫⁻ p, killΦ Φ p ∂(Kernel.id o) ≤ killΦ Φ o
    rw [Kernel.id_apply, lintegral_dirac' o (killΦ_measurable Φ)]
  | succ t ih =>
    change ∫⁻ p, killΦ Φ p ∂(((killK_now K G ^ t) ∘ₖ killK_now K G) o)
      ≤ a ^ (t + 1) * killΦ Φ o + b * ∑ i ∈ Finset.range (t + 1), a ^ i
    rw [Kernel.lintegral_comp _ _ o (killΦ_measurable Φ)]
    calc ∫⁻ p, ∫⁻ q, killΦ Φ q ∂((killK_now K G ^ t) p) ∂(killK_now K G o)
        ≤ ∫⁻ p, (a ^ t * killΦ Φ p + b * ∑ i ∈ Finset.range t, a ^ i)
            ∂(killK_now K G o) := lintegral_mono (fun p => ih p)
      _ = a ^ t * (∫⁻ p, killΦ Φ p ∂(killK_now K G o))
            + b * (∑ i ∈ Finset.range t, a ^ i) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (killΦ_measurable Φ),
              lintegral_const, measure_univ, mul_one]
      _ ≤ a ^ t * (a * killΦ Φ o + b) + b * (∑ i ∈ Finset.range t, a ^ i) := by
          gcongr; exact killK_now_drift_affine Φ a b hdrift_G o
      _ = a ^ (t + 1) * killΦ Φ o + b * ∑ i ∈ Finset.range (t + 1), a ^ i := by
          rw [Finset.sum_range_succ, mul_add, mul_add]
          rw [show a ^ t * (a * killΦ Φ o) = a ^ (t + 1) * killΦ Φ o by rw [pow_succ]; ring]
          rw [show a ^ t * b = b * a ^ t by ring]
          ring

/-- **The generic killed affine tail** (`a ≥ 0` arbitrary; `b = 0` special case included).
From the affine drift on `G` only, the killed walk from an alive start `some x₀` has the
threshold tail
  `(killK_now^t)(some x₀) {o | θ ≤ killΦ Φ o} ≤ (aᵗ·Φ(x₀) + b·∑_{i<t}aⁱ)/θ`.
The event `{θ ≤ killΦ Φ}` excludes the cemetery (`killΦ none = 0 < θ`); when `a < 1` the
`aᵗ` factor genuinely decays.  With `b = 0` this is the purely-multiplicative killed tail
`aᵗ·Φ(x₀)/θ` with NO `1 ≤ a` requirement. -/
theorem killed_now_affine_tail [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (a b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ a * Φ x + b)
    (t : ℕ) (x₀ : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (killK_now K G ^ t) (some x₀) {o | θ ≤ killΦ Φ o}
      ≤ (a ^ t * Φ x₀ + b * ∑ i ∈ Finset.range t, a ^ i) / θ := by
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := (killK_now K G ^ t) (some x₀))
    (killΦ_measurable Φ).aemeasurable θ
  have hdecay := killed_now_lintegral_decay_affine Φ a b hdrift_G t (some x₀)
  have hchain : θ * (killK_now K G ^ t) (some x₀) {o | θ ≤ killΦ Φ o}
      ≤ a ^ t * Φ x₀ + b * ∑ i ∈ Finset.range t, a ^ i := by
    refine le_trans hmarkov ?_
    simpa only [killΦ_some] using hdecay
  rw [ENNReal.le_div_iff_mul_le (Or.inl hθ0) (Or.inl hθtop), mul_comm]
  exact hchain

/-! ## Stage 2 — `real ≤ killed-affine-tail + escape` composition.

`real_le_killed_now` dominates the real bad mass by the killed mass of
`{none} ∪ {some y | bad y}`.  Splitting that union (`measure_union_le`) gives ESCAPE
(`{none}`) + the ALIVE bad mass.  When `bad y := θ ≤ Φ y`, the alive bad mass is exactly
the killed affine tail event `{o | θ ≤ killΦ Φ o}` restricted to alive states, so it is
bounded by `killed_now_affine_tail`.  The composition leaves only the escape mass to be
controlled (Stage 3). -/

/-- **`real ≤ killed-affine-tail + escape`.**  With the affine drift on `G`, the real
`t`-step mass of `{θ ≤ Φ}` from a gate start is bounded by the killed affine tail PLUS
the escape (cemetery) mass:
  `(K^t) x₀ {θ ≤ Φ} ≤ (aᵗΦx₀ + b∑aⁱ)/θ + (killK_now^t)(some x₀){none}`. -/
theorem real_le_killed_affine_tail_add_escape [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (a b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ a * Φ x + b)
    (t : ℕ) (x₀ : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (K ^ t) x₀ {y | θ ≤ Φ y}
      ≤ (a ^ t * Φ x₀ + b * ∑ i ∈ Finset.range t, a ^ i) / θ
          + (killK_now K G ^ t) (some x₀) {(none : Option α)} := by
  classical
  -- Step 1: real ≤ killed mass of {none} ∪ {some y | θ ≤ Φ y}.
  refine le_trans (real_le_killed_now (K := K) (G := G) (fun y => θ ≤ Φ y) t x₀) ?_
  -- Step 2: that set ⊆ {none} ∪ {θ ≤ killΦ Φ}.
  have hsub : {o : Option α | o = none ∨ (∃ y, o = some y ∧ θ ≤ Φ y)}
      ⊆ {(none : Option α)} ∪ {o | θ ≤ killΦ Φ o} := by
    rintro o (rfl | ⟨y, rfl, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr (by simpa only [Set.mem_setOf_eq, killΦ_some] using hy)
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  -- Step 3: bound each piece; killed affine tail (right of target) + escape (left).
  rw [add_comm ((a ^ t * Φ x₀ + b * ∑ i ∈ Finset.range t, a ^ i) / θ)]
  refine add_le_add ?_ ?_
  · -- {none} mass = escape (matches the right summand of the target)
    exact le_rfl
  · -- {θ ≤ killΦ Φ} mass ≤ killed affine tail (matches the left summand of the target)
    exact killed_now_affine_tail Φ a b hdrift_G t x₀ θ hθ0 hθtop

/-! ## Stage 3 — the self-referential escape closure (deterministic exit bridge).

The escape (cemetery) mass `(killK_now^M)(some x₀){none}` is the run-long accounting of
the walk leaving `G`.  `kill_now_escape_le_prefix_union` bounds it by `M·q + ∑_τ (K^τ)
x₀ Sᶜ` given a per-step bound `K x Gᶜ ≤ q` on `G ∩ S`.

The DETERMINISTIC EXIT BRIDGE (the `det_phase0_exit` pattern): if exiting `G` is
impossible UNLESS `θ' ≤ Φ` holds, i.e. `∀ x ∈ G, Φ x < θ' → K x Gᶜ = 0`, then taking the
side event `S := {x | Φ x < θ'}` gives `q = 0`, so

  `escape ≤ ∑_{τ<M} (K^τ) x₀ {θ' ≤ Φ}`.

Each prefix term `(K^τ) x₀ {θ' ≤ Φ}` is itself a real threshold mass — which Stage 2
bounds by `killed-affine-tail(τ) + escape(τ)`.  We expose BOTH the clean escape→prefix
bound (`escape_le_threshold_prefix`) and the fully-unwound packaged window theorem
(`real_window_killed_affine`) where the escape is replaced by the prefix sum of threshold
masses, leaving a statement with NO killed quantity beyond the affine tails. -/

/-- **Escape ≤ threshold-prefix (deterministic exit bridge, `q = 0`).**  If from every
gated state with `Φ < θ'` the one-step probability of leaving `G` is `0` (exit is only
possible at `θ' ≤ Φ`), then the escape mass after `M` steps is bounded by the prefix sum
of the real threshold masses:
  `(killK_now^M)(some x₀){none} ≤ ∑_{τ<M} (K^τ) x₀ {θ' ≤ Φ}`. -/
theorem escape_le_threshold_prefix [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (θ' : ℝ≥0∞)
    (hbridge : ∀ x ∈ G, Φ x < θ' → K x Gᶜ = 0)
    (M : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (killK_now K G ^ M) (some x₀) {(none : Option α)} ≤
      ∑ τ ∈ Finset.range M, (K ^ τ) x₀ {y | θ' ≤ Φ y} := by
  classical
  -- side event S := {x | Φ x < θ'}; then Sᶜ = {θ' ≤ Φ} and q = 0.
  have hstep : ∀ x ∈ G, x ∈ {z | Φ z < θ'} → K x Gᶜ ≤ 0 := by
    intro x hxG hxS
    exact le_of_eq (hbridge x hxG hxS)
  have h := kill_now_escape_le_prefix_union (K := K) (G := G) {z | Φ z < θ'} 0 hstep M x₀ hx₀
  refine le_trans h ?_
  rw [mul_zero, zero_add]
  -- Sᶜ = {z | ¬ (Φ z < θ')} = {θ' ≤ Φ}
  apply Finset.sum_le_sum
  intro τ _
  apply le_of_eq
  congr 1
  ext y
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]

/-- **The packaged real-chain window (killed affine tail + threshold-prefix escape).**
Combining Stage 2 (`real_le_killed_affine_tail_add_escape` at threshold `θ`) with the
deterministic exit bridge (Stage 3, `escape_le_threshold_prefix` at the EXIT threshold
`θ'`):

  `(K^t) x₀ {θ ≤ Φ} ≤ (aᵗΦx₀ + b∑aⁱ)/θ + ∑_{τ<t} (K^τ) x₀ {θ' ≤ Φ}`.

This is the self-referential window: the escape is fully accounted by the prefix sum of
real threshold masses (no killed quantity remains), and each prefix term can be bounded
by the same machinery (or directly by reachability, as the consumers do via their per-τ
whp corollaries). -/
theorem real_window_killed_affine [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (a b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ a * Φ x + b)
    (θ θ' : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hbridge : ∀ x ∈ G, Φ x < θ' → K x Gᶜ = 0)
    (t : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (K ^ t) x₀ {y | θ ≤ Φ y}
      ≤ (a ^ t * Φ x₀ + b * ∑ i ∈ Finset.range t, a ^ i) / θ
          + ∑ τ ∈ Finset.range t, (K ^ τ) x₀ {y | θ' ≤ Φ y} := by
  refine le_trans
    (real_le_killed_affine_tail_add_escape Φ a b hdrift_G t x₀ θ hθ0 hθtop) ?_
  refine add_le_add le_rfl ?_
  exact escape_le_threshold_prefix Φ θ' hbridge t x₀ hx₀

/-- **The fully-bounded window from a uniform per-τ threshold bound.**  If, in addition,
each prefix threshold mass `(K^τ) x₀ {θ' ≤ Φ}` is at most a uniform `β` (supplied by the
consumer's per-τ reachability/whp corollary), the real window failure is bounded by a
fully explicit budget:
  `(K^t) x₀ {θ ≤ Φ} ≤ (aᵗΦx₀ + b∑aⁱ)/θ + t·β`. -/
theorem real_window_killed_affine_uniform [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (a b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ a * Φ x + b)
    (θ θ' : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hbridge : ∀ x ∈ G, Φ x < θ' → K x Gᶜ = 0)
    (t : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) (β : ℝ≥0∞)
    (hβ : ∀ τ ∈ Finset.range t, (K ^ τ) x₀ {y | θ' ≤ Φ y} ≤ β) :
    (K ^ t) x₀ {y | θ ≤ Φ y}
      ≤ (a ^ t * Φ x₀ + b * ∑ i ∈ Finset.range t, a ^ i) / θ + (t : ℝ≥0∞) * β := by
  refine le_trans (real_window_killed_affine Φ a b hdrift_G θ θ' hθ0 hθtop hbridge t x₀ hx₀) ?_
  refine add_le_add le_rfl ?_
  refine le_trans (Finset.sum_le_sum hβ) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end GatedDrift

/-! ## Stage 4 — Consumer 1: the UNCONDITIONAL Phase-0 window (Gap-2 headline).

The campaign's headline blocker: `Phase0Window.phase0_window_tail_affine` needs an
ABSORBING `Q ⊆ allPhase0`, which does NOT exist — `allPhase0` genuinely exits when a
clock hits `counter = 0` (`det_phase0_exit`).  The killed engine REMOVES that
requirement: the gate `G := allPhase0 ∩ {card = n}` is one-step-closed under the killed
kernel EXCEPT for the `allPhase0` exit (which is killed), and that exit is the
deterministic threshold event `{Φ_s ≥ 1}` (`det_phase0_exit`).  So:

* the AFFINE DRIFT on `G` is `clockCounterPotential_drift_affine` (proven on `allPhase0`
  alone, no positive-counter side condition);
* the EXIT BRIDGE `∀ x ∈ G, Φ_s x < 1 → K x Gᶜ = 0` holds: `Φ_s < 1` ⟹ `noClockAtZero`
  (contrapositive of the threshold link), and `allPhase0 ∧ noClockAtZero` ⟹ `allPhase0`
  preserved one step (`transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero`) while
  cardinality is preserved (`stepOrSelf_card_eq`), so the killed walk stays in `G`.

Feeding these into the Stage-1/2/3 engine gives the per-`τ` real clock-zero bound with
hypothesis surface = `Phase0Initial` + arithmetic — no absorbing `Q`. -/

namespace Phase0Window

open GatedDrift

variable {L K : ℕ}

/-- The Phase-0 killed gate `G := allPhase0 ∩ {card = n}`. -/
def phase0Gate (n : ℕ) : Set (Config (AgentState L K)) :=
  {c | allPhase0 (L := L) (K := K) c ∧ Multiset.card c = n}

/-- **The Phase-0 exit bridge.**  From a config in the gate `G = allPhase0 ∩ {card = n}`
whose potential `Φ_s` is below threshold `1` (hence `noClockAtZero`), the real Doty
kernel cannot leave `G`: the `allPhase0` part is preserved
(`transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero`) and the cardinality part is
preserved (`stepOrSelf_card_eq`), so the `Gᶜ` mass is `0`.  This is the `q = 0`
deterministic exit bridge the killed-affine engine needs. -/
theorem phase0Gate_exit_bridge (s : ℝ) (n : ℕ)
    (c : Config (AgentState L K)) (hc : c ∈ phase0Gate (L := L) (K := K) n)
    (hΦ : clockCounterPotential (L := L) (K := K) s c < 1) :
    (NonuniformMajority L K).transitionKernel c (phase0Gate (L := L) (K := K) n)ᶜ = 0 := by
  classical
  obtain ⟨hall, hcard⟩ := hc
  -- Φ < 1 ⟹ noClockAtZero (contrapositive of the threshold link).
  have hno : noClockAtZero (L := L) (K := K) c := by
    by_contra hcontra
    exact absurd (clockCounterPotential_ge_one_of_not_noClockAtZero s c hcontra) (not_le.2 hΦ)
  -- Gᶜ ⊆ {¬allPhase0} ∪ {card ≠ n}; both have mass 0.
  have hsub : (phase0Gate (L := L) (K := K) n)ᶜ ⊆
      {c' | ¬ allPhase0 (L := L) (K := K) c'} ∪ {c' | Multiset.card c' ≠ n} := by
    intro c' hc'
    by_cases h1 : allPhase0 (L := L) (K := K) c'
    · refine Or.inr ?_
      intro hcard'
      exact hc' ⟨h1, hcard'⟩
    · exact Or.inl h1
  refine le_antisymm ?_ (zero_le')
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero c hall hno, zero_add]
  -- {card ≠ n} mass = 0: every support successor preserves card = n.
  have hcardzero : (NonuniformMajority L K).transitionKernel c
      {c' | Multiset.card c' ≠ n} = 0 := by
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Multiset.card c' ≠ n} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _),
      Set.disjoint_left]
    intro c' hsupp hbad
    apply hbad
    -- support successor c' has card c' = card c = n
    have hcc : Multiset.card c' = Multiset.card c := by
      unfold Protocol.stepDistOrSelf at hsupp
      by_cases hc2 : 2 ≤ c.card
      · rw [dif_pos hc2] at hsupp
        obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support _ c hc2 c' hsupp
        rw [show Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂)
              = Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ from rfl] at hr
        rw [← hr]; exact Protocol.stepOrSelf_card_eq c r₁ r₂
      · rw [dif_neg hc2, PMF.mem_support_pure_iff] at hsupp
        rw [hsupp]
    rw [hcc]; exact hcard
  rw [hcardzero]

/-- **Consumer 1 — the per-`τ` real clock-zero bound from the killed affine engine, with
hypothesis surface `card = n` + `allPhase0` + arithmetic (NO absorbing `Q`).**

From a gate start `c₀ ∈ G = allPhase0 ∩ {card = n}` (in particular from any
`Phase0Initial n` start), the real `τ`-step probability that SOME clock reached
`counter = 0` is bounded by the killed affine tail PLUS the self-referential
threshold-exit prefix:

  `(K^τ) c₀ {¬noClockAtZero} ≤ (aᵗΦ_s(c₀) + b∑aⁱ) + ∑_{σ<τ} (K^σ) c₀ {1 ≤ Φ_s}`,

with `a = ofReal(1+2(eˢ−1)/n)`, `b = ofReal(e^{−s·50(L+1)})`.  No absorbing window is
required: the killed kernel substitutes for the (nonexistent) absorbing `Q ⊆ allPhase0`,
and the exit bridge `phase0Gate_exit_bridge` closes the escape.  The remaining prefix sum
is exactly the input `allPhase0_window_whp` (Gap-2) already consumes. -/
theorem phase0_clock_zero_killed_affine (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hn2 : 2 ≤ n)
    (τ : ℕ) (c₀ : Config (AgentState L K))
    (hc₀ : c₀ ∈ phase0Gate (L := L) (K := K) n) :
    (((NonuniformMajority L K).transitionKernel) ^ τ) c₀
        {c | ¬ noClockAtZero (L := L) (K := K) c}
      ≤ (ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) ^ τ
            * clockCounterPotential (L := L) (K := K) s c₀
          + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ))))
              * ∑ i ∈ Finset.range τ,
                  ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) ^ i) / 1
          + ∑ σ ∈ Finset.range τ,
              (((NonuniformMajority L K).transitionKernel) ^ σ) c₀
                {c | (1 : ℝ≥0∞) ≤ clockCounterPotential (L := L) (K := K) s c} := by
  classical
  set Kk := (NonuniformMajority L K).transitionKernel with hKk
  set Φ := clockCounterPotential (L := L) (K := K) s with hΦdef
  set G := phase0Gate (L := L) (K := K) n with hGdef
  set a := ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) with ha
  set b := ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) with hb
  -- the affine drift on G (drift proven on allPhase0 + card = n).
  have hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(Kk x) ≤ a * Φ x + b := by
    intro x hx
    obtain ⟨hall, hcard⟩ := hx
    exact clockCounterPotential_drift_affine s hs n x hcard (hcard ▸ hn2) hall
  -- the deterministic exit bridge at θ' = 1.
  have hbridge : ∀ x ∈ G, Φ x < 1 → Kk x Gᶜ = 0 := by
    intro x hx hxΦ
    exact phase0Gate_exit_bridge s n x hx hxΦ
  -- the threshold link: ¬noClockAtZero ⟹ 1 ≤ Φ.
  have hlink : {c | ¬ noClockAtZero (L := L) (K := K) c} ⊆ {c | (1 : ℝ≥0∞) ≤ Φ c} := by
    intro c hc
    exact clockCounterPotential_ge_one_of_not_noClockAtZero s c hc
  refine le_trans (measure_mono hlink) ?_
  -- apply the Stage-3 packaged window at θ = θ' = 1.
  exact real_window_killed_affine (K := Kk) (G := G) Φ a b hdrift_G 1 1
    (by norm_num) (by norm_num) hbridge τ c₀ hc₀

/-- **The pure killed Phase-0 tail (no escape) — the cleanest decaying object.**  The
KILLED walk's clock-zero mass (trajectories that STAY in the gate `G = allPhase0 ∩ {card
= n}` and end with `Φ_s ≥ 1`) is bounded by the clean affine budget
`aᵗ·Φ_s(c₀) + b·∑_{i<τ} aⁱ`, with `a = ofReal(1+2(eˢ−1)/n)`, `b =
ofReal(e^{−s·50(L+1)})`.  This is `killed_now_affine_tail` at the Phase-0
instantiation: NO `1 ≤ a` requirement (so it decays when `a < 1`), and NO absorbing `Q`.
The real-chain bound adds the escape prefix (`phase0_clock_zero_killed_affine`). -/
theorem phase0_killed_clock_zero_tail (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hn2 : 2 ≤ n)
    (τ : ℕ) (c₀ : Config (AgentState L K)) :
    (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
          (phase0Gate (L := L) (K := K) n) ^ τ) (some c₀)
        {o | (1 : ℝ≥0∞) ≤ GatedDrift.killΦ (clockCounterPotential (L := L) (K := K) s) o}
      ≤ ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) ^ τ
          * clockCounterPotential (L := L) (K := K) s c₀
        + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ))))
            * ∑ i ∈ Finset.range τ,
                ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) ^ i := by
  classical
  have hdrift_G : ∀ x ∈ phase0Gate (L := L) (K := K) n,
      ∫⁻ y, clockCounterPotential (L := L) (K := K) s y
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
              * clockCounterPotential (L := L) (K := K) s x
          + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
    intro x hx
    obtain ⟨hall, hcard⟩ := hx
    exact clockCounterPotential_drift_affine s hs n x hcard (hcard ▸ hn2) hall
  have h := GatedDrift.killed_now_affine_tail
    (K := (NonuniformMajority L K).transitionKernel)
    (G := phase0Gate (L := L) (K := K) n)
    (clockCounterPotential (L := L) (K := K) s)
    (ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)))
    (ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))))
    hdrift_G τ c₀ 1 (by norm_num) (by norm_num)
  simpa using h

end Phase0Window

/-! ## Stage 5a — Consumer 2: the absorbing-Q discharge for `topSplitWindow_whp_rectFree`.

`RoleSplitConcentration.topSplitWindow_whp_rectFree` carries an absorbing `Q` with
`allPhase0`, `card ≥ 2`, `LedgerInv`.  Its drift is MULTIPLICATIVE (`coshPot_drift`, rate
`cosh s ≥ 1`, immigration `b = 0`).  The killed engine handles `b = 0` as the clean
special case of `killed_now_affine_tail`.  The absorbing-`Q` requirement is replaced by
the gate

  `G_top := allPhase0 ∩ {card = n} ∩ NoAssignedMcrConfig ∩ LedgerInv`,

which is one-step-closed under the killed kernel EXCEPT for the `allPhase0` exit:
`LedgerInv` is preserved (`LedgerInv_stepOrSelf`), `NoAssignedMcrConfig` is preserved
(`NoAssignedMcrConfig_stepOrSelf`), cardinality is preserved (`stepOrSelf_card_eq`), and
the only remaining way to leave `G_top` is the `allPhase0` exit, which by
`det_phase0_exit` forces a clock at `counter = 0` — the CLOCK-potential threshold event
`{1 ≤ Φ_clock}` (a DIFFERENT potential from `coshPot`).  So the escape is exactly the
Phase-0 clock-zero window (Consumer 1), and the in-gate tail is the b=0 killed cosh tail.

We deliver (i) the gate exit bridge (`topGate_exit_bridge`) showing exit ⟹ clock-zero
threshold, and (ii) the b=0 killed cosh tail (`top_killed_cosh_tail`).  Together they
convert the absorbing-`Q` hypothesis into killed-tail + (Phase-0) escape. -/

namespace RoleSplitConcentration

open GatedDrift

variable {L K : ℕ}

/-- The Consumer-2 killed gate.  All four conjuncts are protocol-provable along the
surviving trajectory; the `allPhase0` conjunct is the one the killed kernel removes. -/
def topGate (n : ℕ) : Set (Config (AgentState L K)) :=
  {c | Phase0Window.allPhase0 (L := L) (K := K) c ∧ Multiset.card c = n
        ∧ NoAssignedMcrConfig (L := L) (K := K) c ∧ LedgerInv (L := L) (K := K) c}

/-- **The Consumer-2 gate exit bridge.**  From a gate config whose CLOCK potential is
below `1` (hence `noClockAtZero`), the real Doty kernel cannot leave `G_top`: all four
conjuncts are one-step preserved — `allPhase0` via
`transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero`, `card` via `stepOrSelf_card_eq`,
`NoAssignedMcrConfig` via `NoAssignedMcrConfig_stepOrSelf`, `LedgerInv` via
`LedgerInv_stepOrSelf`.  So the `G_topᶜ` mass is `0`: the `q = 0` exit bridge with EXIT
threshold the clock-potential threshold `θ' = 1`. -/
theorem topGate_exit_bridge (sc : ℝ) (n : ℕ)
    (c : Config (AgentState L K)) (hc : c ∈ topGate (L := L) (K := K) n)
    (hΦ : Phase0Window.clockCounterPotential (L := L) (K := K) sc c < 1) :
    (NonuniformMajority L K).transitionKernel c (topGate (L := L) (K := K) n)ᶜ = 0 := by
  classical
  obtain ⟨hall, hcard, hnomcr, hled⟩ := hc
  have hno : Phase0Window.noClockAtZero (L := L) (K := K) c := by
    by_contra hcontra
    exact absurd
      (Phase0Window.clockCounterPotential_ge_one_of_not_noClockAtZero sc c hcontra)
      (not_le.2 hΦ)
  -- Gᶜ ⊆ {¬allPhase0} ∪ {card ≠ n} ∪ {¬NoAssignedMcr} ∪ {¬LedgerInv}; each support
  -- successor satisfies all four, so the only nonzero possibility ({¬allPhase0}) is killed.
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      (topGate (L := L) (K := K) n)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.disjoint_left]
  intro c' hsupp hbad
  apply hbad
  -- decompose the support successor as a stepOrSelf and discharge all four conjuncts.
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hc2 : 2 ≤ c.card
  · rw [dif_pos hc2] at hsupp
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support _ c hc2 c' hsupp
    rw [show Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂)
          = Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ from rfl] at hr
    subst hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- allPhase0 preserved: det_phase0_exit contrapositive (allPhase0 ∧ noClockAtZero).
      by_contra hexit
      exact (Phase0Window.det_phase0_exit c r₁ r₂ hall hexit) hno
    · rw [Protocol.stepOrSelf_card_eq c r₁ r₂]; exact hcard
    · exact NoAssignedMcrConfig_stepOrSelf c r₁ r₂ hall hnomcr
    · exact LedgerInv_stepOrSelf c r₁ r₂ hall hnomcr hled
  · rw [dif_neg hc2, PMF.mem_support_pure_iff] at hsupp
    subst hsupp
    exact ⟨hall, hcard, hnomcr, hled⟩

/-- **The Consumer-2 killed cosh tail (b = 0 special case).**  On the gate `G_top`, the
multiplicative cosh drift `coshPot_drift` (immigration `b = 0`) holds (its inward residual
is supplied by `inwardResidual_of_ledger` + `rectangleResidual_of_allPhase0`).  Feeding it
into `killed_now_affine_tail` with `b = 0` gives the killed cosh tail

  `(killK_now^T)(some c₀) {θ ≤ killΦ coshPot} ≤ (cosh s)^T · coshPot(c₀) / θ`

at any threshold `θ`.  The absorbing `Q` is GONE: the in-gate tail is bounded with no
absorption hypothesis, and the gate's only exit is the (killed) `allPhase0` breach. -/
theorem top_killed_cosh_tail (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hn2 : 2 ≤ n)
    (T : ℕ) (c₀ : Config (AgentState L K)) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (killK_now (NonuniformMajority L K).transitionKernel (topGate (L := L) (K := K) n) ^ T)
        (some c₀) {o | θ ≤ killΦ (coshPot (L := L) (K := K) s) o}
      ≤ ENNReal.ofReal (Real.cosh s) ^ T * coshPot (L := L) (K := K) s c₀ / θ := by
  classical
  have hdrift_G : ∀ x ∈ topGate (L := L) (K := K) n,
      ∫⁻ y, coshPot (L := L) (K := K) s y
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ ENNReal.ofReal (Real.cosh s) * coshPot (L := L) (K := K) s x + 0 := by
    intro x hx
    obtain ⟨hall, hcard, _hnomcr, hled⟩ := hx
    rw [add_zero]
    have hc2 : 2 ≤ Multiset.card x := hcard ▸ hn2
    have hrect := rectangleResidual_of_allPhase0 x hc2 hall
    have hinw := inwardResidual_of_ledger s hs x hc2 hall hled hrect
    exact coshPot_drift s hs x hc2 hall hinw
  have h := killed_now_affine_tail
    (K := (NonuniformMajority L K).transitionKernel)
    (G := topGate (L := L) (K := K) n)
    (coshPot (L := L) (K := K) s)
    (ENNReal.ofReal (Real.cosh s)) 0 hdrift_G T c₀ θ hθ0 hθtop
  -- the b = 0 term `0 * ∑ aⁱ` vanishes.
  simpa using h

end RoleSplitConcentration

/-! ## Stage 5b — Consumer 3: the CONTRACTIVE `r < 1` mid-band prefix engine lemma.

`FloorPrefix`'s finding 3: the gated engines (`gated_real_tail_full`) require `1 ≤ r`,
so the mid-band tail is the NON-decaying escape form `t·η + rᵗΦx/θ` — useless for the
genuinely-contractive `r < 1` mid-band (`εmid`/`εlate`).  As established in this file's
header, the `1 ≤ r` was SPURIOUS.  The killed affine engine `killed_now_affine_tail`
takes `a ≥ 0` ARBITRARY, so for `a = r < 1` the killed mid-band tail GENUINELY decays as
`rᵗ`.  We deliver the exact-shape engine lemma `midBand_killed_contractive_tail`: the
killed pool-MGF tail at any rate `r` (in particular `r < 1`) and any immigration `b ≥ 0`.

`FloorPrefix.midBand_gated_tail` should be re-cut against THIS lemma: instantiate
`Φ := poolExpNeg s`, `a := r` (the Stage-2 mid-band contraction rate, which is `< 1`),
`b := 0` (the pool drift is purely multiplicative), `θ := exp(-s·a₀)`; the killed tail is
`rᵗ·poolExpNeg(x)/θ`, decaying, and the real prefix `εmid` is its aggregate via
`real_le_killed_affine_tail_add_escape` + the floor escape bridge.  No `1 ≤ r`. -/

namespace FloorPrefix

open GatedDrift

variable {L K : ℕ}

/-- **The contractive mid-band killed pool tail (`r < 1` allowed).**  For ANY rate `r ≥ 0`
(in particular `r < 1`) and immigration `b ≥ 0`, if the pool-MGF `poolExpNeg s` satisfies
the affine drift `∫⁻ poolExpNeg s d(K x) ≤ r·poolExpNeg s x + b` on the mid-band gate `G`,
then the killed walk's pool-deficit tail is

  `(killK_now^t)(some x) {θ ≤ killΦ (poolExpNeg s)} ≤ (rᵗ·poolExpNeg s x + b∑rⁱ)/θ`.

With `r < 1` this DECAYS — the contractive mid-band tail `FloorPrefix` needs but the
old `1 ≤ r`-gated engine could not provide.  This is `killed_now_affine_tail` at the
pool-MGF instantiation; the `b = 0` special case gives the clean `rᵗ·poolExpNeg/θ`. -/
theorem midBand_killed_contractive_tail (s : ℝ) (G : Set (Config (AgentState L K)))
    (r b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G,
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ r * poolExpNeg (L := L) (K := K) s x + b)
    (t : ℕ) (x : Config (AgentState L K)) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (killK_now (NonuniformMajority L K).transitionKernel G ^ t) (some x)
        {o | θ ≤ killΦ (poolExpNeg (L := L) (K := K) s) o}
      ≤ (r ^ t * poolExpNeg (L := L) (K := K) s x
          + b * ∑ i ∈ Finset.range t, r ^ i) / θ :=
  killed_now_affine_tail (K := (NonuniformMajority L K).transitionKernel) (G := G)
    (poolExpNeg (L := L) (K := K) s) r b hdrift_G t x θ hθ0 hθtop

/-- **The contractive mid-band REAL tail (`r < 1`), killed + escape.**  The real
pool-deficit mass is the contractive killed tail PLUS the floor escape (the gate breach).
For `r < 1` the killed term decays as `rᵗ`; the escape is the gate-leaving mass, bounded
by the deterministic floor-exit bridge (the consumer's `S`-side prefix).  This is the
exact-shape feeder for `floor_prefix_le`'s `εmid` with a GENUINELY decaying leading term —
no `1 ≤ r`. -/
theorem midBand_real_contractive_tail (s : ℝ) (G : Set (Config (AgentState L K)))
    (r b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G,
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ r * poolExpNeg (L := L) (K := K) s x + b)
    (t : ℕ) (x : Config (AgentState L K)) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (((NonuniformMajority L K).transitionKernel) ^ t) x
        {c | θ ≤ poolExpNeg (L := L) (K := K) s c}
      ≤ (r ^ t * poolExpNeg (L := L) (K := K) s x
            + b * ∑ i ∈ Finset.range t, r ^ i) / θ
          + (killK_now (NonuniformMajority L K).transitionKernel G ^ t) (some x)
              {(none : Option (Config (AgentState L K)))} := by
  exact real_le_killed_affine_tail_add_escape
    (K := (NonuniformMajority L K).transitionKernel) (G := G)
    (poolExpNeg (L := L) (K := K) s) r b hdrift_G t x θ hθ0 hθtop

end FloorPrefix

end ExactMajority
