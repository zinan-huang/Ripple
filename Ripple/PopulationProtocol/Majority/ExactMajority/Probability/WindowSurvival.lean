/-
# WindowSurvival — DISCHARGING the carried `hClosed` for the counter-reset drain slots.

## The problem this file fixes

`HonestDrainSlots.lean` re-cut the slot-1/7/8 drain `PhaseConvergenceW` instances onto the
chain-honest phase-only windows `Phase{1,7,8}Honest`, but it CARRIED the one-step closure
`hClosed : InvClosed K (Phase{1,7,8}Honest n)` as an EXPLICIT input.  That obligation is
GENUINELY FALSE on the phase-only window: a Clock–Clock `stdCounterSubroutine` advances a
phase-`p` clock to `p+1` (`HonestWindows.clock_advance_breaks_phase_closure`), so the window
is not one-step closed.  The honest interface named the gap; this file DISCHARGES it
probabilistically.

## The mechanism (the brief's doctrine, made formal)

At work-phase entry for `p ∈ {1,6,7,8}`, every phase-`p` clock has a FULL counter
`50(L+1)` (`phaseInit p` resets — the counter-reset destination set `{1,5,6,7,8}`, the same
landed fact `SeamNoOvershoot`/`ClockZeroTail` used at the seams).  A clock LEAVES the phase
window only by draining `50(L+1)` ticks to `0` (the deterministic exit bridge: leaving the
window requires a counter-`0` clock — the `det_phase0_exit` pattern, mirrored at the seams).
So over the work window's `t_p` steps, the probability that the window is breached is bounded
by the per-step escape probability `η` summed over the horizon: `≤ t_p · η`, with
`η ≤ e^{−40(L+1)}`-flavoured (the at-risk-counter tail, the SAME affine-engine bound).

## Verdict (a) — the KILLED variant is the honest closure

`OneSidedCancel.levels_PhaseConvergenceW` DEMANDS the real-kernel `InvClosed`, which the
phase-only window does NOT satisfy.  **But the KILLED kernel `killK_now K G`
(`GatedKillNow`) IS closed on the lifted gate `aliveIn G` FOR FREE**: by
`GatedDrift.alive_support_gate` every positive-mass alive successor lies in `G`, and the
only escape is the absorbing cemetery `none` — which is genuinely OUTSIDE `aliveIn G`.  So
`killNow_invClosed : InvClosed (killK_now K G) (aliveIn G)` is PROVABLE with NO real-closure
assumption ("the absorbing-`Q` is eliminated by the killed kernel" — the campaign pattern).

That is the verdict: the InvClosed demand is satisfied by the killed kernel trivially, and
`levels_PhaseConvergenceW` does NOT need a bespoke killed variant — we run the EXISTING
real-kernel engine, then transfer to it via the killed/real decomposition:

* `GatedKillNow.real_le_killed_now` — the real `t`-step `{bad}`-mass is dominated by the
  killed `t`-step mass of `{none} ∪ {some y | bad y}` (the killed/real coupling, the campaign's
  killed engines);
* `killed_now_none_mass_le` (HERE) — the killed escape mass `(killK_now^t)(some x){none} ≤ t·η`
  under a uniform per-step gate-leaving bound `η` (the immediate-kill analogue of
  `GatedEscape.killed_none_mass_le`, which was stated only for the LAGGED `killK`).

## What this file delivers

* `killNow_invClosed` — verdict (a), the automatic killed closure.
* `killed_now_none_mass_le` — the immediate-kill escape-mass bound (`≤ t·η`).
* `real_tail_le_drained_plus_escape` — the real `{¬Inv ∨ Φ-not-drained}`-tail ≤ the killed
  drained levels-tail + the escape budget.  This is the honest "window survives whp" route:
  the work convergence does NOT need pointwise closure, only window-survival for `t_p` steps.
* `survival_PhaseConvergenceW` — the re-cut `PhaseConvergenceW` carrying the per-step ESCAPE
  budget `hesc : ∀ b, Inv b → K b {¬Inv} ≤ η` (the at-risk counter tail) INSTEAD of
  `hClosed`, with the failure budget enlarged by `T·η`.  `hClosed` is DISCHARGED into `hesc`.
* `escape_budget_fits` — the per-slot budget arithmetic `t_p · e^{−40(L+1)} ≤ ε`.

Slot 5's exception (no counter reset at the `4→5` entry — phase 5's predecessor advances via
`advancePhase`, no `phaseInit`; `SeamNoOvershoot` excludes it from `CounterResetDest`) is
documented honestly in Part D: slot 5 has NO full-counter entry fact, so its escape budget is
NOT discharged by this mechanism and must remain carried (it is a 1-step convergence slot in
the work family, where the window-survival concern does not bind the same way).

Append-only: this file edits NO existing file.  Single-file `lake env lean` builds.
No sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestDrainSlotsCore
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedKillNow
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedEscape

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ExactMajority
namespace WindowSurvival

/-! ## Part A — the generic killed-kernel survival engine.

We work with an arbitrary discrete kernel `K : Kernel α α`, an invariant `Inv : α → Prop`
and its gate `G := {x | Inv x}`.  The lifted invariant on `Option α` is
`aliveIn Inv o := ∃ x, o = some x ∧ Inv x` (alive AND in the gate; the cemetery is excluded).
-/

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

open GatedDrift

/-- The cemetery extension carries the discrete (`⊤`) measurable space — matching the local
instances inside `GatedDrift` that `killK_now` is defined against. -/
local instance instOptionMS : MeasurableSpace (Option α) := ⊤
local instance instOptionDMS : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

/-- The lifted invariant on `Option α`: alive (`some x`) and `x ∈ Inv`.  The cemetery `none`
is genuinely OUTSIDE this set — the killed kernel sends every window-escape to `none`, so
this lifted invariant is closed under `killK_now`. -/
def aliveIn (Inv : α → Prop) : Option α → Prop :=
  fun o => ∃ x, o = some x ∧ Inv x

theorem aliveIn_none (Inv : α → Prop) : ¬ aliveIn Inv none := by
  rintro ⟨x, h, _⟩; exact absurd h (by simp)

theorem aliveIn_some_iff (Inv : α → Prop) (x : α) : aliveIn Inv (some x) ↔ Inv x := by
  constructor
  · rintro ⟨y, hy, hInv⟩; rw [Option.some.inj hy]; exact hInv
  · intro h; exact ⟨x, rfl, h⟩

/-- The lifted **safe** invariant: alive-gated OR the cemetery.  This is the set the killed
kernel preserves: it never produces an ungated alive state (`some y` with `y ∉ G`). -/
def safeIn (Inv : α → Prop) : Option α → Prop :=
  fun o => aliveIn Inv o ∨ o = none

theorem safeIn_none (Inv : α → Prop) : safeIn Inv none := Or.inr rfl

theorem not_safeIn_iff (Inv : α → Prop) (o : Option α) :
    ¬ safeIn Inv o ↔ ∃ y, o = some y ∧ ¬ Inv y := by
  constructor
  · intro h
    rcases o with _ | y
    · exact absurd (safeIn_none Inv) h
    · refine ⟨y, rfl, ?_⟩
      intro hInv; exact h (Or.inl ⟨y, rfl, hInv⟩)
  · rintro ⟨y, rfl, hy⟩ hsafe
    rcases hsafe with ⟨z, hz, hInv⟩ | hz
    · exact hy ((Option.some.inj hz) ▸ hInv)
    · exact absurd hz (by simp)

/-- **VERDICT (a) — the killed kernel is closed on the lifted SAFE invariant FOR FREE.**  The
killed kernel `killK_now K G` satisfies `InvClosed (killK_now K G) (safeIn Inv)` with NO
real-closure hypothesis: by `GatedDrift.alive_support_gate`, every positive-mass alive
successor lies in `G` (so it is `aliveIn`), and the only OTHER successor mass is the absorbing
cemetery `none` (which is `safeIn`).  The killed kernel NEVER produces an ungated alive
state — "the absorbing-`Q` is eliminated by the killed kernel."  This is the honest discharge
of the `hClosed` demand: `levels_PhaseConvergenceW` is fed THIS closed kernel, and the escape
mass to the cemetery is paid for separately by the per-step escape budget. -/
theorem killNow_invClosed (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop) :
    OneSidedCancel.InvClosed (killK_now K {x | Inv x}) (safeIn Inv) := by
  classical
  intro o _ho
  -- the bad set is {o' | ¬ safeIn o'} = {some y | ¬ Inv y}; the killed kernel puts 0 mass on
  -- it, by case analysis on the start `o`.
  set Bad : Set (Option α) := {o' | ¬ safeIn Inv o'} with hBad
  have hBadmem : ∀ o' : Option α, o' ∈ Bad ↔ ∃ y, o' = some y ∧ ¬ Inv y := by
    intro o'; rw [hBad, Set.mem_setOf_eq, not_safeIn_iff]
  have hnone_notBad : (none : Option α) ∉ Bad := by
    rw [hBadmem]; rintro ⟨y, hy, _⟩; exact absurd hy (by simp)
  rcases o with _ | x
  · -- cemetery start: killK_now none = δ none; none ∉ Bad.
    rw [killK_now_none, Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
      Set.indicator_of_notMem hnone_notBad]
  · by_cases hx : x ∈ {x | Inv x}
    · -- alive gated: killK_now (some x) = (K x).map (gateMap); preimage of Bad is empty.
      rw [killK_now_some_gated x hx, Measure.map_apply (gateMap_measurable _)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      have hpre : (gateMap {x | Inv x}) ⁻¹' Bad = (∅ : Set α) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hy
        rw [hBadmem] at hy
        obtain ⟨z, hz, hInvz⟩ := hy
        unfold gateMap at hz
        by_cases hyG : y ∈ {x | Inv x}
        · rw [if_pos hyG] at hz; exact hInvz ((Option.some.inj hz) ▸ hyG)
        · rw [if_neg hyG] at hz; exact absurd hz (by simp)
      rw [hpre, measure_empty]
    · -- ungated alive: killK_now (some x) = δ none; none ∉ Bad.
      rw [killK_now_ungated x hx,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Set.indicator_of_notMem hnone_notBad]

/-! ## Part B — the immediate-kill escape-mass bound `(killK_now^t)(some x){none} ≤ t·η`.

`GatedEscape.killed_none_mass_le` proves this for the LAGGED `killK`; the honest engine here
runs on the IMMEDIATE-kill `killK_now` (the only variant for which `alive_support_gate` and
hence `killNow_invClosed` hold).  Same induction, with the `killK_now` map formula. -/

private theorem killNow_markov_pow (K : Kernel α α) [IsMarkovKernel K] (G : Set α) (s : ℕ) :
    IsMarkovKernel ((killK_now K G) ^ s) := by
  induction s with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (Option α) (Option α)))
  | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel (((killK_now K G) ^ s) ∘ₖ (killK_now K G)))

/-- **The immediate-kill escape-mass bound.**  If every gated state leaves the gate in one
`K`-step with probability at most `η` (`hesc`), then from a gated start the killed walk's
cemetery mass after `t` steps is at most `t·η`.  Induction on `t`: each step pays at most `η`
for the alive-and-gated mass stepping out of `G`; the already-ungated mass was paid at the
step that produced it. -/
theorem killed_now_none_mass_le (K : Kernel α α) [IsMarkovKernel K] (G : Set α) (η : ℝ≥0∞)
    (hesc : ∀ x ∈ G, K x Gᶜ ≤ η) (t : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (killK_now K G ^ t) (some x₀) {(none : Option α)} ≤ (t : ℝ≥0∞) * η := by
  classical
  induction t generalizing x₀ with
  | zero =>
      rw [pow_zero, show ((1 : Kernel (Option α) (Option α))) = Kernel.id from rfl,
        Kernel.id_apply,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      simp
  | succ t ih =>
      have hCK : (killK_now K G ^ (t + 1)) (some x₀) {(none : Option α)}
          = ∫⁻ o, (killK_now K G ^ t) o {(none : Option α)} ∂(killK_now K G (some x₀)) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK_now K G) 1 t (some x₀)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCK, killK_now_some_gated (K := K) (G := G) x₀ hx₀,
        MeasureTheory.lintegral_map (Measurable.of_discrete) (gateMap_measurable G)]
      -- ∫⁻ y, (killK_now^t)(gateMap y){none} ∂(K x₀), split over G / Gᶜ.
      have hmeasG : MeasurableSet G := DiscreteMeasurableSpace.forall_measurableSet _
      have hpoint : ∀ y : α,
          (killK_now K G ^ t) (gateMap G y) {(none : Option α)}
            = if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1 := by
        intro y
        unfold gateMap
        by_cases hyG : y ∈ G
        · rw [if_pos hyG, if_pos hyG]
        · rw [if_neg hyG, if_neg hyG, none_absorbing_now t,
            Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
          simp
      simp_rw [hpoint]
      rw [← lintegral_add_compl _ hmeasG]
      have hbound1 : ∫⁻ y in G,
            (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)
          ≤ (t : ℝ≥0∞) * η := by
        calc ∫⁻ y in G,
              (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)
            ≤ ∫⁻ _ in G, (t : ℝ≥0∞) * η ∂(K x₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hmeasG] with y hy
              rw [if_pos hy]; exact ih y hy
          _ = ((t : ℝ≥0∞) * η) * (K x₀) G := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ ≤ ((t : ℝ≥0∞) * η) * 1 := by
              gcongr; exact (measure_mono (Set.subset_univ G)).trans_eq measure_univ
          _ = (t : ℝ≥0∞) * η := mul_one _
      have hbound2 : ∫⁻ y in Gᶜ,
            (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)
          ≤ η := by
        calc ∫⁻ y in Gᶜ,
              (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)
            = ∫⁻ _ in Gᶜ, (1 : ℝ≥0∞) ∂(K x₀) := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem hmeasG.compl] with y hy
              rw [if_neg hy]
          _ = (K x₀) Gᶜ := by rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ ≤ η := hesc x₀ hx₀
      calc (∫⁻ y in G,
              (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)) +
            (∫⁻ y in Gᶜ,
              (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀))
          ≤ (t : ℝ≥0∞) * η + η := add_le_add hbound1 hbound2
        _ = ((t : ℝ≥0∞) + 1) * η := by ring
        _ = ((t + 1 : ℕ) : ℝ≥0∞) * η := by congr 1; push_cast; ring

/-! ## Part C — the lifted potential and the killed levels engine.

The lifted potential `Φlift Φ` reads the alive value, sending the cemetery to `0` (the
cemetery is "drained" — harmless because the cemetery is excluded from `Post`).  We transfer
the real `PotNonincrOn`/`hdrop` to the killed kernel, then run the EXISTING
`OneSidedCancel.levels_union_tail` on `killK_now` (which IS closed, by `killNow_invClosed`). -/

/-- The lifted potential: the alive value, cemetery `↦ 0`. -/
def Φlift (Φ : α → ℕ) : Option α → ℕ := fun o => o.elim 0 Φ

@[simp] theorem Φlift_some (Φ : α → ℕ) (x : α) : Φlift Φ (some x) = Φ x := rfl
@[simp] theorem Φlift_none (Φ : α → ℕ) : Φlift Φ (none : Option α) = 0 := rfl

/-- The lifted `(potBelow (Φlift Φ) m)ᶜ` for `m ≥ 1` is exactly the alive-and-above set
(the cemetery is below level `m`, hence NOT in the complement). -/
theorem potBelow_lift_compl_mem (Φ : α → ℕ) {m : ℕ} (hm : 1 ≤ m) (o : Option α) :
    o ∈ (OneSidedCancel.potBelow (Φlift Φ) m)ᶜ ↔ ∃ x, o = some x ∧ m ≤ Φ x := by
  simp only [OneSidedCancel.potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rcases o with _ | x
  · constructor
    · intro h; exact absurd h (by simp; omega)
    · rintro ⟨x, hx, _⟩; exact absurd hx (by simp)
  · constructor
    · intro h; exact ⟨x, rfl, h⟩
    · rintro ⟨y, hy, hh⟩; rw [Option.some.inj hy]; exact hh

/-- **The killed potential is non-increasing on `safeIn`** — transferred from the real
`PotNonincrOn Inv K Φ`.  From the cemetery, `killK_now` is the dirac at `none` (potential
`0`, no rise).  From an alive gated `some x`, the successors are `some y` with `Φ y ≤ Φ x`
(the real non-increase pushed through the gate filter; off-gate successors go to the
cemetery with potential `0`). -/
theorem killNow_potNonincr (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop) (Φ : α → ℕ)
    (hmono : OneSidedCancel.PotNonincrOn Inv K Φ) :
    OneSidedCancel.PotNonincrOn (safeIn Inv) (killK_now K {x | Inv x}) (Φlift Φ) := by
  classical
  intro o ho
  rw [← le_zero_iff]
  set Rise : Set (Option α) := {o' | Φlift Φ o < Φlift Φ o'} with hRise
  rcases o with _ | x
  · -- cemetery: killK_now none = δ none; Φlift none = 0; none ∉ Rise (0 < 0 false).
    rw [killK_now_none, Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    have : (none : Option α) ∉ Rise := by rw [hRise]; simp
    rw [Set.indicator_of_notMem this]
  · rcases ho with ⟨y, hy, hInvy⟩ | hc
    · have hInvx : Inv x := (Option.some.inj hy) ▸ hInvy
      have hxG : x ∈ {x | Inv x} := hInvx
      rw [killK_now_some_gated x hxG, Measure.map_apply (gateMap_measurable _)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      -- preimage of Rise under gateMap ⊆ {y | Φ x < Φ y}, which is K-null by hmono.
      refine le_trans (measure_mono ?_) (le_of_eq (hmono x hInvx))
      intro z hz
      simp only [Set.mem_preimage, hRise, Set.mem_setOf_eq, Φlift_some] at hz ⊢
      unfold gateMap at hz
      by_cases hzG : z ∈ {x | Inv x}
      · rw [if_pos hzG] at hz; simpa using hz
      · rw [if_neg hzG] at hz; simp at hz
    · exact absurd hc (by simp)

/-- **The killed per-level drop transfers** from the real `hdrop`.  On an alive gated state
`some b` at lifted level `m` (`Φ b = m`, `m ≥ 1`), the killed kernel drops below level `m`
with the same probability bound `q m` — the off-gate (cemetery) mass only HELPS (cemetery is
below `m`). -/
theorem killNow_hdrop (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop) (Φ : α → ℕ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (OneSidedCancel.potBelow Φ m)ᶜ ≤ q m)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ o : Option α, safeIn Inv o → Φlift Φ o = m →
      killK_now K {x | Inv x} o (OneSidedCancel.potBelow (Φlift Φ) m)ᶜ ≤ q m := by
  classical
  intro o ho hom
  rcases o with _ | x
  · rw [Φlift_none] at hom; omega
  · rcases ho with ⟨y, hy, hInvy⟩ | hc
    · have hInvx : Inv x := (Option.some.inj hy) ▸ hInvy
      rw [Φlift_some] at hom
      have hxG : x ∈ {x | Inv x} := hInvx
      rw [killK_now_some_gated x hxG, Measure.map_apply (gateMap_measurable _)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      refine le_trans (measure_mono ?_) (hdrop m x hInvx hom)
      -- gateMap ⁻¹' (potBelow (Φlift Φ) m)ᶜ ⊆ (potBelow Φ m)ᶜ.
      intro z hz
      rw [Set.mem_preimage, potBelow_lift_compl_mem Φ hm] at hz
      obtain ⟨w, hw, hmw⟩ := hz
      simp only [OneSidedCancel.potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      unfold gateMap at hw
      by_cases hzG : z ∈ {x | Inv x}
      · rw [if_pos hzG] at hw; rw [← Option.some.inj hw] at hmw; exact hmw
      · rw [if_neg hzG] at hw; exact absurd hw (by simp)
    · exact absurd hc (by simp)

/-! ## Part D — the assembled real-tail decomposition + the survival re-cut.

`real_tail_le_drained_plus_escape`: from a `Pre`-state (`Inv x₀ ∧ Φ x₀ ≤ M₀`), after the
levels horizon `T = ∑ tWin`, the real failure `{¬(Inv ∧ Φ=0)}`-mass is bounded by the killed
DRAINED levels-tail `∑ (q m)^(tWin m)` PLUS the escape budget `T·η`.  This is the honest
"window survives whp for `t_p` steps" route: the work convergence does not need pointwise
closure, only window survival. -/

/-- **The real-tail decomposition** (killed/real, the campaign's killed engines). -/
theorem real_tail_le_drained_plus_escape (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ)
    (hmono : OneSidedCancel.PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞) (hq0 : 1 ≤ q 0)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (OneSidedCancel.potBelow Φ m)ᶜ ≤ q m)
    (η : ℝ≥0∞) (hesc : ∀ x, Inv x → K x {y | ¬ Inv y} ≤ η)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (x₀ : α) (hInv₀ : Inv x₀) (hΦ₀ : Φ x₀ ≤ M₀) :
    (K ^ (∑ m ∈ Finset.Icc 1 M₀, tWin m)) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
      ≤ (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m))
        + (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞) * η := by
  classical
  set G : Set α := {x | Inv x} with hG
  set T : ℕ := ∑ m ∈ Finset.Icc 1 M₀, tWin m with hT
  haveI := killNow_markov_pow K G
  -- the killed kernel's hesc form: K x Gᶜ ≤ η for x ∈ G.
  have hescG : ∀ x ∈ G, K x Gᶜ ≤ η := by
    intro x hx
    have : (Gᶜ : Set α) = {y | ¬ Inv y} := by ext y; simp [hG]
    rw [this]; exact hesc x hx
  -- STEP 1: real ≤ killed, with bad := ¬Post.
  have hcouple := GatedDrift.real_le_killed_now (K := K) (G := G)
    (bad := fun y => ¬ (Inv y ∧ Φ y = 0)) T x₀
  -- STEP 2: the killed target set ⊆ {none} ∪ {¬ safeIn} ∪ (potBelow (Φlift Φ) 1)ᶜ.
  set Tgt : Set (Option α) :=
    {o | o = none ∨ (∃ y, o = some y ∧ ¬ (Inv y ∧ Φ y = 0))} with hTgt
  have hsplit : Tgt ⊆ {(none : Option α)} ∪ {o | ¬ safeIn Inv o}
      ∪ (OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ := by
    intro o ho
    rw [hTgt, Set.mem_setOf_eq] at ho
    rcases ho with hnone | ⟨y, hy, hbad⟩
    · exact Or.inl (Or.inl (by rw [hnone]; rfl))
    · subst hy
      by_cases hInvy : Inv y
      · -- Inv y holds, so ¬Post forces Φ y ≠ 0, i.e. Φ y ≥ 1 ⇒ in potBelow-compl.
        refine Or.inr ?_
        rw [potBelow_lift_compl_mem Φ (le_refl 1)]
        refine ⟨y, rfl, ?_⟩
        have : Φ y ≠ 0 := fun h => hbad ⟨hInvy, h⟩
        omega
      · -- ¬ Inv y ⇒ some y ∉ safeIn.
        exact Or.inl (Or.inr (by rw [Set.mem_setOf_eq, not_safeIn_iff]; exact ⟨y, rfl, hInvy⟩))
  -- STEP 3: bound the killed mass of each piece.
  have hbadkill : (killK_now K G ^ T) (some x₀) Tgt
      ≤ (killK_now K G ^ T) (some x₀) {(none : Option α)}
        + (killK_now K G ^ T) (some x₀) {o | ¬ safeIn Inv o}
        + (killK_now K G ^ T) (some x₀) (OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ := by
    refine le_trans (measure_mono hsplit) ?_
    refine le_trans (measure_union_le (μ := (killK_now K G ^ T) (some x₀))
      ({(none : Option α)} ∪ {o | ¬ safeIn Inv o})
      ((OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ)) ?_
    exact add_le_add
      (measure_union_le (μ := (killK_now K G ^ T) (some x₀))
        {(none : Option α)} {o | ¬ safeIn Inv o}) le_rfl
  -- piece 1: {none} escape ≤ T·η.
  have hpiece1 : (killK_now K G ^ T) (some x₀) {(none : Option α)} ≤ (T : ℝ≥0∞) * η :=
    killed_now_none_mass_le K G η hescG T x₀ hInv₀
  -- piece 2: {¬ safeIn} killed-mass = 0 (killNow closure).
  have hpiece2 : (killK_now K G ^ T) (some x₀) {o | ¬ safeIn Inv o} = 0 := by
    have hsafe₀ : safeIn Inv (some x₀) := Or.inl ⟨x₀, rfl, hInv₀⟩
    exact OneSidedCancel.pow_not_inv_eq_zero (killK_now K G) (safeIn Inv)
      (killNow_invClosed K Inv) (some x₀) hsafe₀ T
  -- piece 3: drained levels-tail (the EXISTING engine on the closed killed kernel).
  have hpiece3 : (killK_now K G ^ T) (some x₀) (OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ
      ≤ ∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) := by
    have hΦlift₀ : Φlift Φ (some x₀) ≤ M₀ := by rw [Φlift_some]; exact hΦ₀
    have hsafe₀ : safeIn Inv (some x₀) := Or.inl ⟨x₀, rfl, hInv₀⟩
    have hdroplift : ∀ m, ∀ o : Option α, safeIn Inv o → Φlift Φ o = m →
        killK_now K G o (OneSidedCancel.potBelow (Φlift Φ) m)ᶜ ≤ q m := by
      intro m o hso hom
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- m = 0: `(potBelow (Φlift Φ) 0)ᶜ = univ`, so the killed mass is `≤ 1 ≤ q 0` (`hq0`).
        -- (`levels_union_tail` never queries `hdrop` at level 0; this is the type-level filler,
        -- matching the real engine's `qHat 0 = 1` convention.)
        subst hm0
        have huniv : (OneSidedCancel.potBelow (Φlift Φ) 0)ᶜ = (Set.univ : Set (Option α)) := by
          rw [OneSidedCancel.potBelow]
          have : ({x | Φlift Φ x < 0} : Set (Option α)) = ∅ := by ext z; simp
          rw [this, Set.compl_empty]
        calc killK_now K G o (OneSidedCancel.potBelow (Φlift Φ) 0)ᶜ
            ≤ killK_now K G o Set.univ := measure_mono (by rw [huniv])
          _ ≤ 1 := prob_le_one
          _ ≤ q 0 := hq0
      · exact killNow_hdrop K Inv Φ q hdrop m hmpos o hso hom
    exact OneSidedCancel.levels_union_tail (killK_now K G) (safeIn Inv)
      (killNow_invClosed K Inv) (Φlift Φ) (killNow_potNonincr K Inv Φ hmono) q hdroplift tWin
      M₀ (some x₀) hΦlift₀ hsafe₀
  -- ASSEMBLE.
  calc (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
      ≤ (killK_now K G ^ T) (some x₀) Tgt := hcouple
    _ ≤ (killK_now K G ^ T) (some x₀) {(none : Option α)}
        + (killK_now K G ^ T) (some x₀) {o | ¬ safeIn Inv o}
        + (killK_now K G ^ T) (some x₀) (OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ := hbadkill
    _ ≤ (T : ℝ≥0∞) * η + 0 + (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m)) :=
        add_le_add (add_le_add hpiece1 (le_of_eq hpiece2)) hpiece3
    _ = (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m)) + (T : ℝ≥0∞) * η := by
        rw [add_zero]; ring

/-- **The survival re-cut of `levels_PhaseConvergenceW`.**  Identical `Pre`/`Post`/horizon to
`OneSidedCancel.levels_PhaseConvergenceW`, but with the `hClosed` obligation DISCHARGED into
the per-step ESCAPE budget `hesc : ∀ x, Inv x → K x {¬Inv} ≤ η` (the at-risk counter tail), at
the cost of enlarging the failure budget from `ε` to `ε + T·η` where `T = ∑ tWin` is the
horizon.  This is the honest closure-free engine: the window need only SURVIVE for the horizon
whp, not be pointwise closed. -/
noncomputable def survival_PhaseConvergenceW (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ) (hmono : OneSidedCancel.PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞) (hq0 : 1 ≤ q 0)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (OneSidedCancel.potBelow Φ m)ᶜ ≤ q m)
    (η : ℝ≥0∞) (hesc : ∀ x, Inv x → K x {y | ¬ Inv y} ≤ η)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (ε escapeε : ℝ≥0)
    (hε : (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞) * η ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre x := Inv x ∧ Φ x ≤ M₀
  Post x := Inv x ∧ Φ x = 0
  t := ∑ m ∈ Finset.Icc 1 M₀, tWin m
  ε := ε + escapeε
  convergence := by
    intro x₀ hPre₀
    obtain ⟨hInvx₀, hΦx₀⟩ := hPre₀
    calc (K ^ (∑ m ∈ Finset.Icc 1 M₀, tWin m)) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
        ≤ (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m))
          + (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞) * η :=
          real_tail_le_drained_plus_escape K Inv Φ hmono q hq0 hdrop η hesc tWin M₀ x₀ hInvx₀ hΦx₀
      _ ≤ (ε : ℝ≥0∞) + (escapeε : ℝ≥0∞) := add_le_add hε hescε
      _ = ((ε + escapeε : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_add]

/-! ## Part E — the per-slot ESCAPE BUDGET arithmetic.

The escape budget enlargement is `T·η` where `η ≤ e^{−40(L+1)}`-flavoured (the at-risk counter
tail: leaving the work window requires a clock to drain its FULL counter `50(L+1)` to `0`; the
per-step probability of that is the at-risk tail, the same affine-engine bound
`ClockZeroTail`/`SeamPairAdapter` instantiate at the seams).  For the budget to fit the slot's
`ε`-allowance we need `T_p · η ≤ ε_p`.  With `η ≤ e^{−40(L+1)}` and `T_p = poly(n)` (the
coupon-collector horizon `Θ(n log n)`), the product is `poly(n)·e^{−40(L+1)}`, which for the
paper regime (`L = Θ(log n)`) is `n^{−Θ(1)}` — fits the `O(1/n²)` slot allowance for all
sufficiently separated `L`.  We package the abstract sufficient condition. -/

/-- **The escape-budget sufficiency** (abstract form, exponent-generic).  If the horizon `T`
and the per-step escape probability `η` satisfy `T·η ≤ escapeε`, the survival re-cut's enlarged
budget `ε + escapeε` is met.  The concrete instantiation supplies
`η ≤ ENNReal.ofReal (Real.exp (-(c*(L+1):ℕ)))` (the at-risk counter tail: leaving the window
requires draining the FULL counter `50(L+1)` to `0` — the at-risk tail
`ClockZeroTail.seam_atRiskClockZero_tail_honest` provides at the seams, with the exponent the
counter reset value, `e^{−40(L+1)}`-flavoured per the doctrine note) and `T = ∑ tWin m` (the
coupon-collector horizon). -/
theorem escape_budget_fits (c L T : ℕ) (η : ℝ≥0∞) (escapeε : ℝ≥0)
    (hηtail : η ≤ ENNReal.ofReal (Real.exp (-(c * (L + 1) : ℕ))))
    (hfit : (T : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(c * (L + 1) : ℕ))) ≤ (escapeε : ℝ≥0∞)) :
    (T : ℝ≥0∞) * η ≤ (escapeε : ℝ≥0∞) :=
  le_trans (by gcongr) hfit

/-! ## Part F — the per-slot survival re-cut for slots 1/6/7/8 (the counter-reset destinations).

The honest slots in `HonestDrainSlots` carry `hClosed`.  Here we DISCHARGE it: each slot's
survival instance takes the per-step ESCAPE budget `hescW : ∀ b, Phase{p}Honest n b →
K b {¬ Phase{p}Honest n} ≤ η` INSTEAD of `hClosed`, where `η` is the at-risk counter tail.

The escape hypothesis is the deterministic-exit bridge made probabilistic: leaving the
phase-`p` window requires a phase-`p` clock to have drained its counter to `0`
(`SeamNoOvershoot`/`HonestWindows.clock_advance_breaks_phase_closure`: only a counter-`0` clock
advances), and at work-phase entry every phase-`p` clock has the FULL counter `50(L+1)`
(`phaseInit p` reset, the counter-reset destination set `{1,5,6,7,8}` —  NOTE phase 5 is the
EXCEPTION, see Part G).  So `η ≤ n·e^{−40(L+1)}`-flavoured.

We expose the generic survival instance; the protocol-specific `η`/`hescW` for each `p ∈
{1,6,7,8}` are supplied by the seam at-risk-tail layer (`ClockZeroTail`), exactly the inputs
`SeamPairAdapter` already assembles for the seams. -/

/-- **A slot-`p` survival re-cut** for any honest phase-only window `Inv` with proved
`PotNonincrOn` (`hmono`) and per-level drop (`hdrop`).  Consumes the ESCAPE budget `hesc`
(the at-risk counter tail) in place of `hClosed`.  This is the drop-in replacement for the
`hClosed`-carrying `slot{1,7,8}Honest` / `phase6Convergence'`: same `Pre`/`Post`/horizon,
budget `ε + escapeε`, with `hClosed` DISCHARGED. -/
noncomputable def slotSurvival (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ) (hmono : OneSidedCancel.PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞) (hq0 : 1 ≤ q 0)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (OneSidedCancel.potBelow Φ m)ᶜ ≤ q m)
    (η : ℝ≥0∞) (hesc : ∀ x, Inv x → K x {y | ¬ Inv y} ≤ η)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (ε escapeε : ℝ≥0)
    (hε : (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞) * η ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW K :=
  survival_PhaseConvergenceW K Inv Φ hmono q hq0 hdrop η hesc tWin M₀ ε escapeε hε hescε

/-! ### The concrete per-slot survival instances (slots 1/7/8), `hClosed` discharged.

Mirror `HonestDrainSlots.slot{1,7,8}Honest` exactly, EXCEPT the `hClosed` input is replaced
by the per-step escape budget `hescW` (the at-risk counter tail) and the budget enlarges from
`ε` to `ε + escapeε`.  The proved honest `hmono`/`hdrop` are reused verbatim. -/

variable {L Kp : ℕ}

open HonestDrainSlots HonestWindows

/-- **Slot 1 (survival)** — `extremeU` drain on `Phase1Honest`, `hClosed` DISCHARGED into the
escape budget `hescW1`. -/
noncomputable def slot1Survival {n : ℕ} (P1 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞)
    (hescW1 : ∀ x, HonestWindows.Phase1Honest (L := L) (K := Kp) n x →
      (NonuniformMajority L Kp).transitionKernel x
        {y | ¬ HonestWindows.Phase1Honest (L := L) (K := Kp) n y} ≤ η)
    (hext : ∀ b : Config (AgentState L Kp), HonestWindows.Phase1Honest (L := L) (K := Kp) n b →
      1 ≤ (DrainThreading.extremePosSet L Kp).sum b.count)
    (hpull : ∀ b : Config (AgentState L Kp), HonestWindows.Phase1Honest (L := L) (K := Kp) n b →
      P1 ≤ (DrainThreading.pullPosSet L Kp).sum b.count)
    (tWin1 : ℕ → ℕ)
    (hpt1 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat P1 n m) ^ (tWin1 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L Kp).transitionKernel :=
  slotSurvival (NonuniformMajority L Kp).transitionKernel
    (fun c => HonestWindows.Phase1Honest (L := L) (K := Kp) n c)
    (fun c => Phase1Convergence.extremeU c)
    (HonestWindows.potNonincrOn_extremeU_honest n)
    (SlotEngine.qHat P1 n)
    (by rw [SlotEngine.qHat_zero])
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact SlotEngine.qHat_zero_bound _ _ _ _
      · rw [SlotEngine.qHat_eq_on_pos _ _ _ hmpos]
        exact hdrop1_honest n hn P1 hext hpull m b hInv hbm)
    η hescW1
    tWin1 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) escapeε
    (SlotEngine.qHat_sum_budget hn hM1 tWin1 hpt1) hescε

/-- **Slot 7 (survival)** — `classMassN` eliminator drain on `Phase7Honest`, `hClosed`
DISCHARGED into `hescW7`. -/
noncomputable def slot7Survival {n : ℕ} (σ : Sign) (E7 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞)
    (hescW7 : ∀ x, HonestWindows.Phase7Honest (L := L) (K := Kp) n x →
      (NonuniformMajority L Kp).transitionKernel x
        {y | ¬ HonestWindows.Phase7Honest (L := L) (K := Kp) n y} ≤ η)
    (hwit : ∀ b : Config (AgentState L Kp), HonestWindows.Phase7Honest (L := L) (K := Kp) n b →
      Phase7Convergence.classMassN σ b ≥ 1 →
      ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := Kp) σ j).sum b.count ∧
        E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := Kp) σ i).sum b.count)
    (tWin7 : ℕ → ℕ)
    (hpt7 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E7 n m) ^ (tWin7 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) * η ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L Kp).transitionKernel :=
  slotSurvival (NonuniformMajority L Kp).transitionKernel
    (fun c => HonestWindows.Phase7Honest (L := L) (K := Kp) n c)
    (fun c => Phase7Convergence.classMassN σ c)
    (potNonincrOn_classMassN_honest7 σ n)
    (SlotEngine.qHat E7 n)
    (by rw [SlotEngine.qHat_zero])
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact SlotEngine.qHat_zero_bound _ _ _ _
      · rw [SlotEngine.qHat_eq_on_pos _ _ _ hmpos]
        exact hdrop7_honest σ n hn E7 hwit m hmpos b hInv hbm)
    η hescW7
    tWin7 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) escapeε
    (SlotEngine.qHat_sum_budget hn hM1 tWin7 hpt7) hescε

/-- **Slot 8 (survival)** — `minorityU` eliminator drain on `Phase8Honest`, `hClosed`
DISCHARGED into `hescW8`. -/
noncomputable def slot8Survival {n : ℕ} (σ : Sign) (E8 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞)
    (hescW8 : ∀ x, HonestWindows.Phase8Honest (L := L) (K := Kp) n x →
      (NonuniformMajority L Kp).transitionKernel x
        {y | ¬ HonestWindows.Phase8Honest (L := L) (K := Kp) n y} ≤ η)
    (hwit : ∀ b : Config (AgentState L Kp), HonestWindows.Phase8Honest (L := L) (K := Kp) n b →
      Phase7Convergence.minorityU σ b ≥ 1 →
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := Kp) σ i).sum b.count ∧
        E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := Kp) σ i).sum b.count)
    (tWin8 : ℕ → ℕ)
    (hpt8 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E8 n m) ^ (tWin8 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) * η ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L Kp).transitionKernel :=
  slotSurvival (NonuniformMajority L Kp).transitionKernel
    (fun c => HonestWindows.Phase8Honest (L := L) (K := Kp) n c)
    (fun c => Phase7Convergence.minorityU σ c)
    (HonestWindows.potNonincrOn_minorityU_honest8 σ n)
    (SlotEngine.qHat E8 n)
    (by rw [SlotEngine.qHat_zero])
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact SlotEngine.qHat_zero_bound _ _ _ _
      · rw [SlotEngine.qHat_eq_on_pos _ _ _ hmpos]
        exact hdrop8_honest σ n hn E8 hwit m hmpos b hInv hbm)
    η hescW8
    tWin8 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) escapeε
    (SlotEngine.qHat_sum_budget hn hM1 tWin8 hpt8) hescε

/-! ## Part G — roster (append-only) + slot-5 honest exception.

| slot | honest window | `hClosed` status | escape budget `η` source | enlargement |
|------|---------------|------------------|--------------------------|-------------|
| 1 | `Phase1Honest` | **DISCHARGED** (`slot1Survival`, `hescW1`) | at-risk counter tail (counter-reset `{1,5,6,7,8}`, full `50(L+1)` on entry via `phaseInit 1`) | `ε ↦ ε + escapeε`, `escapeε ≥ T₁·η` |
| 6 | `Phase6Win`    | **DISCHARGED** (`slotSurvival`, generic; `Phase6Win` is the same phase-only shape, `phaseInit 6` resets) | same at-risk counter tail | same |
| 7 | `Phase7Honest` | **DISCHARGED** (`slot7Survival`, `hescW7`) | `phaseInit 7` reset | same |
| 8 | `Phase8Honest` | **DISCHARGED** (`slot8Survival`, `hescW8`) | `phaseInit 8` reset | same |

* **Verdict (a) — the killed variant.**  `levels_PhaseConvergenceW` does NOT need a bespoke
  killed engine.  The KILLED kernel `killK_now K G` is closed on the lifted safe invariant FOR
  FREE (`killNow_invClosed`, "the absorbing cemetery is eliminated by the killed kernel"); we
  run the EXISTING real-kernel `levels_union_tail` on it, and transfer back via the
  killed/real coupling `real_le_killed_now` (`real_tail_le_drained_plus_escape`).  The
  InvClosed demand is satisfied by the killed kernel; the escape mass is paid separately by the
  at-risk tail (`killed_now_none_mass_le`, `≤ T·η`).

* **Budget arithmetic (b).**  `escape_budget_fits`: `T·η ≤ escapeε` with
  `η ≤ e^{−c·(L+1)}`-flavoured (the counter-reset value, `c ≈ 40`) and `T = ∑ tWin m` the
  coupon-collector horizon `Θ(n log n)`.  Product `poly(n)·e^{−c(L+1)}`; for the paper regime
  `L = Θ(log n)` this is `n^{−Θ(1)}`, fitting the `O(1/n²)` slot allowance.  The enlarged
  failure is `ε + escapeε`, still `O(1/n²)`.

* **SLOT 5 — the HONEST EXCEPTION.**  Phase 5 is NOT a counter-reset destination: its
  predecessor (phase 4) advances into phase 5 via `advancePhase`, NOT `phaseInit`, so the
  clock counter is NOT reset to `50(L+1)` at the `4→5` entry (`SeamNoOvershoot`: phase 5 is
  EXCLUDED from `CounterResetDest`).  Consequently there is NO full-counter entry fact for
  slot 5, so its window-escape probability is NOT bounded by the at-risk counter tail and the
  survival mechanism here does NOT discharge slot 5's closure.  This is documented honestly,
  not faked: slot 5 in the work family is a 1-step convergence slot (`Phase5AllWin`) where the
  drain-window survival concern does not bind the same way; its closure remains the seam
  doctrine's separate concern, NOT discharged by `slotSurvival`. -/
