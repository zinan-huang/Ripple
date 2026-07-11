import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedEscape

/-!
# GatedKillNow — the IMMEDIATE-kill gated kernel (Doty §6 killed-minute fix)

`GatedDrift.killK` has a documented one-step LAG: from an alive gated state `some x`
(`x ∈ G`) it steps to `some y` even when `y ∉ G`; the kill registers only at the NEXT
step.  For the killed-minute brick this lag is FATAL: it makes "alive states satisfy the
gate" FALSE, so guarded potentials / `none ∈ Post` arguments break (see the killed-minute
blueprint).

This file builds the IMMEDIATE-kill variant `killK_now K G`: from `some x` with `x ∈ G`,
the `K`-successor `y` is pushed through `fun y => if y ∈ G then some y else none` — so
off-gate successors are sent to the cemetery `none` IN THE SAME STEP.  Now
`alive_support_gate` ("any alive successor lies in `G`") is TRUE by construction — the
fix the blueprint calls for.

We mirror the `GatedGeometricDrift`/`GatedEscape` proof patterns: the local discrete
`Option α` instances, the `Kernel.piecewise`/`map`/`comap` machinery, the
`Kernel.pow_add_apply_eq_lintegral` peeling, and the `real_le_killed` / escape induction.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

namespace GatedDrift

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

/-- The cemetery extension carries the discrete (`⊤`) measurable space. -/
local instance instOptionMSnow : MeasurableSpace (Option α) := ⊤
local instance instOptionDMSnow : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

/-- The gate-filtering map: keep `y` alive only if `y ∈ G`, else send it to the cemetery. -/
noncomputable def gateMap (G : Set α) : α → Option α :=
  fun y => if y ∈ G then some y else none

theorem gateMap_measurable (G : Set α) : Measurable (gateMap (α := α) G) :=
  Measurable.of_discrete

/-- The IMMEDIATE-kill gated kernel on `Option α`: alive gated states `some x` (`x ∈ G`)
step via `K` then pass through the gate filter `gateMap G` (off-gate successors die in the
same step); the cemetery `none` and ungated `some x` (`x ∉ G`) are absorbed at `none`. -/
noncomputable def killK_now (K : Kernel α α) (G : Set α) :
    Kernel (Option α) (Option α) :=
  Kernel.piecewise (s := (Option.some '' G))
    (DiscreteMeasurableSpace.forall_measurableSet _)
    ((K.map (gateMap G)).comap (fun o => o.getD default) (Measurable.of_discrete))
    (Kernel.const _ (Measure.dirac (none : Option α)))

variable {K : Kernel α α} {G : Set α}

instance [IsMarkovKernel K] : IsMarkovKernel (killK_now K G) := by
  haveI : IsMarkovKernel (K.map (gateMap G)) :=
    Kernel.IsMarkovKernel.map K (gateMap_measurable G)
  unfold killK_now
  infer_instance

/-- `killK_now` at the cemetery `none` is the dirac at `none` (absorbing). -/
theorem killK_now_none : killK_now K G none = Measure.dirac (none : Option α) := by
  unfold killK_now
  rw [Kernel.piecewise_apply, if_neg none_notMem_image, Kernel.const_apply]

/-- `killK_now` at an ungated alive state `some x` (`x ∉ G`) is the dirac at `none`. -/
theorem killK_now_ungated (x : α) (hx : x ∉ G) :
    killK_now K G (some x) = Measure.dirac (none : Option α) := by
  unfold killK_now
  rw [Kernel.piecewise_apply, if_neg (fun h => hx ((some_mem_image_iff x).1 h)),
    Kernel.const_apply]

/-- **The map formula.**  `killK_now` at an alive gated state `some x` (`x ∈ G`) is the
`K`-step pushed through the gate filter: off-gate successors go to the cemetery. -/
theorem killK_now_some_gated (x : α) (hx : x ∈ G) :
    killK_now K G (some x) = (K x).map (gateMap G) := by
  unfold killK_now
  rw [Kernel.piecewise_apply, if_pos ((some_mem_image_iff x).2 hx),
    Kernel.comap_apply, Kernel.map_apply _ (gateMap_measurable G)]
  simp only [Option.getD_some]

/-- The cemetery stays absorbing under iteration: `(killK_now^t) none = δ none`. -/
theorem none_absorbing_now [IsMarkovKernel K] (t : ℕ) :
    (killK_now K G ^ t) (none : Option α) = Measure.dirac (none : Option α) := by
  induction t with
  | zero => rw [pow_zero]; exact Kernel.id_apply none
  | succ t ih =>
      ext S hS
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral (killK_now K G) 1 t none hS, pow_one, killK_now_none,
        MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete), ih]

/-- **THE FIX — `alive_support_gate`.**  Every alive successor of `killK_now` (at ANY `o`)
that carries POSITIVE mass lies in the gate `G`.  ("Support" of a measure = positive-mass
points; we state it as `0 < killK_now K G o {some c'} → c' ∈ G`.)  This is FALSE for the
lagged `killK`; it holds by construction for the immediate-kill kernel, since off-gate
successors are filtered to the cemetery `none` within the step. -/
theorem alive_support_gate (o : Option α) (c' : α)
    (hsupp : 0 < killK_now K G o {(some c' : Option α)}) : c' ∈ G := by
  classical
  rcases o with _ | x
  · -- cemetery: killK_now none = δ none, mass on {some c'} = 0, contradiction.
    rw [killK_now_none, Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
      Set.indicator_of_notMem (by simp : (none : Option α) ∉ ({some c'} : Set (Option α)))] at hsupp
    exact absurd hsupp (lt_irrefl 0)
  · by_cases hx : x ∈ G
    · -- alive gated: mass = (K x)(gateMap⁻¹{some c'}); positive forces c' ∈ G.
      rw [killK_now_some_gated x hx, Measure.map_apply (gateMap_measurable G)
        (DiscreteMeasurableSpace.forall_measurableSet _)] at hsupp
      by_contra hc'
      have hpre : (gateMap G) ⁻¹' {(some c' : Option α)} = ∅ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro hy
        by_cases hyG : y ∈ G
        · have hy' : (some y : Option α) = some c' := by
            rw [← hy]; unfold gateMap; rw [if_pos hyG]
          exact hc' ((Option.some.inj hy') ▸ hyG)
        · have hy' : (none : Option α) = some c' := by
            rw [← hy]; unfold gateMap; rw [if_neg hyG]
          exact absurd hy' (by simp)
      rw [hpre, measure_empty] at hsupp
      exact absurd hsupp (lt_irrefl 0)
    · -- ungated alive: killK_now (some x) = δ none, mass on {some c'} = 0, contradiction.
      rw [killK_now_ungated x hx,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Set.indicator_of_notMem (by simp : (none : Option α) ∉ ({some c'} : Set (Option α)))] at hsupp
      exact absurd hsupp (lt_irrefl 0)

/-- **`real_le_killed_now`** — the immediate-kill coupling.  Same statement / induction as
`real_le_killed`: the real `t`-step mass on `{bad}` is dominated by the killed `t`-step mass
of `{none} ∪ {some y | bad y}`.  In the alive-gated successor branch the `K`-step is now
filtered through `gateMap G`: on-gate successors map to `some y` (tracked), off-gate
successors map to `none` ∈ the target set, so the inequality only improves. -/
theorem real_le_killed_now [IsMarkovKernel K] (bad : α → Prop) (t : ℕ) (x : α) :
    (K ^ t) x {y | bad y} ≤
      (killK_now K G ^ t) (some x) {o | o = none ∨ (∃ y, o = some y ∧ bad y)} := by
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
      have hCKkill : (killK_now K G ^ (t + 1)) (some x) Rset
          = ∫⁻ o, (killK_now K G ^ t) o Rset ∂(killK_now K G (some x)) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK_now K G) 1 t (some x)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCKK, hCKkill]
      by_cases hx : x ∈ G
      · rw [killK_now_some_gated (K := K) (G := G) x hx,
          MeasureTheory.lintegral_map (Measurable.of_discrete) (gateMap_measurable G)]
        refine lintegral_mono (fun y => ?_)
        -- gateMap G y = some y (y ∈ G) → IH; = none (y ∉ G) → (killK_now^t) none Rset = 1 ≥ ·
        unfold gateMap
        by_cases hyG : y ∈ G
        · rw [if_pos hyG]; exact ih y
        · rw [if_neg hyG]
          rw [none_absorbing_now t, Measure.dirac_apply' _
            (DiscreteMeasurableSpace.forall_measurableSet _),
            Set.indicator_of_mem (show (none : Option α) ∈ Rset from Or.inl rfl), Pi.one_apply]
          haveI := hMK t
          exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
      · -- ungated start: killK_now (some x) = δ none, RHS integral = (killK_now^t)(none) Rset = 1.
        rw [killK_now_ungated x hx, MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete)]
        have hrhs : (killK_now K G ^ t) (none : Option α) Rset = 1 := by
          rw [none_absorbing_now t, Measure.dirac_apply' _
            (DiscreteMeasurableSpace.forall_measurableSet _),
            Set.indicator_of_mem (show (none : Option α) ∈ Rset from Or.inl rfl), Pi.one_apply]
        rw [hrhs]
        haveI : IsMarkovKernel (K ^ t) := hMK t
        calc ∫⁻ y, (K ^ t) y {y | bad y} ∂(K x)
            ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(K x) := by
              refine lintegral_mono (fun y => ?_)
              exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
          _ = 1 := by rw [MeasureTheory.lintegral_one, measure_univ]

/-- **`killed_now_alive_le_real`** — the immediate-kill alive-domination.  The killed walk's
alive mass on a set is dominated by the real walk's mass.  Same statement / induction as
`killed_alive_le_real`; the alive-gated successor now splits through `gateMap G`, with
off-gate successors contributing `0` to the alive (`some`) target. -/
theorem killed_now_alive_le_real [IsMarkovKernel K] (A : Set α) (t : ℕ) (x₀ : α) :
    (killK_now K G ^ t) (some x₀) {o | ∃ y ∈ A, o = some y} ≤ (K ^ t) x₀ A := by
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
      have hCKk : (killK_now K G ^ (t + 1)) (some x₀) {o | ∃ y ∈ A, o = some y}
          = ∫⁻ o, (killK_now K G ^ t) o {o' | ∃ y ∈ A, o' = some y}
              ∂(killK_now K G (some x₀)) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK_now K G) 1 t (some x₀)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      have hCKr : (K ^ (t + 1)) x₀ A = ∫⁻ y, (K ^ t) y A ∂(K x₀) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral K 1 t x₀
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCKk, hCKr]
      by_cases hx : x₀ ∈ G
      · rw [killK_now_some_gated (K := K) (G := G) x₀ hx,
          MeasureTheory.lintegral_map (Measurable.of_discrete) (gateMap_measurable G)]
        refine lintegral_mono (fun y => ?_)
        unfold gateMap
        by_cases hyG : y ∈ G
        · rw [if_pos hyG]; exact ih y
        · rw [if_neg hyG]
          have hzero : (killK_now K G ^ t) (none : Option α) {o' | ∃ y ∈ A, o' = some y} = 0 := by
            rw [none_absorbing_now t,
              Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
            exact Set.indicator_of_notMem (by rintro ⟨y, _, h⟩; exact Option.some_ne_none y h.symm) _
          rw [hzero]; exact zero_le'
      · rw [killK_now_ungated x₀ hx, MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete)]
        have hzero : (killK_now K G ^ t) (none : Option α) {o' | ∃ y ∈ A, o' = some y} = 0 := by
          rw [none_absorbing_now t,
            Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
          exact Set.indicator_of_notMem (by rintro ⟨y, _, h⟩; exact Option.some_ne_none y h.symm) _
        rw [hzero]; exact zero_le'

/-- **`kill_now_escape_le_prefix_union`** — the run-long escape accounting for immediate
kill.  If from every gated state satisfying the side event `S` the one-step probability of
leaving the gate is at most `q`, then the cemetery mass after `M` steps is at most
`M·q + ∑_{τ<M} (K^τ) x₀ Sᶜ`.  For `killK_now` the escape registers IMMEDIATELY (off-gate
successors die in the SAME step), so — unlike the lagged `killK` — there is no carried-over
ungated-alive mass; the gated-successor IH carries the whole prefix sum. -/
theorem kill_now_escape_le_prefix_union [IsMarkovKernel K] (S : Set α) (q : ℝ≥0∞)
    (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q)
    (M : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (killK_now K G ^ M) (some x₀) {(none : Option α)} ≤
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
      have hCK : (killK_now K G ^ (M + 1)) (some x₀) {(none : Option α)}
          = ∫⁻ o, (killK_now K G ^ M) o {(none : Option α)} ∂(killK_now K G (some x₀)) := by
        rw [show M + 1 = 1 + M from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK_now K G) 1 M (some x₀)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCK, killK_now_some_gated (K := K) (G := G) x₀ hx₀,
        MeasureTheory.lintegral_map (Measurable.of_discrete) (gateMap_measurable G)]
      have hmeasG : MeasurableSet G := DiscreteMeasurableSpace.forall_measurableSet _
      -- split the K x₀ integral over G / Gᶜ.  On G: gateMap = some y, apply IH.
      -- On Gᶜ: gateMap = none, the killed walk is already at the cemetery (mass 1).
      rw [← lintegral_add_compl
        (fun y => (killK_now K G ^ M) (gateMap G y) {(none : Option α)}) hmeasG]
      have hbound1 : ∫⁻ y in G, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} ∂(K x₀)
          ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ (τ + 1)) x₀ Sᶜ := by
        calc ∫⁻ y in G, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} ∂(K x₀)
            ≤ ∫⁻ y in G, ((M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ τ) y Sᶜ)
                ∂(K x₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hmeasG] with y hy
              rw [show gateMap G y = some y from by unfold gateMap; rw [if_pos hy]]
              exact ih y hy
          _ ≤ ∫⁻ y, ((M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ τ) y Sᶜ)
                ∂(K x₀) := MeasureTheory.setLIntegral_le_lintegral _ _
          _ = ∫⁻ y, (M : ℝ≥0∞) * q ∂(K x₀)
              + ∫⁻ y, (∑ τ ∈ Finset.range M, (K ^ τ) y Sᶜ) ∂(K x₀) := by
              rw [MeasureTheory.lintegral_add_left (by fun_prop)]
          _ ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ (τ + 1)) x₀ Sᶜ := by
              gcongr
              · rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
              · rw [MeasureTheory.lintegral_finsetSum _
                  (fun τ _ => by fun_prop)]
                refine Finset.sum_le_sum (fun τ _ => ?_)
                rw [show τ + 1 = 1 + τ from by ring,
                  Kernel.pow_add_apply_eq_lintegral K 1 τ x₀
                    (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      have hbound2 : ∫⁻ y in Gᶜ, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} ∂(K x₀)
          ≤ q + (K ^ 0) x₀ Sᶜ := by
        -- on Gᶜ, gateMap G y = none, killed walk already dead: (killK_now^M) none {none} = 1.
        have heq : ∀ y ∈ Gᶜ, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} = 1 := by
          intro y hy
          rw [show gateMap G y = none from by unfold gateMap; rw [if_neg hy]]
          rw [none_absorbing_now M,
            Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
            Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply]
        have hle1 : ∫⁻ y in Gᶜ, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} ∂(K x₀)
            ≤ (K x₀) Gᶜ := by
          have hmeasGc : MeasurableSet Gᶜ := hmeasG.compl
          have hcalc : ∫⁻ y in Gᶜ, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} ∂(K x₀)
              = (K x₀) Gᶜ := by
            calc ∫⁻ y in Gᶜ, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} ∂(K x₀)
                = ∫⁻ _ in Gᶜ, (1 : ℝ≥0∞) ∂(K x₀) := by
                  apply lintegral_congr_ae
                  filter_upwards [ae_restrict_mem hmeasGc] with y hy
                  exact heq y hy
              _ = (K x₀) Gᶜ := by
                  rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, one_mul]
          exact le_of_eq hcalc
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
      have hsum : ∑ τ ∈ Finset.range (M + 1), (K ^ τ) x₀ Sᶜ
          = (K ^ 0) x₀ Sᶜ + ∑ τ ∈ Finset.range M, (K ^ (τ + 1)) x₀ Sᶜ := by
        rw [Finset.sum_range_succ']
        exact add_comm _ _
      calc (∫⁻ y in G, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} ∂(K x₀)) +
            (∫⁻ y in Gᶜ, (killK_now K G ^ M) (gateMap G y) {(none : Option α)} ∂(K x₀))
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

end GatedDrift

end ExactMajority
