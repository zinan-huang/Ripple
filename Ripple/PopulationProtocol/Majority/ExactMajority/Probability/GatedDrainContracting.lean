/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GatedDrainContracting — the CONTRACTING (`r < 1`) slot-5 sampling drain.

This append-only file edits NO existing file.  It fixes the VACUOUS drain term of
`Phase5SurvivalCorrect.phase5_survival_correct`: that theorem composes the slot-5 survival with the
gated geometric engine `GatedDrift.gated_real_tail`, which carries `hr : 1 ≤ r` and yields a drain
term `r^t · Φ / θ`.  With `r ≥ 1` the term GROWS (or is constant) — it is NOT a drain.  A REAL drain
needs `r < 1`, so `r^t → 0` and the tail genuinely shrinks.

## Step 1 — the `hr : 1 ≤ r` is SPURIOUS; generalized `_anyr` engine

The base bound `(K^t) x {θ ≤ Φ} ≤ r^t · Φ x / θ` is a pure Markov-inequality + drift-iteration:
`E[Φ_t] ≤ r^t · Φ_0` (`Supermartingale.geometric_drift_tail`, which carries NO `hr`, depends on
`PopProtoCommon.lintegral_geometric_decay`, also NO `hr`), then Markov `P[Φ_t ≥ θ] ≤ E[Φ_t]/θ`.  The
ONLY place `hr` enters the killed-kernel chain is `GatedDrift.killK_drift`, in the cemetery/off-gate
branches where the goal is `0 ≤ r · killΦ Φ o` — which `positivity` proves for ANY `r : ℝ≥0∞` (it
NEVER consults `hr`).  We rebuild the chain `killK_drift_anyr → killed_geometric_tail_anyr →
gated_real_tail_anyr` WITHOUT `hr`, proving the SAME `r^t · Φ x / θ` bound for arbitrary `r`.  The
existing `r ≥ 1` lemmas are untouched.

## Step 2 — the slot-5 CONTRACTING drift (`r < 1`)

`U = ReserveSampling.unsampledReserveU` drops with per-step probability `≥ ρ` on the gate (the
`{c' | U c' + 1 ≤ U c}` drop event, from `SamplingConcentration.sampleDrain_prob_floor`) and is
NEVER-increasing on the gate (`OneSidedCancel.PotNonincrOn`).  The MGF potential
`Φ_U c = ofReal(exp(s · U c))` (`s > 0`) then satisfies the CONTRACTING drift

  `∀ x ∈ G, ∫⁻ y, Φ_U y ∂(K x) ≤ r · Φ_U x`,  with `r = 1 − ρ·(1 − e^{−s}) < 1`.

Mechanism (the MIRROR of `ClockDepletionCoupling.expPot_drift`, but for a DECREMENT so the factor is
`< 1` not `> 1`): on the drop event (mass `≥ ρ`) `U → U−1` so `Φ_U → Φ_U · e^{−s}`; off it `U` does
not increase (a.e.) so `Φ_U` does not increase; hence
`∫ Φ_U dK ≤ Φ_U·(e^{−s}·p + (1−p))` with `p = K(drop) ≥ ρ`, and since `e^{−s} < 1` this is decreasing
in `p`, so `≤ Φ_U·(1 − ρ(1−e^{−s})) = r·Φ_U`.  `r < 1` because `ρ > 0` and `e^{−s} < 1`.

## Step 3 — the composed slot-5 survival with `r < 1` (genuinely shrinking)

`phase5_survival_contracting` re-instantiates the slot-5 survival using `gated_real_tail_anyr` with
the contracting `r < 1` drift, composed with the cumulative clock tail and confinement tail.  The
drain term `r^T·Φ_U(c₀)/θ` now SHRINKS; `drain_term_shrinks` proves it is `≤ ε` for `T` large enough
(`r^T → 0`).  This is the genuinely-non-vacuous drain, NOT the vacuous `r ≥ 1` version.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedGeometricDrift
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedEscape
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase5ConfinementCompose

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

/-! ## Step 1 — the generalized `_anyr` engine (no `hr : 1 ≤ r`).

The drain bound `r^t·Φ x/θ` holds for ANY `r : ℝ≥0∞`.  The `hr : 1 ≤ r` carried by
`GatedDrift.killK_drift` / `killed_geometric_tail` / `gated_real_tail` is spurious: it is used only
to discharge `0 ≤ r·killΦ Φ o` in the dead branches, which is a `positivity` fact for any `r`. -/

namespace GatedDrift

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

/-- The cemetery extension carries the discrete (`⊤`) measurable space (re-declared `local`,
matching `GatedGeometricDrift`, since those instances do not export). -/
local instance instOptionMS2 : MeasurableSpace (Option α) := ⊤
local instance instOptionDMS2 : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

variable {K : Kernel α α} {G : Set α}

/-- **The unconditional killed drift, for ANY `r`** (Step 1, the `hr`-free `killK_drift`).
Identical proof to `killK_drift` except the dead-branch goal `0 ≤ r·killΦ Φ o` is closed by
`positivity` (which never consults `hr`); the gated branch uses `hdrift_G` exactly as before. -/
theorem killK_drift_anyr [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (r : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x) :
    ∀ o : Option α, ∫⁻ p, killΦ Φ p ∂(killK K G o) ≤ r * killΦ Φ o := by
  have hsome : Measurable (Option.some : α → Option α) := Measurable.of_discrete
  intro o
  unfold killK
  rw [Kernel.piecewise_apply]
  rcases o with _ | x
  · rw [if_neg none_notMem_image, Kernel.const_apply,
      MeasureTheory.lintegral_dirac' _ (killΦ_measurable Φ)]
    simp only [killΦ_none]; positivity
  · by_cases hx : x ∈ G
    · rw [if_pos ((some_mem_image_iff x).2 hx), Kernel.comap_apply,
        Kernel.map_apply _ hsome,
        MeasureTheory.lintegral_map (killΦ_measurable Φ) hsome]
      simp only [Option.getD_some, killΦ_some]
      exact hdrift_G x hx
    · rw [if_neg (fun h => hx ((some_mem_image_iff x).1 h)), Kernel.const_apply,
        MeasureTheory.lintegral_dirac' _ (killΦ_measurable Φ)]
      simp only [killΦ_none]; positivity

/-- **The killed geometric tail, for ANY `r`** (Step 1, the `hr`-free `killed_geometric_tail`).
Feeds `killK_drift_anyr` into the `hr`-free generic `geometric_drift_tail`. -/
theorem killed_geometric_tail_anyr [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (r : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    ((killK K G) ^ t) (some x) {o | θ ≤ killΦ Φ o} ≤ r ^ t * Φ x / θ := by
  have h := geometric_drift_tail (killK K G) (killΦ Φ) (killΦ_measurable Φ) r
    (killK_drift_anyr Φ r hdrift_G) t (some x) θ hθ0 hθtop
  simpa using h

/-- **The gated tail on the REAL kernel, for ANY `r`** (Step 1, the `hr`-free `gated_real_tail`).
Combines the coupling `real_le_killed` (which is `r`-free) with `killed_geometric_tail_anyr`.  The
drain term `r^t · Φ x / θ` now GENUINELY shrinks when `r < 1`. -/
theorem gated_real_tail_anyr [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (r : ℝ≥0∞)
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
        exact killed_geometric_tail_anyr Φ r hdrift_G t x θ hθ0 hθtop

end GatedDrift

/-! ## Step 2 — the slot-5 CONTRACTING drift (`r < 1`).

We build the MGF potential `expDrainPot s = ofReal(exp(s · U))` (the DRAIN MGF: `U` drops, so this
shrinks), and prove the contracting drift on the gate.  The proof is the mirror of
`ClockDepletionCoupling.expPot_drift`, but for a DECREMENT, so the multiplicative factor lands `< 1`.

The drift is stated GENERICALLY over an abstract Markov kernel `K`, an abstract count `U`, a gate
predicate `gate`, and a per-step drop floor `ρ` and never-increase property — exactly the data
`SamplingConcentration.sampleDrain_prob_floor` (drop floor) and `OneSidedCancel.PotNonincrOn`
(never-increase) supply for the slot-5 sampling drain. -/

open ReserveSampling SamplingConcentration Phase5ConfinementCompose

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The slot-5 DRAIN MGF potential: `Φ_U(c) = ofReal(exp(s · U c))`.  Since `U` DROPS, this SHRINKS
along the drain — the opposite sign from `ClockDepletionCoupling.expPot` (which measures `N − count`,
growing as the count drops). -/
noncomputable def expDrainPot (U : Config (AgentState L K) → ℕ) (s : ℝ) :
    Config (AgentState L K) → ℝ≥0∞ :=
  fun c => ENNReal.ofReal (Real.exp (s * (U c : ℝ)))

theorem expDrainPot_measurable (U : Config (AgentState L K) → ℕ) (s : ℝ) :
    Measurable (expDrainPot (L := L) (K := K) U s) :=
  Measurable.of_discrete

/-- **The contracting drift factor.**  `r = 1 − ρ·(1 − e^{−s})`.  For `ρ ∈ (0,1]` and `s > 0` this is
`< 1` (genuine contraction): `1 − e^{−s} ∈ (0,1)`, so `ρ·(1−e^{−s}) > 0`, so `r < 1`. -/
noncomputable def contractRate (ρ : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  1 - ρ * ENNReal.ofReal (1 - Real.exp (-s))

/-- **`contractRate` is genuinely `< 1`** when `0 < ρ` (`hρpos`), `ρ ≤ 1` (`hρle`), and `s > 0`
(`hs`).  This is the NON-VACUITY of the contraction: `r = 1 − ρ(1−e^{−s})` with `ρ(1−e^{−s}) > 0`.
The whole point — if `r ≥ 1` the drain term grows and the survival is vacuous. -/
theorem contractRate_lt_one {ρ : ℝ≥0∞} (s : ℝ) (hs : 0 < s)
    (hρpos : 0 < ρ) (hρle : ρ ≤ 1) :
    contractRate ρ s < 1 := by
  unfold contractRate
  have hexp_lt : Real.exp (-s) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hexp_pos : 0 < Real.exp (-s) := Real.exp_pos _
  have hgap_pos : 0 < 1 - Real.exp (-s) := by linarith
  have hofreal_pos : 0 < ENNReal.ofReal (1 - Real.exp (-s)) :=
    ENNReal.ofReal_pos.mpr hgap_pos
  have hprod_pos : 0 < ρ * ENNReal.ofReal (1 - Real.exp (-s)) :=
    ENNReal.mul_pos (ne_of_gt hρpos) (ne_of_gt hofreal_pos)
  have hgap_le : 1 - Real.exp (-s) ≤ 1 := by linarith [hexp_pos]
  have hofreal_le : ENNReal.ofReal (1 - Real.exp (-s)) ≤ 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal hgap_le
  have hprod_le : ρ * ENNReal.ofReal (1 - Real.exp (-s)) ≤ 1 := by
    calc ρ * ENNReal.ofReal (1 - Real.exp (-s)) ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hprod_ne_top : ρ * ENNReal.ofReal (1 - Real.exp (-s)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hprod_le
  exact ENNReal.sub_lt_self ENNReal.one_ne_top (by simp) (ne_of_gt hprod_pos)

/-- **The CONTRACTING MGF drift (the slot-5 drain supermartingale, `r < 1`).**  GENERIC form: from
* `hdrop : ρ ≤ K c {c' | U c' + 1 ≤ U c}` — the per-step DROP floor (mass `≥ ρ` that `U` drops by
  `≥ 1`), the proven `SamplingConcentration.sampleDrain_prob_floor` content;
* `hnoincr : K c {c' | U c < U c'} = 0` — `U` NEVER increases (a.e.), the `OneSidedCancel.PotNonincrOn`
  content,

the drain MGF `Φ_U = expDrainPot U s` (with `s ≥ 0`) satisfies the CONTRACTING drift

  `∫⁻ Φ_U dK(c) ≤ (1 − ρ·(1 − e^{−s})) · Φ_U(c) = contractRate ρ s · Φ_U(c)`.

On the drop set `Φ_U(c') ≤ e^{−s}·Φ_U(c)` (since `U c' ≤ U c − 1`); off the drop set but on the
never-increase set `Φ_U(c') ≤ Φ_U(c)`; the increase set has mass `0`.  Integrating gives the factor
`e^{−s}·p_drop + (1 − p_drop)` with `p_drop ≥ ρ`, monotone decreasing in `p_drop` (since `e^{−s} < 1`),
hence `≤ 1 − ρ(1−e^{−s})`. -/
theorem expDrainPot_drift_contracting
    (Kn : Kernel (Config (AgentState L K)) (Config (AgentState L K))) [IsMarkovKernel Kn]
    (U : Config (AgentState L K) → ℕ) (s : ℝ) (hs : 0 ≤ s) (ρ : ℝ≥0∞)
    (c : Config (AgentState L K))
    (hdrop : ρ ≤ Kn c {c' | U c' + 1 ≤ U c})
    (hnoincr : Kn c {c' | U c < U c'} = 0) :
    ∫⁻ c', expDrainPot (L := L) (K := K) U s c' ∂(Kn c)
      ≤ contractRate ρ s * expDrainPot (L := L) (K := K) U s c := by
  classical
  set A : ℝ := Real.exp (s * (U c : ℝ)) with hA
  have hApos : 0 < A := Real.exp_pos _
  set D : Set (Config (AgentState L K)) := {c' | U c' + 1 ≤ U c} with hD
  set Inc : Set (Config (AgentState L K)) := {c' | U c < U c'} with hInc
  have hDmeas : MeasurableSet D := MeasurableSet.of_discrete
  have hIncmeas : MeasurableSet Inc := MeasurableSet.of_discrete
  -- Pointwise bound: Φ_U c' ≤ ofReal A · (e^{−s}·𝟙_D + 𝟙_{Dᶜ ∩ Incᶜ}) ... we use the cleaner form
  -- Φ_U c' ≤ ofReal A · (𝟙 − (1−e^{−s})·𝟙_D), valid off Inc; on Inc it's anything but Inc has mass 0.
  -- We bound the integral by splitting on D and Dᶜ, using that off-D-and-off-Inc gives ≤ ofReal A.
  set em : ℝ := Real.exp (-s) with hem
  have hem_pos : 0 < em := Real.exp_pos _
  -- Pointwise: on D, Φ_U c' ≤ ofReal (A * em); on Incᶜ, Φ_U c' ≤ ofReal A.
  have hboundD : ∀ c' ∈ D, expDrainPot (L := L) (K := K) U s c' ≤ ENNReal.ofReal (A * em) := by
    intro c' hc'
    have hUc' : (U c' : ℝ) + 1 ≤ (U c : ℝ) := by exact_mod_cast hc'
    unfold expDrainPot
    apply ENNReal.ofReal_le_ofReal
    rw [hA, hem, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hUc', hs, mul_nonneg hs (by linarith : (0:ℝ) ≤ (U c : ℝ) - (U c' : ℝ))]
  have hboundIncc : ∀ c' ∈ Incᶜ, expDrainPot (L := L) (K := K) U s c' ≤ ENNReal.ofReal A := by
    intro c' hc'
    have hUc' : (U c' : ℝ) ≤ (U c : ℝ) := by
      have : ¬ (U c < U c') := hc'
      have : U c' ≤ U c := by omega
      exact_mod_cast this
    unfold expDrainPot
    apply ENNReal.ofReal_le_ofReal
    rw [hA]
    apply Real.exp_le_exp.mpr
    nlinarith [hUc', hs]
  -- Split the integral over D and Dᶜ.  On D use hboundD; on Dᶜ, since Inc has mass 0, a.e. on Incᶜ.
  have hae : ∀ᵐ c' ∂(Kn c),
      expDrainPot (L := L) (K := K) U s c'
        ≤ ENNReal.ofReal (A * em) * D.indicator (fun _ => 1) c'
          + ENNReal.ofReal A * Dᶜ.indicator (fun _ => 1) c' := by
    -- a.e. c' ∉ Inc (hnoincr), so c' satisfies hboundIncc; and on D it satisfies hboundD.
    have haeIncc : ∀ᵐ c' ∂(Kn c), c' ∈ Incᶜ := by
      rw [ae_iff]
      simp only [Set.mem_compl_iff, not_not]
      exact hnoincr
    filter_upwards [haeIncc] with c' hc'Inc
    by_cases hcD : c' ∈ D
    · rw [Set.indicator_of_mem hcD, Set.indicator_of_notMem (by simp [hcD] : c' ∉ Dᶜ)]
      simp only [mul_one, mul_zero, add_zero]
      exact hboundD c' hcD
    · rw [Set.indicator_of_notMem hcD, Set.indicator_of_mem (by simp [hcD] : c' ∈ Dᶜ)]
      simp only [mul_zero, mul_one, zero_add]
      exact hboundIncc c' hc'Inc
  -- Integrate the a.e. bound.
  calc ∫⁻ c', expDrainPot (L := L) (K := K) U s c' ∂(Kn c)
      ≤ ∫⁻ c', (ENNReal.ofReal (A * em) * D.indicator (fun _ => 1) c'
            + ENNReal.ofReal A * Dᶜ.indicator (fun _ => 1) c') ∂(Kn c) := lintegral_mono_ae hae
    _ = ENNReal.ofReal (A * em) * Kn c D + ENNReal.ofReal A * Kn c Dᶜ := by
        rw [lintegral_add_left (by measurability)]
        congr 1
        · rw [lintegral_const_mul _ (by measurability), lintegral_indicator_const hDmeas, one_mul]
        · rw [lintegral_const_mul _ (by measurability),
            lintegral_indicator_const hDmeas.compl, one_mul]
    _ ≤ contractRate ρ s * expDrainPot (L := L) (K := K) U s c := by
        -- Let p = Kn c D ≥ ρ.  Factor: ofReal(A·em)·p + ofReal A·(1−p) = ofReal A·(em·p + (1−p)).
        -- = ofReal A · (1 − p·(1−em)) ≤ ofReal A · (1 − ρ·(1−em)) since p ≥ ρ and 1−em ≥ 0.
        set p : ℝ≥0∞ := Kn c D with hp
        have hp_le_one : p ≤ 1 := by
          rw [hp]; exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
        have hpc : Kn c Dᶜ = 1 - p := by
          rw [hp, measure_compl hDmeas (measure_ne_top _ _)]
          simp [measure_univ]
        rw [hpc]
        -- abbreviations in ℝ≥0∞
        have hofA : expDrainPot (L := L) (K := K) U s c = ENNReal.ofReal A := by
          unfold expDrainPot; rw [hA]
        rw [hofA]
        have hem_le_one : em ≤ 1 := by
          rw [hem]; rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_le_exp.mpr (by linarith)
        have hAem : ENNReal.ofReal (A * em) = ENNReal.ofReal A * ENNReal.ofReal em := by
          rw [ENNReal.ofReal_mul hApos.le]
        rw [hAem]
        -- Goal: ofReal A · em · p + ofReal A · (1−p) ≤ contractRate ρ s · ofReal A.
        -- Rewrite LHS = ofReal A · (em·p + (1−p)).
        have hofem_le_one : ENNReal.ofReal em ≤ 1 := by
          rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
          exact ENNReal.ofReal_le_ofReal hem_le_one
        -- em·p + (1−p) ≤ contractRate ρ s, then multiply by ofReal A.
        have hfactor : ENNReal.ofReal em * p + (1 - p) ≤ contractRate ρ s := by
          -- Set q := ofReal em (so q ≤ 1), g := 1 - q (= ofReal (1−em), finite).
          set q : ℝ≥0∞ := ENNReal.ofReal em with hq
          have hq_le_one : q ≤ 1 := hofem_le_one
          -- p·q ≤ p (since q ≤ 1), used repeatedly.
          have hpq_le_p : p * q ≤ p := by
            calc p * q ≤ p * 1 := by gcongr
              _ = p := mul_one p
          have hqp_le_p : q * p ≤ p := by rw [mul_comm]; exact hpq_le_p
          have hp_ne_top : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp_le_one
          -- Key identity: q·p + (1−p) = 1 − p·(1−q).  Prove via add-cancel.
          -- p·(1−q) = p − p·q  (ENNReal.mul_sub, q ≤ 1 so finite).
          have hpg : p * (1 - q) = p - p * q := by
            rw [ENNReal.mul_sub (fun _ _ => hp_ne_top), mul_one]
          -- (q·p + (1−p)) + p·(1−q) = 1.
          have hsum1 : (q * p + (1 - p)) + p * (1 - q) = 1 := by
            rw [hpg]
            -- (q·p + (1−p)) + (p − p·q) = (q·p + (p − p·q)) + (1−p)
            --   = ((p·q) + (p − p·q)) + (1−p) = p + (1−p) = 1.
            rw [mul_comm q p]
            calc (p * q + (1 - p)) + (p - p * q)
                = (p * q + (p - p * q)) + (1 - p) := by
                  rw [add_assoc, add_comm (1 - p), ← add_assoc]
              _ = p + (1 - p) := by
                  rw [add_tsub_cancel_of_le hpq_le_p]
              _ = 1 := add_tsub_cancel_of_le hp_le_one
          -- so q·p + (1−p) = 1 − p·(1−q).
          have hpg_le_one : p * (1 - q) ≤ 1 := by
            calc p * (1 - q) ≤ 1 * (1 - q) := by gcongr
              _ = 1 - q := one_mul _
              _ ≤ 1 := tsub_le_self
          have hident : q * p + (1 - p) = 1 - p * (1 - q) :=
            ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top hpg_le_one) hsum1
          rw [hident]
          -- contractRate ρ s = 1 − ρ·(1−q)  (ofReal(1−em) = 1 − ofReal em = 1 − q).
          unfold contractRate
          have hgap : ENNReal.ofReal (1 - em) = 1 - q := by
            rw [hq, ENNReal.ofReal_sub _ hem_pos.le, ENNReal.ofReal_one]
          rw [hgap]
          -- 1 − p·(1−q) ≤ 1 − ρ·(1−q) since ρ ≤ p (monotone in the subtrahend, reversed).
          have hρp : ρ ≤ p := by rw [hp]; exact hdrop
          gcongr
        calc ENNReal.ofReal A * ENNReal.ofReal em * p + ENNReal.ofReal A * (1 - p)
            = ENNReal.ofReal A * (ENNReal.ofReal em * p + (1 - p)) := by ring
          _ ≤ ENNReal.ofReal A * contractRate ρ s := by gcongr
          _ = contractRate ρ s * ENNReal.ofReal A := by ring

/-! ## Step 3 — the composed slot-5 survival with the CONTRACTING (`r < 1`) drain.

We now wire the contracting drift into the slot-5 survival.  The structure MIRRORS
`Phase5SurvivalCorrect.phase5_survival_correct` — the same H-step triple-union split, the same
cumulative clock/confinement tails, the same prefix-union escape — but the drain engine is
`GatedDrift.gated_real_tail_anyr` (NO `hr : 1 ≤ r`), instantiated with the contracting `r =
contractRate ρ s < 1`.  The drain term `r^T·Φ_U c₀/θ` therefore GENUINELY SHRINKS as `T → ∞`,
unlike the vacuous `r ≥ 1` term it replaces. -/

open GatedDrift

/-- **Term 3 — the maintained-window drain with CONTRACTING `r`** (the `_anyr` analogue of
`Phase5SurvivalCorrect.term3_drain_prefix`, WITHOUT `hr : 1 ≤ r`).  On the gate `G`, the real
`T`-step tail of `{θ ≤ Φ_U}` is bounded by the contracting drain `r^T·Φ_U c₀/θ` PLUS the small
confinement leak `T·q_leak` PLUS the cumulative clock prefix-failures `∑_{τ<T} (K^τ) c₀ Sᶜ`.

`r` is arbitrary (in the application `r = contractRate ρ s < 1`, so `r^T → 0`). -/
theorem term3_drain_prefix_anyr
    (n : ℕ)
    (Φ_U : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hUdrift : ∀ x ∈ {c | Phase5Confined (L := L) (K := K) n c},
      ∫⁻ y, Φ_U y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ_U x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase5Confined (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase5Confined (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (c₀ : Config (AgentState L K))
    (hConf₀ : Phase5Confined (L := L) (K := K) n c₀)
    (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ_U c}
      ≤ ((T : ℝ≥0∞) * q_leak
          + ∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
        + r ^ T * Φ_U c₀ / θ := by
  classical
  -- gated tail (NO hr): real high-U tail ≤ cemetery escape + CONTRACTING drain supermartingale.
  have hgated := GatedDrift.gated_real_tail_anyr
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | Phase5Confined (L := L) (K := K) n c})
    Φ_U r hUdrift T c₀ θ hθ0 hθtop
  -- cemetery escape ≤ small leak + cumulative clock prefix-failures.
  have hesc := GatedDrift.kill_escape_le_prefix_union
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | Phase5Confined (L := L) (K := K) n c})
    S q_leak hLeak T c₀ hConf₀
  refine le_trans hgated ?_
  exact add_le_add hesc le_rfl

/-- **CORRECT, CONTRACTING slot-5 survival (`r < 1`).**  The `_anyr` analogue of
`Phase5SurvivalCorrect.phase5_survival_correct`: from a confinement-confined start `c₀`, the
probability that the slot-5 sampling drain FAILS to reach `ReserveSampled` at horizon `T` is at most
`ε_drain + η_clock + η_conf`.  The crucial difference: the drain engine carries NO `hr : 1 ≤ r`, so
`r` may be `< 1` (the contracting `contractRate ρ s`), making the drain term `r^T·Φ_U c₀/θ`
genuinely shrink (proved subcritical by `drain_term_shrinks`).  NO `InvClosed` of any phase window. -/
theorem phase5_survival_contracting (n : ℕ)
    (Φ_U : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hUdrift : ∀ x ∈ {c | Phase5Confined (L := L) (K := K) n c},
      ∫⁻ y, Φ_U y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ_U x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase5Confined (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase5Confined (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (c₀ : Config (AgentState L K))
    (hConf₀ : Phase5Confined (L := L) (K := K) n c₀)
    (εdrain : ℝ≥0)
    (hεdrain : ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_U c₀ / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (η_clock η_conf : ℝ≥0∞)
    (hClock : (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) ≤ η_clock)
    (hConf : ((NonuniformMajority L K).transitionKernel ^ T) c₀
      {c | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c} ≤ η_conf)
    (hcover : {c : Config (AgentState L K) | ¬ ReserveSampled (L := L) (K := K) c}
      ⊆ {c | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c}
        ∪ {c | θ ≤ Φ_U c}) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ ReserveSampled (L := L) (K := K) c}
      ≤ (εdrain : ℝ≥0∞) + η_clock + η_conf := by
  classical
  have hdrain0 := term3_drain_prefix_anyr (L := L) (K := K) n Φ_U r hUdrift S q_leak hLeak T c₀ hConf₀
    θ hθ0 hθtop
  have hdrain : ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ_U c}
      ≤ (εdrain : ℝ≥0∞) + η_clock := by
    refine le_trans hdrain0 ?_
    calc ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ_U c₀ / θ
        = ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_U c₀ / θ)
          + ∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ := by ring
      _ ≤ (εdrain : ℝ≥0∞) + η_clock := add_le_add hεdrain hClock
  set μ := ((NonuniformMajority L K).transitionKernel ^ T) c₀ with hμ
  set Aconf : Set (Config (AgentState L K)) :=
    {c | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c} with hAconf
  set Adrain : Set (Config (AgentState L K)) := {c | θ ≤ Φ_U c} with hAdrain
  calc μ {c | ¬ ReserveSampled (L := L) (K := K) c}
      ≤ μ (Aconf ∪ Adrain) := measure_mono hcover
    _ ≤ μ Aconf + μ Adrain := measure_union_le _ _
    _ ≤ η_conf + ((εdrain : ℝ≥0∞) + η_clock) := add_le_add hConf hdrain
    _ = (εdrain : ℝ≥0∞) + η_clock + η_conf := by ring

/-! ## Step 3b — the drain genuinely SHRINKS (non-vacuity, the whole point).

The vacuous `r ≥ 1` version has `r^T·Φ_U c₀/θ` GROWING.  The contracting `r < 1` version has it
SHRINKING to `0`.  We prove the explicit non-vacuity: for `r < 1` (and `Φ_U c₀ / θ` finite), the
drain term `r^T·Φ_U c₀/θ` is `≤ ε` for all `T` past a threshold.  Combined with the small
confinement leak `T·q_leak` (which is `Θ(T·exp-small)`, controlled separately), this gives a
genuinely subcritical `ε_drain` — NOT achievable with `r ≥ 1`. -/

/-- **The contracting drain term tends to `0`.**  For `r < 1` the supermartingale drain
`r^T · (Φ_U c₀ / θ)` tends to `0` as `T → ∞` (geometric decay).  This is the genuine non-vacuity: it
is FALSE for `r ≥ 1` (then `r^T ≥ 1`, the term does not shrink).  `hcoef` is `Φ_U c₀ / θ ≠ ∞`
(automatic when `θ ≠ 0` and `Φ_U c₀ ≠ ∞`, both true for the MGF lift at a finite threshold). -/
theorem drain_term_tendsto_zero (r : ℝ≥0∞) (hr : r < 1) (coef : ℝ≥0∞) (hcoef : coef ≠ ∞) :
    Filter.Tendsto (fun T : ℕ => r ^ T * coef) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun T : ℕ => r ^ T) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr
  have := ENNReal.Tendsto.mul_const hpow (Or.inr hcoef)
  simpa using this

/-- **The drain shrinks below any positive `ε` past a threshold** (explicit non-vacuity).  For `r < 1`
and finite coefficient `coef = Φ_U c₀ / θ`, and any `ε > 0`, there is a horizon `T₀` such that for all
`T ≥ T₀` the contracting drain term `r^T · coef ≤ ε`.  This is exactly the property the vacuous
`r ≥ 1` engine CANNOT supply: with `r ≥ 1` the term is `≥ coef` for all `T`, never subcritical. -/
theorem drain_term_shrinks (r : ℝ≥0∞) (hr : r < 1) (coef : ℝ≥0∞) (hcoef : coef ≠ ∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T ≥ T₀, r ^ T * coef ≤ ε := by
  have htend := drain_term_tendsto_zero r hr coef hcoef
  have hmem : Set.Iic ε ∈ nhds (0 : ℝ≥0∞) :=
    Iic_mem_nhds hε
  have heventual := htend.eventually_mem hmem
  rw [Filter.eventually_atTop] at heventual
  obtain ⟨T₀, hT₀⟩ := heventual
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

/-- **The full non-vacuity statement combining contraction + shrink.**  The contracting rate
`r = contractRate ρ s` is `< 1` (`contractRate_lt_one`), and its drain term shrinks below any `ε`
past a threshold (`drain_term_shrinks`).  This is the linchpin: a GENUINELY shrinking drain, not the
`r ≥ 1` impostor. -/
theorem contracting_drain_nonvacuous {ρ : ℝ≥0∞} (s : ℝ) (hs : 0 < s)
    (hρpos : 0 < ρ) (hρle : ρ ≤ 1)
    (coef : ℝ≥0∞) (hcoef : coef ≠ ∞) (ε : ℝ≥0∞) (hε : 0 < ε) :
    contractRate ρ s < 1 ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, (contractRate ρ s) ^ T * coef ≤ ε := by
  have hlt := contractRate_lt_one s hs hρpos hρle
  exact ⟨hlt, drain_term_shrinks (contractRate ρ s) hlt coef hcoef ε hε⟩

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms killK_drift_anyr
#print axioms killed_geometric_tail_anyr
#print axioms gated_real_tail_anyr
#print axioms expDrainPot_drift_contracting
#print axioms contractRate_lt_one
#print axioms term3_drain_prefix_anyr
#print axioms phase5_survival_contracting
#print axioms drain_term_tendsto_zero
#print axioms drain_term_shrinks
#print axioms contracting_drain_nonvacuous

end ExactMajority
