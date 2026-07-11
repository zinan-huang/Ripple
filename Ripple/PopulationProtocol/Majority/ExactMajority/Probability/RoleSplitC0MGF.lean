
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# RoleSplitC0MGF — C0 gated MGF hdrift builders and postwarm reconciliation

This file supplies:
* generic `+2` exp-MGF `hdrift` builders for role-count and deficit-count potentials;
* concrete corollaries for `mainCount`, `clockCount`, `reserveCount`, and `assignableCount` deficits;
* deterministic reconciliation between `floorOrDoneGateᶜ` and the landed
  `floorFailsBeforePost` prefix;
* a postwarm Stage-1 wrapper whose only remaining probabilistic input is a satisfiable,
  gated postwarm core tail, not a false universal theorem.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitFloorDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MainProfileDrift
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0InitialFresh

namespace ExactMajority
namespace RoleSplitFloorDischarge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

open RoleSplitConcentration
open FloorPrefix

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## A. Generic `+2` exp-MGF hdrift builders -/

/-- Exponential potential for a natural-valued count. -/
noncomputable def countExpPot
    (N : Config (AgentState L K) → ℕ) (lam : ℝ)
    (c : Config (AgentState L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lam * (N c : ℝ)))

theorem countExpPot_measurable
    (N : Config (AgentState L K) → ℕ) (lam : ℝ) :
    Measurable (countExpPot (L := L) (K := K) N lam) :=
  Measurable.of_discrete

/--
Generic `hdrift` for a `+2` count potential.

This is the role-split analogue of `mainAbove_exp_mgf_drift_add_two`, but with
an arbitrary natural count `N`.  The only genuine one-step content is supplied
by the gated hypotheses:

* `hstep`: one interaction raises `N` by at most `2`;
* `hrise`: the probability of a strict rise is at most `q`.
-/
theorem countExp_mgf_drift_add_two
    (N : Config (AgentState L K) → ℕ)
    (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (Gate : Config (AgentState L K) → Prop)
    (hstep :
      ∀ c, Gate c →
        ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          N c' ≤ N c + 2)
    (hrise :
      ∀ c, Gate c →
        ((NonuniformMajority L K).transitionKernel c)
          {c' | N c < N c'} ≤ ENNReal.ofReal q) :
    ∀ c, Gate c →
      ∫⁻ c', countExpPot (L := L) (K := K) N lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * countExpPot (L := L) (K := K) N lam c := by
  intro c hc
  classical
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
    (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
  have hfac_nonneg : 0 ≤ 1 + q * (Real.exp (2 * lam) - 1) := by
    have hexp2 : 1 ≤ Real.exp (2 * lam) := Real.one_le_exp (by nlinarith)
    nlinarith [hq0, hexp2]
  have h :=
    MainExponentConfinement.mgf_one_step_add_two
      ((NonuniformMajority L K).transitionKernel c)
      lam hlam N (N c)
      (hstep c hc) q hq0 (hrise c hc)
  calc
    ∫⁻ c', countExpPot (L := L) (K := K) N lam c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal
          ((1 + q * (Real.exp (2 * lam) - 1))
            * Real.exp (lam * (N c : ℝ))) := by
        simpa [countExpPot] using h
    _ = ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
          * countExpPot (L := L) (K := K) N lam c := by
        rw [ENNReal.ofReal_mul hfac_nonneg]
        rfl

/-- Natural deficit of a count below a target floor. -/
def natDeficit
    (target : ℕ) (N : Config (AgentState L K) → ℕ)
    (c : Config (AgentState L K)) : ℕ :=
  target - N c

/-- Exponential potential for a natural deficit. -/
noncomputable def deficitExpPot
    (target : ℕ) (N : Config (AgentState L K) → ℕ) (lam : ℝ)
    (c : Config (AgentState L K)) : ℝ≥0∞ :=
  countExpPot (L := L) (K := K)
    (natDeficit (L := L) (K := K) target N) lam c

theorem deficitExpPot_measurable
    (target : ℕ) (N : Config (AgentState L K) → ℕ) (lam : ℝ) :
    Measurable (deficitExpPot (L := L) (K := K) target N lam) :=
  countExpPot_measurable (L := L) (K := K)
    (natDeficit (L := L) (K := K) target N) lam

/--
Generic `hdrift` for a `+2` deficit potential.

This is the lower-tail counterpart of `countExp_mgf_drift_add_two`.
The two gated inputs are:

* `hstep`: the deficit rises by at most `2` in one interaction;
* `hrise`: the probability the deficit strictly rises is at most `q`.
-/
theorem deficitExp_mgf_drift_add_two
    (target : ℕ) (N : Config (AgentState L K) → ℕ)
    (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (Gate : Config (AgentState L K) → Prop)
    (hstep :
      ∀ c, Gate c →
        ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          natDeficit (L := L) (K := K) target N c'
            ≤ natDeficit (L := L) (K := K) target N c + 2)
    (hrise :
      ∀ c, Gate c →
        ((NonuniformMajority L K).transitionKernel c)
          {c' |
            natDeficit (L := L) (K := K) target N c
              < natDeficit (L := L) (K := K) target N c'} ≤ ENNReal.ofReal q) :
    ∀ c, Gate c →
      ∫⁻ c', deficitExpPot (L := L) (K := K) target N lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target N lam c :=
  countExp_mgf_drift_add_two
    (L := L) (K := K)
    (natDeficit (L := L) (K := K) target N)
    lam q hlam hq0 Gate hstep hrise

/-! ## B. Role-count and pool-count drift corollaries -/

/-- Upper-tail MGF drift for `mainCount`, from gated `+2` and rise-probability facts. -/
theorem mainCount_upper_exp_mgf_drift_add_two
    (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (Gate : Config (AgentState L K) → Prop)
    (hstep :
      ∀ c, Gate c →
        ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          mainCount (L := L) (K := K) c'
            ≤ mainCount (L := L) (K := K) c + 2)
    (hrise :
      ∀ c, Gate c →
        ((NonuniformMajority L K).transitionKernel c)
          {c' |
            mainCount (L := L) (K := K) c
              < mainCount (L := L) (K := K) c'} ≤ ENNReal.ofReal q) :
    ∀ c, Gate c →
      ∫⁻ c',
          countExpPot (L := L) (K := K)
            (mainCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * countExpPot (L := L) (K := K)
                (mainCount (L := L) (K := K)) lam c :=
  countExp_mgf_drift_add_two
    (L := L) (K := K)
    (mainCount (L := L) (K := K)) lam q hlam hq0 Gate hstep hrise

/-- Lower-tail deficit MGF drift for `mainCount`. -/
theorem mainCount_lower_deficit_mgf_drift_add_two
    (target : ℕ) (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (Gate : Config (AgentState L K) → Prop)
    (hstep :
      ∀ c, Gate c →
        ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          natDeficit (L := L) (K := K) target
              (mainCount (L := L) (K := K)) c'
            ≤ natDeficit (L := L) (K := K) target
              (mainCount (L := L) (K := K)) c + 2)
    (hrise :
      ∀ c, Gate c →
        ((NonuniformMajority L K).transitionKernel c)
          {c' |
            natDeficit (L := L) (K := K) target
                (mainCount (L := L) (K := K)) c
              < natDeficit (L := L) (K := K) target
                (mainCount (L := L) (K := K)) c'} ≤ ENNReal.ofReal q) :
    ∀ c, Gate c →
      ∫⁻ c',
          deficitExpPot (L := L) (K := K) target
            (mainCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target
                (mainCount (L := L) (K := K)) lam c :=
  deficitExp_mgf_drift_add_two
    (L := L) (K := K)
    target (mainCount (L := L) (K := K))
    lam q hlam hq0 Gate hstep hrise

/-- Lower-tail deficit MGF drift for `clockCount`. -/
theorem clockCount_lower_deficit_mgf_drift_add_two
    (target : ℕ) (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (Gate : Config (AgentState L K) → Prop)
    (hstep :
      ∀ c, Gate c →
        ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          natDeficit (L := L) (K := K) target
              (clockCount (L := L) (K := K)) c'
            ≤ natDeficit (L := L) (K := K) target
              (clockCount (L := L) (K := K)) c + 2)
    (hrise :
      ∀ c, Gate c →
        ((NonuniformMajority L K).transitionKernel c)
          {c' |
            natDeficit (L := L) (K := K) target
                (clockCount (L := L) (K := K)) c
              < natDeficit (L := L) (K := K) target
                (clockCount (L := L) (K := K)) c'} ≤ ENNReal.ofReal q) :
    ∀ c, Gate c →
      ∫⁻ c',
          deficitExpPot (L := L) (K := K) target
            (clockCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target
                (clockCount (L := L) (K := K)) lam c :=
  deficitExp_mgf_drift_add_two
    (L := L) (K := K)
    target (clockCount (L := L) (K := K))
    lam q hlam hq0 Gate hstep hrise

/-- Lower-tail deficit MGF drift for `reserveCount`. -/
theorem reserveCount_lower_deficit_mgf_drift_add_two
    (target : ℕ) (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (Gate : Config (AgentState L K) → Prop)
    (hstep :
      ∀ c, Gate c →
        ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          natDeficit (L := L) (K := K) target
              (reserveCount (L := L) (K := K)) c'
            ≤ natDeficit (L := L) (K := K) target
              (reserveCount (L := L) (K := K)) c + 2)
    (hrise :
      ∀ c, Gate c →
        ((NonuniformMajority L K).transitionKernel c)
          {c' |
            natDeficit (L := L) (K := K) target
                (reserveCount (L := L) (K := K)) c
              < natDeficit (L := L) (K := K) target
                (reserveCount (L := L) (K := K)) c'} ≤ ENNReal.ofReal q) :
    ∀ c, Gate c →
      ∫⁻ c',
          deficitExpPot (L := L) (K := K) target
            (reserveCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target
                (reserveCount (L := L) (K := K)) lam c :=
  deficitExp_mgf_drift_add_two
    (L := L) (K := K)
    target (reserveCount (L := L) (K := K))
    lam q hlam hq0 Gate hstep hrise

/-- Warm-up/floor lower-tail deficit MGF drift for `assignableCount`. -/
theorem assignableCount_deficit_mgf_drift_add_two
    (target : ℕ) (lam q : ℝ) (hlam : 0 ≤ lam) (hq0 : 0 ≤ q)
    (Gate : Config (AgentState L K) → Prop)
    (hstep :
      ∀ c, Gate c →
        ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          natDeficit (L := L) (K := K) target
              (assignableCount (L := L) (K := K)) c'
            ≤ natDeficit (L := L) (K := K) target
              (assignableCount (L := L) (K := K)) c + 2)
    (hrise :
      ∀ c, Gate c →
        ((NonuniformMajority L K).transitionKernel c)
          {c' |
            natDeficit (L := L) (K := K) target
                (assignableCount (L := L) (K := K)) c
              < natDeficit (L := L) (K := K) target
                (assignableCount (L := L) (K := K)) c'} ≤ ENNReal.ofReal q) :
    ∀ c, Gate c →
      ∫⁻ c',
          deficitExpPot (L := L) (K := K) target
            (assignableCount (L := L) (K := K)) lam c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ENNReal.ofReal (1 + q * (Real.exp (2 * lam) - 1))
            * deficitExpPot (L := L) (K := K) target
                (assignableCount (L := L) (K := K)) lam c :=
  deficitExp_mgf_drift_add_two
    (L := L) (K := K)
    target (assignableCount (L := L) (K := K))
    lam q hlam hq0 Gate hstep hrise

/-! ## C. Deterministic postwarm gate reconciliation -/

/--
The warm-up checkpoint implies the raw floor gate.

`Phase0WarmGood` gives the structural shell and `2*a₀ ≤ assignableCount`, hence
`a₀ ≤ assignableCount`.
-/
theorem Phase0WarmGood.mem_floorGate
    {n a₀ uMin : ℕ} {c : Config (AgentState L K)}
    (h : Phase0WarmGood (L := L) (K := K) n a₀ uMin c) :
    c ∈ floorGate (L := L) (K := K) n a₀ := by
  rcases h with ⟨hshell, _hu, hpool⟩
  exact ⟨hshell.1, by omega, hshell.2⟩

/--
Leaving `floorOrDoneGate` means either the structural shell failed, or a floor
failure occurred before Stage 1 was done.

This is the key deterministic bridge from a raw gate-complement residual to the
landed `floorFailsBeforePost` prefix.
-/
theorem floorOrDoneGate_compl_subset_shell_or_floorFails
    (n a₀ : ℕ) (hn2 : 2 ≤ n) :
    (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ
      ⊆ (cardPhaseShell (L := L) (K := K) n)ᶜ
        ∪ {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c} := by
  intro c hc
  have hnotG :
      c ∉ floorOrDoneGate (L := L) (K := K) n a₀ hn2 := hc
  by_cases hshell : c ∈ cardPhaseShell (L := L) (K := K) n
  · right
    have hnotDone :
        ¬ roleSplitGoodMile (L := L) (K := K) n hn2 c := by
      intro hdone
      exact hnotG (Or.inr hdone)
    have hnotFloor :
        c ∉ floorGate (L := L) (K := K) n a₀ := by
      intro hfg
      exact hnotG (Or.inl hfg)
    have hpool_lt :
        assignableCount (L := L) (K := K) c < a₀ := by
      by_contra hlt
      have hfloor : a₀ ≤ assignableCount (L := L) (K := K) c := not_lt.mp hlt
      exact hnotFloor ⟨hshell.1, hfloor, hshell.2⟩
    exact ⟨hpool_lt, hnotDone⟩
  · left
    exact hshell

/--
Prefix version of `floorOrDoneGate_compl_subset_shell_or_floorFails`.
-/
theorem floorOrDone_prefix_le
    (n a₀ T t : ℕ) (hn2 : 2 ≤ n)
    (c₀ : Config (AgentState L K))
    (εshell εfloorFail : ℝ≥0∞)
    (hshell :
      ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ (T + τ)) c₀
          ((cardPhaseShell (L := L) (K := K) n)ᶜ) ≤ εshell)
    (hfloor :
      ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ (T + τ)) c₀
          {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c} ≤ εfloorFail) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T + τ)) c₀
        (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ
      ≤ εshell + εfloorFail := by
  classical
  set μ : ℕ → Measure (Config (AgentState L K)) := fun τ =>
    ((NonuniformMajority L K).transitionKernel ^ (T + τ)) c₀ with hμ
  have hper :
      ∀ τ,
        μ τ (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ
          ≤ μ τ ((cardPhaseShell (L := L) (K := K) n)ᶜ)
            + μ τ {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c} := by
    intro τ
    calc
      μ τ (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ
        ≤ μ τ
            (((cardPhaseShell (L := L) (K := K) n)ᶜ)
              ∪ {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}) :=
          measure_mono
            (floorOrDoneGate_compl_subset_shell_or_floorFails
              (L := L) (K := K) n a₀ hn2)
      _ ≤ μ τ ((cardPhaseShell (L := L) (K := K) n)ᶜ)
            + μ τ {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c} :=
          measure_union_le _ _
  calc
    ∑ τ ∈ Finset.range t,
      μ τ (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ
      ≤ ∑ τ ∈ Finset.range t,
          (μ τ ((cardPhaseShell (L := L) (K := K) n)ᶜ)
            + μ τ {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}) :=
        Finset.sum_le_sum (fun τ _ => hper τ)
    _ =
      (∑ τ ∈ Finset.range t,
        μ τ ((cardPhaseShell (L := L) (K := K) n)ᶜ)
      + ∑ τ ∈ Finset.range t,
        μ τ {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}) := by
        rw [Finset.sum_add_distrib]
    _ ≤ εshell + εfloorFail := by
        exact add_le_add hshell hfloor

/--
Same bridge from a postwarm start, with no extra time shift.
-/
theorem floorOrDone_prefix_le_from_postwarm
    (n a₀ t : ℕ) (hn2 : 2 ≤ n)
    (y : Config (AgentState L K))
    (εshell εfloorFail : ℝ≥0∞)
    (hshell :
      ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) y
          ((cardPhaseShell (L := L) (K := K) n)ᶜ) ≤ εshell)
    (hfloor :
      ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) y
          {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c} ≤ εfloorFail) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ τ) y
        (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ
      ≤ εshell + εfloorFail := by
  simpa using
    floorOrDone_prefix_le
      (L := L) (K := K)
      n a₀ 0 t hn2 y εshell εfloorFail
      (by simpa using hshell) (by simpa using hfloor)

/-! ## D. Postwarm Stage-1 signature reconciliation -/

/--
Postwarm Stage-1 core tail.

This is the only remaining **plumbing/probability** input that cannot be derived
from the currently exported `phase0_stage1_whp_final`, because that theorem still
requires a weak `Phase0Initial` at the Stage-1 start.  A concrete proof should run
the killed-kernel milestone engine from an arbitrary frontier and charge escape from
`floorOrDoneGate`.

The field is satisfiable and gated: it is required only from `Phase0WarmGood` starts.
-/
structure PostwarmStage1Core
    (n a₀ uMin Tstage : ℕ) (hn2 : 2 ≤ n)
    (εcore εshell εfloorFail : ℝ≥0∞) where
  /-- The killed/Janson core plus raw `floorOrDoneGateᶜ` escape prefix. -/
  hcore :
    ∀ y,
      Phase0WarmGood (L := L) (K := K) n a₀ uMin y →
      ((NonuniformMajority L K).transitionKernel ^ Tstage) y
        {z | ¬ roleSplitGoodMile (L := L) (K := K) n hn2 z}
        ≤ εcore
          + ∑ τ ∈ Finset.range Tstage,
              ((NonuniformMajority L K).transitionKernel ^ τ) y
                (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ

  /-- Structural-shell prefix from each postwarm start. -/
  hshell :
    ∀ y,
      Phase0WarmGood (L := L) (K := K) n a₀ uMin y →
      ∑ τ ∈ Finset.range Tstage,
        ((NonuniformMajority L K).transitionKernel ^ τ) y
          ((cardPhaseShell (L := L) (K := K) n)ᶜ) ≤ εshell

  /-- Landed `floorFailsBeforePost` prefix from each postwarm start. -/
  hfloor :
    ∀ y,
      Phase0WarmGood (L := L) (K := K) n a₀ uMin y →
      ∑ τ ∈ Finset.range Tstage,
        ((NonuniformMajority L K).transitionKernel ^ τ) y
          {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c} ≤ εfloorFail

  /-- Budget reconciliation. -/
  hbudget :
    εcore + (εshell + εfloorFail) ≤ εcore + εshell + εfloorFail

/--
The corrected postwarm Stage-1 theorem.

It has the requested shape:
from `Phase0WarmGood`, the Stage-1 bad tail is bounded by an explicit stage budget,
and the residual is reconciled through `floorFailsBeforePost`, not raw `floorGateᶜ`.

`εstage` is a caller-chosen budget upper-bounding
`εcore + (εshell + εfloorFail)`.
-/
theorem phase0_stage1_postwarm_whp
    (n a₀ uMin Tstage : ℕ) (hn2 : 2 ≤ n)
    (εcore εshell εfloorFail εstage : ℝ≥0∞)
    (A : PostwarmStage1Core
      (L := L) (K := K) n a₀ uMin Tstage hn2 εcore εshell εfloorFail)
    (hstageBudget : εcore + (εshell + εfloorFail) ≤ εstage) :
    ∀ y,
      Phase0WarmGood (L := L) (K := K) n a₀ uMin y →
      ((NonuniformMajority L K).transitionKernel ^ Tstage) y
        {z | ¬ roleSplitGoodMile (L := L) (K := K) n hn2 z} ≤ εstage := by
  intro y hy
  have hprefix :
      ∑ τ ∈ Finset.range Tstage,
        ((NonuniformMajority L K).transitionKernel ^ τ) y
          (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ
        ≤ εshell + εfloorFail :=
    floorOrDone_prefix_le_from_postwarm
      (L := L) (K := K)
      n a₀ Tstage hn2 y εshell εfloorFail
      (A.hshell y hy) (A.hfloor y hy)
  calc
    ((NonuniformMajority L K).transitionKernel ^ Tstage) y
        {z | ¬ roleSplitGoodMile (L := L) (K := K) n hn2 z}
      ≤ εcore
          + ∑ τ ∈ Finset.range Tstage,
              ((NonuniformMajority L K).transitionKernel ^ τ) y
                (floorOrDoneGate (L := L) (K := K) n a₀ hn2)ᶜ :=
        A.hcore y hy
    _ ≤ εcore + (εshell + εfloorFail) := by
        gcongr
    _ ≤ εstage := hstageBudget

/--
Warm-up followed by corrected postwarm Stage 1, via CK.

This is the consumer-level chain:
`Phase0InitialFresh` gives `Phase0Initial`, warm-up is discharged by a
`WarmupReachBennettAtom`, and postwarm Stage 1 uses `phase0_stage1_postwarm_whp`.
-/
theorem phase0_stage1_from_fresh_via_warmup
    (n a₀ uMin T₀ Tstage : ℕ) (hn2 : 2 ≤ n)
    (εwarm εcore εshell εfloorFail εstage : ℝ≥0∞)
    (Awarm :
      WarmupReachBennettAtom
        (L := L) (K := K) n a₀ uMin T₀ εwarm)
    (Apost :
      PostwarmStage1Core
        (L := L) (K := K) n a₀ uMin Tstage hn2 εcore εshell εfloorFail)
    (hstageBudget : εcore + (εshell + εfloorFail) ≤ εstage)
    {c₀ : Config (AgentState L K)}
    (hinitFresh : Phase0InitialFresh (L := L) (K := K) n c₀) :
    ((NonuniformMajority L K).transitionKernel ^ (T₀ + Tstage)) c₀
      {z | ¬ roleSplitGoodMile (L := L) (K := K) n hn2 z}
      ≤ εwarm + εstage := by
  have hinit : Phase0Initial (L := L) (K := K) n c₀ :=
    Phase0InitialFresh.toPhase0Initial (L := L) (K := K) hinitFresh
  have hWarm :
      ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
        {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c} ≤ εwarm :=
    warmup_reach_of_bennett (L := L) (K := K) Awarm hinit
  exact
    warmup_ck_extend
      (L := L) (K := K)
      hWarm
      (fun z => roleSplitGoodMile (L := L) (K := K) n hn2 z)
      (phase0_stage1_postwarm_whp
        (L := L) (K := K)
        n a₀ uMin Tstage hn2
        εcore εshell εfloorFail εstage
        Apost hstageBudget)

end RoleSplitFloorDischarge
end ExactMajority
