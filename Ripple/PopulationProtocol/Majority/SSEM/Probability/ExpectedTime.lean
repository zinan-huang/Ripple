/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expected Hitting Time and Parallel Time

Definitions of expected first-hitting time on `Config` and of *parallel
time* (sequential time ÷ `n`), the standard time measure for population
protocols (Kanaya §2).

This file is a **scaffold**.  The intended signatures are stated and the
expected hitting-time definition uses the standard tail-sum form over a
finite-prefix Markov chain with a carried hit flag.

This module lives outside the root import graph until the time-bound
layer is closed.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Probability.RandomScheduler
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Silent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace SSEM
namespace Probability

open scoped ENNReal
open PMF

variable {Q X Y : Type*} {n : ℕ}

/-- Probability that the protocol has reached the goal predicate at
sequential step `t` (marginal at `t`, **not** "hit by `t`"), starting
from `C₀` under uniform random scheduling.

This is a stepping-stone for `expectedHittingTime`; the latter needs
the path-level "first time goal holds" event. -/
noncomputable def probReached
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (t : ℕ) : ENNReal :=
  ∑' C : Config Q X n,
    if Goal C then (nthStepDist P hn C₀ t) C else 0

/-- If `C₀` satisfies `Goal`, then `probReached` at step 0 is `1`. -/
theorem probReached_zero_of_goal
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : Goal C₀) :
    probReached P hn C₀ Goal 0 = 1 := by
  classical
  unfold probReached
  simp only [nthStepDist]
  have heq : ∀ C : Config Q X n,
      (if Goal C then (PMF.pure C₀) C else 0) = (PMF.pure C₀) C := by
    intro C
    by_cases hC : C = C₀
    · subst hC; simp [hGoal]
    · rw [PMF.pure_apply_of_ne C₀ C hC]
      by_cases hGC : Goal C
      · rw [if_pos hGC]
      · rw [if_neg hGC]
  rw [show (∑' C, (if Goal C then (PMF.pure C₀) C else 0)) =
      ∑' C, (PMF.pure C₀) C from tsum_congr heq]
  exact PMF.tsum_coe (PMF.pure C₀)

/-- `probReached` is monotone in the goal predicate. -/
theorem probReached_mono_goal
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal₁ Goal₂ : Config Q X n → Prop)
    [DecidablePred Goal₁] [DecidablePred Goal₂]
    (h : ∀ C, Goal₁ C → Goal₂ C) (t : ℕ) :
    probReached P hn C₀ Goal₁ t ≤ probReached P hn C₀ Goal₂ t := by
  simp only [probReached]
  apply ENNReal.tsum_le_tsum
  intro C
  by_cases h1 : Goal₁ C
  · rw [if_pos h1, if_pos (h C h1)]
  · rw [if_neg h1]; exact zero_le

/-- `probReached` is the outer-measure mass of the target set for the
ordinary `t`-step distribution. -/
theorem probReached_eq_toOuterMeasure
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (t : ℕ) :
    probReached P hn C₀ Goal t =
      (nthStepDist P hn C₀ t).toOuterMeasure {C | Goal C} := by
  rw [probReached, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro C
  by_cases h : Goal C
  · rw [if_pos h]
    rw [Set.indicator_of_mem
      (s := {C : Config Q X n | Goal C})
      (a := C) (f := nthStepDist P hn C₀ t)
      (by simpa using h)]
  · rw [if_neg h]
    rw [Set.indicator_of_notMem
      (s := {C : Config Q X n | Goal C})
      (a := C) (f := nthStepDist P hn C₀ t)
      (by simpa using h)]

/-- Exact-time phase composition for `probReached`.  If the chain is in
`Mid` after `t` steps with probability at least `p`, and every `Mid` state
is in `Target` after another `k` steps with probability at least `q`, then
the chain is in `Target` after `t + k` steps with probability at least
`p * q`. -/
theorem probReached_add_ge_mul
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Mid Target : Config Q X n → Prop)
    [DecidablePred Mid] [DecidablePred Target]
    (t k : ℕ) (p q : ENNReal)
    (hMid : p ≤ probReached P hn C₀ Mid t)
    (hTarget : ∀ C : Config Q X n, Mid C →
      q ≤ probReached P hn C Target k) :
    p * q ≤ probReached P hn C₀ Target (t + k) := by
  classical
  rw [probReached_eq_toOuterMeasure P hn C₀ Target (t + k)]
  rw [nthStepDist_add]
  rw [PMF.toOuterMeasure_bind_apply]
  have hmid_mul :
      probReached P hn C₀ Mid t * q =
        ∑' C : Config Q X n,
          (nthStepDist P hn C₀ t C) *
            (if Mid C then q else 0) := by
    rw [probReached, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro C
    by_cases hC : Mid C <;> simp [hC, mul_comm]
  calc
    p * q ≤ probReached P hn C₀ Mid t * q := by
      calc
        p * q = q * p := by rw [mul_comm]
        _ ≤ q * probReached P hn C₀ Mid t := mul_le_mul_right hMid q
        _ = probReached P hn C₀ Mid t * q := by rw [mul_comm]
    _ = ∑' C : Config Q X n,
          (nthStepDist P hn C₀ t C) *
            (if Mid C then q else 0) := hmid_mul
    _ ≤ ∑' C : Config Q X n,
          (nthStepDist P hn C₀ t C) *
            (nthStepDist P hn C k).toOuterMeasure {D | Target D} := by
      apply ENNReal.tsum_le_tsum
      intro C
      by_cases hC : Mid C
      · have hq :
            q ≤ (nthStepDist P hn C k).toOuterMeasure {D | Target D} := by
          rw [← probReached_eq_toOuterMeasure P hn C Target k]
          exact hTarget C hC
        calc
          (nthStepDist P hn C₀ t C) * (if Mid C then q else 0)
              = (nthStepDist P hn C₀ t C) * q := by simp [hC]
          _ ≤ (nthStepDist P hn C₀ t C) *
              (nthStepDist P hn C k).toOuterMeasure {D | Target D} :=
                mul_le_mul_right hq _
      · simp [hC]

/-- Three-phase exact-time composition for marginal reachability. -/
theorem probReached_add_add_ge_mul3
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B C : Config Q X n → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    (tA tB tC : ℕ) (pA pB pC : ENNReal)
    (hA : pA ≤ probReached P hn C₀ A tA)
    (hAB : ∀ D : Config Q X n, A D →
      pB ≤ probReached P hn D B tB)
    (hBC : ∀ D : Config Q X n, B D →
      pC ≤ probReached P hn D C tC) :
    pA * pB * pC ≤
      probReached P hn C₀ C ((tA + tB) + tC) := by
  have hB :
      pA * pB ≤ probReached P hn C₀ B (tA + tB) :=
    probReached_add_ge_mul P hn C₀ A B tA tB pA pB hA hAB
  simpa [mul_assoc] using
    probReached_add_ge_mul P hn C₀ B C (tA + tB) tC
      (pA * pB) pC hB hBC

/-- Four-phase exact-time composition for marginal reachability. -/
theorem probReached_add_add_add_ge_mul4
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B C D : Config Q X n → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C] [DecidablePred D]
    (tA tB tC tD : ℕ) (pA pB pC pD : ENNReal)
    (hA : pA ≤ probReached P hn C₀ A tA)
    (hAB : ∀ E : Config Q X n, A E →
      pB ≤ probReached P hn E B tB)
    (hBC : ∀ E : Config Q X n, B E →
      pC ≤ probReached P hn E C tC)
    (hCD : ∀ E : Config Q X n, C E →
      pD ≤ probReached P hn E D tD) :
    pA * pB * pC * pD ≤
      probReached P hn C₀ D (((tA + tB) + tC) + tD) := by
  have hC :
      pA * pB * pC ≤
        probReached P hn C₀ C ((tA + tB) + tC) :=
    probReached_add_add_ge_mul3 P hn C₀ A B C
      tA tB tC pA pB pC hA hAB hBC
  simpa [mul_assoc] using
    probReached_add_ge_mul P hn C₀ C D ((tA + tB) + tC) tD
      (pA * pB * pC) pD hC hCD

/-- Five-phase exact-time composition for marginal reachability.  This is the
probability-composition shape used by Kanaya Table 2: no independence between
phase endpoints is assumed, only uniform conditional lower bounds from every
state in the previous phase. -/
theorem probReached_add_add_add_add_ge_mul5
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B C D E : Config Q X n → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    [DecidablePred D] [DecidablePred E]
    (tA tB tC tD tE : ℕ) (pA pB pC pD pE : ENNReal)
    (hA : pA ≤ probReached P hn C₀ A tA)
    (hAB : ∀ F : Config Q X n, A F →
      pB ≤ probReached P hn F B tB)
    (hBC : ∀ F : Config Q X n, B F →
      pC ≤ probReached P hn F C tC)
    (hCD : ∀ F : Config Q X n, C F →
      pD ≤ probReached P hn F D tD)
    (hDE : ∀ F : Config Q X n, D F →
      pE ≤ probReached P hn F E tE) :
    pA * pB * pC * pD * pE ≤
      probReached P hn C₀ E ((((tA + tB) + tC) + tD) + tE) := by
  have hD :
      pA * pB * pC * pD ≤
        probReached P hn C₀ D (((tA + tB) + tC) + tD) :=
    probReached_add_add_add_ge_mul4 P hn C₀ A B C D
      tA tB tC tD pA pB pC pD hA hAB hBC hCD
  simpa [mul_assoc] using
    probReached_add_ge_mul P hn C₀ D E (((tA + tB) + tC) + tD) tE
      (pA * pB * pC * pD) pE hD hDE

/-- One step of the lifted Markov chain that remembers whether `Goal`
has already been reached.  The boolean component is true exactly when
the initial state or some state on the finite prefix has satisfied
`Goal`. -/
noncomputable def hitFlagStepDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (S : Config Q X n × Bool) : PMF (Config Q X n × Bool) := by
  classical
  exact
    (stepDist P hn S.1).map
      (fun C' => (C', S.2 || decide (Goal C')))

/-- Distribution of the configuration after `t` sequential steps,
together with the event flag "the finite prefix has hit `Goal`". -/
noncomputable def hitFlagDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ℕ → PMF (Config Q X n × Bool)
  | 0 => by
      classical
      exact PMF.pure (C₀, decide (Goal C₀))
  | t + 1 => (hitFlagDist P hn C₀ Goal t).bind
      (hitFlagStepDist P hn Goal)

/-- Forgetting the hit flag after one lifted step recovers the ordinary
one-step scheduler distribution. -/
theorem hitFlagStepDist_map_fst
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (S : Config Q X n × Bool) :
    (hitFlagStepDist P hn Goal S).map Prod.fst = stepDist P hn S.1 := by
  classical
  unfold hitFlagStepDist
  rw [PMF.map_comp]
  simpa [Function.comp_def] using
    (PMF.map_id (p := stepDist P hn S.1))

/-- Forgetting the hit flag after `t` lifted steps recovers the ordinary
`t`-step scheduler distribution. -/
theorem hitFlagDist_map_fst
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ∀ t : ℕ,
      (hitFlagDist P hn C₀ Goal t).map Prod.fst =
        nthStepDist P hn C₀ t
  | 0 => by
      classical
      by_cases h : Goal C₀
      · rw [hitFlagDist, nthStepDist]
        simpa [h] using
          (PMF.pure_map (f := Prod.fst) (a := (C₀, true)))
      · rw [hitFlagDist, nthStepDist]
        simpa [h] using
          (PMF.pure_map (f := Prod.fst) (a := (C₀, false)))
  | t + 1 => by
      rw [hitFlagDist, nthStepDist, PMF.map_bind]
      simp only [hitFlagStepDist_map_fst]
      change
        (hitFlagDist P hn C₀ Goal t).bind ((stepDist P hn) ∘ Prod.fst) =
          (nthStepDist P hn C₀ t).bind (stepDist P hn)
      rw [← PMF.bind_map, hitFlagDist_map_fst P hn C₀ Goal t]

/-- The same hit-flag chain, but with an arbitrary initial hit flag.  This
is the block-step version needed for Markov/window composition lemmas. -/
noncomputable def hitFlagDistFrom
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop) :
    Config Q X n × Bool → ℕ → PMF (Config Q X n × Bool)
  | S, 0 => PMF.pure S
  | S, t + 1 =>
      (hitFlagDistFrom P hn Goal S t).bind (hitFlagStepDist P hn Goal)

/-- `hitFlagDist` is `hitFlagDistFrom` started with the correct initial flag. -/
theorem hitFlagDist_eq_hitFlagDistFrom
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) [DecidablePred Goal]
    (t : ℕ) :
    hitFlagDist P hn C₀ Goal t =
      hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t := by
  induction t with
  | zero =>
      by_cases h : Goal C₀
      · simp [hitFlagDist, hitFlagDistFrom, h]
      · simp [hitFlagDist, hitFlagDistFrom, h]
  | succ t ih =>
      rw [hitFlagDist, hitFlagDistFrom, ih]

/-- Semigroup law for the hit-flag chain. -/
theorem hitFlagDistFrom_add
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (S : Config Q X n × Bool) (t k : ℕ) :
    hitFlagDistFrom P hn Goal S (t + k) =
      (hitFlagDistFrom P hn Goal S t).bind
        (fun T => hitFlagDistFrom P hn Goal T k) := by
  induction k generalizing t with
  | zero =>
      simp [hitFlagDistFrom]
  | succ k ih =>
      rw [Nat.add_succ, hitFlagDistFrom, ih t]
      simp only [hitFlagDistFrom, PMF.bind_bind]

/-- Lifted-chain mass of paths whose finite prefix has hit `Hit` and whose
endpoint is in `Final`.  This is the joint event used when a later phase needs
both a past hit flag and a live endpoint condition. -/
noncomputable def probHitAndInFrom
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Hit Final : Config Q X n → Prop)
    (S : Config Q X n × Bool) (t : ℕ) : ENNReal :=
  (hitFlagDistFrom P hn Hit S t).toOuterMeasure
    {T : Config Q X n × Bool | T.2 = true ∧ Final T.1}

/-- Initial-state version of `probHitAndInFrom`. -/
noncomputable def probHitAndIn
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Hit Final : Config Q X n → Prop)
    (t : ℕ) : ENNReal :=
  (hitFlagDist P hn C₀ Hit t).toOuterMeasure
    {T : Config Q X n × Bool | T.2 = true ∧ Final T.1}

/-- A lifted finite-prefix event whose endpoint always satisfies `Goal`
contributes to exact-time `probReached Goal`.  The `Hit` parameter chooses the
hit-flag chain used to represent path information in `GoodEvent`; the theorem
does not require `GoodEvent` to mention the flag. -/
theorem probReached_ge_of_joint_event
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Hit Goal : Config Q X n → Prop)
    [DecidablePred Goal]
    (GoodEvent : Set (Config Q X n × Bool))
    (t : ℕ) (p : ENNReal)
    (hGoodMass :
      p ≤ (hitFlagDist P hn C₀ Hit t).toOuterMeasure GoodEvent)
    (hGoodGoal : ∀ S : Config Q X n × Bool, S ∈ GoodEvent → Goal S.1) :
    p ≤ probReached P hn C₀ Goal t := by
  classical
  refine hGoodMass.trans ?_
  rw [probReached_eq_toOuterMeasure]
  rw [← hitFlagDist_map_fst P hn C₀ Hit t]
  rw [PMF.toOuterMeasure_map_apply]
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro S
  by_cases hS : S ∈ GoodEvent
  · rw [Set.indicator_of_mem (s := GoodEvent)
      (a := S) (f := hitFlagDist P hn C₀ Hit t) hS]
    rw [Set.indicator_of_mem
      (s := Prod.fst ⁻¹' {C : Config Q X n | Goal C})
      (a := S) (f := hitFlagDist P hn C₀ Hit t)
      (by simpa using hGoodGoal S hS)]
  · rw [Set.indicator_of_notMem (s := GoodEvent)
      (a := S) (f := hitFlagDist P hn C₀ Hit t) hS]
    exact zero_le

/-- Specialized form of `probReached_ge_of_joint_event` for the standard
joint event carried by `probHitAndIn`. -/
theorem probReached_ge_of_probHitAndIn
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Hit Goal : Config Q X n → Prop)
    [DecidablePred Goal]
    (t : ℕ) (p : ENNReal)
    (hJoint : p ≤ probHitAndIn P hn C₀ Hit Goal t) :
    p ≤ probReached P hn C₀ Goal t := by
  exact probReached_ge_of_joint_event P hn C₀ Hit Goal
    {S : Config Q X n × Bool | S.2 = true ∧ Goal S.1} t p hJoint
    (by intro S hS; exact hS.2)

/-- Exact-time composition for the lifted hit-flag chain.  If at time `t`
there is mass at least `p` on states where `Hit` has already occurred and the
current endpoint is in `Mid`, and every such lifted state reaches the final
joint event with probability at least `q` in another `k` steps, then the final
joint event has mass at least `p*q`. -/
theorem probHitAndInFrom_add_ge_mul
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Hit Mid Final : Config Q X n → Prop)
    (S₀ : Config Q X n × Bool)
    (t k : ℕ) (p q : ENNReal)
    (hMid : p ≤ probHitAndInFrom P hn Hit Mid S₀ t)
    (hFinal : ∀ S : Config Q X n × Bool,
      S.2 = true → Mid S.1 →
        q ≤ probHitAndInFrom P hn Hit Final S k) :
    p * q ≤ probHitAndInFrom P hn Hit Final S₀ (t + k) := by
  classical
  rw [probHitAndInFrom, hitFlagDistFrom_add]
  rw [PMF.toOuterMeasure_bind_apply]
  have hmid_mul :
      probHitAndInFrom P hn Hit Mid S₀ t * q =
        ∑' S : Config Q X n × Bool,
          (hitFlagDistFrom P hn Hit S₀ t S) *
            (if S.2 = true ∧ Mid S.1 then q else 0) := by
    rw [probHitAndInFrom, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro S
    by_cases hS : S.2 = true ∧ Mid S.1
    · rw [if_pos hS]
      rw [Set.indicator_of_mem
        (s := {T : Config Q X n × Bool | T.2 = true ∧ Mid T.1})
        (a := S)
        (f := hitFlagDistFrom P hn Hit S₀ t)
        (by simpa using hS)]
    · rw [if_neg hS]
      rw [Set.indicator_of_notMem
        (s := {T : Config Q X n × Bool | T.2 = true ∧ Mid T.1})
        (a := S)
        (f := hitFlagDistFrom P hn Hit S₀ t)
        (by simpa using hS)]
      simp
  calc
    p * q ≤ probHitAndInFrom P hn Hit Mid S₀ t * q := by
      calc
        p * q = q * p := by rw [mul_comm]
        _ ≤ q * probHitAndInFrom P hn Hit Mid S₀ t :=
          mul_le_mul_right hMid q
        _ = probHitAndInFrom P hn Hit Mid S₀ t * q := by rw [mul_comm]
    _ = ∑' S : Config Q X n × Bool,
          (hitFlagDistFrom P hn Hit S₀ t S) *
            (if S.2 = true ∧ Mid S.1 then q else 0) := hmid_mul
    _ ≤ ∑' S : Config Q X n × Bool,
          (hitFlagDistFrom P hn Hit S₀ t S) *
            (hitFlagDistFrom P hn Hit S k).toOuterMeasure
              {T : Config Q X n × Bool | T.2 = true ∧ Final T.1} := by
      apply ENNReal.tsum_le_tsum
      intro S
      by_cases hS : S.2 = true ∧ Mid S.1
      · have hq :
            q ≤ (hitFlagDistFrom P hn Hit S k).toOuterMeasure
                {T : Config Q X n × Bool | T.2 = true ∧ Final T.1} := by
          simpa [probHitAndInFrom] using hFinal S hS.1 hS.2
        calc
          (hitFlagDistFrom P hn Hit S₀ t S) *
              (if S.2 = true ∧ Mid S.1 then q else 0)
              = (hitFlagDistFrom P hn Hit S₀ t S) * q := by simp [hS]
          _ ≤ (hitFlagDistFrom P hn Hit S₀ t S) *
              (hitFlagDistFrom P hn Hit S k).toOuterMeasure
                {T : Config Q X n × Bool | T.2 = true ∧ Final T.1} :=
              mul_le_mul_right hq _
      · simp [hS]

/-- Initial-state wrapper for `probHitAndInFrom_add_ge_mul`. -/
theorem probHitAndIn_add_ge_mul
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Hit Mid Final : Config Q X n → Prop)
    (t k : ℕ) (p q : ENNReal)
    (hMid : p ≤ probHitAndIn P hn C₀ Hit Mid t)
    (hFinal : ∀ S : Config Q X n × Bool,
      S.2 = true → Mid S.1 →
        q ≤ probHitAndInFrom P hn Hit Final S k) :
    p * q ≤ probHitAndIn P hn C₀ Hit Final (t + k) := by
  classical
  rw [probHitAndIn]
  rw [hitFlagDist_eq_hitFlagDistFrom P hn C₀ Hit (t + k)]
  refine probHitAndInFrom_add_ge_mul P hn Hit Mid Final
    (C₀, decide (Hit C₀)) t k p q ?_ hFinal
  simpa [probHitAndIn, probHitAndInFrom,
    hitFlagDist_eq_hitFlagDistFrom P hn C₀ Hit t] using hMid

/-- Starting from a false hit flag at a non-goal configuration agrees with
the ordinary hit distribution from that configuration. -/
theorem hitFlagDistFrom_false_eq_hitFlagDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀) (t : ℕ) :
    hitFlagDistFrom P hn Goal (C₀, false) t =
      hitFlagDist P hn C₀ Goal t := by
  classical
  rw [hitFlagDist_eq_hitFlagDistFrom]
  simp [hGoal]

/-- One step of the lifted chain carrying two hit flags at once. -/
noncomputable def hitTwoFlagStepDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (A B : Config Q X n → Prop)
    (S : Config Q X n × (Bool × Bool)) :
    PMF (Config Q X n × (Bool × Bool)) := by
  classical
  exact
    (stepDist P hn S.1).map
      (fun C' =>
        (C', (S.2.1 || decide (A C'), S.2.2 || decide (B C'))))

/-- Finite-prefix distribution carrying two hit flags. -/
noncomputable def hitTwoFlagDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (A B : Config Q X n → Prop) :
    ℕ → PMF (Config Q X n × (Bool × Bool))
  | 0 => by
      classical
      exact PMF.pure (C₀, (decide (A C₀), decide (B C₀)))
  | t + 1 => (hitTwoFlagDist P hn C₀ A B t).bind
      (hitTwoFlagStepDist P hn A B)

theorem hitTwoFlagStepDist_map_left
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (A B : Config Q X n → Prop)
    (S : Config Q X n × (Bool × Bool)) :
    (hitTwoFlagStepDist P hn A B S).map (fun T => (T.1, T.2.1)) =
      hitFlagStepDist P hn A (S.1, S.2.1) := by
  classical
  unfold hitTwoFlagStepDist hitFlagStepDist
  rw [PMF.map_comp]
  rfl

theorem hitTwoFlagStepDist_map_right
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (A B : Config Q X n → Prop)
    (S : Config Q X n × (Bool × Bool)) :
    (hitTwoFlagStepDist P hn A B S).map (fun T => (T.1, T.2.2)) =
      hitFlagStepDist P hn B (S.1, S.2.2) := by
  classical
  unfold hitTwoFlagStepDist hitFlagStepDist
  rw [PMF.map_comp]
  rfl

theorem hitTwoFlagStepDist_map_or
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (A B : Config Q X n → Prop)
    (S : Config Q X n × (Bool × Bool)) :
    (hitTwoFlagStepDist P hn A B S).map
        (fun T => (T.1, T.2.1 || T.2.2)) =
      hitFlagStepDist P hn (fun C => A C ∨ B C)
        (S.1, S.2.1 || S.2.2) := by
  classical
  unfold hitTwoFlagStepDist hitFlagStepDist
  rw [PMF.map_comp]
  congr 1
  funext C'
  by_cases hA : A C' <;> by_cases hB : B C' <;> simp [hA, hB]

theorem hitTwoFlagDist_map_left
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (A B : Config Q X n → Prop) :
    ∀ t : ℕ,
      (hitTwoFlagDist P hn C₀ A B t).map (fun S => (S.1, S.2.1)) =
        hitFlagDist P hn C₀ A t
  | 0 => by
      classical
      by_cases hA : A C₀
      · simpa [hitTwoFlagDist, hitFlagDist, hA] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × Bool) => (S.1, S.2.1))
            (a := (C₀, (true, decide (B C₀)))))
      · simpa [hitTwoFlagDist, hitFlagDist, hA] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × Bool) => (S.1, S.2.1))
            (a := (C₀, (false, decide (B C₀)))))
  | t + 1 => by
      rw [hitTwoFlagDist, hitFlagDist, PMF.map_bind]
      simp only [hitTwoFlagStepDist_map_left]
      change
        (hitTwoFlagDist P hn C₀ A B t).bind
            (hitFlagStepDist P hn A ∘ fun S => (S.1, S.2.1)) =
          (hitFlagDist P hn C₀ A t).bind (hitFlagStepDist P hn A)
      rw [← PMF.bind_map, hitTwoFlagDist_map_left P hn C₀ A B t]

theorem hitTwoFlagDist_map_right
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (A B : Config Q X n → Prop) :
    ∀ t : ℕ,
      (hitTwoFlagDist P hn C₀ A B t).map (fun S => (S.1, S.2.2)) =
        hitFlagDist P hn C₀ B t
  | 0 => by
      classical
      by_cases hB : B C₀
      · simpa [hitTwoFlagDist, hitFlagDist, hB] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × Bool) => (S.1, S.2.2))
            (a := (C₀, (decide (A C₀), true))))
      · simpa [hitTwoFlagDist, hitFlagDist, hB] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × Bool) => (S.1, S.2.2))
            (a := (C₀, (decide (A C₀), false))))
  | t + 1 => by
      rw [hitTwoFlagDist, hitFlagDist, PMF.map_bind]
      simp only [hitTwoFlagStepDist_map_right]
      change
        (hitTwoFlagDist P hn C₀ A B t).bind
            (hitFlagStepDist P hn B ∘ fun S => (S.1, S.2.2)) =
          (hitFlagDist P hn C₀ B t).bind (hitFlagStepDist P hn B)
      rw [← PMF.bind_map, hitTwoFlagDist_map_right P hn C₀ A B t]

theorem hitTwoFlagDist_map_or
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (A B : Config Q X n → Prop) :
    ∀ t : ℕ,
      (hitTwoFlagDist P hn C₀ A B t).map
          (fun S => (S.1, S.2.1 || S.2.2)) =
        hitFlagDist P hn C₀ (fun C => A C ∨ B C) t
  | 0 => by
      classical
      by_cases hA : A C₀ <;> by_cases hB : B C₀
      · simpa [hitTwoFlagDist, hitFlagDist, hA, hB] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × Bool) =>
              (S.1, S.2.1 || S.2.2))
            (a := (C₀, (true, true))))
      · simpa [hitTwoFlagDist, hitFlagDist, hA, hB] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × Bool) =>
              (S.1, S.2.1 || S.2.2))
            (a := (C₀, (true, false))))
      · simpa [hitTwoFlagDist, hitFlagDist, hA, hB] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × Bool) =>
              (S.1, S.2.1 || S.2.2))
            (a := (C₀, (false, true))))
      · simpa [hitTwoFlagDist, hitFlagDist, hA, hB] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × Bool) =>
              (S.1, S.2.1 || S.2.2))
            (a := (C₀, (false, false))))
  | t + 1 => by
      rw [hitTwoFlagDist, hitFlagDist, PMF.map_bind]
      simp only [hitTwoFlagStepDist_map_or]
      change
        (hitTwoFlagDist P hn C₀ A B t).bind
            (hitFlagStepDist P hn (fun C => A C ∨ B C) ∘
              fun S => (S.1, S.2.1 || S.2.2)) =
          (hitFlagDist P hn C₀ (fun C => A C ∨ B C) t).bind
            (hitFlagStepDist P hn (fun C => A C ∨ B C))
      rw [← PMF.bind_map, hitTwoFlagDist_map_or P hn C₀ A B t]

private theorem hitTwoFlagDist_support_left_true_right_false_of_mono
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (A B : Config Q X n → Prop)
    (hmono : ∀ C : Config Q X n, A C → B C) :
    ∀ t : ℕ, ∀ S : Config Q X n × (Bool × Bool),
      S ∈ (hitTwoFlagDist P hn C₀ A B t).support →
        S.2.1 = true → S.2.2 = false → False
  | 0, S => by
      classical
      intro hS hleft hright
      rw [hitTwoFlagDist, PMF.support_pure] at hS
      subst S
      by_cases hA : A C₀
      · have hB : B C₀ := hmono C₀ hA
        simp [hB] at hright
      · simp [hA] at hleft
  | t + 1, S => by
      classical
      intro hS hleft hright
      rw [hitTwoFlagDist, PMF.mem_support_bind_iff] at hS
      obtain ⟨T, hT, hStep⟩ := hS
      rcases T with ⟨C, bc⟩
      rw [hitTwoFlagStepDist, PMF.support_map] at hStep
      obtain ⟨D, hD, hEq⟩ := hStep
      have hleft_step :=
        (congrArg (fun U : Config Q X n × (Bool × Bool) => U.2.1) hEq).trans
          hleft
      have hright_step :=
        (congrArg (fun U : Config Q X n × (Bool × Bool) => U.2.2) hEq).trans
          hright
      have hleft_or :
          bc.1 = true ∨ A D := by
        cases hbc : bc.1
        · right
          by_contra hAD
          have hcontr := hleft_step
          simp [hbc, hAD] at hcontr
        · left
          rfl
      have hright_false : bc.2 = false := by
        cases hbc : bc.2
        · rfl
        · exfalso
          have hcontr := hright_step
          simp [hbc] at hcontr
      have hnotB : ¬ B D := by
        intro hBD
        have hcontr := hright_step
        simp [hright_false, hBD] at hcontr
      rcases hleft_or with hprev | hAD
      · exact hitTwoFlagDist_support_left_true_right_false_of_mono
          P hn C₀ A B hmono t (C, bc) hT hprev hright_false
      · exact hnotB (hmono D hAD)

private theorem hitTwoFlagDist_support_inv
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (A B Inv : Config Q X n → Prop)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j)) :
    ∀ t : ℕ, ∀ S : Config Q X n × (Bool × Bool),
      S ∈ (hitTwoFlagDist P hn C₀ A B t).support → Inv S.1
  | 0, S => by
      intro hS
      rw [hitTwoFlagDist, PMF.support_pure] at hS
      subst S
      exact hInv₀
  | t + 1, S => by
      intro hS
      rw [hitTwoFlagDist, PMF.mem_support_bind_iff] at hS
      obtain ⟨T, hT, hStep⟩ := hS
      rcases T with ⟨C, bc⟩
      rw [hitTwoFlagStepDist, PMF.support_map] at hStep
      obtain ⟨D, hD, hEq⟩ := hStep
      subst S
      rw [stepDist, PMF.support_map] at hD
      obtain ⟨p, _hp, hpEq⟩ := hD
      subst D
      exact hInvStep C
        (hitTwoFlagDist_support_inv P hn C₀ A B Inv hInv₀ hInvStep t (C, bc) hT)
        p.1 p.2

private theorem hitTwoFlagDist_support_left_true_right_false_of_mono_inv
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (A B Inv : Config Q X n → Prop)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (hmono : ∀ C : Config Q X n, Inv C → A C → B C) :
    ∀ t : ℕ, ∀ S : Config Q X n × (Bool × Bool),
      S ∈ (hitTwoFlagDist P hn C₀ A B t).support →
        S.2.1 = true → S.2.2 = false → False
  | 0, S => by
      classical
      intro hS hleft hright
      rw [hitTwoFlagDist, PMF.support_pure] at hS
      subst S
      by_cases hA : A C₀
      · have hB : B C₀ := hmono C₀ hInv₀ hA
        simp [hB] at hright
      · simp [hA] at hleft
  | t + 1, S => by
      classical
      intro hS hleft hright
      rw [hitTwoFlagDist, PMF.mem_support_bind_iff] at hS
      obtain ⟨T, hT, hStep⟩ := hS
      rcases T with ⟨C, bc⟩
      rw [hitTwoFlagStepDist, PMF.support_map] at hStep
      obtain ⟨D, hD, hEq⟩ := hStep
      have hleft_step :=
        (congrArg (fun U : Config Q X n × (Bool × Bool) => U.2.1) hEq).trans
          hleft
      have hright_step :=
        (congrArg (fun U : Config Q X n × (Bool × Bool) => U.2.2) hEq).trans
          hright
      have hleft_or :
          bc.1 = true ∨ A D := by
        cases hbc : bc.1
        · right
          by_contra hAD
          have hcontr := hleft_step
          simp [hbc, hAD] at hcontr
        · left
          rfl
      have hright_false : bc.2 = false := by
        cases hbc : bc.2
        · rfl
        · exfalso
          have hcontr := hright_step
          simp [hbc] at hcontr
      have hnotB : ¬ B D := by
        intro hBD
        have hcontr := hright_step
        simp [hright_false, hBD] at hcontr
      rcases hleft_or with hprev | hAD
      · exact hitTwoFlagDist_support_left_true_right_false_of_mono_inv
          P hn C₀ A B Inv hInv₀ hInvStep hmono t (C, bc) hT hprev
          hright_false
      · have hInvD : Inv D := by
          have hInvC : Inv C :=
            hitTwoFlagDist_support_inv P hn C₀ A B Inv hInv₀ hInvStep
              t (C, bc) hT
          rw [stepDist, PMF.support_map] at hD
          obtain ⟨p, _hp, hpEq⟩ := hD
          rw [← hpEq]
          exact hInvStep C hInvC p.1 p.2
        exact hnotB (hmono D hInvD hAD)

/-- Tail mass for the arbitrary-start hit-flag chain. -/
noncomputable def probNotHitFrom
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (S : Config Q X n × Bool) (t : ℕ) : ENNReal :=
  ∑' T : Config Q X n × Bool,
    if T.2 = false then hitFlagDistFrom P hn Goal S t T else 0

/-- `probNotHitFrom` is the outer-measure mass of false hit-flag states. -/
theorem probNotHitFrom_eq_toOuterMeasure
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (S : Config Q X n × Bool) (t : ℕ) :
    probNotHitFrom P hn Goal S t =
      (hitFlagDistFrom P hn Goal S t).toOuterMeasure
        {T : Config Q X n × Bool | T.2 = false} := by
  rw [probNotHitFrom, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro T
  by_cases h : T.2 = false
  · rw [if_pos h]
    rw [Set.indicator_of_mem
      (s := {T : Config Q X n × Bool | T.2 = false})
      (a := T) (f := hitFlagDistFrom P hn Goal S t)
      (by simpa using h)]
  · rw [if_neg h]
    rw [Set.indicator_of_notMem
      (s := {T : Config Q X n × Bool | T.2 = false})
      (a := T) (f := hitFlagDistFrom P hn Goal S t)
      (by simpa using h)]

/-- Tail probability `P[T > t]`, where `T` is the first hitting time of
`Goal`.  Equivalently, the hit flag is still false after the finite
prefix of length `t`. -/
noncomputable def probNotHitBy
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) : ENNReal :=
  ∑' S : Config Q X n × Bool,
    if S.2 = false then (hitFlagDist P hn C₀ Goal t) S else 0

/-- Probability `P[T ≤ t]`, where `T` is the first hitting time of
`Goal`.  This is the finite-prefix hit event and is the natural entry
point for high-probability statements. -/
noncomputable def probHitBy
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) : ENNReal :=
  ∑' S : Config Q X n × Bool,
    if S.2 = true then (hitFlagDist P hn C₀ Goal t) S else 0

/-- Conventional theorem-statement name for finite-window hitting
probability.  `ProbHitWithin P hn C₀ Goal t` is `P[T ≤ t]`. -/
noncomputable abbrev ProbHitWithin
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) : ENNReal :=
  probHitBy P hn C₀ Goal t

/-- The finite-prefix hit and non-hit events partition the probability
mass. -/
theorem probHitBy_add_probNotHitBy
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    probHitBy P hn C₀ Goal t + probNotHitBy P hn C₀ Goal t = 1 := by
  classical
  rw [probHitBy, probNotHitBy, ← ENNReal.tsum_add]
  trans ∑' S : Config Q X n × Bool, (hitFlagDist P hn C₀ Goal t) S
  · apply tsum_congr
    intro S
    cases S.2 <;> simp
  · exact PMF.tsum_coe _

/-- `probHitBy` is the `PMF` mass of the true hit-flag states. -/
theorem probHitBy_eq_hitFlagDist_toOuterMeasure
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    probHitBy P hn C₀ Goal t =
      (hitFlagDist P hn C₀ Goal t).toOuterMeasure {S | S.2 = true} := by
  rw [probHitBy, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro S
  by_cases h : S.2 = true
  · rw [if_pos h]
    rw [Set.indicator_of_mem
      (s := {S : Config Q X n × Bool | S.2 = true})
      (a := S) (f := hitFlagDist P hn C₀ Goal t)
      (by simpa using h)]
  · rw [if_neg h]
    rw [Set.indicator_of_notMem
      (s := {S : Config Q X n × Bool | S.2 = true})
      (a := S) (f := hitFlagDist P hn C₀ Goal t)
      (by simpa using h)]

/-- `probNotHitBy` is the `PMF` mass of the false hit-flag states. -/
theorem probNotHitBy_eq_hitFlagDist_toOuterMeasure
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    probNotHitBy P hn C₀ Goal t =
      (hitFlagDist P hn C₀ Goal t).toOuterMeasure {S | S.2 = false} := by
  rw [probNotHitBy, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro S
  by_cases h : S.2 = false
  · rw [if_pos h]
    rw [Set.indicator_of_mem
      (s := {S : Config Q X n × Bool | S.2 = false})
      (a := S) (f := hitFlagDist P hn C₀ Goal t)
      (by simpa using h)]
  · rw [if_neg h]
    rw [Set.indicator_of_notMem
      (s := {S : Config Q X n × Bool | S.2 = false})
      (a := S) (f := hitFlagDist P hn C₀ Goal t)
      (by simpa using h)]

/-- Finite-prefix hit probability is monotone in the target predicate. -/
theorem ProbHitWithin_mono_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B : Config Q X n → Prop)
    (hmono : ∀ C : Config Q X n, A C → B C) (t : ℕ) :
    ProbHitWithin P hn C₀ A t ≤ ProbHitWithin P hn C₀ B t := by
  classical
  change probHitBy P hn C₀ A t ≤ probHitBy P hn C₀ B t
  rw [probHitBy_eq_hitFlagDist_toOuterMeasure]
  rw [show probHitBy P hn C₀ B t =
      (hitTwoFlagDist P hn C₀ A B t).toOuterMeasure {S | S.2.2 = true} by
        rw [probHitBy_eq_hitFlagDist_toOuterMeasure,
          ← hitTwoFlagDist_map_right P hn C₀ A B t, PMF.toOuterMeasure_map_apply]
        congr 1]
  rw [← hitTwoFlagDist_map_left P hn C₀ A B t, PMF.toOuterMeasure_map_apply]
  change
    (hitTwoFlagDist P hn C₀ A B t).toOuterMeasure {S | S.2.1 = true} ≤
      (hitTwoFlagDist P hn C₀ A B t).toOuterMeasure {S | S.2.2 = true}
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro S
  by_cases hleft : S.2.1 = true
  · by_cases hright : S.2.2 = true
    · simp [hleft, hright]
    · have hright_false : S.2.2 = false := by
        cases hS2 : S.2.2
        · rfl
        · exact False.elim (hright (by simp [hS2]))
      have hzero : hitTwoFlagDist P hn C₀ A B t S = 0 := by
        rw [PMF.apply_eq_zero_iff]
        intro hS
        exact hitTwoFlagDist_support_left_true_right_false_of_mono
          P hn C₀ A B hmono t S hS hleft hright_false
      simp [hleft, hright, hzero]
  · simp [hleft]

/-- If `Inv` is preserved by every protocol step and holds initially, then
adding `Inv` to the hit target does not change finite-prefix hitting
probability.  This is useful for threading protocol invariants, such as timer
upper bounds, through non-absorbing phase targets. -/
theorem ProbHitWithin_eq_and_inv_of_invariant
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Goal Inv : Config Q X n → Prop)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (t : ℕ) :
    ProbHitWithin P hn C₀ (fun C => Goal C ∧ Inv C) t =
      ProbHitWithin P hn C₀ Goal t := by
  classical
  apply le_antisymm
  · exact ProbHitWithin_mono_goal P hn C₀
      (fun C => Goal C ∧ Inv C) Goal (fun C hC => hC.1) t
  · change probHitBy P hn C₀ Goal t ≤
      probHitBy P hn C₀ (fun C => Goal C ∧ Inv C) t
    rw [probHitBy_eq_hitFlagDist_toOuterMeasure]
    rw [show probHitBy P hn C₀ (fun C => Goal C ∧ Inv C) t =
        (hitTwoFlagDist P hn C₀ Goal (fun C => Goal C ∧ Inv C) t).toOuterMeasure
          {S | S.2.2 = true} by
          rw [probHitBy_eq_hitFlagDist_toOuterMeasure,
            ← hitTwoFlagDist_map_right P hn C₀ Goal
              (fun C => Goal C ∧ Inv C) t, PMF.toOuterMeasure_map_apply]
          congr 1]
    rw [← hitTwoFlagDist_map_left P hn C₀ Goal
      (fun C => Goal C ∧ Inv C) t, PMF.toOuterMeasure_map_apply]
    change
      (hitTwoFlagDist P hn C₀ Goal (fun C => Goal C ∧ Inv C) t).toOuterMeasure
          {S | S.2.1 = true} ≤
        (hitTwoFlagDist P hn C₀ Goal (fun C => Goal C ∧ Inv C) t).toOuterMeasure
          {S | S.2.2 = true}
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    apply ENNReal.tsum_le_tsum
    intro S
    by_cases hleft : S.2.1 = true
    · by_cases hright : S.2.2 = true
      · simp [hleft, hright]
      · have hright_false : S.2.2 = false := by
          cases hS2 : S.2.2
          · rfl
          · exact False.elim (hright (by simp [hS2]))
        have hzero :
            hitTwoFlagDist P hn C₀ Goal (fun C => Goal C ∧ Inv C) t S = 0 := by
          rw [PMF.apply_eq_zero_iff]
          intro hS
          exact hitTwoFlagDist_support_left_true_right_false_of_mono_inv
            P hn C₀ Goal (fun C => Goal C ∧ Inv C) Inv hInv₀ hInvStep
            (fun C hInvC hGoalC => ⟨hGoalC, hInvC⟩)
            t S hS hleft hright_false
        simp [hleft, hright, hzero]
    · simp [hleft]

/-- Union bound for ProbHitWithin: the hit probability of a disjunction
is at most the sum of the individual hit probabilities. -/
theorem ProbHitWithin_union_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B : Config Q X n → Prop) [DecidablePred A] [DecidablePred B] (t : ℕ) :
    ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t ≤
      ProbHitWithin P hn C₀ A t + ProbHitWithin P hn C₀ B t := by
  classical
  let μ := hitTwoFlagDist P hn C₀ A B t
  change probHitBy P hn C₀ (fun C => A C ∨ B C) t ≤
    probHitBy P hn C₀ A t + probHitBy P hn C₀ B t
  have hOr : probHitBy P hn C₀ (fun C => A C ∨ B C) t =
      μ.toOuterMeasure {S | S.2.1 || S.2.2 = true} := by
    rw [probHitBy_eq_hitFlagDist_toOuterMeasure,
      ← hitTwoFlagDist_map_or P hn C₀ A B t, PMF.toOuterMeasure_map_apply]
    congr 1; ext ⟨c, fA, fB⟩; simp [Set.mem_preimage, Bool.or_eq_true]
  have hLeft : probHitBy P hn C₀ A t =
      μ.toOuterMeasure {S | S.2.1 = true} := by
    rw [probHitBy_eq_hitFlagDist_toOuterMeasure,
      ← hitTwoFlagDist_map_left P hn C₀ A B t, PMF.toOuterMeasure_map_apply]
    simpa [μ]
  have hRight : probHitBy P hn C₀ B t =
      μ.toOuterMeasure {S | S.2.2 = true} := by
    rw [probHitBy_eq_hitFlagDist_toOuterMeasure,
      ← hitTwoFlagDist_map_right P hn C₀ A B t, PMF.toOuterMeasure_map_apply]
    simpa [μ]
  rw [hOr, hLeft, hRight]
  simp only [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro ⟨c, fA, fB⟩
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  cases fA <;> cases fB <;> simp

/-! ### Event-counting distribution

Tracks how many times a specific pair-event occurs alongside the
Markov chain state and the hit flag. The key application is
`ProbHitWithin_le_of_exit_count`: if BadGoal is only reachable after
≥K occurrences of Event, then ProbHitWithin(BadGoal, t) ≤ tp/K
where p = P(Event per step). -/

noncomputable def eventCountStepDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Event : Config Q X n → Fin n → Fin n → Bool)
    (S : Config Q X n × ℕ) : PMF (Config Q X n × ℕ) :=
  (uniformPair n hn).map
    (fun pair => (S.1.step P pair.1 pair.2,
      S.2 + if Event S.1 pair.1 pair.2 then 1 else 0))

noncomputable def eventCountDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Event : Config Q X n → Fin n → Fin n → Bool) :
    ℕ → PMF (Config Q X n × ℕ)
  | 0 => PMF.pure (C₀, 0)
  | t + 1 => (eventCountDist P hn C₀ Event t).bind
      (eventCountStepDist P hn Event)

private noncomputable def goalFlag
    (Goal : Config Q X n → Prop) (C : Config Q X n) : Bool := by
  classical
  exact decide (Goal C)

noncomputable def hitEventCountStepDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (Event : Config Q X n → Fin n → Fin n → Bool)
    (S : Config Q X n × (Bool × ℕ)) :
    PMF (Config Q X n × (Bool × ℕ)) := by
  classical
  exact
    (uniformPair n hn).map
      (fun pair =>
        let C' := S.1.step P pair.1 pair.2
        (C', (S.2.1 || goalFlag Goal C',
          S.2.2 + if Event S.1 pair.1 pair.2 then 1 else 0)))

noncomputable def hitEventCountDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (Event : Config Q X n → Fin n → Fin n → Bool) :
    ℕ → PMF (Config Q X n × (Bool × ℕ))
  | 0 => by
      classical
      exact PMF.pure (C₀, (goalFlag Goal C₀, 0))
  | t + 1 => (hitEventCountDist P hn C₀ Goal Event t).bind
      (hitEventCountStepDist P hn Goal Event)

theorem hitEventCountDist_marginal_hitFlag
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (Event : Config Q X n → Fin n → Fin n → Bool)
    [DecidablePred Goal] (t : ℕ) :
    (hitEventCountDist P hn C₀ Goal Event t).map
        (fun S : Config Q X n × (Bool × ℕ) => (S.1, S.2.1)) =
      hitFlagDist P hn C₀ Goal t := by
  induction t with
  | zero =>
      rw [hitEventCountDist, hitFlagDist]
      by_cases h : Goal C₀
      · simpa [goalFlag, h] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × ℕ) => (S.1, S.2.1))
            (a := (C₀, (true, 0))))
      · simpa [goalFlag, h] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × ℕ) => (S.1, S.2.1))
            (a := (C₀, (false, 0))))
  | succ t ih =>
      rw [hitEventCountDist, hitFlagDist, PMF.map_bind]
      have hstep : ∀ S : Config Q X n × (Bool × ℕ),
          (hitEventCountStepDist P hn Goal Event S).map
              (fun T : Config Q X n × (Bool × ℕ) => (T.1, T.2.1)) =
            hitFlagStepDist P hn Goal (S.1, S.2.1) := by
        intro S
        unfold hitEventCountStepDist hitFlagStepDist stepDist
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      simp only [hstep]
      change
        (hitEventCountDist P hn C₀ Goal Event t).bind
            ((hitFlagStepDist P hn Goal) ∘
              (fun S : Config Q X n × (Bool × ℕ) => (S.1, S.2.1))) =
          (hitFlagDist P hn C₀ Goal t).bind (hitFlagStepDist P hn Goal)
      rw [← PMF.bind_map, ih]

theorem hitEventCountDist_marginal_eventCount
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (Event : Config Q X n → Fin n → Fin n → Bool)
    [DecidablePred Goal] (t : ℕ) :
    (hitEventCountDist P hn C₀ Goal Event t).map
        (fun S : Config Q X n × (Bool × ℕ) => (S.1, S.2.2)) =
      eventCountDist P hn C₀ Event t := by
  induction t with
  | zero =>
      rw [hitEventCountDist, eventCountDist]
      by_cases h : Goal C₀
      · simpa [goalFlag, h] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × ℕ) => (S.1, S.2.2))
            (a := (C₀, (true, 0))))
      · simpa [goalFlag, h] using
          (PMF.pure_map
            (f := fun S : Config Q X n × (Bool × ℕ) => (S.1, S.2.2))
            (a := (C₀, (false, 0))))
  | succ t ih =>
      rw [hitEventCountDist, eventCountDist, PMF.map_bind]
      have hstep : ∀ S : Config Q X n × (Bool × ℕ),
          (hitEventCountStepDist P hn Goal Event S).map
              (fun T : Config Q X n × (Bool × ℕ) => (T.1, T.2.2)) =
            eventCountStepDist P hn Event (S.1, S.2.2) := by
        intro S
        unfold hitEventCountStepDist eventCountStepDist
        rw [PMF.map_comp]
        rfl
      simp only [hstep]
      change
        (hitEventCountDist P hn C₀ Goal Event t).bind
            ((eventCountStepDist P hn Event) ∘
              (fun S : Config Q X n × (Bool × ℕ) => (S.1, S.2.2))) =
          (eventCountDist P hn C₀ Event t).bind (eventCountStepDist P hn Event)
      rw [← PMF.bind_map, ih]

private theorem toOuterMeasure_le_of_support_imp
    {α : Type*} (μ : PMF α) (A B : Set α)
    (h : ∀ a : α, μ a ≠ 0 → a ∈ A → a ∈ B) :
    μ.toOuterMeasure A ≤ μ.toOuterMeasure B := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases hA : a ∈ A
  · rw [Set.indicator_of_mem hA]
    by_cases hB : a ∈ B
    · rw [Set.indicator_of_mem hB]
    · rw [Set.indicator_of_notMem hB]
      have hzero : μ a = 0 := by
        by_contra hne
        exact hB (h a hne hA)
      simp [hzero]
  · rw [Set.indicator_of_notMem hA]
    exact zero_le

/-- The non-hit tail is monotone contravariantly in the goal predicate:
enlarging the target can only make the first hit happen earlier. -/
theorem probNotHitBy_mono_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B : Config Q X n → Prop)
    (hmono : ∀ C : Config Q X n, A C → B C) (t : ℕ) :
    probNotHitBy P hn C₀ B t ≤ probNotHitBy P hn C₀ A t := by
  classical
  let μ := hitTwoFlagDist P hn C₀ A B t
  have hB :
      probNotHitBy P hn C₀ B t =
        μ.toOuterMeasure {S : Config Q X n × (Bool × Bool) | S.2.2 = false} := by
    rw [probNotHitBy_eq_hitFlagDist_toOuterMeasure,
      ← hitTwoFlagDist_map_right P hn C₀ A B t, PMF.toOuterMeasure_map_apply]
    simpa [μ]
  have hA :
      probNotHitBy P hn C₀ A t =
        μ.toOuterMeasure {S : Config Q X n × (Bool × Bool) | S.2.1 = false} := by
    rw [probNotHitBy_eq_hitFlagDist_toOuterMeasure,
      ← hitTwoFlagDist_map_left P hn C₀ A B t, PMF.toOuterMeasure_map_apply]
    simpa [μ]
  rw [hB, hA]
  apply toOuterMeasure_le_of_support_imp
  intro S hS hRightFalse
  by_cases hLeftTrue : S.2.1 = true
  · have hSupp : S ∈ (hitTwoFlagDist P hn C₀ A B t).support := by
      simpa [μ, PMF.mem_support_iff] using hS
    exact False.elim
      (hitTwoFlagDist_support_left_true_right_false_of_mono
        P hn C₀ A B hmono t S hSupp hLeftTrue hRightFalse)
  · cases hLeft : S.2.1
    · exact hLeft
    · exact False.elim (hLeftTrue hLeft)

theorem ProbHitWithin_le_eventCountDist_tail_of_support_imp
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (Event : Config Q X n → Fin n → Fin n → Bool)
    [DecidablePred Goal] (t K : ℕ)
    (h :
      ∀ S : Config Q X n × (Bool × ℕ),
        hitEventCountDist P hn C₀ Goal Event t S ≠ 0 →
          S.2.1 = true → K ≤ S.2.2) :
    ProbHitWithin P hn C₀ Goal t ≤
      (eventCountDist P hn C₀ Event t).toOuterMeasure
        {S : Config Q X n × ℕ | K ≤ S.2} := by
  classical
  let μ := hitEventCountDist P hn C₀ Goal Event t
  let hitSet : Set (Config Q X n × (Bool × ℕ)) := {S | S.2.1 = true}
  let countSet : Set (Config Q X n × (Bool × ℕ)) := {S | K ≤ S.2.2}
  have hhit_count :
      μ.toOuterMeasure hitSet ≤ μ.toOuterMeasure countSet :=
    toOuterMeasure_le_of_support_imp μ hitSet countSet (by
      intro S hμ hhit
      exact h S (by simpa [μ] using hμ) hhit)
  calc
    ProbHitWithin P hn C₀ Goal t
        = (hitFlagDist P hn C₀ Goal t).toOuterMeasure
            {S : Config Q X n × Bool | S.2 = true} := by
          simpa [ProbHitWithin] using
            (probHitBy_eq_hitFlagDist_toOuterMeasure
              (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal) (t := t))
    _ = μ.toOuterMeasure hitSet := by
          rw [← hitEventCountDist_marginal_hitFlag
            (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal)
            (Event := Event) (t := t)]
          rw [PMF.toOuterMeasure_map_apply]
          rfl
    _ ≤ μ.toOuterMeasure countSet := hhit_count
    _ = (eventCountDist P hn C₀ Event t).toOuterMeasure
          {S : Config Q X n × ℕ | K ≤ S.2} := by
          rw [← hitEventCountDist_marginal_eventCount
            (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal)
            (Event := Event) (t := t)]
          rw [PMF.toOuterMeasure_map_apply]
          rfl

theorem hitEventCountDist_support_inv
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (Event : Config Q X n → Fin n → Fin n → Bool)
    [DecidablePred Goal]
    (Inv : Config Q X n × (Bool × ℕ) → Prop)
    (h0 : Inv (C₀, (goalFlag Goal C₀, 0)))
    (hstep :
      ∀ S : Config Q X n × (Bool × ℕ),
        Inv S →
          ∀ p : Fin n × Fin n, p ∈ (uniformPair n hn).support →
            Inv
              (let C' : Config Q X n := S.1.step P p.1 p.2
               (C', (S.2.1 || goalFlag Goal C',
                 S.2.2 + if Event S.1 p.1 p.2 then 1 else 0)))) :
    ∀ t : ℕ, ∀ S : Config Q X n × (Bool × ℕ),
      S ∈ (hitEventCountDist P hn C₀ Goal Event t).support → Inv S := by
  intro t
  induction t with
  | zero =>
      intro S hS
      rw [hitEventCountDist] at hS
      have hEq :
          S = (C₀, (goalFlag Goal C₀, 0)) := by
        simpa [PMF.mem_support_pure_iff] using hS
      simpa [hEq] using h0
  | succ t ih =>
      intro S hS
      rw [hitEventCountDist] at hS
      rw [PMF.mem_support_bind_iff] at hS
      rcases hS with ⟨T, hT, hST⟩
      have hInvT := ih T hT
      unfold hitEventCountStepDist at hST
      rw [PMF.mem_support_map_iff] at hST
      rcases hST with ⟨p, hp, hpEq⟩
      rw [← hpEq]
      exact hstep T hInvT p hp

theorem hitEventCountDist_support_inv_decide
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (Event : Config Q X n → Fin n → Fin n → Bool)
    [DecidablePred Goal]
    (Inv : Config Q X n × (Bool × ℕ) → Prop)
    (h0 : Inv (C₀, (decide (Goal C₀), 0)))
    (hstep :
      ∀ S : Config Q X n × (Bool × ℕ),
        Inv S →
          ∀ p : Fin n × Fin n, p ∈ (uniformPair n hn).support →
            Inv
              (let C' : Config Q X n := S.1.step P p.1 p.2
               (C', (S.2.1 || decide (Goal C'),
                 S.2.2 + if Event S.1 p.1 p.2 then 1 else 0)))) :
    ∀ t : ℕ, ∀ S : Config Q X n × (Bool × ℕ),
      S ∈ (hitEventCountDist P hn C₀ Goal Event t).support → Inv S := by
  classical
  refine hitEventCountDist_support_inv
    (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal) (Event := Event)
    (Inv := Inv) ?_ ?_
  · by_cases h : Goal C₀
    · simpa [goalFlag, h] using h0
    · simpa [goalFlag, h] using h0
  · intro S hInv p hp
    by_cases h : Goal (S.1.step P p.1 p.2)
    · simpa [goalFlag, h] using hstep S hInv p hp
    · simpa [goalFlag, h] using hstep S hInv p hp

private noncomputable def eventCountMean
    (μ : PMF (Config Q X n × ℕ)) : ENNReal :=
  ∑' S : Config Q X n × ℕ, μ S * (S.2 : ENNReal)

private theorem eventCountMean_pure (S : Config Q X n × ℕ) :
    eventCountMean (PMF.pure S) = (S.2 : ENNReal) := by
  unfold eventCountMean
  rw [tsum_eq_single S]
  · simp
  · intro T hT
    rw [PMF.pure_apply_of_ne S T hT]
    simp

private theorem eventCountMean_bind
    (μ : PMF α) (F : α → PMF (Config Q X n × ℕ)) :
    eventCountMean (μ.bind F) =
      ∑' a : α, μ a * eventCountMean (F a) := by
  unfold eventCountMean
  simp only [PMF.bind_apply]
  calc
    ∑' S : Config Q X n × ℕ,
        (∑' a : α, μ a * F a S) * (S.2 : ENNReal)
        = ∑' S : Config Q X n × ℕ,
            ∑' a : α, μ a * F a S * (S.2 : ENNReal) := by
          apply tsum_congr
          intro S
          rw [ENNReal.tsum_mul_right]
    _ = ∑' a : α,
          ∑' S : Config Q X n × ℕ, μ a * F a S * (S.2 : ENNReal) :=
          ENNReal.tsum_comm
    _ = ∑' a : α, μ a *
          ∑' S : Config Q X n × ℕ, F a S * (S.2 : ENNReal) := by
          apply tsum_congr
          intro a
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro S
          rw [mul_assoc]

private theorem eventCountMean_map
    (μ : PMF α) (f : α → Config Q X n × ℕ) :
    eventCountMean (μ.map f) =
      ∑' a : α, μ a * ((f a).2 : ENNReal) := by
  rw [← PMF.bind_pure_comp, eventCountMean_bind]
  apply tsum_congr
  intro a
  change μ a * eventCountMean (PMF.pure (f a)) = μ a * ↑(f a).2
  rw [eventCountMean_pure]

private theorem eventCountStepMean_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Event : Config Q X n → Fin n → Fin n → Bool)
    (eventProb : ENNReal)
    (hProb : ∀ C : Config Q X n, (uniformPair n hn).toOuterMeasure
      {p | Event C p.1 p.2 = true} ≤ eventProb)
    (S : Config Q X n × ℕ) :
    eventCountMean (eventCountStepDist P hn Event S) ≤
      (S.2 : ENNReal) + eventProb := by
  classical
  unfold eventCountStepDist
  rw [eventCountMean_map]
  have hmass :
      ∑' p : Fin n × Fin n,
          uniformPair n hn p *
            (if Event S.1 p.1 p.2 = true then (1 : ENNReal) else 0) =
        (uniformPair n hn).toOuterMeasure {p | Event S.1 p.1 p.2 = true} := by
    rw [PMF.toOuterMeasure_apply]
    apply tsum_congr
    intro p
    by_cases hp : Event S.1 p.1 p.2 = true
    · rw [if_pos hp]
      rw [Set.indicator_of_mem
        (s := {p : Fin n × Fin n | Event S.1 p.1 p.2 = true})
        (a := p) (f := uniformPair n hn) (by simpa using hp)]
      simp
    · rw [if_neg hp]
      rw [Set.indicator_of_notMem
        (s := {p : Fin n × Fin n | Event S.1 p.1 p.2 = true})
        (a := p) (f := uniformPair n hn) (by simpa using hp)]
      simp
  calc
    ∑' p : Fin n × Fin n,
        uniformPair n hn p *
          (((S.1.step P p.1 p.2,
            S.2 + if Event S.1 p.1 p.2 then 1 else 0) :
              Config Q X n × ℕ).2 : ENNReal)
        = ∑' p : Fin n × Fin n,
            uniformPair n hn p *
              ((S.2 : ENNReal) +
                if Event S.1 p.1 p.2 = true then (1 : ENNReal) else 0) := by
          apply tsum_congr
          intro p
          by_cases hp : Event S.1 p.1 p.2 = true <;> simp [hp]
    _ = ∑' p : Fin n × Fin n,
          (uniformPair n hn p * (S.2 : ENNReal) +
            uniformPair n hn p *
              (if Event S.1 p.1 p.2 = true then (1 : ENNReal) else 0)) := by
          apply tsum_congr
          intro p
          rw [mul_add]
    _ = (∑' p : Fin n × Fin n, uniformPair n hn p * (S.2 : ENNReal)) +
          (∑' p : Fin n × Fin n,
            uniformPair n hn p *
              (if Event S.1 p.1 p.2 = true then (1 : ENNReal) else 0)) := by
          rw [ENNReal.tsum_add]
    _ = (S.2 : ENNReal) +
          (uniformPair n hn).toOuterMeasure {p | Event S.1 p.1 p.2 = true} := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, hmass]
    _ ≤ (S.2 : ENNReal) + eventProb := add_le_add le_rfl (hProb S.1)

private theorem eventCountDist_mean_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Event : Config Q X n → Fin n → Fin n → Bool)
    (eventProb : ENNReal)
    (hProb : ∀ C : Config Q X n, (uniformPair n hn).toOuterMeasure
      {p | Event C p.1 p.2 = true} ≤ eventProb) :
    ∀ t : ℕ,
      eventCountMean (eventCountDist P hn C₀ Event t) ≤
        (t : ENNReal) * eventProb
  | 0 => by
      rw [eventCountDist, eventCountMean_pure]
      simp
  | t + 1 => by
      rw [eventCountDist, eventCountMean_bind]
      calc
        ∑' S : Config Q X n × ℕ,
            eventCountDist P hn C₀ Event t S *
              eventCountMean (eventCountStepDist P hn Event S)
            ≤ ∑' S : Config Q X n × ℕ,
                eventCountDist P hn C₀ Event t S *
                  ((S.2 : ENNReal) + eventProb) := by
              apply ENNReal.tsum_le_tsum
              intro S
              exact mul_le_mul_right
                (eventCountStepMean_le P hn Event eventProb hProb S) _
        _ = ∑' S : Config Q X n × ℕ,
              (eventCountDist P hn C₀ Event t S * (S.2 : ENNReal) +
                eventCountDist P hn C₀ Event t S * eventProb) := by
              apply tsum_congr
              intro S
              rw [mul_add]
        _ = eventCountMean (eventCountDist P hn C₀ Event t) +
              eventProb := by
              rw [ENNReal.tsum_add]
              unfold eventCountMean
              rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        _ ≤ (t : ENNReal) * eventProb + eventProb := by
              exact add_le_add
                (eventCountDist_mean_le P hn C₀ Event eventProb hProb t) le_rfl
        _ = ((t + 1 : ℕ) : ENNReal) * eventProb := by
              rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

theorem eventCountDist_marginal_config
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Event : Config Q X n → Fin n → Fin n → Bool)
    (t : ℕ) :
    (eventCountDist P hn C₀ Event t).map Prod.fst =
      nthStepDist P hn C₀ t := by
  induction t with
  | zero =>
      rw [eventCountDist, nthStepDist]
      simpa using
        (PMF.pure_map (f := Prod.fst) (a := (C₀, 0)))
  | succ t ih =>
      rw [eventCountDist, nthStepDist, PMF.map_bind]
      have hstep : ∀ S : Config Q X n × ℕ,
          (eventCountStepDist P hn Event S).map Prod.fst = stepDist P hn S.1 := by
        intro S
        unfold eventCountStepDist stepDist
        rw [PMF.map_comp]
        rfl
      simp only [hstep]
      change
        (eventCountDist P hn C₀ Event t).bind ((stepDist P hn) ∘ Prod.fst) =
          (nthStepDist P hn C₀ t).bind (stepDist P hn)
      rw [← PMF.bind_map, ih]

theorem eventCountDist_expected_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Event : Config Q X n → Fin n → Fin n → Bool)
    (eventProb : ENNReal) (K : ℕ) [NeZero K]
    (hProb : ∀ C : Config Q X n, (uniformPair n hn).toOuterMeasure
      {p | Event C p.1 p.2 = true} ≤ eventProb)
    (t : ℕ) :
    (eventCountDist P hn C₀ Event t).toOuterMeasure
      {S | (K : ℕ) ≤ S.2} ≤ (t : ENNReal) * eventProb / K := by
  classical
  let μ := eventCountDist P hn C₀ Event t
  have hK0 : ((K : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast (NeZero.ne K)
  have hKtop : ((K : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top K
  have hmarkov :
      μ.toOuterMeasure {S : Config Q X n × ℕ | K ≤ S.2} ≤
        eventCountMean μ / (K : ENNReal) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop)).2
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    unfold eventCountMean
    apply ENNReal.tsum_le_tsum
    intro S
    by_cases hS : K ≤ S.2
    · rw [Set.indicator_of_mem
        (s := {S : Config Q X n × ℕ | K ≤ S.2})
        (a := S) (f := μ) (by simpa using hS)]
      exact mul_le_mul_right (by exact_mod_cast hS) _
    · rw [Set.indicator_of_notMem
        (s := {S : Config Q X n × ℕ | K ≤ S.2})
        (a := S) (f := μ) (by simpa using hS)]
      simp
  refine hmarkov.trans ?_
  simpa [μ] using
    (ENNReal.div_le_div_right
      (eventCountDist_mean_le P hn C₀ Event eventProb hProb t) (K : ENNReal))

/-- `probNotHitFrom` agrees with the ordinary tail probability when the
arbitrary-start chain is initialized with the ordinary initial flag. -/
theorem probNotHitFrom_initial_eq_probNotHitBy
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) [DecidablePred Goal]
    (t : ℕ) :
    probNotHitFrom P hn Goal (C₀, decide (Goal C₀)) t =
      probNotHitBy P hn C₀ Goal t := by
  rw [probNotHitFrom_eq_toOuterMeasure, probNotHitBy_eq_hitFlagDist_toOuterMeasure,
    hitFlagDist_eq_hitFlagDistFrom]

/-- Tower decomposition of arbitrary-start non-hit tail mass across a
`t`-step prefix and a `k`-step suffix. -/
theorem probNotHitFrom_add_eq_tsum
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (S : Config Q X n × Bool) (t k : ℕ) :
    probNotHitFrom P hn Goal S (t + k) =
      ∑' T : Config Q X n × Bool,
        hitFlagDistFrom P hn Goal S t T *
          probNotHitFrom P hn Goal T k := by
  rw [probNotHitFrom_eq_toOuterMeasure, hitFlagDistFrom_add,
    PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro T
  rw [probNotHitFrom_eq_toOuterMeasure]

/-- A one-step transition from an already-hit flag never lands in a false
flag state. -/
theorem hitFlagStepDist_true_apply_false
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (C D : Config Q X n) :
    hitFlagStepDist P hn Goal (C, true) (D, false) = 0 := by
  classical
  unfold hitFlagStepDist
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.2
  intro C'
  by_cases hEq : (D, false) = (C', true || decide (Goal C'))
  · simp at hEq
  · simp

/-- Starting from an already-hit flag, every false-flag point has zero mass
at every later time. -/
theorem hitFlagDistFrom_true_apply_false
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (C D : Config Q X n) :
    ∀ t : ℕ, hitFlagDistFrom P hn Goal (C, true) t (D, false) = 0
  | 0 => by
      rw [hitFlagDistFrom]
      have hne : (D, false) ≠ (C, true) := by
        intro h
        have hb := congrArg Prod.snd h
        simp at hb
      exact PMF.pure_apply_of_ne (a := (C, true)) (a' := (D, false)) hne
  | t + 1 => by
      rw [hitFlagDistFrom, PMF.bind_apply]
      apply ENNReal.tsum_eq_zero.2
      intro S
      rcases S with ⟨E, b⟩
      cases b
      · rw [hitFlagDistFrom_true_apply_false P hn Goal C E t]
        simp
      · rw [hitFlagStepDist_true_apply_false P hn Goal E D]
        simp

/-- Starting a block with the hit flag already true gives zero non-hit mass. -/
theorem probNotHitFrom_true
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (C : Config Q X n) (t : ℕ) :
    probNotHitFrom P hn Goal (C, true) t = 0 := by
  rw [probNotHitFrom]
  apply ENNReal.tsum_eq_zero.2
  intro T
  rcases T with ⟨D, b⟩
  cases b
  · simp [hitFlagDistFrom_true_apply_false P hn Goal C D t]
  · simp

/-- If the hit flag is already true, it remains true after one lifted step. -/
theorem hitFlagStepDist_true_toOuterMeasure_false
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (C : Config Q X n) :
    (hitFlagStepDist P hn Goal (C, true)).toOuterMeasure
        {S : Config Q X n × Bool | S.2 = false} = 0 := by
  classical
  unfold hitFlagStepDist
  rw [PMF.toOuterMeasure_map_apply]
  simp

/-- If the hit flag is already true, it remains in the true-flag event after
one lifted step with probability one. -/
theorem hitFlagStepDist_true_toOuterMeasure_true
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (C : Config Q X n) :
    (hitFlagStepDist P hn Goal (C, true)).toOuterMeasure
        {S : Config Q X n × Bool | S.2 = true} = 1 := by
  classical
  unfold hitFlagStepDist
  rw [PMF.toOuterMeasure_map_apply]
  rw [show
      ((fun C' : Config Q X n => (C', true || decide (Goal C'))) ⁻¹'
          {S : Config Q X n × Bool | S.2 = true}) =
        Set.univ by
    ext C'
    simp]
  rw [PMF.toOuterMeasure_apply]
  simp [PMF.tsum_coe]

/-- From a false hit flag, the one-step false-flag mass is exactly the mass of
next configurations that still miss the goal. -/
theorem hitFlagStepDist_false_toOuterMeasure_false
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (C : Config Q X n) :
    (hitFlagStepDist P hn Goal (C, false)).toOuterMeasure
        {S : Config Q X n × Bool | S.2 = false} =
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} := by
  classical
  unfold hitFlagStepDist
  rw [PMF.toOuterMeasure_map_apply]
  congr 1
  ext C'
  by_cases h : Goal C'
  · simp [h]
  · simp [h]

/-- A lifted step cannot land with a false flag in a goal configuration. -/
theorem hitFlagStepDist_apply_false_of_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop)
    (S : Config Q X n × Bool) (C : Config Q X n)
    (hGoal : Goal C) :
    hitFlagStepDist P hn Goal S (C, false) = 0 := by
  classical
  unfold hitFlagStepDist
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.2
  intro C'
  by_cases hEq : (C, false) = (C', S.2 || decide (Goal C'))
  · have hC' : C' = C := by
      exact (congrArg Prod.fst hEq).symm
    subst C'
    simp [hGoal] at hEq
  · simp [hEq]

/-- In the hit-flag chain, a state with false flag and a goal configuration has
zero mass at every time. -/
theorem hitFlagDist_apply_false_of_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ C : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : Goal C) (t : ℕ) :
    hitFlagDist P hn C₀ Goal t (C, false) = 0 := by
  induction t with
  | zero =>
      classical
      rw [hitFlagDist]
      by_cases hC : C₀ = C
      · subst C₀
        simp [hGoal]
      · rw [PMF.pure_apply_of_ne]
        intro h
        exact hC (congrArg Prod.fst h).symm
  | succ t ih =>
      rw [hitFlagDist, PMF.bind_apply]
      apply ENNReal.tsum_eq_zero.2
      intro S
      rw [hitFlagStepDist_apply_false_of_goal P hn Goal S C hGoal]
      simp

/-- Being in `Goal` at the final time is contained in the finite-prefix hit
event. -/
theorem probReached_le_ProbHitWithin
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (t : ℕ) :
    probReached P hn C₀ Goal t ≤
      ProbHitWithin P hn C₀ Goal t := by
  classical
  rw [probReached_eq_toOuterMeasure]
  rw [← hitFlagDist_map_fst P hn C₀ Goal t]
  rw [PMF.toOuterMeasure_map_apply]
  change (hitFlagDist P hn C₀ Goal t).toOuterMeasure
      (Prod.fst ⁻¹' {C | Goal C}) ≤
    probHitBy P hn C₀ Goal t
  rw [probHitBy_eq_hitFlagDist_toOuterMeasure]
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro S
  rcases S with ⟨C, b⟩
  by_cases hGoalC : Goal C
  · cases b
    · rw [Set.indicator_of_mem
        (s := Prod.fst ⁻¹' {C : Config Q X n | Goal C})
        (a := (C, false)) (f := hitFlagDist P hn C₀ Goal t)
        (by simpa using hGoalC)]
      rw [Set.indicator_of_notMem
        (s := {S : Config Q X n × Bool | S.2 = true})
        (a := (C, false)) (f := hitFlagDist P hn C₀ Goal t)
        (by simp)]
      rw [hitFlagDist_apply_false_of_goal P hn C₀ C Goal hGoalC t]
    · rw [Set.indicator_of_mem
        (s := Prod.fst ⁻¹' {C : Config Q X n | Goal C})
        (a := (C, true)) (f := hitFlagDist P hn C₀ Goal t)
        (by simpa using hGoalC)]
      rw [Set.indicator_of_mem
        (s := {S : Config Q X n × Bool | S.2 = true})
        (a := (C, true)) (f := hitFlagDist P hn C₀ Goal t)
        (by simp)]
  · rw [Set.indicator_of_notMem
      (s := Prod.fst ⁻¹' {C : Config Q X n | Goal C})
      (a := (C, b)) (f := hitFlagDist P hn C₀ Goal t)
      (by simpa using hGoalC)]
    simp

/-- Exact-time phase composition, delivered as a finite-prefix hit bound for
the final phase. -/
theorem probReached_add_ge_mul_to_ProbHitWithin
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Mid Target : Config Q X n → Prop)
    [DecidablePred Mid] [DecidablePred Target]
    (t k : ℕ) (p q : ENNReal)
    (hMid : p ≤ probReached P hn C₀ Mid t)
    (hTarget : ∀ C : Config Q X n, Mid C →
      q ≤ probReached P hn C Target k) :
    p * q ≤ ProbHitWithin P hn C₀ Target (t + k) := by
  exact (probReached_add_ge_mul P hn C₀ Mid Target t k p q hMid hTarget).trans
    (probReached_le_ProbHitWithin P hn C₀ Target (t + k))

/-- Three-phase exact-time composition, delivered as a finite-prefix hit
bound for the final phase. -/
theorem probReached_add_add_ge_mul3_to_ProbHitWithin
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B C : Config Q X n → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    (tA tB tC : ℕ) (pA pB pC : ENNReal)
    (hA : pA ≤ probReached P hn C₀ A tA)
    (hAB : ∀ D : Config Q X n, A D →
      pB ≤ probReached P hn D B tB)
    (hBC : ∀ D : Config Q X n, B D →
      pC ≤ probReached P hn D C tC) :
    pA * pB * pC ≤
      ProbHitWithin P hn C₀ C ((tA + tB) + tC) := by
  exact (probReached_add_add_ge_mul3 P hn C₀ A B C
    tA tB tC pA pB pC hA hAB hBC).trans
    (probReached_le_ProbHitWithin P hn C₀ C ((tA + tB) + tC))

/-- Four-phase exact-time composition, delivered as a finite-prefix hit
bound for the final phase. -/
theorem probReached_add_add_add_ge_mul4_to_ProbHitWithin
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B C D : Config Q X n → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C] [DecidablePred D]
    (tA tB tC tD : ℕ) (pA pB pC pD : ENNReal)
    (hA : pA ≤ probReached P hn C₀ A tA)
    (hAB : ∀ E : Config Q X n, A E →
      pB ≤ probReached P hn E B tB)
    (hBC : ∀ E : Config Q X n, B E →
      pC ≤ probReached P hn E C tC)
    (hCD : ∀ E : Config Q X n, C E →
      pD ≤ probReached P hn E D tD) :
    pA * pB * pC * pD ≤
      ProbHitWithin P hn C₀ D (((tA + tB) + tC) + tD) := by
  exact (probReached_add_add_add_ge_mul4 P hn C₀ A B C D
    tA tB tC tD pA pB pC pD hA hAB hBC hCD).trans
    (probReached_le_ProbHitWithin P hn C₀ D (((tA + tB) + tC) + tD))

/-- Five-phase exact-time composition, delivered as a finite-prefix hit
bound for the final phase.  This is the direct Table-2 composition interface:
no phase independence is assumed. -/
theorem probReached_add_add_add_add_ge_mul5_to_ProbHitWithin
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B C D E : Config Q X n → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    [DecidablePred D] [DecidablePred E]
    (tA tB tC tD tE : ℕ) (pA pB pC pD pE : ENNReal)
    (hA : pA ≤ probReached P hn C₀ A tA)
    (hAB : ∀ F : Config Q X n, A F →
      pB ≤ probReached P hn F B tB)
    (hBC : ∀ F : Config Q X n, B F →
      pC ≤ probReached P hn F C tC)
    (hCD : ∀ F : Config Q X n, C F →
      pD ≤ probReached P hn F D tD)
    (hDE : ∀ F : Config Q X n, D F →
      pE ≤ probReached P hn F E tE) :
    pA * pB * pC * pD * pE ≤
      ProbHitWithin P hn C₀ E ((((tA + tB) + tC) + tD) + tE) := by
  exact (probReached_add_add_add_add_ge_mul5 P hn C₀ A B C D E
    tA tB tC tD tE pA pB pC pD pE hA hAB hBC hCD hDE).trans
    (probReached_le_ProbHitWithin P hn C₀ E
      ((((tA + tB) + tC) + tD) + tE))

/-- One-step tower decomposition for the non-hit tail probability. -/
theorem probNotHitBy_succ_eq_tsum
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    probNotHitBy P hn C₀ Goal (t + 1) =
      ∑' S : Config Q X n × Bool,
        (hitFlagDist P hn C₀ Goal t S) *
          (hitFlagStepDist P hn Goal S).toOuterMeasure
            {T : Config Q X n × Bool | T.2 = false} := by
  rw [probNotHitBy_eq_hitFlagDist_toOuterMeasure]
  simp only [hitFlagDist]
  rw [PMF.toOuterMeasure_bind_apply]

/-- Any `PMF` gives outer measure at most one to every set. -/
theorem PMF.toOuterMeasure_le_one {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply]
  calc
    (∑' a : α, s.indicator (fun x => p x) a) ≤ ∑' a : α, p a := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : a ∈ s <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha]
    _ = 1 := PMF.tsum_coe p

/-- The non-hit tail probability is monotone decreasing in time. -/
theorem probNotHitBy_succ_le_self
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    probNotHitBy P hn C₀ Goal (t + 1) ≤
      probNotHitBy P hn C₀ Goal t := by
  classical
  rw [probNotHitBy_succ_eq_tsum]
  rw [probNotHitBy]
  calc
    (∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (hitFlagStepDist P hn Goal S).toOuterMeasure
            {T : Config Q X n × Bool | T.2 = false})
        ≤ ∑' S : Config Q X n × Bool,
          hitFlagDist P hn C₀ Goal t S *
            (if S.2 = false then 1 else 0) := by
          apply ENNReal.tsum_le_tsum
          intro S
          by_cases hS : S.2 = false
          · have hle :
                (hitFlagStepDist P hn Goal S).toOuterMeasure
                    {T : Config Q X n × Bool | T.2 = false} ≤ 1 :=
              PMF.toOuterMeasure_le_one _ _
            have hmul := mul_le_mul_right hle (hitFlagDist P hn C₀ Goal t S)
            simpa [hS, mul_comm, mul_left_comm, mul_assoc] using hmul
          · cases S with
            | mk C b =>
                cases b
                · exact False.elim (hS rfl)
                · rw [hitFlagStepDist_true_toOuterMeasure_false]
                  simp
    _ = ∑' S : Config Q X n × Bool,
          if S.2 = false then hitFlagDist P hn C₀ Goal t S else 0 := by
          apply tsum_congr
          intro S
          by_cases hS : S.2 = false <;> simp [hS]

/-- Monotone form of `probNotHitBy_succ_le_self`. -/
theorem probNotHitBy_le_of_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    {m t : ℕ} (hmt : m ≤ t) :
    probNotHitBy P hn C₀ Goal t ≤
      probNotHitBy P hn C₀ Goal m := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmt
  subst t
  clear hmt
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        probNotHitBy P hn C₀ Goal (m + (k + 1))
            = probNotHitBy P hn C₀ Goal ((m + k) + 1) := by
              rw [Nat.add_assoc]
        _ ≤ probNotHitBy P hn C₀ Goal (m + k) :=
              probNotHitBy_succ_le_self P hn C₀ Goal (m + k)
        _ ≤ probNotHitBy P hn C₀ Goal m := ih

/-- One-step tower decomposition for finite-prefix hit probability. -/
theorem probHitBy_succ_eq_tsum
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    probHitBy P hn C₀ Goal (t + 1) =
      ∑' S : Config Q X n × Bool,
        (hitFlagDist P hn C₀ Goal t S) *
          (hitFlagStepDist P hn Goal S).toOuterMeasure
            {T : Config Q X n × Bool | T.2 = true} := by
  rw [probHitBy_eq_hitFlagDist_toOuterMeasure]
  simp only [hitFlagDist]
  rw [PMF.toOuterMeasure_bind_apply]

/-- Finite-window hit probability is monotone in the window length. -/
theorem ProbHitWithin_le_succ
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    ProbHitWithin P hn C₀ Goal t ≤
      ProbHitWithin P hn C₀ Goal (t + 1) := by
  classical
  rw [ProbHitWithin, ProbHitWithin, probHitBy_succ_eq_tsum]
  rw [probHitBy]
  calc
    (∑' S : Config Q X n × Bool,
        if S.2 = true then hitFlagDist P hn C₀ Goal t S else 0)
        ≤
      ∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (hitFlagStepDist P hn Goal S).toOuterMeasure
            {T : Config Q X n × Bool | T.2 = true} := by
        apply ENNReal.tsum_le_tsum
        intro S
        by_cases hS : S.2 = true
        · cases S with
          | mk C b =>
              cases b
              · exact False.elim (by simp at hS)
              · simp [hitFlagStepDist_true_toOuterMeasure_true]
        · simp [hS]

/-- One-step hit lower bounds extend to any nonzero finite window. -/
theorem ProbHitWithin_one_le_of_pos
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    {t : ℕ} (ht : 1 ≤ t) :
    ProbHitWithin P hn C₀ Goal 1 ≤
      ProbHitWithin P hn C₀ Goal t := by
  rcases Nat.exists_eq_add_of_le ht with ⟨k, hk⟩
  subst t
  clear ht
  induction k with
  | zero => rfl
  | succ k ih =>
      exact ih.trans (by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          ProbHitWithin_le_succ P hn C₀ Goal (1 + k))

/-- A one-step success lower bound is also a lower bound for any nonzero
finite window. -/
theorem ProbHitWithin_lower_bound_of_one_lower_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    {p : ENNReal} {t : ℕ} (ht : 1 ≤ t)
    (hp : p ≤ ProbHitWithin P hn C₀ Goal 1) :
    p ≤ ProbHitWithin P hn C₀ Goal t :=
  hp.trans (ProbHitWithin_one_le_of_pos P hn C₀ Goal ht)

/-- The finite-prefix hit probability is the complement of the corresponding
non-hit tail probability. -/
theorem ProbHitWithin_eq_one_sub_probNotHitBy
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    ProbHitWithin P hn C₀ Goal t =
      1 - probNotHitBy P hn C₀ Goal t := by
  have hsum := probHitBy_add_probNotHitBy P hn C₀ Goal t
  have h : (1 : ENNReal) =
      probNotHitBy P hn C₀ Goal t + probHitBy P hn C₀ Goal t := by
    rw [add_comm, hsum]
  rw [ProbHitWithin]
  exact (ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top h).symm

/-- `ProbHitWithin` is non-decreasing in the time horizon. -/
theorem ProbHitWithin_mono_time
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    {m t : ℕ} (hmt : m ≤ t) :
    ProbHitWithin P hn C₀ Goal m ≤ ProbHitWithin P hn C₀ Goal t := by
  simp only [ProbHitWithin_eq_one_sub_probNotHitBy]
  exact tsub_le_tsub_left (probNotHitBy_le_of_le P hn C₀ Goal hmt) 1

/-- Finite-prefix hit probabilities are bounded by `1`. -/
theorem ProbHitWithin_le_one
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) (t : ℕ) :
    ProbHitWithin P hn C₀ Goal t ≤ 1 := by
  rw [ProbHitWithin]
  calc
    probHitBy P hn C₀ Goal t
        ≤ probHitBy P hn C₀ Goal t + probNotHitBy P hn C₀ Goal t := by
          exact le_self_add
    _ = 1 := probHitBy_add_probNotHitBy P hn C₀ Goal t

/-- Finite-prefix union bound for hitting probabilities. -/
theorem ProbHitWithin_or_le_add
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B : Config Q X n → Prop) (t : ℕ) :
    ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t ≤
      ProbHitWithin P hn C₀ A t + ProbHitWithin P hn C₀ B t := by
  classical
  rw [ProbHitWithin, probHitBy_eq_hitFlagDist_toOuterMeasure]
  rw [← hitTwoFlagDist_map_or P hn C₀ A B t, PMF.toOuterMeasure_map_apply]
  rw [show ProbHitWithin P hn C₀ A t =
      (hitTwoFlagDist P hn C₀ A B t).toOuterMeasure
        ((fun S : Config Q X n × (Bool × Bool) => (S.1, S.2.1)) ⁻¹'
          {S : Config Q X n × Bool | S.2 = true}) by
        rw [ProbHitWithin, probHitBy_eq_hitFlagDist_toOuterMeasure,
          ← hitTwoFlagDist_map_left P hn C₀ A B t, PMF.toOuterMeasure_map_apply]]
  rw [show ProbHitWithin P hn C₀ B t =
      (hitTwoFlagDist P hn C₀ A B t).toOuterMeasure
        ((fun S : Config Q X n × (Bool × Bool) => (S.1, S.2.2)) ⁻¹'
          {S : Config Q X n × Bool | S.2 = true}) by
        rw [ProbHitWithin, probHitBy_eq_hitFlagDist_toOuterMeasure,
          ← hitTwoFlagDist_map_right P hn C₀ A B t, PMF.toOuterMeasure_map_apply]]
  repeat rw [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro S
  rcases S with ⟨C, bA, bB⟩
  cases bA <;> cases bB <;> simp

/-- Subtraction form of the finite-prefix union bound used in phase proofs:
if `A ∨ B` has probability at least `1/2 + 1/8` and `B` has probability at
most `1/2`, then `A` has probability at least `1/8`. -/
theorem ProbHitWithin_left_ge_inv8_of_or_ge_half_add_inv8_and_right_le_half
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B : Config Q X n → Prop) (t : ℕ)
    (hor :
      (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹ ≤
        ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t)
    (hB : ProbHitWithin P hn C₀ B t ≤ (2 : ENNReal)⁻¹) :
    (8 : ENNReal)⁻¹ ≤ ProbHitWithin P hn C₀ A t := by
  let x := ProbHitWithin P hn C₀ A t
  let y := ProbHitWithin P hn C₀ B t
  have hOr :
      ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t ≤ x + y := by
    simpa [x, y] using ProbHitWithin_or_le_add P hn C₀ A B t
  have h58 : (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹ ≤ x + (2 : ENNReal)⁻¹ := by
    calc
      (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹
          ≤ ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t := hor
      _ ≤ x + y := hOr
      _ ≤ x + (2 : ENNReal)⁻¹ := by
        have hy : y ≤ (2 : ENNReal)⁻¹ := by
          dsimp [y]
          exact hB
        simpa [add_comm] using add_le_add_left hy x
  have hhalf_ne_top : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  rw [add_comm x ((2 : ENNReal)⁻¹)] at h58
  exact (ENNReal.add_le_add_iff_left hhalf_ne_top).mp h58

/-- A tail upper bound immediately gives a finite-window hit lower bound. -/
theorem ProbHitWithin_ge_one_sub_of_probNotHitBy_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) {b : ENNReal}
    (hb : probNotHitBy P hn C₀ Goal t ≤ b) :
    1 - b ≤ ProbHitWithin P hn C₀ Goal t := by
  rw [ProbHitWithin_eq_one_sub_probNotHitBy]
  exact tsub_le_tsub_left hb 1

/-- A finite-window hit lower bound gives the complementary non-hit upper
bound for the same window. -/
theorem probNotHitBy_le_one_sub_of_ProbHitWithin_lower_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) (p : ENNReal)
    (hp : p ≤ ProbHitWithin P hn C₀ Goal t) :
    probNotHitBy P hn C₀ Goal t ≤ 1 - p := by
  have hsum := probHitBy_add_probNotHitBy P hn C₀ Goal t
  have hhit_le_one : ProbHitWithin P hn C₀ Goal t ≤ 1 := by
    calc
      ProbHitWithin P hn C₀ Goal t
          ≤ ProbHitWithin P hn C₀ Goal t +
            probNotHitBy P hn C₀ Goal t := by
              exact le_self_add
      _ = 1 := hsum
  have hp_ne_top : p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hp.trans hhit_le_one)
  exact ENNReal.le_sub_of_add_le_left hp_ne_top (by
    calc
      p + probNotHitBy P hn C₀ Goal t
          ≤ ProbHitWithin P hn C₀ Goal t +
            probNotHitBy P hn C₀ Goal t := by
              exact add_le_add_left hp _
      _ = 1 := hsum)

/-- If a non-goal configuration has a `p` lower bound for hitting within a
`K`-step block, then an arbitrary-start false flag at that configuration has
non-hit mass at most `1 - p` after the block. -/
theorem probNotHitFrom_false_le_one_sub_of_ProbHitWithin_lower_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) (p : ENNReal)
    (hGoal : ¬ Goal C)
    (hp : p ≤ ProbHitWithin P hn C Goal K) :
    probNotHitFrom P hn Goal (C, false) K ≤ 1 - p := by
  classical
  rw [probNotHitFrom_eq_toOuterMeasure]
  rw [hitFlagDistFrom_false_eq_hitFlagDist P hn C Goal hGoal K]
  rw [← probNotHitBy_eq_hitFlagDist_toOuterMeasure]
  exact probNotHitBy_le_one_sub_of_ProbHitWithin_lower_bound
    P hn C Goal K p hp

/-- A uniform `K`-step hit lower bound contracts the non-hit tail by
`1 - p` across one more `K`-step window. -/
theorem probNotHitBy_add_window_le_mul
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K t : ℕ) (p : ENNReal)
    (hwin : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    probNotHitBy P hn C₀ Goal (t + K) ≤
      probNotHitBy P hn C₀ Goal t * (1 - p) := by
  classical
  rw [← probNotHitFrom_initial_eq_probNotHitBy P hn C₀ Goal (t + K)]
  rw [probNotHitFrom_add_eq_tsum]
  calc
    (∑' T : Config Q X n × Bool,
        hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t T *
          probNotHitFrom P hn Goal T K)
        ≤
      ∑' T : Config Q X n × Bool,
        hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t T *
          (if T.2 = false then 1 - p else 0) := by
        apply ENNReal.tsum_le_tsum
        intro T
        rcases T with ⟨C, b⟩
        cases b
        · by_cases hGoalC : Goal C
          · have hzero :
                hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t
                  (C, false) = 0 := by
              rw [← hitFlagDist_eq_hitFlagDistFrom]
              exact hitFlagDist_apply_false_of_goal P hn C₀ C Goal hGoalC t
            rw [hzero]
            simp
          · have hblock :
                probNotHitFrom P hn Goal (C, false) K ≤ 1 - p :=
              probNotHitFrom_false_le_one_sub_of_ProbHitWithin_lower_bound
                P hn C Goal K p hGoalC (hwin C hGoalC)
            have hmul := mul_le_mul_right hblock
              (hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t (C, false))
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        · rw [probNotHitFrom_true]
          simp
    _ =
      (∑' T : Config Q X n × Bool,
        (if T.2 = false then
          hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t T
        else 0)) * (1 - p) := by
        rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro T
        by_cases hT : T.2 = false <;> simp [hT, mul_comm]
    _ = probNotHitBy P hn C₀ Goal t * (1 - p) := by
        rw [← probNotHitFrom_initial_eq_probNotHitBy P hn C₀ Goal t]
        rw [probNotHitFrom]

/-- Repeating a uniform `K`-step success window gives a geometric tail bound
at window endpoints. -/
theorem probNotHitBy_mul_window_le_initial_mul_pow
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) (p : ENNReal)
    (hwin : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    ∀ r : ℕ,
      probNotHitBy P hn C₀ Goal (r * K) ≤
        probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ r
  | 0 => by simp
  | r + 1 => by
      have hstep :=
        probNotHitBy_add_window_le_mul P hn C₀ Goal K (r * K) p hwin
      have ih :=
        probNotHitBy_mul_window_le_initial_mul_pow
          P hn C₀ Goal K p hwin r
      calc
        probNotHitBy P hn C₀ Goal ((r + 1) * K)
            = probNotHitBy P hn C₀ Goal (r * K + K) := by
              rw [Nat.succ_mul]
        _ ≤ probNotHitBy P hn C₀ Goal (r * K) * (1 - p) := hstep
        _ ≤ (probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ r) * (1 - p) := by
              exact mul_le_mul_left ih _
        _ = probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ (r + 1) := by
              rw [pow_succ, mul_assoc]

/-- Repeated-window high-probability form with the initial tail left
explicit. -/
theorem ProbHitWithin_mul_window_ge_one_sub_initial_mul_pow
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) (p : ENNReal)
    (hwin : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    ∀ r : ℕ,
      1 - probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ r ≤
        ProbHitWithin P hn C₀ Goal (r * K) := by
  intro r
  exact ProbHitWithin_ge_one_sub_of_probNotHitBy_le P hn C₀ Goal (r * K)
    (probNotHitBy_mul_window_le_initial_mul_pow P hn C₀ Goal K p hwin r)

/-- If every one-step transition from a not-yet-hit configuration misses the
goal with probability at most `q`, then the non-hit tail contracts by `q` in
one more step. -/
theorem probNotHitBy_succ_le_mul
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hmiss : ∀ C : Config Q X n,
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q)
    (t : ℕ) :
    probNotHitBy P hn C₀ Goal (t + 1) ≤
      probNotHitBy P hn C₀ Goal t * q := by
  classical
  rw [probNotHitBy_succ_eq_tsum]
  calc
    (∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (hitFlagStepDist P hn Goal S).toOuterMeasure
            {T : Config Q X n × Bool | T.2 = false})
        ≤
      ∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (if S.2 = false then q else 0) := by
        apply ENNReal.tsum_le_tsum
        intro S
        by_cases hS : S.2 = false
        · cases S with
          | mk C b =>
              cases b
              · have hmul :=
                  mul_le_mul_right (hmiss C)
                    (hitFlagDist P hn C₀ Goal t (C, false))
                simpa [hitFlagStepDist_false_toOuterMeasure_false,
                  mul_comm, mul_left_comm, mul_assoc] using hmul
              · exact False.elim (by simp at hS)
        · cases S with
          | mk C b =>
              cases b
              · exact False.elim (hS rfl)
              · simp [hitFlagStepDist_true_toOuterMeasure_false]
    _ = (∑' S : Config Q X n × Bool,
        (if S.2 = false then hitFlagDist P hn C₀ Goal t S else 0)) * q := by
        rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro S
        by_cases hS : S.2 = false <;> simp [hS, mul_comm]
    _ = probNotHitBy P hn C₀ Goal t * q := by
        rw [probNotHitBy]

/-- Version of `probNotHitBy_succ_le_mul` with the natural hypothesis:
only non-goal configurations need a one-step miss bound. -/
theorem probNotHitBy_succ_le_mul_of_not_goal_miss
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hmiss : ∀ C : Config Q X n, ¬ Goal C →
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q)
    (t : ℕ) :
    probNotHitBy P hn C₀ Goal (t + 1) ≤
      probNotHitBy P hn C₀ Goal t * q := by
  classical
  rw [probNotHitBy_succ_eq_tsum]
  calc
    (∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (hitFlagStepDist P hn Goal S).toOuterMeasure
            {T : Config Q X n × Bool | T.2 = false})
        ≤
      ∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (if S.2 = false then q else 0) := by
        apply ENNReal.tsum_le_tsum
        intro S
        by_cases hS : S.2 = false
        · cases S with
          | mk C b =>
              cases b
              · by_cases hGoalC : Goal C
                · rw [hitFlagDist_apply_false_of_goal P hn C₀ C Goal hGoalC t]
                  simp
                · have hmul :=
                    mul_le_mul_right (hmiss C hGoalC)
                      (hitFlagDist P hn C₀ Goal t (C, false))
                  simpa [hitFlagStepDist_false_toOuterMeasure_false,
                    mul_comm, mul_left_comm, mul_assoc] using hmul
              · exact False.elim (by simp at hS)
        · cases S with
          | mk C b =>
              cases b
              · exact False.elim (hS rfl)
              · simp [hitFlagStepDist_true_toOuterMeasure_false]
    _ = (∑' S : Config Q X n × Bool,
        (if S.2 = false then hitFlagDist P hn C₀ Goal t S else 0)) * q := by
        rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro S
        by_cases hS : S.2 = false <;> simp [hS, mul_comm]
    _ = probNotHitBy P hn C₀ Goal t * q := by
        rw [probNotHitBy]

/-- Iterating the one-step miss bound gives a geometric tail bound. -/
theorem probNotHitBy_le_initial_mul_pow_of_not_goal_miss
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hmiss : ∀ C : Config Q X n, ¬ Goal C →
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q) :
    ∀ t : ℕ,
      probNotHitBy P hn C₀ Goal t ≤
        probNotHitBy P hn C₀ Goal 0 * q ^ t
  | 0 => by simp
  | t + 1 => by
      have hstep :=
        probNotHitBy_succ_le_mul_of_not_goal_miss
          P hn C₀ Goal q hmiss t
      have ih :=
        probNotHitBy_le_initial_mul_pow_of_not_goal_miss
          P hn C₀ Goal q hmiss t
      calc
        probNotHitBy P hn C₀ Goal (t + 1)
            ≤ probNotHitBy P hn C₀ Goal t * q := hstep
        _ ≤ (probNotHitBy P hn C₀ Goal 0 * q ^ t) * q := by
            exact mul_le_mul_left ih q
        _ = probNotHitBy P hn C₀ Goal 0 * q ^ (t + 1) := by
            rw [pow_succ, mul_assoc]

/-- Geometric miss bounds give the corresponding high-probability lower bound
for hitting within `t` steps. -/
theorem ProbHitWithin_ge_one_sub_initial_mul_pow_of_not_goal_miss
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hmiss : ∀ C : Config Q X n, ¬ Goal C →
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q) :
    ∀ t : ℕ,
      1 - probNotHitBy P hn C₀ Goal 0 * q ^ t ≤
        ProbHitWithin P hn C₀ Goal t := by
  intro t
  exact ProbHitWithin_ge_one_sub_of_probNotHitBy_le P hn C₀ Goal t
    (probNotHitBy_le_initial_mul_pow_of_not_goal_miss
      P hn C₀ Goal q hmiss t)

/-- A one-step window from a non-goal state has exactly the scheduler mass of
the ordered pairs whose interaction lands in the goal. -/
theorem ProbHitWithin_one_eq_pairSetMass_filter
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : ¬ Goal C₀) :
    ProbHitWithin P hn C₀ Goal 1 =
      pairSetMass n hn
        ((OffDiagonalPairs n).filter fun p => Goal (C₀.step P p.1 p.2)) := by
  rw [ProbHitWithin, probHitBy_eq_hitFlagDist_toOuterMeasure]
  have hdist :
      hitFlagDist P hn C₀ Goal 1 =
        (uniformPair n hn).map
          (fun p : Fin n × Fin n =>
            (C₀.step P p.1 p.2,
              @decide (Goal (C₀.step P p.1 p.2))
                (Classical.propDecidable _))) := by
    simp only [hitFlagDist, hGoal, decide_false]
    unfold hitFlagStepDist stepDist
    simp [PMF.map_comp, Function.comp_def]
  rw [hdist, PMF.toOuterMeasure_map_apply]
  rw [show
      ((fun p : Fin n × Fin n =>
        (C₀.step P p.1 p.2,
          @decide (Goal (C₀.step P p.1 p.2))
            (Classical.propDecidable _))) ⁻¹'
          {S : Config Q X n × Bool | S.2 = true}) =
        {p : Fin n × Fin n | Goal (C₀.step P p.1 p.2)} by
    ext p
    simp]
  exact (pairSetMass_filter_offDiagonal_eq_toOuterMeasure n hn
    (fun p : Fin n × Fin n => Goal (C₀.step P p.1 p.2))).symm

/-- One-step marginal reachability is exactly the scheduler mass of ordered
pairs whose interaction lands in the target set. -/
theorem probReached_one_eq_pairSetMass_filter
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] :
    probReached P hn C₀ Goal 1 =
      pairSetMass n hn
        ((OffDiagonalPairs n).filter fun p => Goal (C₀.step P p.1 p.2)) := by
  rw [probReached_eq_toOuterMeasure]
  have hdist :
      nthStepDist P hn C₀ 1 =
        (uniformPair n hn).map (fun p : Fin n × Fin n =>
          C₀.step P p.1 p.2) := by
    simp [nthStepDist, stepDist]
  rw [hdist, PMF.toOuterMeasure_map_apply]
  exact (pairSetMass_filter_offDiagonal_eq_toOuterMeasure n hn
    (fun p : Fin n × Fin n => Goal (C₀.step P p.1 p.2))).symm

/-- A whole set of one-step witnesses gives its scheduler mass as a lower
bound for one-step marginal reachability. -/
theorem probReached_one_lower_bound_of_pairSet
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal]
    (S : Finset (Fin n × Fin n))
    (hS : S ⊆ OffDiagonalPairs n)
    (hstep : ∀ p ∈ S, Goal (C₀.step P p.1 p.2)) :
    pairSetMass n hn S ≤ probReached P hn C₀ Goal 1 := by
  classical
  rw [probReached_one_eq_pairSetMass_filter P hn C₀ Goal]
  apply pairSetMass_mono
  intro p hp
  rw [Finset.mem_filter]
  exact ⟨hS hp, hstep p hp⟩

/-- A concrete one-step witness gives one ordered pair's scheduler mass as a
lower bound for one-step marginal reachability. -/
theorem probReached_one_lower_bound_of_step
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal]
    {i j : Fin n} (hij : i ≠ j)
    (hstep : Goal (C₀.step P i j)) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      probReached P hn C₀ Goal 1 := by
  classical
  rw [probReached_one_eq_pairSetMass_filter P hn C₀ Goal]
  unfold pairSetMass
  have hmem :
      (i, j) ∈ (OffDiagonalPairs n).filter
        (fun p : Fin n × Fin n => Goal (C₀.step P p.1 p.2)) := by
    rw [Finset.mem_filter]
    exact ⟨(mem_offDiagonalPairs n (i, j)).mpr hij, hstep⟩
  calc
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ = uniformPair n hn (i, j) := by
      rw [uniformPair_apply_of_ne n hn hij]
    _ ≤ ((OffDiagonalPairs n).filter
          (fun p : Fin n × Fin n => Goal (C₀.step P p.1 p.2))).sum
          (fun p => uniformPair n hn p) := by
        exact Finset.single_le_sum (fun p _ => zero_le) hmem

/-- From a non-target initial state, one-step finite-prefix hitting and
one-step marginal reachability are the same event. -/
theorem ProbHitWithin_one_eq_probReached_one_of_not_goal
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : ¬ Goal C₀) :
    ProbHitWithin P hn C₀ Goal 1 =
      probReached P hn C₀ Goal 1 := by
  rw [ProbHitWithin_one_eq_pairSetMass_filter P hn C₀ Goal hGoal,
    probReached_one_eq_pairSetMass_filter P hn C₀ Goal]

/-- A one-step hit-probability lower bound from a non-target state can be
used as a one-step marginal-reachability lower bound. -/
theorem probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] {p : ENNReal}
    (hGoal : ¬ Goal C₀)
    (hp : p ≤ ProbHitWithin P hn C₀ Goal 1) :
    p ≤ probReached P hn C₀ Goal 1 := by
  rwa [ProbHitWithin_one_eq_probReached_one_of_not_goal P hn C₀ Goal hGoal] at hp

/-- In a one-step window, enlarging the target predicate can only increase
the hitting probability. -/
theorem ProbHitWithin_one_mono_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Goal₁ Goal₂ : Config Q X n → Prop)
    (hGoal₁ : ¬ Goal₁ C₀) (hGoal₂ : ¬ Goal₂ C₀)
    (hmono : ∀ D : Config Q X n, Goal₁ D → Goal₂ D) :
    ProbHitWithin P hn C₀ Goal₁ 1 ≤
      ProbHitWithin P hn C₀ Goal₂ 1 := by
  classical
  rw [ProbHitWithin_one_eq_pairSetMass_filter P hn C₀ Goal₁ hGoal₁,
    ProbHitWithin_one_eq_pairSetMass_filter P hn C₀ Goal₂ hGoal₂]
  apply pairSetMass_mono
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hmono (C₀.step P p.1 p.2) hp.2⟩

/-- In a one-step window from a non-goal state, the non-hit probability is the
one-step transition mass of configurations that still miss the goal. -/
theorem probNotHitBy_one_eq_stepDist_toOuterMeasure_not_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀) :
    probNotHitBy P hn C₀ Goal 1 =
      (stepDist P hn C₀).toOuterMeasure {D | ¬ Goal D} := by
  classical
  rw [probNotHitBy_eq_hitFlagDist_toOuterMeasure]
  have hdist :
      hitFlagDist P hn C₀ Goal 1 =
        (uniformPair n hn).map
          (fun p : Fin n × Fin n =>
            (C₀.step P p.1 p.2,
              @decide (Goal (C₀.step P p.1 p.2))
                (Classical.propDecidable _))) := by
    simp only [hitFlagDist, hGoal, decide_false]
    unfold hitFlagStepDist stepDist
    simp [PMF.map_comp, Function.comp_def]
  rw [hdist, PMF.toOuterMeasure_map_apply]
  rw [show
      ((fun p : Fin n × Fin n =>
        (C₀.step P p.1 p.2,
          @decide (Goal (C₀.step P p.1 p.2))
            (Classical.propDecidable _))) ⁻¹'
          {S : Config Q X n × Bool | S.2 = false}) =
        {p : Fin n × Fin n | ¬ Goal (C₀.step P p.1 p.2)} by
    ext p
    by_cases h : Goal (C₀.step P p.1 p.2) <;> simp [h]]
  rw [stepDist, PMF.toOuterMeasure_map_apply]
  rfl

/-- The one-step hit event and one-step miss event partition probability mass
when starting outside the goal. -/
theorem ProbHitWithin_one_add_step_miss_eq_one
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀) :
    ProbHitWithin P hn C₀ Goal 1 +
      (stepDist P hn C₀).toOuterMeasure {D | ¬ Goal D} = 1 := by
  rw [← probNotHitBy_one_eq_stepDist_toOuterMeasure_not_goal
    P hn C₀ Goal hGoal]
  exact probHitBy_add_probNotHitBy P hn C₀ Goal 1

/-- A one-step success lower bound gives the corresponding one-step miss upper
bound. -/
theorem step_miss_le_one_sub_of_ProbHitWithin_one_lower_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (p : ENNReal) (hGoal : ¬ Goal C₀)
    (hp : p ≤ ProbHitWithin P hn C₀ Goal 1) :
    (stepDist P hn C₀).toOuterMeasure {D | ¬ Goal D} ≤ 1 - p := by
  have hsum := ProbHitWithin_one_add_step_miss_eq_one P hn C₀ Goal hGoal
  have hhit_le_one : ProbHitWithin P hn C₀ Goal 1 ≤ 1 := by
    calc
      ProbHitWithin P hn C₀ Goal 1
          ≤ ProbHitWithin P hn C₀ Goal 1 +
            (stepDist P hn C₀).toOuterMeasure {D | ¬ Goal D} := by
              exact le_self_add
      _ = 1 := hsum
  have hp_ne_top : p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hp.trans hhit_le_one)
  exact ENNReal.le_sub_of_add_le_left hp_ne_top (by
    calc
      p + (stepDist P hn C₀).toOuterMeasure {D | ¬ Goal D}
          ≤ ProbHitWithin P hn C₀ Goal 1 +
            (stepDist P hn C₀).toOuterMeasure {D | ¬ Goal D} := by
              exact add_le_add_left hp _
      _ = 1 := hsum)

/-- For the potential-decrease goal, one-step hit probability is exactly the
mass of `GoodPairs`. -/
theorem ProbHitWithin_one_eq_pairSetMass_GoodPairs
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (φ : Config Q X n → ℕ) (C₀ : Config Q X n) :
    ProbHitWithin P hn C₀ (fun D => φ D < φ C₀) 1 =
      pairSetMass n hn (GoodPairs P φ C₀) := by
  classical
  rw [ProbHitWithin_one_eq_pairSetMass_filter P hn C₀
    (fun D => φ D < φ C₀) (by omega)]
  rfl

/-- A concrete one-step witness gives the scheduler probability of that
ordered pair as a lower bound for hitting the goal in one step. -/
theorem ProbHitWithin_one_lower_bound_of_step
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀)
    {i j : Fin n} (hij : i ≠ j)
    (hstep : Goal (C₀.step P i j)) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      ProbHitWithin P hn C₀ Goal 1 := by
  classical
  rw [ProbHitWithin_one_eq_pairSetMass_filter P hn C₀ Goal hGoal]
  unfold pairSetMass
  have hmem :
      (i, j) ∈ (OffDiagonalPairs n).filter
        (fun p : Fin n × Fin n => Goal (C₀.step P p.1 p.2)) := by
    rw [Finset.mem_filter]
    exact ⟨(mem_offDiagonalPairs n (i, j)).mpr hij, hstep⟩
  calc
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ = uniformPair n hn (i, j) := by
      rw [uniformPair_apply_of_ne n hn hij]
    _ ≤ ((OffDiagonalPairs n).filter
          (fun p : Fin n × Fin n => Goal (C₀.step P p.1 p.2))).sum
          (fun p => uniformPair n hn p) := by
        exact Finset.single_le_sum (fun p _ => zero_le) hmem

/-- A whole set of one-step witnesses gives its scheduler mass as a lower
bound for the one-step hit probability. -/
theorem ProbHitWithin_one_lower_bound_of_pairSet
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀)
    (S : Finset (Fin n × Fin n))
    (hS : S ⊆ OffDiagonalPairs n)
    (hstep : ∀ p ∈ S, Goal (C₀.step P p.1 p.2)) :
    pairSetMass n hn S ≤ ProbHitWithin P hn C₀ Goal 1 := by
  classical
  rw [ProbHitWithin_one_eq_pairSetMass_filter P hn C₀ Goal hGoal]
  apply pairSetMass_mono
  intro p hp
  rw [Finset.mem_filter]
  exact ⟨hS hp, hstep p hp⟩

/-- If every interaction involving a fixed agent hits the goal, the one-step
hit probability is at least `2 / n`. -/
theorem ProbHitWithin_one_lower_bound_of_agent_participation
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀)
    (μ : Fin n)
    (hstep : ∀ p ∈ PairsInvolving n μ, Goal (C₀.step P p.1 p.2)) :
    (2 : ENNReal) * (n : ENNReal)⁻¹ ≤
      ProbHitWithin P hn C₀ Goal 1 := by
  rw [← pairSetMass_pairsInvolving n hn μ]
  exact ProbHitWithin_one_lower_bound_of_pairSet P hn C₀ Goal hGoal
    (PairsInvolving n μ)
    (fun p hp => (mem_offDiagonalPairs n p).mpr ((mem_PairsInvolving n μ p).mp hp).1)
    hstep

/-- At time zero the goal has already been hit iff it holds at the
initial configuration. -/
theorem probHitBy_zero_of_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : Goal C₀) :
    probHitBy P hn C₀ Goal 0 = 1 := by
  classical
  rw [probHitBy]
  rw [show hitFlagDist P hn C₀ Goal 0 = PMF.pure (C₀, true) by
    simp [hitFlagDist, hGoal]]
  rw [tsum_eq_single (C₀, true)]
  · simp
  · intro S hS
    simp [PMF.pure_apply, hS]

/-- If the initial configuration does not satisfy the goal, then the
time-zero hit probability is zero. -/
theorem probHitBy_zero_of_not_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀) :
    probHitBy P hn C₀ Goal 0 = 0 := by
  classical
  rw [probHitBy]
  simp [hitFlagDist, hGoal]

/-- If the initial configuration already satisfies the goal, the
time-zero non-hit probability is zero. -/
theorem probNotHitBy_zero_of_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : Goal C₀) :
    probNotHitBy P hn C₀ Goal 0 = 0 := by
  classical
  rw [probNotHitBy]
  simp [hitFlagDist, hGoal]

/-- If the initial configuration does not satisfy the goal, the time-zero
non-hit probability is one. -/
theorem probNotHitBy_zero_of_not_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀) :
    probNotHitBy P hn C₀ Goal 0 = 1 := by
  classical
  rw [probNotHitBy]
  rw [show hitFlagDist P hn C₀ Goal 0 = PMF.pure (C₀, false) by
    simp [hitFlagDist, hGoal]]
  rw [tsum_eq_single (C₀, false)]
  · simp
  · intro S hS
    simp [PMF.pure_apply, hS]

/-- From a non-goal initial state, a geometric one-step miss bound yields the
usual `1 - q^t` finite-window success probability. -/
theorem ProbHitWithin_ge_one_sub_pow_of_not_goal_miss
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hGoal : ¬ Goal C₀)
    (hmiss : ∀ C : Config Q X n, ¬ Goal C →
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q) :
    ∀ t : ℕ,
      1 - q ^ t ≤ ProbHitWithin P hn C₀ Goal t := by
  intro t
  simpa [probNotHitBy_zero_of_not_goal P hn C₀ Goal hGoal] using
    ProbHitWithin_ge_one_sub_initial_mul_pow_of_not_goal_miss
      P hn C₀ Goal q hmiss t

/-- Repeated-window high-probability form from a non-goal initial
configuration. -/
theorem ProbHitWithin_mul_window_ge_one_sub_pow_of_not_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) (p : ENNReal)
    (hGoal : ¬ Goal C₀)
    (hwin : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    ∀ r : ℕ,
      1 - (1 - p) ^ r ≤
        ProbHitWithin P hn C₀ Goal (r * K) := by
  intro r
  simpa [probNotHitBy_zero_of_not_goal P hn C₀ Goal hGoal] using
    ProbHitWithin_mul_window_ge_one_sub_initial_mul_pow
      P hn C₀ Goal K p hwin r

/-- Almost-sure eventual reachability, expressed using the finite-prefix
hit probabilities.  This avoids an infinite path-space construction:
`⨆ t, P[T ≤ t] = 1`. -/
def reachesGoalAlmostSurely
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) : Prop :=
  (⨆ t : ℕ, probHitBy P hn C₀ Goal t) = 1

/-- A finite-time tail bound for the first hitting time of `Goal`.
This is the intended primitive for high-probability time statements. -/
def hitsGoalByWithFailureAtMost
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) (ε : ENNReal) : Prop :=
  probNotHitBy P hn C₀ Goal t ≤ ε

/-- A finite-window success lower bound.  This is the primitive used by
the quantitative upper-bound plan: if every non-goal configuration has a
uniform `p` chance to hit `Goal` within `W` steps, then repeated windows
give expected-time and high-probability bounds. -/
def reachesGoalInWindowWithProbAtLeast
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) (p : ENNReal) : Prop :=
  p ≤ ProbHitWithin P hn C₀ Goal t

/-- A goal state succeeds in the zero-length window with probability one. -/
theorem reachesGoalInWindowWithProbAtLeast_zero_of_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : Goal C₀) :
    reachesGoalInWindowWithProbAtLeast P hn C₀ Goal 0 1 := by
  rw [reachesGoalInWindowWithProbAtLeast, ProbHitWithin,
    probHitBy_zero_of_goal P hn C₀ Goal hGoal]

/-- Expected first-hitting time of `Goal` from `C₀` under uniform
random scheduling.

This is the discrete nonnegative-integer tail-sum definition
`E[T] = ∑ t, P[T > t]`, using `hitFlagDist` to encode the finite-prefix
event without constructing the infinite schedule-stream measure. -/
noncomputable def expectedHittingTime
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) : ENNReal :=
  ∑' t : ℕ, probNotHitBy P hn C₀ Goal t

/-- Expected hitting time is monotone contravariantly in the target
predicate: enlarging the goal can only decrease the expected first-hit time. -/
theorem expectedHittingTime_mono_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B : Config Q X n → Prop)
    (hmono : ∀ C : Config Q X n, A C → B C) :
    expectedHittingTime P hn C₀ B ≤ expectedHittingTime P hn C₀ A := by
  rw [expectedHittingTime, expectedHittingTime]
  exact ENNReal.tsum_le_tsum fun t =>
    probNotHitBy_mono_goal P hn C₀ A B hmono t

/-- Markov inequality for hitting time: if the expected hitting time is at most
`M`, then `probNotHitBy` at time `t` is at most `M / (t + 1)`.  This follows
because `expectedHittingTime ≥ (t+1) · probNotHitBy(t)` (the tail is
non-increasing). -/
theorem probNotHitBy_le_expectedHittingTime_div
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ) :
    probNotHitBy P hn C₀ Goal t * (t + 1 : ℕ) ≤
      expectedHittingTime P hn C₀ Goal := by
  rw [expectedHittingTime]
  calc probNotHitBy P hn C₀ Goal t * (↑(t + 1) : ENNReal)
      = ∑ s ∈ Finset.range (t + 1), probNotHitBy P hn C₀ Goal t := by
        rw [Finset.sum_const, Finset.card_range, mul_comm, nsmul_eq_mul]
    _ ≤ ∑ s ∈ Finset.range (t + 1), probNotHitBy P hn C₀ Goal s := by
        apply Finset.sum_le_sum
        intro s hs
        exact probNotHitBy_le_of_le P hn C₀ Goal (by
          rw [Finset.mem_range] at hs; omega)
    _ ≤ ∑' s : ℕ, probNotHitBy P hn C₀ Goal s :=
        ENNReal.sum_le_tsum (Finset.range (t + 1))

/-- Corollary: if `expectedHittingTime ≤ M` and `t + 1 ≥ 2 * M`, then
`ProbHitWithin` at time `t` is at least `1/2`. -/
theorem ProbHitWithin_ge_half_of_expectedHittingTime_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    {M : ℕ} (hM : expectedHittingTime P hn C₀ Goal ≤ M)
    {t : ℕ} (ht : 2 * M ≤ t + 1) :
    ((2 : ENNReal)⁻¹) ≤ ProbHitWithin P hn C₀ Goal t := by
  classical
  let miss := probNotHitBy P hn C₀ Goal t
  have ht_pos : ((t + 1 : ℕ) : ENNReal) ≠ 0 := by norm_num
  have ht_ne_top : ((t + 1 : ℕ) : ENNReal) ≠ ⊤ := by norm_num
  have hmiss_mul :
      miss * ((t + 1 : ℕ) : ENNReal) ≤ (M : ENNReal) := by
    exact (probNotHitBy_le_expectedHittingTime_div P hn C₀ Goal t).trans hM
  have hmiss_le_M_div :
      miss ≤ (M : ENNReal) / ((t + 1 : ℕ) : ENNReal) := by
    exact (ENNReal.le_div_iff_mul_le (Or.inl ht_pos) (Or.inl ht_ne_top)).2
      hmiss_mul
  have htwo_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have htwo_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  have ht_enn :
      (((2 * M : ℕ) : ENNReal)) ≤ ((t + 1 : ℕ) : ENNReal) := by
    exact_mod_cast ht
  have htwoM_cast :
      (((2 * M : ℕ) : ENNReal)) = (2 : ENNReal) * (M : ENNReal) := by
    norm_num
  have htwoM_le_t :
      (2 : ENNReal) * (M : ENNReal) ≤ ((t + 1 : ℕ) : ENNReal) := by
    simpa [htwoM_cast] using ht_enn
  have hM_le_half_mul_t :
      (M : ENNReal) ≤ (2 : ENNReal)⁻¹ * ((t + 1 : ℕ) : ENNReal) := by
    calc
      (M : ENNReal) = (2 : ENNReal)⁻¹ * ((2 : ENNReal) * (M : ENNReal)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel htwo_ne_zero htwo_ne_top, one_mul]
      _ ≤ (2 : ENNReal)⁻¹ * ((t + 1 : ℕ) : ENNReal) := by
        gcongr
  have hM_div_le_half :
      (M : ENNReal) / ((t + 1 : ℕ) : ENNReal) ≤ (2 : ENNReal)⁻¹ := by
    exact (ENNReal.div_le_iff_le_mul (Or.inl ht_pos) (Or.inl ht_ne_top)).2
      (by simpa [mul_comm] using hM_le_half_mul_t)
  have hmiss_le_half : miss ≤ (2 : ENNReal)⁻¹ :=
    hmiss_le_M_div.trans hM_div_le_half
  have hhalf_sub :
      (1 : ENNReal) - (2 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ := by
    simp
  rw [ProbHitWithin_eq_one_sub_probNotHitBy]
  calc
    (2 : ENNReal)⁻¹ = (1 : ENNReal) - (2 : ENNReal)⁻¹ := hhalf_sub.symm
    _ ≤ (1 : ENNReal) - miss := tsub_le_tsub_left hmiss_le_half 1

/-- Compare expected hitting times by comparing all tail probabilities. -/
theorem expectedHittingTime_le_of_tail_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (f : ℕ → ENNReal)
    (hf : ∀ t, probNotHitBy P hn C₀ Goal t ≤ f t) :
    expectedHittingTime P hn C₀ Goal ≤ ∑' t : ℕ, f t := by
  exact ENNReal.tsum_le_tsum hf

/-- Finite truncation of the tail-sum expected hitting time. -/
private noncomputable def truncatedExpectedHittingTime
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (T : ℕ) : ENNReal :=
  ∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t

/-- One-step tail recursion from a non-goal state. -/
private theorem probNotHitBy_succ_eq_tsum_step_of_not_goal
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : ¬ Goal C₀) (t : ℕ) :
    probNotHitBy P hn C₀ Goal (t + 1) =
      ∑' C : Config Q X n,
        stepDist P hn C₀ C * probNotHitBy P hn C Goal t := by
  classical
  rw [← probNotHitFrom_initial_eq_probNotHitBy P hn C₀ Goal (t + 1)]
  simp only [hGoal, decide_false]
  rw [show t + 1 = 1 + t by omega]
  rw [probNotHitFrom_eq_toOuterMeasure, hitFlagDistFrom_add]
  simp only [hitFlagDistFrom, PMF.pure_bind]
  rw [hitFlagStepDist, PMF.bind_map]
  simp only [Bool.false_or]
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro C
  simp only [Function.comp_apply]
  have hdec :
      @decide (Goal C) (Classical.propDecidable (Goal C)) =
        @decide (Goal C) (inferInstance : Decidable (Goal C)) := by
    by_cases h : Goal C <;> simp [h]
  rw [hdec]
  have htail :
      (hitFlagDistFrom P hn Goal (C, decide (Goal C)) t).toOuterMeasure
          {T : Config Q X n × Bool | T.2 = false} =
        probNotHitBy P hn C Goal t := by
    rw [← probNotHitFrom_eq_toOuterMeasure P hn Goal (C, decide (Goal C)) t]
    rw [probNotHitFrom_initial_eq_probNotHitBy P hn C Goal t]
  exact congrArg (fun x => (stepDist P hn C₀) C * x) htail

/-- One-step hit recursion from a non-goal state. -/
private theorem probHitBy_succ_eq_tsum_step_of_not_goal
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : ¬ Goal C₀) (t : ℕ) :
    probHitBy P hn C₀ Goal (t + 1) =
      ∑' C : Config Q X n,
        stepDist P hn C₀ C * probHitBy P hn C Goal t := by
  classical
  rw [probHitBy_eq_hitFlagDist_toOuterMeasure]
  rw [hitFlagDist_eq_hitFlagDistFrom]
  simp only [hGoal, decide_false]
  rw [show t + 1 = 1 + t by omega]
  rw [hitFlagDistFrom_add]
  simp only [hitFlagDistFrom, PMF.pure_bind]
  rw [hitFlagStepDist, PMF.bind_map]
  simp only [Bool.false_or]
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro C
  simp only [Function.comp_apply]
  have hdec :
      @decide (Goal C) (Classical.propDecidable (Goal C)) =
        @decide (Goal C) (inferInstance : Decidable (Goal C)) := by
    by_cases h : Goal C <;> simp [h]
  rw [hdec]
  have hhit :
      (hitFlagDistFrom P hn Goal (C, decide (Goal C)) t).toOuterMeasure
          {T : Config Q X n × Bool | T.2 = true} =
        probHitBy P hn C Goal t := by
    rw [probHitBy_eq_hitFlagDist_toOuterMeasure,
      hitFlagDist_eq_hitFlagDistFrom P hn C Goal t]
  exact congrArg (fun x => (stepDist P hn C₀) C * x) hhit

/-- Finite truncated tail recursion from a non-goal state. -/
private theorem truncatedExpectedHittingTime_succ_eq_of_not_goal
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal] (hGoal : ¬ Goal C₀) (T : ℕ) :
    truncatedExpectedHittingTime P hn C₀ Goal (T + 1) =
      1 + ∑' C : Config Q X n,
        stepDist P hn C₀ C *
          truncatedExpectedHittingTime P hn C Goal T := by
  classical
  rw [truncatedExpectedHittingTime, Finset.sum_range_succ']
  rw [probNotHitBy_zero_of_not_goal P hn C₀ Goal hGoal]
  rw [add_comm]
  congr 1
  calc
    (∑ x ∈ Finset.range T, probNotHitBy P hn C₀ Goal (x + 1))
        = ∑ x ∈ Finset.range T,
            ∑' C : Config Q X n,
              stepDist P hn C₀ C * probNotHitBy P hn C Goal x := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact probNotHitBy_succ_eq_tsum_step_of_not_goal
            P hn C₀ Goal hGoal x
    _ = ∑' C : Config Q X n,
          stepDist P hn C₀ C *
            ∑ x ∈ Finset.range T, probNotHitBy P hn C Goal x := by
          induction T with
          | zero =>
              simp
          | succ T ih =>
              rw [Finset.sum_range_succ, ih]
              rw [← ENNReal.tsum_add]
              apply tsum_congr
              intro C
              rw [Finset.sum_range_succ]
              simp [mul_add]
    _ = ∑' C : Config Q X n,
          stepDist P hn C₀ C *
            truncatedExpectedHittingTime P hn C Goal T := by
          rfl

/-- Expected time composition (strong Markov property): reaching `Goal` via
an intermediate `Mid`.  If `Goal → Mid` (reaching Goal implies reaching Mid
first), then E[T to Goal] ≤ E[T to Mid] + sup_{Mid} E[T from Mid to Goal].

The proof uses: probNotHitBy(Goal, t) ≤ probNotHitBy(Mid, t) + Σ_{s≤t} P(first Mid at s) · probNotHitBy(Goal from Mid, t-s). Summing over t and using Tonelli/Fubini gives the bound. -/
theorem expectedHittingTime_add_le
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Mid Goal : Config Q X n → Prop)
    [DecidablePred Mid] [DecidablePred Goal]
    (M₁ M₂ : ENNReal)
    (hMid : expectedHittingTime P hn C₀ Mid ≤ M₁)
    (hGoal : ∀ C : Config Q X n, Mid C →
      expectedHittingTime P hn C Goal ≤ M₂)
    (hMidGoal : ∀ C, Goal C → Mid C) :
    expectedHittingTime P hn C₀ Goal ≤ M₁ + M₂ := by
  classical
  have htrunc :
      ∀ T : ℕ, ∀ C : Config Q X n,
        truncatedExpectedHittingTime P hn C Goal T ≤
          truncatedExpectedHittingTime P hn C Mid T + M₂ := by
    intro T
    induction T with
    | zero =>
        intro C
        simp [truncatedExpectedHittingTime]
    | succ T ih =>
        intro C
        by_cases hMidC : Mid C
        · have hGoalTrunc :
              truncatedExpectedHittingTime P hn C Goal (T + 1) ≤
                expectedHittingTime P hn C Goal := by
            rw [truncatedExpectedHittingTime, expectedHittingTime]
            exact ENNReal.sum_le_tsum (Finset.range (T + 1))
          calc
            truncatedExpectedHittingTime P hn C Goal (T + 1)
                ≤ expectedHittingTime P hn C Goal := hGoalTrunc
            _ ≤ M₂ := hGoal C hMidC
            _ ≤ truncatedExpectedHittingTime P hn C Mid (T + 1) + M₂ := by
              exact le_add_of_nonneg_left
                (zero_le)
        · have hGoalC : ¬ Goal C := fun h => hMidC (hMidGoal C h)
          rw [truncatedExpectedHittingTime_succ_eq_of_not_goal
            P hn C Goal hGoalC T]
          rw [truncatedExpectedHittingTime_succ_eq_of_not_goal
            P hn C Mid hMidC T]
          have hsum_le :
              (∑' D : Config Q X n,
                  stepDist P hn C D *
                    truncatedExpectedHittingTime P hn D Goal T) ≤
                ∑' D : Config Q X n,
                  stepDist P hn C D *
                    (truncatedExpectedHittingTime P hn D Mid T + M₂) := by
            apply ENNReal.tsum_le_tsum
            intro D
            exact mul_le_mul_right (ih D) ((stepDist P hn C) D)
          have hsum_add :
              (∑' D : Config Q X n,
                  stepDist P hn C D *
                    (truncatedExpectedHittingTime P hn D Mid T + M₂)) =
                (∑' D : Config Q X n,
                  stepDist P hn C D *
                    truncatedExpectedHittingTime P hn D Mid T) + M₂ := by
            calc
              (∑' D : Config Q X n,
                  stepDist P hn C D *
                    (truncatedExpectedHittingTime P hn D Mid T + M₂))
                  = ∑' D : Config Q X n,
                      (stepDist P hn C D *
                        truncatedExpectedHittingTime P hn D Mid T +
                      stepDist P hn C D * M₂) := by
                    apply tsum_congr
                    intro D
                    rw [mul_add]
              _ = (∑' D : Config Q X n,
                    stepDist P hn C D *
                      truncatedExpectedHittingTime P hn D Mid T) +
                  ∑' D : Config Q X n, stepDist P hn C D * M₂ := by
                    rw [ENNReal.tsum_add]
              _ = (∑' D : Config Q X n,
                    stepDist P hn C D *
                      truncatedExpectedHittingTime P hn D Mid T) +
                  (∑' D : Config Q X n, stepDist P hn C D) * M₂ := by
                    rw [ENNReal.tsum_mul_right]
              _ = (∑' D : Config Q X n,
                    stepDist P hn C D *
                      truncatedExpectedHittingTime P hn D Mid T) + M₂ := by
                    rw [PMF.tsum_coe, one_mul]
          calc
            1 + (∑' D : Config Q X n,
              stepDist P hn C D *
                truncatedExpectedHittingTime P hn D Goal T)
                ≤ 1 + ∑' D : Config Q X n,
                    stepDist P hn C D *
                      (truncatedExpectedHittingTime P hn D Mid T + M₂) := by
                  exact add_le_add le_rfl hsum_le
            _ = 1 + ((∑' D : Config Q X n,
                    stepDist P hn C D *
                      truncatedExpectedHittingTime P hn D Mid T) + M₂) := by
                  rw [hsum_add]
            _ = 1 + (∑' D : Config Q X n,
                    stepDist P hn C D *
                      truncatedExpectedHittingTime P hn D Mid T) + M₂ := by
                  rw [add_assoc]
  rw [expectedHittingTime, ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro T
  have hMidTrunc :
      truncatedExpectedHittingTime P hn C₀ Mid T ≤
        expectedHittingTime P hn C₀ Mid := by
    rw [truncatedExpectedHittingTime, expectedHittingTime]
    exact ENNReal.sum_le_tsum (Finset.range T)
  calc
    (∑ t ∈ Finset.range T, probNotHitBy P hn C₀ Goal t)
        = truncatedExpectedHittingTime P hn C₀ Goal T := rfl
    _ ≤ truncatedExpectedHittingTime P hn C₀ Mid T + M₂ := htrunc T C₀
    _ ≤ expectedHittingTime P hn C₀ Mid + M₂ := by
      exact add_le_add hMidTrunc le_rfl
    _ ≤ M₁ + M₂ := by
      exact add_le_add hMid le_rfl

/-- Absorbing-goal version of `expectedHittingTime_add_le`.
When `Goal` is absorbing, the composition is simpler: `probNotHitBy Goal t`
decomposes cleanly because once Goal is reached, it persists. -/
theorem expectedHittingTime_add_le_of_absorbing
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Mid Goal : Config Q X n → Prop)
    [DecidablePred Mid] [DecidablePred Goal]
    (M₁ M₂ : ENNReal)
    (_hAbsorb : ∀ C, Goal C → ∀ i j : Fin n, Goal (C.step P i j))
    (hMid : expectedHittingTime P hn C₀ Mid ≤ M₁)
    (hGoal : ∀ C : Config Q X n, Mid C →
      expectedHittingTime P hn C Goal ≤ M₂)
    (hMidGoal : ∀ C, Goal C → Mid C) :
    expectedHittingTime P hn C₀ Goal ≤ M₁ + M₂ := by
  exact expectedHittingTime_add_le P hn C₀ Mid Goal M₁ M₂ hMid hGoal hMidGoal

/-- Reindex a block-constant geometric tail by quotient and remainder. -/
theorem tsum_pow_div_eq_mul_tsum_pow
    (K : ℕ) [NeZero K] (q : ENNReal) :
    (∑' t : ℕ, q ^ (t / K)) = (K : ENNReal) * ∑' r : ℕ, q ^ r := by
  calc
    (∑' t : ℕ, q ^ (t / K))
        = ∑' p : ℕ × Fin K, q ^ (((Nat.divModEquiv K).symm p) / K) := by
            rw [← (Nat.divModEquiv K).symm.tsum_eq
              (fun t : ℕ => q ^ (t / K))]
    _ = ∑' p : ℕ × Fin K, q ^ p.1 := by
          apply tsum_congr
          intro p
          rw [Nat.divModEquiv_symm_apply]
          have hK : 0 < K := NeZero.pos K
          have hdiv : (p.1 * K + (p.2 : ℕ)) / K = p.1 := by
            rw [mul_comm p.1 K, Nat.mul_add_div hK,
              Nat.div_eq_of_lt p.2.is_lt, add_zero]
          rw [hdiv]
    _ = ∑' r : ℕ, ∑' s : Fin K, q ^ r := by
          exact ENNReal.tsum_prod (f := fun (r : ℕ) (_s : Fin K) => q ^ r)
    _ = ∑' r : ℕ, (K : ENNReal) * q ^ r := by
          apply tsum_congr
          intro r
          rw [tsum_fintype]
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (K : ENNReal) * ∑' r : ℕ, q ^ r := by
          rw [ENNReal.tsum_mul_left]

/-- If the initial state is already a goal state, the expected hitting time is
zero. -/
theorem expectedHittingTime_eq_zero_of_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : Goal C₀) :
    expectedHittingTime P hn C₀ Goal = 0 := by
  rw [expectedHittingTime]
  apply ENNReal.tsum_eq_zero.2
  intro t
  have htail :
      probNotHitBy P hn C₀ Goal t ≤ probNotHitBy P hn C₀ Goal 0 :=
    probNotHitBy_le_of_le P hn C₀ Goal (Nat.zero_le t)
  rw [probNotHitBy_zero_of_goal P hn C₀ Goal hGoal] at htail
  exact le_antisymm htail (zero_le)

/-- A uniform `K`-step success window gives the expected-time bound in
geometric-series form. -/
theorem expectedHittingTime_le_window_mul_tsum_pow_of_not_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) [NeZero K] (p : ENNReal)
    (hGoal : ¬ Goal C₀)
    (hwin : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    expectedHittingTime P hn C₀ Goal ≤
      (K : ENNReal) * ∑' r : ℕ, (1 - p) ^ r := by
  calc
    expectedHittingTime P hn C₀ Goal
        ≤ ∑' t : ℕ, (1 - p) ^ (t / K) := by
          apply expectedHittingTime_le_of_tail_bound
          intro t
          have hfloor : (t / K) * K ≤ t := Nat.div_mul_le_self t K
          have hmono :
              probNotHitBy P hn C₀ Goal t ≤
                probNotHitBy P hn C₀ Goal ((t / K) * K) :=
            probNotHitBy_le_of_le P hn C₀ Goal hfloor
          have hendpoint :
              probNotHitBy P hn C₀ Goal ((t / K) * K) ≤
                probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ (t / K) :=
            probNotHitBy_mul_window_le_initial_mul_pow
              P hn C₀ Goal K p hwin (t / K)
          calc
            probNotHitBy P hn C₀ Goal t
                ≤ probNotHitBy P hn C₀ Goal ((t / K) * K) := hmono
            _ ≤ probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ (t / K) := hendpoint
            _ = (1 - p) ^ (t / K) := by
                  rw [probNotHitBy_zero_of_not_goal P hn C₀ Goal hGoal]
                  simp
    _ = (K : ENNReal) * ∑' r : ℕ, (1 - p) ^ r := by
          exact tsum_pow_div_eq_mul_tsum_pow K (1 - p)

/-- A uniform `K`-step success lower bound gives expected hitting time at most
`K / p`.  This is the abstract window-amplification lemma used by the
time-bound layer. -/
theorem expectedHittingTime_le_window_mul_inv
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) [NeZero K] (p : ENNReal)
    (hp_le_one : p ≤ 1)
    (hwin : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    expectedHittingTime P hn C₀ Goal ≤ (K : ENNReal) * p⁻¹ := by
  by_cases hGoal : Goal C₀
  · rw [expectedHittingTime_eq_zero_of_goal P hn C₀ Goal hGoal]
    exact zero_le
  · have hbound :=
      expectedHittingTime_le_window_mul_tsum_pow_of_not_goal
        P hn C₀ Goal K p hGoal hwin
    calc
      expectedHittingTime P hn C₀ Goal
          ≤ (K : ENNReal) * ∑' r : ℕ, (1 - p) ^ r := hbound
      _ = (K : ENNReal) * (1 - (1 - p))⁻¹ := by
            rw [ENNReal.tsum_geometric]
      _ = (K : ENNReal) * p⁻¹ := by
            rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hp_le_one]

/-- Geometric tail comparison for the expected hitting time, leaving the
geometric series value explicit. -/
theorem expectedHittingTime_le_initial_mul_tsum_pow_of_not_goal_miss
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hmiss : ∀ C : Config Q X n, ¬ Goal C →
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q) :
    expectedHittingTime P hn C₀ Goal ≤
      probNotHitBy P hn C₀ Goal 0 * ∑' t : ℕ, q ^ t := by
  calc
    expectedHittingTime P hn C₀ Goal
        ≤ ∑' t : ℕ, probNotHitBy P hn C₀ Goal 0 * q ^ t := by
          exact expectedHittingTime_le_of_tail_bound P hn C₀ Goal
            (fun t => probNotHitBy P hn C₀ Goal 0 * q ^ t)
            (probNotHitBy_le_initial_mul_pow_of_not_goal_miss
              P hn C₀ Goal q hmiss)
    _ = probNotHitBy P hn C₀ Goal 0 * ∑' t : ℕ, q ^ t := by
          rw [ENNReal.tsum_mul_left]

/-- From a non-goal initial state, the initial tail term is one, so the
geometric expected-time bound has no leading factor. -/
theorem expectedHittingTime_le_tsum_pow_of_not_goal_miss
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hGoal : ¬ Goal C₀)
    (hmiss : ∀ C : Config Q X n, ¬ Goal C →
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q) :
    expectedHittingTime P hn C₀ Goal ≤ ∑' t : ℕ, q ^ t := by
  simpa [probNotHitBy_zero_of_not_goal P hn C₀ Goal hGoal] using
    expectedHittingTime_le_initial_mul_tsum_pow_of_not_goal_miss
      P hn C₀ Goal q hmiss

/-- Closed geometric-series form of
`expectedHittingTime_le_initial_mul_tsum_pow_of_not_goal_miss`. -/
theorem expectedHittingTime_le_initial_mul_inv_one_sub_of_not_goal_miss
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hmiss : ∀ C : Config Q X n, ¬ Goal C →
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q) :
    expectedHittingTime P hn C₀ Goal ≤
      probNotHitBy P hn C₀ Goal 0 * (1 - q)⁻¹ := by
  simpa [ENNReal.tsum_geometric] using
    expectedHittingTime_le_initial_mul_tsum_pow_of_not_goal_miss
      P hn C₀ Goal q hmiss

/-- Closed geometric expected-time bound from a non-goal initial state. -/
theorem expectedHittingTime_le_inv_one_sub_of_not_goal_miss
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (q : ENNReal)
    (hGoal : ¬ Goal C₀)
    (hmiss : ∀ C : Config Q X n, ¬ Goal C →
      (stepDist P hn C).toOuterMeasure {D | ¬ Goal D} ≤ q) :
    expectedHittingTime P hn C₀ Goal ≤ (1 - q)⁻¹ := by
  simpa [ENNReal.tsum_geometric] using
    expectedHittingTime_le_tsum_pow_of_not_goal_miss
      P hn C₀ Goal q hGoal hmiss

/-- If every non-goal state has one-step success probability at least `p`, then
the expected hitting time is bounded by the corresponding geometric mean. -/
theorem expectedHittingTime_le_inv_of_ProbHitWithin_one_lower_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (p : ENNReal)
    (hGoal : ¬ Goal C₀)
    (hp : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal 1) :
    expectedHittingTime P hn C₀ Goal ≤ p⁻¹ := by
  have hhit_le_one : ProbHitWithin P hn C₀ Goal 1 ≤ 1 := by
    calc
      ProbHitWithin P hn C₀ Goal 1
          ≤ ProbHitWithin P hn C₀ Goal 1 +
            probNotHitBy P hn C₀ Goal 1 := by
              exact le_self_add
      _ = 1 := probHitBy_add_probNotHitBy P hn C₀ Goal 1
  have hp_le_one : p ≤ 1 := (hp C₀ hGoal).trans hhit_le_one
  have hbound := expectedHittingTime_le_inv_one_sub_of_not_goal_miss
    P hn C₀ Goal (1 - p) hGoal
    (fun C hC =>
      step_miss_le_one_sub_of_ProbHitWithin_one_lower_bound
        P hn C Goal p hC (hp C hC))
  simpa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hp_le_one] using hbound

/-- High-probability companion of
`expectedHittingTime_le_inv_of_ProbHitWithin_one_lower_bound`: a uniform
one-step success lower bound gives a geometric finite-window lower bound. -/
theorem ProbHitWithin_ge_one_sub_pow_of_ProbHitWithin_one_lower_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (p : ENNReal)
    (hGoal : ¬ Goal C₀)
    (hp : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal 1) :
    ∀ t : ℕ,
      1 - (1 - p) ^ t ≤ ProbHitWithin P hn C₀ Goal t := by
  exact ProbHitWithin_ge_one_sub_pow_of_not_goal_miss
    P hn C₀ Goal (1 - p) hGoal
    (fun C hC =>
      step_miss_le_one_sub_of_ProbHitWithin_one_lower_bound
        P hn C Goal p hC (hp C hC))

/-- Local one-step window amplification.  If the one-step lower bound is
available only while the chain remains in a phase region `Region`, then the
right target for geometric amplification is "hit `Goal` or leave `Region`".
This is the exact form needed for phase-window proofs where leaving the
current phase is itself routed to the next case. -/
theorem ProbHitWithin_ge_one_sub_pow_of_local_one_lower_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Region Goal : Config Q X n → Prop)
    (p : ENNReal)
    (hRegion : Region C₀) (hGoal : ¬ Goal C₀)
    (hp : ∀ C : Config Q X n, Region C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C (fun D => Goal D ∨ ¬ Region D) 1) :
    ∀ t : ℕ,
      1 - (1 - p) ^ t ≤
        ProbHitWithin P hn C₀ (fun D => Goal D ∨ ¬ Region D) t := by
  classical
  apply ProbHitWithin_ge_one_sub_pow_of_ProbHitWithin_one_lower_bound
    (P := P) (hn := hn) (C₀ := C₀)
    (Goal := fun D => Goal D ∨ ¬ Region D) (p := p)
  · intro hTarget
    rcases hTarget with hG | hNotRegion
    · exact hGoal hG
    · exact hNotRegion hRegion
  · intro C hTarget
    have hRegionC : Region C := by
      by_contra h
      exact hTarget (Or.inr h)
    have hGoalC : ¬ Goal C := by
      intro h
      exact hTarget (Or.inl h)
    exact hp C hRegionC hGoalC

/-- Expected-time version of
`ProbHitWithin_ge_one_sub_pow_of_local_one_lower_bound`. -/
theorem expectedHittingTime_le_inv_of_local_one_lower_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Region Goal : Config Q X n → Prop)
    (p : ENNReal)
    (hRegion : Region C₀) (hGoal : ¬ Goal C₀)
    (hp : ∀ C : Config Q X n, Region C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C (fun D => Goal D ∨ ¬ Region D) 1) :
    expectedHittingTime P hn C₀ (fun D => Goal D ∨ ¬ Region D) ≤ p⁻¹ := by
  classical
  apply expectedHittingTime_le_inv_of_ProbHitWithin_one_lower_bound
    (P := P) (hn := hn) (C₀ := C₀)
    (Goal := fun D => Goal D ∨ ¬ Region D) (p := p)
  · intro hTarget
    rcases hTarget with hG | hNotRegion
    · exact hGoal hG
    · exact hNotRegion hRegion
  · intro C hTarget
    have hRegionC : Region C := by
      by_contra h
      exact hTarget (Or.inr h)
    have hGoalC : ¬ Goal C := by
      intro h
      exact hTarget (Or.inl h)
    exact hp C hRegionC hGoalC

/-- If the initial configuration is not already a goal state, the
sequential expected hitting time is at least one interaction.  This is the
first tail-sum term. -/
theorem one_le_expectedHittingTime_of_not_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀) :
    (1 : ENNReal) ≤ expectedHittingTime P hn C₀ Goal := by
  rw [expectedHittingTime]
  calc
    (1 : ENNReal) = probNotHitBy P hn C₀ Goal 0 := by
      rw [probNotHitBy_zero_of_not_goal P hn C₀ Goal hGoal]
    _ ≤ ∑' t : ℕ, probNotHitBy P hn C₀ Goal t := ENNReal.le_tsum 0

/-- Alias used in phase-bound theorem statements when we want to stress
that the underlying clock is sequential interactions. -/
noncomputable abbrev expectedSequentialTime
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) : ENNReal :=
  expectedHittingTime P hn C₀ Goal

/-- Parallel time: sequential expected hitting time divided by `n`.
A *parallel round* in the population-protocol model consists of `n`
sequential pair-pick steps (Kanaya §2). -/
noncomputable def parallelTime (T : ENNReal) (n : ℕ) : ENNReal :=
  T / n

/-- Expected parallel time for a generic goal predicate.
Used by Theorem 3 (output-stability goal, generic `Q`) and by the §5.2
upper bound (consensus goal, `Q = AgentState n`). -/
noncomputable def expectedParallelTime
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) : ENNReal :=
  parallelTime (expectedHittingTime P hn C₀ Goal) n

/-- Parallel-time version of `one_le_expectedHittingTime_of_not_goal`. -/
theorem inv_nat_le_expectedParallelTime_of_not_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ¬ Goal C₀) :
    (((n : ENNReal))⁻¹) ≤ expectedParallelTime P hn C₀ Goal := by
  rw [expectedParallelTime, parallelTime]
  have hseq := one_le_expectedHittingTime_of_not_goal P hn C₀ Goal hGoal
  calc
    (((n : ENNReal))⁻¹) = (1 : ENNReal) / n := by simp
    _ ≤ expectedHittingTime P hn C₀ Goal / n := by
      exact ENNReal.div_le_div_right hseq (n : ENNReal)

/-- A sequential expected-time upper bound immediately gives the corresponding
parallel-time upper bound after division by `n`. -/
theorem expectedParallelTime_le_of_expectedHittingTime_le
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    {B : ENNReal}
    (hB : expectedHittingTime P hn C₀ Goal ≤ B) :
    expectedParallelTime P hn C₀ Goal ≤ B / n := by
  rw [expectedParallelTime, parallelTime]
  exact ENNReal.div_le_div_right hB (n : ENNReal)

/-- Parallel-time form of the constant-success-window expected-time bound. -/
theorem expectedParallelTime_le_window_mul_inv
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) [NeZero K] (p : ENNReal)
    (hp_le_one : p ≤ 1)
    (hwin : ∀ C : Config Q X n, ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    expectedParallelTime P hn C₀ Goal ≤ ((K : ENNReal) * p⁻¹) / n := by
  exact expectedParallelTime_le_of_expectedHittingTime_le P hn C₀ Goal
    (expectedHittingTime_le_window_mul_inv P hn C₀ Goal K p hp_le_one hwin)

/-- Invariant-aware window amplification: if `Inv` is preserved by every
protocol step and the window property holds for `Inv` configs, then the
expected hitting time from an `Inv` initial config is at most `K / p`.

The proof is identical to `expectedHittingTime_le_window_mul_inv` but
threads the invariant through the Markov chain: since `nthStepDist` from
an `Inv` config only puts mass on `Inv` configs, the window hypothesis
is only needed on the `Inv` subspace. -/
theorem nthStepDist_support_inv
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Inv : Config Q X n → Prop)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (t : ℕ) : ∀ C : Config Q X n, C ∈ (nthStepDist P hn C₀ t).support → Inv C := by
  induction t with
  | zero =>
    intro C hC
    have hCeq : C = C₀ := by
      simpa [nthStepDist, PMF.support_pure] using hC
    exact hCeq ▸ hInv₀
  | succ t ih =>
    intro C hC
    rw [nthStepDist, PMF.mem_support_bind_iff] at hC
    obtain ⟨C', hC'supp, hCstep⟩ := hC
    have hInvC' := ih C' hC'supp
    rw [stepDist, PMF.support_map] at hCstep
    obtain ⟨pair, _, hpair_eq⟩ := hCstep
    rw [← hpair_eq]
    exact hInvStep C' hInvC' pair.1 pair.2

private theorem hitFlagDist_support_inv
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (t : ℕ) (C : Config Q X n) (b : Bool) :
    (C, b) ∈ (hitFlagDist P hn C₀ Goal t).support → Inv C := by
  intro hmem
  have hfst : C ∈ ((hitFlagDist P hn C₀ Goal t).map Prod.fst).support := by
    rw [PMF.support_map]
    exact ⟨(C, b), hmem, rfl⟩
  rw [hitFlagDist_map_fst] at hfst
  exact nthStepDist_support_inv P hn C₀ Inv hInv₀ hInvStep t C hfst

private theorem hitFlagDist_support_true_goal_of_absorbing
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hAbsorb : ∀ C : Config Q X n, Goal C →
      ∀ i j : Fin n, Goal (C.step P i j)) :
    ∀ t : ℕ, ∀ C : Config Q X n,
      (C, true) ∈ (hitFlagDist P hn C₀ Goal t).support → Goal C
  | 0, C => by
      classical
      intro hmem
      rw [hitFlagDist, PMF.support_pure] at hmem
      have hC : C = C₀ := by
        simpa using congrArg Prod.fst hmem
      have hb : true = decide (Goal C₀) := by
        simpa using congrArg Prod.snd hmem
      rw [hC]
      exact of_decide_eq_true hb.symm
  | t + 1, C => by
      classical
      intro hmem
      rw [hitFlagDist, PMF.mem_support_bind_iff] at hmem
      obtain ⟨S, hS, hstep⟩ := hmem
      rcases S with ⟨D, b⟩
      rw [hitFlagStepDist, PMF.support_map] at hstep
      obtain ⟨E, hE, hEeq⟩ := hstep
      have hCE : C = E := by
        simpa using (congrArg Prod.fst hEeq).symm
      subst C
      cases b
      · have hb : decide (Goal E) = true := by
          simpa using congrArg Prod.snd hEeq
        exact of_decide_eq_true hb
      · have hGoalD :
            Goal D :=
          hitFlagDist_support_true_goal_of_absorbing
            P hn C₀ Goal hAbsorb t D hS
        rw [stepDist, PMF.support_map] at hE
        obtain ⟨p, _hp, hpE⟩ := hE
        rw [← hpE]
        exact hAbsorb D hGoalD p.1 p.2

/-- If no configuration satisfies the target, the finite-prefix hit
probability is zero. -/
theorem ProbHitWithin_eq_zero_of_forall_not
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (hGoal : ∀ C : Config Q X n, ¬ Goal C) :
    ∀ t : ℕ, ProbHitWithin P hn C₀ Goal t = 0 := by
  intro t
  rw [ProbHitWithin, probHitBy_eq_hitFlagDist_toOuterMeasure]
  rw [PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_eq_zero.2
  intro S
  rcases S with ⟨C, b⟩
  cases b
  · simp
  · have hzero : hitFlagDist P hn C₀ Goal t (C, true) = 0 := by
      rw [PMF.apply_eq_zero_iff]
      intro hmem
      exact hGoal C
        (hitFlagDist_support_true_goal_of_absorbing
          P hn C₀ Goal (by
            intro D hD i j
            exact False.elim (hGoal D hD)) t C hmem)
    simp [hzero]

/-- **ProbHitWithin chain composition** (strong Markov property).
If `Mid` is hit by time `t₁` with probability ≥ p, and from any `Mid` config
`Goal` is hit within `t₂` steps with probability ≥ q, then `Goal` is hit
by time `t₁ + t₂` with probability ≥ p * q.

Unlike `probReached_add_ge_mul`, this uses ProbHitWithin for the
intermediate target, so non-absorbing `Mid` works without endpoint
absorption. -/
theorem ProbHitWithin_add_ge_mul
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Mid Goal : Config Q X n → Prop)
    [DecidablePred Mid] [DecidablePred Goal]
    (t₁ t₂ : ℕ) (p q : ENNReal)
    (hMid : p ≤ ProbHitWithin P hn C₀ Mid t₁)
    (hGoal : ∀ C : Config Q X n, Mid C →
      q ≤ ProbHitWithin P hn C Goal t₂) :
    p * q ≤ ProbHitWithin P hn C₀ Goal (t₁ + t₂) := by
  classical
  have hprod_le_one :
      ∀ C : Config Q X n, ∀ t : ℕ, ∀ r : ENNReal,
        r ≤ ProbHitWithin P hn C Mid t → r * q ≤ 1 := by
    intro C t r hr
    by_cases hEx : ∃ D : Config Q X n, Mid D
    · obtain ⟨D, hD⟩ := hEx
      have hq_le_one : q ≤ 1 :=
        (hGoal D hD).trans (ProbHitWithin_le_one P hn D Goal t₂)
      have hr_le_one : r ≤ 1 :=
        hr.trans (ProbHitWithin_le_one P hn C Mid t)
      calc
        r * q ≤ 1 * q := mul_le_mul_left hr_le_one q
        _ = q := by rw [one_mul]
        _ ≤ 1 := hq_le_one
    · push_neg at hEx
      have hzero : ProbHitWithin P hn C Mid t = 0 :=
        ProbHitWithin_eq_zero_of_forall_not P hn C Mid hEx t
      have hr0 : r = 0 := le_antisymm (hr.trans (le_of_eq hzero)) (zero_le)
      simp [hr0]
  revert C₀ p hMid
  induction t₁ with
  | zero =>
      intro C₀ p hMid
      by_cases hMidC : Mid C₀
      · have hp_le_one : p ≤ 1 :=
          hMid.trans (ProbHitWithin_le_one P hn C₀ Mid 0)
        calc
          p * q ≤ 1 * q := mul_le_mul_left hp_le_one q
          _ = q := by rw [one_mul]
          _ ≤ ProbHitWithin P hn C₀ Goal t₂ := hGoal C₀ hMidC
          _ = ProbHitWithin P hn C₀ Goal (0 + t₂) := by simp
      · have hzero : ProbHitWithin P hn C₀ Mid 0 = 0 := by
          rw [ProbHitWithin, probHitBy_zero_of_not_goal P hn C₀ Mid hMidC]
        have hp0 : p = 0 := le_antisymm (hMid.trans (le_of_eq hzero)) (zero_le)
        simp [hp0]
  | succ t ih =>
      intro C₀ p hMid
      by_cases hMidC : Mid C₀
      · have hp_le_one : p ≤ 1 :=
          hMid.trans (ProbHitWithin_le_one P hn C₀ Mid (t + 1))
        calc
          p * q ≤ 1 * q := mul_le_mul_left hp_le_one q
          _ = q := by rw [one_mul]
          _ ≤ ProbHitWithin P hn C₀ Goal t₂ := hGoal C₀ hMidC
          _ ≤ ProbHitWithin P hn C₀ Goal ((t + 1) + t₂) :=
              ProbHitWithin_mono_time P hn C₀ Goal (by omega)
      · by_cases hGoalC : Goal C₀
        · have hprod : p * q ≤ 1 := hprod_le_one C₀ (t + 1) p hMid
          have hone : ProbHitWithin P hn C₀ Goal ((t + 1) + t₂) = 1 := by
            apply le_antisymm
            · exact ProbHitWithin_le_one P hn C₀ Goal ((t + 1) + t₂)
            · calc
                1 = ProbHitWithin P hn C₀ Goal 0 := by
                  rw [ProbHitWithin, probHitBy_zero_of_goal P hn C₀ Goal hGoalC]
                _ ≤ ProbHitWithin P hn C₀ Goal ((t + 1) + t₂) :=
                  ProbHitWithin_mono_time P hn C₀ Goal (by omega)
          simpa [hone] using hprod
        · have hMidRec :
              ProbHitWithin P hn C₀ Mid (t + 1) =
                ∑' D : Config Q X n,
                  stepDist P hn C₀ D * ProbHitWithin P hn D Mid t := by
            rw [ProbHitWithin]
            exact probHitBy_succ_eq_tsum_step_of_not_goal P hn C₀ Mid hMidC t
          have hGoalRec :
              ProbHitWithin P hn C₀ Goal ((t + 1) + t₂) =
                ∑' D : Config Q X n,
                  stepDist P hn C₀ D *
                    ProbHitWithin P hn D Goal (t + t₂) := by
            rw [show (t + 1) + t₂ = (t + t₂) + 1 by omega]
            rw [ProbHitWithin]
            exact probHitBy_succ_eq_tsum_step_of_not_goal
              P hn C₀ Goal hGoalC (t + t₂)
          calc
            p * q ≤ ProbHitWithin P hn C₀ Mid (t + 1) * q :=
              mul_le_mul_left hMid q
            _ = (∑' D : Config Q X n,
                  stepDist P hn C₀ D * ProbHitWithin P hn D Mid t) * q := by
              rw [hMidRec]
            _ = ∑' D : Config Q X n,
                  stepDist P hn C₀ D *
                    (ProbHitWithin P hn D Mid t * q) := by
              rw [← ENNReal.tsum_mul_right]
              apply tsum_congr
              intro D
              rw [mul_assoc]
            _ ≤ ∑' D : Config Q X n,
                  stepDist P hn C₀ D *
                    ProbHitWithin P hn D Goal (t + t₂) := by
              apply ENNReal.tsum_le_tsum
              intro D
              exact mul_le_mul_right (ih D (ProbHitWithin P hn D Mid t) le_rfl)
                (stepDist P hn C₀ D)
            _ = ProbHitWithin P hn C₀ Goal ((t + 1) + t₂) := hGoalRec.symm

/-- For an absorbing goal (preserved by every step), `ProbHitWithin ≤ probReached`
at every time — once you hit, you stay. -/
theorem ProbHitWithin_le_probReached_of_absorbing
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal]
    (hAbsorb : ∀ C : Config Q X n, Goal C →
      ∀ i j : Fin n, Goal (C.step P i j))
    (t : ℕ) :
    ProbHitWithin P hn C₀ Goal t ≤ probReached P hn C₀ Goal t := by
  classical
  rw [ProbHitWithin, probHitBy_eq_hitFlagDist_toOuterMeasure]
  rw [probReached_eq_toOuterMeasure]
  rw [← hitFlagDist_map_fst P hn C₀ Goal t]
  rw [PMF.toOuterMeasure_map_apply]
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply ENNReal.tsum_le_tsum
  intro S
  rcases S with ⟨C, b⟩
  cases b
  · rw [Set.indicator_of_notMem
      (s := {S : Config Q X n × Bool | S.2 = true})
      (a := (C, false)) (f := hitFlagDist P hn C₀ Goal t)
      (by simp)]
    simp
  · by_cases hGoalC : Goal C
    · rw [Set.indicator_of_mem
        (s := {S : Config Q X n × Bool | S.2 = true})
        (a := (C, true)) (f := hitFlagDist P hn C₀ Goal t)
        (by simp)]
      rw [Set.indicator_of_mem
        (s := Prod.fst ⁻¹' {C : Config Q X n | Goal C})
        (a := (C, true)) (f := hitFlagDist P hn C₀ Goal t)
        (by simpa using hGoalC)]
    · rw [Set.indicator_of_mem
        (s := {S : Config Q X n × Bool | S.2 = true})
        (a := (C, true)) (f := hitFlagDist P hn C₀ Goal t)
        (by simp)]
      rw [Set.indicator_of_notMem
        (s := Prod.fst ⁻¹' {C : Config Q X n | Goal C})
        (a := (C, true)) (f := hitFlagDist P hn C₀ Goal t)
        (by simpa using hGoalC)]
      have hzero :
          hitFlagDist P hn C₀ Goal t (C, true) = 0 := by
        exact (PMF.apply_eq_zero_iff _ _).mpr fun hmem =>
          hGoalC
            (hitFlagDist_support_true_goal_of_absorbing
              P hn C₀ Goal hAbsorb t C hmem)
      rw [hzero]

/-- Invariant-aware version of `probNotHitBy_add_window_le_mul`.
Only `Inv` states can carry positive mass from an `Inv` initial state, so the
window hypothesis is needed only on the invariant subspace. -/
private theorem probNotHitBy_add_window_le_mul_of_invariant
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (K t : ℕ) (p : ENNReal)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (hwin : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    probNotHitBy P hn C₀ Goal (t + K) ≤
      probNotHitBy P hn C₀ Goal t * (1 - p) := by
  classical
  rw [← probNotHitFrom_initial_eq_probNotHitBy P hn C₀ Goal (t + K)]
  rw [probNotHitFrom_add_eq_tsum]
  calc
    (∑' T : Config Q X n × Bool,
        hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t T *
          probNotHitFrom P hn Goal T K)
        ≤
      ∑' T : Config Q X n × Bool,
        hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t T *
          (if T.2 = false then 1 - p else 0) := by
        apply ENNReal.tsum_le_tsum
        intro T
        rcases T with ⟨C, b⟩
        cases b
        · by_cases hGoalC : Goal C
          · have hzero :
                hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t
                  (C, false) = 0 := by
              rw [← hitFlagDist_eq_hitFlagDistFrom]
              exact hitFlagDist_apply_false_of_goal P hn C₀ C Goal hGoalC t
            rw [hzero]
            simp
          · by_cases hInvC : Inv C
            · have hblock :
                  probNotHitFrom P hn Goal (C, false) K ≤ 1 - p :=
                probNotHitFrom_false_le_one_sub_of_ProbHitWithin_lower_bound
                  P hn C Goal K p hGoalC (hwin C hInvC hGoalC)
              have hmul := mul_le_mul_right hblock
                (hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t (C, false))
              simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
            · have hzero :
                  hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t
                    (C, false) = 0 := by
                have hnotmem :
                    ¬ (C, false) ∈ (hitFlagDist P hn C₀ Goal t).support := by
                  intro hmem
                  exact hInvC
                    (hitFlagDist_support_inv P hn C₀ Goal Inv
                      hInv₀ hInvStep t C false hmem)
                rw [hitFlagDist_eq_hitFlagDistFrom] at hnotmem
                rw [PMF.mem_support_iff] at hnotmem
                exact not_not.mp hnotmem
              rw [hzero]
              simp
        · rw [probNotHitFrom_true]
          simp
    _ =
      (∑' T : Config Q X n × Bool,
        (if T.2 = false then
          hitFlagDistFrom P hn Goal (C₀, decide (Goal C₀)) t T
        else 0)) * (1 - p) := by
        rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro T
        by_cases hT : T.2 = false <;> simp [hT, mul_comm]
    _ = probNotHitBy P hn C₀ Goal t * (1 - p) := by
        rw [← probNotHitFrom_initial_eq_probNotHitBy P hn C₀ Goal t]
        rw [probNotHitFrom]

private theorem probNotHitBy_mul_window_le_initial_mul_pow_of_invariant
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (K : ℕ) (p : ENNReal)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (hwin : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    ∀ r : ℕ,
      probNotHitBy P hn C₀ Goal (r * K) ≤
        probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ r
  | 0 => by simp
  | r + 1 => by
      have hstep :=
        probNotHitBy_add_window_le_mul_of_invariant
          P hn C₀ Goal Inv K (r * K) p hInv₀ hInvStep hwin
      have ih :=
        probNotHitBy_mul_window_le_initial_mul_pow_of_invariant
          P hn C₀ Goal Inv K p hInv₀ hInvStep hwin r
      calc
        probNotHitBy P hn C₀ Goal ((r + 1) * K)
            = probNotHitBy P hn C₀ Goal (r * K + K) := by
              rw [Nat.succ_mul]
        _ ≤ probNotHitBy P hn C₀ Goal (r * K) * (1 - p) := hstep
        _ ≤ (probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ r) * (1 - p) := by
              exact mul_le_mul_left ih _
        _ = probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ (r + 1) := by
              rw [pow_succ, mul_assoc]

private theorem expectedHittingTime_le_window_mul_tsum_pow_of_not_goal_of_invariant
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (K : ℕ) [NeZero K] (p : ENNReal)
    (hGoal : ¬ Goal C₀)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (hwin : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    expectedHittingTime P hn C₀ Goal ≤
      (K : ENNReal) * ∑' r : ℕ, (1 - p) ^ r := by
  calc
    expectedHittingTime P hn C₀ Goal
        ≤ ∑' t : ℕ, (1 - p) ^ (t / K) := by
          apply expectedHittingTime_le_of_tail_bound
          intro t
          have hfloor : (t / K) * K ≤ t := Nat.div_mul_le_self t K
          have hmono :
              probNotHitBy P hn C₀ Goal t ≤
                probNotHitBy P hn C₀ Goal ((t / K) * K) :=
            probNotHitBy_le_of_le P hn C₀ Goal hfloor
          have hendpoint :
              probNotHitBy P hn C₀ Goal ((t / K) * K) ≤
                probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ (t / K) :=
            probNotHitBy_mul_window_le_initial_mul_pow_of_invariant
              P hn C₀ Goal Inv K p hInv₀ hInvStep hwin (t / K)
          calc
            probNotHitBy P hn C₀ Goal t
                ≤ probNotHitBy P hn C₀ Goal ((t / K) * K) := hmono
            _ ≤ probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ (t / K) := hendpoint
            _ = (1 - p) ^ (t / K) := by
                  rw [probNotHitBy_zero_of_not_goal P hn C₀ Goal hGoal]
                  simp
    _ = (K : ENNReal) * ∑' r : ℕ, (1 - p) ^ r := by
          exact tsum_pow_div_eq_mul_tsum_pow K (1 - p)

theorem expectedHittingTime_le_window_mul_inv_of_invariant
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (K : ℕ) [NeZero K] (p : ENNReal)
    (hp_le_one : p ≤ 1)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (hwin : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    expectedHittingTime P hn C₀ Goal ≤ (K : ENNReal) * p⁻¹ := by
  by_cases hGoal : Goal C₀
  · rw [expectedHittingTime_eq_zero_of_goal P hn C₀ Goal hGoal]
    exact zero_le
  · have hbound :=
      expectedHittingTime_le_window_mul_tsum_pow_of_not_goal_of_invariant
        P hn C₀ Goal Inv K p hGoal hInv₀ hInvStep hwin
    calc
      expectedHittingTime P hn C₀ Goal
          ≤ (K : ENNReal) * ∑' r : ℕ, (1 - p) ^ r := hbound
      _ = (K : ENNReal) * (1 - (1 - p))⁻¹ := by
            rw [ENNReal.tsum_geometric]
      _ = (K : ENNReal) * p⁻¹ := by
            rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hp_le_one]

/-- If `Inv` is preserved until the first time `Goal` is hit, then every
false-flag state in the hit-flag chain still satisfies `Inv`.  Unlike
`hitFlagDist_support_inv`, this does not require `Inv` to hold after a goal
state has been reached. -/
private theorem hitFlagDist_support_false_inv_until_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j)) :
    ∀ t : ℕ, ∀ C : Config Q X n,
      (C, false) ∈ (hitFlagDist P hn C₀ Goal t).support → Inv C
  | 0, C => by
      classical
      intro hmem
      rw [hitFlagDist, PMF.support_pure] at hmem
      have hC : C = C₀ := by
        simpa using congrArg Prod.fst hmem
      exact hC.symm ▸ hInv₀
  | t + 1, C => by
      classical
      intro hmem
      rw [hitFlagDist, PMF.mem_support_bind_iff] at hmem
      obtain ⟨S, hS, hstep⟩ := hmem
      rcases S with ⟨D, b⟩
      rw [hitFlagStepDist, PMF.support_map] at hstep
      obtain ⟨E, hE, hEq⟩ := hstep
      have hCE : C = E := by
        simpa using (congrArg Prod.fst hEq).symm
      subst C
      cases b
      · have hnotGoalE : ¬ Goal E := by
          intro hGoalE
          have hfalse := congrArg Prod.snd hEq
          simp [hGoalE] at hfalse
        have hInvD :
            Inv D :=
          hitFlagDist_support_false_inv_until_goal
            P hn C₀ Goal Inv hInv₀ hInvStep t D hS
        have hnotGoalD : ¬ Goal D := by
          intro hGoalD
          have hzero :=
            hitFlagDist_apply_false_of_goal P hn C₀ D Goal hGoalD t
          rw [PMF.mem_support_iff] at hS
          exact hS hzero
        rw [stepDist, PMF.support_map] at hE
        obtain ⟨pair, _hpair_mem, hpair_eq⟩ := hE
        rw [← hpair_eq]
        rcases hInvStep D hInvD hnotGoalD pair.1 pair.2 with hInv' | hGoal'
        · exact hInv'
        · exact False.elim (hnotGoalE (by simpa [hpair_eq] using hGoal'))
      · have hfalse := congrArg Prod.snd hEq
        simp at hfalse

/-- One-step local geometric contraction where the invariant only needs to be
preserved until the goal is first hit. -/
theorem probNotHitBy_succ_le_mul_until_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (p : ENNReal)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j))
    (hwin : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal 1)
    (t : ℕ) :
    probNotHitBy P hn C₀ Goal (t + 1) ≤
      probNotHitBy P hn C₀ Goal t * (1 - p) := by
  classical
  rw [probNotHitBy_succ_eq_tsum]
  calc
    (∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (hitFlagStepDist P hn Goal S).toOuterMeasure
            {T : Config Q X n × Bool | T.2 = false})
        ≤
      ∑' S : Config Q X n × Bool,
        hitFlagDist P hn C₀ Goal t S *
          (if S.2 = false then 1 - p else 0) := by
        apply ENNReal.tsum_le_tsum
        intro S
        rcases S with ⟨C, b⟩
        cases b
        · by_cases hGoalC : Goal C
          · have hzero :
                hitFlagDist P hn C₀ Goal t (C, false) = 0 :=
              hitFlagDist_apply_false_of_goal P hn C₀ C Goal hGoalC t
            rw [hzero]
            simp
          · by_cases hmem : (C, false) ∈ (hitFlagDist P hn C₀ Goal t).support
            · have hInvC :
                  Inv C :=
                hitFlagDist_support_false_inv_until_goal
                  P hn C₀ Goal Inv hInv₀ hInvStep t C hmem
              have hblock :
                  (hitFlagStepDist P hn Goal (C, false)).toOuterMeasure
                      {T : Config Q X n × Bool | T.2 = false} ≤ 1 - p := by
                rw [hitFlagStepDist_false_toOuterMeasure_false]
                exact step_miss_le_one_sub_of_ProbHitWithin_one_lower_bound
                  P hn C Goal p hGoalC (hwin C hInvC hGoalC)
              have hmul := mul_le_mul_right hblock
                (hitFlagDist P hn C₀ Goal t (C, false))
              simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
            · rw [PMF.mem_support_iff] at hmem
              have hzero : hitFlagDist P hn C₀ Goal t (C, false) = 0 :=
                not_not.mp hmem
              rw [hzero]
              simp
        · rw [hitFlagStepDist_true_toOuterMeasure_false]
          simp
    _ =
      (∑' S : Config Q X n × Bool,
        (if S.2 = false then hitFlagDist P hn C₀ Goal t S else 0)) *
          (1 - p) := by
        rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro S
        by_cases hS : S.2 = false <;> simp [hS, mul_comm]
    _ = probNotHitBy P hn C₀ Goal t * (1 - p) := by
        rw [probNotHitBy]

/-- Expected-time form of `probNotHitBy_succ_le_mul_until_goal`.  This is the
local one-step analogue of `expectedHittingTime_le_window_mul_inv_of_invariant`
when the invariant is only maintained until the target is first hit. -/
theorem expectedHittingTime_le_inv_of_local_one_lower_bound_until_goal
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (p : ENNReal)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j))
    (hwin : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal 1) :
    expectedHittingTime P hn C₀ Goal ≤ p⁻¹ := by
  by_cases hGoal : Goal C₀
  · rw [expectedHittingTime_eq_zero_of_goal P hn C₀ Goal hGoal]
    exact zero_le
  · have hhit_le_one : ProbHitWithin P hn C₀ Goal 1 ≤ 1 := by
      calc
        ProbHitWithin P hn C₀ Goal 1
            ≤ ProbHitWithin P hn C₀ Goal 1 +
              probNotHitBy P hn C₀ Goal 1 := by
                exact le_self_add
        _ = 1 := probHitBy_add_probNotHitBy P hn C₀ Goal 1
    have hp_le_one : p ≤ 1 :=
      (hwin C₀ hInv₀ hGoal).trans hhit_le_one
    have htail : ∀ t : ℕ,
        probNotHitBy P hn C₀ Goal t ≤ (1 - p) ^ t := by
      intro t
      have hraw : probNotHitBy P hn C₀ Goal t ≤
          probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ t := by
        induction t with
        | zero => simp
        | succ t ih =>
            have hstep :=
              probNotHitBy_succ_le_mul_until_goal
                P hn C₀ Goal Inv p hInv₀ hInvStep hwin t
            calc
              probNotHitBy P hn C₀ Goal (t + 1)
                  ≤ probNotHitBy P hn C₀ Goal t * (1 - p) := hstep
              _ ≤ (probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ t) *
                    (1 - p) := by
                    exact mul_le_mul_left ih _
              _ = probNotHitBy P hn C₀ Goal 0 * (1 - p) ^ (t + 1) := by
                    rw [pow_succ, mul_assoc]
      simpa [probNotHitBy_zero_of_not_goal P hn C₀ Goal hGoal] using hraw
    calc
      expectedHittingTime P hn C₀ Goal
          ≤ ∑' t : ℕ, (1 - p) ^ t :=
            expectedHittingTime_le_of_tail_bound P hn C₀ Goal
              (fun t => (1 - p) ^ t) htail
      _ = (1 - (1 - p))⁻¹ := by rw [ENNReal.tsum_geometric]
      _ = p⁻¹ := by
            rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hp_le_one]

/-- Expected hitting time from a non-increasing potential with a uniform
one-step chance to strictly decrease.  The non-increase hypothesis is essential:
without it, failed descent attempts can move the chain to larger potential
levels, and the bound by the initial potential is false. -/
theorem expectedHittingTime_le_of_potential_descent
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (φ : Config Q X n → ℕ)
    (p : ENNReal)
    (_hGoal : φ C₀ ≠ 0)
    (hNonincrease : ∀ C : Config Q X n,
      ∀ i j : Fin n, φ (C.step P i j) ≤ φ C)
    (hp : ∀ C : Config Q X n, φ C ≠ 0 →
      p ≤ ProbHitWithin P hn C (fun D => φ D < φ C) 1) :
    expectedHittingTime P hn C₀ (fun D => φ D = 0) ≤ ↑(φ C₀) * p⁻¹ := by
  classical
  let Zero : Config Q X n → Prop := fun D => φ D = 0
  have hAll : ∀ m : ℕ, ∀ C : Config Q X n, φ C = m →
      expectedHittingTime P hn C Zero ≤ (m : ENNReal) * p⁻¹ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro C hφ
        by_cases hm0 : m = 0
        · have hZeroC : Zero C := by
            dsimp [Zero]
            rw [hφ, hm0]
          rw [expectedHittingTime_eq_zero_of_goal P hn C Zero hZeroC]
          exact zero_le
        · let Mid : Config Q X n → Prop := fun D => φ D < m
          let Inv : Config Q X n → Prop := fun D => φ D ≤ m
          have hCpos : φ C ≠ 0 := by
            rw [hφ]
            exact hm0
          have hMidC : ¬ Mid C := by
            dsimp [Mid]
            rw [hφ]
            exact Nat.lt_irrefl m
          have hp_le_one : p ≤ 1 := by
            have hhit_le_one : ProbHitWithin P hn C Mid 1 ≤ 1 := by
              calc
                ProbHitWithin P hn C Mid 1
                    ≤ ProbHitWithin P hn C Mid 1 +
                      probNotHitBy P hn C Mid 1 := by
                        exact le_self_add
                _ = 1 := probHitBy_add_probNotHitBy P hn C Mid 1
            have hpC : p ≤ ProbHitWithin P hn C Mid 1 := by
              simpa [Mid, hφ] using hp C hCpos
            exact hpC.trans hhit_le_one
          have hInv₀ : Inv C := by
            dsimp [Inv]
            rw [hφ]
          have hInvStep : ∀ D : Config Q X n, Inv D →
              ∀ i j : Fin n, Inv (D.step P i j) := by
            intro D hInvD i j
            dsimp [Inv] at hInvD ⊢
            exact (hNonincrease D i j).trans hInvD
          have hwin : ∀ D : Config Q X n, Inv D → ¬ Mid D →
              p ≤ ProbHitWithin P hn D Mid 1 := by
            intro D hInvD hNotMidD
            have hDge : m ≤ φ D := le_of_not_gt hNotMidD
            have hDφ : φ D = m := le_antisymm hInvD hDge
            have hDpos : φ D ≠ 0 := by
              rw [hDφ]
              exact hm0
            simpa [Mid, hDφ] using hp D hDpos
          have hToMid : expectedHittingTime P hn C Mid ≤ p⁻¹ := by
            have hbound :=
              expectedHittingTime_le_window_mul_inv_of_invariant
                P hn C Mid Inv 1 p hp_le_one hInv₀ hInvStep hwin
            simpa using hbound
          have hBelow : ∀ D : Config Q X n, Mid D →
              expectedHittingTime P hn D Zero ≤
                ((m - 1 : ℕ) : ENNReal) * p⁻¹ := by
            intro D hDmid
            have hDrec :
                expectedHittingTime P hn D Zero ≤
                  (φ D : ENNReal) * p⁻¹ :=
              ih (φ D) hDmid D rfl
            have hDle_pred : φ D ≤ m - 1 := by
              omega
            have hcast : (φ D : ENNReal) ≤ ((m - 1 : ℕ) : ENNReal) := by
              exact_mod_cast hDle_pred
            exact hDrec.trans (mul_le_mul_left hcast p⁻¹)
          have hcomp :
              expectedHittingTime P hn C Zero ≤
                p⁻¹ + ((m - 1 : ℕ) : ENNReal) * p⁻¹ :=
            expectedHittingTime_add_le P hn C Mid Zero
              p⁻¹ (((m - 1 : ℕ) : ENNReal) * p⁻¹)
              hToMid hBelow (by
                intro D hZeroD
                dsimp [Mid, Zero] at hZeroD ⊢
                rw [hZeroD]
                exact Nat.pos_of_ne_zero hm0)
          calc
            expectedHittingTime P hn C Zero
                ≤ p⁻¹ + ((m - 1 : ℕ) : ENNReal) * p⁻¹ := hcomp
            _ = (m : ENNReal) * p⁻¹ := by
              have hm_succ : m = (m - 1) + 1 := by
                omega
              rw [hm_succ]
              norm_num
              rw [add_mul, one_mul, add_comm]
  simpa [Zero] using hAll (φ C₀) C₀ rfl

/-- Variable-rate potential descent: if at level `k`, one-step descent
probability is at least `pRate k`, and the potential is non-increasing, then
the expected hitting time of level zero is bounded by the sum of the geometric
waiting-time bounds for the levels below the start.

For the swap phase with quadratic good-pairs, `pRate k = k²/(n(n-1))`, so the
finite sum is controlled by `Σ 1/k²`, not the harmonic `Σ 1/k`. -/
theorem expectedHittingTime_le_of_variable_descent
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (φ : Config Q X n → ℕ)
    (pRate : ℕ → ENNReal)
    (hNonincrease : ∀ C : Config Q X n,
      ∀ i j : Fin n, φ (C.step P i j) ≤ φ C)
    (hp : ∀ k : ℕ, 0 < k → ∀ C : Config Q X n, φ C = k →
      pRate k ≤ ProbHitWithin P hn C (fun D => φ D < k) 1)
    (_hGoal : φ C₀ ≠ 0) :
    expectedHittingTime P hn C₀ (fun D => φ D = 0) ≤
      ∑ k ∈ Finset.range (φ C₀), (pRate (k + 1))⁻¹ := by
  classical
  let Zero : Config Q X n → Prop := fun D => φ D = 0
  let B : ℕ → ENNReal := fun m =>
    ∑ k ∈ Finset.range m, (pRate (k + 1))⁻¹
  have hAll : ∀ m : ℕ, ∀ C : Config Q X n, φ C = m →
      expectedHittingTime P hn C Zero ≤ B m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro C hφ
        by_cases hm0 : m = 0
        · have hZeroC : Zero C := by
            dsimp [Zero]
            rw [hφ, hm0]
          rw [expectedHittingTime_eq_zero_of_goal P hn C Zero hZeroC]
          exact zero_le
        · let Mid : Config Q X n → Prop := fun D => φ D < m
          let Inv : Config Q X n → Prop := fun D => φ D ≤ m
          have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          have hMidC : ¬ Mid C := by
            dsimp [Mid]
            rw [hφ]
            exact Nat.lt_irrefl m
          have hp_le_one : pRate m ≤ 1 := by
            have hhit_le_one : ProbHitWithin P hn C Mid 1 ≤ 1 := by
              calc
                ProbHitWithin P hn C Mid 1
                    ≤ ProbHitWithin P hn C Mid 1 +
                      probNotHitBy P hn C Mid 1 := by
                        exact le_self_add
                _ = 1 := probHitBy_add_probNotHitBy P hn C Mid 1
            have hpC : pRate m ≤ ProbHitWithin P hn C Mid 1 := by
              simpa [Mid, hφ] using hp m hmpos C hφ
            exact hpC.trans hhit_le_one
          have hInv₀ : Inv C := by
            dsimp [Inv]
            rw [hφ]
          have hInvStep : ∀ D : Config Q X n, Inv D →
              ∀ i j : Fin n, Inv (D.step P i j) := by
            intro D hInvD i j
            dsimp [Inv] at hInvD ⊢
            exact (hNonincrease D i j).trans hInvD
          have hwin : ∀ D : Config Q X n, Inv D → ¬ Mid D →
              pRate m ≤ ProbHitWithin P hn D Mid 1 := by
            intro D hInvD hNotMidD
            have hDge : m ≤ φ D := le_of_not_gt hNotMidD
            have hDφ : φ D = m := le_antisymm hInvD hDge
            simpa [Mid, hDφ] using hp m hmpos D hDφ
          have hToMid : expectedHittingTime P hn C Mid ≤ (pRate m)⁻¹ := by
            have hbound :=
              expectedHittingTime_le_window_mul_inv_of_invariant
                P hn C Mid Inv 1 (pRate m) hp_le_one
                hInv₀ hInvStep hwin
            simpa using hbound
          have hBelow : ∀ D : Config Q X n, Mid D →
              expectedHittingTime P hn D Zero ≤ B (m - 1) := by
            intro D hDmid
            have hDrec :
                expectedHittingTime P hn D Zero ≤ B (φ D) :=
              ih (φ D) hDmid D rfl
            have hDle_pred : φ D ≤ m - 1 := by
              omega
            have hsubset :
                Finset.range (φ D) ⊆ Finset.range (m - 1) := by
              intro x hx
              rw [Finset.mem_range] at hx ⊢
              omega
            have hBmono : B (φ D) ≤ B (m - 1) := by
              dsimp [B]
              exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
                (by
                  intro x _hxSmall _hxLarge
                  exact zero_le)
            exact hDrec.trans hBmono
          have hcomp :
              expectedHittingTime P hn C Zero ≤
                (pRate m)⁻¹ + B (m - 1) :=
            expectedHittingTime_add_le P hn C Mid Zero
              (pRate m)⁻¹ (B (m - 1))
              hToMid hBelow (by
                intro D hZeroD
                dsimp [Mid, Zero] at hZeroD ⊢
                rw [hZeroD]
                exact hmpos)
          calc
            expectedHittingTime P hn C Zero
                ≤ (pRate m)⁻¹ + B (m - 1) := hcomp
            _ = B m := by
              have hm_succ : m = (m - 1) + 1 := by omega
              dsimp [B]
              rw [hm_succ, Finset.sum_range_succ]
              rw [Nat.sub_add_cancel hmpos]
              rw [add_comm]
  simpa [Zero, B] using hAll (φ C₀) C₀ rfl

/-- Variable-rate potential descent where an invariant only has to hold until
the target is first reached.  At level `k`, the one-step progress event may
either hit `Goal` immediately or stay inside `Inv` and move to a lower level.

This is the local form needed for phase analyses where leaving the phase region
is itself treated as a target event. -/
theorem expectedHittingTime_le_of_variable_descent_until_goal
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Goal Inv : Config Q X n → Prop)
    [DecidablePred Goal] [DecidablePred Inv]
    (φ : Config Q X n → ℕ)
    (pRate : ℕ → ENNReal)
    (hInv₀ : Inv C₀)
    (hZeroGoal : ∀ C : Config Q X n, Inv C → φ C = 0 → Goal C)
    (hInvStep : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j))
    (hNonincrease : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      ∀ i j : Fin n, φ (C.step P i j) ≤ φ C)
    (hp : ∀ k : ℕ, 0 < k → ∀ C : Config Q X n, Inv C → φ C = k →
      pRate k ≤
        ProbHitWithin P hn C
          (fun D => Goal D ∨ (Inv D ∧ φ D < k)) 1) :
    expectedHittingTime P hn C₀ Goal ≤
      ∑ k ∈ Finset.range (φ C₀), (pRate (k + 1))⁻¹ := by
  classical
  let B : ℕ → ENNReal := fun m =>
    ∑ k ∈ Finset.range m, (pRate (k + 1))⁻¹
  have hAll : ∀ m : ℕ, ∀ C : Config Q X n, Inv C → φ C = m →
      expectedHittingTime P hn C Goal ≤ B m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro C hInvC hφ
        by_cases hGoalC : Goal C
        · rw [expectedHittingTime_eq_zero_of_goal P hn C Goal hGoalC]
          exact zero_le
        · by_cases hm0 : m = 0
          · have hGoal0 : Goal C := hZeroGoal C hInvC (by rw [hφ, hm0])
            exact False.elim (hGoalC hGoal0)
          · let Mid : Config Q X n → Prop :=
              fun D => Goal D ∨ (Inv D ∧ φ D < m)
            let InvLevel : Config Q X n → Prop := fun D => Inv D ∧ φ D ≤ m
            have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
            have hp_le_one : pRate m ≤ 1 := by
              have hhit_le_one : ProbHitWithin P hn C Mid 1 ≤ 1 := by
                calc
                  ProbHitWithin P hn C Mid 1
                      ≤ ProbHitWithin P hn C Mid 1 +
                        probNotHitBy P hn C Mid 1 := by
                          exact le_self_add
                  _ = 1 := probHitBy_add_probNotHitBy P hn C Mid 1
              have hpC : pRate m ≤ ProbHitWithin P hn C Mid 1 := by
                simpa [Mid, hφ] using hp m hmpos C hInvC hφ
              exact hpC.trans hhit_le_one
            have hInvLevel₀ : InvLevel C := by
              exact ⟨hInvC, by rw [hφ]⟩
            have hInvLevelStep : ∀ D : Config Q X n, InvLevel D → ¬ Mid D →
                ∀ i j : Fin n, InvLevel (D.step P i j) ∨ Mid (D.step P i j) := by
              intro D hInvD hNotMidD i j
              have hNotGoalD : ¬ Goal D := by
                intro hD
                exact hNotMidD (Or.inl hD)
              rcases hInvStep D hInvD.1 hNotGoalD i j with hInv' | hGoal'
              · have hφ' : φ (D.step P i j) ≤ m :=
                  (hNonincrease D hInvD.1 hNotGoalD i j).trans hInvD.2
                exact Or.inl ⟨hInv', hφ'⟩
              · exact Or.inr (Or.inl hGoal')
            have hwin : ∀ D : Config Q X n, InvLevel D → ¬ Mid D →
                pRate m ≤ ProbHitWithin P hn D Mid 1 := by
              intro D hInvD hNotMidD
              have hDge : m ≤ φ D := by
                by_contra hlt_not
                have hlt : φ D < m := by omega
                exact hNotMidD (Or.inr ⟨hInvD.1, hlt⟩)
              have hDφ : φ D = m := le_antisymm hInvD.2 hDge
              simpa [Mid, hDφ] using hp m hmpos D hInvD.1 hDφ
            have hToMid : expectedHittingTime P hn C Mid ≤ (pRate m)⁻¹ := by
              exact expectedHittingTime_le_inv_of_local_one_lower_bound_until_goal
                P hn C Mid InvLevel (pRate m) hInvLevel₀ hInvLevelStep hwin
            have hBelow : ∀ D : Config Q X n, Mid D →
                expectedHittingTime P hn D Goal ≤ B (m - 1) := by
              intro D hDmid
              rcases hDmid with hGoalD | hLower
              · rw [expectedHittingTime_eq_zero_of_goal P hn D Goal hGoalD]
                exact zero_le
              · have hDrec :
                    expectedHittingTime P hn D Goal ≤ B (φ D) :=
                  ih (φ D) hLower.2 D hLower.1 rfl
                have hDle_pred : φ D ≤ m - 1 := by omega
                have hsubset :
                    Finset.range (φ D) ⊆ Finset.range (m - 1) := by
                  intro x hx
                  rw [Finset.mem_range] at hx ⊢
                  omega
                have hBmono : B (φ D) ≤ B (m - 1) := by
                  dsimp [B]
                  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
                    (by
                      intro x _hxSmall _hxLarge
                      exact zero_le)
                exact hDrec.trans hBmono
            have hcomp :
                expectedHittingTime P hn C Goal ≤
                  (pRate m)⁻¹ + B (m - 1) :=
              expectedHittingTime_add_le P hn C Mid Goal
                (pRate m)⁻¹ (B (m - 1))
                hToMid hBelow (by
                  intro D hGoalD
                  exact Or.inl hGoalD)
            calc
              expectedHittingTime P hn C Goal
                  ≤ (pRate m)⁻¹ + B (m - 1) := hcomp
              _ = B m := by
                have hm_succ : m = (m - 1) + 1 := by omega
                dsimp [B]
                rw [hm_succ, Finset.sum_range_succ]
                rw [Nat.sub_add_cancel hmpos]
                rw [add_comm]
  simpa [B] using hAll (φ C₀) C₀ hInv₀ rfl

/-- Parallel-time form of `expectedHittingTime_le_window_mul_inv_of_invariant`. -/
theorem expectedParallelTime_le_window_mul_inv_of_invariant
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (K : ℕ) [NeZero K] (p : ENNReal)
    (hp_le_one : p ≤ 1)
    (hInv₀ : Inv C₀)
    (hInvStep : ∀ C : Config Q X n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j))
    (hwin : ∀ C : Config Q X n, Inv C → ¬ Goal C →
      p ≤ ProbHitWithin P hn C Goal K) :
    expectedParallelTime P hn C₀ Goal ≤ ((K : ENNReal) * p⁻¹) / n :=
  expectedParallelTime_le_of_expectedHittingTime_le P hn C₀ Goal
    (expectedHittingTime_le_window_mul_inv_of_invariant P hn C₀ Goal Inv
      K p hp_le_one hInv₀ hInvStep hwin)

/-- Tail comparison packaged directly as a parallel-time bound. -/
theorem expectedParallelTime_le_of_tail_bound
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (f : ℕ → ENNReal)
    (hf : ∀ t, probNotHitBy P hn C₀ Goal t ≤ f t) :
    expectedParallelTime P hn C₀ Goal ≤ (∑' t : ℕ, f t) / n := by
  exact expectedParallelTime_le_of_expectedHittingTime_le P hn C₀ Goal
    (expectedHittingTime_le_of_tail_bound P hn C₀ Goal f hf)

/-- Expected parallel time to reach an output-stable/safe configuration.
This is the generic stabilization-time objective in Kanaya §2. -/
noncomputable def expectedParallelTimeToOutputStable
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) : ENNReal :=
  expectedParallelTime P hn C₀ (fun C => C.isOutputStable P)

/-- Expected parallel time to reach a silent configuration.  This is the
silence-time objective used for silent protocols. -/
noncomputable def expectedParallelTimeToSilent
    [DecidableEq Q] [DecidableEq X]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) : ENNReal :=
  expectedParallelTime P hn C₀ (fun C => C.isSilent P)

/-- Expected parallel time to reach the consensus predicate.
Specialised to `Q = AgentState n` (the protocol's actual state type),
because `IsConsensusConfig` is defined on that. -/
noncomputable def expectedParallelTimeToConsensus
    (P : Protocol (AgentState n) Opinion Output) (hn : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n) : ENNReal :=
  expectedParallelTime P hn C₀ IsConsensusConfig

/-! ### Bridge: deterministic reachability → probabilistic expected time

If `reach_zero_potential` provides a deterministic descent pair for every
non-zero potential level, the uniform random scheduler hits that pair with
probability ≥ 1/(n(n-1)). This gives E[T] ≤ φ₀ · n(n-1). -/

theorem expectedHittingTime_le_of_deterministic_descent
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (Goal Inv : Config Q X n → Prop)
    [DecidablePred Goal] [DecidablePred Inv]
    (φ : Config Q X n → ℕ)
    (hInv₀ : Inv C₀)
    (hZeroGoal : ∀ C, Inv C → φ C = 0 → Goal C)
    (hInvStep : ∀ C, Inv C → ¬ Goal C →
      ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j))
    (hNonincrease : ∀ C, Inv C → ¬ Goal C →
      ∀ i j : Fin n, φ (C.step P i j) ≤ φ C)
    (hDescent : ∀ C, Inv C → ¬ Goal C → 0 < φ C →
      ∃ u v : Fin n, u ≠ v ∧
        ((Inv (C.step P u v) ∧ φ (C.step P u v) < φ C) ∨
          Goal (C.step P u v))) :
    expectedHittingTime P hn C₀ Goal ≤
      ↑(φ C₀) * ((n * (n - 1) : ℕ) : ENNReal) := by
  classical
  let pUnif : ENNReal := ((n * (n - 1) : ℕ) : ENNReal)⁻¹
  have hpStep : ∀ k : ℕ, 0 < k → ∀ C : Config Q X n, Inv C → φ C = k →
      pUnif ≤ ProbHitWithin P hn C
        (fun D => Goal D ∨ (Inv D ∧ φ D < k)) 1 := by
    intro k hk C hInvC hφ
    by_cases hGoalC : Goal C
    · have h1 : ProbHitWithin P hn C (fun D => Goal D ∨ (Inv D ∧ φ D < k)) 0 = 1 :=
        probHitBy_zero_of_goal P hn C _ (Or.inl hGoalC)
      calc pUnif ≤ 1 := by
              simp only [pUnif]
              exact ENNReal.inv_le_one.mpr (by
                norm_cast
                have : 1 ≤ n := by omega
                have : 1 ≤ n - 1 := by omega
                exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
        _ = ProbHitWithin P hn C (fun D => Goal D ∨ (Inv D ∧ φ D < k)) 0 := h1.symm
        _ ≤ ProbHitWithin P hn C (fun D => Goal D ∨ (Inv D ∧ φ D < k)) 1 :=
              ProbHitWithin_le_succ P hn C _ 0
    · obtain ⟨u, v, huv, hprog⟩ := hDescent C hInvC hGoalC (by omega)
      have hTarget : (fun D => Goal D ∨ (Inv D ∧ φ D < k)) (C.step P u v) := by
        rcases hprog with ⟨hI, hlt⟩ | hG
        · exact Or.inr ⟨hI, by rwa [hφ] at hlt⟩
        · exact Or.inl hG
      have hNotGoalOr : ¬ (fun D => Goal D ∨ (Inv D ∧ φ D < k)) C := by
        intro h; rcases h with hG | ⟨_, hlt⟩
        · exact hGoalC hG
        · rw [hφ] at hlt; omega
      exact ProbHitWithin_one_lower_bound_of_step P hn C _ hNotGoalOr huv hTarget
  have hBound := expectedHittingTime_le_of_variable_descent_until_goal
    P hn C₀ Goal Inv φ (fun _ => pUnif)
    hInv₀ hZeroGoal hInvStep hNonincrease hpStep
  calc expectedHittingTime P hn C₀ Goal
      ≤ ∑ _k ∈ Finset.range (φ C₀), pUnif⁻¹ := hBound
    _ = ↑(φ C₀) * ((n * (n - 1) : ℕ) : ENNReal) := by
        simp only [pUnif, inv_inv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-! ### Bridging lemma: deterministic schedule to probabilistic bound.

If a deterministic schedule of length t with distinct pairs reaches
Goal, then probReached t C Goal >= (1/(n(n-1)))^t. Combined with
expectedHittingTime_le_window_mul_inv this converts deterministic
convergence proofs into expected-time bounds. -/

/-- Lower bound on probReached from a deterministic schedule with distinct
pairs reaching Goal. -/
theorem probReached_ge_inv_pow_of_execution
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal]
    (γ : DetScheduler n) (t : ℕ)
    (hDistinct : ∀ k, k < t → (γ k).1 ≠ (γ k).2)
    (hGoal : Goal (execution P C γ t)) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ t ≤
      probReached P hn C Goal t := by
  induction t generalizing C γ with
  | zero =>
    simp only [pow_zero]
    exact le_of_eq (probReached_zero_of_goal P hn C Goal hGoal).symm
  | succ t ih =>
    set C' := C.step P (γ 0).1 (γ 0).2
    have hDistinct0 : (γ 0).1 ≠ (γ 0).2 := hDistinct 0 (by omega)
    set γ' : DetScheduler n := fun k => γ (k + 1)
    have hExec : ∀ s, execution P C' γ' s = execution P C γ (s + 1) := by
      intro s; induction s with
      | zero => simp [execution, C']
      | succ s ih' =>
        simp only [execution, γ'] at ih' ⊢
        rw [ih']
    have hGoal' : Goal (execution P C' γ' t) := by
      rw [hExec]; exact hGoal
    have hDistinct' : ∀ k, k < t → (γ' k).1 ≠ (γ' k).2 := by
      intro k hk; exact hDistinct (k + 1) (by omega)
    have hIH : ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ t ≤
        probReached P hn C' Goal t :=
      ih C' γ' hDistinct' hGoal'
    have hStep : ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        probReached P hn C (fun D => D = C') 1 :=
      probReached_one_lower_bound_of_step P hn C (fun D => D = C')
        hDistinct0 rfl
    have hTarget : ∀ D : Config Q X n, D = C' →
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ t ≤
          probReached P hn D Goal t := by
      intro D hD; subst hD; exact hIH
    have hComp := probReached_add_ge_mul P hn C (fun D => D = C') Goal
      1 t
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹)
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ t)
      hStep hTarget
    calc ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ (t + 1)
        = ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ t *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := pow_succ _ t
      _ = ((n * (n - 1) : ℕ) : ENNReal)⁻¹ *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ t := mul_comm _ _
      _ ≤ probReached P hn C Goal (1 + t) := hComp
      _ = probReached P hn C Goal (t + 1) := by ring_nf
/-- ProbHitWithin version of the schedule bridging lemma. -/
theorem ProbHitWithin_ge_inv_pow_of_execution
    [DecidableEq (Config Q X n)]
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C : Config Q X n) (Goal : Config Q X n → Prop)
    [DecidablePred Goal]
    (γ : DetScheduler n) (t : ℕ)
    (hDistinct : ∀ k, k < t → (γ k).1 ≠ (γ k).2)
    (hGoal : Goal (execution P C γ t)) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ^ t ≤
      ProbHitWithin P hn C Goal t :=
  (probReached_ge_inv_pow_of_execution P hn C Goal γ t hDistinct hGoal).trans
    (probReached_le_ProbHitWithin P hn C Goal t)


end Probability
end SSEM
