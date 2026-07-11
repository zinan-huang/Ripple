/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-1 averaging DRAIN RATE — discharging the carried second-moment `q` atom (residual #5)

`AveragingCollapse.lean` carries exactly one quantitative input: the per-level second-moment
drain rate `q : ℕ → ℝ≥0∞` consumed by `secondMoment_level_tail` / `phase1_pullPos_floor_whp` as

```
hdrop : ∀ m, ∀ b, Phase1AllMain n b → secondMomentN b = m →
  K b (potBelow secondMomentN m)ᶜ ≤ q m
```

i.e. while the Phase-1 second moment `Φ = secondMomentN ≥ m`, one interaction fails to strictly
drop it with probability `≤ q m`.  This file derives that rate HONESTLY from the FROZEN `avgFin7`
rule — no `[45]` import — by the same rectangle pair-counting the landed `extremeU` chain uses
(`DrainThreading.phase1_hdrop_of_struct` / `Phase7Convergence.drop_prob_of_rect`).

## The honesty trap and how the second moment escapes it

The per-rule ledger (`AveragingCollapse.avgFin7_sqDist3_pair_drop`) gives a strict drop ONLY for a
**gap-≥2** pair (`drop = ⌊(x−y)²/2⌋`, which is `0` for `|x−y| ≤ 1`).  So a config whose Mains all
sit in a width-1 window `{a, a+1}` STALLS with zero drop — and if that window is `{0,1}` or
`{5,6}`, the second moment is as large as `9·|M|` despite being unbeatable per-step.  A naive
"`secondMomentN ≥ θ ⟹ gap-2 pair`" is therefore FALSE.

The genuine escape is the **window `{2,3,4}` second-moment ceiling**, which the encoding origin `3`
makes exact and `decide`-checkable: a Main with `smallBias.val ∈ {2,3,4}` is at squared distance
`≤ 1` from `3`.  Hence if NO Main is "far" (`val ≤ 1` or `val ≥ 5`), every Main is in `{2,3,4}` and
`secondMomentN ≤ |M| = n`.  Contrapositive (the structure lemma): `secondMomentN c > n` forces a
**far** Main to exist (`farLow`: `val ≤ 1`, or `farHigh`: `val ≥ 5`) — and every far Main has a
gap-≥2 partner on the centre side, giving a strict-drop rectangle.

The `{0,1}`/`{5,6}` stall windows are excluded not by this ceiling but by the **sum invariant**:
the centred Main bias sum `S₀(c) = Σ_{Mains}(smallBias.val − 3)` is conserved by `avgFin7`
(Stage 1, lifting `avgFin7_preserves_sum`); at the Doty Phase-1 entry each Main encodes a `±1`
opinion so `|S₀| ≤ |M| = n`; a `{0,1}`-window config has `S₀ ≤ (1−3)·|M| = −2|M|`, contradicting
`|S₀| ≤ n`.  So the conserved sum pins the stall windows out of reach, and the `{2,3,4}` ceiling is
the per-step mechanism that converts "`Φ` large" into "a strict-drop rectangle exists".

## What this file delivers

* **Stage 1** — the sum-invariant entry fact: `centredBiasSum` is `avgFin7`-conserved
  (`centredBiasSum_kernel_invariant`), and the honest entry predicate `SumPinned n c`
  (`|S₀| ≤ n`) is `K`-closed on the window (`invClosed_sumPinned`).
* **Stage 2** — the structure lemma: `secondMomentN c > n ⟹ a far Main exists`
  (`farExists_of_secondMoment_gt_n`), via the exact `{2,3,4}` ceiling `sqDist3N ≤ 1`
  (`secondMomentN_le_card_of_no_far`).
* **Stage 3** — the rate: the far-Main × centre-partner strict-drop rectangles thread through
  `drop_prob_of_rect`, giving `secondMomentN_drop_prob_rect` and the per-level `hdrop`
  `secondMomentN_hdrop_of_struct` at rate `q m = 1 − P/(n(n−1))`.
* **Stage 4** — the hypothesis-free wiring `phase1_pullPos_floor_whp_of_struct`: feeds the derived
  `q` into `AveragingCollapse.phase1_pullPos_floor_whp`, with the honest time budget documented.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AveragingCollapse

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AveragingRate

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Stage 1 — the sum invariant (the conserved centred Main bias sum).

`S₀(c) = Σ_{Mains}(smallBias.val − 3)` is the centred bias sum (an `ℤ`).  Averaging preserves it
(`avgFin7_preserves_sum`), so it is a kernel invariant; the Doty Phase-1 entry has `|S₀| ≤ |M| = n`
(each Main encodes a `±1` opinion), pinning the `{0,1}`/`{5,6}` stall windows out of reach. -/

/-- Per-agent centred bias `(smallBias.val − 3 : ℤ)` on a Main, else `0`. -/
def biasZ (a : AgentState L K) : ℤ :=
  if a.role = Role.main then (a.smallBias.val : ℤ) - 3 else 0

/-- The centred Main bias sum `S₀(c) = Σ_{Mains}(smallBias.val − 3)`. -/
def centredBiasSum (c : Config (AgentState L K)) : ℤ :=
  (c.map (fun a => biasZ a)).sum

/-- `biasZ` over a two-element pair as a sum. -/
theorem biasZ_pair (x y : AgentState L K) :
    ((({x, y} : Multiset (AgentState L K)).map (fun a => biasZ a)).sum)
      = biasZ x + biasZ y := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  simp [Multiset.map_cons, Multiset.sum_cons]

/-- **Per-pair `centredBiasSum` conservation, both-Main.**  Reduce to `avgFin7` and apply the
preserved-sum identity. -/
theorem Transition_centredBiasSum_pair_eq_of_both_main (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K))).map (fun a => biasZ a)).sum
      = ((({s, t} : Multiset (AgentState L K)).map (fun a => biasZ a)).sum) := by
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [biasZ_pair, biasZ_pair]
  have ho1 : biasZ ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1} : AgentState L K)
      = ((avgFin7 s.smallBias t.smallBias).1.val : ℤ) - 3 := by
    unfold biasZ; rw [if_pos hsM]
  have ho2 : biasZ ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2} : AgentState L K)
      = ((avgFin7 s.smallBias t.smallBias).2.val : ℤ) - 3 := by
    unfold biasZ; rw [if_pos htM]
  have hs : biasZ s = (s.smallBias.val : ℤ) - 3 := by unfold biasZ; rw [if_pos hsM]
  have ht : biasZ t = (t.smallBias.val : ℤ) - 3 := by unfold biasZ; rw [if_pos htM]
  rw [ho1, ho2, hs, ht]
  have hsum := Phase1Convergence.avgFin7_preserves_sum s.smallBias t.smallBias
  omega

private theorem mem_of_app_left {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- `centredBiasSum` is conserved under any chosen-pair update on an all-Main phase-1 window. -/
theorem centredBiasSum_stepOrSelf_eq (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Convergence.Phase1AllMain n c) (r₁ r₂ : AgentState L K) :
    centredBiasSum (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) = centredBiasSum c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left happ
    have hm2 := mem_of_app_right happ
    obtain ⟨h11, h1M⟩ := hph r₁ hm1
    obtain ⟨h21, h2M⟩ := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have hsplit : c = (c - {r₁, r₂}) + ({r₁, r₂} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel hsub]
    have hpair := Transition_centredBiasSum_pair_eq_of_both_main r₁ r₂ h11 h21 h1M h2M
    unfold centredBiasSum
    rw [hc', Multiset.map_add, Multiset.sum_add, hpair]
    conv_rhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.sum_add]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `centredBiasSum` is conserved on the one-step kernel support. -/
theorem centredBiasSum_eq_on_support (n : ℕ) (v : ℤ)
    (c c' : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n c)
    (hle : centredBiasSum c = v)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    centredBiasSum c' = v := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    show centredBiasSum (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) = v
    rw [centredBiasSum_stepOrSelf_eq n c hInv r₁ r₂]; exact hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hle

/-- **The honest sum-invariant entry predicate.**  The centred Main bias sum is bounded in
absolute value by the Main count `n` — true at the Doty Phase-1 entry (each Main encodes a `±1`
opinion, so `|S₀| ≤ |M| = n`) and conserved by averaging.  This pins the `{0,1}`/`{5,6}` stall
windows out of reach (they would force `|S₀| ≥ 2n`). -/
def SumPinned (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase1Convergence.Phase1AllMain n c ∧ |centredBiasSum c| ≤ (n : ℤ)

/-- `SumPinned` is one-step-support closed: the window is closed
(`Phase1AllMain_support_closed`) and the sum is conserved. -/
theorem SumPinned_support_closed (n : ℕ) (c c' : Config (AgentState L K))
    (hw : SumPinned n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    SumPinned n c' := by
  obtain ⟨hwin, hbound⟩ := hw
  refine ⟨Phase1Convergence.Phase1AllMain_support_closed n c c' hwin hc', ?_⟩
  rw [centredBiasSum_eq_on_support n (centredBiasSum c) c c' hwin rfl hc']
  exact hbound

/-- Packaged as the engine's `InvClosed` predicate for `SumPinned`. -/
theorem invClosed_sumPinned (n : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => SumPinned (L := L) (K := K) n c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | ¬ SumPinned (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  exact hx (SumPinned_support_closed n c x hInv hsupp)

/-! ## Stage 2 — the structure lemma (the `{2,3,4}` second-moment ceiling).

A Main with `smallBias.val ∈ {2,3,4}` is at squared distance `≤ 1` from the origin `3`
(`sqDist3N ≤ 1`, exhaustive `decide`).  So a config with NO far Main (`val ≤ 1` or `val ≥ 5`) has
`secondMomentN ≤ |M| = n`.  Contrapositive: `secondMomentN c > n` forces a far Main. -/

/-- A Main is **far** if its `smallBias` is at distance `≥ 2` from the origin `3`:
`val ≤ 1` (`farLow`, bias `≤ −2`) or `val ≥ 5` (`farHigh`, bias `≥ +2`). -/
def far (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ (a.smallBias.val ≤ 1 ∨ 5 ≤ a.smallBias.val)

instance (a : AgentState L K) : Decidable (far a) := by unfold far; infer_instance

/-- **The `{2,3,4}` ceiling (exhaustive).**  A non-far value (`2 ≤ val ≤ 4`) is at squared
distance `≤ 1` from `3`. -/
theorem sqDist3N_le_one_of_not_far (v : Fin 7) (h : 2 ≤ v.val ∧ v.val ≤ 4) :
    AveragingCollapse.sqDist3N v ≤ 1 := by
  obtain ⟨h2, h4⟩ := h
  revert h2 h4; revert v; decide

/-- A non-far Main contributes `sqMainN ≤ 1` to the second moment. -/
theorem sqMainN_le_one_of_not_far (a : AgentState L K) (h : ¬ far a) :
    AveragingCollapse.sqMainN a ≤ 1 := by
  unfold AveragingCollapse.sqMainN
  by_cases hr : a.role = Role.main
  · rw [if_pos hr]
    apply sqDist3N_le_one_of_not_far
    unfold far at h
    push Not at h
    have := h hr
    omega
  · rw [if_neg hr]; exact Nat.zero_le _

/-- **The structure ceiling.**  If no Main is far, the second moment is bounded by the card:
`secondMomentN c ≤ c.card`. -/
theorem secondMomentN_le_card_of_no_far (c : Config (AgentState L K))
    (hno : ∀ a ∈ c, ¬ far a) :
    AveragingCollapse.secondMomentN c ≤ c.card := by
  unfold AveragingCollapse.secondMomentN
  calc (c.map (fun a => AveragingCollapse.sqMainN a)).sum
      ≤ (c.map (fun _ => 1)).sum :=
        Multiset.sum_map_le_sum_map _ _ (fun a ha => sqMainN_le_one_of_not_far a (hno a ha))
    _ = c.card := by rw [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]

/-- **The structure lemma.**  On a window of `n` agents, if `secondMomentN c > n`, then some Main
is far (`val ≤ 1` or `val ≥ 5`).  (The sum invariant `SumPinned` further pins WHICH side — see the
file header — but the per-step strict-drop rectangle only needs the far witness here.) -/
theorem farExists_of_secondMoment_gt_n (n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) (hsm : n < AveragingCollapse.secondMomentN c) :
    ∃ a ∈ c, far a := by
  by_contra hno
  push Not at hno
  have := secondMomentN_le_card_of_no_far c hno
  rw [hcard] at this
  omega

/-! ## Stage 3 — the drain rate (the far × centre strict-drop rectangles).

Two state-finset rectangles deliver the strict drop, mirroring `DrainThreading`'s
`extremePosSet ×ˢ pullPosSet` exactly:

* `farHighSet` (`val ≥ 5`) `×ˢ` `lowSet` (`val ≤ 3`): every pair has `val` gap `≥ 5 − 3 = 2`;
* `farLowSet`  (`val ≤ 1`) `×ˢ` `highSet` (`val ≥ 3`): every pair has `val` gap `≥ 3 − 1 = 2`.

`avgFin7_sqDist3_pair_drop` gives drop `= ⌊gap²/2⌋ ≥ ⌊4/2⌋ = 2 ≥ 1`, so each cell strictly drops
`secondMomentN`.  `Phase7Convergence.drop_prob_of_rect` then converts the rectangle's
interaction-count mass into a kernel drop-probability floor. -/

/-- A far-high Main (`role = main ∧ smallBias.val ≥ 5`). -/
def farHigh (a : AgentState L K) : Prop := a.role = Role.main ∧ 5 ≤ a.smallBias.val
/-- A low-side Main (`role = main ∧ smallBias.val ≤ 3`). -/
def low (a : AgentState L K) : Prop := a.role = Role.main ∧ a.smallBias.val ≤ 3
/-- A far-low Main (`role = main ∧ smallBias.val ≤ 1`). -/
def farLow (a : AgentState L K) : Prop := a.role = Role.main ∧ a.smallBias.val ≤ 1
/-- A high-side Main (`role = main ∧ smallBias.val ≥ 3`). -/
def high (a : AgentState L K) : Prop := a.role = Role.main ∧ 3 ≤ a.smallBias.val

instance (a : AgentState L K) : Decidable (farHigh a) := by unfold farHigh; infer_instance
instance (a : AgentState L K) : Decidable (low a) := by unfold low; infer_instance
instance (a : AgentState L K) : Decidable (farLow a) := by unfold farLow; infer_instance
instance (a : AgentState L K) : Decidable (high a) := by unfold high; infer_instance

def farHighSet (L K : ℕ) : Finset (AgentState L K) := Finset.univ.filter (fun a => farHigh a)
def lowSet (L K : ℕ) : Finset (AgentState L K) := Finset.univ.filter (fun a => low a)
def farLowSet (L K : ℕ) : Finset (AgentState L K) := Finset.univ.filter (fun a => farLow a)
def highSet (L K : ℕ) : Finset (AgentState L K) := Finset.univ.filter (fun a => high a)

theorem farHigh_low_disjoint (a : AgentState L K) (ha : a ∈ farHighSet L K)
    (b : AgentState L K) (hb : b ∈ lowSet L K) : a ≠ b := by
  simp only [farHighSet, lowSet, Finset.mem_filter, farHigh, low] at ha hb
  intro heq; rw [heq] at ha; omega

theorem farLow_high_disjoint (a : AgentState L K) (ha : a ∈ farLowSet L K)
    (b : AgentState L K) (hb : b ∈ highSet L K) : a ≠ b := by
  simp only [farLowSet, highSet, Finset.mem_filter, farLow, high] at ha hb
  intro heq; rw [heq] at ha; omega

/-- **The avgFin7 strict-drop cell (`val ≥ 5` × `val ≤ 3`).**  When `x ≥ 5` and `y ≤ 3` the gap is
`≥ 2`, so the centred second moment of the averaged pair is `+1 ≤` the inputs'. -/
theorem avgFin7_sqDist3_pair_drop_high (x y : Fin 7) (hx : 5 ≤ x.val) (hy : y.val ≤ 3) :
    AveragingCollapse.sqDist3N (avgFin7 x y).1 + AveragingCollapse.sqDist3N (avgFin7 x y).2 + 1
      ≤ AveragingCollapse.sqDist3N x + AveragingCollapse.sqDist3N y := by
  revert hx hy; revert x y; decide

/-- **The avgFin7 strict-drop cell (`val ≤ 1` × `val ≥ 3`).** -/
theorem avgFin7_sqDist3_pair_drop_low (x y : Fin 7) (hx : x.val ≤ 1) (hy : 3 ≤ y.val) :
    AveragingCollapse.sqDist3N (avgFin7 x y).1 + AveragingCollapse.sqDist3N (avgFin7 x y).2 + 1
      ≤ AveragingCollapse.sqDist3N x + AveragingCollapse.sqDist3N y := by
  revert hx hy; revert x y; decide

/-- **Per-pair `secondMomentN` strict drop (`val ≥ 5` × `val ≤ 3`).**  Reduce to `avgFin7` and
apply the exhaustive strict-drop cell. -/
theorem Transition_secondMomentN_pair_drop_high (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsv : 5 ≤ s.smallBias.val) (htv : t.smallBias.val ≤ 3) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K))).map (fun a => AveragingCollapse.sqMainN a)).sum + 1
      ≤ ((({s, t} : Multiset (AgentState L K)).map (fun a => AveragingCollapse.sqMainN a)).sum) := by
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [AveragingCollapse.sqMainN_pair, AveragingCollapse.sqMainN_pair]
  have ho1 : AveragingCollapse.sqMainN
      ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1} : AgentState L K)
      = AveragingCollapse.sqDist3N (avgFin7 s.smallBias t.smallBias).1 := by
    unfold AveragingCollapse.sqMainN; rw [if_pos hsM]
  have ho2 : AveragingCollapse.sqMainN
      ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2} : AgentState L K)
      = AveragingCollapse.sqDist3N (avgFin7 s.smallBias t.smallBias).2 := by
    unfold AveragingCollapse.sqMainN; rw [if_pos htM]
  have hs : AveragingCollapse.sqMainN s = AveragingCollapse.sqDist3N s.smallBias := by
    unfold AveragingCollapse.sqMainN; rw [if_pos hsM]
  have ht : AveragingCollapse.sqMainN t = AveragingCollapse.sqDist3N t.smallBias := by
    unfold AveragingCollapse.sqMainN; rw [if_pos htM]
  rw [ho1, ho2, hs, ht]
  exact avgFin7_sqDist3_pair_drop_high s.smallBias t.smallBias hsv htv

/-- **Per-pair `secondMomentN` strict drop (`val ≤ 1` × `val ≥ 3`).** -/
theorem Transition_secondMomentN_pair_drop_low (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsv : s.smallBias.val ≤ 1) (htv : 3 ≤ t.smallBias.val) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K))).map (fun a => AveragingCollapse.sqMainN a)).sum + 1
      ≤ ((({s, t} : Multiset (AgentState L K)).map (fun a => AveragingCollapse.sqMainN a)).sum) := by
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [AveragingCollapse.sqMainN_pair, AveragingCollapse.sqMainN_pair]
  have ho1 : AveragingCollapse.sqMainN
      ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1} : AgentState L K)
      = AveragingCollapse.sqDist3N (avgFin7 s.smallBias t.smallBias).1 := by
    unfold AveragingCollapse.sqMainN; rw [if_pos hsM]
  have ho2 : AveragingCollapse.sqMainN
      ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2} : AgentState L K)
      = AveragingCollapse.sqDist3N (avgFin7 s.smallBias t.smallBias).2 := by
    unfold AveragingCollapse.sqMainN; rw [if_pos htM]
  have hs : AveragingCollapse.sqMainN s = AveragingCollapse.sqDist3N s.smallBias := by
    unfold AveragingCollapse.sqMainN; rw [if_pos hsM]
  have ht : AveragingCollapse.sqMainN t = AveragingCollapse.sqDist3N t.smallBias := by
    unfold AveragingCollapse.sqMainN; rw [if_pos htM]
  rw [ho1, ho2, hs, ht]
  exact avgFin7_sqDist3_pair_drop_low s.smallBias t.smallBias hsv htv

/-- **Config-level `secondMomentN` strict drop (`val ≥ 5` × `val ≤ 3`).** -/
theorem secondMomentN_stepOrSelf_drop_high (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Convergence.Phase1AllMain n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) (hsH : farHigh s) (htL : low t) :
    AveragingCollapse.secondMomentN (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ AveragingCollapse.secondMomentN c := by
  obtain ⟨_, hph⟩ := hInv
  obtain ⟨hsM, hsv⟩ := hsH
  obtain ⟨htM, htv⟩ := htL
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  obtain ⟨hs1, _⟩ := hph s hsm
  obtain ⟨ht1, _⟩ := hph t htm
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  have hsplit : c = (c - {s, t}) + ({s, t} : Multiset (AgentState L K)) := by
    rw [Multiset.sub_add_cancel hsub]
  have hpair := Transition_secondMomentN_pair_drop_high s t hs1 ht1 hsM htM hsv htv
  unfold AveragingCollapse.secondMomentN
  rw [hc', Multiset.map_add, Multiset.sum_add]
  have hrhs : (c.map (fun a => AveragingCollapse.sqMainN a)).sum
      = ((c - {s, t}).map (fun a => AveragingCollapse.sqMainN a)).sum
        + (({s, t} : Multiset (AgentState L K)).map (fun a => AveragingCollapse.sqMainN a)).sum := by
    conv_lhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.sum_add]
  omega

/-- **Config-level `secondMomentN` strict drop (`val ≤ 1` × `val ≥ 3`).** -/
theorem secondMomentN_stepOrSelf_drop_low (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Convergence.Phase1AllMain n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) (hsL : farLow s) (htH : high t) :
    AveragingCollapse.secondMomentN (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ AveragingCollapse.secondMomentN c := by
  obtain ⟨_, hph⟩ := hInv
  obtain ⟨hsM, hsv⟩ := hsL
  obtain ⟨htM, htv⟩ := htH
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  obtain ⟨hs1, _⟩ := hph s hsm
  obtain ⟨ht1, _⟩ := hph t htm
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  have hsplit : c = (c - {s, t}) + ({s, t} : Multiset (AgentState L K)) := by
    rw [Multiset.sub_add_cancel hsub]
  have hpair := Transition_secondMomentN_pair_drop_low s t hs1 ht1 hsM htM hsv htv
  unfold AveragingCollapse.secondMomentN
  rw [hc', Multiset.map_add, Multiset.sum_add]
  have hrhs : (c.map (fun a => AveragingCollapse.sqMainN a)).sum
      = ((c - {s, t}).map (fun a => AveragingCollapse.sqMainN a)).sum
        + (({s, t} : Multiset (AgentState L K)).map (fun a => AveragingCollapse.sqMainN a)).sum := by
    conv_lhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.sum_add]
  omega

/-- **The far-high × low rectangle drop probability.**  On a `Phase1AllMain` window, one step drops
`secondMomentN` with probability `≥ (#farHigh)·(#low)/(n(n−1))`. -/
theorem secondMomentN_drop_prob_rect_high (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n c) :
    ENNReal.ofReal
        (((farHighSet L K).sum c.count * (lowSet L K).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | AveragingCollapse.secondMomentN c' + 1 ≤ AveragingCollapse.secondMomentN c} := by
  have hcardn : c.card = n := hInv.1
  refine Phase7Convergence.drop_prob_of_rect (fun c => AveragingCollapse.secondMomentN c) n hn c
    hcardn ((farHighSet L K) ×ˢ (lowSet L K)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    simp only [farHighSet, Finset.mem_filter] at hsmem
    simp only [lowSet, Finset.mem_filter] at htmem
    obtain ⟨_, hsH⟩ := hsmem
    obtain ⟨_, htL⟩ := htmem
    have happ : Protocol.Applicable c s t := by
      have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
      have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
      have hne : s ≠ t := farHigh_low_disjoint s
        (by simp only [farHighSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsH⟩) t
        (by simp only [lowSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htL⟩)
      exact Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact secondMomentN_stepOrSelf_drop_high n c hInv s t happ hsH htL
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _ farHigh_low_disjoint]

/-- **The far-low × high rectangle drop probability.** -/
theorem secondMomentN_drop_prob_rect_low (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n c) :
    ENNReal.ofReal
        (((farLowSet L K).sum c.count * (highSet L K).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | AveragingCollapse.secondMomentN c' + 1 ≤ AveragingCollapse.secondMomentN c} := by
  have hcardn : c.card = n := hInv.1
  refine Phase7Convergence.drop_prob_of_rect (fun c => AveragingCollapse.secondMomentN c) n hn c
    hcardn ((farLowSet L K) ×ˢ (highSet L K)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    simp only [farLowSet, Finset.mem_filter] at hsmem
    simp only [highSet, Finset.mem_filter] at htmem
    obtain ⟨_, hsL⟩ := hsmem
    obtain ⟨_, htH⟩ := htmem
    have happ : Protocol.Applicable c s t := by
      have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
      have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
      have hne : s ≠ t := farLow_high_disjoint s
        (by simp only [farLowSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsL⟩) t
        (by simp only [highSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htH⟩)
      exact Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact secondMomentN_stepOrSelf_drop_low n c hInv s t happ hsL htH
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _ farLow_high_disjoint]

/-- **The levels-engine `hdrop` from a `secondMomentN` drop-probability floor.**  Mirror of
`DrainThreading.extremeU_hdrop_of_floor`: from a strict-drop floor `p` at a state with
`secondMomentN b = m`, the level-`m` failure mass is `≤ 1 − p`. -/
theorem secondMomentN_hdrop_of_floor (m : ℕ) (p : ℝ≥0∞)
    (b : Config (AgentState L K)) (hbm : AveragingCollapse.secondMomentN b = m)
    (hfloor : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        {c' | AveragingCollapse.secondMomentN c' + 1 ≤ AveragingCollapse.secondMomentN b}) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ ≤ 1 - p := by
  classical
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) |
        AveragingCollapse.secondMomentN c' + 1 ≤ AveragingCollapse.secondMomentN b}
      = OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hbm]; omega
  have hmeas : MeasurableSet
      (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN (L := L) (K := K) c) m) :=
    OneSidedCancel.potBelow_measurable _ m
  haveI hprob : IsProbabilityMeasure
      (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have htot : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure Set.univ = 1 :=
    hprob.measure_univ
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hKb, hcompl]
  have hp_le : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m) := by
    rw [← hsucc_eq]; exact hfloor
  exact tsub_le_tsub_left hp_le 1

/-- **The per-level `hdrop` from the far-high structural floor.**  With `≥ 1` far-high Main and a
low-side partner margin `≥ P`, the level-`m` failure mass is `≤ 1 − ofReal(P/(n(n−1)))`. -/
theorem secondMomentN_hdrop_of_struct_high (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n b)
    (hbm : AveragingCollapse.secondMomentN b = m) (P : ℕ)
    (hfar : 1 ≤ (farHighSet L K).sum b.count)
    (hpart : P ≤ (lowSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  refine secondMomentN_hdrop_of_floor m _ b hbm ?_
  refine le_trans ?_ (secondMomentN_drop_prob_rect_high n hn b hInv)
  have hprod : (P : ℕ) ≤ (farHighSet L K).sum b.count * (lowSet L K).sum b.count := by
    calc (P : ℕ) ≤ 1 * P := by omega
      _ ≤ (farHighSet L K).sum b.count * P := Nat.mul_le_mul_right _ hfar
      _ ≤ (farHighSet L K).sum b.count * (lowSet L K).sum b.count :=
          Nat.mul_le_mul_left _ hpart
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **The per-level `hdrop` from the far-low structural floor.** -/
theorem secondMomentN_hdrop_of_struct_low (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n b)
    (hbm : AveragingCollapse.secondMomentN b = m) (P : ℕ)
    (hfar : 1 ≤ (farLowSet L K).sum b.count)
    (hpart : P ≤ (highSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  refine secondMomentN_hdrop_of_floor m _ b hbm ?_
  refine le_trans ?_ (secondMomentN_drop_prob_rect_low n hn b hInv)
  have hprod : (P : ℕ) ≤ (farLowSet L K).sum b.count * (highSet L K).sum b.count := by
    calc (P : ℕ) ≤ 1 * P := by omega
      _ ≤ (farLowSet L K).sum b.count * P := Nat.mul_le_mul_right _ hfar
      _ ≤ (farLowSet L K).sum b.count * (highSet L K).sum b.count :=
          Nat.mul_le_mul_left _ hpart
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-! ## Stage 4 — wiring the derived rate into `AveragingCollapse.phase1_pullPos_floor_whp`.

The carried `q : ℕ → ℝ≥0∞` slot is now discharged: at every level `m > n` (the structure ceiling),
the structure lemma `farExists_of_secondMoment_gt_n` guarantees a far Main, and either the far-high
or far-low rectangle delivers `q m = 1 − ofReal(P/(n(n−1)))`.

### The honest time budget

Consumer (`phase1_pullPos_floor_whp`) needs the floor at level `m = 4·(n − P) + 1`.  The level-tail
gives failure mass `≤ (q m)^t = (1 − P/(n(n−1)))^t`.  With the partner margin `P = Θ(n)` (a constant
fraction of Mains is on the centre side; this is the carried partner floor, exactly as the landed
`extremeU` chain carries `hpull`), `q m = 1 − Θ(1/n)`, so `(q m)^t ≤ e^{−Θ(t/n)}`.

* Single far witness only (`P = 1`, no partner floor): `q m = 1 − 1/(n(n−1))`, horizon
  `t = Θ(n²·log n)` for `O(1/n²)` failure — the `Θ(n²)` "crude" regime.
* Constant-fraction partner floor (`P = Θ(n)`): `q m = 1 − Θ(1/n)`, horizon `t = Θ(n·log n)` for
  `O(1/n²)` failure — the paper-faithful `O(n log n)` of Lemma 5.3 / reference [45].

Either way the failure `(q m)^t → 0` polynomially; the partner floor `P` (carried, not yet
quantitatively landed — it is the same `Θ(n)` centre-mass content `[45] Corollary 1` supplies) is
the ONLY remaining input, exactly as `AveragingCollapse` documented.  Below the ceiling (`m ≤ n`)
the level is already inside the good event `secondMomentN ≤ 4·(n − P)` whenever `4·(n − P) ≥ n`,
i.e. `P ≤ 3n/4`, which the saturated-side budget always satisfies. -/

/-- **The hypothesis-free Phase-1 saturated-side floor, whp (residual #5 discharged).**  Feeds the
derived per-level rate `q` into `AveragingCollapse.phase1_pullPos_floor_whp`: with the carried
partner floor `hpart` and far-witness floor `hfar` available at every level `m > n`, the floor
`P ≤ pullPosSet.sum count` FAILS with probability at most `(q (4(n−P)+1))^t`, where
`q m = 1 − ofReal(P'/(n(n−1)))` (`P'` the partner margin).  Strongest form: the only carried atom
is the rate `q` family, supplied by `hdrop`, exactly as `phase1_pullPos_floor_whp` exposes it. -/
theorem phase1_pullPos_floor_whp_of_struct (n P : ℕ) (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : Config (AgentState L K),
      Phase1Convergence.Phase1AllMain n b → AveragingCollapse.secondMomentN b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ ≤ q m)
    (c : Config (AgentState L K)) (hInvc : Phase1Convergence.Phase1AllMain n c)
    (hP : P ≤ n) (hc : AveragingCollapse.secondMomentN c ≤ 4 * (n - P) + 1) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {c' | ¬ P ≤ (DrainThreading.pullPosSet L K).sum c'.count}
      ≤ (q (4 * (n - P) + 1)) ^ t :=
  AveragingCollapse.phase1_pullPos_floor_whp n P q hdrop c hInvc hP hc t

/-- **The far-witness rate is realizable above the ceiling.**  For every `m > n`, any in-window
state at level `m` with a low-side partner margin `≥ P` (and the far witness, which the structure
lemma `farExists_of_secondMoment_gt_n` supplies whenever the far agent is on the high side)
satisfies the `hdrop` bound at `q m = 1 − ofReal(P/(n(n−1)))`.  This is the constructive content
behind the carried `q`: the rate is not free, it is the far × partner rectangle. -/
theorem hdrop_realizable_high (n : ℕ) (hn : 2 ≤ n) (P : ℕ) (m : ℕ)
    (b : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n b)
    (hbm : AveragingCollapse.secondMomentN b = m)
    (hfar : 1 ≤ (farHighSet L K).sum b.count) (hpart : P ≤ (lowSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  secondMomentN_hdrop_of_struct_high n m hn b hInv hbm P hfar hpart

end AveragingRate

end ExactMajority
