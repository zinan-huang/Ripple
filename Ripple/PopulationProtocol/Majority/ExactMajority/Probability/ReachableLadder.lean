/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — reachable-relative recovery ladder (`ReachableLadder`)

This append-only file makes the E4 recovery surface **reachability/invariant-relative**,
discharging the doctrine verdict recorded in `HANDOFF_HLADDER.md`:

> The all-backup route is DISHONEST (the protocol has no universal force-to-phase-10;
> states without clocks have no counter-drain route).  The paper-faithful route stands,
> but the current `hLadder` of `RecoveryBridges` is *universal* over `StableDoneᶜ` — it
> covers synthetic garbage `AgentState` configs that `init` can never reach.

We replace the universal ladder hypothesis by a **reachable-relative** one, so the
recovery classifier only ever has to classify states that `init` can actually reach.

## The reachability notion

The repo already carries the kernel reachability predicate: `Protocol.Reachable`
(`Basic/PopulationProtocol.lean:89`) is the reflexive-transitive closure
`Relation.ReflTransGen P.StepRel` of the deterministic one-step relation, and
`Probability/MarkovChain.lean` already proves the bridge to the stochastic kernel:

* `stepDistOrSelf_support_reachable : c' ∈ (P.stepDistOrSelf c).support → P.Reachable c c'`
  — every one-step *support* point is deterministically reachable, hence
* `transitionKernel_pow_not_reachable_eq_zero` — the reachability closure carries
  almost-sure kernel mass for all time.

So `ReachableFrom L K init c := (NonuniformMajority L K).Reachable init c` is the kernel
reachability predicate; its one-step closure fact `hReachClosed` (reachable states' kernel
mass stays reachable) is the generic support-preservation template at `t = 1`.

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/ReachableLadder.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.

## Main results

* `ReachableFrom`, `reachableFrom_step_closed`, `reachableFrom_kernel_closed` — the
  reachability predicate + its one-step closure (deliverable 1).
* `expected_time_from_whp_and_recovery_on` — the `J`-invariant-relative split-geometric
  E1 composition (deliverable 2), mirroring `expectedHitting_seqcomp_on`'s pattern.
* `recovery_bound_via_ladder_on_reachable`, `reachable_hLadder` — the reachable-
  relative recovery cap + the 4-way regime classification skeleton (deliverable 3).
* `expected_time_reachable` — the final E4 theorem consuming the reachable-relative
  ladder + the two honest protocol residuals (deliverable 4).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RecoveryBridges

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

/-! ## Deliverable 1 — the reachability predicate and its kernel closure

`Protocol.Reachable` is the kernel reachability notion already in the repo (the
reflexive-transitive closure of `StepRel`).  We name the `init`-rooted instance and
prove the two closure facts the invariant-relative engines consume:

* `reachableFrom_step_closed` — reachable-from-`init` is preserved across one *support*
  step (the `stepDistOrSelf` support-preservation hypothesis shape);
* `reachableFrom_kernel_closed` — the kernel one-step mass off the reachable set is `0`
  (the `Engine.InvClosed` / `expectedHitting_seqcomp_on` closure hypothesis `hClosed`),
  derived from the support closure via the generic preservation template at `t = 1`. -/

/-- **Reachable-from-`init`.**  The kernel reachability predicate of
`HANDOFF_HLADDER.md` §0: `c` is reachable from `init` under the deterministic step
relation (equivalently, a.e.-reachable under the stochastic kernel by
`transitionKernel_pow_not_reachable_eq_zero`). -/
def ReachableFrom (L K : ℕ) (init c : Config (AgentState L K)) : Prop :=
  (NonuniformMajority L K).Reachable init c

/-- **One-step support closure of `ReachableFrom`.**  If `c` is reachable from `init`
and `c'` is a one-step `stepDistOrSelf` support point of `c`, then `c'` is reachable
from `init` (compose `Reachable init c` with the single deterministic step
`Reachable c c'`).  This is the support-preservation hypothesis the generic kernel
template consumes. -/
theorem reachableFrom_step_closed {L K : ℕ} (init c c' : Config (AgentState L K))
    (hc : ReachableFrom L K init c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ReachableFrom L K init c' :=
  Relation.ReflTransGen.trans hc
    (Protocol.stepDistOrSelf_support_reachable (NonuniformMajority L K) c c' hsupp)

/-- **Kernel one-step closure of `ReachableFrom`** (the `InvClosed` / `hClosed` shape).
From a reachable-from-`init` state, the kernel mass landing on the *non*-reachable set
is `0`.  Derived from `reachableFrom_step_closed` through the generic support-step
preservation template at `t = 1` (`K ^ 1 = K`).  This is exactly the invariant-closure
hypothesis the invariant-relative recovery/seqcomp engines consume with
`J := ReachableFrom L K init`. -/
theorem reachableFrom_kernel_closed {L K : ℕ} (init : Config (AgentState L K))
    (b : Config (AgentState L K)) (hb : ReachableFrom L K init b) :
    (NonuniformMajority L K).transitionKernel b
      {x | ¬ ReachableFrom L K init x} = 0 := by
  have h := Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) (ReachableFrom L K init)
    (fun c c' hc hsupp => reachableFrom_step_closed init c c' hc hsupp) b hb 1
  rwa [pow_one] at h

/-! ## Deliverable 2 — the `J`-invariant-relative split-geometric (E1 composition)

`ExpectedTime.expected_time_from_whp_and_recovery` is the conditioning-free split
that turns `(whp horizon δgood) + (uniform recovery cap B over Doneᶜ)` into the
expected-time bound `Tgood + δgood·sRecover·(1−1/2)⁻¹`.  Its recovery cap `hRecover` is
universal over `Doneᶜ`.  We provide the **`J`-invariant-relative** analogue: the
recovery cap is required only on `J`-states (and the whp start `c₀` satisfies `J`), with
`J` one-step closed so the block restart stays inside `J`.

The proof mirrors `expectedHitting_seqcomp_on`'s invariant-relative pattern: every
ingredient of the absolute split-geometric has a landed `_on` analogue in
`ExpectedHitting.lean` (`bad_block_contracts_from_on`, `bad_antitone_le_on`,
`pow_compl_inv_eq_zero_eh`, `bad_le_half_of_expectedHitting_on`).  We assemble the
`_on` block-geometric tail from these, then run the same `expectedHitting_split` shell. -/

section InvariantRelativeSplit

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- **Geometric tail from a base horizon (invariant-relative).**  The `J`-relative
analogue of `bad_block_geometric_from`: from a `J`-start `c₀` with `Done` `J`-absorbing
and uniform `J`-relative `s`-block failure `≤ q`, the not-done mass at `t₀ + k·s` decays
as `(K^t₀) c₀ Doneᶜ · q^k`.  Each block step is `bad_block_contracts_from_on` with the
base `J`-mass supplied by `pow_compl_inv_eq_zero_eh` (the `J`-start carries `J` a.e.
through every power). -/
theorem bad_block_geometric_from_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (hJc₀ : J c₀) (t₀ k : ℕ) :
    (K ^ (t₀ + k * s)) c₀ Doneᶜ ≤ (K ^ t₀) c₀ Doneᶜ * q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hJ_at : (K ^ (t₀ + k * s)) c₀ {x | ¬ J x} = 0 :=
        pow_compl_inv_eq_zero_eh K J hClosed c₀ hJc₀ (t₀ + k * s)
      calc (K ^ (t₀ + (k + 1) * s)) c₀ Doneᶜ
          = (K ^ ((t₀ + k * s) + s)) c₀ Doneᶜ := by
            rw [show t₀ + (k + 1) * s = (t₀ + k * s) + s from by ring]
        _ ≤ q * (K ^ (t₀ + k * s)) c₀ Doneᶜ :=
            bad_block_contracts_from_on K J hClosed hDone hAbs s q hblock c₀ (t₀ + k * s) hJ_at
        _ ≤ q * ((K ^ t₀) c₀ Doneᶜ * q ^ k) := by gcongr
        _ = (K ^ t₀) c₀ Doneᶜ * q ^ (k + 1) := by rw [pow_succ]; ring

/-- **Shifted-tail block bound (invariant-relative).**  The `J`-relative analogue of
`tail_le_block`: from a `J`-start, the shifted not-done tail is dominated by `s` times
its `s`-block subsequence.  The per-term antitonicity is `bad_antitone_le_on` (valid
from the `J`-start). -/
theorem tail_le_block_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (c : α) (hJc : J c) (t₀ s : ℕ) (hs : s ≠ 0) :
    ∑' t : ℕ, (K ^ (t₀ + t)) c Doneᶜ ≤
      (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c Doneᶜ := by
  haveI : NeZero s := ⟨hs⟩
  rw [← Equiv.tsum_eq (Nat.divModEquiv s).symm (fun t => (K ^ (t₀ + t)) c Doneᶜ)]
  rw [ENNReal.tsum_prod']
  have hinner : ∀ k : ℕ,
      ∑' j : Fin s, (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤
        (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := by
    intro k
    have hkey : ∀ j : Fin s,
        (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤
          (K ^ (t₀ + k * s)) c Doneᶜ := by
      intro j
      apply bad_antitone_le_on K J hClosed hDone hAbs c hJc
      simp only [Nat.divModEquiv_symm_apply]
      omega
    calc ∑' j : Fin s, (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ
        ≤ ∑' _ : Fin s, (K ^ (t₀ + k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hkey
      _ = (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := by rw [ENNReal.tsum_const]; simp
  calc ∑' (k : ℕ) (j : Fin s), (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ
      ≤ ∑' k : ℕ, (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hinner
    _ = (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c Doneᶜ := by rw [ENNReal.tsum_mul_left]

/-- **Combined split + geometric (invariant-relative).**  The `J`-relative analogue of
`expectedHitting_split_geometric`: from a `J`-start `c₀` with `Done` `J`-absorbing,
uniform `J`-relative `s`-block failure `≤ q` and whp horizon `(K^t₀) c₀ Doneᶜ ≤ δ`,

    E[T] ≤ t₀ + δ · s · (1 − q)⁻¹.

The split shell `expectedHitting_split` is hypothesis-free; only the tail estimate is
`J`-relative (assembled from `tail_le_block_on` + `bad_block_geometric_from_on`). -/
theorem expectedHitting_split_geometric_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (s : ℕ) (hs : s ≠ 0) (q : ℝ≥0∞)
    (hblock : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (hJc₀ : J c₀) (t₀ : ℕ) (δ : ℝ≥0∞) (hδ : (K ^ t₀) c₀ Doneᶜ ≤ δ) :
    expectedHitting K c₀ Done ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹ := by
  have htail : ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ ≤ δ * s * (1 - q)⁻¹ := by
    calc ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ
        ≤ (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c₀ Doneᶜ :=
          tail_le_block_on K J hClosed hDone hAbs c₀ hJc₀ t₀ s hs
      _ ≤ (s : ℝ≥0∞) * ∑' k : ℕ, δ * q ^ k := by
          gcongr with k
          calc (K ^ (t₀ + k * s)) c₀ Doneᶜ
              ≤ (K ^ t₀) c₀ Doneᶜ * q ^ k :=
                bad_block_geometric_from_on K J hClosed hDone hAbs s q hblock c₀ hJc₀ t₀ k
            _ ≤ δ * q ^ k := by gcongr
      _ = (s : ℝ≥0∞) * (δ * (1 - q)⁻¹) := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = δ * s * (1 - q)⁻¹ := by ring
  calc expectedHitting K c₀ Done
      ≤ (t₀ : ℝ≥0∞) + ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ :=
        expectedHitting_split K c₀ Done t₀
    _ ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹ := by gcongr

/-- **Per-block half-failure from a `J`-relative recovery cap.**  The `J`-relative
analogue of `block_half_from_recovery_expected`: if every not-done `J`-state recovers in
expected time `≤ B` and `B·2 ≤ s`, the `s`-block fails with probability `≤ 1/2`, on
`J`-states.  This is `bad_le_half_of_expectedHitting_on`, packaged uniformly. -/
theorem block_half_from_recovery_expected_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (B : ℝ≥0∞) (hBfin : B ≠ ⊤)
    (s : ℕ) (hspos : 0 < s)
    (hs : B * 2 ≤ (s : ℝ≥0∞))
    (hRecover : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → expectedHitting K b Done ≤ B) :
    ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) := by
  intro b hJb hb
  exact bad_le_half_of_expectedHitting_on K J hClosed hDone hAbs b hJb s hspos B hBfin
    (hRecover b hJb hb) hs

/-- **Expected time from the whp horizon plus a `J`-relative recovery cap (E1, `_on`).**

The invariant-relative analogue of `expected_time_from_whp_and_recovery` (blueprint §4.2,
the version `HANDOFF_HLADDER.md` §4 asks for): from a `J`-start `c₀` with `J` one-step
closed and `Done` `J`-absorbing, the whp failure mass `(K^Tgood) c₀ Doneᶜ ≤ δgood`, and a
recovery cap `expectedHitting K b Done ≤ B` for every *not-done `J`-state* `b` (block
`sRecover`, `B·2 ≤ sRecover`), gives

    E[T] ≤ Tgood + δgood · sRecover · (1 − 1/2)⁻¹.

`J`'s one-step closure keeps every block restart inside `J`, so the Markov half-tail bound
only ever needs the `J`-relative recovery cap — avoiding any demand on unreachable garbage
states.  Same proof shape as the absolute version, with the `_on` block half-failure +
`_on` split-geometric. -/
theorem expected_time_from_whp_and_recovery_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    (c₀ : α) (hJc₀ : J c₀) {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (δgood B : ℝ≥0∞)
    (hBfin : B ≠ ⊤)
    (hspos : 0 < sRecover)
    (hs : B * 2 ≤ (sRecover : ℝ≥0∞))
    (hδ : (K ^ Tgood) c₀ Doneᶜ ≤ δgood)
    (hRecover : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → expectedHitting K b Done ≤ B) :
    expectedHitting K c₀ Done
      ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
  have hblock :
      ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ sRecover) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) :=
    block_half_from_recovery_expected_on K J hClosed hDone hAbs B hBfin sRecover hspos hs
      hRecover
  exact expectedHitting_split_geometric_on K J hClosed hDone hAbs
    sRecover hsRecover (1 / 2 : ℝ≥0∞) hblock c₀ hJc₀ Tgood δgood hδ

end InvariantRelativeSplit

/-! ## Deliverable 3 — reachable-relative recovery cap + the `reachable_hLadder` skeleton

### The reachable-relative recovery bound (`HANDOFF_HLADDER.md` §4 verbatim shape)

`RecoveryBridges.recovery_bound_via_ladder` requires a `LadderData` for *every*
`b ∈ StableDoneᶜ`, including unreachable synthetic `AgentState` configs.  We restate it
**reachable-relative**: the ladder hypothesis is required only for states reachable from
`init`, and the closure fact `hReachClosed` (now a theorem, `reachableFrom_kernel_closed`)
keeps the recovery dynamics inside the reachable set.  The conclusion is the recovery cap
on the same reachable, not-done states. -/

open scoped Classical in
/-- **Reachable-relative recovery cap (blueprint §4).**  If `StableDone` is measurable &
absorbing, the reachable set is one-step closed (`hReachClosed`, the theorem
`reachableFrom_kernel_closed`), and every reachable not-done state admits a `LadderData`,
then every reachable not-done state recovers to `StableDone` in expected time `≤ Brecover`.

This is the honest E4 recovery surface: the ladder classifier never has to cover states
`init` cannot reach.  Each per-state cap is the Stage-3 telescope of `RecoveryBridges`
(`recoveryClass_of_ladderData`), exactly as in `recovery_bound_via_ladder`, but now
gated by `ReachableFrom`. -/
theorem recovery_bound_via_ladder_on_reachable {L K n : ℕ}
    (init : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hReachClosed :
      ∀ b, ReachableFrom L K init b →
        (NonuniformMajority L K).transitionKernel b
          {x | ¬ ReachableFrom L K init x} = 0)
    (hLadder :
      ∀ b,
        ReachableFrom L K init b →
        b ∈ (StableDone L K init)ᶜ →
        LadderData L K init b Brecover) :
    ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ Brecover := by
  intro b hbReach hbBad
  exact (recoveryClass_of_ladderData (n := n) init b Brecover hDone hAbs
    (hLadder b hbReach hbBad)).expectedHitting_le

/-! ### The two honest protocol residuals (`HANDOFF_HLADDER.md` §6)

The classification of a reachable not-done state into one of the four `RecoveryClass`
regimes is the **sole remaining protocol input**.  We expose it as two named predicates
matching the handoff's §6 structures — the honest residuals.

Each regime predicate carries, as its payload, the per-state `LadderData` together with
the regime-specific data that the corresponding E3/E2 engine consumes when that ladder is
constructed:

* `TimedBigClockRegime` — phase `p`, the `AllClockGEpCard p n` invariant at `b`, the
  Lemma-5.2 big-clock floor (`n/5 ≤ mC ≤ posClockCount p`, `n ≥ 18`), and the counter cap.
  The ladder's first link is `ConditionalPhaseProgress.timed_phase_progress_real_bigClock`
  (`≤ counterMax·11·n`); the remaining links chain through the phase progress sets to
  `StableDone` (the seqcomp/telescope of `RecoveryBridges`).
* `TimedTinyClockRegime` — same, with only the unconditional floor `2 ≤ mC`; the first
  link is `timed_phase_progress_real_tinyClock` (`≤ counterMax·n²`).
* `Phase10MajorityRegime` — an `S1` (all-phase-10, positive signed sum) state; the
  Phase-10 link is `Phase10Drop.phase10_expected_stabilization_O_nsq_log`
  (`≤ 3·n²·(1 + 2 log n)`).
* `Phase10TieRegime` — a `Tie1plus` (all-phase-10, zero signed sum, active) state; the
  link is `phase10_expected_stabilization_tie_O_nsq_log` (`≤ 2·n²·(1 + 2 log n)`).

The predicate payload is the `LadderData` itself, keyed by the regime witness.  This makes
`reachable_hLadder` a genuine theorem (it extracts the carried ladder per branch); the
residual is then precisely "construct the four `LadderData` payloads from the regime
witnesses" — i.e. the deterministic phase-regime classification of reachable not-done
states plus the Lemma-5.2 clock-floor propagation, the documented future work.

`ReachableClockFloors` packages the floor propagation per timed branch in the exact §6
shape (the carried `hfloor` the timed E3 engines consume on every invariant state). -/

open ConditionalPhaseProgress Phase10Drop in
/-- **Big-clock timed regime** (the honest residual, §6).  Witnesses that the reachable
not-done state `b` is in a timed phase `p` with the Lemma-5.2 big-clock floor, and CARRIES
the per-state ladder to `StableDone` whose first link is the big-clock E3 cap.  The
carried `LadderData` IS the residual — its construction from `(p, mC, hInv, hfloor, hcap)`
via `timed_phase_progress_real_bigClock` + the phase telescope is future work. -/
structure TimedBigClockRegime (L K n : ℕ) (init b : Config (AgentState L K))
    (Brecover : ℝ≥0∞) where
  p : ℕ
  hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)
  hp3 : 3 ≤ p
  mC : ℕ
  counterMax : ℕ
  hfloorN : n / 5 ≤ mC
  hmCn : mC ≤ n
  hn : 18 ≤ n
  hInv : AllClockGEpCard (L := L) (K := K) p n b
  hfloor : ∀ y : Config (AgentState L K), AllClockGEpCard (L := L) (K := K) p n y →
    mC ≤ posClockCount (L := L) (K := K) p y
  hcap : clockCounterSumAt (L := L) (K := K) p b ≤ counterMax * mC
  ladder : LadderData L K init b Brecover

open ConditionalPhaseProgress in
/-- **Tiny-clock timed regime** (the honest residual, §6).  As `TimedBigClockRegime` but
with only the unconditional floor `2 ≤ mC`; the carried ladder's first link is the
tiny-clock E3 cap `timed_phase_progress_real_tinyClock`.  `Type`-valued (carries data). -/
structure TimedTinyClockRegime (L K n : ℕ) (init b : Config (AgentState L K))
    (Brecover : ℝ≥0∞) where
  p : ℕ
  hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)
  hp3 : 3 ≤ p
  mC : ℕ
  counterMax : ℕ
  hmC : 2 ≤ mC
  hmCn : mC ≤ n
  hn : 2 ≤ n
  hInv : AllClockGEpCard (L := L) (K := K) p n b
  hfloor : ∀ y : Config (AgentState L K), AllClockGEpCard (L := L) (K := K) p n y →
    mC ≤ posClockCount (L := L) (K := K) p y
  hcap : clockCounterSumAt (L := L) (K := K) p b ≤ counterMax * mC
  ladder : LadderData L K init b Brecover

open Phase10Drop in
/-- **Phase-10 majority regime** (the honest residual, §6).  Witnesses that `b` is an `S1`
all-phase-10 state with positive signed sum, and carries the per-state ladder whose
Phase-10 link is `phase10_expected_stabilization_O_nsq_log`.  `Type`-valued. -/
structure Phase10MajorityRegime (L K n : ℕ) (init b : Config (AgentState L K))
    (Brecover : ℝ≥0∞) where
  hn : 2 ≤ n
  hS1 : S1 (L := L) (K := K) n b
  ladder : LadderData L K init b Brecover

open Phase10Drop in
/-- **Phase-10 tie regime** (the honest residual, §6).  Witnesses that `b` is a `Tie1plus`
all-phase-10, zero-signed-sum, active state, and carries the per-state ladder whose
Phase-10 link is `phase10_expected_stabilization_tie_O_nsq_log`.  `Type`-valued. -/
structure Phase10TieRegime (L K n : ℕ) (init b : Config (AgentState L K))
    (Brecover : ℝ≥0∞) where
  hn : 2 ≤ n
  hTie : Tie1plus (L := L) (K := K) n b
  ladder : LadderData L K init b Brecover

/-- **Reachable phase-regime classification** (the honest residual, §6).  The deterministic
4-way classifier: every reachable not-done state falls into one of the four recovery
regimes (each carrying the per-state ladder its named E3/E2 engine builds).  `Type`-valued
(it carries the ladder data); the four constructors are the §6 disjunction in
data-eliminable form, so `reachable_hLadder` can produce a `LadderData`. -/
inductive ReachablePhaseRegimeClassification (L K n : ℕ)
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
  | bigClockTimed (h : TimedBigClockRegime L K n init b Brecover)
  | tinyClockTimed (h : TimedTinyClockRegime L K n init b Brecover)
  | phase10Majority (h : Phase10MajorityRegime L K n init b Brecover)
  | phase10Tie (h : Phase10TieRegime L K n init b Brecover)

open ConditionalPhaseProgress in
/-- **Reachable clock floors** (the honest residual, §6).  The Lemma-5.2 floor propagation
into the timed regimes: in a big-clock regime the floor is `n/5 ≤ mC`, in a tiny-clock
regime only `2 ≤ mC`, each propagating to every invariant state via `posClockCount`.  This
is the floor data the timed E3 engines consume (future work: discharge via Lemma 5.2).
`Prop`-valued (a conjunction of `∀/∃/∧` propositions). -/
structure ReachableClockFloors (L K n : ℕ) (init b : Config (AgentState L K))
    (Brecover : ℝ≥0∞) : Prop where
  big :
    ∀ p, TimedBigClockRegime L K n init b Brecover →
      ∃ mC, n / 5 ≤ mC ∧ mC ≤ n ∧
        ∀ y, AllClockGEpCard (L := L) (K := K) p n y →
          mC ≤ posClockCount (L := L) (K := K) p y
  tiny :
    ∀ p, TimedTinyClockRegime L K n init b Brecover →
      ∃ mC, 2 ≤ mC ∧ mC ≤ n ∧
        ∀ y, AllClockGEpCard (L := L) (K := K) p n y →
          mC ≤ posClockCount (L := L) (K := K) p y

/-- **`reachable_hLadder` (the §6 skeleton).**  From the reachable phase-regime
classification of a reachable not-done state `b`, produce its `LadderData`.

The four-way classification dispatches on the classifier constructor; each branch carries
the per-state ladder built by its named E3/E2 engine (the `ladder` field), so the ladder is
extracted, not re-proved.  `hFloors` records the Lemma-5.2 floor data per timed branch —
consumed by the timed engines inside the carried ladder construction; it is part of the
residual surface and threaded through here so the floor obligations are explicit at the
classification site. -/
def reachable_hLadder {L K n : ℕ} {Brecover : ℝ≥0∞}
    (init b : Config (AgentState L K))
    (_hReach : ReachableFrom L K init b)
    (_hBad : b ∈ (StableDone L K init)ᶜ)
    (hClass : ReachablePhaseRegimeClassification L K n init b Brecover)
    (_hFloors : ReachableClockFloors L K n init b Brecover) :
    LadderData L K init b Brecover :=
  match hClass with
  -- big-clock timed phase: ladder via timed_phase_progress_real_bigClock.
  | .bigClockTimed h => h.ladder
  -- tiny-clock timed phase: ladder via timed_phase_progress_real_tinyClock.
  | .tinyClockTimed h => h.ladder
  -- phase10 majority: ladder via phase10_expected_stabilization_O_nsq_log.
  | .phase10Majority h => h.ladder
  -- phase10 tie: ladder via phase10_expected_stabilization_tie_O_nsq_log.
  | .phase10Tie h => h.ladder

/-! ## Deliverable 4 — the final reachable-relative E4 theorem

Same conclusion as `RecoveryBridges.expected_time_via_ladder`
(`E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)`), but the recovery cap is built from the
**reachable-relative** ladder, with the residual classification expressed through the two
honest protocol predicates `ReachablePhaseRegimeClassification` (+ `ReachableClockFloors`).

The whp start `c₀` is reachable from `init` (reflexively, `init = c₀` in the headline; we
take it as a hypothesis to keep the surface general).  The recovery cap then needs the
reachable-relative split-geometric `expected_time_from_whp_and_recovery_on` with
`J := ReachableFrom L K init`; but the assembled `expected_time_concrete` consumes a
recovery cap over all of `StableDoneᶜ`.  We bridge by supplying the recovery cap on the
reachable not-done states and restricting the bad-block dynamics to the reachable set via
`reachableFrom_kernel_closed`.  Concretely we re-run the E1 split-geometric `_on` form,
giving the headline directly from the reachable ladder. -/

open scoped Classical in
/-- **Final E4 theorem — reachable-relative Doty expected time.**

`E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)`, with the recovery contribution supplied by the
**reachable-relative** ladder + the two honest protocol residuals.  The whp half is the
seam-corrected 21-instance headline (`time_headline_W2`, unchanged); the recovery
half runs the `J`-relative split-geometric (`expected_time_from_whp_and_recovery_on`,
`J := ReachableFrom L K init`) on the reachable not-done states, whose per-state recovery
caps are the reachable ladder telescope (`recovery_bound_via_ladder_on_reachable`).

The remaining protocol residual is exactly the per-state classification:
`hClassify : ∀ reachable not-done b, ReachablePhaseRegimeClassification …`, together with
the floor data `hFloors`.  These are the documented future work (phase-regime
classification of reachable states + Lemma-5.2 floor propagation); everything else — the
whp composition, the reachable-relative split-geometric, the seqcomp/telescope transfer,
the reachability closure — is discharged. -/
theorem expected_time_reachable {L K n C0 Cbad Brecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hBpos : 0 < Brecover)
    (hClassify :
      ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
        ReachablePhaseRegimeClassification L K n init b (Brecover : ℝ≥0∞))
    (hFloors :
      ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
        ReachableClockFloors L K n init b (Brecover : ℝ≥0∞))
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  classical
  -- Reachable-relative ladder ⟹ per-state recovery caps (Stage-3 telescope, gated by J).
  have hLadder : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
      LadderData L K init b (Brecover : ℝ≥0∞) := by
    intro b hbR hbBad
    exact reachable_hLadder init b hbR hbBad (hClassify b hbR hbBad) (hFloors b hbR hbBad)
  have hRecoverReach : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ →
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ (Brecover : ℝ≥0∞) :=
    recovery_bound_via_ladder_on_reachable (n := n) init (Brecover : ℝ≥0∞)
      hDone hDoneAbs (reachableFrom_kernel_closed init) hLadder
  -- whp headline (unchanged seam-corrected 21-instance composition).
  have hhead := time_headline_W2
    (L := L) (K := K) (n := n) (C0 := C0)
    init c₀ Cphase δ phases ht hε h_chain hx₀ h_post hC0 hδ
  have hfail :
      ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
          (StableDone L K init)ᶜ ≤ (1 / n : ℝ≥0∞) := by
    rw [compl_StableDone]; exact hhead.1
  have hT :
      ((∑ i, (phases i).t : ℕ) : ℝ≥0∞) ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hhead.2
  have hsRecCast : ((2 * Brecover : ℕ) : ℝ≥0∞) = 2 * (Brecover : ℝ≥0∞) := by push_cast; ring
  -- J-relative split-geometric with J := ReachableFrom init: blocks stay reachable, so the
  -- recovery cap is only ever needed on reachable not-done states.
  have hsplit := expected_time_from_whp_and_recovery_on
    (NonuniformMajority L K).transitionKernel (ReachableFrom L K init)
    (reachableFrom_kernel_closed init) c₀ hc₀Reach hDone
    (fun x hx _ => hDoneAbs x hx)
    (∑ i, (phases i).t) (2 * Brecover) (by omega : 2 * Brecover ≠ 0)
    (1 / n : ℝ≥0∞) (Brecover : ℝ≥0∞)
    (by exact_mod_cast (ENNReal.natCast_ne_top Brecover))
    (by omega : 0 < 2 * Brecover)
    (by rw [hsRecCast]; exact le_of_eq (mul_comm (Brecover : ℝ≥0∞) 2))
    hfail
    (fun b hbR hbBad => hRecoverReach b hbR hbBad)
  -- assemble: Tgood + recovery tail ≤ (21·C0 + 4·Cbad)·n·(L+1).
  calc expectedHitting (NonuniformMajority L K).transitionKernel c₀ (StableDone L K init)
      ≤ ((∑ i, (phases i).t : ℕ) : ℝ≥0∞)
          + (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := hsplit
    _ ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
          + ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) :=
        add_le_add (by exact_mod_cast hT) hrecmass
    _ = (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by push_cast; ring

end ExactMajority
