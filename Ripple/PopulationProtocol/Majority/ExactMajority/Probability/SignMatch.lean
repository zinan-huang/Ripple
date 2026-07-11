/-
# SignMatch — producing the conserved gap-sign-match residual `Atoms.Phase10SignMatch`.

This file is the *atom campaign first target*: it DISCHARGES the V3 surface's residual field
`hPhase10Sign : Atoms.Phase10SignMatch init` — the honest finding recorded in
`Atoms` (Part 2, F6 c) that `Phase10Post` does NOT pin the unanimous output `o` to the
init-gap sign.  The missing link is the conserved signed sum.

It is **append-only**: it edits NO existing file.  It imports `Atoms` (for `Phase10SignMatch`
/ `postOfSign`) and `BackupEntry` (for the chain-conserved quantity
`Phase10Backup.phase10ActiveSignedSum_eq_initialGap_of_reachable` and the arrival classification).
It defines only names in namespace `ExactMajority.SignMatch`.

## The honest mechanism (the survey)

`Atoms.Phase10SignMatch init` is `∀ c, Phase10Post c → phase10MajorityWitness init c`, where
`Phase10Post c = ∃ o, ∀ a ∈ c, phase = 10 ∧ output = o` (unanimous output, `o` UNPINNED) and the
witness demands `o = .A`/`.B`/`.T` for `gap >`/`<`/`= 0`.

The chain-conserved quantity is the backup signed sum
`phase10ActiveSignedSum c = (activeACount c) − (activeBCount c)`
(`Phase10Backup.phase10ActiveSignedSum_eq_activeACount_sub_activeBCount`), which equals
`initialGap init` on every reachable all-phase-10 state
(`Phase10Backup.phase10ActiveSignedSum_eq_initialGap_of_reachable`).  `signedContribution`
only counts ACTIVE (`full = true`) agents: active `A` `+1`, active `B` `−1`, everything else `0`.

So on a unanimous-output (`Phase10Post`) state the conserved sum is SIGN-LOCKED to `o`:

* `o = .A`  ⟹  no agent outputs `B`/`T`  ⟹  `activeBCount = 0`  ⟹  `signedSum = activeACount ≥ 0`;
* `o = .B`  ⟹  `activeACount = 0`  ⟹  `signedSum = −activeBCount ≤ 0`;
* `o = .T`  ⟹  `activeACount = activeBCount = 0`  ⟹  `signedSum = 0`.

Combined with `signedSum = gap`:

* `gap > 0`  ⟹  `o ≠ .B` (would force `gap ≤ 0`), `o ≠ .T` (`gap = 0`)  ⟹  `o = .A`  (left disjunct);
* `gap < 0`  ⟹  `o = .B`  (middle disjunct);
* `gap = 0`  ⟹  AMBIGUOUS from the sum alone: `o = .A` gives `activeACount = 0` (all `A` PASSIVE),
  which is `signedSum = 0` consistent — so the witness (which demands `o = .T`) is NOT forced.
  The genuine extra premise is `hasActiveAgent c`: the active agent outputs `o`, so it is an
  `IsActive{o}` source; if `o = .A`/`.B` then `activeACount`/`activeBCount ≥ 1`, forcing
  `gap = signedSum ≠ 0`, contradiction.  Hence `hasActiveAgent ⟹ o = .T` at `gap = 0`.

This is the SAME `hasActiveAgent` the landed `BackupEntry.allPhase10_tie_imp_Tie1plus` requires to
route the tie arrival into `Tie1plus`: the tie regime is genuinely a LIVENESS regime, and the
sign-match for the tie verdict is honest only on a still-active state.

## The deliverable

`phase10SignMatch_of_conservation`: from the per-`Phase10Post`-config conservation
(`signedSum c = gap`) PLUS per-config activity (`hasActiveAgent c`), produce
`Atoms.Phase10SignMatch init`.  Then `Atoms.postOfSign` turns it into `h_post`, and the V3
surface's `hPhase10Sign` field is PRODUCIBLE.  A reachability wrapper
`phase10SignMatch_of_reachable` supplies the conservation from
`phase10ActiveSignedSum_eq_initialGap_of_reachable` (so the only carried residual is the
per-config reachability + activity, exactly the honest content the correctness chain already owns).

## Discipline
Append-only; single-file `lake env lean`; `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`;
no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Atoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BackupEntry

namespace ExactMajority
namespace SignMatch

open Phase10Drop

variable {L K : ℕ}

/-! ## Part 1 — the unanimous-output counting locks.

On a `Phase10Post`-style unanimous-output config the off-output active counts vanish, because an
`IsActive{B}` / `IsActive{A}` / `IsActive{T}` source carries that very output, contradicting the
unanimity.  These are direct `Multiset.countP_eq_zero` facts. -/

/-- **Unanimous-`A` ⟹ no active `B`.**  If every agent outputs `A`, then no agent is an active
`B` source, so `activeBCount c = 0`. -/
theorem activeBCount_zero_of_unanimousA {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.A) : activeBCount c = 0 := by
  rw [activeBCount, Multiset.countP_eq_zero]
  intro a ha hActB
  have : a.output = Output.A := hu a ha
  rw [hActB.2] at this
  exact absurd this (by decide)

/-- **Unanimous-`B` ⟹ no active `A`.** -/
theorem activeACount_zero_of_unanimousB {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.B) : activeACount c = 0 := by
  rw [activeACount, Multiset.countP_eq_zero]
  intro a ha hActA
  have : a.output = Output.B := hu a ha
  rw [hActA.2] at this
  exact absurd this (by decide)

/-- **Unanimous-`T` ⟹ no active `A`.** -/
theorem activeACount_zero_of_unanimousT {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.T) : activeACount c = 0 := by
  rw [activeACount, Multiset.countP_eq_zero]
  intro a ha hActA
  have : a.output = Output.T := hu a ha
  rw [hActA.2] at this
  exact absurd this (by decide)

/-- **Unanimous-`T` ⟹ no active `B`.** -/
theorem activeBCount_zero_of_unanimousT {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.T) : activeBCount c = 0 := by
  rw [activeBCount, Multiset.countP_eq_zero]
  intro a ha hActB
  have : a.output = Output.T := hu a ha
  rw [hActB.2] at this
  exact absurd this (by decide)

/-! ## Part 2 — the signed-sum sign locks for unanimous-output configs.

`phase10ActiveSignedSum = activeACount − activeBCount` (`Phase10Backup`), so the off-output zero
counts above turn the conserved sum into a SIGN-LOCKED quantity of the unanimous output. -/

/-- **Unanimous-`A` ⟹ `0 ≤ signedSum`.**  `signedSum = activeACount − activeBCount = activeACount ≥ 0`. -/
theorem signedSum_nonneg_of_unanimousA {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.A) : 0 ≤ phase10ActiveSignedSum c := by
  rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount,
    activeBCount_zero_of_unanimousA hu]
  simp

/-- **Unanimous-`B` ⟹ `signedSum ≤ 0`.**  `signedSum = −activeBCount ≤ 0`. -/
theorem signedSum_nonpos_of_unanimousB {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.B) : phase10ActiveSignedSum c ≤ 0 := by
  rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount,
    activeACount_zero_of_unanimousB hu]
  simp

/-- **Unanimous-`T` ⟹ `signedSum = 0`.**  Both active counts vanish. -/
theorem signedSum_zero_of_unanimousT {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.T) : phase10ActiveSignedSum c = 0 := by
  rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount,
    activeACount_zero_of_unanimousT hu, activeBCount_zero_of_unanimousT hu]
  simp

/-! ## Part 3 — the active-agent positivity lock (the tie-disambiguator).

On a `Phase10Post`-`A` state WITH an active agent, that agent is an active `A` source, so
`activeACount ≥ 1` and the signed sum is STRICTLY positive — this is what excludes the
ambiguous `gap = 0 ∧ o = .A` (resp. `.B`) case, exactly the `hasActiveAgent` premise the landed
`BackupEntry.allPhase10_tie_imp_Tie1plus` consumes. -/

/-- **Unanimous-`A` + active agent ⟹ `0 < signedSum`.**  The active agent outputs `A`, so it is an
active-`A` source: `activeACount ≥ 1`, and (no active `B`) `signedSum = activeACount > 0`. -/
theorem signedSum_pos_of_unanimousA_active {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.A) (hact : hasActiveAgent c) :
    0 < phase10ActiveSignedSum c := by
  obtain ⟨a, ha, hfull⟩ := hact
  have hApos : 0 < activeACount c := by
    rw [activeACount, Multiset.countP_pos]
    exact ⟨a, ha, ⟨hfull, hu a ha⟩⟩
  rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount,
    activeBCount_zero_of_unanimousA hu]
  simpa using hApos

/-- **Unanimous-`B` + active agent ⟹ `signedSum < 0`.**  Mirror of the `A` case. -/
theorem signedSum_neg_of_unanimousB_active {c : Config (AgentState L K)}
    (hu : ∀ a ∈ c, a.output = Output.B) (hact : hasActiveAgent c) :
    phase10ActiveSignedSum c < 0 := by
  obtain ⟨a, ha, hfull⟩ := hact
  have hBpos : 0 < activeBCount c := by
    rw [activeBCount, Multiset.countP_pos]
    exact ⟨a, ha, ⟨hfull, hu a ha⟩⟩
  rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount,
    activeACount_zero_of_unanimousB hu]
  simpa using hBpos

/-! ## Part 4 — the per-config sign-match (`Phase10Post` ⟹ witness, under conservation + activity).

The core production: given the chain-conserved sum at `c` (`signedSum c = gap`) and an active agent,
the unanimous output is PINNED to the gap sign, producing `phase10MajorityWitness init c`.  The
`gap = 0` tie disambiguation is exactly where `hasActiveAgent` is consumed. -/

/-- **Per-config sign-match.**  A `Phase10Post` state `c` whose conserved signed sum equals the init
gap, and which still has an active agent, is a `phase10MajorityWitness`: the unanimous output matches
the gap sign.  This is `Atoms.Phase10SignMatch` pointwise — the honest production from the
chain-conserved quantity. -/
theorem witness_of_post_conservation {init c : Config (AgentState L K)}
    (hPost : Phase10Drop.Phase10Post (L := L) (K := K) c)
    (hcons : phase10ActiveSignedSum c = initialGap (L := L) (K := K) init)
    (hact : hasActiveAgent c) :
    phase10MajorityWitness (L := L) (K := K) init c := by
  obtain ⟨o, ho⟩ := hPost
  -- `ho a ha : a.phase.val = 10 ∧ a.output = o`; extract the two unanimities.
  have hphase : ∀ a ∈ c, a.phase.val = 10 := fun a ha => (ho a ha).1
  have hout : ∀ a ∈ c, a.output = o := fun a ha => (ho a ha).2
  -- Case on the gap sign and pin `o`.
  rcases lt_trichotomy (initialGap (L := L) (K := K) init) 0 with hneg | hzero | hpos
  · -- gap < 0 ⟹ o = .B (left/right disjuncts excluded by the sign locks).
    refine Or.inr (Or.inl ⟨hneg, ?_⟩)
    have ho_eq : o = Output.B := by
      rcases o with _ | _ | _
      · -- o = A: signedSum ≥ 0, but signedSum = gap < 0, contradiction.
        exact absurd (hcons ▸ signedSum_nonneg_of_unanimousA hout) (by omega)
      · rfl
      · -- o = T: signedSum = 0 ≠ gap < 0.
        exact absurd (hcons ▸ signedSum_zero_of_unanimousT hout) (by omega)
    intro a ha
    exact ⟨hphase a ha, ho_eq ▸ hout a ha⟩
  · -- gap = 0 ⟹ o = .T (the active-agent disambiguator excludes A and B).
    refine Or.inr (Or.inr ⟨hzero, ?_⟩)
    have ho_eq : o = Output.T := by
      rcases o with _ | _ | _
      · -- o = A + active ⟹ signedSum > 0, but = gap = 0.
        exact absurd (hcons ▸ signedSum_pos_of_unanimousA_active hout hact) (by omega)
      · -- o = B + active ⟹ signedSum < 0, but = gap = 0.
        exact absurd (hcons ▸ signedSum_neg_of_unanimousB_active hout hact) (by omega)
      · rfl
    intro a ha
    exact ⟨hphase a ha, ho_eq ▸ hout a ha⟩
  · -- gap > 0 ⟹ o = .A.
    refine Or.inl ⟨hpos, ?_⟩
    have ho_eq : o = Output.A := by
      rcases o with _ | _ | _
      · rfl
      · -- o = B: signedSum ≤ 0 ≠ gap > 0.
        exact absurd (hcons ▸ signedSum_nonpos_of_unanimousB hout) (by omega)
      · -- o = T: signedSum = 0 ≠ gap > 0.
        exact absurd (hcons ▸ signedSum_zero_of_unanimousT hout) (by omega)
    intro a ha
    exact ⟨hphase a ha, ho_eq ▸ hout a ha⟩

/-! ## Part 5 — the campaign atom: `phase10SignMatch_of_conservation`.

The whole-`init` production of `Atoms.Phase10SignMatch`, the field the V3 surface carries as
`hPhase10Sign`.  Two forms: the conservation/activity form (the honest atom), and the reachability
wrapper that derives the conservation from the landed chain-conservation theorem. -/

/-- **The campaign atom (conservation form).**  From per-`Phase10Post`-config conservation
(`signedSum c = gap`) and per-config activity (`hasActiveAgent c`), PRODUCE
`Atoms.Phase10SignMatch init`.  This discharges the V3 `hPhase10Sign` residual into the
chain-conserved signed sum plus the (tie-liveness) active-agent premise. -/
theorem phase10SignMatch_of_conservation {init : Config (AgentState L K)}
    (hcons : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      phase10ActiveSignedSum c = initialGap (L := L) (K := K) init)
    (hact : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c → hasActiveAgent c) :
    Atoms.Phase10SignMatch (L := L) (K := K) init :=
  fun c hPost => witness_of_post_conservation hPost (hcons c hPost) (hact c hPost)

/-- **The campaign atom (reachability form).**  The conservation is DERIVED from the landed chain
fact `Phase10Backup.phase10ActiveSignedSum_eq_initialGap_of_reachable`: on a reachable all-phase-10
state the conserved signed sum is the init gap.  `Phase10Post c` supplies the all-phase-10 premise.
The only carried residual is the per-`Phase10Post` reachability + activity — exactly the content the
correctness chain owns (`BackupEntry` consumes the same `validInitial`/`Reachable`/`hasActiveAgent`). -/
theorem phase10SignMatch_of_reachable {init : Config (AgentState L K)}
    (hinit : validInitial init)
    (hreach : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable init c)
    (hact : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c → hasActiveAgent c) :
    Atoms.Phase10SignMatch (L := L) (K := K) init := by
  refine phase10SignMatch_of_conservation (fun c hPost => ?_) hact
  obtain ⟨o, ho⟩ := hPost
  have hphase : ∀ a ∈ c, a.phase.val = 10 := fun a ha => (ho a ha).1
  exact phase10ActiveSignedSum_eq_initialGap_of_reachable (L := L) (K := K) init c hinit
    (hreach c ⟨o, ho⟩) hphase

/-! ## Part 6 — wiring through `Atoms.postOfSign` to `h_post`.

The end-to-end check: the produced `Phase10SignMatch` feeds `Atoms.postOfSign` to turn any
slot-20 `Phase10Post` into `majorityStableEndpoint`, which is exactly the `h_post` the V3 surface
needs.  Stated as a theorem so the production chain is closed in-file. -/

/-- **`h_post` PRODUCED from conservation.**  Composing the campaign atom with `Atoms.postOfSign`:
on any `Phase10Post` state, conservation + activity yield `majorityStableEndpoint init`.  This is the
`h_post` verdict of the V3 surfaces, derived (not freely binder'd) from the chain-conserved sum. -/
theorem post_of_conservation {init : Config (AgentState L K)}
    (hcons : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      phase10ActiveSignedSum c = initialGap (L := L) (K := K) init)
    (hact : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c → hasActiveAgent c)
    {c : Config (AgentState L K)} (hPost : Phase10Drop.Phase10Post (L := L) (K := K) c) :
    majorityStableEndpoint (L := L) (K := K) init c :=
  Atoms.postOfSign (phase10SignMatch_of_conservation hcons hact) hPost

end SignMatch
end ExactMajority
