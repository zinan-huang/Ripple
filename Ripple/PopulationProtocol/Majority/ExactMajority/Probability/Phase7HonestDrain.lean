/-
# Phase-7 honest drain — the F3 fix (audit finding F3).

The independent adversarial audit (F3) flagged that the Part-I Phase-7 surface
`Phase7Convergence.phase7Convergence'` carries

  `hmono : PotNonincrOn Inv7Sum K minorityU`

— a *deterministic* per-step non-increase of the minority **count** `minorityU σ`
along the kernel — as an honest-but-FALSE hypothesis.  The campaign's OWN proven
lemma `Phase7Convergence.gap2_minorityU_rise_compatible_with_pos_sum` exhibits a gap-2
opposite-sign `cancelSplit` step that *raises* `minorityU σ` by exactly `1` while
CONSERVING the signed sum — so on an `Inv7Sum`-compatible configuration the kernel can
strictly INCREASE `minorityU σ`.  Hence `PotNonincrOn Inv7Sum K minorityU` is FALSE,
and every consumer downstream of that carried `hmono` is conditionally vacuous.

This file delivers the HONEST fix, append-only, importing only the already-built
`Phase7Convergence` surface (no edits to existing files).

## The honest engine: count → mass

The relay-5 obstruction is to the minority *count*.  Doty §6's actual `|B|`-control
rests on the σ-class **mass** `classMass σ` (the `2^L`-scaled total dyadic mass of the
σ-signed Mains), which DROPS in the very gap-2 branch where the count rises:

* gap-2 opposite-sign: count `+1`, mass `−2^{L−(i+2)} < 0`  (the divergence).
* every other branch: count `≤`, mass `≤`.

So `classMassN σ := (classMass σ).toNat` is the honest one-sided potential — genuinely
non-increasing along the kernel from any `Inv7Sum`-state (`potNonincrOn_classMassN`,
PROVED INTERNAL in `Phase7Convergence`, NO index-ordering hypothesis), with
`{classMassN σ = 0} ⊆ NoMinority σ` (`minorityU_eq_zero_of_classMassN_zero`).

## What this file contributes

1. The honest per-pair RISE/DROP ledger, restated as a clean named surface:
   * `gap2_count_rises_exactly_one_mass_drops` — the count `+1` / mass strict-drop
     divergence on the gap-2 opposite-sign pair (the F3 witness, per-pair).
   * `classMass_pair_noincr` — the universal per-pair mass non-increase (every branch).
2. The F3 falsity, made a THEOREM:
   * `false_hmono_forbids_gap2_rise` — ANY `PotNonincrOn Inv7Sum K minorityU` would force
     the gap-2-rise successor to carry zero kernel mass; so the carried `hmono` cannot
     coexist with a kernel that actually fires the (signed-sum-conserving) gap-2 pair.
3. The honest replacement surface, with `hmono` REPLACED:
   * `phase7HonestDrain` — the Phase-7 `PhaseConvergenceW` with `hClosed`
     (= `invClosed_Inv7Sum`) and `hmono` (= `potNonincrOn_classMassN`) BOTH proved
     internal; only the σ-class-MASS drain `hstep` carried.  Post ⟹ `NoMinority σ`.
   * `phase7HonestDrain_post_noMinority` — the re-wired post bridge: the honest engine's
     `Post` delivers exactly the count target `minorityU σ = 0` that the false-`hmono`
     chain advertised, with no false hypothesis in the path.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence

namespace ExactMajority
namespace Phase7HonestDrain

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

/-! ## Part 1 — the honest per-pair RISE/DROP ledger.

The single fact at the heart of F3: on a gap-2 opposite-sign Main pair, the protocol
`cancelSplit` raises the minority *count* by exactly `1` but drops the σ-class *mass*.
The two halves are separately proved in `Phase7Convergence`; here they are bound into
one named ledger so the divergence (`count ↑`, `mass ↓`) is a single citable statement —
this is precisely the configuration on which `PotNonincrOn Inv7Sum K minorityU` fails. -/

/-- **The F3 divergence, per pair.**  On a gap-2 opposite-sign Main pair
(`s` the σ-minority Main at smaller index `i`, `t` the σ.flip Main at `j = i+2`),
`cancelSplit`:
* RAISES the minority *count* on the pair by exactly `1`
  (`countP minoritySt + 1 ≤ countP minoritySt (after)`), and
* DROPS (non-strictly here; strictly in the dedicated gap-1 drain) the σ-class *mass*
  on the pair (`classMass (after) ≤ classMass (before)`),
while CONSERVING the signed mass.  The count rise is what kills any
`PotNonincrOn _ K minorityU`; the mass non-increase is the honest engine potential. -/
theorem gap2_count_rises_exactly_one_mass_drops
    (σ st : Sign) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic σ i)
    (htb : t.bias = Bias.dyadic st j) (hss : σ ≠ st) (hg2 : i.val + 2 = j.val) :
    -- minority COUNT rises by ≥ 1 on the pair
    (Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
          ({(cancelSplit L K s t).1,
            (cancelSplit L K s t).2} : Multiset (AgentState L K)))
    -- σ-class MASS does NOT rise on the pair
    ∧ (Phase7Convergence.agentClassMass σ (cancelSplit L K s t).1
        + Phase7Convergence.agentClassMass σ (cancelSplit L K s t).2
      ≤ Phase7Convergence.agentClassMass σ s + Phase7Convergence.agentClassMass σ t)
    -- signed mass CONSERVED
    ∧ (Phase7Convergence.agentSignedMass (cancelSplit L K s t).1
        + Phase7Convergence.agentSignedMass (cancelSplit L K s t).2
      = Phase7Convergence.agentSignedMass s + Phase7Convergence.agentSignedMass t) := by
  obtain ⟨hrise, hsum⟩ :=
    Phase7Convergence.gap2_minorityU_rise_compatible_with_pos_sum
      σ st s t hsM htM i j hsb htb hss hg2
  exact ⟨hrise, Phase7Convergence.cancelSplit_classMass_pair_le σ s t, hsum⟩

/-- **The universal per-pair mass non-increase** (every `cancelSplit` branch, no
index-ordering hypothesis): the honest one-sided potential's defining inequality.  This
is the per-pair fact that lifts (via `classMass_stepOrSelf_le` /
`classMass_support_le`) to the config-level non-increase that becomes `hmono`. -/
theorem classMass_pair_noincr (σ : Sign) (s t : AgentState L K) :
    Phase7Convergence.agentClassMass σ (cancelSplit L K s t).1
        + Phase7Convergence.agentClassMass σ (cancelSplit L K s t).2
      ≤ Phase7Convergence.agentClassMass σ s + Phase7Convergence.agentClassMass σ t :=
  Phase7Convergence.cancelSplit_classMass_pair_le σ s t

/-! ## Part 2 — the F3 falsity, made a theorem.

`PotNonincrOn Inv7Sum K minorityU` says: from any `Inv7Sum`-state `b`, the kernel mass on
`{x | minorityU σ b < minorityU σ x}` is `0`.  The honest replacement does not rely on
any such hypothesis; to certify that the audit finding is REAL (not just "honestly
named") we record that the hypothesis is incompatible with the kernel actually placing
positive mass on a count-raising successor.  Concretely: if some `Inv7Sum`-state `b`
admits a successor `c'` in the kernel support with `minorityU σ b < minorityU σ c'`
(exactly the gap-2 rise), then the carried `hmono` is contradicted. -/

/-- **The carried `hmono` forbids any count-raising reachable successor.**  Unfolding
`PotNonincrOn`: a `PotNonincrOn Inv7Sum K minorityU` proof would force the kernel mass on
the count-raising set to vanish; combined with a witnessed support member that raises the
count it yields `False`.  This is the precise sense in which the Part-I
`phase7Convergence'` `hmono` is FALSE-on-reachable: the gap-2 opposite-sign fire is a
genuine kernel-support successor that raises `minorityU σ`. -/
theorem false_hmono_forbids_gap2_rise (σ : Sign) (n : ℕ)
    (hmono : OneSidedCancel.PotNonincrOn
      (fun c => Phase7Convergence.Inv7Sum (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel
      (fun c => Phase7Convergence.minorityU σ c))
    (b c' : Config (AgentState L K))
    (hb : Phase7Convergence.Inv7Sum n b)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf b).support)
    (hrise : Phase7Convergence.minorityU σ b < Phase7Convergence.minorityU σ c') :
    False := by
  classical
  -- `hmono b hb` says the kernel mass on the count-raising set is 0; but `c'` is a
  -- support member of that very set, so the mass cannot be 0.
  have hzero := hmono b hb
  -- transitionKernel b = stepDistOrSelf b (as a measure).
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  rw [hKb,
    PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.disjoint_left] at hzero
  exact hzero hsupp (by
    simp only [Set.mem_setOf_eq]; exact hrise)

/-! ## Part 3 — the honest replacement surface (`hmono` REPLACED).

`phase7HonestDrain` is the Phase-7 cancellation `PhaseConvergenceW` with the FALSE
`minorityU`-`hmono` removed entirely: `hmono = potNonincrOn_classMassN σ n` (PROVED) and
`hClosed = invClosed_Inv7Sum n` (PROVED) are both internal, and the ONLY carried input is
the σ-class-MASS drain `hstep` (the Doty Lemma 7.4/7.5 mass floor).  This is exactly the
already-built `Phase7Convergence.phase7Convergence''` — re-exposed here under the F3
name, with the post-bridge that delivers the count target the false chain advertised. -/

/-- **The honest Phase-7 `PhaseConvergenceW`** (F3 fix).  `Pre = Inv7Sum n ∧ classMassN
σ ≤ M₀`, `Post = Inv7Sum n ∧ classMassN σ = 0`.  `hClosed` and `hmono` are BOTH proved
internal (`invClosed_Inv7Sum` / `potNonincrOn_classMassN`); the FALSE `minorityU` count
non-increase is gone.  Only the σ-class-mass drain `hstep` is carried. -/
noncomputable def phase7HonestDrain (σ : Sign) (n : ℕ)
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Phase7Convergence.Inv7Sum n b →
      1 ≤ Phase7Convergence.classMassN σ b →
      ((NonuniformMajority L K).transitionKernel b)
        (OneSidedCancel.potDone (fun c => Phase7Convergence.classMassN σ c))ᶜ ≤ q)
    (M₀ t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase7Convergence.phase7Convergence'' σ n q hstep M₀ t ε hε

/-- **The re-wired post bridge.**  The honest engine's `Post`
(`Inv7Sum n ∧ classMassN σ = 0`) delivers the genuine Phase-7 count target
`minorityU σ = 0` (`NoMinority σ`) — exactly the conclusion the false-`hmono`
`phase7Convergence'` chain advertised, now reached with the FALSE hypothesis removed
from the path. -/
theorem phase7HonestDrain_post_noMinority (σ : Sign) (n : ℕ)
    (c : Config (AgentState L K))
    (hpost : Phase7Convergence.Inv7Sum n c ∧ Phase7Convergence.classMassN σ c = 0) :
    Phase7Convergence.NoMinority σ c :=
  Phase7Convergence.minorityU_eq_zero_of_classMassN_zero σ c hpost.2

/-- **`hmono` discharged internally** (the F3 replacement, isolated).  The σ-class mass
`classMassN σ` is non-increasing along the kernel from any `Inv7Sum`-state — the honest
substitute for the false `PotNonincrOn Inv7Sum K minorityU`.  Re-exported here so the
re-wiring is a single citable fact. -/
theorem honest_hmono (σ : Sign) (n : ℕ) :
    OneSidedCancel.PotNonincrOn
      (fun c => Phase7Convergence.Inv7Sum (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel
      (fun c => Phase7Convergence.classMassN σ c) :=
  Phase7Convergence.potNonincrOn_classMassN σ n

/-- **`hClosed` discharged internally** (re-exported).  `Inv7Sum` is genuinely one-step
closed under the real kernel (conserved signed sum + closed all-Main window) — the
`hClosed` the broken `MinorityHiIdx`-version could never supply. -/
theorem honest_hClosed (n : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase7Convergence.Inv7Sum (L := L) (K := K) n c) :=
  Phase7Convergence.invClosed_Inv7Sum n

end Phase7HonestDrain
end ExactMajority
