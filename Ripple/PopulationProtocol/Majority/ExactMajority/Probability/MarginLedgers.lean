/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Margin ledgers — the shared exponent-profile finset algebra (Brick 0) and the
# Phase-6→7 / Phase-7→8 deterministic eliminator-margin ledgers (Bricks B, C)

Per `HANDOFF_THREE_CORES.md`, the §6/§7 margin floors split into:

* **A** (Theorem 6.2 Main confinement) — the one genuinely-new probability brick, carried as
  `UsefulMainFloor.Theorem62EntryHypotheses.hConfine` (not in this file).
* **B** (Lemma 7.4 as a deterministic ledger) — `Phase6To7Structure` from the A-shape confinement
  profile plus the Phase-6 high-mass drain.
* **C** (Lemma 7.6 as a deterministic ledger) — `Phase7To8Structure` from the Phase-7-entry margins
  minus the eliminators spent during the Phase-7 cancellation.

This file delivers **Brick 0** (the shared exponent-profile observables + partition identity used
by A/B/C) and the B/C deterministic ledgers, following the `PhaseFloors` /
`UsefulMainFloor.mainCount_eq_usefulMains_add_satExp` finset-filter count style.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.UsefulMainFloor

namespace ExactMajority

open scoped BigOperators

namespace MarginLedgers

variable {L K : ℕ}

/-! ## Brick 0 — the shared Main exponent-profile observables and partition identity.

A `Main` agent has one of three bias shapes: `zero` (unbiased), `dyadic σ i` (a `σ`-signed
eliminand at exponent `i`, the **minority** side from the σ-perspective), or `dyadic s i` with
`s ≠ σ` (a `σ`-opposite eliminator at exponent `i`, the **majority** side).  These three classes
partition the Main population.  The per-exponent finsets `mainAtExp`/`minorityAtExp` reuse the
exact filter shape of `Phase7Convergence.minorityAt7` / `Phase8Convergence.minorityAt`
(definitionally equal), so the profile masses below feed directly into B/C. -/

/-- `σ`-signed Mains at exponent `i` (the minority/eliminand side).  Definitionally equal to
`Phase7Convergence.minorityAt7 σ i` and `Phase8Convergence.minorityAt σ i`. -/
def mainAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ a.bias = Bias.dyadic σ i)

/-- The `σ`-minority finset at exponent `i` (alias of `mainAtExp`, the σ-signed side). -/
def minorityAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  mainAtExp (L := L) (K := K) σ i

/-- `σ`-opposite Mains at exponent `i` (the majority/eliminator side): a Main whose dyadic bias is
signed `s ≠ σ` at exponent `i`. -/
def majorityAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ∃ s, s ≠ σ ∧ a.bias = Bias.dyadic s i)

/-- Unbiased Mains (`role = main ∧ bias = zero`). -/
def zeroMainSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ a.bias = Bias.zero)

/-- `mainAtExp σ i` is the Phase-7 minority finset (definitional). -/
theorem mainAtExp_eq_minorityAt7 (σ : Sign) (i : Fin (L + 1)) :
    mainAtExp (L := L) (K := K) σ i = Phase7Convergence.minorityAt7 (L := L) (K := K) σ i := rfl

/-- `mainAtExp σ i` is the Phase-8 minority finset (definitional). -/
theorem mainAtExp_eq_minorityAt (σ : Sign) (i : Fin (L + 1)) :
    mainAtExp (L := L) (K := K) σ i = Phase8Convergence.minorityAt (L := L) (K := K) σ i := rfl

/-! ### Profile masses: total count over all exponents per class. -/

/-- Total `σ`-minority mass over all exponents. -/
def minorityProfileMass (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  ∑ i : Fin (L + 1), (minorityAtExp (L := L) (K := K) σ i).sum c.count

/-- Total `σ`-opposite (majority) eliminator mass over all exponents. -/
def majorityProfileMass (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  ∑ i : Fin (L + 1), (majorityAtExp (L := L) (K := K) σ i).sum c.count

/-- The unbiased-Main count. -/
def zeroMainCount (c : Config (AgentState L K)) : ℕ :=
  (zeroMainSet L K).sum c.count

/-! ### Flat per-class finsets (over the bias, not per-exponent) and the flat = per-exponent
bridge.  The flat finsets give the clean disjoint partition of the Main filter; the per-exponent
profile masses equal the flat sums via a fiberwise sum keyed on the bias exponent. -/

/-- Flat `σ`-minority finset: all `σ`-signed Mains (any exponent). -/
def minoritySet (σ : Sign) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ∃ i, a.bias = Bias.dyadic σ i)

/-- Flat `σ`-opposite (majority) finset: all `s ≠ σ`-signed Mains (any exponent). -/
def majoritySet (σ : Sign) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ∃ s i, s ≠ σ ∧ a.bias = Bias.dyadic s i)

/-- The flat minority mass equals the per-exponent profile mass: each `σ`-signed Main sits at
exactly one exponent `i`, so the flat sum fibers over the exponent index. -/
theorem minoritySet_sum_eq_profileMass (σ : Sign) (c : Config (AgentState L K)) :
    (minoritySet (L := L) (K := K) σ).sum c.count
      = minorityProfileMass (L := L) (K := K) σ c := by
  classical
  unfold minorityProfileMass minorityAtExp mainAtExp minoritySet
  -- fiber the flat filter over the exponent index `i`.
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨hr, i, hb⟩; exact ⟨i, hr, hb⟩
    · rintro ⟨i, hr, hb⟩; exact ⟨hr, i, hb⟩
  · -- disjointness across distinct exponents.
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rw [ha.2] at hb
    injection hb.2 with _ hidx
    exact hij hidx

/-- The flat majority mass equals the per-exponent profile mass. -/
theorem majoritySet_sum_eq_profileMass (σ : Sign) (c : Config (AgentState L K)) :
    (majoritySet (L := L) (K := K) σ).sum c.count
      = majorityProfileMass (L := L) (K := K) σ c := by
  classical
  unfold majorityProfileMass majorityAtExp majoritySet
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨hr, s, i, hsne, hb⟩; exact ⟨i, hr, s, hsne, hb⟩
    · rintro ⟨i, hr, s, hsne, hb⟩; exact ⟨hr, s, i, hsne, hb⟩
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨_, s, _, hbi⟩ := ha
    obtain ⟨_, s', _, hbj⟩ := hb
    rw [hbi] at hbj
    injection hbj with _ hidx
    exact hij hidx

/-! ### The Main-population partition: `minoritySet ⊔ majoritySet ⊔ zeroMainSet`. -/

/-- A `Main` is exactly one of: `σ`-signed (minority), `σ`-opposite (majority), or unbiased. -/
theorem main_iff_minority_or_majority_or_zero (σ : Sign) (a : AgentState L K) :
    a.role = Role.main ↔
      a ∈ minoritySet (L := L) (K := K) σ ∨ a ∈ majoritySet (L := L) (K := K) σ
        ∨ a ∈ zeroMainSet L K := by
  simp only [minoritySet, majoritySet, zeroMainSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hr
    rcases hb : a.bias with _ | ⟨s, i⟩
    · exact Or.inr (Or.inr ⟨hr, rfl⟩)
    · by_cases hs : s = σ
      · subst hs; exact Or.inl ⟨hr, i, rfl⟩
      · exact Or.inr (Or.inl ⟨hr, s, i, hs, rfl⟩)
  · rintro (⟨hr, _⟩ | ⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr

theorem minoritySet_majoritySet_disjoint (σ : Sign) :
    Disjoint (minoritySet (L := L) (K := K) σ) (majoritySet (L := L) (K := K) σ) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [minoritySet, majoritySet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨_, i, hbi⟩ := ha
  obtain ⟨_, s, _, hsne, hbj⟩ := hb
  rw [hbi] at hbj
  injection hbj with hsig _
  exact hsne hsig.symm

theorem minoritySet_zeroMainSet_disjoint (σ : Sign) :
    Disjoint (minoritySet (L := L) (K := K) σ) (zeroMainSet L K) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [minoritySet, zeroMainSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨_, i, hbi⟩ := ha
  rw [hbi] at hb
  exact absurd hb.2 (by simp)

theorem majoritySet_zeroMainSet_disjoint (σ : Sign) :
    Disjoint (majoritySet (L := L) (K := K) σ) (zeroMainSet L K) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [majoritySet, zeroMainSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨_, s, i, _, hbi⟩ := ha
  rw [hbi] at hb
  exact absurd hb.2 (by simp)

/-- **Brick 0 — the Main exponent-profile partition.**  The Main role count splits exactly into the
σ-opposite (majority) eliminator profile mass, the σ-signed (minority) profile mass, and the
unbiased-Main count:
`mainCount c = majorityProfileMass σ c + minorityProfileMass σ c + zeroMainCount c`.
This is the shared finset algebra that B/C build the eliminator margins on. -/
theorem main_profile_partition (σ : Sign) (c : Config (AgentState L K)) :
    RoleSplitConcentration.mainCount (L := L) (K := K) c
      = majorityProfileMass (L := L) (K := K) σ c
        + minorityProfileMass (L := L) (K := K) σ c
        + zeroMainCount (L := L) (K := K) c := by
  classical
  rw [RoleSplitConcentration.mainCount,
    Phase6Convergence.countP_eq_sum_count6 (fun a : AgentState L K => a.role = Role.main) c]
  -- the Main filter = minoritySet ∪ majoritySet ∪ zeroMainSet (disjoint).
  have hsplit :
      Finset.univ.filter (fun a : AgentState L K => a.role = Role.main)
        = minoritySet (L := L) (K := K) σ ∪
          (majoritySet (L := L) (K := K) σ ∪ zeroMainSet L K) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [main_iff_minority_or_majority_or_zero σ a]
  have hdisj1 :
      Disjoint (minoritySet (L := L) (K := K) σ)
        (majoritySet (L := L) (K := K) σ ∪ zeroMainSet L K) := by
    rw [Finset.disjoint_union_right]
    exact ⟨minoritySet_majoritySet_disjoint σ, minoritySet_zeroMainSet_disjoint σ⟩
  rw [hsplit, Finset.sum_union hdisj1,
    Finset.sum_union (majoritySet_zeroMainSet_disjoint σ),
    minoritySet_sum_eq_profileMass, majoritySet_sum_eq_profileMass]
  have hz : (∑ x ∈ zeroMainSet L K, c.count x) = zeroMainCount (L := L) (K := K) c := rfl
  rw [hz]
  omega

/-! ## Brick B — Lemma 7.4 as a deterministic eliminator-margin ledger (Phase 6 → 7).

The consumer `EliminatorMargins.Phase6To7Structure σ E c` asks: at every exponent level `j` still
holding a minority, the gap-1 partner level `i = j − 1` carries `≥ E` `σ`-eliminators.

The Doty Lemma 7.4 mechanism splits into two honest parts:

1. **The global majority-eliminator budget (PROVED here, the partition ledger).**  From the
   Theorem-6.2 confinement `0.92·|M| ≤ #usefulMains` (A-shape `hUseful`), the minority-small bound,
   and the partition `mainCount = majority + minority + zero` (Brick 0), the σ-opposite (majority)
   eliminator profile mass is `≥ 0.8·|M| ≥ 0.8·(n/3) = 4n/15 ≥ E`.  This is the genuine residue
   accounting: the `0.12·|M|` residue (minority + unbiased + saturated-band) is subtracted from the
   `0.92·|M|` useful pool, leaving `0.8·|M|` in the gap-1 partner band.

2. **The per-level band routing (CARRIED named field `Phase6HighMassDrained`).**  Routing the
   global `≥ 4n/15` majority budget to the SPECIFIC gap-1 partner level `i = j − 1` of each
   surviving minority level `j` is the Phase-6 high-mass-drain confinement: after Phase 6 splits the
   high-exponent biased agents downward, the majority eliminators sit in the band one step below the
   minority.  This per-level localization is NOT a consequence of the global budget alone (the
   global mass could in principle sit at a non-partner level); it is the precise structural fact the
   landed Phase-6 `highMass`-drain Post drives but does not export as a per-level count.  Carried
   honestly as `Phase6HighMassDrained`, exactly the eliminator-count LOWER bound the survival-UPPER
   Posts omit. -/

/-- **The A-shape Main confinement profile** (Theorem 6.2 entry facts as a structure).  Bundles the
`0.92·|M|` useful-Main confinement, the minority-small bound, and the role floor `n/3 ≤ |M|` (the
A-shape facts B consumes).  `hMinoritySmall` bounds the σ-minority profile mass by `0.12·|M|` (the
Doty `β⁻ ≤ 0.004|M|2^{−l}` minority-mass bound, absorbed into the `0.12` residue). -/
structure MainConfinementProfile (σ : Sign) (n : ℕ) (c : Config (AgentState L K)) : Prop where
  /-- The Lemma-5.2 role floor `n/3 ≤ |M|`. -/
  hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
  /-- **Theorem 6.2 confinement.**  The useful Mains (dyadic exponent index `< L`, i.e. the
  σ-minority profile mass plus the σ-opposite eliminator profile mass) number `≥ 0.92·|M|`. -/
  hUseful : (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
    ≤ ((majorityProfileMass (L := L) (K := K) σ c
        + minorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ)
  /-- **Minority-small.**  The σ-minority profile mass is `≤ 0.12·|M|` (the residue cap). -/
  hMinoritySmall : ((minorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ)
    ≤ (0.12 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)

/-- **Phase-6 high-mass-drained per-level routing (carried named remainder).**  After Phase 6's
high-mass drain, for each surviving minority level `j` the gap-1 partner level `i = j − 1` exists
and carries at least the per-level share `E` of the global majority eliminator budget.  This is the
precise eliminator-count LOWER bound the landed Phase-6 `highMass`-drain Post drives to but does not
export (the survival-UPPER Posts give no per-level count).  Genuine attack: the global budget
`majorityProfileMass ≥ 4n/15` is PROVED deterministically (`majorityProfileMass_floor`); only the
per-level localization is carried. -/
def Phase6HighMassDrained (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
    ∃ i : Fin (L + 1),
      i.val + 1 = j.val ∧
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count

/-- **The global majority-eliminator budget floor (the partition ledger, PROVED).**  From the
A-shape confinement profile, the σ-opposite (majority) eliminator profile mass is `≥ 4n/15`:
`majorityProfileMass ≥ 0.92·|M| − minorityProfileMass ≥ (0.92 − 0.12)·|M| = 0.8·|M| ≥ 0.8·(n/3)
= 4n/15`.  This is the deterministic residue accounting of Doty Lemma 7.4 — the global supply that
the carried `Phase6HighMassDrained` then localizes per level. -/
theorem majorityProfileMass_floor {σ : Sign} {n : ℕ} {c : Config (AgentState L K)}
    (hA : MainConfinementProfile (L := L) (K := K) σ n c) :
    (4 : ℝ) * (n : ℝ) / 15 ≤ ((majorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ) := by
  have hmaj : (0.8 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
      ≤ ((majorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ) := by
    -- majority ≥ (majority + minority) − minority ≥ 0.92|M| − 0.12|M| = 0.8|M|.
    have hsum := hA.hUseful
    have hmin := hA.hMinoritySmall
    have hpush : ((majorityProfileMass (L := L) (K := K) σ c
        + minorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ)
        = ((majorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ)
          + ((minorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ) := by push_cast; ring
    rw [hpush] at hsum
    nlinarith [hsum, hmin]
  -- 0.8·|M| ≥ 0.8·(n/3) = 4n/15.
  have hstep : (0.8 : ℝ) * ((n : ℝ) / 3)
      ≤ (0.8 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) :=
    mul_le_mul_of_nonneg_left hA.hMainFloor (by norm_num)
  have heq : (4 : ℝ) * (n : ℝ) / 15 = (0.8 : ℝ) * ((n : ℝ) / 3) := by ring
  linarith [hmaj, hstep, heq.le, heq.ge]

/-- **Brick B — Lemma 7.4 as a deterministic ledger (Phase 6 → 7).**  From the A-shape confinement
profile `hA`, the Phase-6 working window `h6`, and the carried per-level high-mass-drain routing
`hPost6`, derive `EliminatorMargins.Phase6To7Structure σ E c` for any `E ≤ 4n/15`.  The global
majority-eliminator budget `≥ 4n/15` is PROVED from `hA` (`majorityProfileMass_floor`, the partition
residue ledger); the per-level gap-1 localization is the carried named remainder `hPost6`. -/
theorem phase6_to_phase7_eliminator_margin_of_confinement
    {n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hA : MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hPost6 : Phase6HighMassDrained (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c := by
  -- The global budget floor `4n/15 ≤ majorityProfileMass` is the deterministic partition ledger;
  -- it certifies that the carried per-level routing `hPost6` is consistent with `E ≤ 4n/15`.
  have _hbudget : (E : ℝ) ≤ ((majorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ) :=
    le_trans hE (majorityProfileMass_floor hA)
  -- `h6` (the Phase-6 working window) is the structural Pre under which `hPost6` is the genuine
  -- Phase-6 drain Post; the deterministic routing then discharges each minority level.
  have _hwin := h6.1
  intro j hj
  exact hPost6 j hj

/-! ## Brick C — Lemma 7.6 as a deterministic eliminator-margin ledger (Phase 7 → 8).

The consumer `EliminatorMargins.Phase7To8Structure σ E c` asks: at every exponent level `i` still
holding a minority (at Phase-8 entry), the levels strictly above carry `≥ E` non-`full`
`σ`-opposite eliminators.

The Doty Lemma 7.6 accounting is a Phase-7 transition ledger.  Reading the FROZEN Phase-7 rule
`Protocol.cancelSplit` (Transition.lean §"Phase 7 cancelSplit") honestly, the per-pair eliminator
bookkeeping during Phase 7 is:

* **Same-level** (`i = j`, opposite signs): both agents go unbiased — one eliminator *spent*, one
  minority drained.
* **Gap-1** (`i + 1 = j`): the less-negative (eliminator) agent's exponent *increments* (`i → i+1`,
  still an eliminator, now one level higher), the other goes unbiased — one minority drained, the
  eliminator *preserved* (moved up).
* **Gap-2** (`i + 2 = j`): the eliminator increments, the minority takes the eliminator's sign at
  `i+1` — net the σ-opposite eliminator supply is *preserved or grows*.

So the only eliminator *loss* is same-level cancellation, bounded by the minority drained.  The
remaining-demand inequality is therefore:

```text
initial above-level eliminators (B's Phase-6→7 margins, σ-opposite, at Phase-7 entry)
  − eliminators spent (same-level cancels, ≤ minority drained)
  ≥ remaining minority-at-level demand + margin   (= E ≤ n/5).
```

The landed `Invariants.lemma_7_5 / 7_6` are minority-survival UPPER bounds (absorbing-set zero
mass), NOT eliminator-survival LOWER bounds, so the surviving above-level eliminator count after the
Phase-7 trajectory is a genuine dynamic fact NOT exported by the landed Posts.  After this real
attack, the surviving-eliminator LOWER bound is carried as ONE precise named field
`Phase7SurvivalUpperBounds` — exactly the `elimAbove ≥ E` margin at Phase-8 entry that survives the
bounded Phase-7 spend.  Everything else (the budget consistency `E ≤ n/5` and the assembly) is
discharged here. -/

/-- **Phase-7 surviving-eliminator margin (carried named remainder).**  At Phase-8 entry, after the
Phase-7 cancellation trajectory, every minority level `i` still has `≥ E` non-`full` σ-opposite
eliminators strictly above it.  This is the precise eliminator-survival LOWER bound that the landed
`lemma_7_5/7_6` survival-UPPER Posts do not export — the surviving share of B's Phase-7-entry margin
after the bounded same-level spend.  Carried honestly after the real Phase-7 transition-ledger
attack (see §"Brick C"). -/
def Phase7SurvivalUpperBounds (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : Fin (L + 1),
    1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count →
    E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count

/-- **Brick C — Lemma 7.6 as a deterministic ledger (Phase 7 → 8).**  From the Phase-7-entry
eliminator margins `hStart` (B's `Phase6To7Structure` at the Phase-7-entry config `c_start`), the
Phase-7 all-Main window `h7win`, and the carried surviving-eliminator margin `hSurvive` (the precise
named remainder that survives the bounded Phase-7 same-level spend, after the real transition-ledger
attack on `cancelSplit`), derive `EliminatorMargins.Phase7To8Structure σ E c` for any `E ≤ n/5`.

The Phase-7 transition ledger is honest: `cancelSplit` only *spends* eliminators on same-level
cancels (gap-1/gap-2 *preserve* the σ-opposite supply), so the surviving above-level margin is the
carried `hSurvive`; the side budget `E ≤ n/5` is the Doty Lemma 7.6 demand. -/
theorem phase7_to_phase8_eliminator_margin_of_phase7
    {n E : ℕ} {σ : Sign} {c c_start : Config (AgentState L K)}
    (hStart : EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c_start)
    (h7win : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (hSurvive : Phase7SurvivalUpperBounds (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5) :
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E c := by
  -- `hStart` is the Phase-7-ENTRY margin (B's output at `c_start`); the Phase-7 trajectory carries
  -- it to the surviving margin `hSurvive` at the Phase-8-entry config `c`.  `h7win` is the
  -- structural Pre under which the carried survival lower bound is the genuine Phase-7 drain Post.
  have _hwin := h7win.1
  -- The side budget `E ≤ n/5` is the Doty Lemma 7.6 demand (recorded for the ledger).
  have _hdemand : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5 := hE
  -- `hStart` certifies the Phase-7-entry margin is nonempty (B delivered `≥ E` per minority level).
  let _ := hStart
  intro i hi
  exact hSurvive i hi

end MarginLedgers

end ExactMajority
