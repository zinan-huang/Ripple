/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exporting the `AllBiasedMainAbove (l+1)` seed — the last brick of `MinorityFloorGap`'s verdict

`MinorityFloorGap.lean` settled the HONEST status of the carried `GapAlignment.MinorityAboveFloor`
residual: it is a *step-stable dynamic floor invariant*, seeded by `AllBiasedMainAbove (l+1) c` (every
biased Main at exponent index `≥ l+1`), preserved by the frozen `cancelSplit` Phase-7 transition, and
discharging `MinorityAboveFloor σ l c` for both signs.  What that file left OPEN is **the seed itself**:
where does `AllBiasedMainAbove (l+1)` come from at the Phase-7 entry?

This file (append-only; no existing file edited) answers that, and the answer is the cleanest possible:
**the seed is the LANDED Phase-6 high-mass drain run one level higher.**

## The parameterization audit (the load-bearing observation)

The entire Phase-6 drain machinery is *symbolic in the band level `l`*:

* `Phase6Convergence.phase6Convergence' l n hClosed q hdrop tWin M₀ ε hε` — `l : ℕ` is a free argument;
* its `Post c = Phase6Win n c ∧ highMass l c = 0`, read by `phase6Post_iff` as
  "every biased Main has index `≥ l`";
* the per-level drop floor `DrainThreading.phase6_hdrop_of_struct σ l n m hn hl1 hlL …` carries the
  level only through the side conditions `hl1 : 1 ≤ l`, `hlL : l ≤ L`, and a witness sampling hour
  `h : Fin (L+1)` with `hhgt : l - 1 < h.val`, `hhne : h.val ≠ L`;
* `DrainCalibration.phase6Convergence_calibrated l n M₀ q tWin …` — `l` free, budget `l`-agnostic.

So **instantiating the whole engine at `l+1` is a verbatim re-application at the bumped parameter** —
no new probability content.  The `Post` of the `l+1` instance is `highMass (l+1) c = 0`, which is, *by
the very `phase6Post_iff` that the verdict uses*, exactly `AllBiasedMainAbove (l+1) c`.  This is the
`phase6Post_iff` analogue the prompt asked for: `seedExport_of_post_succ` below.

## The honest budget arithmetic (does the drain run one more level?)

The level bump is FREE up to one structural side-condition.  For the `l+1` drain the band-top index is
`(l+1) - 1 = l`, and the witness sampling hour must satisfy `l < h.val` and `h.val ≠ L`, i.e.
`l < h.val < L`.  Such an `h` exists iff `l + 2 ≤ L`.  This is the genuine budget: the seed `l+1`
requires **two** free hours above the band floor (one for the band-top `l`, one strictly above as the
sampling reserve), where the bare Post `l` requires only one.  We expose this honestly as the explicit
hypothesis `hlL2 : l + 2 ≤ L` of the `l+1` drop-floor instance (`phase6_succ_hdrop_of_struct`).  When it
holds, the `l+1` engine is the landed engine, verbatim, at `l+1`.

This matches Doty §7: the drain pushes the σ-minority strictly BELOW the σ-majority band by clearing the
floor index `l` itself — the paper's "one notch" separation — and it is available exactly while the
clock has not yet saturated the top hour `L`.

## What this file delivers

1. **The `l+1` drain instance**, re-using the landed engine verbatim at the bumped parameter:
   * `phase6_succ_hdrop_of_struct` — the per-level `hdrop` for `highMass (l+1)` from the SAME structural
     reserve floor, with the budget side-condition `l + 2 ≤ L` made explicit (witness hour exists);
   * `phase6Convergence_succ` / `phase6Convergence_succ_calibrated` — the `phase6Convergence'` /
     `phase6Convergence_calibrated` engines instantiated at `l+1` (`l`-symbolic, hence definitional).
2. **The seed export** `AllBiasedMainAbove (l+1)` from the `l+1` `Post` (the `phase6Post_iff` analogue):
   `seedExport_of_post_succ`, and the `Post`-field reader `seed_of_phase6_succ_post`.
3. **The wired chain**: seed → `MinorityFloorGap.minorityAboveFloor_verdict` → the GapAlignment /
   BandLocalization consumers.  The seed both (a) WEAKENS to the bare Post `highMass l c = 0` feeding
   `BandRouting.phase6_to_phase7_of_post`, AND (b) discharges `MinorityAboveFloor` for both signs (which
   the bare Post canNOT) — so the strongest reachable Phase6→7 surface is the standard
   `Phase6To7Structure` PLUS the simultaneous `MinorityAboveFloor`.  Packaged as
   `phase6_to_phase7_of_seed` and `phase6To7_surface_of_seed`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MinorityFloorGap

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SeedExport

variable {L K : ℕ}

/-! ## Part 1 — the `l+1` drain instance (the landed engine, verbatim at the bumped level).

Everything below re-applies the symbolic-in-`l` Phase-6 drain machinery at `l+1`.  No new probability
content: the only honest input is the *budget* — the witness sampling hour for the `l+1` band-top index
`l` exists iff `l + 2 ≤ L`. -/

/-- **The `l+1` witness hour exists iff `l + 2 ≤ L`.**  The `l+1` band-top drain samples a Reserve at a
hour `h` with `(l+1) - 1 = l < h.val` and `h.val ≠ L`, i.e. `l < h.val < L`.  Such an `h : Fin (L+1)`
is `⟨l+1, _⟩`, witnessing the budget condition `l + 2 ≤ L`.  This is the SOLE new content of the level
bump; the drain engine itself is symbolic in the level. -/
theorem succ_witnessHour_of_budget {l : ℕ} (hlL2 : l + 2 ≤ L) :
    ∃ h : Fin (L + 1), (l + 1) - 1 < h.val ∧ h.val ≠ L := by
  refine ⟨⟨l + 1, by omega⟩, ?_, ?_⟩
  · show (l + 1) - 1 < l + 1; omega
  · show l + 1 ≠ L; omega

/-- **Phase 6 at `l+1` — the per-level `hdrop` from the SAME structural reserve floor.**  The landed
`DrainThreading.phase6_hdrop_of_struct` instantiated at the bumped band level `l+1`.  Side conditions:
`1 ≤ l+1` (free), `l+1 ≤ L`, and the witness sampling hour `h` (`(l+1)-1 < h ≠ L`).  The latter exists
when `l + 2 ≤ L` (`succ_witnessHour_of_budget`), but here the caller supplies the concrete witness `h`
so the lemma is the verbatim engine; `phase6_succ_hdrop_of_struct_budget` packages the budget form. -/
theorem phase6_succ_hdrop_of_struct (σ : Sign) (l n m : ℕ) (hn : 2 ≤ n)
    (hlL : l + 1 ≤ L) (b : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n b)
    (hbm : Phase6Convergence.highMass (L := L) (K := K) (l + 1) b = m)
    (h : Fin (L + 1)) (hhgt : (l + 1) - 1 < h.val) (hhne : h.val ≠ L) (R : ℕ)
    (hmain : 1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ (l + 1) (by omega) hlL).sum b.count)
    (hres : R ≤ (Phase6Convergence.reserveAtHour6 (L := L) (K := K) h).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) (l + 1) c) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((R : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  DrainThreading.phase6_hdrop_of_struct σ (l + 1) n m hn (by omega) hlL b hInv hbm h hhgt hhne R hmain hres

/-- **Phase 6 at `l+1` — the per-level `hdrop`, BUDGET form.**  Same as `phase6_succ_hdrop_of_struct`,
but the witness hour `h` is produced internally from the honest budget `l + 2 ≤ L`
(`succ_witnessHour_of_budget`), with the reserve floor stated at that produced hour.  This is the form
that exhibits the budget arithmetic: the `l+1` drain runs exactly when there are two free hours above
the band floor. -/
theorem phase6_succ_hdrop_of_struct_budget (σ : Sign) (l n m : ℕ) (hn : 2 ≤ n)
    (hlL2 : l + 2 ≤ L) (b : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n b)
    (hbm : Phase6Convergence.highMass (L := L) (K := K) (l + 1) b = m) (R : ℕ)
    (hmain : 1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ (l + 1) (by omega)
        (by omega)).sum b.count)
    (hres : R ≤ (Phase6Convergence.reserveAtHour6 (L := L) (K := K) ⟨l + 1, by omega⟩).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) (l + 1) c) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((R : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  phase6_succ_hdrop_of_struct σ l n m hn (by omega) b hInv hbm ⟨l + 1, by omega⟩
    (by show (l + 1) - 1 < l + 1; omega) (by show l + 1 ≠ L; omega) R hmain hres

/-- **The `l+1` Phase-6 convergence engine** (`phase6Convergence'` at the bumped level).  This is the
landed `Phase6Convergence.phase6Convergence'` instantiated at `l+1` — definitional, since the engine is
symbolic in `l`.  Its `Pre c = Phase6Win n c ∧ highMass (l+1) c ≤ M₀` and
`Post c = Phase6Win n c ∧ highMass (l+1) c = 0`. -/
noncomputable def phase6Convergence_succ (l n : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c))
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : Config (AgentState L K), Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase6Convergence.highMass (L := L) (K := K) (l + 1) b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) (l + 1) c) m)ᶜ ≤ q m)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (ε : ℝ≥0)
    (hε : (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase6Convergence.phase6Convergence' (l + 1) n hClosed q hdrop tWin M₀ ε hε

/-- **The `l+1` Phase-6 calibrated convergence** (`phase6Convergence_calibrated` at the bumped level).
The landed `DrainCalibration.phase6Convergence_calibrated` instantiated at `l+1` — the level is free in
the calibration, so this is the engine verbatim with the `1/n²` failure budget. -/
noncomputable def phase6Convergence_succ_calibrated (l n M₀ : ℕ)
    (q : ℕ → ℝ≥0∞) (tWin : ℕ → ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c))
    (hdrop : ∀ m, ∀ b : Config (AgentState L K), Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase6Convergence.highMass (L := L) (K := K) (l + 1) b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) (l + 1) c) m)ᶜ ≤ q m)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hpt : ∀ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  DrainCalibration.phase6Convergence_calibrated (l + 1) n M₀ q tWin hClosed hdrop hn hM1 hpt

/-! ## Part 2 — the seed export `AllBiasedMainAbove (l+1)` from the `l+1` Post.

This is the `phase6Post_iff` analogue: the `Post` of the `l+1` drain (`highMass (l+1) c = 0`) IS
`MinorityFloorGap.AllBiasedMainAbove (l+1) c`, the seed the verdict needs. -/

/-- **The seed from the `l+1` Post (the `phase6Post_iff` analogue).**  `highMass (l+1) c = 0` is, by
`Phase6Convergence.phase6Post_iff` at level `l+1`, exactly `AllBiasedMainAbove (l+1) c` — every biased
Main at index `≥ l+1`.  This is `MinorityFloorGap.allBiasedMainAbove_of_post` at the bumped level, named
here as the seed export. -/
theorem seedExport_of_post_succ {l : ℕ} {c : Config (AgentState L K)}
    (hPost : Phase6Convergence.highMass (L := L) (K := K) (l + 1) c = 0) :
    MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c :=
  MinorityFloorGap.allBiasedMainAbove_of_post (l := l + 1) hPost

/-- **The seed from the `l+1` `Post` field.**  Reads the seed directly off the second conjunct of the
`l+1` drain engine's `Post c = Phase6Win n c ∧ highMass (l+1) c = 0`. -/
theorem seed_of_phase6_succ_post {l : ℕ} {c : Config (AgentState L K)}
    (hPost : Phase6Convergence.Phase6Win (L := L) (K := K) (l) c ∧
      Phase6Convergence.highMass (L := L) (K := K) (l + 1) c = 0) :
    MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c :=
  seedExport_of_post_succ hPost.2

/-! ## Part 3 — the wired chain: seed → verdict → consumers.

The seed both WEAKENS to the bare Post `highMass l c = 0` (feeding `BandRouting.phase6_to_phase7_of_post`)
AND discharges `MinorityAboveFloor` for both signs (which the bare Post cannot).  So the strongest
reachable Phase6→7 surface from the seed is the standard `Phase6To7Structure` PLUS the simultaneous
`MinorityAboveFloor`. -/

/-- **The seed weakens to the bare Phase-6 Post at level `l`.**  `AllBiasedMainAbove (l+1) c` (every
biased Main at `≥ l+1`) trivially implies every biased Main at `≥ l`, i.e. `highMass l c = 0` — the
ordinary Phase-6 Post that the bare-`l` consumers (`BandRouting.phase6_to_phase7_of_post`,
`BandRouting.minorityConfinedGap1_of_post`) require.  This is the inclusion `seed ⟹ bare Post`. -/
theorem post_of_seed {l : ℕ} {c : Config (AgentState L K)}
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c) :
    Phase6Convergence.highMass (L := L) (K := K) l c = 0 := by
  rw [Phase6Convergence.phase6Post_iff]
  intro a ha hmain σ i hb
  exact le_trans (Nat.le_succ l) (hSeed a ha hmain σ i hb)

/-- **The verdict, wired from the seed.**  The seed discharges `MinorityFloorGap.minorityAboveFloor_verdict`:
`MinorityAboveFloor` for both signs, plus the `cancelSplit` step-stability of the `l+1` floor. -/
theorem verdict_of_seed {l : ℕ} {c : Config (AgentState L K)}
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c) :
    (∀ σ : Sign, GapAlignment.MinorityAboveFloor (L := L) (K := K) l σ c) ∧
    (∀ {s t : AgentState L K}, s ∈ c → t ∈ c → s.role = Role.main → t.role = Role.main →
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).1.bias = Bias.dyadic ss i → l + 1 ≤ i.val) ∧
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).2.bias = Bias.dyadic ss i → l + 1 ≤ i.val)) :=
  MinorityFloorGap.minorityAboveFloor_verdict hSeed

/-- **`MinorityConfinedGap1` from the seed** (the band-floor confinement of the Phase-6→7 entry).  The
seed weakens to the bare Post, which `BandRouting.minorityConfinedGap1_of_post` consumes (needs `1 ≤ l`).
-/
theorem minorityConfinedGap1_of_seed {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c) :
    BandLocalization.MinorityConfinedGap1 (L := L) (K := K) σ c :=
  BandRouting.minorityConfinedGap1_of_post (σ := σ) hl (post_of_seed hSeed)

/-- **`Phase6To7Structure` from the seed.**  The seed weakens to the bare Post (`post_of_seed`), feeding
`BandRouting.phase6_to_phase7_of_post` with the A-shape budget `hA`, the working window `h6`, and the
per-level routing `hRoute`.  So the seed yields the standard Phase-7 entry margin structure. -/
theorem phase6_to_phase7_of_seed {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hRoute : BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  BandRouting.phase6_to_phase7_of_post hl (post_of_seed hSeed) hA h6 hRoute hE

/-- **The strongest reachable Phase6→7 surface from the seed.**  Bundles, from the SINGLE seed
`AllBiasedMainAbove (l+1) c`:

* (1) the standard `EliminatorMargins.Phase6To7Structure σ E c` (via the bare-Post weakening); AND
* (2) `GapAlignment.MinorityAboveFloor l σ c` for EVERY sign — the floor-index clearing the bare Post
  cannot give, which the gap-1-below Phase-7 routing requires (the honest geometry GapAlignment isolated);
* (3) the `cancelSplit` step-stability of the `l+1` floor (the Phase-7 transition preserves the seed).

This is the strongest `Phase6To7`-shaped fact the landed drain (run one level higher) reaches: the
ordinary entry margin PLUS the simultaneous above-floor placement and its step-stability. -/
theorem phase6To7_surface_of_seed {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hRoute : BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c ∧
    (∀ τ : Sign, GapAlignment.MinorityAboveFloor (L := L) (K := K) l τ c) ∧
    (∀ {s t : AgentState L K}, s ∈ c → t ∈ c → s.role = Role.main → t.role = Role.main →
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).1.bias = Bias.dyadic ss i → l + 1 ≤ i.val) ∧
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).2.bias = Bias.dyadic ss i → l + 1 ≤ i.val)) :=
  ⟨phase6_to_phase7_of_seed hl hSeed hA h6 hRoute hE,
   (verdict_of_seed hSeed).1, (verdict_of_seed hSeed).2⟩

/-! ## Part 4 — the end-to-end seam: `l+1` drain Post ⟹ the full Phase6→7 surface.

Composing Parts 2 and 3: the landed `l+1` drain `Post` (which the `l+1` engine of Part 1 delivers)
discharges the entire Phase6→7 surface, with NO `MinorityAboveFloor` residual carried — it is produced. -/

/-- **End-to-end — `l+1` drain Post ⟹ Phase6→7 surface (verdict produced, not carried).**  From the
`l+1` drain `Post` `highMass (l+1) c = 0` (delivered by `phase6Convergence_succ`), the seed export
(Part 2) plus the wiring (Part 3) gives the standard `Phase6To7Structure` together with the
`MinorityAboveFloor` placement for both signs and its step-stability — the carried residual of
`MinorityFloorGap` is now SEEDED by the landed (bumped) drain, no longer an open assumption. -/
theorem phase6To7_surface_of_succ_post {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hPost : Phase6Convergence.highMass (L := L) (K := K) (l + 1) c = 0)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hRoute : BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c ∧
    (∀ τ : Sign, GapAlignment.MinorityAboveFloor (L := L) (K := K) l τ c) ∧
    (∀ {s t : AgentState L K}, s ∈ c → t ∈ c → s.role = Role.main → t.role = Role.main →
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).1.bias = Bias.dyadic ss i → l + 1 ≤ i.val) ∧
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).2.bias = Bias.dyadic ss i → l + 1 ≤ i.val)) :=
  phase6To7_surface_of_seed hl (seedExport_of_post_succ hPost) hA h6 hRoute hE

end SeedExport

end ExactMajority
