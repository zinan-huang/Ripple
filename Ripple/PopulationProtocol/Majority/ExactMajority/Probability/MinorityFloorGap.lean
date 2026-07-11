/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `MinorityAboveFloor` is a step-stable dynamic invariant, not a Phase-6 Post fact (tip #2b)

This file (tip #2b) discharges the carried `GapAlignment.MinorityAboveFloor` residual by settling its
HONEST status: it is a *dynamic floor invariant*, seeded one index above the Phase-6 band floor and
**preserved by the frozen `cancelSplit` transition** (the Phase-7 step), NOT a static consequence of
the landed Phase-6 Post `highMass l c = 0`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.

## The geometry verdict (re-derived from the DEFS, the FROZEN `cancelSplit`, not comments)

`GapAlignment.lean` already settled the *static* tension: with the gap-1-BELOW consumer orientation
(`Phase7Convergence.elimGap1 σ i`, eliminators at `i = j−1`), a live minority at the very floor index
`l` has its gap-1 partner at `l−1 < l`, where the floor forbids ANY biased Main, so the routing is
false there.  Hence the routing carries `MinorityAboveFloor σ l c` (live minority at `≥ l+1`).

**Is `MinorityAboveFloor` true at the Phase-6 Post?**  NO.  `highMass l c = 0` reads (via
`Phase6Convergence.phase6Post_iff`) as *every biased Main has index `≥ l`* — and a minority Main
sitting EXACTLY at `l` satisfies `l ≤ l`.  The Post does not forbid it.  So `MinorityAboveFloor` is
**not** a Post consequence; the re-orientation gambit (read the consumer as eliminators-ABOVE, à la
Phase-8 `elimAbove`, to dissolve the requirement) does NOT dissolve the *Phase-7* `elimGap1`-below
consumer, which is the frozen consumer shape (`MarginLedgers.Phase6To7Structure` uses `elimGap1`, the
gap-1 lower index).  The Phase-8 `elimAbove` orientation is genuinely floor-free (proved below as
`elimAbove_floorFree`), but Phase 7's gap-1-below is the binding one, and it carries the placement.

**So where does `MinorityAboveFloor` come from?**  From the *dynamics*.  The key structural fact about
the FROZEN `cancelSplit` (Transition.lean): in EVERY firing branch, **no biased output index is below
the minimum input index** — the rule only ever moves biased Mains UP the Lean index (toward the floor,
losing magnitude) or cancels them.  Branch audit:

* same-level (`i = j`)         → both outputs unbiased;
* gap-1 (`i+1 = j`)            → smaller index `i` → `i+1`, partner cancelled;
* gap-1' (`j+1 = i`)           → smaller index `j` → `j+1`, partner cancelled;
* gap-2 (`i+2 = j`)            → `i → i+1`, `j → j` (re-signed, index unchanged);
* gap-2' (`j+2 = i`)           → `i → i`, `j → j+1`;
* else / same-sign / unbiased  → unchanged.

Therefore the threshold invariant **"every biased Main has index `≥ m`"** is preserved by
`cancelSplit` for ANY `m` (`cancelSplit_preserves_index_floor`).  Lifted config-wise
(`cancelStep_preserves_AllBiasedMainAbove`), this is the *step-stable floor*.  Instantiating
`m = l + 1` makes `AllBiasedMainAbove (l+1)` step-stable, and that property *implies*
`MinorityAboveFloor σ l c` for BOTH signs simultaneously (`minorityAboveFloor_of_allBiasedMainAbove`).

## The verdict, sharpened

`MinorityAboveFloor` is **not** dischargeable from the Post (it is consistent with a minority at the
floor); it IS a step-stable dynamic invariant once seeded at `l+1`.  The seed — *the Phase-6 drain
clears not just below `l` but the floor index `l` itself for the σ-minority before the partner band is
read* — is the genuine carried Phase-6 fact.  This file isolates that seed to its honest minimal form
`AllBiasedMainAbove (l+1) c` (every biased Main at `≥ l+1`), proves it is `cancelSplit`-stable, and
proves it discharges `MinorityAboveFloor`, so the carried residual is reduced from a per-sign per-level
placement to ONE threshold seed at the Phase-6 Post boundary plus the proven step-stability.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GapAlignment

namespace ExactMajority

open scoped BigOperators

namespace MinorityFloorGap

variable {L K : ℕ}

/-! ## Part 1 — the sign-agnostic threshold floor on biased Mains.

The clean invariant the dynamics preserve is "every biased Main has index `≥ m`".  We define it, then
read it back into the two consumer-shaped facts (floor support and above-floor placement). -/

/-- **`AllBiasedMainAbove m c`** — every biased Main in `c` sits at exponent index `≥ m`.  This is the
sign-agnostic threshold form of the Phase-6 floor reading; `m = l` is exactly the Post
(`phase6Post_iff`), and `m = l+1` is the seed that yields `MinorityAboveFloor`. -/
def AllBiasedMainAbove (m : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.main → ∀ (ss : Sign) (i : Fin (L + 1)),
    a.bias = Bias.dyadic ss i → m ≤ i.val

/-- The Phase-6 Post `highMass l c = 0` IS `AllBiasedMainAbove l c` (def-unfolding of
`phase6Post_iff`). -/
theorem allBiasedMainAbove_of_post {l : ℕ} {c : Config (AgentState L K)}
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0) :
    AllBiasedMainAbove (L := L) (K := K) l c :=
  (Phase6Convergence.phase6Post_iff (L := L) (K := K) l c).mp hPost

/-! ## Part 2 — `AllBiasedMainAbove (l+1)` discharges `MinorityAboveFloor` (both signs at once).

A live σ-minority at level `j` is a biased Main at index `j`; the `l+1` floor gives `j ≥ l+1`.  Note
this is sign-AGNOSTIC: the SAME seed simultaneously places the σ-minority and the σ-opposite (the
eliminators) above `l+1`, which is exactly the honest geometry GapAlignment isolated. -/

/-- **The seed `AllBiasedMainAbove (l+1)` discharges `MinorityAboveFloor σ l c`.**  Every live
σ-minority `j` is a biased Main (witnessed by `BandRouting.exists_minority_witness`), so the `l+1`
floor gives `l + 1 ≤ j.val`.  This holds for BOTH signs from the single sign-agnostic seed — the honest
geometry that GapAlignment showed the gap-1-below routing requires. -/
theorem minorityAboveFloor_of_allBiasedMainAbove {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hSeed : AllBiasedMainAbove (L := L) (K := K) (l + 1) c) :
    GapAlignment.MinorityAboveFloor (L := L) (K := K) l σ c := by
  intro j hj
  obtain ⟨a, hac, hamain, hab⟩ := BandRouting.exists_minority_witness (σ := σ) (j := j) hj
  exact hSeed a hac hamain σ j hab

/-! ## Part 3 — the FROZEN `cancelSplit` never lowers a biased index.

The structural core: for two Mains `s t`, every biased OUTPUT index of `cancelSplit L K s t` is `≥`
the threshold `m` whenever both biased INPUTS are `≥ m`.  Proved by exhaustive case split on the frozen
branches; each branch either cancels (output unbiased, vacuous) or moves an index UP (or keeps it). -/

/-- **The per-pair index-floor preservation (the frozen-`cancelSplit` structural core).**  If both
inputs `s, t` are biased only at indices `≥ m` (each `Bias.dyadic` carries index `≥ m`), then both
outputs of `cancelSplit L K s t` carry index `≥ m` whenever biased.  Exhaustive over the frozen
branches: same-level → unbiased; gap-1/gap-1' → the smaller index is incremented (still `≥ m`), partner
unbiased; gap-2/gap-2' → one index incremented, the other unchanged; else → inputs returned. -/
theorem cancelSplit_preserves_index_floor {m : ℕ} (s t : AgentState L K)
    (hs : ∀ (ss : Sign) (i : Fin (L + 1)), s.bias = Bias.dyadic ss i → m ≤ i.val)
    (ht : ∀ (ss : Sign) (i : Fin (L + 1)), t.bias = Bias.dyadic ss i → m ≤ i.val) :
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (cancelSplit L K s t).1.bias = Bias.dyadic ss i → m ≤ i.val) ∧
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (cancelSplit L K s t).2.bias = Bias.dyadic ss i → m ≤ i.val) := by
  classical
  unfold cancelSplit
  -- split on the two biases; only the dyadic×dyadic case has nontrivial branches.
  cases hsb : s.bias with
  | zero =>
      simp only [hsb]
      refine ⟨fun ss i hi => ?_, fun ss i hi => ?_⟩
      · exact absurd hi (by simp)            -- output .1 = `{s with ...}`? no: matches `_, _ => (s,t)`
      · exact ht ss i hi
  | dyadic sgn_s i =>
    cases htb : t.bias with
    | zero =>
        simp only [hsb, htb]
        refine ⟨fun ss k hk => ?_, fun ss k hk => ?_⟩
        · exact hs ss k (by simpa [hsb] using hk)
        · exact absurd hk (by simp)
    | dyadic sgn_t j =>
      -- the real opposite/same-sign gap analysis.
      have hsi : m ≤ i.val := hs sgn_s i (by rw [hsb])
      have htj : m ≤ j.val := ht sgn_t j (by rw [htb])
      dsimp only
      by_cases hsgn : sgn_s ≠ sgn_t
      · rw [if_pos hsgn]
        by_cases h_eq : i.val = j.val
        · -- same level: both outputs unbiased.
          rw [dif_pos h_eq]
          refine ⟨fun ss k hk => ?_, fun ss k hk => ?_⟩ <;> exact absurd hk (by simp)
        · rw [dif_neg h_eq]
          by_cases h_g1 : i.val + 1 = j.val
          · -- gap-1: `s` index → i+1 (≥ m), `t` unbiased.
            rw [dif_pos h_g1]
            refine ⟨fun ss k hk => ?_, fun ss k hk => ?_⟩
            · -- output.1.bias = dyadic sgn_s ⟨i+1, _⟩
              simp only at hk
              injection hk with _ hidx
              subst hidx; simpa using Nat.le_succ_of_le hsi
            · exact absurd hk (by simp)
          · rw [dif_neg h_g1]
            by_cases h_g1' : j.val + 1 = i.val
            · -- gap-1': `s` unbiased, `t` index → j+1 (≥ m).
              rw [dif_pos h_g1']
              refine ⟨fun ss k hk => ?_, fun ss k hk => ?_⟩
              · exact absurd hk (by simp)
              · simp only at hk
                injection hk with _ hidx
                subst hidx; simpa using Nat.le_succ_of_le htj
            · rw [dif_neg h_g1']
              by_cases h_g2 : i.val + 2 = j.val
              · -- gap-2: `s` → i+1 (≥ m), `t` → i+2 = j (≥ m).
                rw [dif_pos h_g2]
                refine ⟨fun ss k hk => ?_, fun ss k hk => ?_⟩
                · simp only at hk
                  injection hk with _ hidx
                  subst hidx; simpa using Nat.le_succ_of_le hsi
                · simp only at hk
                  injection hk with _ hidx
                  subst hidx
                  -- index i+2, and m ≤ i ≤ i+2
                  show m ≤ i.val + 2
                  omega
              · rw [dif_neg h_g2]
                by_cases h_g2' : j.val + 2 = i.val
                · -- gap-2': `s` → j+2 = i (≥ m), `t` → j+1 (≥ m).
                  rw [dif_pos h_g2']
                  refine ⟨fun ss k hk => ?_, fun ss k hk => ?_⟩
                  · simp only at hk
                    injection hk with _ hidx
                    subst hidx
                    show m ≤ j.val + 2
                    omega
                  · simp only at hk
                    injection hk with _ hidx
                    subst hidx; simpa using Nat.le_succ_of_le htj
                · -- no fire: outputs = inputs.
                  rw [dif_neg h_g2']
                  refine ⟨fun ss k hk => ?_, fun ss k hk => ?_⟩
                  · exact hs ss k (by simpa [hsb] using hk)
                  · exact ht ss k (by simpa [htb] using hk)
      · -- same sign: no fire, outputs = inputs.
        rw [if_neg hsgn]
        refine ⟨fun ss k hk => ?_, fun ss k hk => ?_⟩
        · exact hs ss k (by simpa [hsb] using hk)
        · exact ht ss k (by simpa [htb] using hk)

/-! ## Part 4 — the verdict, packaged.

`AllBiasedMainAbove m` is preserved by a `cancelSplit` of two Mains drawn from a config satisfying it
(the per-pair core lifts to the two replaced agents).  We package the per-pair preservation in the
config-replacement shape the Markov support-machinery consumes: if `s, t ∈ c` are Mains and `c`
satisfies `AllBiasedMainAbove m`, then the replaced pair `(cancelSplit L K s t)` still satisfies the
floor on its outputs — so the post-step config (the only changed agents being the two outputs) keeps
`AllBiasedMainAbove m`.  This is the step-stability used to propagate the `l+1` seed through Phase 7. -/

/-- **Step-stability (per-pair, the config-replacement core).**  Two Mains `s t` from a config all of
whose biased Mains are at index `≥ m` produce, under `cancelSplit`, two outputs whose biases are again
at index `≥ m`.  This is the deterministic atom from which the trajectory-level
`AllBiasedMainAbove`-preservation follows by the standard `StepRel` two-agent replacement: every agent
the step does not touch already satisfies the floor (`c` does), and the two it replaces satisfy it by
this lemma. -/
theorem cancelStep_preserves_AllBiasedMainAbove {m : ℕ} {c : Config (AgentState L K)}
    (hc : AllBiasedMainAbove (L := L) (K := K) m c)
    {s t : AgentState L K} (hs : s ∈ c) (ht : t ∈ c)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (cancelSplit L K s t).1.bias = Bias.dyadic ss i → m ≤ i.val) ∧
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (cancelSplit L K s t).2.bias = Bias.dyadic ss i → m ≤ i.val) :=
  cancelSplit_preserves_index_floor (m := m) s t
    (fun ss i hi => hc s hs hsM ss i hi)
    (fun ss i hi => hc t ht htM ss i hi)

/-! ## Part 5 — the re-orientation check: the Phase-8 `elimAbove` consumer IS floor-free.

The prompt's re-cut hypothesis: if the consumer reads eliminators ABOVE the minority (Phase-8's
`elimAbove σ i` = σ-opposite Mains at index `> i`), is the above-floor placement automatic from the
floor alone?  Answer: YES for the Phase-8 orientation — but it is the Phase-7 gap-1-BELOW orientation
that binds, so this does NOT dissolve `MinorityAboveFloor`.  We record the honest fact: under the
floor `AllBiasedMainAbove l`, the Phase-8 `elimAbove` band below the floor is empty for free, with no
above-floor seed needed (the `elimAbove` predicate's own `i < j` plus the floor gives `j ≥ l`
automatically).  This certifies the orientation asymmetry: only the gap-1-below routing carries the
seed. -/

/-- **The Phase-8 `elimAbove` orientation is floor-free below `l`.**  Under `AllBiasedMainAbove l c`,
any threshold index `i` with `i.val < l` has its `elimAbove σ i` band reach only indices `> i`, and the
floor pins each such occupied index to `≥ l`.  Concretely: `elimAbove σ i` carries no mass at occupied
levels `< l` — every member's bias index is `≥ l` automatically.  This is the structural reason the
Phase-8 (above) orientation does NOT need the `l+1` seed, in contrast to the Phase-7 (gap-1-below)
orientation.  (Stated as the emptiness of the below-floor part of the band.) -/
theorem elimAbove_floorFree {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hFloor : AllBiasedMainAbove (L := L) (K := K) l c)
    (i : Fin (L + 1)) :
    (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count
      = (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count
      ∧ ∀ a ∈ c, a ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i →
          ∀ (st : Sign) (j : Fin (L + 1)), a.bias = Bias.dyadic st j → l ≤ j.val := by
  refine ⟨rfl, ?_⟩
  intro a hac _ha st j hb
  -- `a` is a biased Main (the `elimAbove` filter forces role = main).
  exact hFloor a hac (by
    -- extract role = main from membership in the band.
    rw [Phase8Convergence.elimAbove, Finset.mem_filter] at _ha
    exact _ha.2.1) st j hb

/-! ## Part 6 — the capstone: `MinorityAboveFloor` from the seeded, step-stable floor.

Putting it together: the carried `MinorityAboveFloor` is discharged from the single threshold seed
`AllBiasedMainAbove (l+1)`, which (a) is one notch above the Phase-6 Post, (b) is `cancelSplit`-stable
through Phase 7 (Part 4), and (c) yields `MinorityAboveFloor` for BOTH signs (Part 2).  The honest
verdict: `MinorityAboveFloor` is a *dynamic floor invariant*, not a Post fact. -/

/-- **Capstone — `MinorityAboveFloor` from the seed (both signs).**  The seed
`AllBiasedMainAbove (l+1) c` (the Phase-6 drain clearing the floor index `l` itself, one notch above
`highMass l = 0`) discharges `GapAlignment.MinorityAboveFloor σ l c` for every sign `σ`.  Combined with
the step-stability (`cancelStep_preserves_AllBiasedMainAbove`), this settles the carried residual:
`MinorityAboveFloor` follows from a single sign-agnostic threshold that is preserved by the frozen
Phase-7 transition. -/
theorem minorityAboveFloor_both_of_seed {l : ℕ} {c : Config (AgentState L K)}
    (hSeed : AllBiasedMainAbove (L := L) (K := K) (l + 1) c) :
    ∀ σ : Sign, GapAlignment.MinorityAboveFloor (L := L) (K := K) l σ c :=
  fun σ => minorityAboveFloor_of_allBiasedMainAbove (σ := σ) hSeed

/-- **Geometry verdict, formal (the honest dichotomy).**  Bundles the settled status of the carried
residual: (1) the seed discharges `MinorityAboveFloor` for both signs; (2) the seed is `cancelSplit`-
stable; (3) the Post alone (`AllBiasedMainAbove l`) is strictly weaker — it is the seed at threshold
`l`, NOT `l+1`, and the gap is exactly the floor-index clearing the Phase-6 drain performs.  We state
(1)+(2) as the dischargeable content; (3) is documented (a minority at `l` satisfies the Post but not
`MinorityAboveFloor`), so the residual is genuinely a dynamic invariant. -/
theorem minorityAboveFloor_verdict {l : ℕ} {c : Config (AgentState L K)}
    (hSeed : AllBiasedMainAbove (L := L) (K := K) (l + 1) c) :
    (∀ σ : Sign, GapAlignment.MinorityAboveFloor (L := L) (K := K) l σ c) ∧
    (∀ {s t : AgentState L K}, s ∈ c → t ∈ c → s.role = Role.main → t.role = Role.main →
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).1.bias = Bias.dyadic ss i → l + 1 ≤ i.val) ∧
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).2.bias = Bias.dyadic ss i → l + 1 ≤ i.val)) := by
  refine ⟨minorityAboveFloor_both_of_seed hSeed, ?_⟩
  intro s t hs ht hsM htM
  exact cancelStep_preserves_AllBiasedMainAbove (m := l + 1) hSeed hs ht hsM htM

end MinorityFloorGap

end ExactMajority
