# AAE 2008 Errata Statement — Ripple README and Technical Report Correction

> **Current status.** The correction was completed in
> [Technical Report v2](https://arxiv.org/abs/2607.13531v2), posted
> 21 July 2026. Cite v2; version 1 is superseded.

## Background

An author of Angluin-Aspnes-Eisenstat 2008 ("A simple population protocol for fast robust approximate majority") objected to claims in Ripple's README and Technical Report v1 (§6.1) that the formalization found a "gap" in AAE's proof. The README (line 75, under "Gaps exposed by formalization") read:

> **Approximate majority (AAE 2008).** The central-region multiplicative drift inequality suggested by the original proof sketch is *false* — there is an explicit n = 4 counterexample. The Lean proof replaces it with a product-form supermartingale argument.

Technical Report v1 (§6.1, pp. 9-11) made the same claim in detail, calling it "the headline gap."

The author's objections:

1. **They do not use Jensen's inequality.** The proof of Corollary 1 uses a Taylor series expansion and adjusts constants to absorb higher-order terms for sufficiently large n.
2. **An n = 4 counterexample does not contradict their result**, which is stated for sufficiently large n.
3. **The claim misattributes** a formalization-internal failure to the published proof.

## Independent verification against the AAE 2008 paper

We re-read the AAE 2008 paper (Distributed Computing, 2008) to verify these objections. Here is what the paper actually does:

### AAE's proof structure (Sections 4.3-4.4, pp. 91-93)

1. **Lemma 1** (p. 91): Series expansion — Δ(1/f)/(1/f) = Σ_{i≥1} (-Δf/f)^i.

2. **Lemma 2** (p. 92): E[Δ(1/f)/(1/f) | I^vb] ≤ -15/(32n) + O(n^{-3/2}).

3. **Lemma 3** (p. 93): E[Δ(1/f)/(1/f) | I^xy] ≤ 9/(32n) + O(n^{-3/2}).

4. **Corollary 1** (p. 93): "For all sufficiently large n,"
   - E[1/f_{t+1} | I^vb] < exp(-7/(16n)) · (1/f_t)
   - E[1/f_{t+1} | I^xy] < exp(5/(16n)) · (1/f_t)

   These are **per-interaction-type** bounds. The proof absorbs the O(n^{-3/2}) error by shifting -15/32 → -7/16 and 9/32 → 5/16, using "the Taylor series expansion of the exponential."

5. **Lemma 4** (p. 93): M_t = exp((7/16·S^vb_t - 5/16·S^xy_t)/n) / (u²_t + 2n) is a supermartingale — **for all regions, including central.** Proof directly uses Corollary 1.

### What Technical Report v1 claimed vs. what the paper actually does

Technical Report v1 (§6.1, p. 10) set up the following equation:

> "The surrounding proof sketch implicitly carries the same multiplicative-drift framework into the central region, i.e. it needs ... E[1/f' | F_t] ≤ (1-δ) · (1/f_t) (central region)."

This is equation (1) in the technical report. **The AAE paper never needs this inequality.** The paper needs the **per-interaction-type** bounds of Corollary 1 (conditioned on I^vb or I^xy, not on F_t unconditionally), and these are used to build Lemma 4's product-form supermartingale. The xy interaction is explicitly ALLOWED to increase 1/f (Corollary 1 gives a factor exp(+5/(16n)) > 1). The contraction comes from the product-form structure, not from 1/f contracting unconditionally.

### The n = 4 counterexample refutes a straw man

The counterexample (n=4, x=1, b=0, y=3) showing E[1/f']/(1/f) = 103/102 > 1 refutes the **unconditional** E[1/f' | F_t] ≤ (1-δ)/f. But this inequality is never part of the AAE proof. In fact:

- Corollary 1's per-interaction-type bounds hold even at n = 4. We verified numerically:
  - For n=4, b=0, so I^vb has probability 0 (irrelevant)
  - E[1/f' | I^xy] = 0.0850, exp(5/(16·4))·(1/f) = 0.0901: **Corollary 1 holds**
- The "sufficiently large n" in Corollary 1 is conservative; the bounds appear to hold for all n ≥ 1 numerically.
- More importantly, the counterexample mixes interaction types (including null yy interactions) into an unconditional expectation, which is not what any part of the AAE proof requires.

### The "Jensen" attribution

Technical Report v1 says "The reason it fails: Jensen runs the wrong way" (p. 10). This is the report's own analysis of why the straw man equation (1) fails — 1/x is convex, so E[1/f'] ≥ 1/E[f']. The AAE paper does not invoke Jensen's inequality anywhere. The AAE author's objection on this point is correct.

## What actually happened

Technical Report v1 (§6.1) mischaracterizes the AAE proof. The error is:

1. **Equation (1) is a straw man.** The report attributes to AAE the unconditional bound E[1/f' | F_t] ≤ (1-δ)/f, claiming it is "implicitly carried" by the proof sketch. The paper never needs or uses this bound.

2. **The "gap" description is backwards.** The report says "The repair is already implicit in the authors' own Lemma 4; formalization made the disconnect between Lemma 4 and the surrounding drift narrative explicit." But there is no disconnect — Lemma 4 IS the paper's explicit technique for the central region, directly derived from Corollary 1. The corner regions use separate potential functions (1/v, 1/(n-x), 1/(n-y)); the central region was never supposed to use the same direct drift.

3. **Origin of the error.** The formalization's first attempt at the central region tried a naive unconditional multiplicative drift bound on 1/f. When this failed (the n=4 counterexample), the failure was incorrectly attributed to the AAE paper rather than to the formalization's own naive approach. The formalization then correctly followed AAE's Lemma 4. The writeup in Technical Report v1 framed this as "finding and fixing a gap" rather than "initial failed attempt followed by correct implementation of the paper's approach."

## The formalization's actual contribution

The formalization does NOT find a gap in the AAE proof. It does:

1. **Machine-check AAE's Lemma 4 supermartingale** — the per-step inequalities (equations 5-6 in Technical Report v1, corresponding to Corollary 1's bounds) are verified formally.

2. **Prove the per-step inequalities unconditionally, for all n ≥ 1** — the formalization replaces AAE's exponential weights exp(∓c/(16n)) with rational weights α_vb = (16n+7)/(16n), α_xy = (16n-5)/(16n), and proves the resulting algebraic inequalities exactly for all n ≥ 1 (`supermartingale_factor_vb_le`, `supermartingale_factor_xy_le`, both with hypothesis `n ≥ 1`).

   **Precision note — do not overstate this.** The rational weights are *weaker* per step than AAE's exponential ones, at every n: since 1/(1+t) ≥ e^{−t} and 1/(1−t) ≥ e^{t}, our required bounds 16n/(16n+7) and 16n/(16n−5) are looser than AAE's exp(−7/(16n)) and exp(+5/(16n)). Verified numerically at n = 1, 2, 4, 10, 100, 1000: AAE's factor is tighter in every case. So this is **not** a strengthening of AAE's inequalities. It is a strengthening only along the *range of n* — unconditional rather than asymptotic — and it is paid for with a looser decay constant (15000), which costs nothing asymptotically. Describing it as "stronger than the paper's bound" would repeat the original error in a new place.

3. **Complete the full probabilistic convergence theorem** with explicit constants — the four regional geometric-decay bounds are combined via union bound into a single O(n log n) high-probability theorem.

## Correction status

### Repository and source corrections

1. **README.md**: Moved AAE bullet from "Gaps exposed" to "Formalization insights." Rewrote to describe a naive formalization route that fails, credit AAE's paper approach as correct, note strengthening to all n ≥ 1.

2. **ConvergenceTime.lean**, **CentralSupermartingale.lean**, **AugmentedState.lean**, **Supermartingale.lean**: Clarified that the drift failure is a formalization route failure, not a gap in the paper. Credited AAE's approach explicitly. Updated stale comments.

3. **README.md — corrected report restored.** Links to v1 were temporarily removed while the
   report was under revision. The corrected [Technical Report v2](https://arxiv.org/abs/2607.13531v2)
   was posted on 21 July 2026; README links and citation guidance now point explicitly to v2.
   Version 1 is superseded.

4. **Blog post** (`zinan-blog`, `content/math/011-formalizing-population-protocol.md`,
   published as `/math/formalizing-population-protocol/`): the post was built entirely around
   the "we found an error in the original proof sketch" framing. Rewritten — title and the
   `erratum` tag dropped, the failing drift bound now explicitly attributed to our own naive
   route, AAE's Lemma 4 credited as the paper's own technique, and the scope of the n = 4
   counterexample stated. The slug is unchanged so the published URL still resolves.

### Technical Report v2 — completed 2026-07-21

The corrected [v2 report](https://arxiv.org/abs/2607.13531v2) removes the
incorrect AAE gap claim. The original correction was not confined to §6.1:
in v1 it was load-bearing in the abstract, the
contribution list, the framework figure, §5, the §6 preamble, §6.1 itself, and the conclusion —
**seven locations**. All seven were changed together in v2.

| # | Location | v1 text | Correction applied in v2 |
|---|---|---|---|
| 1 | Abstract | "it exposed genuine, fixable gaps in published proofs (**the approximate-majority convergence argument** and the LPP main theorem)" | The approximate-majority item was removed; the LPP and Catalan-dependency claims remain. |
| 2 | §1, contribution 2 ("It exposes gaps") | "gaps in published constructions — **in the original approximate-majority convergence proof** and in the LPP main theorem" | The approximate-majority clause was removed. |
| 3 | Figure 1 table + caption | "approximate majority [2] (**drift gap found and fixed**)"; "Angluin–Aspnes–Eisenstat **with the drift-gap fix of §6(A)**" | The gap language was removed. |
| 4 | Approximate-majority overview | "This is the formalization in which **Gap A was found** ..." | The section now states that the formalization follows AAE's Lemma 4 and verifies rational-weight per-step inequalities for every n ≥ 1. |
| 5 | Gaps-section preamble | "We document **three** representative gaps," including approximate majority | The section now documents **two** gaps: the LPP compilation and Catalan dependency. |
| 6 | Former §6.1 | "The approximate-majority central-region drift inequality is false" and related gap analysis | The AAE material was removed from the gaps section. |
| 7 | Conclusion | Listed "the approximate-majority drift inequality" as a gap | The approximate-majority item was removed. |

**Interpretive constraints retained from the correction:**

- Any discussion of the false inequality must attribute it to the naive formalization route, not to AAE.
- **Equation (1)** (p. 10) attributes an unconditional bound `E[1/f' | F_t] ≤ (1-δ)/f` to the "proof sketch" — this attribution is incorrect. AAE need only the *per-interaction-type* bounds of Corollary 1.
- There is no gap in the published AAE proof.
- **"The reason it fails: Jensen runs the wrong way"** — this is the report's own analysis of its own straw man. AAE do not invoke Jensen; they use a Taylor expansion (Lemma 1).
- Lemma 4 is not a repair; it is the paper's approach for the central region.
- **The n = 4 counterexample** should be presented with its scope stated: AAE's Corollary 1 is asserted for sufficiently large n, so a small-n configuration does not bear on it.

**Retained, legitimate contribution in v2.** The formalization machine-checks AAE's Lemma 4 route with
rational weights in place of the exponential ones, proving the two per-step inequalities exactly and
unconditionally for all n ≥ 1 (vs. the paper's asymptotic form), and assembles the four regional
bounds into the full O(n log n) high-probability theorem. State it that way — as an unconditional
re-derivation, not as a repair, and not as a sharper constant (the rational weights are looser than
AAE's; see the precision note above).

### Current citation status

Readers should cite [arXiv:2607.13531v2](https://arxiv.org/abs/2607.13531v2),
not v1. The v2 submission history explicitly records removal of the incorrect
AAE gap claim.

## Technical summary

| Aspect | AAE 2008 paper | Technical Report v1 claim | Corrected account |
|--------|---------------|---------------------|---------|
| Central region technique | Corollary 1 (per-type bounds, large n) → Lemma 4 (product-form supermartingale) | "proof sketch implicitly carries multiplicative drift" E[1/f'] ≤ (1-δ)/f | AAE uses Lemma 4, not unconditional drift |
| Jensen's inequality | Not used | "Jensen runs the wrong way" | AAE uses Taylor series expansion (Lemma 1) |
| n = 4 counterexample | N/A — result is for large n | Disproves equation (1) | Equation (1) is a straw man; Corollary 1 holds for n = 4 |
| Scope | Corollary 1: sufficiently large n | Claims gap | No gap; formalization strengthens to all n ≥ 1 |
| Lemma 4 | Paper's own technique | "repair ... already implicit in authors' own Lemma 4" | Lemma 4 is not a repair; it IS the proof |

## Historical diff summary (initial README + Lean comment correction)

```
README.md                                          |  5 ++++-
.../Convergence/AugmentedState.lean                | 10 +++++-----
.../Convergence/CentralSupermartingale.lean         |  8 ++++----
.../Convergence/ConvergenceTime.lean               | 11 ++++++++---
.../Convergence/Supermartingale.lean               | 22 ++++++++++------------
                                                    ----------------
                                                    31 ins, 25 del
```
