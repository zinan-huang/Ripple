/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Why the pre-fix Phase-8 absorb direction could not drain the minority

Historical archive (2026-07-16 adjudication).  Before the direction fix,
`absorbConsume` fired when the consumer had the *larger* dyadic index, i.e.
the *smaller* |bias| — the reverse of the paper's Phase 8 ("an agent at a
larger exponent i consumes an agent at an arbitrarily smaller exponent
j < i", with exponents negative and the Lean index equal to minus the
exponent).  This file pins the mathematical consequence that forced the fix:

* under the old direction, a bias at the bottom index `L` can never be
  zeroed, so a bottom-level minority Main is immortal in Phase 8 and the
  slot-8 drain target `minorityU σ = 0` is unreachable from any window
  containing one;
* in the paper regime (minority strictly deeper than every eliminator) the
  old absorb *destroys the majority* and leaves the minority intact.

The old behavior is inlined below (`absorbConsumeReversed`) so this archive
compiles unchanged after the live `absorbConsume` is fixed.

One theorem here is about the *live* interface and remains load-bearing
after the fix: `elimAbove σ ⟨L⟩` is empty in every configuration, so the
carried witness of `Phase8DrainReady` forces `E8 = 0` whenever the minority
sits only at the bottom level.  With the corrected absorb direction the
draining pairs are (shallow eliminator, deep minority), so the slot-8 ready
witness must be recut from `elimAbove` to an `elimBelow` pool before the
drain engine can be rebuilt.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase678ReadySurvival

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase8AbsorbDirectionImpossibility

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## The pre-fix absorb, inlined verbatim -/

/-- Verbatim copy of `absorbConsume` as it stood before the 2026-07-16
direction fix (`Protocol/Transition.lean:1353` at commit `43295ea`):
the consumer is the agent with the larger index, i.e. the smaller |bias|. -/
def absorbConsumeReversed (L K : ℕ) (s t : AgentState L K) :
    AgentState L K × AgentState L K :=
  match s.bias, t.bias with
  | .dyadic .pos i, .dyadic .neg j =>
      if i.val > j.val ∧ ¬ s.full then
        ({ s with full := true }, { t with bias := .zero })
      else if j.val > i.val ∧ ¬ t.full then
        ({ s with bias := .zero }, { t with full := true })
      else (s, t)
  | .dyadic .neg i, .dyadic .pos j =>
      if i.val > j.val ∧ ¬ s.full then
        ({ s with full := true }, { t with bias := .zero })
      else if j.val > i.val ∧ ¬ t.full then
        ({ s with bias := .zero }, { t with full := true })
      else (s, t)
  | _, _ => (s, t)

/-- The bottom dyadic index. -/
def bottomIdx (L : ℕ) : Fin (L + 1) := ⟨L, by omega⟩

/-! ## Bottom-level immortality under the old direction -/

/-- Under the old direction, a left agent carrying a bottom-index bias keeps
it: zeroing the left slot requires the partner index to be strictly larger,
which is impossible above `L`. -/
theorem absorbConsumeReversed_fst_bias_of_bottom (σ : Sign) (s t : AgentState L K)
    (hs : s.bias = .dyadic σ (bottomIdx L)) :
    (absorbConsumeReversed L K s t).1.bias = s.bias := by
  have hjle : ∀ j : Fin (L + 1), ¬ ((j : ℕ) > (bottomIdx L : ℕ)) := by
    intro j
    have := j.2
    simp only [bottomIdx]
    omega
  unfold absorbConsumeReversed
  rcases htb : t.bias with _ | ⟨sgt, j⟩ <;> rcases σ <;> rcases hsb : s.bias <;>
    simp_all <;> rcases sgt <;> simp_all <;> split_ifs with h1 h2 <;>
    first
    | rfl
    | (exact absurd h2.1 (by simpa [hsb] using hjle j))
    | simp_all

/-- Right-slot version of `absorbConsumeReversed_fst_bias_of_bottom`. -/
theorem absorbConsumeReversed_snd_bias_of_bottom (σ : Sign) (s t : AgentState L K)
    (ht : t.bias = .dyadic σ (bottomIdx L)) :
    (absorbConsumeReversed L K s t).2.bias = t.bias := by
  have hile : ∀ i : Fin (L + 1), ¬ ((i : ℕ) > (bottomIdx L : ℕ)) := by
    intro i
    have := i.2
    simp only [bottomIdx]
    omega
  unfold absorbConsumeReversed
  rcases hsb : s.bias with _ | ⟨sgs, i⟩ <;> rcases σ <;> rcases htb : t.bias <;>
    simp_all <;> rcases sgs <;> simp_all <;> split_ifs with h1 h2 <;>
    first
    | rfl
    | (exact absurd h1.1 (by simpa [htb] using hile i))
    | simp_all

/-! ## The paper regime: the old absorb destroys the majority -/

/-- In a separated pair — minority `σ` strictly deeper than the opposite-sign
eliminator — the old absorb zeroes the *eliminator* and merely marks the
minority `full`; the minority bias survives.  (With the corrected direction
the same pair zeroes the minority.)  Stated for `σ = pos`; the reaction is
sign-symmetric. -/
theorem absorbConsumeReversed_kills_eliminator (s t : AgentState L K)
    (i j : Fin (L + 1))
    (hs : s.bias = .dyadic .pos i)   -- deep minority
    (ht : t.bias = .dyadic .neg j)   -- shallow eliminator
    (hij : j.val < i.val) (hsf : ¬ s.full) :
    absorbConsumeReversed L K s t =
      ({ s with full := true }, { t with bias := .zero }) := by
  unfold absorbConsumeReversed
  rw [hs, ht]
  have hcond : (i : ℕ) > (j : ℕ) ∧ ¬ s.full = true := ⟨hij, hsf⟩
  dsimp only
  rw [if_pos hcond]

/-! ## HISTORICAL: the pre-flip ready-gate witness was bottom-blind

Frozen record (2026-07-16).  Before the `elimAbove` semantic flip, the pool
`elimAbove σ i` collected eliminators at Lean index `> i` — *smaller* |bias|
than the minority level, so at the bottom index the pool was provably empty
and the live `Phase8DrainReady.witness` forced `E8 = 0` (the obstruction that
motivated the repair).  The chosen repair kept the name `elimAbove` and
flipped its filter to `j.val < i.val` (reading "above" in the paper's
exponent order), so the live gate is no longer bottom-blind and these two
theorems no longer hold for it.  They are restated verbatim against the
frozen pre-flip pool `elimAboveIndex`, mirroring the `absorbConsumeReversed`
archive above.  Do not delete: this is the recorded proof of why the flip
was load-bearing. -/

/-- Frozen pre-flip pool (43295ea shape): non-`full` opposite-sign Mains at
Lean index strictly *greater* than `i` — i.e. strictly smaller |bias|. -/
def elimAboveIndex (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ¬ a.full ∧
    ∃ st j, st ≠ σ ∧ i.val < j.val ∧ a.bias = Bias.dyadic st j)

/-- `elimAboveIndex σ ⟨L⟩` is empty: there is no Lean index strictly above the
bottom. -/
theorem elimAboveIndex_bottom_sum_eq_zero (σ : Sign) (c : Config (AgentState L K)) :
    (elimAboveIndex (L := L) (K := K) σ (bottomIdx L)).sum c.count
      = 0 := by
  have hempty : elimAboveIndex (L := L) (K := K) σ (bottomIdx L)
      = (∅ : Finset (AgentState L K)) := by
    apply Finset.filter_eq_empty_iff.2
    rintro a -
    rintro ⟨-, -, st, j, -, hij, -⟩
    have := j.2
    simp only [bottomIdx] at hij
    omega
  rw [hempty, Finset.sum_empty]

/-- A positive `minorityAt` pool sum exhibits a member of the configuration
carrying exactly that bias. -/
private lemma exists_minority_mem_of_pool_pos (σ : Sign) (i : Fin (L + 1))
    (c : Config (AgentState L K))
    (hpos : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count) :
    ∃ a ∈ c, a.role = Role.main ∧ a.bias = Bias.dyadic σ i := by
  by_contra hno
  have hzero : (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [Phase8Convergence.minorityAt, Finset.mem_filter] at ha
    by_contra hcnt
    have hmem : a ∈ c := Multiset.count_pos.1 (Nat.pos_of_ne_zero hcnt)
    exact hno ⟨a, hmem, ha.2⟩
  omega

/-- **HISTORICAL: the pre-flip slot-8 ready witness forced `E8 = 0`.**  If
every `σ`-signed bias in the configuration sits at the bottom index, a
witness of the frozen pre-flip shape — `E8` eliminators at a Lean index
*strictly above* some populated minority level — forces `E8 = 0`.  This was
the live `Phase8DrainReady.witness` before 2026-07-16; the repair flipped
the `elimAbove` filter in place, so the live gate now demands the
higher-|bias| pool and is not subject to this obstruction. -/
theorem phase8DrainReadyAboveIndex_E8_eq_zero_of_bottom_only
    (σ : Sign) (E8 : ℕ) (c : Config (AgentState L K))
    (hwitness : Phase7Convergence.minorityU (L := L) (K := K) σ c ≥ 1 →
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count ∧
        E8 ≤ (elimAboveIndex (L := L) (K := K) σ i).sum c.count)
    (hmin : 1 ≤ Phase7Convergence.minorityU (L := L) (K := K) σ c)
    (hbottom : ∀ a ∈ c, ∀ i : Fin (L + 1),
      a.bias = Bias.dyadic σ i → i = bottomIdx L) :
    E8 = 0 := by
  obtain ⟨i, hpool, hE8⟩ := hwitness hmin
  obtain ⟨a, hmem, -, hbias⟩ := exists_minority_mem_of_pool_pos σ i c hpool
  have hi : i = bottomIdx L := hbottom a hmem i hbias
  rw [hi, elimAboveIndex_bottom_sum_eq_zero] at hE8
  omega

#print axioms absorbConsumeReversed_fst_bias_of_bottom
#print axioms absorbConsumeReversed_snd_bias_of_bottom
#print axioms absorbConsumeReversed_kills_eliminator
#print axioms elimAboveIndex_bottom_sum_eq_zero
#print axioms phase8DrainReadyAboveIndex_E8_eq_zero_of_bottom_only

end Phase8AbsorbDirectionImpossibility
end Ripple.PopulationProtocol.ExactMajority
