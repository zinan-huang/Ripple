/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# §5.2 Quantitative Upper Bound — scaffold

Kanaya §5.2 / Theorem 4 (quantitative): `P_EM` reaches a silent
configuration in O(n) expected parallel time and O(n log n) parallel time
with high probability on `n ≥ 4` agents under uniform random scheduling.
This scaffold states the Lean upper bound with an explicit
constant/externally bounded timer hypothesis; the literal
`protocolPEM n n n ...` timer range needs a separate theorem or a weakened
O(n²)-parallel statement.

Proof outline (`docs/TIME_BOUND_PLAN.md`):
- Phase A (ranking, Burman 2021 §3): O(n) expected parallel time.
- Phase B (swap): O(n) parallel time (`misorderedCount` decreases
  under uniform random pair selection).
- Phase C (decision/propagation/timer): O(n) expected parallel time.
- The constant-success phase argument gives O(n) expected time; repeating
  O(log n) windows gives O(n log n) with high probability.

This file is a **scaffold**.  The quantitative upper-bound claim is kept
as a target proposition until the phase-window stochastic proof is closed,
and the file lives outside the root import graph until then.  See
`docs/TIME_BOUND_PLAN.md` for the full plan.
-/
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal
import Ripple.PopulationProtocol.Majority.SSEM.Probability.ExpectedTime
import Mathlib.Analysis.PSeries


namespace SSEM

open scoped ENNReal

/-- PEM protocol family used by the time-bound layer.

The paper treats `trank` (the ranking-time/timer parameter) separately from
`Rmax` (the reset-count parameter).  In particular, Kanaya §5.2 assumes
`trank = O(1)`, while some qualitative Lean wrappers instantiate both
parameters by the same value. -/
abbrev PEMProtocol (n trank Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)

/-- Legacy/coupled time-layer instance used by the existing deterministic
proof blocks in this file.  This is not the paper's constant-`trank` regime
unless `Rmax` is externally bounded. -/
abbrev PEMProtocolCoupled (n Rmax Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  PEMProtocol n Rmax Rmax Emax Dmax hn

/-- Literal protocol instance from the current prompt.  The timer parameter is
linear in `n`, so Kanaya's constant-`trank` timer-drain argument does not
directly give an O(n) parallel-time bound for this instance. -/
abbrev ConcretePEM (n Emax Dmax : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  PEMProtocol n n n Emax Dmax hn

/-! ### Initial configuration predicate -/

/-- A configuration is *initial* when every agent's internal state is at the
protocol's default: `Unsettled`, rank 0, no leader, all counters zero.
Only the input opinion varies.  This matches the standard population-protocol
initialization where agents carry only their input. -/
def IsInitialConfig (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.role = .Unsettled ∧
    (C μ).1.rank.val = 0 ∧
    (C μ).1.leader = .F ∧
    (C μ).1.resetcount = 0 ∧
    (C μ).1.timer = 0 ∧
    (C μ).1.answer = .outA ∧
    (C μ).1.errorcount = 0 ∧
    (C μ).1.delaytimer = 0 ∧
    (C μ).1.children = 0

/-- A weaker predicate: all internal counters are bounded by `M`.
This is preserved by protocol execution when `M` is large enough. -/
def IsBoundedConfig (M : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.timer ≤ M ∧
    (C μ).1.resetcount ≤ M ∧
    (C μ).1.errorcount ≤ M ∧
    (C μ).1.delaytimer ≤ M ∧
    (C μ).1.children ≤ M

def IsTimerBoundedConfig (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n, (C μ).1.timer ≤ K

theorem IsInitialConfig.isBounded {C : Config (AgentState n) Opinion n}
    (h : IsInitialConfig C) : IsBoundedConfig 0 C := by
  intro μ; obtain ⟨_, _, _, hr, ht, _, he, hd, hc⟩ := h μ
  exact ⟨le_of_eq ht, le_of_eq hr, le_of_eq he, le_of_eq hd, Nat.le_of_eq hc⟩

theorem IsInitialConfig.isTimerBounded {C : Config (AgentState n) Opinion n}
    (h : IsInitialConfig C) : IsTimerBoundedConfig 0 C := by
  intro μ; exact le_of_eq (h μ).2.2.2.2.1

/-! ### Phase predicates for the stochastic layer -/

/-- `Sdec`-style local decision predicate: every median-rank agent already
carries the current exact-majority answer.  For odd `n` this is the single
median agent; for even `n` this is the lower median used by
`ceilHalf`. -/
def MedianAnswerCorrect (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.rank.val + 1 = ceilHalf n →
      (C μ).1.answer = majorityAnswer C

/-- Live median timer predicate used by the decision/timer phase windows. -/
def MedianTimerAtLeast (k : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.rank.val + 1 = ceilHalf n →
      k ≤ (C μ).1.timer

theorem MedianTimerAtLeast.mono {a b : ℕ}
    (hab : a ≤ b) {C : Config (AgentState n) Opinion n} :
    MedianTimerAtLeast b C → MedianTimerAtLeast a C := by
  intro hb μ hμ
  exact le_trans hab (hb μ hμ)

def MedianTimerAtMost (k : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n,
    (C μ).1.rank.val + 1 = ceilHalf n →
      (C μ).1.timer ≤ k

/-- Paper Table-2 `Tswap`: ranked configuration with the median timer still
large enough for the decision-window Chernoff argument.  Since `InSrank`
gives a unique median rank, the universal form is equivalent to the paper's
existential median-agent formulation. -/
def InTswap28 (C : Config (AgentState n) Opinion n) : Prop :=
  InSrank C ∧ MedianTimerAtLeast 28 C

/-- Timer-bounded version of paper `Tswap`, used when a protocol invariant is
threaded through a phase proof. -/
def InTswap28TimerBounded (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (InSrank C ∧ MedianTimerAtLeast 28 C ∧ MedianTimerAtMost K C) ∨
    IsConsensusConfig C

/-- After-swap version of paper `Tswap`, used by the current phase
composition: the swap work has already reached `Sswap`, and the median timer
still has the `28` units needed for the Lemma-9 survival/decision window. -/
def InTswap28SswapTimerBounded (K : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianTimerAtLeast 28 C ∧ MedianTimerAtMost K C) ∨
    IsConsensusConfig C

/-- Legacy helper, not paper `Tswap`: it starts after `Sswap` and requires only
positive median timer.  It is useful for already-closed coupled proofs, but is
too weak for the paper Lemma-9 timer-survival argument. -/
def InTswapTimerBounded (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianTimerAtLeast 1 C ∧ MedianTimerAtMost K C) ∨
    IsConsensusConfig C

def InSdecTimerBounded (K : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  (InSswap C ∧ MedianAnswerCorrect C ∧ MedianTimerAtLeast 1 C ∧
      MedianTimerAtMost K C) ∨
    IsConsensusConfig C

theorem MedianTimerAtMost_of_IsTimerBounded
    {K : ℕ} {C : Config (AgentState n) Opinion n}
    (h : IsTimerBoundedConfig K C) : MedianTimerAtMost K C := by
  intro μ _hμ
  exact h μ

theorem RankingEndpoint.to_InSrank {C : Config (AgentState n) Opinion n}
    (h : RankingEndpoint C) : InSrank C :=
  h.1

theorem RankingEndpoint.to_timerAtLeast_two_or_consensus
    {C : Config (AgentState n) Opinion n}
    (h : RankingEndpoint C) :
    MedianTimerAtLeast 2 C ∨ IsConsensusConfig C :=
  h.2

theorem RankingEndpoint.to_InSrank_and_timerAtLeast_two_or_consensus
    {C : Config (AgentState n) Opinion n}
    (h : RankingEndpoint C) :
    (InSrank C ∧ MedianTimerAtLeast 2 C) ∨ IsConsensusConfig C := by
  rcases h.2 with hTimer | hCons
  · exact Or.inl ⟨h.1, hTimer⟩
  · exact Or.inr hCons

/-- A median-wrong witness is exactly the negation of
`MedianAnswerCorrect`. -/
theorem not_MedianAnswerCorrect_iff_exists_median_wrong
    {C : Config (AgentState n) Opinion n} :
    ¬ MedianAnswerCorrect C ↔
      ∃ μ : Fin n,
        (C μ).1.rank.val + 1 = ceilHalf n ∧
          (C μ).1.answer ≠ majorityAnswer C := by
  classical
  unfold MedianAnswerCorrect
  constructor
  · intro h
    push_neg at h
    exact h
  · rintro ⟨μ, hμ, hwrong⟩ hcorr
    exact hwrong (hcorr μ hμ)

theorem MedianAnswerCorrect_of_no_median_wrong
    {C : Config (AgentState n) Opinion n}
    (h :
      ¬ ∃ μ : Fin n,
        (C μ).1.rank.val + 1 = ceilHalf n ∧
          (C μ).1.answer ≠ majorityAnswer C) :
    MedianAnswerCorrect C := by
  classical
  rw [← not_MedianAnswerCorrect_iff_exists_median_wrong] at h
  exact not_not.mp h

/-! ### Swap-phase good-pair counting

These are the first quantitative bridge lemmas for Phase B.  They turn the
existing deterministic descent theorem for a misordered pair into a lower bound
on the number of scheduler pairs that strictly decrease `misorderedCount`.
-/

/-- B-input agents that currently occupy the low-rank A side. -/
def wrongLowBSet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C u).2 = Opinion.B ∧ (C u).1.rank.val < nAOf C

/-- A-input agents that currently occupy the high-rank B side. -/
def wrongHighASet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C u).2 = Opinion.A ∧ nAOf C ≤ (C u).1.rank.val

/-- Agents currently occupying the low-rank side. -/
def lowRankSet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C u).1.rank.val < nAOf C

/-- A-input agents currently occupying the low-rank side. -/
def lowASet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun u => (C u).2 = Opinion.A ∧ (C u).1.rank.val < nAOf C

/-- Count of B-input agents on the low-rank side. -/
def wrongLowBCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (wrongLowBSet C).card

/-- Count of A-input agents on the high-rank side. -/
def wrongHighACount (C : Config (AgentState n) Opinion n) : ℕ :=
  (wrongHighASet C).card

/-- Auxiliary: cardinality of `{i : Fin n | i.val < k}` is exactly `k`
when `k ≤ n`.  This local copy keeps the time-bound layer independent of the
private helper used in the deterministic swap proof. -/
private theorem time_card_Fin_filter_val_lt {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  classical
  let toFin : Fin k → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hinj : Function.Injective toFin := by
    intro i j h
    have : i.val = j.val := congrArg (fun x : Fin n => x.val) h
    exact Fin.ext this
  have himg : (Finset.univ : Finset (Fin k)).image toFin
            = Finset.univ.filter (fun i : Fin n => i.val < k) := by
    ext i
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hfj⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      have : (toFin j).val = i.val := congrArg Fin.val hfj
      have hj : j.val < k := j.isLt
      exact this ▸ hj
    · rintro ⟨_, hi⟩
      refine ⟨⟨i.val, hi⟩, Finset.mem_univ _, ?_⟩
      apply Fin.eq_of_val_eq
      rfl
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]

/-- In an `Srank` configuration, exactly `k` agents have rank below `k`. -/
private theorem time_card_filter_rank_lt {C : Config (AgentState n) Opinion n}
    (hRank : InSrank C) {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < k)).card = k := by
  classical
  have hinj : Function.Injective (fun u : Fin n => (C u).1.rank) := hRank.ranks_inj
  have hsurj : Function.Surjective (fun u : Fin n => (C u).1.rank) :=
    Finite.injective_iff_surjective.mp hinj
  have himg : (Finset.univ.filter (fun u : Fin n => (C u).1.rank.val < k)).image
                (fun u => (C u).1.rank)
            = Finset.univ.filter (fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hi
      obtain ⟨u, hu⟩ := hsurj i
      refine ⟨u, ?_, hu⟩
      rw [show (C u).1.rank.val = i.val from congrArg Fin.val hu]
      exact hi
  rw [← Finset.card_image_of_injective _ hinj, himg, time_card_Fin_filter_val_lt hk]

theorem lowRankSet_card_of_InSrank {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (lowRankSet C).card = nAOf C := by
  unfold lowRankSet
  exact time_card_filter_rank_lt hSrank (by have := nAOf_add_nBOf C; omega)

theorem lowRankSet_eq_lowA_union_wrongLowB
    {C : Config (AgentState n) Opinion n} :
    lowRankSet C = lowASet C ∪ wrongLowBSet C := by
  classical
  ext u
  simp only [lowRankSet, lowASet, wrongLowBSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hlow
    cases h : (C u).2 with
    | A => exact Or.inl ⟨rfl, hlow⟩
    | B => exact Or.inr ⟨rfl, hlow⟩
  · rintro (⟨_, hlow⟩ | ⟨_, hlow⟩) <;> exact hlow

theorem agentsWithInput_A_eq_lowA_union_wrongHighA
    {C : Config (AgentState n) Opinion n} :
    C.agentsWithInput Opinion.A = lowASet C ∪ wrongHighASet C := by
  classical
  ext u
  simp only [Config.agentsWithInput, Config.inputOf, lowASet, wrongHighASet,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hA
    by_cases hlow : (C u).1.rank.val < nAOf C
    · exact Or.inl ⟨hA, hlow⟩
    · exact Or.inr ⟨hA, by omega⟩
  · rintro (⟨hA, _⟩ | ⟨hA, _⟩) <;> exact hA

theorem lowA_disjoint_wrongLowB {C : Config (AgentState n) Opinion n} :
    Disjoint (lowASet C) (wrongLowBSet C) := by
  classical
  rw [Finset.disjoint_left]
  intro u huA huB
  rw [lowASet, Finset.mem_filter] at huA
  rw [wrongLowBSet, Finset.mem_filter] at huB
  rw [huA.2.1] at huB
  cases huB.2.1

theorem lowA_disjoint_wrongHighA {C : Config (AgentState n) Opinion n} :
    Disjoint (lowASet C) (wrongHighASet C) := by
  classical
  rw [Finset.disjoint_left]
  intro u huLow huHigh
  rw [lowASet, Finset.mem_filter] at huLow
  rw [wrongHighASet, Finset.mem_filter] at huHigh
  omega

/-- In an `Srank` configuration, the two misplaced sides have the same
cardinality. -/
theorem wrongLowBCount_eq_wrongHighACount_of_InSrank
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C) :
    wrongLowBCount C = wrongHighACount C := by
  classical
  have hLowPartition :
      (lowASet C).card + (wrongLowBSet C).card = nAOf C := by
    have hcard := Finset.card_union_of_disjoint
      (lowA_disjoint_wrongLowB (C := C))
    rw [← lowRankSet_eq_lowA_union_wrongLowB (C := C)] at hcard
    rw [lowRankSet_card_of_InSrank hSrank] at hcard
    exact hcard.symm
  have hAPartition :
      (lowASet C).card + (wrongHighASet C).card = nAOf C := by
    have hcard := Finset.card_union_of_disjoint
      (lowA_disjoint_wrongHighA (C := C))
    rw [← agentsWithInput_A_eq_lowA_union_wrongHighA (C := C)] at hcard
    unfold nAOf
    exact hcard.symm
  unfold wrongLowBCount wrongHighACount
  omega

/-- If no B-input agent remains on the low-rank side, then an `Srank`
configuration is already in `Sswap`. -/
theorem InSswap_of_InSrank_of_wrongLowBCount_zero
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (h0 : wrongLowBCount C = 0) :
    InSswap C := by
  classical
  have hLowEmpty : wrongLowBSet C = ∅ := by
    unfold wrongLowBCount at h0
    exact Finset.card_eq_zero.mp h0
  have hHigh0 : wrongHighACount C = 0 := by
    rw [← wrongLowBCount_eq_wrongHighACount_of_InSrank hSrank]
    exact h0
  have hHighEmpty : wrongHighASet C = ∅ := by
    unfold wrongHighACount at hHigh0
    exact Finset.card_eq_zero.mp hHigh0
  refine { toInSrank := hSrank, input_rank := ?_ }
  intro v
  constructor
  · intro hA
    by_contra hnot
    push_neg at hnot
    have hmem : v ∈ wrongHighASet C := by
      rw [wrongHighASet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hA, hnot⟩
    rw [hHighEmpty] at hmem
    exact Finset.notMem_empty v hmem
  · intro hLow
    cases h : (C v).2 with
    | A => rfl
    | B =>
        have hmem : v ∈ wrongLowBSet C := by
          rw [wrongLowBSet, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, h, hLow⟩
        rw [hLowEmpty] at hmem
        exact (Finset.notMem_empty v hmem).elim

/-- In an `Sswap` configuration, the single-side misplaced count is zero. -/
theorem wrongLowBCount_eq_zero_of_InSswap
    {C : Config (AgentState n) Opinion n} (hSswap : InSswap C) :
    wrongLowBCount C = 0 := by
  classical
  unfold wrongLowBCount
  rw [Finset.card_eq_zero]
  apply Finset.ext
  intro v
  constructor
  · intro hmem
    rw [wrongLowBSet, Finset.mem_filter] at hmem
    have hRankGe : nAOf C ≤ (C v).1.rank.val := by
      by_contra hlt
      push_neg at hlt
      have hA : (C v).2 = Opinion.A := (hSswap.input_rank v).mpr hlt
      rw [hA] at hmem
      cases hmem.2.1
    omega
  · intro hmem
    exact (Finset.notMem_empty v hmem).elim

/-- If an `Srank` configuration has not yet reached `Sswap`, the single-side
misplaced count is positive. -/
theorem wrongLowBCount_pos_of_InSrank_not_InSswap
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hNotSwap : ¬ InSswap C) :
    0 < wrongLowBCount C := by
  by_contra hpos
  have hzero : wrongLowBCount C = 0 := by omega
  exact hNotSwap (InSswap_of_InSrank_of_wrongLowBCount_zero hSrank hzero)

/-- Within `Srank`, `Sswap` is exactly the zero level of the single-side
misplaced potential. -/
theorem InSswap_iff_wrongLowBCount_zero_of_InSrank
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C) :
    InSswap C ↔ wrongLowBCount C = 0 := by
  constructor
  · exact wrongLowBCount_eq_zero_of_InSswap
  · exact InSswap_of_InSrank_of_wrongLowBCount_zero hSrank

/-- The single-side misplaced count is always bounded by the population size. -/
theorem wrongLowBCount_le_n (C : Config (AgentState n) Opinion n) :
    wrongLowBCount C ≤ n := by
  unfold wrongLowBCount wrongLowBSet
  calc
    (Finset.univ.filter
        (fun u : Fin n => (C u).2 = Opinion.B ∧ (C u).1.rank.val < nAOf C)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- Stepping a low-side B against a high-side A removes that low-side B from
the single-side misplaced set and changes no other membership. -/
theorem wrongLowBSet_step_at_wrongLowB_wrongHighA
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C)
    {u v : Fin n}
    (hu : u ∈ wrongLowBSet C) (hv : v ∈ wrongHighASet C) :
    wrongLowBSet (C.step (protocolPEM n trank Rmax rankDelta) u v) =
      (wrongLowBSet C).erase u := by
  classical
  rw [wrongLowBSet, Finset.mem_filter] at hu
  rw [wrongHighASet, Finset.mem_filter] at hv
  rcases hu with ⟨_, huB, huLow⟩
  rcases hv with ⟨_, hvA, hvHigh⟩
  have huv : u ≠ v := by
    intro huv
    subst v
    rw [huB] at hvA
    cases hvA
  have hRankLt : (C u).1.rank < (C v).1.rank := by
    exact_mod_cast (by omega : (C u).1.rank.val < (C v).1.rank.val)
  have hMis : MisorderedPair C (u, v) :=
    ⟨huB, hvA, hRankLt⟩
  set C' := C.step (protocolPEM n trank Rmax rankDelta) u v
  have hRankSwap := transitionPEM_rank_swap_at_misorder
    (trank := trank) (Rmax := Rmax) hRankDelta hSrank hMis
  have huRank : (C' u).1.rank = (C v).1.rank := by
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) u).1.rank =
      (C v).1.rank
    unfold Config.step
    simp only [if_neg huv, if_pos rfl]
    exact hRankSwap.1
  have hvRank : (C' v).1.rank = (C u).1.rank := by
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) v).1.rank =
      (C u).1.rank
    unfold Config.step
    simp only [if_neg huv, if_neg huv.symm, if_pos rfl]
    exact hRankSwap.2
  have hOtherRank :
      ∀ w : Fin n, w ≠ u → w ≠ v → (C' w).1.rank = (C w).1.rank := by
    intro w hwu hwv
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).1.rank =
      (C w).1.rank
    unfold Config.step
    simp [huv, hwu, hwv]
  have hInput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    exact step_input_preserved
      (protocolPEM n trank Rmax rankDelta) C u v w
  have hnA : nAOf C' = nAOf C := by
    simpa [C'] using
      (nAOf_step_eq (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDelta) C u v)
  ext w
  by_cases hwu : w = u
  · subst w
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and]
    constructor
    · intro hmem
      rw [wrongLowBSet, Finset.mem_filter] at hmem
      have hlow' : (C v).1.rank.val < nAOf C := by
        have hlow'' : (C' u).1.rank.val < nAOf C' := hmem.2.2
        rw [huRank, hnA] at hlow''
        exact hlow''
      omega
    · intro h
      exact h.elim
  · by_cases hwv : w = v
    · subst w
      simp only [Finset.mem_erase, huv.symm, true_and]
      constructor
      · intro hmem
        rw [wrongLowBSet, Finset.mem_filter] at hmem
        have hvB : (C v).2 = Opinion.B := by
          rw [← hInput v]
          exact hmem.2.1
        rw [hvA] at hvB
        cases hvB
      · intro hmem
        rw [wrongLowBSet, Finset.mem_filter] at hmem
        have hvB : (C v).2 = Opinion.B := hmem.2.2.1
        rw [hvA] at hvB
        cases hvB
    · rw [wrongLowBSet, Finset.mem_erase, wrongLowBSet]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hInput w, hOtherRank w hwu hwv, hnA]
      constructor
      · intro hmem
        exact ⟨hwu, hmem⟩
      · intro hmem
        exact hmem.2

/-- A low-side B/high-side A interaction strictly decreases the single-side
misplaced count. -/
theorem wrongLowBCount_decreases_step_at_wrongLowB_wrongHighA
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C)
    {u v : Fin n}
    (hu : u ∈ wrongLowBSet C) (hv : v ∈ wrongHighASet C) :
    wrongLowBCount (C.step (protocolPEM n trank Rmax rankDelta) u v) <
      wrongLowBCount C := by
  classical
  have hset := wrongLowBSet_step_at_wrongLowB_wrongHighA
    (trank := trank) (Rmax := Rmax) hRankDelta hSrank hu hv
  unfold wrongLowBCount
  have hpos : 0 < (wrongLowBSet C).card := Finset.card_pos.mpr ⟨u, hu⟩
  rw [hset, Finset.card_erase_of_mem hu]
  omega

/-- While the configuration is in `Srank`, one PEM step cannot increase the
single-side misplaced-count potential.  A Phase-4 swap only exchanges a lower
ranked `B` with a higher ranked `A`; all other settled pairs preserve ranks. -/
theorem wrongLowBCount_step_le_of_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hSrank : InSrank C)
    (u v : Fin n) :
    wrongLowBCount (C.step (protocolPEM n trank Rmax rankDelta) u v) ≤
      wrongLowBCount C := by
  classical
  by_cases huv : u = v
  · subst v
    simp [Config.step]
  · set P := protocolPEM n trank Rmax rankDelta
    set C' := C.step P u v
    have hInput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
      intro w
      simpa [C', P] using step_input_preserved P C u v w
    have hnA : nAOf C' = nAOf C := by
      simpa [C', P] using
        (nAOf_step_eq (trank := trank) (Rmax := Rmax)
          (rankDelta := rankDelta) C u v)
    have hRankNe : (C u).1.rank ≠ (C v).1.rank := by
      intro hEq
      exact huv (hSrank.ranks_inj hEq)
    by_cases hswap :
        (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A
    · have hMis : MisorderedPair C (u, v) := ⟨hswap.2.1, hswap.2.2, hswap.1⟩
      have hRankSwap := transitionPEM_rank_swap_at_misorder
        (trank := trank) (Rmax := Rmax) hRankDelta hSrank hMis
      have huRank : (C' u).1.rank = (C v).1.rank := by
        show ((C.step P u v) u).1.rank = (C v).1.rank
        simp only [P, Config.step, if_neg huv, if_pos rfl]
        exact hRankSwap.1
      have hvRank : (C' v).1.rank = (C u).1.rank := by
        show ((C.step P u v) v).1.rank = (C u).1.rank
        simp only [P, Config.step, if_neg huv, if_neg (Ne.symm huv), if_pos rfl]
        exact hRankSwap.2
      have hOtherRank :
          ∀ w : Fin n, w ≠ u → w ≠ v → (C' w).1.rank = (C w).1.rank := by
        intro w hwu hwv
        show ((C.step P u v) w).1.rank = (C w).1.rank
        simp [P, Config.step, huv, hwu, hwv]
      unfold wrongLowBCount
      apply Finset.card_le_card
      intro w hw
      rw [wrongLowBSet, Finset.mem_filter] at hw
      rw [wrongLowBSet, Finset.mem_filter]
      rcases hw with ⟨_, hwB, hwLow⟩
      rw [hInput w] at hwB
      refine ⟨Finset.mem_univ _, hwB, ?_⟩
      by_cases hwu : w = u
      · subst w
        rw [huRank, hnA] at hwLow
        have hltRank : (C u).1.rank.val < (C v).1.rank.val := by
          exact_mod_cast hswap.1
        omega
      · by_cases hwv : w = v
        · subst w
          rw [hswap.2.2] at hwB
          cases hwB
        · rw [hOtherRank w hwu hwv, hnA] at hwLow
          exact hwLow
    · have hRanks := transitionPEM_rank_of_no_swap
        (n := n) (trank := trank) (Rmax := Rmax)
        (rankDelta := rankDelta) hRankDelta
        (s₀ := (C u).1) (s₁ := (C v).1)
        (x₀ := (C u).2) (x₁ := (C v).2)
        (hSrank.allSettled u) (hSrank.allSettled v) hswap hRankNe
      have huRank : (C' u).1.rank = (C u).1.rank := by
        show ((C.step P u v) u).1.rank = (C u).1.rank
        simp only [P, Config.step, if_neg huv, if_pos rfl]
        exact hRanks.1
      have hvRank : (C' v).1.rank = (C v).1.rank := by
        show ((C.step P u v) v).1.rank = (C v).1.rank
        simp only [P, Config.step, if_neg huv, if_neg (Ne.symm huv), if_pos rfl]
        exact hRanks.2
      have hOtherRank :
          ∀ w : Fin n, w ≠ u → w ≠ v → (C' w).1.rank = (C w).1.rank := by
        intro w hwu hwv
        show ((C.step P u v) w).1.rank = (C w).1.rank
        simp [P, Config.step, huv, hwu, hwv]
      unfold wrongLowBCount
      apply Finset.card_le_card
      intro w hw
      rw [wrongLowBSet, Finset.mem_filter] at hw
      rw [wrongLowBSet, Finset.mem_filter]
      rcases hw with ⟨_, hwB, hwLow⟩
      rw [hInput w] at hwB
      refine ⟨Finset.mem_univ _, hwB, ?_⟩
      by_cases hwu : w = u
      · subst w
        rw [huRank, hnA] at hwLow
        exact hwLow
      · by_cases hwv : w = v
        · subst w
          rw [hvRank, hnA] at hwLow
          exact hwLow
        · rw [hOtherRank w hwu hwv, hnA] at hwLow
          exact hwLow

/-- Every low-side B / high-side A ordered pair is a good scheduler pair for
the single-side misplaced-count potential. -/
theorem wrongLowB_product_wrongHighA_subset_GoodPairs_wrongLowBCount
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (wrongLowBSet C).product (wrongHighASet C) ⊆
      Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) wrongLowBCount C := by
  intro p hp
  rcases p with ⟨u, v⟩
  have hp' := Finset.mem_product.mp hp
  rcases hp' with ⟨hu, hv⟩
  rw [wrongLowBSet, Finset.mem_filter] at hu
  rw [wrongHighASet, Finset.mem_filter] at hv
  have huv : u ≠ v := by
    intro huv
    subst v
    rw [hu.2.1] at hv
    cases hv.2.1
  exact (Probability.mem_GoodPairs
    (protocolPEM n trank Rmax rankDelta) wrongLowBCount C (u, v)).mpr
      ⟨huv,
        wrongLowBCount_decreases_step_at_wrongLowB_wrongHighA
          (trank := trank) (Rmax := Rmax) hRankDelta hSrank
          (by
            rw [wrongLowBSet, Finset.mem_filter]
            exact hu)
          (by
            rw [wrongHighASet, Finset.mem_filter]
            exact hv)⟩

/-- Product-form lower bound on scheduler pairs that decrease the single-side
misplaced-count potential. -/
theorem wrongLowB_mul_wrongHighA_le_GoodPairs_wrongLowBCount_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    wrongLowBCount C * wrongHighACount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) wrongLowBCount C).card := by
  unfold wrongLowBCount wrongHighACount
  rw [← Finset.card_product]
  exact Finset.card_le_card
    (wrongLowB_product_wrongHighA_subset_GoodPairs_wrongLowBCount
      (trank := trank) (Rmax := Rmax) hRankDelta hSrank)

/-- Square-form lower bound on scheduler pairs that decrease the single-side
misplaced-count potential. -/
theorem wrongLowB_square_le_GoodPairs_wrongLowBCount_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    wrongLowBCount C * wrongLowBCount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) wrongLowBCount C).card := by
  have hEq : wrongHighACount C = wrongLowBCount C :=
    (wrongLowBCount_eq_wrongHighACount_of_InSrank hSrank).symm
  simpa [hEq] using
    (wrongLowB_mul_wrongHighA_le_GoodPairs_wrongLowBCount_card
      (trank := trank) (Rmax := Rmax) hRankDelta hSrank)

/-- One-step scheduler mass of side-potential progress pairs is at least
`i^2 / (n * (n - 1))`, with `i = wrongLowBCount C`. -/
theorem wrongLowB_square_sideGoodPairs_mass_lower_bound
    {n trank Rmax : ℕ} (hn : 2 ≤ n)
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn
        (Probability.GoodPairs
          (protocolPEM n trank Rmax rankDelta) wrongLowBCount C) := by
  rw [Probability.pairSetMass_GoodPairs]
  exact mul_le_mul_left
    (by exact_mod_cast
      wrongLowB_square_le_GoodPairs_wrongLowBCount_card hRankDelta hSrank)
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹)

/-- PEM specialization of the side-potential square-form scheduler mass
bound. -/
theorem PEM_wrongLowB_square_sideGoodPairs_mass_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn2
        (Probability.GoodPairs
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) wrongLowBCount C) := by
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (wrongLowB_square_sideGoodPairs_mass_lower_bound
      (n := n) (trank := Rmax) (Rmax := Rmax) hn2
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hSrank)

/-- One-step probability form of the side-potential square lower bound. -/
theorem PEM_wrongLowB_one_step_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 := by
  classical
  rw [Probability.ProbHitWithin_one_eq_pairSetMass_GoodPairs]
  exact PEM_wrongLowB_square_sideGoodPairs_mass_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window form of the side-potential square lower bound. -/
theorem PEM_wrongLowB_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) {t : ℕ} (ht : 1 ≤ t) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => wrongLowBCount D < wrongLowBCount C) ht
    (PEM_wrongLowB_one_step_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank)

/-- Phase-B square-form progress bound.

This is the bound needed for Kanaya Lemma 7.  At misplaced-side level
`k = wrongLowBCount C`, the one-step probability of decreasing the swap
potential is at least `k^2 / (n * (n - 1))`.  Using the linear
`misorderedCount / (n * (n - 1))` bound instead would introduce a harmonic
sum and only give an `O(n^2 log n)` sequential expectation. -/
theorem PEM_swap_phase_wrongLowB_square_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 := by
  exact PEM_wrongLowB_one_step_descent_prob_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- If the single-side misplaced count is positive, at least one ordered pair
strictly decreases it in one random interaction. -/
theorem PEM_wrongLowB_positive_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < wrongLowBCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 := by
  have hcount : (1 : ENNReal) ≤
      ((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) := by
    have hsq : 1 ≤ wrongLowBCount C * wrongLowBCount C := by
      nlinarith [hpos]
    exact_mod_cast hsq
  calc
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹
        = (1 : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
    _ ≤ ((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
          exact mul_le_mul_left hcount _
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 :=
          PEM_wrongLowB_one_step_descent_prob_lower_bound
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window version of
`PEM_wrongLowB_positive_descent_prob_lower_bound`. -/
theorem PEM_wrongLowB_positive_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < wrongLowBCount C)
    {t : ℕ} (ht : 1 ≤ t) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => wrongLowBCount D < wrongLowBCount C) ht
    (PEM_wrongLowB_positive_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank hpos)

/-- Swap-phase entry form: every `Srank` state outside `Sswap` has at least
one scheduler pair that decreases the single-side misplaced count. -/
theorem PEM_swap_not_done_wrongLowB_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hNotSwap : ¬ InSswap C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) 1 := by
  exact PEM_wrongLowB_positive_descent_prob_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn2 hn0 hSrank
    (wrongLowBCount_pos_of_InSrank_not_InSswap hSrank hNotSwap)

/-- Nonzero-window version of
`PEM_swap_not_done_wrongLowB_descent_prob_lower_bound`. -/
theorem PEM_swap_not_done_wrongLowB_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hNotSwap : ¬ InSswap C)
    {t : ℕ} (ht : 1 ≤ t) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => wrongLowBCount D < wrongLowBCount C) ht
    (PEM_swap_not_done_wrongLowB_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hSrank hNotSwap)

/-- Marginal one-step version of
`PEM_wrongLowB_positive_descent_prob_lower_bound`, for phase composition.
The strict-descent target is false at the start state. -/
theorem PEM_wrongLowB_positive_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < wrongLowBCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => wrongLowBCount D < wrongLowBCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact Nat.lt_irrefl _ h
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_wrongLowB_positive_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hSrank hpos)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Marginal one-step swap-phase entry form: every `Srank` state outside
`Sswap` has one-step endpoint probability at least one ordered pair of
strictly decreasing the side misplaced-count potential. -/
theorem PEM_swap_not_done_wrongLowB_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hNotSwap : ¬ InSswap C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongLowBCount D < wrongLowBCount C)
        (by classical exact inferInstance) 1 := by
  exact PEM_wrongLowB_positive_descent_probReached_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn2 hn0 hSrank
    (wrongLowBCount_pos_of_InSrank_not_InSswap hSrank hNotSwap)

/-- Every low-side B paired with every high-side A is a misordered pair. -/
theorem wrongLowB_product_wrongHighA_subset_misorderedSet
    {C : Config (AgentState n) Opinion n} :
    (wrongLowBSet C).product (wrongHighASet C) ⊆ misorderedSet C := by
  intro p hp
  rcases p with ⟨u, v⟩
  have hp' := Finset.mem_product.mp hp
  rcases hp' with ⟨hu, hv⟩
  rw [wrongLowBSet, Finset.mem_filter] at hu
  rw [wrongHighASet, Finset.mem_filter] at hv
  rcases hu with ⟨_, huB, huLow⟩
  rcases hv with ⟨_, hvA, hvHigh⟩
  exact mem_misorderedSet.mpr ⟨huB, hvA, by omega⟩

/-- Product-form lower bound on the number of misordered pairs. -/
theorem wrongLowB_mul_wrongHighA_le_misorderedCount
    {C : Config (AgentState n) Opinion n} :
    wrongLowBCount C * wrongHighACount C ≤ misorderedCount C := by
  unfold wrongLowBCount wrongHighACount misorderedCount
  rw [← Finset.card_product]
  exact Finset.card_le_card wrongLowB_product_wrongHighA_subset_misorderedSet

/-- Every currently misordered ordered pair is a good scheduler pair for the
`misorderedCount` potential. -/
theorem misorderedSet_subset_GoodPairs_misorderedCount
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    misorderedSet C ⊆
      Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) misorderedCount C := by
  intro p hp
  rcases p with ⟨u, v⟩
  have hMis : MisorderedPair C (u, v) := mem_misorderedSet.mp hp
  rcases hMis with ⟨huB, hvA, hlt⟩
  have huv : u ≠ v := by
    intro huv
    subst v
    rw [huB] at hvA
    cases hvA
  exact (Probability.mem_GoodPairs
    (protocolPEM n trank Rmax rankDelta) misorderedCount C (u, v)).mpr
      ⟨huv, misorderedCount_decreases_step_at_misorder
        hRankDelta hSrank ⟨huB, hvA, hlt⟩⟩

/-- The number of good scheduler pairs is at least the current
`misorderedCount`. -/
theorem misorderedCount_le_GoodPairs_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    misorderedCount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) misorderedCount C).card := by
  unfold misorderedCount
  exact Finset.card_le_card
    (misorderedSet_subset_GoodPairs_misorderedCount hRankDelta hSrank)

/-- Product-form lower bound on swap-progress scheduler pairs. -/
theorem wrongLowB_mul_wrongHighA_le_GoodPairs_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    wrongLowBCount C * wrongHighACount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) misorderedCount C).card := by
  exact (wrongLowB_mul_wrongHighA_le_misorderedCount (C := C)).trans
    (misorderedCount_le_GoodPairs_card hRankDelta hSrank)

/-- Square-form lower bound on swap-progress scheduler pairs.  Here
`wrongLowBCount` is the common misplaced-side count in an `Srank`
configuration. -/
theorem wrongLowB_square_le_GoodPairs_card
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    wrongLowBCount C * wrongLowBCount C ≤
      (Probability.GoodPairs
        (protocolPEM n trank Rmax rankDelta) misorderedCount C).card := by
  have hEq : wrongHighACount C = wrongLowBCount C :=
    (wrongLowBCount_eq_wrongHighACount_of_InSrank hSrank).symm
  simpa [hEq] using
    (wrongLowB_mul_wrongHighA_le_GoodPairs_card
      (trank := trank) (Rmax := Rmax) hRankDelta hSrank)

/-- One-step scheduler mass of swap-progress pairs is at least
`misorderedCount / (n * (n - 1))`. -/
theorem misordered_goodPairs_mass_lower_bound
    {n trank Rmax : ℕ} (hn : 2 ≤ n)
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    ((misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn
        (Probability.GoodPairs
          (protocolPEM n trank Rmax rankDelta) misorderedCount C) := by
  rw [Probability.pairSetMass_GoodPairs]
  exact mul_le_mul_left
    (by exact_mod_cast
      misorderedCount_le_GoodPairs_card hRankDelta hSrank)
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹)

/-- Specialization of the swap good-pair mass lower bound to the PEM protocol
family used in the time-bound theorem. -/
theorem PEM_misordered_goodPairs_mass_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    ((misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn2
        (Probability.GoodPairs
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) misorderedCount C) := by
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (misordered_goodPairs_mass_lower_bound
      (n := n) (trank := Rmax) (Rmax := Rmax) hn2
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hSrank)

/-- One-step probability form of the linear `misorderedCount` good-pair
lower bound. -/
theorem PEM_misordered_one_step_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    ((misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) 1 := by
  classical
  rw [Probability.ProbHitWithin_one_eq_pairSetMass_GoodPairs]
  exact PEM_misordered_goodPairs_mass_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window form of the linear `misorderedCount` lower bound. -/
theorem PEM_misordered_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) {t : ℕ} (ht : 1 ≤ t) :
    ((misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => misorderedCount D < misorderedCount C) ht
    (PEM_misordered_one_step_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank)

/-- If an `Srank` configuration has a positive misordered count, the one-step
probability of strictly decreasing that count is at least the mass of one
ordered scheduler pair. -/
theorem PEM_misordered_positive_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < misorderedCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) 1 := by
  have hcount : (1 : ENNReal) ≤ (misorderedCount C : ENNReal) := by
    exact_mod_cast hpos
  calc
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹
        = (1 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
    _ ≤ (misorderedCount C : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
          exact mul_le_mul_left hcount _
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) 1 :=
          PEM_misordered_one_step_descent_prob_lower_bound
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window version of `PEM_misordered_positive_descent_prob_lower_bound`. -/
theorem PEM_misordered_positive_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) (hpos : 0 < misorderedCount C)
    {t : ℕ} (ht : 1 ≤ t) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => misorderedCount D < misorderedCount C) ht
    (PEM_misordered_positive_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank hpos)

/-- One-step scheduler mass of swap-progress pairs is at least the Kanaya
square-form lower bound `i^2 / (n * (n - 1))`, where `i` is the common
misplaced-side count. -/
theorem wrongLowB_square_goodPairs_mass_lower_bound
    {n trank Rmax : ℕ} (hn : 2 ≤ n)
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankDelta : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn
        (Probability.GoodPairs
          (protocolPEM n trank Rmax rankDelta) misorderedCount C) := by
  rw [Probability.pairSetMass_GoodPairs]
  exact mul_le_mul_left
    (by exact_mod_cast
      wrongLowB_square_le_GoodPairs_card hRankDelta hSrank)
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹)

/-- PEM specialization of the square-form swap good-pair mass lower bound. -/
theorem PEM_wrongLowB_square_goodPairs_mass_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.pairSetMass n hn2
        (Probability.GoodPairs
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) misorderedCount C) := by
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (wrongLowB_square_goodPairs_mass_lower_bound
      (n := n) (trank := Rmax) (Rmax := Rmax) hn2
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hSrank)

/-- One-step probability form of the Kanaya square lower bound for swap
progress measured by `misorderedCount`. -/
theorem PEM_wrongLowB_square_swap_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) 1 := by
  classical
  rw [Probability.ProbHitWithin_one_eq_pairSetMass_GoodPairs]
  exact PEM_wrongLowB_square_goodPairs_mass_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank

/-- Nonzero-window form of the Kanaya square lower bound for swap progress. -/
theorem PEM_wrongLowB_square_swap_window_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) {t : ℕ} (ht : 1 ≤ t) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C) t := by
  exact Probability.ProbHitWithin_lower_bound_of_one_lower_bound
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => misorderedCount D < misorderedCount C) ht
    (PEM_wrongLowB_square_swap_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hSrank)

/-- Marginal one-step version of the Kanaya square lower bound for swap
progress measured by `misorderedCount`. -/
theorem PEM_wrongLowB_square_swap_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => misorderedCount D < misorderedCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => misorderedCount D < misorderedCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact Nat.lt_irrefl _ h
  have hhit :
      (((wrongLowBCount C * wrongLowBCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_wrongLowB_square_swap_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hSrank)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-! ### Decision-phase one-step probability witnesses -/

/-- Any concrete one-step decision witness gives the exact ordered-pair
scheduler lower bound for decreasing `wrongAnswerCount`. -/
theorem PEM_wrongAnswer_one_step_descent_prob_lower_bound_of_step
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hdec :
      wrongAnswerCount
        (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) u v) <
      wrongAnswerCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  exact Probability.ProbHitWithin_one_lower_bound_of_step
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
    (fun D => wrongAnswerCount D < wrongAnswerCount C)
    (by exact Nat.lt_irrefl (wrongAnswerCount C)) huv hdec

/-- Even-population median-pair decision step as a one-step probability lower
bound for decreasing `wrongAnswerCount`. -/
theorem PEM_even_median_pair_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_agree : (C u).2 = (C v).2)
    (hne : nAOf C ≠ nBOf C)
    (h_one_wrong : (C u).1.answer ≠ majorityAnswer C ∨
      (C v).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  apply PEM_wrongAnswer_one_step_descent_prob_lower_bound_of_step
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 huv
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (decision_step_at_median_pair_even_decreases
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC huv hpar hu_med hv_upper h_inputs_agree hne hn4 h_one_wrong).2

/-- Even-population tie-case median-pair decision step as a one-step
probability lower bound for decreasing `wrongAnswerCount`. -/
theorem PEM_even_median_pair_tie_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (h_inputs_disagree : (C u).2 ≠ (C v).2)
    (hTie : nAOf C = nBOf C)
    (h_one_wrong : (C u).1.answer ≠ majorityAnswer C ∨
      (C v).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  apply PEM_wrongAnswer_one_step_descent_prob_lower_bound_of_step
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 huv
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (decision_step_at_median_pair_even_tie_decreases
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC huv hpar hu_med hv_upper h_inputs_disagree hTie hn4 h_one_wrong).2

/-- If `n` is even and some median agent is wrong, then the appropriate
median-pair witness (strict-majority or tie case) gives a one-step scheduler
lower bound for decreasing `wrongAnswerCount`. -/
theorem PEM_even_median_wrong_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  classical
  by_cases hTie : nAOf C = nBOf C
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong_tie hC hpar hn4 hTie h_med_wrong
    exact PEM_even_median_pair_tie_decision_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC huv hpar hu_med hv_upper h_disagree hTie h_wrong
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong hC hpar hn4 hTie h_med_wrong
    exact PEM_even_median_pair_decision_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC huv hpar hu_med hv_upper h_agree hTie h_wrong

/-- Even-population median-wrong decision reaches the local `Sdec` predicate
(`MedianAnswerCorrect`) in one median-pair step, preserving `InSswap`. -/
theorem PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hRankFix := rankDeltaOSSR_satisfies_fix
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have htarget_not : ¬ (InSswap C ∧ MedianAnswerCorrect C) := by
    intro hTarget
    rcases h_med_wrong with ⟨μ, hμ, hwrong⟩
    exact hwrong (hTarget.2 μ hμ)
  by_cases hTie : nAOf C = nBOf C
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong_tie hC hpar hn4 hTie h_med_wrong
    have hsu := hC.allSettled u
    have hsv := hC.allSettled v
    have h_no_swap : ¬((C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
      intro h
      rcases h with ⟨huB, _hvA⟩
      have hsum := nAOf_add_nBOf C
      have hu_low : (C u).1.rank.val < nAOf C := by omega
      have huA : (C u).2 = Opinion.A := (hC.input_rank u).mpr hu_low
      rw [huA] at huB
      cases huB
    obtain ⟨h_u, _h_v, h_others, _h_inputs⟩ :=
      step_at_median_pair_even_disagreed_inputs
        (trank := Rmax) (Rmax := Rmax)
        hRankFix huv hsu hsv hpar hu_med hv_upper h_disagree h_no_swap hn4
    have hSwap' : InSswap (C.step P u v) := by
      have hdec := decision_step_at_median_pair_even_tie_decreases
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hC huv hpar hu_med hv_upper h_disagree hTie hn4 h_wrong
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hdec.1
    have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C u v)
    have h_u_correct : (C.step P u v u).1.answer = majorityAnswer (C.step P u v) := by
      have h_outT : majorityAnswer C = .outT := majorityAnswer_eq_outT_of_tie hTie
      have hu_state : (C.step P u v u).1 = {(C u).1 with answer := .outT} := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using h_u
      rw [hmaj, h_outT, hu_state]
    have h_u_med' : (C.step P u v u).1.rank.val + 1 = ceilHalf n := by
      have hu_state : (C.step P u v u).1 = {(C u).1 with answer := .outT} := by
        simpa [P, PEMProtocolCoupled, PEMProtocol] using h_u
      rw [hu_state, hceil]
      simpa using hu_med
    have hGoal : InSswap (C.step P u v) ∧ MedianAnswerCorrect (C.step P u v) := by
      refine ⟨hSwap', ?_⟩
      intro η hη
      have hηu : η = u := by
        apply hSwap'.ranks_inj
        apply Fin.eq_of_val_eq
        have hηval : (C.step P u v η).1.rank.val = ceilHalf n - 1 := by omega
        have huval : (C.step P u v u).1.rank.val = ceilHalf n - 1 := by omega
        exact hηval.trans huval.symm
      subst η
      exact h_u_correct
    exact Probability.ProbHitWithin_one_lower_bound_of_step
      (P := P) hn2 C (fun D => InSswap D ∧ MedianAnswerCorrect D)
      htarget_not huv hGoal
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
      evenCase_witness_when_median_wrong hC hpar hn4 hTie h_med_wrong
    have hsu := hC.allSettled u
    have hsv := hC.allSettled v
    have hC'_eq := step_at_median_pair_even_agreed_inputs
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      hRankFix huv hsu hsv hpar hu_med hv_upper h_agree hn4
    have hSwap' : InSswap (C.step P u v) := by
      have hdec := decision_step_at_median_pair_even_decreases
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hC huv hpar hu_med hv_upper h_agree hTie hn4 h_wrong
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hdec.1
    have hmaj : majorityAnswer (C.step P u v) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C u v)
    have h_correct : opinionToAnswer (C u).2 = majorityAnswer C :=
      opinionToAnswer_lower_median_eq_majorityAnswer_even hC hu_med hpar hTie
    have h_u_correct : (C.step P u v u).1.answer = majorityAnswer (C.step P u v) := by
      rw [hmaj]
      have hval := congrFun hC'_eq u
      rw [show (C.step P u v u) =
          (if u = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
            else if u = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
            else C u) by simpa [P, PEMProtocolCoupled, PEMProtocol] using hval]
      simp [h_correct]
    have h_u_med' : (C.step P u v u).1.rank.val + 1 = ceilHalf n := by
      have hval := congrFun hC'_eq u
      rw [show (C.step P u v u) =
          (if u = u then ({(C u).1 with answer := opinionToAnswer (C u).2}, (C u).2)
            else if u = v then ({(C v).1 with answer := opinionToAnswer (C u).2}, (C v).2)
            else C u) by simpa [P, PEMProtocolCoupled, PEMProtocol] using hval]
      simp [hceil, hu_med]
    have hGoal : InSswap (C.step P u v) ∧ MedianAnswerCorrect (C.step P u v) := by
      refine ⟨hSwap', ?_⟩
      intro η hη
      have hηu : η = u := by
        apply hSwap'.ranks_inj
        apply Fin.eq_of_val_eq
        have hηval : (C.step P u v η).1.rank.val = ceilHalf n - 1 := by omega
        have huval : (C.step P u v u).1.rank.val = ceilHalf n - 1 := by omega
        exact hηval.trans huval.symm
      subst η
      exact h_u_correct
    exact Probability.ProbHitWithin_one_lower_bound_of_step
      (P := P) hn2 C (fun D => InSswap D ∧ MedianAnswerCorrect D)
      htarget_not huv hGoal

/-- Odd-population median no-swap decision step as a one-step probability
lower bound for decreasing `wrongAnswerCount`. -/
theorem PEM_odd_median_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_rank_gt : (C v).1.rank < (C μ).1.rank)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  apply PEM_wrongAnswer_one_step_descent_prob_lower_bound_of_step
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hμv
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (decision_step_at_median_no_swap_odd_decreases
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer h_μ_wrong).2

/-- Odd-population median-wrong decision progress has `ceilHalf n - 1`
ordered good pairs: the wrong median can interact with any lower-rank agent.
This is the quantitative strengthening needed for the `Tswap -> Sdec`
window, not just a single deterministic witness. -/
theorem PEM_odd_median_wrong_lower_rank_decision_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n}
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  classical
  let lowerSet : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.rank.val < (C μ).1.rank.val
  let S : Finset (Fin n × Fin n) := lowerSet.image fun v => (μ, v)
  have hμ_rank : (C μ).1.rank.val = ceilHalf n - 1 := by omega
  have hceil_le_n : ceilHalf n ≤ n := by
    unfold ceilHalf
    omega
  have hcardLower : lowerSet.card = ceilHalf n - 1 := by
    have hk : (C μ).1.rank.val ≤ n := Nat.le_of_lt (C μ).1.rank.isLt
    have hcard := time_card_filter_rank_lt hC.toInSrank (k := (C μ).1.rank.val) hk
    simpa [lowerSet, hμ_rank] using hcard
  have hS_card : S.card = ceilHalf n - 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · exact hcardLower
    · intro a b h
      exact congrArg Prod.snd h
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [Probability.mem_offDiagonalPairs]
    rw [← hpv]
    intro hμv
    have hv_lt : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμ_eq_v : μ = v := by
      simpa using hμv
    subst v
    exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt
  have hstep : ∀ p ∈ S,
      wrongAnswerCount (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) p.1 p.2) <
        wrongAnswerCount C := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [← hpv]
    have hv_lt_val : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμv : μ ≠ v := by
      intro h
      subst v
      exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt_val
    have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
      omega
    have hv_no_max : (C v).1.rank.val + 1 ≠ n := by
      have hv_lt_ceil : (C v).1.rank.val + 1 < ceilHalf n := by omega
      omega
    have h_rank_gt : (C v).1.rank < (C μ).1.rank := by
      exact_mod_cast hv_lt_val
    simpa [PEMProtocolCoupled, PEMProtocol] using
      (decision_step_at_median_no_swap_odd_decreases
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer h_μ_wrong).2
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => wrongAnswerCount D < wrongAnswerCount C)
            (by exact Nat.lt_irrefl (wrongAnswerCount C))
            S hS_sub hstep

/-- Odd-population median-wrong decision reaches the local `Sdec` predicate
(`MedianAnswerCorrect`) in one step with the mass of all lower-rank partners,
while preserving `InSswap`. -/
theorem PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ : Fin n}
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : 1 ≤ (C μ).1.timer)
    (h_μ_wrong : (C μ).1.answer ≠ majorityAnswer C) :
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  classical
  let lowerSet : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.rank.val < (C μ).1.rank.val
  let S : Finset (Fin n × Fin n) := lowerSet.image fun v => (μ, v)
  have hμ_rank : (C μ).1.rank.val = ceilHalf n - 1 := by omega
  have hcardLower : lowerSet.card = ceilHalf n - 1 := by
    have hk : (C μ).1.rank.val ≤ n := Nat.le_of_lt (C μ).1.rank.isLt
    have hcard := time_card_filter_rank_lt hC.toInSrank (k := (C μ).1.rank.val) hk
    simpa [lowerSet, hμ_rank] using hcard
  have hS_card : S.card = ceilHalf n - 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · exact hcardLower
    · intro a b h
      exact congrArg Prod.snd h
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [Probability.mem_offDiagonalPairs]
    rw [← hpv]
    intro hμv
    have hv_lt : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμ_eq_v : μ = v := by
      simpa using hμv
    subst v
    exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt
  have hstep : ∀ p ∈ S,
      InSswap (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) p.1 p.2) ∧
        MedianAnswerCorrect
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) p.1 p.2) := by
    intro p hp
    dsimp [S] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [← hpv]
    have hv_lt_val : (C v).1.rank.val < (C μ).1.rank.val :=
      (Finset.mem_filter.mp hv).2
    have hμv : μ ≠ v := by
      intro h
      subst v
      exact (Nat.lt_irrefl (C μ).1.rank.val) hv_lt_val
    have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
      omega
    have hv_no_max : (C v).1.rank.val + 1 ≠ n := by
      have hv_lt_ceil : (C v).1.rank.val + 1 < ceilHalf n := by omega
      omega
    have h_rank_gt : (C v).1.rank < (C μ).1.rank := by
      exact_mod_cast hv_lt_val
    have hRankFix := rankDeltaOSSR_satisfies_fix
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
    have hSwap' : InSswap
        (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v) := by
      simpa [PEMProtocolCoupled, PEMProtocol] using
        (step_at_median_no_swap_odd_preserves_InSswap
          (n := n) (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hC hμv hpar hμ_med hv_no_med hv_no_max
          h_rank_gt h_timer)
    have hC'_eq :
        C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v =
          fun w =>
            if w = μ then
              ({(C μ).1 with answer := opinionToAnswer (C μ).2}, (C μ).2)
            else if w = v then
              ((C v).1, (C v).2)
            else C w := by
      simpa [PEMProtocolCoupled, PEMProtocol] using
        (step_at_median_no_swap_odd_v_not_max
          (n := n) (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hμv (hC.allSettled μ) (hC.allSettled v) hpar
          hμ_med hv_no_med hv_no_max h_rank_gt h_timer)
    have hmaj :
        majorityAnswer (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v) =
          majorityAnswer C := by
      simpa [PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
    have hμ_correct :
        (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v μ).1.answer =
          majorityAnswer (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v) := by
      rw [hmaj, hC'_eq]
      simp [opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar]
    have hμ_med' :
        (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v μ).1.rank.val + 1 =
          ceilHalf n := by
      rw [hC'_eq]
      simp [hμ_med]
    refine ⟨hSwap', ?_⟩
    intro η hη
    have hημ : η = μ := by
      apply hSwap'.ranks_inj
      apply Fin.eq_of_val_eq
      have hη_med' :
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v η).1.rank.val + 1 =
            ceilHalf n := by
        simpa using hη
      have hηval :
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v η).1.rank.val =
            ceilHalf n - 1 := by omega
      have hμval :
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) μ v μ).1.rank.val =
            ceilHalf n - 1 := by omega
      exact hηval.trans hμval.symm
    subst η
    exact hμ_correct
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => InSswap D ∧ MedianAnswerCorrect D)
            (by
              intro hGoal
              exact h_μ_wrong (hGoal.2 μ hμ_med))
            S hS_sub hstep

/-- Odd-population witness form of the median-wrong decision probability
bound.  The lower bound uses all lower-rank partners for the wrong median. -/
theorem PEM_odd_median_wrong_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : ¬ n % 2 = 0)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    (((ceilHalf n - 1 : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
  exact PEM_odd_median_wrong_lower_rank_decision_prob_lower_bound
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn2 hn0 hC hpar hμ_med (h_med_timer μ hμ_med) hμ_wrong

/-- Parity-unified median-wrong decision probability bound: if some median is
wrong and median timers are positive, one random interaction decreases
`wrongAnswerCount` with at least the mass of one ordered scheduler pair. -/
theorem PEM_median_wrong_decision_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := by
  by_cases hpar : n % 2 = 0
  · exact PEM_even_median_wrong_decision_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC hpar h_med_wrong
  · have hodd :=
      PEM_odd_median_wrong_decision_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hC hpar h_med_timer h_med_wrong
    have hcoef : (1 : ENNReal) ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) := by
      have hnat : 1 ≤ ceilHalf n - 1 := by
        unfold ceilHalf
        omega
      exact_mod_cast hnat
    calc
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹
          = (1 : ENNReal) *
              ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
      _ ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            exact mul_le_mul_left hcoef _
      _ ≤ Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D => wrongAnswerCount D < wrongAnswerCount C) 1 := hodd

/-- Marginal one-step version of
`PEM_median_wrong_decision_descent_prob_lower_bound`, for phase
composition.  The strict-descent target is false at the start state. -/
theorem PEM_median_wrong_decision_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => wrongAnswerCount D < wrongAnswerCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => wrongAnswerCount D < wrongAnswerCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact Nat.lt_irrefl _ h
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_median_wrong_decision_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer h_med_wrong)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Parity-unified `Tswap -> Sdec` one-step probability bound.  If some
median answer is wrong and the median timers are positive, then one scheduler
step reaches the local decision predicate with at least the mass of one
ordered pair, while preserving `InSswap`. -/
theorem PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := by
  by_cases hpar : n % 2 = 0
  · exact PEM_even_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC hpar h_med_wrong
  · obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_wrong
    have hodd :=
      PEM_odd_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hC hpar hμ_med (h_med_timer μ hμ_med) hμ_wrong
    have hcoef : (1 : ENNReal) ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) := by
      have hnat : 1 ≤ ceilHalf n - 1 := by
        unfold ceilHalf
        omega
      exact_mod_cast hnat
    calc
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹
          = (1 : ENNReal) *
              ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
      _ ≤ ((ceilHalf n - 1 : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            exact mul_le_mul_left hcoef _
      _ ≤ Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D => InSswap D ∧ MedianAnswerCorrect D) 1 := hodd

/-- Marginal one-step form of
`PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound`, for phase
composition.  The start state is not already in the target because a median
wrong witness contradicts `MedianAnswerCorrect`. -/
theorem PEM_median_wrong_to_MedianAnswerCorrect_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D
  have hGoal : ¬ Goal C := by
    rintro ⟨_, hDec⟩
    rcases h_med_wrong with ⟨μ, hμ, hwrong⟩
    exact hwrong (hDec μ hμ)
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer h_med_wrong)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Window amplification for the `Tswap -> Sdec` local phase.  Starting in
`InSswap` with live median timers and with a wrong median answer, within `t`
steps the chain either reaches the local decision predicate or leaves the
timer-live swap region with the usual geometric lower bound. -/
theorem PEM_Tswap_to_MedianAnswerCorrect_or_exit_prob_window
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    ∀ t : ℕ,
      1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^ t ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D =>
            (InSswap D ∧ MedianAnswerCorrect D) ∨
              ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) t := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  apply Probability.ProbHitWithin_ge_one_sub_pow_of_local_one_lower_bound
    (P := P) (hn := hn2) (C₀ := C)
    (Region := fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
    (Goal := fun D => InSswap D ∧ MedianAnswerCorrect D)
    (p := ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  · exact ⟨hC, h_med_timer⟩
  · intro hGoal
    exact h_not_dec hGoal.2
  · intro D hRegionD hGoalD
    have h_med_wrong :
        ∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
          (D μ).1.answer ≠ majorityAnswer D := by
      rw [← not_MedianAnswerCorrect_iff_exists_median_wrong]
      intro hDec
      exact hGoalD ⟨hRegionD.1, hDec⟩
    have hbase :
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 := by
      simpa [P] using
        (PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn2 hn0 hn4 hRegionD.1 hRegionD.2 h_med_wrong)
    have hTargetD :
        ¬ ((fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) D) := by
      intro hTarget
      rcases hTarget with hGoal | hExit
      · exact hGoalD hGoal
      · exact hExit hRegionD
    have hmono :
        Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 ≤
          Probability.ProbHitWithin P hn2 D
            (fun E =>
              (InSswap E ∧ MedianAnswerCorrect E) ∨
                ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) 1 :=
      Probability.ProbHitWithin_one_mono_goal
        (P := P) (hn := hn2) (C₀ := D)
        (Goal₁ := fun E => InSswap E ∧ MedianAnswerCorrect E)
        (Goal₂ := fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E))
        hGoalD hTargetD (fun E h => Or.inl h)
    exact le_trans hbase hmono

/-- Table-2 Phase-3 live-region wrapper.

This is the provable form of the `Sswap -> Sdec` window from the existing
one-step median-wrong lemma: while the median timers are live, the process
geometrically reaches `InSswap ∧ MedianAnswerCorrect`; otherwise the window
has exited the live swap region, which must be handled by a surrounding
phase-composition argument. -/
theorem PEM_phase3_live_or_exit_window
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^
        (4 * n * n) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          (InSswap D ∧ MedianAnswerCorrect D) ∨
            ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (4 * n * n) := by
  simpa using
    (PEM_Tswap_to_MedianAnswerCorrect_or_exit_prob_window
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC h_med_timer h_not_dec (4 * n * n))

/-- Same Phase-3 decision-or-exit window with the paper Lemma-9 live-timer
entry condition.  The remaining Lemma-9 work is to separate the decision
success mass from the early timer-expiration exit mass. -/
theorem PEM_phase3_timer28_live_or_exit_window
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 28 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^
        (4 * n * n) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          (InSswap D ∧ MedianAnswerCorrect D) ∨
            ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (4 * n * n) := by
  exact PEM_phase3_live_or_exit_window
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn2 hn0 hn4 hC
    (MedianTimerAtLeast.mono (n := n) (a := 1) (b := 28) (by norm_num)
      h_med_timer)
    h_not_dec

private theorem real_one_sub_one_div_pow_self_le_half {m : ℕ} (hm : 2 ≤ m) :
    (1 - (1 / (m : ℝ))) ^ m ≤ (1 / 2 : ℝ) := by
  have hm_pos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hm_gt_one : (1 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  set q : ℝ := 1 - (1 / (m : ℝ))
  have hq_pos : 0 < q := by
    dsimp [q]
    field_simp [ne_of_gt hm_pos]
    nlinarith
  have hbase : q⁻¹ = 1 + 1 / ((m : ℝ) - 1) := by
    dsimp [q]
    field_simp [ne_of_gt hm_pos, ne_of_gt hm1_pos]
    ring
  have hbern :
      1 + (m : ℝ) * (1 / ((m : ℝ) - 1)) ≤
        (1 + 1 / ((m : ℝ) - 1)) ^ m := by
    exact one_add_mul_le_pow (a := 1 / ((m : ℝ) - 1)) (n := m)
      (by
        have hpos : 0 < 1 / ((m : ℝ) - 1) := one_div_pos.mpr hm1_pos
        linarith)
  have h2_le_linear :
      (2 : ℝ) ≤ 1 + (m : ℝ) * (1 / ((m : ℝ) - 1)) := by
    have hfrac : (1 : ℝ) ≤ (m : ℝ) / ((m : ℝ) - 1) := by
      rw [one_le_div hm1_pos]
      linarith
    rw [mul_one_div]
    linarith
  have h2_inv : (2 : ℝ) ≤ (q ^ m)⁻¹ := by
    rw [← inv_pow, hbase]
    exact h2_le_linear.trans hbern
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 2) h2_inv
  simpa [one_div] using h

private theorem ennreal_one_sub_inv_nat_pow_self_le_half {m : ℕ} (hm : 2 ≤ m) :
    (1 - ((m : ENNReal)⁻¹)) ^ m ≤ (2 : ENNReal)⁻¹ := by
  rw [← ENNReal.toReal_le_toReal]
  · rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_sub_of_le]
    · simpa [one_div] using real_one_sub_one_div_pow_self_le_half hm
    · exact ENNReal.inv_le_one.mpr
        (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hm))
    · exact ENNReal.one_ne_top
  · simp
  · simp

private theorem ennreal_inv_two_pow_four_le_three_inv_eight :
    ((2 : ENNReal)⁻¹) ^ 4 ≤ (3 : ENNReal) * (8 : ENNReal)⁻¹ := by
  have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have h8 : ((8 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hleft : (((2 : ENNReal)⁻¹) ^ 4) ≠ ⊤ := by simp [h2]
  have hright : ((3 : ENNReal) * (8 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top 3) h8
  rw [← ENNReal.toReal_le_toReal hleft hright]
  simp [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_mul]
  norm_num

private theorem ennreal_half_add_eighth_add_three_eighth_le_one :
    ((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹) +
      (3 : ENNReal) * (8 : ENNReal)⁻¹ ≤ 1 := by
  have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have h8 : ((8 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hsum : ((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h2, h8⟩
  have hmul : ((3 : ENNReal) * (8 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top 3) h8
  have hleft :
      (((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹) +
        (3 : ENNReal) * (8 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hsum, hmul⟩
  rw [← ENNReal.toReal_le_toReal hleft ENNReal.one_ne_top]
  rw [ENNReal.toReal_add hsum hmul]
  rw [ENNReal.toReal_add h2 h8]
  simp [ENNReal.toReal_inv, ENNReal.toReal_mul]
  norm_num

/-- The geometric part of the Phase-3 decision-or-exit window is already
larger than `1/2 + 1/8` for `n ≥ 4`. -/
theorem PEM_phase3_geometric_live_or_exit_lower_bound
    {n : ℕ} (hn4 : 4 ≤ n) :
    (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹ ≤
      1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^
        (4 * n * n) := by
  let m := n * (n - 1)
  let q : ENNReal := 1 - ((m : ENNReal)⁻¹)
  have hm : 2 ≤ m := by
    dsimp [m]
    calc
      2 ≤ 4 := by norm_num
      _ ≤ n * (n - 1) := by
        exact Nat.mul_le_mul hn4 (by omega : 1 ≤ n - 1)
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    exact tsub_le_self
  have hqm : q ^ m ≤ (2 : ENNReal)⁻¹ := by
    simpa [q, m] using ennreal_one_sub_inv_nat_pow_self_le_half hm
  have hq4m : q ^ (4 * m) ≤ ((2 : ENNReal)⁻¹) ^ 4 := by
    rw [show 4 * m = m * 4 by ring, pow_mul]
    exact ENNReal.pow_le_pow_left hqm
  have htime : 4 * m ≤ 4 * n * n := by
    dsimp [m]
    rw [show 4 * (n * (n - 1)) = 4 * n * (n - 1) by ring]
    exact Nat.mul_le_mul_left (4 * n) (Nat.sub_le n 1)
  have hfail :
      q ^ (4 * n * n) ≤ (3 : ENNReal) * (8 : ENNReal)⁻¹ := by
    exact (pow_le_pow_of_le_one (zero_le) hq_le_one htime).trans
      (hq4m.trans ennreal_inv_two_pow_four_le_three_inv_eight)
  have hsum :
      ((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹) + q ^ (4 * n * n) ≤ 1 := by
    exact (add_le_add_right hfail ((2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹)).trans
      ennreal_half_add_eighth_add_three_eighth_le_one
  have hthree_ne_top : ((3 : ENNReal) * (8 : ENNReal)⁻¹) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top 3
    · rw [ENNReal.inv_ne_top]
      norm_num
  have hqpow_ne_top : q ^ (4 * n * n) ≠ ⊤ :=
    ne_top_of_le_ne_top hthree_ne_top hfail
  simpa [q, m] using ENNReal.le_sub_of_add_le_right hqpow_ne_top hsum

/-- Phase-3 subtraction wrapper.

The existing local-good-pair argument gives a lower bound for reaching
`decision ∨ exit-live-region`.  If the early live-region exit probability is
at most `1/2`, and the geometric lower bound is at least `1/2 + 1/8`, the
finite-prefix union bound leaves at least `1/8` probability for hitting the
live decision predicate. -/
theorem PEM_phase3_live_decision_hit_lower_bound_of_exit_le_half
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 28 C)
    (h_not_dec : ¬ MedianAnswerCorrect C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (4 * n * n) ≤ (2 : ENNReal)⁻¹) :
    (8 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D)
        (4 * n * n) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let A : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  let B : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  have hGoalEq :
      (fun D : Config (AgentState n) Opinion n =>
          (InSswap D ∧ MedianAnswerCorrect D) ∨
            ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) =
        (fun D => A D ∨ B D) := by
    funext D
    apply propext
    constructor
    · intro h
      rcases h with hdec | hexit
      · by_cases htimer : MedianTimerAtLeast 1 D
        · exact Or.inl ⟨hdec.1, hdec.2, htimer⟩
        · exact Or.inr (fun hLive => htimer hLive.2)
      · exact Or.inr hexit
    · intro h
      rcases h with hdec | hexit
      · exact Or.inl ⟨hdec.1, hdec.2.1⟩
      · exact Or.inr hexit
  have hor :
      (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin P hn2 C (fun D => A D ∨ B D) (4 * n * n) := by
    calc
      (2 : ENNReal)⁻¹ + (8 : ENNReal)⁻¹
          ≤ 1 - (1 - ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ^
              (4 * n * n) :=
          PEM_phase3_geometric_live_or_exit_lower_bound hn4
      _ ≤ Probability.ProbHitWithin P hn2 C
            (fun D =>
              (InSswap D ∧ MedianAnswerCorrect D) ∨
                ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
            (4 * n * n) :=
          PEM_phase3_timer28_live_or_exit_window
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn2 hn0 hn4 hC h_med_timer h_not_dec
      _ = Probability.ProbHitWithin P hn2 C (fun D => A D ∨ B D)
            (4 * n * n) := by rw [hGoalEq]
  exact
    Probability.ProbHitWithin_left_ge_inv8_of_or_ge_half_add_inv8_and_right_le_half
      P hn2 C A B (4 * n * n) hor (by simpa [P, B] using hExit)

/-- Phase-3 subtraction wrapper with an enlarged target predicate. -/
theorem PEM_phase3_live_decision_hit_lower_bound_of_exit_le_half_mono
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (G : Config (AgentState n) Opinion n → Prop)
    (hG : ∀ D : Config (AgentState n) Opinion n,
      InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D → G D)
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 28 C)
    (h_not_dec : ¬ MedianAnswerCorrect C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (4 * n * n) ≤ (2 : ENNReal)⁻¹) :
    (8 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C G
        (4 * n * n) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let A : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  exact
    (PEM_phase3_live_decision_hit_lower_bound_of_exit_le_half
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC h_med_timer h_not_dec hExit).trans
      (Probability.ProbHitWithin_mono_goal P hn2 C A G hG (4 * n * n))

/-- Standalone Phase-3 endpoint theorem.

The remaining probabilistic work for Lemma 9 is exactly the joint-event
hypothesis: with probability at least `1/8`, the finite prefix has hit the
decision predicate and the endpoint of the whole `4*n*n` window still lies in
the timer-live `Sdec` phase predicate.  This wrapper converts that path-level
joint event into the exact-time `probReached` hypothesis required by the
Table-2 phase composition. -/
theorem PEM_decision_phase_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (_hC : InSswap C)
    (_h_med_timer : MedianTimerAtLeast 28 C)
    (_h_timer_upper : MedianTimerAtMost (7 * (Rmax + 4)) C)
    (_h_not_consensus : ¬ IsConsensusConfig C)
    (hJoint :
      (8 : ENNReal)⁻¹ ≤
        Probability.probHitAndIn
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C
          (fun D => InSswap D ∧ MedianAnswerCorrect D)
          (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n)) :
    (8 : ENNReal)⁻¹ ≤
      Probability.probReached
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C
        (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
  exact Probability.probReached_ge_of_probHitAndIn
    (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
    (by omega : 2 ≤ n) C
    (fun D => InSswap D ∧ MedianAnswerCorrect D)
    (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n)
    ((8 : ENNReal)⁻¹) hJoint

/-- Expected sequential-time form of
`PEM_Tswap_to_MedianAnswerCorrect_or_exit_prob_window`. -/
theorem PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (h_not_dec : ¬ MedianAnswerCorrect C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
    (P := P) (hn := hn2) (C₀ := C)
    (Region := fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
    (Goal := fun D => InSswap D ∧ MedianAnswerCorrect D)
    (p := ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  · exact ⟨hC, h_med_timer⟩
  · intro hGoal
    exact h_not_dec hGoal.2
  · intro D hRegionD hGoalD
    have h_med_wrong :
        ∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
          (D μ).1.answer ≠ majorityAnswer D := by
      rw [← not_MedianAnswerCorrect_iff_exists_median_wrong]
      intro hDec
      exact hGoalD ⟨hRegionD.1, hDec⟩
    have hbase :
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 := by
      simpa [P] using
        (PEM_median_wrong_to_MedianAnswerCorrect_prob_lower_bound
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn2 hn0 hn4 hRegionD.1 hRegionD.2 h_med_wrong)
    have hTargetD :
        ¬ ((fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) D) := by
      intro hTarget
      rcases hTarget with hGoal | hExit
      · exact hGoalD hGoal
      · exact hExit hRegionD
    have hmono :
        Probability.ProbHitWithin P hn2 D
            (fun E => InSswap E ∧ MedianAnswerCorrect E) 1 ≤
          Probability.ProbHitWithin P hn2 D
            (fun E =>
              (InSswap E ∧ MedianAnswerCorrect E) ∨
                ¬ (InSswap E ∧ MedianTimerAtLeast 1 E)) 1 :=
      Probability.ProbHitWithin_one_mono_goal
        (P := P) (hn := hn2) (C₀ := D)
        (Goal₁ := fun E => InSswap E ∧ MedianAnswerCorrect E)
        (Goal₂ := fun E =>
          (InSswap E ∧ MedianAnswerCorrect E) ∨
            ¬ (InSswap E ∧ MedianTimerAtLeast 1 E))
        hGoalD hTargetD (fun E h => Or.inl h)
    exact le_trans hbase hmono

/-- Version of `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le` that
also covers the already-decided case. -/
theorem PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le_live
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)) ≤
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
  classical
  by_cases h_dec : MedianAnswerCorrect C
  · rw [Probability.expectedHittingTime_eq_zero_of_goal
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
      (Or.inl ⟨hC, h_dec⟩)]
    exact zero_le
  · exact PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC h_med_timer h_dec

private theorem ennreal_inv_two_eq_inv_four_add_inv_four :
    ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) + ((4 : ENNReal)⁻¹) := by
  have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have h4 : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  have hsum : ((4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h4, h4⟩
  rw [← ENNReal.toReal_eq_toReal_iff' h2 hsum]
  rw [ENNReal.toReal_add h4 h4]
  simp [ENNReal.toReal_inv]
  norm_num

private theorem ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
    {n : ℕ} (P : Protocol (AgentState n) Opinion Output) (hn : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (A B : Config (AgentState n) Opinion n → Prop)
    [DecidablePred A] [DecidablePred B] (t : ℕ)
    (hor : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t)
    (hB : Probability.ProbHitWithin P hn C₀ B t ≤ (4 : ENNReal)⁻¹) :
    ((4 : ENNReal)⁻¹) ≤ Probability.ProbHitWithin P hn C₀ A t := by
  let x := Probability.ProbHitWithin P hn C₀ A t
  let y := Probability.ProbHitWithin P hn C₀ B t
  have hOr :
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t ≤ x + y := by
    simpa [x, y] using Probability.ProbHitWithin_union_le P hn C₀ A B t
  have hhalf_le : ((2 : ENNReal)⁻¹) ≤ x + (4 : ENNReal)⁻¹ := by
    calc
      ((2 : ENNReal)⁻¹)
          ≤ Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t := hor
      _ ≤ x + y := hOr
      _ ≤ x + (4 : ENNReal)⁻¹ := by
        exact add_le_add_right (show y ≤ (4 : ENNReal)⁻¹ from hB) x
  have hquarter_ne_top : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  rw [ennreal_inv_two_eq_inv_four_add_inv_four] at hhalf_le
  rw [add_comm x ((4 : ENNReal)⁻¹)] at hhalf_le
  exact (ENNReal.add_le_add_iff_left hquarter_ne_top).mp hhalf_le

/-- Decision-only Phase-3 lower bound from the expectation-to-`decision ∨ exit`
lemma plus a finite-window union-bound subtraction.

This is intentionally conditional on an exit upper bound; the remaining
probabilistic work is to control the probability of leaving the live swap
region before the decision hit. -/
theorem PEM_phase3_decision_hit_lower_bound_of_exit_le_quarter_from_expected
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D)
        (2 * n * (n - 1)) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let A : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D
  let B : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  let Goal : Config (AgentState n) Opinion n → Prop := fun D => A D ∨ B D
  have hE₀ :
      Probability.expectedHittingTime P hn2 C Goal ≤
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
    simpa [P, Goal, A, B] using
      (PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le_live
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer)
  have hE :
      Probability.expectedHittingTime P hn2 C Goal ≤
        ((n * (n - 1) : ℕ) : ENNReal) := by
    simpa using hE₀
  have hWindow : 2 * (n * (n - 1)) ≤ 2 * n * (n - 1) + 1 := by
    nlinarith
  have hor :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Goal (2 * n * (n - 1)) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C Goal hE hWindow
  have hA :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C A (2 * n * (n - 1)) :=
    ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C A B (2 * n * (n - 1))
      (by simpa [Goal, A, B] using hor)
      (by simpa [P, B] using hExit)
  simpa [P, A]

/-- Live Phase-3 decision lower bound from the expectation-to-`decision ∨ exit`
lemma plus finite-window union-bound subtraction.

This is the propagation-ready version: the left target retains the
`MedianTimerAtLeast 1` hypothesis.  Any decision hit without the timer-live
condition is charged to the exit event, so the same union subtraction applies. -/
theorem PEM_phase3_live_decision_hit_lower_bound_of_exit_le_quarter_from_expected
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹) :
    (4 : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D)
        (2 * n * (n - 1)) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let A : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  let B : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨ B D
  have hGoalEq :
      Goal = (fun D => A D ∨ B D) := by
    funext D
    apply propext
    constructor
    · intro h
      rcases h with hdec | hexit
      · by_cases htimer : MedianTimerAtLeast 1 D
        · exact Or.inl ⟨hdec.1, hdec.2, htimer⟩
        · exact Or.inr (fun hLive => htimer hLive.2)
      · exact Or.inr hexit
    · intro h
      rcases h with hdec | hexit
      · exact Or.inl ⟨hdec.1, hdec.2.1⟩
      · exact Or.inr hexit
  have hE₀ :
      Probability.expectedHittingTime P hn2 C Goal ≤
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
    simpa [P, Goal, B] using
      (PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le_live
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer)
  have hE :
      Probability.expectedHittingTime P hn2 C Goal ≤
        ((n * (n - 1) : ℕ) : ENNReal) := by
    simpa using hE₀
  have hWindow : 2 * (n * (n - 1)) ≤ 2 * n * (n - 1) + 1 := by
    nlinarith
  have hor :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Goal (2 * n * (n - 1)) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C Goal hE hWindow
  have hA :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C A (2 * n * (n - 1)) :=
    ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C A B (2 * n * (n - 1))
      (by simpa [hGoalEq] using hor)
      (by simpa [P, B] using hExit)
  simpa [P, A]

/-- Conditional Phase-C composition.

Once the exit probability from the live swap region is bounded by `1/4`, the
decision lemma above gives a `1/4` chance to hit a live correct median.  Any
uniform propagation window lower bound from such live decision states then
composes by strong Markov. -/
theorem PEM_consensus_ProbHitWithin_from_decision_exit_and_propagation
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (IsConsensusConfig :
      Config (AgentState n) Opinion n → Prop)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (h_med_timer : MedianTimerAtLeast 1 C)
    (hExit :
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * n * (n - 1)) ≤ (4 : ENNReal)⁻¹)
    (hPropagation :
      ∀ D : Config (AgentState n) Opinion n,
        InSswap D →
        MedianAnswerCorrect D →
        MedianTimerAtLeast 1 D →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 D
              IsConsensusConfig (20 * Rmax * n * n)) :
    ((4 : ENNReal)⁻¹) * ((1280 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        IsConsensusConfig ((2 * n * (n - 1)) + (20 * Rmax * n * n)) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let DecLive : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianAnswerCorrect D ∧ MedianTimerAtLeast 1 D
  have hDecision :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C DecLive (2 * n * (n - 1)) := by
    simpa [P, DecLive] using
      (PEM_phase3_live_decision_hit_lower_bound_of_exit_le_quarter_from_expected
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_med_timer hExit)
  have hProp : ∀ D : Config (AgentState n) Opinion n, DecLive D →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 D IsConsensusConfig
          (20 * Rmax * n * n) := by
    intro D hD
    exact hPropagation D hD.1 hD.2.1 hD.2.2
  simpa [P, DecLive] using
    (Probability.ProbHitWithin_add_ge_mul P hn2 C
      DecLive IsConsensusConfig
      (2 * n * (n - 1)) (20 * Rmax * n * n)
      ((4 : ENNReal)⁻¹) ((1280 : ENNReal)⁻¹)
      hDecision hProp)

/-- Reservoir-aware median-wrong probability bound: under `ResAns`, a
median-wrong decision step gives a one-step scheduler lower bound for
returning to `InSswap ∧ ResAns` with strictly smaller `phiCount`. -/
theorem PEM_median_wrong_resAns_phi_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          InSswap D ∧
          ResAns (majorityAnswer D) D ∧
          phiCount D < phiCount C) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  obtain ⟨p, hSwap', hRes', _hTimer', hWrongDec⟩ :=
    median_wrong_step_resAns_decrease_tieaware
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
      hn4 hC hRes h_med_timer h_med_wrong
  have hp_ne : p.1 ≠ p.2 := by
    intro hp_eq
    have hstep_eq :
        C.step P p.1 p.2 = C := by
      rcases p with ⟨u, v⟩
      dsimp at hp_eq
      subst v
      simp [Config.step]
    have hWrongDecP :
        wrongAnswerCount (C.step P p.1 p.2) < wrongAnswerCount C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hWrongDec
    rw [hstep_eq] at hWrongDecP
    exact (Nat.lt_irrefl (wrongAnswerCount C)) hWrongDecP
  have hPhiDec :
      phiCount (C.step P p.1 p.2) < phiCount C := by
    have hResP :
        ResAns (majorityAnswer (C.step P p.1 p.2)) (C.step P p.1 p.2) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hRes'
    have hWrongDecP :
        wrongAnswerCount (C.step P p.1 p.2) < wrongAnswerCount C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hWrongDec
    rw [phiCount_eq_wrongAnswerCount_of_resAns hResP,
      phiCount_eq_wrongAnswerCount_of_resAns hRes]
    exact hWrongDecP
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D =>
      InSswap D ∧
      ResAns (majorityAnswer D) D ∧
      phiCount D < phiCount C)
  · intro hGoal
    exact (Nat.lt_irrefl (phiCount C)) hGoal.2.2
  · exact hp_ne
  · have hSwapP : InSswap (C.step P p.1 p.2) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hSwap'
    have hResP :
        ResAns (majorityAnswer (C.step P p.1 p.2)) (C.step P p.1 p.2) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hRes'
    exact ⟨hSwapP, hResP, hPhiDec⟩

/-- Marginal one-step form of
`PEM_median_wrong_resAns_phi_descent_prob_lower_bound`. -/
theorem PEM_median_wrong_resAns_phi_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    (hRes : ResAns (majorityAnswer C) C)
    (h_med_timer : ∀ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer)
    (h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
      (C μ).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          InSswap D ∧
          ResAns (majorityAnswer D) D ∧
          phiCount D < phiCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      InSswap D ∧
      ResAns (majorityAnswer D) D ∧
      phiCount D < phiCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact (Nat.lt_irrefl (phiCount C)) h.2.2
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_median_wrong_resAns_phi_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC hRes h_med_timer h_med_wrong)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-! ### Timer-drain one-step probability witnesses -/

/-- Odd-population median/max no-swap timer descent as a one-step scheduler
probability lower bound. -/
theorem PEM_odd_median_max_timer_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hstep :=
    step_at_median_max_no_swap_odd_explicit
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC hn2 hμv hμ_med hv_max hpar h_no_swap h_timer
  have hSwap' : InSswap (C.step P μ v) := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (step_at_median_max_no_swap_odd_explicit_preserves_InSswap
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hn2 hμv hμ_med hv_max hpar h_no_swap h_timer)
  have hTimer' : (C.step P μ v μ).1.timer + 1 = (C μ).1.timer := by
    have htimer_eq : (C.step P μ v μ).1.timer = (C μ).1.timer - 1 := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hstep.1
    rw [htimer_eq]
    omega
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer)
  · intro hGoal
    omega
  · exact hμv
  · exact ⟨hSwap', hTimer'⟩

/-- Even-population lower-median/max no-reset timer descent as a one-step
scheduler probability lower bound. -/
theorem PEM_even_lower_median_max_timer_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hstep :=
    step_at_even_lower_max_timer_ge_two
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hC hn4 hμv hpar hμ_lower hv_max h_no_swap h_timer
  have hSwap' : InSswap (C.step P μ v) := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (step_at_even_lower_max_timer_ge_two_preserves_InSswap
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hn4 hμv hpar hμ_lower hv_max h_no_swap h_timer)
  have hTimer' : (C.step P μ v μ).1.timer + 1 = (C μ).1.timer := by
    have htimer_eq : (C.step P μ v μ).1.timer = (C μ).1.timer - 1 := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hstep.1
    rw [htimer_eq]
    omega
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer)
  · intro hGoal
    omega
  · exact hμv
  · exact ⟨hSwap', hTimer'⟩

/-- Parity-unified median/max no-swap timer descent lower bound.  This is
the one-step probability interface used by the timer-drain part of the
`Sdec -> Stim` window. -/
theorem PEM_median_max_timer_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer) 1 := by
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
    exact PEM_even_lower_median_max_timer_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hC hμv hpar (by simpa [hceil] using hμ_med)
      hv_max h_no_swap h_timer
  · exact PEM_odd_median_max_timer_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hC hμv hpar hμ_med hv_max h_no_swap h_timer

/-- Marginal one-step form of
`PEM_median_max_timer_descent_prob_lower_bound`. -/
theorem PEM_median_max_timer_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ (D μ).1.timer + 1 = (C μ).1.timer
  have hGoal : ¬ Goal C := by
    intro h
    omega
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_median_max_timer_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC hμv hμ_med hv_max h_no_swap h_timer)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Odd-population median/max timer-one no-reset step exits the live-timer
swap region with the mass of one ordered scheduler pair. -/
theorem PEM_odd_median_max_timer_one_no_reset_exit_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_live : MedianTimerAtLeast 1 C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hstep :
      InSswap (C.step P μ v) ∧
        (C.step P μ v μ).1.timer = 0 ∧
        (C.step P μ v μ).1.answer = opinionToAnswer (C μ).2 ∧
        (C.step P μ v μ).1.rank.val + 1 = ceilHalf n ∧
        (C.step P μ v v).1.rank.val + 1 = n ∧
        (∀ w : Fin n, w ≠ μ → w ≠ v → C.step P μ v w = C w) ∧
        (∀ w : Fin n, (C.step P μ v w).2 = (C w).2) := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (step_at_median_max_timer_one_no_reset_explicit
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hn4 hμv hμ_med hv_max hpar h_no_swap h_timer h_post_same)
  have hGoal :
      InSswap (C.step P μ v) ∧
        ¬ MedianTimerAtLeast 1 (C.step P μ v) := by
    refine ⟨hstep.1, ?_⟩
    intro hLive'
    have htimer_ge : 1 ≤ (C.step P μ v μ).1.timer :=
      hLive' μ hstep.2.2.2.1
    omega
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D)
  · intro hTarget
    exact hTarget.2 h_live
  · exact hμv
  · exact hGoal

/-- Marginal one-step form of
`PEM_odd_median_max_timer_one_no_reset_exit_prob_lower_bound`. -/
theorem PEM_odd_median_max_timer_one_no_reset_exit_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_live : MedianTimerAtLeast 1 C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D
  have hGoal : ¬ Goal C := by
    intro h
    exact h.2 h_live
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_odd_median_max_timer_one_no_reset_exit_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_live hμv hpar hμ_med hv_max h_no_swap
        h_timer h_post_same)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Even-population lower-median/max timer-one no-reset step exits the
live-timer swap region with the mass of one ordered scheduler pair. -/
theorem PEM_even_lower_median_max_timer_one_no_reset_exit_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_live : MedianTimerAtLeast 1 C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hstep :
      InSswap (C.step P μ v) ∧
        (C.step P μ v μ).1.timer = 0 ∧
        (C.step P μ v μ).1.answer = (C μ).1.answer ∧
        (C.step P μ v μ).1.rank.val + 1 = n / 2 := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (no_reset_even_lower_max_timer_one_step_InSswap
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same)
  have hceil : ceilHalf n = n / 2 := ceilHalf_eq_half_of_even hpar
  have hGoal :
      InSswap (C.step P μ v) ∧
        ¬ MedianTimerAtLeast 1 (C.step P μ v) := by
    refine ⟨hstep.1, ?_⟩
    intro hLive'
    have hμ_med' : (C.step P μ v μ).1.rank.val + 1 = ceilHalf n := by
      simpa [hceil] using hstep.2.2.2
    have htimer_ge : 1 ≤ (C.step P μ v μ).1.timer :=
      hLive' μ hμ_med'
    omega
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C
    (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D)
  · intro hTarget
    exact hTarget.2 h_live
  · exact hμv
  · exact hGoal

/-- Marginal one-step form of
`PEM_even_lower_median_max_timer_one_no_reset_exit_prob_lower_bound`. -/
theorem PEM_even_lower_median_max_timer_one_no_reset_exit_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (h_live : MedianTimerAtLeast 1 C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : (C μ).1.timer = 1)
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ ¬ MedianTimerAtLeast 1 D
  have hGoal : ¬ Goal C := by
    intro h
    exact h.2 h_live
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_even_lower_median_max_timer_one_no_reset_exit_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hn4 hC h_live hμv hpar hμ_lower hv_max h_no_swap
        h_timer h_post_same)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Odd-population timer-one median/max reset-firing step creates a
`CorrectResetSeed` with the mass of one ordered scheduler pair. -/
theorem PEM_odd_median_max_timer_one_reset_seed_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : (C μ).1.timer = 1)
    (h_max_wrong : (C v).1.answer ≠ opinionToAnswer (C μ).2) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        CorrectResetSeed 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    rintro ⟨_, hB, _⟩
    rw [hμ_input_A] at hB
    cases hB
  have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
    intro h
    exact h_max_wrong h.symm
  have hsnap :
      (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
        (C' μ).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        (C := C) hC.toInSrank hn4 hμv hμ_med hv_max h_timer
        h_no_swap hpar h_post_diff)
  have hstep :
      (C' μ).1.role = .Resetting ∧
      (C' v).1.role = .Resetting ∧
      (C' μ).1.answer = opinionToAnswer (C μ).2 ∧
      (C' v).1.answer = opinionToAnswer (C μ).2 ∧
      (C' μ).1.resetcount = Rmax ∧
      (C' v).1.resetcount = Rmax ∧
      (∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w) ∧
      (∀ w : Fin n, (C' w).2 = (C w).2) := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (step_at_median_max_timer_one_reset_fires_odd
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (rankDeltaOSSR_satisfies_fix
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
        hC hn2 hμv hμ_med hv_max hpar hμ_input_A h_timer h_max_wrong)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
  have hμ_majority : opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hC hμ_med hpar
  have hN_bound : nonResettingCount C' < Rmax := by
    have hcard_le : nonResettingCount C' ≤ n - 1 := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hS
      have hsub : S ⊆ Finset.univ.erase μ := by
        intro x hx
        have hx_ne : x ≠ μ := by
          intro hxμ
          subst x
          have hx_not : (C' μ).1.role ≠ .Resetting := by
            rw [hS] at hx
            exact (Finset.mem_filter.mp hx).2
          rw [hstep.1] at hx_not
          exact hx_not rfl
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase μ).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
        simp
      unfold nonResettingCount
      rw [← hS]
      omega
    have hn_pos : 0 < n := by omega
    have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn_pos hRmax
    omega
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  have hSeed : CorrectResetSeed C' := by
    refine ⟨⟨μ, hsnap.1, ?_, hsnap.2.2.1, ?_⟩, ?_⟩
    · rw [hsnap.2.1]
      exact hN_bound
    · rw [hstep.2.2.1, hmaj, hμ_majority]
    · intro w hw
      by_cases hwμ : w = μ
      · subst w
        refine ⟨?_, ?_⟩
        · rw [hsnap.2.1]
          exact hRmax_pos
        · rw [hstep.2.2.1, hmaj, hμ_majority]
      · by_cases hwv : w = v
        · subst w
          refine ⟨?_, ?_⟩
          · rw [hsnap.2.2.2.2.1]
            exact hRmax_pos
          · rw [hstep.2.2.2.1, hmaj, hμ_majority]
        · have hOldSettled : (C' w).1.role = .Settled := by
            rw [hstep.2.2.2.2.2.2.1 w hwμ hwv]
            exact hC.allSettled w
          rw [hOldSettled] at hw
          cases hw
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C CorrectResetSeed
  · intro hSeedC
    obtain ⟨⟨r, hr, _⟩, _⟩ := hSeedC
    rw [hC.allSettled r] at hr
    cases hr
  · exact hμv
  · simpa [C'] using hSeed

/-- Even-population lower-median/max timer-one reset-firing step creates a
`CorrectResetSeed` with the mass of one ordered scheduler pair. -/
theorem PEM_even_lower_median_max_timer_one_reset_seed_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        CorrectResetSeed 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hC.swap_condition_false μ v
  have h_post_diff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hsnap :
      (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
        (C' μ).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
        h_no_swap h_post_diff)
  have htr :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v) =
        ({ (C μ).1 with
            answer := (C μ).1.answer,
            timer := 0,
            role := .Resetting,
            leader := .L,
            resetcount := Rmax },
         { (C v).1 with
            answer := (C μ).1.answer,
            role := .Resetting,
            leader := .L,
            resetcount := Rmax }) := by
    simpa using
      (propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer
        h_no_swap h_post_diff)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P, PEMProtocolCoupled, PEMProtocol] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C μ v)
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_ans' : (C' μ).1.answer = majorityAnswer C' := by
    rw [hmaj]
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.answer hfst]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v)).1.answer = majorityAnswer C
    rw [htr, hμ_correct]
  have hv_ans' : (C' v).1.answer = majorityAnswer C' := by
    rw [hmaj]
    dsimp [C', P, PEMProtocolCoupled, PEMProtocol]
    rw [congrArg AgentState.answer hsnd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (C μ, C v)).2.answer = majorityAnswer C
    rw [htr, hμ_correct]
  have hN_bound : nonResettingCount C' < Rmax := by
    have hcard_le : nonResettingCount C' ≤ n - 1 := by
      set S := Finset.univ.filter
        (fun w : Fin n => (C' w).1.role ≠ .Resetting) with hS
      have hsub : S ⊆ Finset.univ.erase μ := by
        intro x hx
        have hx_ne : x ≠ μ := by
          intro hxμ
          subst x
          have hx_not : (C' μ).1.role ≠ .Resetting := by
            rw [hS] at hx
            exact (Finset.mem_filter.mp hx).2
          rw [hsnap.1] at hx_not
          exact hx_not rfl
        exact Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_univ x⟩
      have hle := Finset.card_le_card hsub
      have herase : (Finset.univ.erase μ).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
        simp
      unfold nonResettingCount
      rw [← hS]
      omega
    have hn_pos : 0 < n := by omega
    have hRmax_pos : 0 < Rmax := Nat.lt_of_lt_of_le hn_pos hRmax
    omega
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  have hSeed : CorrectResetSeed C' := by
    refine ⟨⟨μ, hsnap.1, ?_, hsnap.2.2.1, hμ_ans'⟩, ?_⟩
    · rw [hsnap.2.1]
      exact hN_bound
    · intro w hw
      by_cases hwμ : w = μ
      · subst w
        refine ⟨?_, hμ_ans'⟩
        · rw [hsnap.2.1]
          exact hRmax_pos
      · by_cases hwv : w = v
        · subst w
          refine ⟨?_, hv_ans'⟩
          · rw [hsnap.2.2.2.2.1]
            exact hRmax_pos
        · have hOldSettled : (C' w).1.role = .Settled := by
            dsimp [C', P]
            simp [Config.step, hμv, hwμ, hwv, hC.allSettled w]
          rw [hOldSettled] at hw
          cases hw
  apply Probability.ProbHitWithin_one_lower_bound_of_step
    (P := P) hn2 C CorrectResetSeed
  · intro hSeedC
    obtain ⟨⟨r, hr, _⟩, _⟩ := hSeedC
    rw [hC.allSettled r] at hr
    cases hr
  · exact hμv
  · simpa [C'] using hSeed

/-- Marginal one-step form of
`PEM_odd_median_max_timer_one_reset_seed_prob_lower_bound`. -/
theorem PEM_odd_median_max_timer_one_reset_seed_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : (C μ).1.timer = 1)
    (h_max_wrong : (C v).1.answer ≠ opinionToAnswer (C μ).2) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C CorrectResetSeed
        (by classical exact inferInstance) 1 := by
  classical
  have hGoal : ¬ CorrectResetSeed C := by
    intro hSeedC
    obtain ⟨⟨r, hr, _⟩, _⟩ := hSeedC
    rw [hC.allSettled r] at hr
    cases hr
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C CorrectResetSeed 1 :=
    PEM_odd_median_max_timer_one_reset_seed_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hRmax hC hμv hpar hμ_med hv_max hμ_input_A
      h_timer h_max_wrong
  simpa using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := CorrectResetSeed) hGoal hhit)

/-- Marginal one-step form of
`PEM_even_lower_median_max_timer_one_reset_seed_prob_lower_bound`. -/
theorem PEM_even_lower_median_max_timer_one_reset_seed_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by classical exact inferInstance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C CorrectResetSeed
        (by classical exact inferInstance) 1 := by
  classical
  have hGoal : ¬ CorrectResetSeed C := by
    intro hSeedC
    obtain ⟨⟨r, hr, _⟩, _⟩ := hSeedC
    rw [hC.allSettled r] at hr
    cases hr
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C CorrectResetSeed 1 :=
    PEM_even_lower_median_max_timer_one_reset_seed_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hn4 hRmax hC hμv hpar hμ_lower hv_max h_timer
      hμ_correct hv_wrong
  simpa using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := CorrectResetSeed) hGoal hhit)

/-- Resetting agents that can safely spread the correct reset seed without
exhausting their reset fuel. -/
def richResetSeedSet (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter fun r : Fin n =>
    (C r).1.role = .Resetting ∧
    nonResettingCount C < (C r).1.resetcount ∧
    (C r).1.answer = majorityAnswer C

def richResetSeedCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (richResetSeedSet C).card

theorem richResetSeedCount_pos_of_CorrectResetSeed
    {C : Config (AgentState n) Opinion n} (hSeed : CorrectResetSeed C) :
    0 < richResetSeedCount C := by
  classical
  obtain ⟨⟨r, hr_role, hr_count, _hr_leader, hr_answer⟩, _⟩ := hSeed
  unfold richResetSeedCount richResetSeedSet
  apply Finset.card_pos.mpr
  exact ⟨r, Finset.mem_filter.mpr
    ⟨Finset.mem_univ r, hr_role, hr_count, hr_answer⟩⟩

theorem richResetSeedCount_le_n
    (C : Config (AgentState n) Opinion n) :
    richResetSeedCount C ≤ n := by
  classical
  unfold richResetSeedCount richResetSeedSet
  calc
    (Finset.univ.filter fun r : Fin n =>
        (C r).1.role = .Resetting ∧
        nonResettingCount C < (C r).1.resetcount ∧
        (C r).1.answer = majorityAnswer C).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem propagate_reset_step_nonResettingCount_eq_sub_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C r).1.role = .Resetting)
    (hr_rc : 0 < (C r).1.resetcount)
    (hv_not : (C v).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    nonResettingCount (C.step P r v) + 1 = nonResettingCount C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C₁ : Config (AgentState n) Opinion n := C.step P r v with hC₁
  have hstep :=
    propagate_reset_step_nonResettingCount_lt
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C hrv hr_res hr_rc hv_not
  have hr_reset : (C₁ r).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_reset : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.2.1
  set S := Finset.univ.filter fun w : Fin n => (C w).1.role ≠ .Resetting with hS
  set S' := Finset.univ.filter fun w : Fin n => (C₁ w).1.role ≠ .Resetting with hS'
  have hv_mem : v ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ v, hv_not⟩
  have hS'_eq : S' = S.erase v := by
    ext x
    constructor
    · intro hx
      have hx_not : (C₁ x).1.role ≠ .Resetting := by
        rw [hS'] at hx
        exact (Finset.mem_filter.mp hx).2
      have hx_ne_v : x ≠ v := by
        intro hxv
        subst x
        exact hx_not hv_reset
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_not hr_reset
      have hx_state : C₁ x = C x := by
        rw [hC₁]
        dsimp [P]
        simp [Config.step, hrv, hx_ne_r, hx_ne_v]
      have hx_old : (C x).1.role ≠ .Resetting := by
        intro hreset
        exact hx_not (by rw [hx_state]; exact hreset)
      rw [Finset.mem_erase, hS, Finset.mem_filter]
      exact ⟨hx_ne_v, Finset.mem_univ x, hx_old⟩
    · intro hx
      have hx_ne_v : x ≠ v := (Finset.mem_erase.mp hx).1
      have hx_old : (C x).1.role ≠ .Resetting :=
        (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_old hr_res
      have hx_state : C₁ x = C x := by
        rw [hC₁]
        dsimp [P]
        simp [Config.step, hrv, hx_ne_r, hx_ne_v]
      rw [hS', Finset.mem_filter]
      refine ⟨Finset.mem_univ x, ?_⟩
      rw [hx_state]
      exact hx_old
  have hcard : S'.card + 1 = S.card := by
    rw [hS'_eq, Finset.card_erase_of_mem hv_mem]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨v, hv_mem⟩))
  dsimp [nonResettingCount]
  change (Finset.univ.filter (fun w : Fin n => (C₁ w).1.role ≠ .Resetting)).card + 1 =
    (Finset.univ.filter (fun w : Fin n => (C w).1.role ≠ .Resetting)).card
  rw [← hS, ← hS']
  exact hcard

/-- Once a correct reset seed exists, every interaction from the seed to a
non-`Resetting` agent keeps the correct-seed invariant and strictly decreases
`nonResettingCount`.  This is the stochastic companion to the deterministic
seed-propagation induction: it counts all currently non-resetting partners,
not just one chosen schedule edge. -/
theorem PEM_correctResetSeed_nonResetting_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  obtain ⟨⟨r, hr_role, hr_count, hr_leader, hr_answer⟩, hAllResetting⟩ := hSeed
  let NR : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.role ≠ .Resetting
  let S : Finset (Fin n × Fin n) := NR.image fun v => (r, v)
  have hr_count_pos : 0 < (C r).1.resetcount :=
    (hAllResetting r hr_role).1
  have hNR_card : NR.card = nonResettingCount C := by
    rfl
  have hS_card : S.card = nonResettingCount C := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · exact hNR_card
    · intro a b h
      exact congrArg Prod.snd h
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S, NR] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [Probability.mem_offDiagonalPairs]
    rw [← hpv]
    intro hrv
    have hv_not : (C v).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv).2
    have hrv' : r = v := by
      simpa using hrv
    subst v
    exact hv_not hr_role
  have hstep : ∀ p ∈ S,
      CorrectResetSeed (C.step P p.1 p.2) ∧
        nonResettingCount (C.step P p.1 p.2) < nonResettingCount C := by
    intro p hp
    dsimp [S, NR] at hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨v, hv, hpv⟩
    rw [← hpv]
    have hv_not : (C v).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv).2
    have hrv : r ≠ v := by
      intro h
      subst v
      exact hv_not hr_role
    have hdrop :=
      propagate_reset_step_nonResettingCount_lt
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hrv hr_role hr_count_pos hv_not
    have hsender :=
      propagate_reset_spreader_state
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hrv hr_role hr_count_pos hv_not
    have hpartner :=
      propagate_reset_step_partner_rc
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hrv hr_role hr_count_pos hv_not
    have hans :=
      propagate_reset_step_answer_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hrv hr_role hr_count_pos hv_not hr_answer
    have hmaj :
        majorityAnswer (C.step P r v) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C r v)
    have hothers : ∀ w : Fin n, w ≠ r → w ≠ v →
        C.step P r v w = C w := by
      intro w hwr hwv
      dsimp [P, PEMProtocolCoupled, PEMProtocol]
      simp [Config.step, hrv, hwr, hwv]
    have hSeed' : CorrectResetSeed (C.step P r v) := by
      refine ⟨⟨r, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
      · have hdrop_count :
            nonResettingCount (C.step P r v) < nonResettingCount C := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
        have hrc :
            (C.step P r v r).1.resetcount = (C r).1.resetcount - 1 := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
        rw [hrc]
        omega
      · have hleader :
            (C.step P r v r).1.leader = (C r).1.leader := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using hsender.2.2
        rw [hleader, hr_leader]
      · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
      · intro w hw
        by_cases hwr : w = r
        · subst w
          constructor
          · have hrc :
                (C.step P r v r).1.resetcount =
                  (C r).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · by_cases hwv : w = v
          · subst w
            constructor
            · have hrc :
                (C.step P r v v).1.resetcount =
                  (C r).1.resetcount - 1 := by
                simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
              rw [hrc]
              omega
            · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
          · have hw_state : C.step P r v w = C w := hothers w hwr hwv
            have hw_old_role : (C w).1.role = .Resetting := by
              rw [← hw_state]
              exact hw
            have hw_old := hAllResetting w hw_old_role
            constructor
            · rw [hw_state]
              exact hw_old.1
            · rw [hw_state, hmaj]
              exact hw_old.2
    exact ⟨hSeed', by simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2⟩
  have hGoal_not :
      ¬ (CorrectResetSeed C ∧ nonResettingCount C < nonResettingCount C) := by
    intro h
    exact Nat.lt_irrefl _ h.2
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => CorrectResetSeed D ∧
              nonResettingCount D < nonResettingCount C)
            hGoal_not S hS_sub hstep

/-- Epidemic version of the correct-seed propagation bound.  Every rich reset
seed can recruit every non-`Resetting` agent; after such a step the
`CorrectResetSeed` invariant is still true and `nonResettingCount` strictly
drops. -/
theorem PEM_richResetSeed_nonResetting_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  obtain ⟨⟨r₀, hr₀_role, hr₀_count, hr₀_leader, hr₀_answer⟩,
    hAllResetting⟩ := hSeed
  let NR : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.role ≠ .Resetting
  let S : Finset (Fin n × Fin n) := (richResetSeedSet C).product NR
  have hNR_card : NR.card = nonResettingCount C := by
    rfl
  have hS_card : S.card = richResetSeedCount C * nonResettingCount C := by
    dsimp [S, richResetSeedCount]
    rw [Finset.card_product, hNR_card]
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S, NR] at hp
    obtain ⟨hq_mem, hv_mem⟩ := Finset.mem_product.mp hp
    have hq_role : (C p.1).1.role = .Resetting :=
      (Finset.mem_filter.mp hq_mem).2.1
    have hv_not : (C p.2).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv_mem).2
    rw [Probability.mem_offDiagonalPairs]
    intro hp_eq
    exact hv_not (by rw [← hp_eq]; exact hq_role)
  have hstep : ∀ p ∈ S,
      CorrectResetSeed (C.step P p.1 p.2) ∧
        nonResettingCount (C.step P p.1 p.2) < nonResettingCount C := by
    intro p hp
    dsimp [S, NR] at hp
    obtain ⟨hq_mem, hv_mem⟩ := Finset.mem_product.mp hp
    have hq_rich := (Finset.mem_filter.mp hq_mem).2
    have hq_role : (C p.1).1.role = .Resetting := hq_rich.1
    have hq_count : nonResettingCount C < (C p.1).1.resetcount :=
      hq_rich.2.1
    have hq_answer : (C p.1).1.answer = majorityAnswer C :=
      hq_rich.2.2
    have hv_not : (C p.2).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv_mem).2
    have hp_ne : p.1 ≠ p.2 := by
      intro h
      exact hv_not (by rw [← h]; exact hq_role)
    have hq_count_pos : 0 < (C p.1).1.resetcount := by
      omega
    have hdrop :=
      propagate_reset_step_nonResettingCount_lt
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hsender :=
      propagate_reset_spreader_state
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hpartner :=
      propagate_reset_step_partner_rc
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hans :=
      propagate_reset_step_answer_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not hq_answer
    have hmaj :
        majorityAnswer (C.step P p.1 p.2) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C p.1 p.2)
    have hothers : ∀ w : Fin n, w ≠ p.1 → w ≠ p.2 →
        C.step P p.1 p.2 w = C w := by
      intro w hwq hwv
      dsimp [P, PEMProtocolCoupled, PEMProtocol]
      simp [Config.step, hp_ne, hwq, hwv]
    have hSeed' : CorrectResetSeed (C.step P p.1 p.2) := by
      refine ⟨?_, ?_⟩
      · by_cases hqr₀ : p.1 = r₀
        · refine ⟨p.1, ?_, ?_, ?_, ?_⟩
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
          · have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            have hN_drop :
                nonResettingCount (C.step P p.1 p.2) <
                  nonResettingCount C := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
            rw [hrc]
            omega
          · have hleader :
                (C.step P p.1 p.2 p.1).1.leader = (C p.1).1.leader := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hsender.2.2
            rw [hleader, hqr₀, hr₀_leader]
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · have hr₀_ne_v : r₀ ≠ p.2 := by
            intro h
            subst h
            exact hv_not hr₀_role
          have hr₀_state : C.step P p.1 p.2 r₀ = C r₀ :=
            hothers r₀ (by intro h; exact hqr₀ h.symm) hr₀_ne_v
          refine ⟨r₀, ?_, ?_, ?_, ?_⟩
          · rw [hr₀_state]
            exact hr₀_role
          · rw [hr₀_state]
            have hN_drop :
                nonResettingCount (C.step P p.1 p.2) <
                  nonResettingCount C := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
            omega
          · rw [hr₀_state]
            exact hr₀_leader
          · rw [hr₀_state, hmaj]
            exact hr₀_answer
      · intro w hw
        by_cases hwq : w = p.1
        · subst w
          constructor
          · have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · by_cases hwv : w = p.2
          · subst w
            constructor
            · have hrc :
                (C.step P p.1 p.2 p.2).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
                simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
              rw [hrc]
              omega
            · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
          · have hw_state : C.step P p.1 p.2 w = C w := hothers w hwq hwv
            have hw_old_role : (C w).1.role = .Resetting := by
              rw [← hw_state]
              exact hw
            have hw_old := hAllResetting w hw_old_role
            constructor
            · rw [hw_state]
              exact hw_old.1
            · rw [hw_state, hmaj]
              exact hw_old.2
    exact ⟨hSeed', by simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2⟩
  have hGoal_not :
      ¬ (CorrectResetSeed C ∧ nonResettingCount C < nonResettingCount C) := by
    intro h
    exact Nat.lt_irrefl _ h.2
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => CorrectResetSeed D ∧
              nonResettingCount D < nonResettingCount C)
            hGoal_not S hS_sub hstep

/-- Uniform one-step descent form of the rich-seed epidemic bound.  Since
`CorrectResetSeed` guarantees at least one rich seed and the phase is live
when `nonResettingCount > 0`, the one-step descent probability is at least
one ordered scheduler edge. -/
theorem PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C) 1 := by
  classical
  have hrich_pos : 0 < richResetSeedCount C :=
    richResetSeedCount_pos_of_CorrectResetSeed hSeed
  have hnat :
      1 ≤ richResetSeedCount C * nonResettingCount C := by
    exact Nat.succ_le_of_lt (Nat.mul_pos hrich_pos hpos)
  have hcoef :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    calc
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹
          = (1 : ENNReal) *
              ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by simp
      _ ≤ ((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
            have hcast :
                (1 : ENNReal) ≤
                  ((richResetSeedCount C * nonResettingCount C : ℕ) :
                    ENNReal) := by
              exact_mod_cast hnat
            exact mul_le_mul_left hcast _
  exact le_trans hcoef
    (PEM_richResetSeed_nonResetting_descent_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hDmax hSeed hpos)

/-- Marginal one-step version of
`PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound`, for
reset-epidemic phase composition. -/
theorem PEM_correctResetSeed_nonResetting_positive_descent_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => CorrectResetSeed D ∧
      nonResettingCount D < nonResettingCount C
  have hGoal : ¬ Goal C := by
    intro h
    exact Nat.lt_irrefl _ h.2
  have hhit :
      ((n * (n - 1) : ℕ) : ENNReal)⁻¹ ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_correctResetSeed_nonResetting_positive_descent_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hDmax hSeed hpos)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Successful rich-seed propagation is not only a descent in
`nonResettingCount`; it also strictly increases the number of rich reset
seeds.  This is the local epidemic-growth statement needed for the real
Kanaya-style propagation window. -/
theorem PEM_richResetSeed_growth_exact_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount D) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  obtain ⟨⟨r₀, hr₀_role, hr₀_count, hr₀_leader, hr₀_answer⟩,
    hAllResetting⟩ := hSeed
  let NR : Finset (Fin n) :=
    Finset.univ.filter fun v : Fin n => (C v).1.role ≠ .Resetting
  let S : Finset (Fin n × Fin n) := (richResetSeedSet C).product NR
  have hNR_card : NR.card = nonResettingCount C := by
    rfl
  have hS_card : S.card = richResetSeedCount C * nonResettingCount C := by
    dsimp [S, richResetSeedCount]
    rw [Finset.card_product, hNR_card]
  have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
    intro p hp
    dsimp [S, NR] at hp
    obtain ⟨hq_mem, hv_mem⟩ := Finset.mem_product.mp hp
    have hq_role : (C p.1).1.role = .Resetting :=
      (Finset.mem_filter.mp hq_mem).2.1
    have hv_not : (C p.2).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv_mem).2
    rw [Probability.mem_offDiagonalPairs]
    intro hp_eq
    exact hv_not (by rw [← hp_eq]; exact hq_role)
  have hstep : ∀ p ∈ S,
      CorrectResetSeed (C.step P p.1 p.2) ∧
        nonResettingCount (C.step P p.1 p.2) + 1 = nonResettingCount C ∧
        richResetSeedCount C < richResetSeedCount (C.step P p.1 p.2) := by
    intro p hp
    dsimp [S, NR] at hp
    obtain ⟨hq_mem, hv_mem⟩ := Finset.mem_product.mp hp
    have hq_rich := (Finset.mem_filter.mp hq_mem).2
    have hq_role : (C p.1).1.role = .Resetting := hq_rich.1
    have hq_count : nonResettingCount C < (C p.1).1.resetcount :=
      hq_rich.2.1
    have hq_answer : (C p.1).1.answer = majorityAnswer C :=
      hq_rich.2.2
    have hv_not : (C p.2).1.role ≠ .Resetting :=
      (Finset.mem_filter.mp hv_mem).2
    have hp_ne : p.1 ≠ p.2 := by
      intro h
      exact hv_not (by rw [← h]; exact hq_role)
    have hq_count_pos : 0 < (C p.1).1.resetcount := by omega
    have hdrop :=
      propagate_reset_step_nonResettingCount_lt
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hsender :=
      propagate_reset_spreader_state
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hpartner :=
      propagate_reset_step_partner_rc
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not
    have hans :=
      propagate_reset_step_answer_trace
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hDmax C hp_ne hq_role hq_count_pos hv_not hq_answer
    have hmaj :
        majorityAnswer (C.step P p.1 p.2) = majorityAnswer C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (majorityAnswer_step_eq
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) C p.1 p.2)
    have hN_drop :
        nonResettingCount (C.step P p.1 p.2) < nonResettingCount C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.2.2
    have hN_exact :
        nonResettingCount (C.step P p.1 p.2) + 1 =
          nonResettingCount C := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (propagate_reset_step_nonResettingCount_eq_sub_one
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
          hDmax C hp_ne hq_role hq_count_pos hv_not)
    have hothers : ∀ w : Fin n, w ≠ p.1 → w ≠ p.2 →
        C.step P p.1 p.2 w = C w := by
      intro w hwq hwv
      dsimp [P, PEMProtocolCoupled, PEMProtocol]
      simp [Config.step, hp_ne, hwq, hwv]
    have hSeed' : CorrectResetSeed (C.step P p.1 p.2) := by
      refine ⟨?_, ?_⟩
      · by_cases hqr₀ : p.1 = r₀
        · refine ⟨p.1, ?_, ?_, ?_, ?_⟩
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
          · have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · have hleader :
                (C.step P p.1 p.2 p.1).1.leader = (C p.1).1.leader := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hsender.2.2
            rw [hleader, hqr₀, hr₀_leader]
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · have hr₀_ne_v : r₀ ≠ p.2 := by
            intro h
            subst h
            exact hv_not hr₀_role
          have hr₀_state : C.step P p.1 p.2 r₀ = C r₀ :=
            hothers r₀ (by intro h; exact hqr₀ h.symm) hr₀_ne_v
          refine ⟨r₀, ?_, ?_, ?_, ?_⟩
          · rw [hr₀_state]
            exact hr₀_role
          · rw [hr₀_state]
            omega
          · rw [hr₀_state]
            exact hr₀_leader
          · rw [hr₀_state, hmaj]
            exact hr₀_answer
      · intro w hw
        by_cases hwq : w = p.1
        · subst w
          constructor
          · have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
        · by_cases hwv : w = p.2
          · subst w
            constructor
            · have hrc :
                (C.step P p.1 p.2 p.2).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
                simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
              rw [hrc]
              omega
            · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
          · have hw_state : C.step P p.1 p.2 w = C w := hothers w hwq hwv
            have hw_old_role : (C w).1.role = .Resetting := by
              rw [← hw_state]
              exact hw
            have hw_old := hAllResetting w hw_old_role
            constructor
            · rw [hw_state]
              exact hw_old.1
            · rw [hw_state, hmaj]
              exact hw_old.2
    have hp2_not_old : p.2 ∉ richResetSeedSet C := by
      intro hp2_old
      have hp2_role : (C p.2).1.role = .Resetting :=
        (Finset.mem_filter.mp hp2_old).2.1
      exact hv_not hp2_role
    have hsub_insert :
        insert p.2 (richResetSeedSet C) ⊆
          richResetSeedSet (C.step P p.1 p.2) := by
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with hwv | hwold
      · subst w
        unfold richResetSeedSet
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ p.2, ?_, ?_, ?_⟩
        · simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.1
        · have hrc :
              (C.step P p.1 p.2 p.2).1.resetcount =
                (C p.1).1.resetcount - 1 := by
            simpa [P, PEMProtocolCoupled, PEMProtocol] using hpartner.2
          rw [hrc]
          omega
        · simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.2
      · have hw_rich := (Finset.mem_filter.mp hwold).2
        have hrole_new : (C.step P p.1 p.2 w).1.role = .Resetting := by
          by_cases hwq : w = p.1
          · subst w
            simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.1
          · have hwv_ne : w ≠ p.2 := by
              intro h
              subst w
              exact hp2_not_old hwold
            have hw_state : C.step P p.1 p.2 w = C w :=
              hothers w hwq hwv_ne
            rw [hw_state]
            exact hw_rich.1
        have hcount_new :
            nonResettingCount (C.step P p.1 p.2) <
              (C.step P p.1 p.2 w).1.resetcount := by
          by_cases hwq : w = p.1
          · subst w
            have hrc :
                (C.step P p.1 p.2 p.1).1.resetcount =
                  (C p.1).1.resetcount - 1 := by
              simpa [P, PEMProtocolCoupled, PEMProtocol] using hdrop.2.1
            rw [hrc]
            omega
          · have hwv_ne : w ≠ p.2 := by
              intro h
              subst w
              exact hp2_not_old hwold
            have hw_state : C.step P p.1 p.2 w = C w :=
              hothers w hwq hwv_ne
            rw [hw_state]
            omega
        have hanswer_new :
            (C.step P p.1 p.2 w).1.answer =
              majorityAnswer (C.step P p.1 p.2) := by
          by_cases hwq : w = p.1
          · subst w
            simpa [P, PEMProtocolCoupled, PEMProtocol] using hans.1
          · have hwv_ne : w ≠ p.2 := by
              intro h
              subst w
              exact hp2_not_old hwold
            have hw_state : C.step P p.1 p.2 w = C w :=
              hothers w hwq hwv_ne
            rw [hw_state, hmaj]
            exact hw_rich.2.2
        unfold richResetSeedSet
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ w, hrole_new, hcount_new, hanswer_new⟩
    have hcard_insert :
        (insert p.2 (richResetSeedSet C)).card =
          richResetSeedCount C + 1 := by
      unfold richResetSeedCount
      rw [Finset.card_insert_of_notMem hp2_not_old]
    have hgrowth : richResetSeedCount C <
        richResetSeedCount (C.step P p.1 p.2) := by
      have hle := Finset.card_le_card hsub_insert
      have hle' :
          richResetSeedCount C + 1 ≤
            richResetSeedCount (C.step P p.1 p.2) := by
        rw [← hcard_insert]
        unfold richResetSeedCount
        exact hle
      omega
    exact ⟨hSeed', hN_exact, hgrowth⟩
  have hGoal_not :
      ¬ (CorrectResetSeed C ∧ nonResettingCount C + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount C) := by
    intro h
    omega
  have hmass :
      Probability.pairSetMass n hn2 S =
        (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
    rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub,
      hS_card]
  calc
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
        = Probability.pairSetMass n hn2 S := hmass.symm
    _ ≤ Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount D) 1 :=
          Probability.ProbHitWithin_one_lower_bound_of_pairSet
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (fun D => CorrectResetSeed D ∧
              nonResettingCount D + 1 = nonResettingCount C ∧
              richResetSeedCount C < richResetSeedCount D)
            hGoal_not S hS_sub hstep

theorem PEM_richResetSeed_growth_prob_lower_bound
    {n Rmax Emax Dmax : ℕ} (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D < nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount D) 1 := by
  classical
  have hexact :=
    PEM_richResetSeed_growth_exact_prob_lower_bound
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hDmax hSeed hpos
  have hGoalExact :
      ¬ (CorrectResetSeed C ∧
          nonResettingCount C + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount C) := by
    intro h
    omega
  have hGoalWeak :
      ¬ (CorrectResetSeed C ∧ nonResettingCount C < nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount C) := by
    intro h
    exact Nat.lt_irrefl _ h.2.1
  have hmono :
      Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D => CorrectResetSeed D ∧
            nonResettingCount D + 1 = nonResettingCount C ∧
            richResetSeedCount C < richResetSeedCount D) 1 ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
          (fun D => CorrectResetSeed D ∧
            nonResettingCount D < nonResettingCount C ∧
            richResetSeedCount C < richResetSeedCount D) 1 :=
    Probability.ProbHitWithin_one_mono_goal
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal₁ := fun D => CorrectResetSeed D ∧
        nonResettingCount D + 1 = nonResettingCount C ∧
        richResetSeedCount C < richResetSeedCount D)
      (Goal₂ := fun D => CorrectResetSeed D ∧
        nonResettingCount D < nonResettingCount C ∧
        richResetSeedCount C < richResetSeedCount D)
      hGoalExact hGoalWeak
      (by
        intro D hD
        refine ⟨hD.1, ?_, hD.2.2⟩
        omega)
  exact le_trans hexact hmono

/-- Marginal one-step version of
`PEM_richResetSeed_growth_exact_prob_lower_bound`, for phase composition.
From the current state the exact-growth target is false, so one-step hitting
and one-step endpoint reachability coincide. -/
theorem PEM_richResetSeed_growth_exact_probReached_lower_bound
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (hDmax : 1 < Dmax)
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hpos : 0 < nonResettingCount C) :
    (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      @Probability.probReached (AgentState n) Opinion Output n
        (by infer_instance)
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => CorrectResetSeed D ∧
          nonResettingCount D + 1 = nonResettingCount C ∧
          richResetSeedCount C < richResetSeedCount D)
        (by classical exact inferInstance) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => CorrectResetSeed D ∧
      nonResettingCount D + 1 = nonResettingCount C ∧
      richResetSeedCount C < richResetSeedCount D
  have hGoal : ¬ Goal C := by
    intro h
    dsimp [Goal] at h
    omega
  have hhit :
      (((richResetSeedCount C * nonResettingCount C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C Goal 1 := by
    simpa [Goal] using
      (PEM_richResetSeed_growth_exact_prob_lower_bound
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 hDmax hSeed hpos)
  simpa [Goal] using
    (Probability.probReached_one_lower_bound_of_ProbHitWithin_one_lower_bound
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0) (hn := hn2) (C₀ := C)
      (Goal := Goal) hGoal hhit)

/-- Endpoint form of the reset-seed epidemic: once no non-`Resetting` agent
remains, `CorrectResetSeed` gives exactly the all-resetting positive-leader
uniform-answer shape consumed by the deterministic Phase-A normalizer. -/
theorem allResetting_pos_leader_uniform_answer_of_CorrectResetSeed_nonResetting_zero
    {C : Config (AgentState n) Opinion n}
    (hSeed : CorrectResetSeed C) (hzero : nonResettingCount C = 0) :
    (∀ w : Fin n, (C w).1.role = .Resetting) ∧
    (∀ w : Fin n, 0 < (C w).1.resetcount) ∧
    (∃ ℓ : Fin n, (C ℓ).1.leader = .L) ∧
    (∀ w : Fin n, (C w).1.answer = majorityAnswer C) := by
  classical
  obtain ⟨⟨r, hr_role, _hr_count, hr_leader, _hr_answer⟩, hAll⟩ := hSeed
  have hAllRole : ∀ w : Fin n, (C w).1.role = .Resetting := by
    intro w
    by_contra hw
    have hpos : 0 < nonResettingCount C := by
      unfold nonResettingCount
      apply Finset.card_pos.mpr
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩
    omega
  refine ⟨hAllRole, ?_, ?_, ?_⟩
  · intro w
    exact (hAll w (hAllRole w)).1
  · exact ⟨r, hr_leader⟩
  · intro w
    exact (hAll w (hAllRole w)).2

/-- Qualitative deterministic consensus reachability for the coupled protocol
family used by the existing time-bound lemmas.  This is the deterministic
input that the stochastic layer must quantify by counting scheduler windows. -/
theorem PEM_consensus_reachable
    {n Rmax Emax Dmax : ℕ} {hn0 : 0 < n}
    [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig
          (execution (PEMProtocolCoupled n Rmax Emax Dmax hn0) C₀ γ t) := by
  simpa [PEMProtocolCoupled, PEMProtocol] using
    (P_EM_consensus_reachable_from_BurmanConvergence_only
      (n := n) (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
      (rankDeltaOSSR_satisfies_fix
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hn4
      (burmanConvergence_concrete
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hn4 hEmax hDmax hRmax))

/-! ### Kanaya Table-2 phase composition -/

/-- The product of the five success probabilities in Kanaya Table 2:
`1/10 * 1/20 * 1/8 * 1/1280 * 1/2`.

The decimal denominator is `4096000`; keeping the product form avoids
unnecessary arithmetic coercion work in phase-composition proofs. -/
noncomputable def pemTable2SuccessProb : ENNReal :=
  ((10 : ENNReal)⁻¹) *
    ((20 : ENNReal)⁻¹) *
      ((8 : ENNReal)⁻¹) *
        ((1280 : ENNReal)⁻¹) *
          ((2 : ENNReal)⁻¹)

theorem pemTable2SuccessProb_le_one : pemTable2SuccessProb ≤ 1 := by
  unfold pemTable2SuccessProb
  have h10 : ((10 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  have h20 : ((20 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  have h8 : ((8 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  have h1280 : ((1280 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  have h2 : ((2 : ENNReal)⁻¹) ≤ 1 :=
    (ENNReal.inv_le_one).2 (by norm_num)
  calc
    ((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹) *
          ((8 : ENNReal)⁻¹) * ((1280 : ENNReal)⁻¹) *
          ((2 : ENNReal)⁻¹)
        ≤ 1 * 1 * 1 * 1 * 1 := by
          gcongr
    _ = 1 := by norm_num

/-- Direct five-phase window composition for the Table-2 route.  The
hypotheses are conditional endpoint probabilities for each phase; no
independence between phase endpoints is assumed. -/
theorem pem_table2_phase_window_to_ProbHitWithin
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (SrankPhase SswapPhase SdecPhase StimPhase SemPhase :
      Config (AgentState n) Opinion n → Prop)
    [DecidablePred SrankPhase] [DecidablePred SswapPhase]
    [DecidablePred SdecPhase] [DecidablePred StimPhase]
    [DecidablePred SemPhase]
    (tRank tSwap tDec tTim tSem : ℕ)
    (hRank :
      ((10 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C₀ SrankPhase tRank)
    (hSwap : ∀ C, SrankPhase C →
      ((20 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SswapPhase tSwap)
    (hDec : ∀ C, SswapPhase C →
      ((8 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SdecPhase tDec)
    (hTim : ∀ C, SdecPhase C →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C StimPhase tTim)
    (hSem : ∀ C, StimPhase C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SemPhase tSem) :
    pemTable2SuccessProb ≤
      Probability.ProbHitWithin P hn2 C₀ SemPhase
        ((((tRank + tSwap) + tDec) + tTim) + tSem) := by
  classical
  have hRankHit :
      ((10 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ SrankPhase tRank :=
    hRank.trans (Probability.probReached_le_ProbHitWithin P hn2 C₀ SrankPhase tRank)
  have hSwapHit : ∀ C, SrankPhase C →
      ((20 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SswapPhase tSwap := by
    intro C hC
    exact (hSwap C hC).trans
      (Probability.probReached_le_ProbHitWithin P hn2 C SswapPhase tSwap)
  have hDecHit : ∀ C, SswapPhase C →
      ((8 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SdecPhase tDec := by
    intro C hC
    exact (hDec C hC).trans
      (Probability.probReached_le_ProbHitWithin P hn2 C SdecPhase tDec)
  have hTimHit : ∀ C, SdecPhase C →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C StimPhase tTim := by
    intro C hC
    exact (hTim C hC).trans
      (Probability.probReached_le_ProbHitWithin P hn2 C StimPhase tTim)
  have hSemHit : ∀ C, StimPhase C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SemPhase tSem := by
    intro C hC
    exact (hSem C hC).trans
      (Probability.probReached_le_ProbHitWithin P hn2 C SemPhase tSem)
  have h12 :
      ((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ SswapPhase (tRank + tSwap) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      SrankPhase SswapPhase tRank tSwap
      ((10 : ENNReal)⁻¹) ((20 : ENNReal)⁻¹) hRankHit hSwapHit
  have h123 :
      (((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ SdecPhase
          ((tRank + tSwap) + tDec) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      SswapPhase SdecPhase (tRank + tSwap) tDec
      (((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) ((8 : ENNReal)⁻¹)
      h12 hDecHit
  have h1234 :
      ((((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹)) *
          ((1280 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ StimPhase
          (((tRank + tSwap) + tDec) + tTim) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      SdecPhase StimPhase ((tRank + tSwap) + tDec) tTim
      ((((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹))
      ((1280 : ENNReal)⁻¹) h123 hTimHit
  have h12345 :
      (((((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹)) *
          ((1280 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C₀ SemPhase
          ((((tRank + tSwap) + tDec) + tTim) + tSem) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      StimPhase SemPhase (((tRank + tSwap) + tDec) + tTim) tSem
      (((((10 : ENNReal)⁻¹) * ((20 : ENNReal)⁻¹)) * ((8 : ENNReal)⁻¹)) *
        ((1280 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹) h1234 hSemHit
  simpa [pemTable2SuccessProb, mul_assoc] using h12345

/-- Three-phase consensus composition using only hitting-window probabilities.

This is the lightweight PEM route: hit `InSrank`, then hit `InSswap` from any
ranking endpoint, then hit consensus from any swap endpoint.  The middle target
does not need to be absorbing, because the composition is entirely in
`ProbHitWithin`. -/
theorem PEM_consensus_ProbHitWithin_from_phase_bounds
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred
      (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (tRank tSwap tConsensus : ℕ)
    (pRank pSwap pConsensus : ENNReal)
    (hRank :
      pRank ≤ Probability.ProbHitWithin P hn2 C₀ InSrank tRank)
    (hSwap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
      pSwap ≤ Probability.ProbHitWithin P hn2 C InSswap tSwap)
    (hConsensus : ∀ C : Config (AgentState n) Opinion n, InSswap C →
      pConsensus ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig tConsensus) :
    (pRank * pSwap) * pConsensus ≤
      Probability.ProbHitWithin P hn2 C₀ IsConsensusConfig
        ((tRank + tSwap) + tConsensus) := by
  classical
  have hRankSwap :
      pRank * pSwap ≤
        Probability.ProbHitWithin P hn2 C₀ InSswap (tRank + tSwap) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      InSrank InSswap tRank tSwap pRank pSwap hRank hSwap
  exact
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀
      InSswap IsConsensusConfig (tRank + tSwap) tConsensus
      (pRank * pSwap) pConsensus hRankSwap hConsensus

/-- Markov-generated `1/2 × 1/2 × 1/2` version of
`PEM_consensus_ProbHitWithin_from_phase_bounds`.  Each phase only supplies an
expected hitting-time bound; Markov converts it to a half-probability
`ProbHitWithin` window, and the three windows compose by strong Markov. -/
theorem PEM_consensus_ProbHitWithin_from_expected_phases
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred
      (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (MRank MSwap MConsensus tRank tSwap tConsensus : ℕ)
    (hRankExpected :
      Probability.expectedHittingTime P hn2 C₀ InSrank ≤ MRank)
    (hRankWindow : 2 * MRank ≤ tRank + 1)
    (hSwapExpected : ∀ C : Config (AgentState n) Opinion n, InSrank C →
      Probability.expectedHittingTime P hn2 C InSswap ≤ MSwap)
    (hSwapWindow : 2 * MSwap ≤ tSwap + 1)
    (hConsensusExpected :
      ∀ C : Config (AgentState n) Opinion n, InSswap C →
        Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
          MConsensus)
    (hConsensusWindow : 2 * MConsensus ≤ tConsensus + 1) :
    (((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ IsConsensusConfig
        ((tRank + tSwap) + tConsensus) := by
  classical
  apply PEM_consensus_ProbHitWithin_from_phase_bounds P hn2 C₀
    tRank tSwap tConsensus
    ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
  · exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C₀ InSrank hRankExpected hRankWindow
  · intro C hC
    exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C InSswap (hSwapExpected C hC) hSwapWindow
  · intro C hC
    exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
      P hn2 C IsConsensusConfig (hConsensusExpected C hC)
        hConsensusWindow

/-- Expected-parallel-time consequence of a uniform Table-2 success window.
This is the abstract geometric amplification step after the concrete phase
probability window has been proved. -/
theorem pem_table2_window_to_expectedParallelTime
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (K : ℕ) [NeZero K]
    (hwin : ∀ C : Config (AgentState n) Opinion n,
      ¬ IsConsensusConfig C →
        pemTable2SuccessProb ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig K) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      Probability.expectedParallelTimeToConsensus P hn2 C₀ ≤
        ((K : ENNReal) * pemTable2SuccessProb⁻¹) / n := by
  intro C₀
  exact
    (Probability.expectedParallelTime_le_window_mul_inv
      (P := P) (hn := hn2) (C₀ := C₀)
      (Goal := IsConsensusConfig) (K := K) (p := pemTable2SuccessProb)
      pemTable2SuccessProb_le_one hwin)

/-- Uniform five-phase Table-2 hypotheses imply the expected-parallel-time
window bound.  The remaining protocol-specific work is exactly to prove these
five hypotheses from scheduler-good-pair counts. -/
theorem pem_table2_phase_windows_to_expectedParallelTime
    {n : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
    (SrankPhase SswapPhase SdecPhase StimPhase :
      Config (AgentState n) Opinion n → Prop)
    [DecidablePred SrankPhase] [DecidablePred SswapPhase]
    [DecidablePred SdecPhase] [DecidablePred StimPhase]
    [DecidablePred
      (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (tRank tSwap tDec tTim tSem : ℕ)
    [NeZero ((((tRank + tSwap) + tDec) + tTim) + tSem)]
    (hRank : ∀ C₀,
      ((10 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C₀ SrankPhase tRank)
    (hSwap : ∀ C, SrankPhase C →
      ((20 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SswapPhase tSwap)
    (hDec : ∀ C, SswapPhase C →
      ((8 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C SdecPhase tDec)
    (hTim : ∀ C, SdecPhase C →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C StimPhase tTim)
    (hSem : ∀ C, StimPhase C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C
          (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)
          tSem) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      Probability.expectedParallelTimeToConsensus P hn2 C₀ ≤
        (((((tRank + tSwap) + tDec) + tTim) + tSem : ℕ) : ENNReal) *
          pemTable2SuccessProb⁻¹ / n := by
  classical
  let K := (((tRank + tSwap) + tDec) + tTim) + tSem
  have hwin : ∀ C : Config (AgentState n) Opinion n,
      ¬ IsConsensusConfig C →
        pemTable2SuccessProb ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C _hNot
    simpa [K] using
      (pem_table2_phase_window_to_ProbHitWithin
        (P := P) (hn2 := hn2) (C₀ := C)
        (SrankPhase := SrankPhase) (SswapPhase := SswapPhase)
        (SdecPhase := SdecPhase) (StimPhase := StimPhase)
        (SemPhase := IsConsensusConfig)
        tRank tSwap tDec tTim tSem
        (hRank C) hSwap hDec hTim hSem)
  intro C₀
  simpa [K] using
    (pem_table2_window_to_expectedParallelTime
      (P := P) (hn2 := hn2) (K := K) hwin C₀)

theorem not_exists_global_InSswap_median_timer_bound
    {n : ℕ} (hn0 : 0 < n) :
    ¬ ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C →
        (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀ := by
  classical
  rintro ⟨K₀, hK₀⟩
  let Cbad : Config (AgentState n) Opinion n := fun μ =>
    (({ role := .Settled
        rank := μ
        leader := .F
        resetcount := 0
        answer := .outA
        timer := K₀ + 1 } : AgentState n), Opinion.A)
  have hnA : nAOf Cbad = n := by
    unfold nAOf Config.agentsWithInput Config.inputOf
    simp [Cbad]
  have hSwap : InSswap Cbad := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_ }
    · intro v
      rfl
    · intro u v huv
      exact huv
    · intro v
      rw [hnA]
      simp [Cbad]
  have hceil_pos : 0 < ceilHalf n := ceilHalf_pos hn0
  have hceil_le : ceilHalf n ≤ n := ceilHalf_le n
  let μ : Fin n := ⟨ceilHalf n - 1, by omega⟩
  have hμ : (Cbad μ).1.rank.val + 1 = ceilHalf n := by
    dsimp [Cbad, μ]
    omega
  have hle : (Cbad μ).1.timer ≤ K₀ := hK₀ Cbad μ hSwap hμ
  dsimp [Cbad] at hle
  omega

/-- `InSswap` by itself carries neither a consensus guarantee nor a median
timer bound.  This is the concrete obstruction to any phase-C statement that
starts from an arbitrary `InSswap` configuration and tries to bound the time
to `IsConsensusConfig` only in terms of protocol parameters. -/
theorem exists_InSswap_not_consensus_with_large_median_timer
    {n : ℕ} (hn0 : 0 < n) (K : ℕ) :
    ∃ (C : Config (AgentState n) Opinion n) (μ : Fin n),
      InSswap C ∧ ¬ IsConsensusConfig C ∧
      (C μ).1.rank.val + 1 = ceilHalf n ∧ K < (C μ).1.timer := by
  classical
  let bad : Fin n := ⟨0, hn0⟩
  have hceil_pos : 0 < ceilHalf n := ceilHalf_pos hn0
  have hceil_le : ceilHalf n ≤ n := ceilHalf_le n
  let μ : Fin n := ⟨ceilHalf n - 1, by omega⟩
  let Cbad : Config (AgentState n) Opinion n := fun v =>
    (({ role := .Settled
        rank := v
        leader := .F
        resetcount := 0
        answer := if v = bad then .outB else .outA
        timer := if v = μ then K + 1 else 0 } : AgentState n), Opinion.A)
  have hnA : nAOf Cbad = n := by
    unfold nAOf Config.agentsWithInput Config.inputOf
    simp [Cbad]
  have hnB : nBOf Cbad = 0 := by
    unfold nBOf Config.agentsWithInput Config.inputOf
    simp [Cbad]
  have hSwap : InSswap Cbad := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_ }
    · intro v
      rfl
    · intro u v huv
      exact huv
    · intro v
      rw [hnA]
      simp [Cbad]
  have hMaj : majorityAnswer Cbad = .outA := by
    unfold majorityAnswer
    simp [hnA, hnB, hn0]
  have hNotConsensus : ¬ IsConsensusConfig Cbad := by
    intro hCons
    have hbad := hCons.allAnswerCorrect bad
    rw [hMaj] at hbad
    simp [Cbad, bad] at hbad
  have hμ_rank : (Cbad μ).1.rank.val + 1 = ceilHalf n := by
    dsimp [Cbad, μ]
    omega
  have hμ_timer : K < (Cbad μ).1.timer := by
    dsimp [Cbad]
    simp [μ]
  exact ⟨Cbad, μ, hSwap, hNotConsensus, hμ_rank, hμ_timer⟩

/-! ### Consolidated window hypothesis

The final theorem reduces to a single window-success claim: from any
non-consensus configuration, within a quadratic sequential window
(`c · n²` interactions), the protocol reaches `IsConsensusConfig` with
probability at least `pemTable2SuccessProb = 1/4096000`.

Once this claim is established, the abstract geometric-restart inequality
(`pem_table2_window_to_expectedParallelTime`) converts it directly into an
O(n) expected parallel time upper bound. -/

/-- **Kanaya Table-2 consolidated window hypothesis.**  From any non-consensus
configuration, the coupled PEM wrapper reaches `IsConsensusConfig` within
`c · n²` sequential interactions with probability at least
`pemTable2SuccessProb`.

The constant `c` absorbs the per-phase window constants from Table 2:
ranking (`O(n²)` seq), swap (`O(n²)` seq), decision/propagation
(`O(n²)` seq each), plus a trivial identity phase. -/
theorem PEM_consensus_window_success_prob_vacuous_timer_const
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (hTimerConst :
      ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C →
        (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * n * n) := by
  classical
  exact (not_exists_global_InSswap_median_timer_bound (by omega : 0 < n)
    hTimerConst).elim

/-- `pemTable2SuccessProb` is positive: product of positive inverses. -/
private theorem pemTable2SuccessProb_pos : 0 < pemTable2SuccessProb := by
  unfold pemTable2SuccessProb
  have hinv : ∀ (k : ℕ), ((k : ENNReal)⁻¹) ≠ 0 := by
    intro k; rw [ne_eq, ENNReal.inv_eq_zero]; exact ENNReal.natCast_ne_top k
  exact pos_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hinv 10) (hinv 20))
      (hinv 8)) (hinv 1280)) (hinv 2))

/-- `pemTable2SuccessProb` is not `⊤`. -/
private theorem pemTable2SuccessProb_ne_top : pemTable2SuccessProb ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt pemTable2SuccessProb_le_one ENNReal.one_lt_top)

/-- `pemTable2SuccessProb⁻¹` is not `⊤` (since `pemTable2SuccessProb > 0`). -/
private theorem pemTable2SuccessProb_inv_ne_top : pemTable2SuccessProb⁻¹ ≠ ⊤ := by
  rw [ENNReal.inv_ne_top]
  exact ne_of_gt pemTable2SuccessProb_pos

/-- Arithmetic helper: `c · n² · p⁻¹ / n = c · p⁻¹ · n` in ENNReal
after cancelling one factor of `n`. -/
private theorem ennreal_quadratic_window_div_cancel
    {c n : ℕ} (p : ENNReal) (hn : 0 < n)
    (_hp_pos : 0 < p) (_hp_ne_top : p ≠ ⊤) :
    ((c * n * n : ℕ) : ENNReal) * p⁻¹ / ↑n =
      ↑c * p⁻¹ * ↑n := by
  have hn_ne : (↑n : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_ne_top : (↑n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  rw [show (c * n * n : ℕ) = c * (n * n) from by ring]
  push_cast [Nat.cast_mul]
  rw [div_eq_mul_inv]
  calc ↑c * (↑n * ↑n) * p⁻¹ * (↑n : ENNReal)⁻¹
      = ↑c * p⁻¹ * (↑n * ↑n * (↑n : ENNReal)⁻¹) := by
        simp only [mul_comm, mul_assoc]
    _ = ↑c * p⁻¹ * (↑n * (↑n * (↑n : ENNReal)⁻¹)) := by
        rw [mul_assoc (↑n : ENNReal)]
    _ = ↑c * p⁻¹ * (↑n * 1) := by
        rw [ENNReal.mul_inv_cancel hn_ne hn_ne_top]
    _ = ↑c * p⁻¹ * ↑n := by rw [mul_one]

/-- Roundtrip: `↑c * p⁻¹ * ↑n` in ENNReal equals
`ENNReal.ofReal ((c : ℝ) * p⁻¹.toReal * (n : ℝ))` for finite `p⁻¹`. -/
private theorem ennreal_nat_mul_inv_mul_nat_eq_ofReal
    {c n : ℕ} (p : ENNReal)
    (hp_pos : 0 < p) (_hp_ne_top : p ≠ ⊤) :
    ↑c * p⁻¹ * (↑n : ENNReal) =
      ENNReal.ofReal ((c : ℝ) * p⁻¹.toReal * (n : ℝ)) := by
  have hp_inv_ne_top : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ne_of_gt hp_pos)
  symm
  calc ENNReal.ofReal ((c : ℝ) * p⁻¹.toReal * (n : ℝ))
      = ENNReal.ofReal ((c : ℝ) * p⁻¹.toReal) * ENNReal.ofReal (n : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (c : ℝ) * ENNReal.ofReal (p⁻¹.toReal) * ENNReal.ofReal (n : ℝ) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg c)]
    _ = ↑c * p⁻¹ * ↑n := by
          rw [ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hp_inv_ne_top, ENNReal.ofReal_natCast]

/-- **§5.2 quantitative — O(n) expected parallel time upper bound for P_EM,
parameterized by a constant/externally bounded timer regime.**

The literal `ConcretePEM n Emax Dmax` has timer range `7 * (n + 4)`, so the
direct Kanaya timer-drain argument only gives a weaker bound unless a sharper
timer lemma is added. -/
theorem PEM_expected_parallel_time_linear_param
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hTimerConst :
      ∃ K₀ : ℕ, ∀ (C : Config (AgentState n) Opinion n) (μ : Fin n),
        InSswap C →
        (C μ).1.rank.val + 1 = ceilHalf n →
        (C μ).1.timer ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        Probability.expectedParallelTimeToConsensus
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * n) := by
  classical
  obtain ⟨c, hc_pos, hwin⟩ :=
    PEM_consensus_window_success_prob_vacuous_timer_const hn4 hRmax hEmax hDmax hTimerConst
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  have hK_ne : NeZero (c * n * n) := ⟨by positivity⟩
  have hle := pem_table2_window_to_expectedParallelTime P hn2 (K := c * n * n) hwin
  refine ⟨c * pemTable2SuccessProb⁻¹.toReal, ?_, fun C₀ => ?_⟩
  · apply mul_pos
    · exact Nat.cast_pos.mpr hc_pos
    · exact ENNReal.toReal_pos
        (ne_of_gt (ENNReal.inv_pos.mpr pemTable2SuccessProb_ne_top))
        pemTable2SuccessProb_inv_ne_top
  · calc Probability.expectedParallelTimeToConsensus P hn2 C₀
        ≤ ((c * n * n : ℕ) : ENNReal) * pemTable2SuccessProb⁻¹ / ↑n := hle C₀
      _ = ↑c * pemTable2SuccessProb⁻¹ * ↑n :=
          ennreal_quadratic_window_div_cancel pemTable2SuccessProb
            (by omega) pemTable2SuccessProb_pos pemTable2SuccessProb_ne_top
      _ = ENNReal.ofReal (↑c * pemTable2SuccessProb⁻¹.toReal * ↑n) :=
          ennreal_nat_mul_inv_mul_nat_eq_ofReal pemTable2SuccessProb
            pemTable2SuccessProb_pos pemTable2SuccessProb_ne_top

/-! ### Non-vacuous window hypothesis and time bound -/

private def AgentCountersBounded (M : ℕ) (s : AgentState n) : Prop :=
  s.timer ≤ M ∧
  s.resetcount ≤ M ∧
  s.errorcount ≤ M ∧
  s.delaytimer ≤ M ∧
  s.children ≤ M

private def PairCountersBounded (M : ℕ) (p : AgentState n × AgentState n) : Prop :=
  AgentCountersBounded M p.1 ∧ AgentCountersBounded M p.2

private theorem resetOSSR_preserves_counter_bound
    {n Emax M : ℕ} {hn : 0 < n} {s : AgentState n}
    (hEmax : Emax ≤ M) (hs : AgentCountersBounded M s) :
    AgentCountersBounded M (resetOSSR Emax hn s) := by
  rcases s with ⟨role, rank, leader, resetcount, answer, timer, children,
    errorcount, delaytimer⟩
  cases leader <;> simp [AgentCountersBounded, resetOSSR] at * <;> omega

set_option maxHeartbeats 800000 in
private theorem processAgent_preserves_counter_bound
    {n Emax Dmax M : ℕ} {hn : 0 < n} {s : AgentState n}
    {oldRc : ℕ} {partnerResetting : Bool}
    (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (hs : AgentCountersBounded M s) :
    AgentCountersBounded M
      (processAgent Emax Dmax hn s oldRc partnerResetting) := by
  unfold processAgent
  by_cases hmain : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos hmain]
    let t : AgentState n :=
      if 0 < oldRc then
        { s with delaytimer := Dmax }
      else
        { s with delaytimer := s.delaytimer - 1 }
    have ht : AgentCountersBounded M t := by
      by_cases hold : 0 < oldRc
      · simp [t, hold, AgentCountersBounded] at * <;> omega
      · simp [t, hold, AgentCountersBounded] at * <;> omega
    change AgentCountersBounded M
      (if t.delaytimer = 0 ∨ !partnerResetting then resetOSSR Emax hn t else t)
    cases partnerResetting <;>
      by_cases hfire : t.delaytimer = 0 <;>
      simp [hfire, resetOSSR_preserves_counter_bound hEmax ht, ht]
  · rw [if_neg hmain]
    exact hs

private theorem propagateReset_recruit_preserves_counter_bound
    {n Emax Dmax M : ℕ} {a b : AgentState n}
    (hDmax : Dmax ≤ M)
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    PairCountersBounded M
      (if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
        (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
      else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
        ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
      else (a, b)) := by
  unfold PairCountersBounded
  split_ifs <;> simp_all [AgentCountersBounded] <;> omega

private theorem propagateReset_sync_preserves_counter_bound
    {n M : ℕ} {a b : AgentState n}
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    PairCountersBounded M
      (if a.role = .Resetting ∧ b.role = .Resetting then
        let newRc := max (a.resetcount - 1) (b.resetcount - 1)
        ({ a with resetcount := newRc }, { b with resetcount := newRc })
      else (a, b)) := by
  unfold PairCountersBounded
  split_ifs <;> simp_all [AgentCountersBounded, max_le_iff] <;> omega

private theorem propagateReset_preserves_counter_bound
    {n Emax Dmax M : ℕ} {hn : 0 < n} {a b : AgentState n}
    (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (propagateReset Emax Dmax hn a b).1 ∧
    AgentCountersBounded M (propagateReset Emax Dmax hn a b).2 := by
  unfold propagateReset
  let p₁ :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  have hp₁ : PairCountersBounded M p₁ := by
    simpa [p₁] using
      propagateReset_recruit_preserves_counter_bound
        (Emax := Emax) (Dmax := Dmax) hDmax ha hb
  let oldRcA := p₁.1.resetcount
  let oldRcB := p₁.2.resetcount
  let p₂ :=
    if p₁.1.role = .Resetting ∧ p₁.2.role = .Resetting then
      let newRc := max (p₁.1.resetcount - 1) (p₁.2.resetcount - 1)
      ({ p₁.1 with resetcount := newRc }, { p₁.2 with resetcount := newRc })
    else p₁
  have hp₂ : PairCountersBounded M p₂ := by
    exact propagateReset_sync_preserves_counter_bound hp₁.1 hp₁.2
  simpa [p₁, oldRcA, oldRcB, p₂, PairCountersBounded] using
    And.intro
      (processAgent_preserves_counter_bound hEmax hDmax hp₂.1)
      (processAgent_preserves_counter_bound hEmax hDmax hp₂.2)

set_option maxHeartbeats 800000 in
private theorem rankDeltaOSSR_preserves_counter_bound
    {n Rmax Emax Dmax M : ℕ} {hn : 0 < n} {a b : AgentState n}
    (hRmax : Rmax ≤ M) (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (hTwo : 2 ≤ M)
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
    AgentCountersBounded M (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  by_cases hReset : a.role = .Resetting ∨ b.role = .Resetting
  · simp [rankDeltaOSSR, hReset]
    have hpr := propagateReset_preserves_counter_bound (hn := hn) hEmax hDmax ha hb
    split_ifs <;> simp_all [AgentCountersBounded]
  · simp [rankDeltaOSSR, hReset]
    repeat' split_ifs <;> simp_all [AgentCountersBounded] <;> omega

set_option maxHeartbeats 800000 in
private theorem phase4_propagate_preserves_counter_bound
    {n Rmax M : ℕ} {a b : AgentState n}
    (hRmax : Rmax ≤ M)
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (phase4_propagate n Rmax a b).1 ∧
    AgentCountersBounded M (phase4_propagate n Rmax a b).2 := by
  unfold phase4_propagate
  by_cases haMed : a.rank.val + 1 = ceilHalf n
  · by_cases hbLast : b.rank.val + 1 = n
    · by_cases hReset :
        ({ a with timer := a.timer - 1 } : AgentState n).timer = 0 ∧
          ({ a with timer := a.timer - 1 } : AgentState n).answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentCountersBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, AgentCountersBounded] at * <;> omega
    · by_cases hReset : a.timer = 0 ∧ a.answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentCountersBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, AgentCountersBounded] at * <;> omega
  · by_cases hbMed : b.rank.val + 1 = ceilHalf n
    · by_cases haLast : a.rank.val + 1 = n
      · by_cases hReset :
          ({ b with timer := b.timer - 1 } : AgentState n).timer = 0 ∧
            ({ b with timer := b.timer - 1 } : AgentState n).answer ≠ a.answer
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentCountersBounded] at * <;>
            omega
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentCountersBounded] at * <;>
            omega
      · by_cases hReset : b.timer = 0 ∧ b.answer ≠ a.answer
        · simp [haMed, hbMed, haLast, hReset, AgentCountersBounded] at * <;> omega
        · simp [haMed, hbMed, haLast, hReset, AgentCountersBounded] at * <;> omega
    · simp [haMed, hbMed, AgentCountersBounded] at * <;> omega

private theorem phase4_swap_preserves_counter_bound
    {n M : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (phase4_swap a b x₀ x₁).1 ∧
    AgentCountersBounded M (phase4_swap a b x₀ x₁).2 := by
  unfold phase4_swap
  split_ifs <;> simp_all [AgentCountersBounded]

private theorem phase4_decide_preserves_counter_bound
    {n M : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentCountersBounded M a) (hb : AgentCountersBounded M b) :
    AgentCountersBounded M (phase4_decide n a b x₀ x₁).1 ∧
    AgentCountersBounded M (phase4_decide n a b x₀ x₁).2 := by
  unfold phase4_decide
  repeat' split_ifs <;> simp_all [AgentCountersBounded]

private theorem transitionPEM_phase4_preserves_counter_bound
    {n Rmax M : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (hRmax : Rmax ≤ M)
    (ha : AgentCountersBounded M a.1) (hb : AgentCountersBounded M a.2) :
    AgentCountersBounded M (transitionPEM_phase4 n Rmax a x₀ x₁).1 ∧
    AgentCountersBounded M (transitionPEM_phase4 n Rmax a x₀ x₁).2 := by
  by_cases hSettled : a.1.role = .Settled ∧ a.2.role = .Settled
  · let sw := phase4_swap a.1 a.2 x₀ x₁
    have hsw : AgentCountersBounded M sw.1 ∧ AgentCountersBounded M sw.2 :=
      phase4_swap_preserves_counter_bound (x₀ := x₀) (x₁ := x₁) ha hb
    let dec := phase4_decide n sw.1 sw.2 x₀ x₁
    have hdec : AgentCountersBounded M dec.1 ∧ AgentCountersBounded M dec.2 :=
      phase4_decide_preserves_counter_bound (x₀ := x₀) (x₁ := x₁) hsw.1 hsw.2
    have hprop :
        AgentCountersBounded M (phase4_propagate n Rmax dec.1 dec.2).1 ∧
        AgentCountersBounded M (phase4_propagate n Rmax dec.1 dec.2).2 :=
      phase4_propagate_preserves_counter_bound hRmax hdec.1 hdec.2
    simpa [transitionPEM_phase4, hSettled, sw, dec] using hprop
  · simpa [transitionPEM_phase4, hSettled] using And.intro ha hb

set_option maxHeartbeats 800000 in
private theorem transitionPEM_prePhase4_preserves_counter_bound
    {n trank M : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hTimer : 7 * (trank + 4) ≤ M)
    (hRankDelta :
      AgentCountersBounded M (rankDelta (s₀, s₁)).1 ∧
      AgentCountersBounded M (rankDelta (s₀, s₁)).2) :
    AgentCountersBounded M
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1 ∧
      AgentCountersBounded M
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2 := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s₀, s₁) with ⟨r₀, r₁⟩
  simp [hrd] at hRankDelta ⊢
  repeat' split_ifs <;> simp_all [AgentCountersBounded] <;> omega

set_option maxHeartbeats 800000 in
private theorem transitionPEM_preserves_counter_bound
    {n Rmax Emax Dmax M : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hTimer : 7 * (Rmax + 4) ≤ M)
    (hRmax : Rmax ≤ M) (hEmax : Emax ≤ M) (hDmax : Dmax ≤ M)
    (hTwo : 2 ≤ M)
    (hs₀ : AgentCountersBounded M s₀) (hs₁ : AgentCountersBounded M s₁) :
    AgentCountersBounded M
        ((PEMProtocolCoupled n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).1 ∧
      AgentCountersBounded M
        ((PEMProtocolCoupled n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).2 := by
  have hrd :=
    rankDeltaOSSR_preserves_counter_bound (hn := hn)
      hRmax hEmax hDmax hTwo hs₀ hs₁
  have hpre :=
    transitionPEM_prePhase4_preserves_counter_bound
      (x₀ := x₀) (x₁ := x₁) hTimer hrd
  simpa [PEMProtocolCoupled, protocolPEM, transitionPEM] using
    transitionPEM_phase4_preserves_counter_bound
      (x₀ := x₀) (x₁ := x₁) hRmax hpre.1 hpre.2

/-- Protocol execution preserves bounded counters: if all counters are
initially bounded by `7 * (Rmax + 4) + Emax + Dmax`, they stay bounded
after any interaction.  This is a protocol-specific invariant. -/
theorem PEMProtocolCoupled_preserves_bounded
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n) :
    let M := 7 * (Rmax + 4) + Emax + Dmax
    ∀ C : Config (AgentState n) Opinion n,
      IsBoundedConfig M C →
      ∀ i j : Fin n,
        IsBoundedConfig M (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn) i j) := by
  classical
  change ∀ C : Config (AgentState n) Opinion n,
      IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C →
      ∀ i j : Fin n,
        IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax)
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn) i j)
  intro C hC i j μ
  let M := 7 * (Rmax + 4) + Emax + Dmax
  have hTimer : 7 * (Rmax + 4) ≤ M := by omega
  have hRmaxM : Rmax ≤ M := by omega
  have hEmaxM : Emax ≤ M := by omega
  have hDmaxM : Dmax ≤ M := by omega
  have hTwo : 2 ≤ M := by omega
  have hi : AgentCountersBounded M (C i).1 := hC i
  have hj : AgentCountersBounded M (C j).1 := hC j
  by_cases hij : i = j
  · subst j
    simpa [Config.step, AgentCountersBounded, IsBoundedConfig] using hC μ
  · by_cases hμi : μ = i
    · subst μ
      have hpair :=
        transitionPEM_preserves_counter_bound
          (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2)
          hTimer hRmaxM hEmaxM hDmaxM hTwo hi hj
      simpa [Config.step, hij, AgentCountersBounded, IsBoundedConfig]
        using hpair.1
    · by_cases hμj : μ = j
      · subst μ
        have hpair :=
          transitionPEM_preserves_counter_bound
            (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2)
            hTimer hRmaxM hEmaxM hDmaxM hTwo hi hj
        simpa [Config.step, hij, hμi, AgentCountersBounded, IsBoundedConfig]
          using hpair.2
      · simpa [Config.step, hij, hμi, hμj, AgentCountersBounded, IsBoundedConfig]
          using hC μ

private def AgentTimerBounded (K : ℕ) (s : AgentState n) : Prop :=
  s.timer ≤ K

private def PairTimerBounded (K : ℕ) (p : AgentState n × AgentState n) : Prop :=
  AgentTimerBounded K p.1 ∧ AgentTimerBounded K p.2

private theorem resetOSSR_preserves_timer_bound
    {n Emax K : ℕ} {hn : 0 < n} {s : AgentState n}
    (hs : AgentTimerBounded K s) :
    AgentTimerBounded K (resetOSSR Emax hn s) := by
  rcases s with ⟨role, rank, leader, resetcount, answer, timer, children,
    errorcount, delaytimer⟩
  cases leader <;> simpa [AgentTimerBounded, resetOSSR] using hs

private theorem processAgent_preserves_timer_bound
    {n Emax Dmax K : ℕ} {hn : 0 < n} {s : AgentState n}
    {oldRc : ℕ} {partnerResetting : Bool}
    (hs : AgentTimerBounded K s) :
    AgentTimerBounded K
      (processAgent Emax Dmax hn s oldRc partnerResetting) := by
  unfold processAgent
  by_cases hmain : s.role = .Resetting ∧ s.resetcount = 0
  · rw [if_pos hmain]
    by_cases hold : 0 < oldRc
    · rw [if_pos hold]
      by_cases hfire :
          ({s with delaytimer := Dmax} : AgentState n).delaytimer = 0 ∨
            !partnerResetting
      · rw [if_pos hfire]
        exact resetOSSR_preserves_timer_bound (s := {s with delaytimer := Dmax}) hs
      · rw [if_neg hfire]
        exact hs
    · rw [if_neg hold]
      by_cases hfire :
          ({s with delaytimer := s.delaytimer - 1} : AgentState n).delaytimer = 0 ∨
            !partnerResetting
      · rw [if_pos hfire]
        exact resetOSSR_preserves_timer_bound
          (s := {s with delaytimer := s.delaytimer - 1}) hs
      · rw [if_neg hfire]
        exact hs
  · rw [if_neg hmain]
    exact hs

private theorem propagateReset_recruit_preserves_timer_bound
    {n Emax Dmax K : ℕ} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    PairTimerBounded K
      (if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
        (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
      else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
        ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
      else (a, b)) := by
  unfold PairTimerBounded
  split_ifs <;> simp_all [AgentTimerBounded]

private theorem propagateReset_sync_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    PairTimerBounded K
      (if a.role = .Resetting ∧ b.role = .Resetting then
        let newRc := max (a.resetcount - 1) (b.resetcount - 1)
        ({ a with resetcount := newRc }, { b with resetcount := newRc })
      else (a, b)) := by
  unfold PairTimerBounded
  split_ifs <;> simp_all [AgentTimerBounded]

private theorem propagateReset_preserves_timer_bound
    {n Emax Dmax K : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (propagateReset Emax Dmax hn a b).1 ∧
    AgentTimerBounded K (propagateReset Emax Dmax hn a b).2 := by
  unfold propagateReset
  let p₁ :=
    if a.role = .Resetting ∧ 0 < a.resetcount ∧ b.role ≠ .Resetting then
      (a, { b with role := .Resetting, resetcount := 0, delaytimer := Dmax })
    else if b.role = .Resetting ∧ 0 < b.resetcount ∧ a.role ≠ .Resetting then
      ({ a with role := .Resetting, resetcount := 0, delaytimer := Dmax }, b)
    else (a, b)
  have hp₁ : PairTimerBounded K p₁ := by
    simpa [p₁] using
      propagateReset_recruit_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) ha hb
  let oldRcA := p₁.1.resetcount
  let oldRcB := p₁.2.resetcount
  let p₂ :=
    if p₁.1.role = .Resetting ∧ p₁.2.role = .Resetting then
      let newRc := max (p₁.1.resetcount - 1) (p₁.2.resetcount - 1)
      ({ p₁.1 with resetcount := newRc }, { p₁.2 with resetcount := newRc })
    else p₁
  have hp₂ : PairTimerBounded K p₂ := by
    exact propagateReset_sync_preserves_timer_bound hp₁.1 hp₁.2
  simpa [p₁, oldRcA, oldRcB, p₂, PairTimerBounded] using
    And.intro
      (processAgent_preserves_timer_bound (Emax := Emax) (Dmax := Dmax) (hn := hn) hp₂.1)
      (processAgent_preserves_timer_bound (Emax := Emax) (Dmax := Dmax) (hn := hn) hp₂.2)

set_option maxHeartbeats 800000 in
private theorem rankDeltaOSSR_preserves_timer_bound
    {n Rmax Emax Dmax K : ℕ} {hn : 0 < n} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).1 ∧
    AgentTimerBounded K (rankDeltaOSSR Rmax Emax Dmax hn (a, b)).2 := by
  unfold rankDeltaOSSR
  by_cases hReset : a.role = .Resetting ∨ b.role = .Resetting
  · simp [hReset]
    have hpr :=
      propagateReset_preserves_timer_bound
        (Emax := Emax) (Dmax := Dmax) (hn := hn) ha hb
    split_ifs <;> simp_all [AgentTimerBounded]
  · simp [hReset]
    repeat' split_ifs <;> simp_all [AgentTimerBounded]

set_option maxHeartbeats 800000 in
private theorem transitionPEM_prePhase4_preserves_protocol_timer_bound
    {n trank K : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hK : 7 * (trank + 4) ≤ K)
    (hRankDelta :
      AgentTimerBounded K (rankDelta (s₀, s₁)).1 ∧
      AgentTimerBounded K (rankDelta (s₀, s₁)).2) :
    AgentTimerBounded K
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1 ∧
      AgentTimerBounded K
        (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2 := by
  unfold transitionPEM_prePhase4
  rcases hrd : rankDelta (s₀, s₁) with ⟨r₀, r₁⟩
  simp [hrd] at hRankDelta ⊢
  repeat' split_ifs <;> simp_all [AgentTimerBounded] <;> omega

private theorem phase4_swap_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (phase4_swap a b x₀ x₁).1 ∧
    AgentTimerBounded K (phase4_swap a b x₀ x₁).2 := by
  unfold phase4_swap
  split_ifs <;> simp_all [AgentTimerBounded]

private theorem phase4_decide_preserves_timer_bound
    {n K : ℕ} {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (phase4_decide n a b x₀ x₁).1 ∧
    AgentTimerBounded K (phase4_decide n a b x₀ x₁).2 := by
  unfold phase4_decide
  repeat' split_ifs <;> simp_all [AgentTimerBounded]

set_option maxHeartbeats 800000 in
private theorem phase4_propagate_preserves_timer_bound
    {n Rmax K : ℕ} {a b : AgentState n}
    (ha : AgentTimerBounded K a) (hb : AgentTimerBounded K b) :
    AgentTimerBounded K (phase4_propagate n Rmax a b).1 ∧
    AgentTimerBounded K (phase4_propagate n Rmax a b).2 := by
  unfold phase4_propagate
  by_cases haMed : a.rank.val + 1 = ceilHalf n
  · by_cases hbLast : b.rank.val + 1 = n
    · by_cases hReset :
        ({ a with timer := a.timer - 1 } : AgentState n).timer = 0 ∧
          ({ a with timer := a.timer - 1 } : AgentState n).answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentTimerBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, AgentTimerBounded] at * <;> omega
    · by_cases hReset : a.timer = 0 ∧ a.answer ≠ b.answer
      · simp [haMed, hbLast, hReset, AgentTimerBounded] at * <;> omega
      · simp [haMed, hbLast, hReset, AgentTimerBounded] at * <;> omega
  · by_cases hbMed : b.rank.val + 1 = ceilHalf n
    · by_cases haLast : a.rank.val + 1 = n
      · by_cases hReset :
          ({ b with timer := b.timer - 1 } : AgentState n).timer = 0 ∧
            ({ b with timer := b.timer - 1 } : AgentState n).answer ≠ a.answer
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentTimerBounded] at * <;>
            omega
        · have hn_ne_ceil : n ≠ ceilHalf n := by
            intro h
            exact haMed (by omega)
          simp [hn_ne_ceil, hbMed, haLast, hReset, AgentTimerBounded] at * <;>
            omega
      · by_cases hReset : b.timer = 0 ∧ b.answer ≠ a.answer
        · simp [haMed, hbMed, haLast, hReset, AgentTimerBounded] at * <;> omega
        · simp [haMed, hbMed, haLast, hReset, AgentTimerBounded] at * <;> omega
    · simp [haMed, hbMed, AgentTimerBounded] at * <;> omega

private theorem transitionPEM_phase4_preserves_timer_bound
    {n Rmax K : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (ha : AgentTimerBounded K a.1) (hb : AgentTimerBounded K a.2) :
    AgentTimerBounded K (transitionPEM_phase4 n Rmax a x₀ x₁).1 ∧
    AgentTimerBounded K (transitionPEM_phase4 n Rmax a x₀ x₁).2 := by
  by_cases hSettled : a.1.role = .Settled ∧ a.2.role = .Settled
  · let sw := phase4_swap a.1 a.2 x₀ x₁
    have hsw : AgentTimerBounded K sw.1 ∧ AgentTimerBounded K sw.2 :=
      phase4_swap_preserves_timer_bound (x₀ := x₀) (x₁ := x₁) ha hb
    let dec := phase4_decide n sw.1 sw.2 x₀ x₁
    have hdec : AgentTimerBounded K dec.1 ∧ AgentTimerBounded K dec.2 :=
      phase4_decide_preserves_timer_bound (x₀ := x₀) (x₁ := x₁) hsw.1 hsw.2
    have hprop :
        AgentTimerBounded K (phase4_propagate n Rmax dec.1 dec.2).1 ∧
        AgentTimerBounded K (phase4_propagate n Rmax dec.1 dec.2).2 :=
      phase4_propagate_preserves_timer_bound hdec.1 hdec.2
    simpa [transitionPEM_phase4, hSettled, sw, dec] using hprop
  · simpa [transitionPEM_phase4, hSettled] using And.intro ha hb

private theorem transitionPEM_preserves_protocol_timer_bound
    {n Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hs₀ : AgentTimerBounded (7 * (Rmax + 4)) s₀)
    (hs₁ : AgentTimerBounded (7 * (Rmax + 4)) s₁) :
      AgentTimerBounded (7 * (Rmax + 4))
          ((PEMProtocolCoupled n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).1 ∧
        AgentTimerBounded (7 * (Rmax + 4))
          ((PEMProtocolCoupled n Rmax Emax Dmax hn).δ ((s₀, x₀), (s₁, x₁))).2 := by
  have hrd :=
    rankDeltaOSSR_preserves_timer_bound (hn := hn)
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hs₀ hs₁
  have hpre :=
    transitionPEM_prePhase4_preserves_protocol_timer_bound
      (trank := Rmax) (K := 7 * (Rmax + 4))
      (x₀ := x₀) (x₁ := x₁) (by omega) hrd
  simpa [PEMProtocolCoupled, protocolPEM, transitionPEM] using
    transitionPEM_phase4_preserves_timer_bound
      (x₀ := x₀) (x₁ := x₁) hpre.1 hpre.2

theorem PEMProtocolCoupled_preserves_timer_bounded
    {n Rmax Emax Dmax : ℕ} (hn : 0 < n) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      ∀ i j : Fin n,
        IsTimerBoundedConfig (7 * (Rmax + 4))
          (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn) i j) := by
  intro C hC i j μ
  have hi : AgentTimerBounded (7 * (Rmax + 4)) (C i).1 := hC i
  have hj : AgentTimerBounded (7 * (Rmax + 4)) (C j).1 := hC j
  by_cases hij : i = j
  · subst j
    simpa [Config.step, AgentTimerBounded, IsTimerBoundedConfig] using hC μ
  · by_cases hμi : μ = i
    · subst μ
      have hpair :=
        transitionPEM_preserves_protocol_timer_bound
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2) hi hj
      simpa [Config.step, hij, AgentTimerBounded, IsTimerBoundedConfig]
        using hpair.1
    · by_cases hμj : μ = j
      · subst μ
        have hpair :=
          transitionPEM_preserves_protocol_timer_bound
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (hn := hn) (x₀ := (C i).2) (x₁ := (C j).2) hi hj
        simpa [Config.step, hij, hμi, AgentTimerBounded, IsTimerBoundedConfig]
          using hpair.2
      · simpa [Config.step, hij, hμi, hμj, AgentTimerBounded, IsTimerBoundedConfig]
          using hC μ

theorem PEMProtocolCoupled_consensus_probReached_eq_one
    {n Rmax Emax Dmax : ℕ} [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hC : IsConsensusConfig C) (t : ℕ) :
    Probability.probReached (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      IsConsensusConfig t = 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hfix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix
  have hstep : ∀ C' : Config (AgentState n) Opinion n,
      IsConsensusConfig C' → ∀ i j : Fin n,
        IsConsensusConfig (C'.step P i j) := by
    intro C' hC' i j
    simpa [P, PEMProtocolCoupled, PEMProtocol] using step_preserves_consensus hfix hC' i j
  simp only [Probability.probReached]
  have hsupport :=
    Probability.nthStepDist_support_inv P hn2 C IsConsensusConfig hC hstep t
  conv_lhs => arg 1; ext D; rw [show (if IsConsensusConfig D then
      (Probability.nthStepDist P hn2 C t) D else 0) =
      (Probability.nthStepDist P hn2 C t) D from by
        by_cases hD : IsConsensusConfig D
        · rw [if_pos hD]
        · have hDzero : (Probability.nthStepDist P hn2 C t) D = 0 :=
            (PMF.apply_eq_zero_iff _ _).mpr (fun h => hD (hsupport D h))
          rw [if_neg hD, hDzero]]
  exact PMF.tsum_coe _

theorem PEM_decision_phase_hypothesis_of_live_branch
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n)) :
      ∀ C : Config (AgentState n) Opinion n,
        InTswap28SswapTimerBounded (7 * (Rmax + 4)) C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
  classical
  intro C hC
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  rcases hC with ⟨hSwap, hTimer, hTimerUpper⟩ | hCon
  · by_cases hCon' : IsConsensusConfig C
    · calc ((8 : ENNReal)⁻¹) ≤ 1 := by norm_num
        _ = Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
              IsConsensusConfig (4 * n * n) :=
            (PEMProtocolCoupled_consensus_probReached_eq_one
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn2 hn0 hCon' (4 * n * n)).symm
        _ ≤ Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) :=
            Probability.probReached_mono_goal
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C IsConsensusConfig
              (InSdecTimerBounded (7 * (Rmax + 4))) (fun D hD => Or.inr hD) _
    · exact hLive C hSwap hTimer hTimerUpper hCon'
  · calc ((8 : ENNReal)⁻¹) ≤ 1 := by norm_num
      _ = Probability.probReached
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            IsConsensusConfig (4 * n * n) :=
          (PEMProtocolCoupled_consensus_probReached_eq_one
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn2 hn0 hCon (4 * n * n)).symm
      _ ≤ Probability.probReached
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) :=
          Probability.probReached_mono_goal
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C IsConsensusConfig
            (InSdecTimerBounded (7 * (Rmax + 4))) (fun D hD => Or.inr hD) _

theorem PEM_propagation_phase_hypothesis_of_live_branch
    {n Rmax Emax Dmax : ℕ}
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
      ∀ C : Config (AgentState n) Opinion n,
        InSdecTimerBounded (7 * (Rmax + 4)) C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n) := by
  classical
  intro C hC
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  rcases hC with ⟨hSwap, hAns, hTimer, hTimerUpper⟩ | hCon
  · by_cases hCon' : IsConsensusConfig C
    · calc ((1280 : ENNReal)⁻¹) ≤ 1 := by norm_num
        _ = Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
              IsConsensusConfig (20 * Rmax * n * n) :=
            (PEMProtocolCoupled_consensus_probReached_eq_one
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn2 hn0 hCon' (20 * Rmax * n * n)).symm
    · exact hLive C hSwap hAns hTimer hTimerUpper hCon'
  · calc ((1280 : ENNReal)⁻¹) ≤ 1 := by norm_num
      _ = Probability.probReached
            (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
            IsConsensusConfig (20 * Rmax * n * n) :=
          (PEMProtocolCoupled_consensus_probReached_eq_one
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn2 hn0 hCon (20 * Rmax * n * n)).symm

/-- Phase-B variable-descent expectation up to either completing the swap phase
or leaving `Srank`.  The exit branch is necessary because the coupled PEM
transition may trigger a reset from an arbitrary `InSrank` state; the pure
`InSswap` hitting statement needs a separate timer/no-reset hypothesis or a
restart through Phase A. -/
theorem PEM_swap_phase_expected_until_swap_or_exit_le_sum
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C) :
    Probability.expectedHittingTime
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D => InSswap D ∨ ¬ InSrank D) ≤
      ∑ k ∈ Finset.range (wrongLowBCount C),
        ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∨ ¬ InSrank D
  let pRate : ℕ → ENNReal := fun k =>
    (((k * k : ℕ) : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  have hRankFix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0)
  have hZeroGoal : ∀ D : Config (AgentState n) Opinion n,
      InSrank D → wrongLowBCount D = 0 → Goal D := by
    intro D hD hzero
    exact Or.inl (InSswap_of_InSrank_of_wrongLowBCount_zero hD hzero)
  have hInvStep : ∀ D : Config (AgentState n) Opinion n, InSrank D → ¬ Goal D →
      ∀ i j : Fin n, InSrank (D.step P i j) ∨ Goal (D.step P i j) := by
    intro D _hD _hGoalD i j
    by_cases h' : InSrank (D.step P i j)
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
  have hNonincrease : ∀ D : Config (AgentState n) Opinion n, InSrank D → ¬ Goal D →
      ∀ i j : Fin n, wrongLowBCount (D.step P i j) ≤ wrongLowBCount D := by
    intro D hD _hGoalD i j
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      (wrongLowBCount_step_le_of_InSrank
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
        hRankFix hD i j)
  have hp : ∀ k : ℕ, 0 < k →
      ∀ D : Config (AgentState n) Opinion n, InSrank D → wrongLowBCount D = k →
        pRate k ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => Goal E ∨ (InSrank E ∧ wrongLowBCount E < k)) 1 := by
    intro k hk D hD hφ
    have hrate_le :
        pRate k ≤
          (((wrongLowBCount D * wrongLowBCount D : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
      dsimp [pRate]
      rw [← hφ]
    have hdescent :
        (((wrongLowBCount D * wrongLowBCount D : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 D
            (fun E => wrongLowBCount E < wrongLowBCount D) 1 := by
      simpa [P] using
        (PEM_swap_phase_wrongLowB_square_descent_prob_lower_bound
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn2 hn0 hD)
    refine hrate_le.trans (hdescent.trans ?_)
    apply Probability.ProbHitWithin_mono_goal P hn2 D
    intro E hlt
    by_cases hE : InSrank E
    · exact Or.inr ⟨hE, by simpa [hφ] using hlt⟩
    · exact Or.inl (Or.inr hE)
  simpa [P, Goal, pRate] using
    (Probability.expectedHittingTime_le_of_variable_descent_until_goal
      P hn2 C Goal InSrank wrongLowBCount pRate hSrank
      hZeroGoal hInvStep hNonincrease hp)

/-! ### Ranking-phase stochastic bridge -/

/-- One binary-tree recruit step has at least the scheduler mass of one
ordered pair.

This is the stochastic wrapper around the deterministic
`heapPrefix_recruit_step_with_child_BCF`: while the ranking heap prefix is at
level `k < n`, an unsettled child and its heap parent form a concrete ordered
pair whose interaction advances the prefix to `k + 1`, preserving the median
timer side conditions needed by the later swap phase. -/
theorem PEM_heapPrefix_recruit_step_ProbHitWithin
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
        (k + 1 < n → SettledMedianTimerStrong D)
  by_cases hGoalC : Goal C
  · have hp_le_one :
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := by
      exact ENNReal.inv_le_one.mpr (by
        have hn_one : 1 ≤ n := by omega
        have hpred_one : 1 ≤ n - 1 := by omega
        exact_mod_cast (Nat.mul_le_mul hn_one hpred_one))
    calc
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := hp_le_one
      _ = Probability.ProbHitWithin P hn2 C Goal 0 := by
        rw [Probability.ProbHitWithin, Probability.probHitBy_zero_of_goal P hn2 C Goal hGoalC]
      _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 :=
        Probability.ProbHitWithin_mono_time P hn2 C Goal (by omega)
  · have hExistsUnsettled : ∃ u : Fin n, (C u).1.role = .Unsettled := by
      by_contra hnone
      push_neg at hnone
      have hall : ∀ w : Fin n, (C w).1.role = .Settled := by
        intro w
        rcases hHeap.2.2.2.1 w with hwS | hwU
        · exact hwS
        · exact False.elim (hnone w hwU)
      exact heapPrefix_no_unsettled_contradiction hk_lt hHeap hall
    obtain ⟨u, hu_unsettled⟩ := hExistsUnsettled
    obtain ⟨parent, hparent_settled, _hparent_children, _hvalid, _hrank,
        hstep⟩ :=
      heapPrefix_recruit_step_with_child_BCF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
        hk_pos hk_lt C hHeap hTimer u hu_unsettled
    have hup : u ≠ parent := by
      intro h
      subst u
      rw [hparent_settled] at hu_unsettled
      cases hu_unsettled
    have hstepGoal : Goal (C.step P u parent) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol, Goal, runPairs] using hstep
    simpa [P, Goal] using
      (Probability.ProbHitWithin_one_lower_bound_of_step
        (P := P) hn2 C Goal hGoalC hup hstepGoal)

/-- All unsettled agents in a heap-prefix configuration contribute distinct
successful recruit ordered pairs.

This is the rate form needed for the ranking expected-time bound: at heap
level `k`, every unsettled agent can be recruited by the unique heap parent of
rank `heapParent k`, so the one-step success probability is at least
`unsettledCount / (n(n-1))`. -/
theorem PEM_heapPrefix_recruit_step_mass_ProbHitWithin
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    ((unsettledCount C : ℕ) : ENNReal) *
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) 1 := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
        (k + 1 < n → SettledMedianTimerStrong D)
  by_cases hGoalC : Goal C
  · have hU_le_n : unsettledCount C ≤ n := by
      unfold unsettledCount
      calc
        (Finset.univ.filter fun w : Fin n => (C w).1.role == .Unsettled).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := by simp
    have hden_le : n ≤ n * (n - 1) := by
      have hpred_one : 1 ≤ n - 1 := by omega
      calc
        n = n * 1 := by omega
        _ ≤ n * (n - 1) := Nat.mul_le_mul_left n hpred_one
    have hmass_le_one :
        ((unsettledCount C : ℕ) : ENNReal) *
            (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := by
      calc
        ((unsettledCount C : ℕ) : ENNReal) *
            (((n * (n - 1) : ℕ) : ENNReal)⁻¹)
            ≤ ((n : ℕ) : ENNReal) *
                (((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
              gcongr
        _ ≤ ((n * (n - 1) : ℕ) : ENNReal) *
                (((n * (n - 1) : ℕ) : ENNReal)⁻¹) := by
              gcongr
        _ ≤ 1 := by
              exact ENNReal.mul_inv_le_one ((n * (n - 1) : ℕ) : ENNReal)
    calc
      ((unsettledCount C : ℕ) : ENNReal) *
          (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := hmass_le_one
      _ = Probability.ProbHitWithin P hn2 C Goal 0 := by
        rw [Probability.ProbHitWithin, Probability.probHitBy_zero_of_goal P hn2 C Goal hGoalC]
      _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 :=
        Probability.ProbHitWithin_mono_time P hn2 C Goal (by omega)
  · let parentOf : Fin n → Fin n := fun u =>
      if hu : (C u).1.role = .Unsettled then
        Classical.choose
          (heapPrefix_recruit_step_with_child_BCF
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
            hk_pos hk_lt C hHeap hTimer u hu)
      else u
    have parentOf_spec : ∀ u : Fin n, (C u).1.role = .Unsettled →
        (C (parentOf u)).1.role = .Settled ∧
        (C (parentOf u)).1.children < 2 ∧
        2 * (C (parentOf u)).1.rank.val +
            (C (parentOf u)).1.children + 1 < n ∧
        2 * (C (parentOf u)).1.rank.val +
            (C (parentOf u)).1.children + 1 = k ∧
        (let C' := runPairs (protocolPEM n Rmax Rmax
          (rankDeltaOSSR Rmax Emax Dmax hn0)) C [(u, parentOf u)]
         HeapPrefix C' (k + 1) ∧ SettledMedianTimerGood C' ∧
          (k + 1 < n → SettledMedianTimerStrong C')) := by
      intro u hu
      dsimp [parentOf]
      rw [dif_pos hu]
      exact Classical.choose_spec
        (heapPrefix_recruit_step_with_child_BCF
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0)
          hk_pos hk_lt C hHeap hTimer u hu)
    let U : Finset (Fin n) :=
      Finset.univ.filter fun u : Fin n => (C u).1.role == .Unsettled
    let S : Finset (Fin n × Fin n) := U.image fun u => (u, parentOf u)
    have hU_card : U.card = unsettledCount C := by
      rfl
    have hS_card : S.card = unsettledCount C := by
      dsimp [S]
      rw [Finset.card_image_of_injective]
      · exact hU_card
      · intro a b h
        exact congrArg Prod.fst h
    have hS_sub : S ⊆ Probability.OffDiagonalPairs n := by
      intro p hp
      dsimp [S] at hp
      obtain ⟨u, huU, rfl⟩ := Finset.mem_image.mp hp
      have hu_role : (C u).1.role = .Unsettled := by
        have hbool := (Finset.mem_filter.mp huU).2
        simpa using hbool
      have hspec := parentOf_spec u hu_role
      have hup : u ≠ parentOf u := by
        intro h
        rw [h] at hu_role
        rw [hspec.1] at hu_role
        cases hu_role
      exact (Probability.mem_offDiagonalPairs n (u, parentOf u)).mpr hup
    have hS_step : ∀ p ∈ S, Goal (C.step P p.1 p.2) := by
      intro p hp
      dsimp [S] at hp
      obtain ⟨u, huU, rfl⟩ := Finset.mem_image.mp hp
      have hu_role : (C u).1.role = .Unsettled := by
        have hbool := (Finset.mem_filter.mp huU).2
        simpa using hbool
      have hspec := parentOf_spec u hu_role
      have hstep := hspec.2.2.2.2
      simpa [P, PEMProtocolCoupled, PEMProtocol, Goal, runPairs] using hstep
    calc
      ((unsettledCount C : ℕ) : ENNReal) *
          (((n * (n - 1) : ℕ) : ENNReal)⁻¹)
          = Probability.pairSetMass n hn2 S := by
            rw [Probability.pairSetMass_eq_card_mul_inv_of_subset n hn2 S hS_sub]
            rw [hS_card]
      _ ≤ Probability.ProbHitWithin P hn2 C Goal 1 :=
        Probability.ProbHitWithin_one_lower_bound_of_pairSet
          P hn2 C Goal hGoalC S hS_sub hS_step

/-- In a `HeapPrefix C k` state, exactly the first `k` ranks are occupied by
settled agents and all remaining agents are unsettled.  This is the counting
bridge that turns the mass recruit bound into a level-dependent rate. -/
theorem HeapPrefix.unsettledCount_add_eq_n
    {n : ℕ} {C : Config (AgentState n) Opinion n} {k : ℕ}
    (hHeap : HeapPrefix C k) :
    k + unsettledCount C = n := by
  classical
  rcases hHeap with ⟨hk_le, hRankLt, hRankUnique, hRoles, _hChildren⟩
  let S : Finset (Fin n) :=
    Finset.univ.filter fun w : Fin n => (C w).1.role = .Settled
  let U : Finset (Fin n) :=
    Finset.univ.filter fun w : Fin n => (C w).1.role == .Unsettled
  have hSettledCard : S.card = k := by
    let rankOnSettled : {w : Fin n // w ∈ S} → Fin k := fun w =>
      ⟨(C w.1).1.rank.val, by
        have hw_settled : (C w.1).1.role = .Settled := by
          exact (Finset.mem_filter.mp w.2).2
        exact hRankLt w.1 hw_settled⟩
    have hBij : Function.Bijective rankOnSettled := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        obtain ⟨z, _hz, hz_unique⟩ :=
          hRankUnique (rankOnSettled x).val (rankOnSettled x).isLt
        have hxz : x.1 = z := by
          apply hz_unique
          constructor
          · exact (Finset.mem_filter.mp x.2).2
          · rfl
        have hyz : y.1 = z := by
          apply hz_unique
          constructor
          · exact (Finset.mem_filter.mp y.2).2
          · exact congrArg Fin.val hxy |>.symm
        exact hxz.trans hyz.symm
      · intro r
        obtain ⟨w, hw, _hw_unique⟩ := hRankUnique r.val r.isLt
        have hwS : w ∈ S := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw.1⟩
        exact ⟨⟨w, hwS⟩, Fin.ext hw.2⟩
    have hCardSubtype :
        Fintype.card {w : Fin n // w ∈ S} = Fintype.card (Fin k) :=
      Fintype.card_congr (Equiv.ofBijective rankOnSettled hBij)
    have hSubtypeCard : Fintype.card {w : Fin n // w ∈ S} = S.card :=
      Fintype.card_of_subtype S (fun _ => Iff.rfl)
    rw [← hSubtypeCard, hCardSubtype]
    simp
  have hUCard : U.card = unsettledCount C := by
    rfl
  have hDisjoint : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro w hwS hwU
    have hSrole : (C w).1.role = .Settled := (Finset.mem_filter.mp hwS).2
    have hUrole : (C w).1.role = .Unsettled := by
      simpa using (Finset.mem_filter.mp hwU).2
    rw [hSrole] at hUrole
    cases hUrole
  have hUnion : S ∪ U = (Finset.univ : Finset (Fin n)) := by
    ext w
    constructor
    · intro _hw
      exact Finset.mem_univ w
    · intro _hw
      rcases hRoles w with hSettled | hUnsettled
      · exact Finset.mem_union_left U
          (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hSettled⟩)
      · exact Finset.mem_union_right S
          (Finset.mem_filter.mpr ⟨Finset.mem_univ w, by simpa [hUnsettled]⟩)
  have htotal : n = S.card + U.card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ = (S ∪ U).card := by rw [hUnion]
      _ = S.card + U.card := Finset.card_union_of_disjoint hDisjoint
  omega

/-- Level-rate form of the heap-prefix recruit bound.  At prefix level `k`,
there are exactly `n-k` unsettled agents, hence that many successful recruit
edges. -/
theorem PEM_heapPrefix_recruit_step_level_ProbHitWithin
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    (((n - k : ℕ) : ENNReal) *
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹)) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) 1 := by
  classical
  have hcount : unsettledCount C = n - k := by
    have hsum := HeapPrefix.unsettledCount_add_eq_n (C := C) (k := k) hHeap
    omega
  simpa [hcount] using
    (PEM_heapPrefix_recruit_step_mass_ProbHitWithin
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 hk_pos hk_lt C hHeap hTimer)

/-- Expected time to advance one heap-prefix level or leave the level,
using the full mass of all unsettled recruitable agents. -/
theorem PEM_heapPrefix_recruit_step_or_exit_expected_le_level
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) ∨
          ¬ (HeapPrefix D k ∧ SettledMedianTimerStrong D)) ≤
      ((((n - k : ℕ) : ENNReal) *
          (((n * (n - 1) : ℕ) : ENNReal)⁻¹))⁻¹) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Region : Config (AgentState n) Opinion n → Prop :=
    fun D => HeapPrefix D k ∧ SettledMedianTimerStrong D
  let Next : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
        (k + 1 < n → SettledMedianTimerStrong D)
  have hRegion : Region C := ⟨hHeap, hTimer⟩
  by_cases hNextC : Next C
  · rw [Probability.expectedHittingTime_eq_zero_of_goal
        P hn2 C (fun D => Next D ∨ ¬ Region D) (Or.inl hNextC)]
    exact zero_le
  · apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
      (P := P) (hn := hn2) (C₀ := C)
      (Region := Region) (Goal := Next)
      (p := (((n - k : ℕ) : ENNReal) *
        (((n * (n - 1) : ℕ) : ENNReal)⁻¹)))
    · exact hRegion
    · exact hNextC
    · intro D hRegionD _hNextD
      have hbase :
          (((n - k : ℕ) : ENNReal) *
              (((n * (n - 1) : ℕ) : ENNReal)⁻¹)) ≤
            Probability.ProbHitWithin P hn2 D Next 1 := by
        simpa [P, Next] using
          (PEM_heapPrefix_recruit_step_level_ProbHitWithin
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn2 hn0 hk_pos hk_lt D hRegionD.1 hRegionD.2)
      exact hbase.trans
        (Probability.ProbHitWithin_mono_goal P hn2 D Next
          (fun E => Next E ∨ ¬ Region E) (fun E hE => Or.inl hE) 1)

/-- Expected time to either advance one heap-prefix level or leave the current
heap-prefix region.

The exit disjunct is deliberate: arbitrary scheduler interactions can touch
unsettled agents and error counters, so the honest local statement does not
pretend the heap-prefix invariant is globally preserved.  The theorem says
that while the current heap-prefix state is live, one concrete recruit pair
gives a geometric `n(n-1)` sequential-time bound for either making the intended
advance or detecting that the region has been left. -/
theorem PEM_heapPrefix_recruit_step_or_exit_expected_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        (HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
            (k + 1 < n → SettledMedianTimerStrong D)) ∨
          ¬ (HeapPrefix D k ∧ SettledMedianTimerStrong D)) ≤
      ((n * (n - 1) : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Region : Config (AgentState n) Opinion n → Prop :=
    fun D => HeapPrefix D k ∧ SettledMedianTimerStrong D
  let Next : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      HeapPrefix D (k + 1) ∧ SettledMedianTimerGood D ∧
        (k + 1 < n → SettledMedianTimerStrong D)
  have hRegion : Region C := ⟨hHeap, hTimer⟩
  by_cases hNextC : Next C
  · rw [Probability.expectedHittingTime_eq_zero_of_goal
        P hn2 C (fun D => Next D ∨ ¬ Region D) (Or.inl hNextC)]
    exact zero_le
  · have hraw :
        Probability.expectedHittingTime P hn2 C
          (fun D => Next D ∨ ¬ Region D) ≤
        ((((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) := by
      apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
        (P := P) (hn := hn2) (C₀ := C)
        (Region := Region) (Goal := Next)
        (p := (((n * (n - 1) : ℕ) : ENNReal)⁻¹))
      · exact hRegion
      · exact hNextC
      · intro D hRegionD hNextD
        have hbase :
            (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
              Probability.ProbHitWithin P hn2 D Next 1 := by
          simpa [P, Next] using
            (PEM_heapPrefix_recruit_step_ProbHitWithin
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
              hn2 hn0 hk_pos hk_lt D hRegionD.1 hRegionD.2)
        exact hbase.trans
          (Probability.ProbHitWithin_mono_goal P hn2 D Next
            (fun E => Next E ∨ ¬ Region E) (fun E hE => Or.inl hE) 1)
    change
      Probability.expectedHittingTime P hn2 C
        (fun D => Next D ∨ ¬ Region D) ≤
        ((n * (n - 1) : ℕ) : ENNReal)
    calc
      Probability.expectedHittingTime P hn2 C
          (fun D => Next D ∨ ¬ Region D)
          ≤ ((((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) := hraw
      _ = ((n * (n - 1) : ℕ) : ENNReal) := by
        rw [inv_inv]

/-- Multi-level heap-prefix ranking estimate, with an explicit exit target.

Starting at prefix level `j`, the process reaches `RankingEndpoint` or leaves one of
the heap-prefix/strong-timer regions at levels `k₀, …, n-1` in at most
`(n-j) * n(n-1)` expected sequential steps.  This is the honest stochastic
version of the deterministic binary-tree recruit loop: the exit disjunct
records arbitrary scheduler interactions that break the recruit-loop invariant
and must be handled by the outer restart/rerank analysis. -/
theorem PEM_heapPrefix_expected_until_rankingEndpoint_or_exit_from_level_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    {k₀ j : ℕ} (hk₀j : k₀ ≤ j) (hj_pos : 1 ≤ j) (hj_le : j ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C j) (hTimer : SettledMedianTimerStrong C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
      (fun D =>
        RankingEndpoint D ∨
          ∃ ℓ : ℕ, k₀ ≤ ℓ ∧ ℓ < n ∧
            ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)) ≤
      (((n - j) * (n * (n - 1)) : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let G : Config (AgentState n) Opinion n → Prop := fun D =>
    RankingEndpoint D ∨
      ∃ ℓ : ℕ, k₀ ≤ ℓ ∧ ℓ < n ∧
        ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)
  let den : ℕ := n * (n - 1)
  have hAll :
      ∀ fuel : ℕ, ∀ j : ℕ, ∀ C : Config (AgentState n) Opinion n,
        n - j ≤ fuel → k₀ ≤ j → 1 ≤ j → j ≤ n →
        HeapPrefix C j → SettledMedianTimerStrong C →
        Probability.expectedHittingTime P hn2 C G ≤
          (((n - j) * den : ℕ) : ENNReal) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
        intro j C hfuel hk₀j hj_pos hj_le hHeap hTimer
        by_cases hG_C : G C
        · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 C G hG_C]
          exact zero_le
        · by_cases hj_eq : j = n
          · subst j
            have hEndpoint : RankingEndpoint C :=
              HeapPrefix.to_RankingEndpoint hHeap
                (SettledMedianTimerStrong.toGood hTimer)
            exact False.elim (hG_C (Or.inl hEndpoint))
          · have hj_lt : j < n := by omega
            let Next : Config (AgentState n) Opinion n → Prop := fun D =>
              HeapPrefix D (j + 1) ∧ SettledMedianTimerGood D ∧
                (j + 1 < n → SettledMedianTimerStrong D)
            let GoalLocal : Config (AgentState n) Opinion n → Prop := fun D =>
              Next D ∨ G D
            let Region : Config (AgentState n) Opinion n → Prop := fun D =>
              HeapPrefix D j ∧ SettledMedianTimerStrong D
            let Mid : Config (AgentState n) Opinion n → Prop := fun D =>
              GoalLocal D ∨ ¬ Region D
            have hRegionC : Region C := ⟨hHeap, hTimer⟩
            by_cases hNextC : Next C
            · have hBelow : Probability.expectedHittingTime P hn2 C G ≤
                  (((n - (j + 1)) * den : ℕ) : ENNReal) := by
                by_cases hlast : j + 1 = n
                · have hSrank : InSrank C := by
                    exact HeapPrefix.to_InSrank
                      (by simpa [Next, hlast] using hNextC.1)
                  have hEndpoint : RankingEndpoint C :=
                    HeapPrefix.to_RankingEndpoint
                      (by simpa [Next, hlast] using hNextC.1)
                      (by simpa [Next] using hNextC.2.1)
                  rw [Probability.expectedHittingTime_eq_zero_of_goal
                    P hn2 C G (Or.inl hEndpoint)]
                  exact zero_le
                · have hj_next_lt : j + 1 < n := by omega
                  exact ih (n - (j + 1)) (by omega) (j + 1) C
                    (by omega) (by omega) (by omega) (by omega)
                    hNextC.1 (hNextC.2.2 hj_next_lt)
              exact hBelow.trans (by
                have hle : n - (j + 1) ≤ n - j := by omega
                exact_mod_cast Nat.mul_le_mul_right den hle)
            · have hToMid : Probability.expectedHittingTime P hn2 C Mid ≤
                  ((den : ENNReal)) := by
                have hraw :
                    Probability.expectedHittingTime P hn2 C Mid ≤
                      ((((den : ℕ) : ENNReal)⁻¹)⁻¹) := by
                  apply Probability.expectedHittingTime_le_inv_of_local_one_lower_bound
                    (P := P) (hn := hn2) (C₀ := C)
                    (Region := Region) (Goal := GoalLocal)
                    (p := (((den : ℕ) : ENNReal)⁻¹))
                  · exact hRegionC
                  · intro hGoalLocal
                    rcases hGoalLocal with hNext | hG
                    · exact hNextC hNext
                    · exact hG_C hG
                  · intro D hRegionD _hGoalLocalD
                    have hbase :
                        (((den : ℕ) : ENNReal)⁻¹) ≤
                          Probability.ProbHitWithin P hn2 D Next 1 := by
                      simpa [P, Next, den] using
                        (PEM_heapPrefix_recruit_step_ProbHitWithin
                          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
                          hn2 hn0 hj_pos hj_lt D hRegionD.1 hRegionD.2)
                    have hmono₁ :
                        Probability.ProbHitWithin P hn2 D Next 1 ≤
                          Probability.ProbHitWithin P hn2 D GoalLocal 1 :=
                      Probability.ProbHitWithin_mono_goal P hn2 D Next GoalLocal
                        (fun E hE => Or.inl hE) 1
                    have hmono₂ :
                        Probability.ProbHitWithin P hn2 D GoalLocal 1 ≤
                          Probability.ProbHitWithin P hn2 D Mid 1 :=
                      Probability.ProbHitWithin_mono_goal P hn2 D GoalLocal Mid
                        (fun E hE => Or.inl hE) 1
                    exact hbase.trans (hmono₁.trans hmono₂)
                calc
                  Probability.expectedHittingTime P hn2 C Mid
                      ≤ ((((den : ℕ) : ENNReal)⁻¹)⁻¹) := hraw
                  _ = (den : ENNReal) := by rw [inv_inv]
              have hFromMid : ∀ D : Config (AgentState n) Opinion n, Mid D →
                  Probability.expectedHittingTime P hn2 D G ≤
                    (((n - (j + 1)) * den : ℕ) : ENNReal) := by
                intro D hD
                rcases hD with hGoalLocal | hExit
                · rcases hGoalLocal with hNext | hG
                  · by_cases hlast : j + 1 = n
                    · have hEndpoint : RankingEndpoint D :=
                        HeapPrefix.to_RankingEndpoint
                          (by simpa [Next, hlast] using hNext.1)
                          (by simpa [Next] using hNext.2.1)
                      rw [Probability.expectedHittingTime_eq_zero_of_goal
                        P hn2 D G (Or.inl hEndpoint)]
                      exact zero_le
                    · have hj_next_lt : j + 1 < n := by omega
                      exact ih (n - (j + 1)) (by omega) (j + 1) D
                        (by omega) (by omega) (by omega) (by omega)
                        hNext.1 (hNext.2.2 hj_next_lt)
                  · rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D G hG]
                    exact zero_le
                · have hG : G D := Or.inr ⟨j, hk₀j, hj_lt, hExit⟩
                  rw [Probability.expectedHittingTime_eq_zero_of_goal P hn2 D G hG]
                  exact zero_le
              have hComp :
                  Probability.expectedHittingTime P hn2 C G ≤
                    (den : ENNReal) + (((n - (j + 1)) * den : ℕ) : ENNReal) :=
                Probability.expectedHittingTime_add_le P hn2 C Mid G
                  (den : ENNReal)
                  (((n - (j + 1)) * den : ℕ) : ENNReal)
                  hToMid hFromMid
                  (by intro D hD; exact Or.inl (Or.inr hD))
              calc
                Probability.expectedHittingTime P hn2 C G
                    ≤ (den : ENNReal) +
                      (((n - (j + 1)) * den : ℕ) : ENNReal) := hComp
                _ = (((n - j) * den : ℕ) : ENNReal) := by
                  have hnj : n - j = (n - (j + 1)) + 1 := by omega
                  rw [hnj]
                  have hnat :
                      den + (n - (j + 1)) * den =
                        ((n - (j + 1)) + 1) * den := by
                    rw [Nat.add_mul, Nat.one_mul, add_comm]
                  rw [← Nat.cast_add, hnat]
  simpa [P, G, den] using
    hAll (n - j) j C (by omega) hk₀j hj_pos hj_le hHeap hTimer

/-- Fresh-ranking-start corollary of the heap-prefix stochastic recruit loop.

This is the ranking subphase that starts once the deterministic reset/dormant
normalizer has produced a `FreshRankingStart`.  It reaches `RankingEndpoint`, or else
explicitly records that some heap-prefix/strong-timer level was left. -/
theorem PEM_FreshRankingStart_expected_until_rankingEndpoint_or_heap_exit_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hFresh : FreshRankingStart C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D =>
        RankingEndpoint D ∨
          ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
            ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)) ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hHeap : HeapPrefix C 1 := FreshRankingStart.to_heapPrefix_one hFresh
  have hTimer : SettledMedianTimerStrong C :=
    FreshRankingStart.to_timerStrong hn4 hFresh
  have hbase :
      Probability.expectedHittingTime
        (PEMProtocolCoupled n Rmax Emax Dmax hn0) hn2 C
        (fun D =>
          RankingEndpoint D ∨
            ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
              ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)) ≤
        (((n - 1) * (n * (n - 1)) : ℕ) : ENNReal) := by
    simpa using
      (PEM_heapPrefix_expected_until_rankingEndpoint_or_exit_from_level_le
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn2 hn0 (k₀ := 1) (j := 1)
        (by omega) (by omega) (by omega) C hHeap hTimer)
  have hnat :
      (n - 1) * (n * (n - 1)) ≤ Rmax * n * n := by
    have hnm1_le_n : n - 1 ≤ n := Nat.sub_le n 1
    have hnm1_le_Rmax : n - 1 ≤ Rmax := hnm1_le_n.trans hRmax
    calc
      (n - 1) * (n * (n - 1))
          ≤ n * (n * (n - 1)) := by
            exact Nat.mul_le_mul_right (n * (n - 1)) hnm1_le_n
      _ ≤ n * (n * Rmax) := by
            exact Nat.mul_le_mul_left n (Nat.mul_le_mul_left n hnm1_le_Rmax)
      _ = Rmax * n * n := by ac_rfl
  exact hbase.trans (by exact_mod_cast hnat)

/-- Fresh-ranking-start bound with the ranking endpoint expanded into the
phase target shape consumed by the probabilistic composition layer.  The
heap-exit disjunct is still explicit; closing the full ranking phase requires
the outer restart/normalizer argument to discharge that branch. -/
theorem PEM_FreshRankingStart_expected_until_srank_timer2_or_consensus_or_heap_exit_le
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hFresh : FreshRankingStart C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D =>
        ((InSrank D ∧ MedianTimerAtLeast 2 D) ∨ IsConsensusConfig D) ∨
          ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
            ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)) ≤
      ((Rmax * n * n : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let OldTarget : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      RankingEndpoint D ∨
        ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
          ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)
  let NewTarget : Config (AgentState n) Opinion n → Prop :=
    fun D =>
      ((InSrank D ∧ MedianTimerAtLeast 2 D) ∨ IsConsensusConfig D) ∨
        ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
          ¬ (HeapPrefix D ℓ ∧ SettledMedianTimerStrong D)
  have hOld :
      Probability.expectedHittingTime P (by omega : 2 ≤ n) C OldTarget ≤
        ((Rmax * n * n : ℕ) : ENNReal) := by
    simpa [P, OldTarget] using
      (PEM_FreshRankingStart_expected_until_rankingEndpoint_or_heap_exit_le
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax C hFresh)
  have hMono :
      Probability.expectedHittingTime P (by omega : 2 ≤ n) C NewTarget ≤
        Probability.expectedHittingTime P (by omega : 2 ≤ n) C OldTarget := by
    apply Probability.expectedHittingTime_mono_goal
    intro D hOldD
    rcases hOldD with hEndpoint | hExit
    · exact Or.inl (RankingEndpoint.to_InSrank_and_timerAtLeast_two_or_consensus hEndpoint)
    · exact Or.inr hExit
  exact hMono.trans hOld

/-! ### Conditional phase probability interface

The original Table-2 `probReached` standalone lemmas are intentionally not
asserted here.  The robust composition path in this file is the
`ProbHitWithin` chain below; exact-time `probReached` phase statements are
kept as explicit hypotheses in the legacy composition wrappers. -/

/-! ### Full Table-2 composition and expected time -/

/-- This is not the full Table-2 proof: it composes four explicit phase
probability hypotheses.  The key design is that the window is applied only
inside the protocol timer invariant.  This matches the paper's phase
analysis: Lemma 10 needs the median timer to be bounded by its protocol
initialization value `7 * (Rmax + 4)`, not merely positive. -/
theorem PEM_consensus_window_success_prob_from_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * Rmax * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  have hDecisionPhase :
      ∀ C : Config (AgentState n) Opinion n,
        InTswap28SswapTimerBounded (7 * (Rmax + 4)) C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached P hn2 C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
    intro C hC
    simpa [P] using
      (PEM_decision_phase_hypothesis_of_live_branch
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hDecisionLive C hC)
  have hPropagationPhase :
      ∀ C : Config (AgentState n) Opinion n,
        InSdecTimerBounded (7 * (Rmax + 4)) C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached P hn2 C IsConsensusConfig (20 * Rmax * n * n) := by
    intro C hC
    simpa [P] using
      (PEM_propagation_phase_hypothesis_of_live_branch
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hPropagationLive C hC)
  refine ⟨24, by omega, fun C hTimerBd hNotCon => ?_⟩
  have htotal : (((2 * Rmax * n * n + 4 * n * n) +
      4 * n * n) + 20 * Rmax * n * n) + 0 = (22 * Rmax + 8) * n * n := by ring
  have hle_window : (22 * Rmax + 8) * n * n ≤ 24 * Rmax * n * n := by
    have hle_factor : 22 * Rmax + 8 ≤ 24 * Rmax := by
      have hR4 : 4 ≤ Rmax := by omega
      omega
    exact Nat.mul_le_mul_right n (Nat.mul_le_mul_right n hle_factor)
  rw [show 24 * Rmax * n * n = 24 * Rmax * n * n from rfl]
  apply le_trans _ (Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig hle_window)
  rw [← htotal]
  have phase1_ranking :
      ((10 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C InSrank (2 * Rmax * n * n) := by
    simpa [P] using hRankPhase C hTimerBd hNotCon
  have phase2_swap : ∀ C' : Config (AgentState n) Opinion n, InSrank C' →
      ((20 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C'
          (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
    intro C' hC'
    simpa [P] using hSwapPhase C' hC'
  have phase3_decision : ∀ C' : Config (AgentState n) Opinion n,
      InTswap28SswapTimerBounded (7 * (Rmax + 4)) C' →
      ((8 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C'
          (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n) := by
    intro C' hC'
    simpa [P] using hDecisionPhase C' hC'
  have phase4_propagation : ∀ C' : Config (AgentState n) Opinion n,
      InSdecTimerBounded (7 * (Rmax + 4)) C' →
      ((1280 : ENNReal)⁻¹) ≤
        Probability.probReached P hn2 C' IsConsensusConfig (20 * Rmax * n * n) := by
    intro C' hC'
    simpa [P] using hPropagationPhase C' hC'
  exact pem_table2_phase_window_to_ProbHitWithin P hn2 C
    (SrankPhase := InSrank)
    (SswapPhase := InTswap28SswapTimerBounded (7 * (Rmax + 4)))
    (SdecPhase := InSdecTimerBounded (7 * (Rmax + 4)))
    (StimPhase := IsConsensusConfig)
    (SemPhase := IsConsensusConfig)
    (2 * Rmax * n * n) (4 * n * n)
    (4 * n * n) (20 * Rmax * n * n) 0
    phase1_ranking phase2_swap phase3_decision phase4_propagation
    (fun C' hC' => by
      rw [Probability.probReached_zero_of_goal P hn2 C' IsConsensusConfig hC']
      norm_num)

/-- Concrete Table-2 window bound from the four legacy exact-time phase
hypotheses.  This wrapper is conditional: the file's unconditional composition
path is the `ProbHitWithin` chain below. -/
theorem PEM_consensus_window_success_prob_of_phase_hypotheses
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * Rmax * n * n) := by
  exact PEM_consensus_window_success_prob_from_phase_bounds
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn4 hRmax hEmax hDmax hRankPhase hSwapPhase hDecisionLive
    hPropagationLive

/-! ### Non-vacuous time bound (corrected statement)

The above `PEM_expected_parallel_time_linear_param` has a vacuously false
hypothesis (`hTimerConst` quantifies over ALL `InSswap` configs, but
`AgentState.timer : ℕ` is unbounded).  The theorem is technically proved
but says nothing about actual time complexity.

For this coupled wrapper, the correct statement makes the time bound depend
on `Rmax` because it is also used as the timer parameter.  This gives
`O(Rmax · n)` expected parallel time.  For externally bounded `Rmax`, this
is `O(n)`; for `Rmax = n` (our literal instantiation), this is `O(n²)`. -/

/-- Conditional expected-time consequence of the Table-2 phase hypotheses.

This theorem deliberately exposes the four probabilistic phase statements as
hypotheses; until those are proved, it should not be read as a complete
formalization of Kanaya Lemma 13.  Its conclusion is `O(Rmax · n)` expected
parallel time from standard initial configurations.  When `Rmax = n`, this
is `O(n²)`, not the paper's `O(n)` bound. -/
theorem PEM_expected_parallel_time_from_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        IsInitialConfig C₀ →
        Probability.expectedParallelTimeToConsensus
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * Rmax * n) := by
  classical
  obtain ⟨c, hc_pos, hwin⟩ :=
    PEM_consensus_window_success_prob_from_phase_bounds hn4 hRmax hEmax hDmax
      hRankPhase hSwapPhase hDecisionLive hPropagationLive
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  have hRmax_pos : 0 < Rmax := by omega
  have hcRnn_pos : 0 < c * Rmax * n * n := by
    apply Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hc_pos hRmax_pos) (by omega)) (by omega)
  have hK_ne : NeZero (c * Rmax * n * n) := ⟨Nat.pos_iff_ne_zero.mp hcRnn_pos⟩
  have hInvStep : ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C → ∀ i j : Fin n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) (C.step P i j) := by
    intro C hC i j; rw [hP_def]
    exact PEMProtocolCoupled_preserves_timer_bounded (by omega : 0 < n) C hC i j
  refine ⟨c * pemTable2SuccessProb⁻¹.toReal, ?_, fun C₀ hInit => ?_⟩
  · apply mul_pos
    · exact Nat.cast_pos.mpr hc_pos
    · exact ENNReal.toReal_pos
        (ne_of_gt (ENNReal.inv_pos.mpr pemTable2SuccessProb_ne_top))
        pemTable2SuccessProb_inv_ne_top
  · have hTimer₀ : IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ := by
      intro μ
      have ht0 : (C₀ μ).1.timer = 0 := (hInit μ).2.2.2.2.1
      omega
    have hle :=
      Probability.expectedParallelTime_le_window_mul_inv_of_invariant
        P hn2 C₀ IsConsensusConfig
        (IsTimerBoundedConfig (7 * (Rmax + 4)))
        (c * Rmax * n * n) pemTable2SuccessProb
        pemTable2SuccessProb_le_one hTimer₀ hInvStep hwin
    calc Probability.expectedParallelTimeToConsensus P hn2 C₀
        ≤ ((c * Rmax * n * n : ℕ) : ENNReal) * pemTable2SuccessProb⁻¹ / ↑n := hle
      _ = ↑(c * Rmax) * pemTable2SuccessProb⁻¹ * ↑n := by
          rw [show (c * Rmax * n * n : ℕ) = (c * Rmax) * n * n from by ring]
          exact ennreal_quadratic_window_div_cancel pemTable2SuccessProb
            (by omega) pemTable2SuccessProb_pos pemTable2SuccessProb_ne_top
      _ = ENNReal.ofReal (↑(c * Rmax) * pemTable2SuccessProb⁻¹.toReal * ↑n) :=
          ennreal_nat_mul_inv_mul_nat_eq_ofReal pemTable2SuccessProb
            pemTable2SuccessProb_pos pemTable2SuccessProb_ne_top
      _ = ENNReal.ofReal (↑c * pemTable2SuccessProb⁻¹.toReal * ↑Rmax * ↑n) := by
          congr 1; push_cast; ring

/-! ### Conditional exports -/

theorem PEM_consensus_window_success_prob
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ c : ℕ, 0 < c ∧
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          pemTable2SuccessProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (c * Rmax * n * n) :=
  PEM_consensus_window_success_prob_of_phase_hypotheses hn4 hRmax hEmax hDmax
    hRankPhase hSwapPhase hDecisionLive hPropagationLive

theorem PEM_expected_parallel_time
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InTswap28SswapTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSdecTimerBounded (7 * (Rmax + 4)) :
      Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankPhase :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((10 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hSwapPhase :
      ∀ C : Config (AgentState n) Opinion n, InSrank C →
          ((20 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InTswap28SswapTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hDecisionLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianTimerAtLeast 28 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((8 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (InSdecTimerBounded (7 * (Rmax + 4))) (4 * n * n))
    (hPropagationLive :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C →
        MedianAnswerCorrect C →
        MedianTimerAtLeast 1 C →
        MedianTimerAtMost (7 * (Rmax + 4)) C →
        ¬ IsConsensusConfig C →
          ((1280 : ENNReal)⁻¹) ≤
            Probability.probReached
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C₀ : Config (AgentState n) Opinion n,
        IsInitialConfig C₀ →
        Probability.expectedParallelTimeToConsensus
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ ≤
          ENNReal.ofReal (C * Rmax * n) :=
  PEM_expected_parallel_time_from_phase_bounds hn4 hRmax hEmax hDmax
    hRankPhase hSwapPhase hDecisionLive hPropagationLive

/-! ### ProbHitWithin-chain composition (brainstorm Round 3 design)

This alternative composition uses `ProbHitWithin_add_ge_mul` (proved!) instead
of `probReached_add_ge_mul`. Each phase only needs a ProbHitWithin lower
bound (not probReached), bypassing the non-absorbing joint-event problem.

Structure: 3 phases with ProbHitWithin ≥ 1/2 each (from Markov on E[T]):
- Phase A: any config → InSrank (ranking)
- Phase B: InSrank → InSswap (swap)
- Phase C: InSswap → IsConsensusConfig (decision+propagation)

Product: (1/2)³ = 1/8 ≥ 1/4096000 = pemTable2SuccessProb. -/

theorem PEM_consensus_ProbHitWithin_from_phases
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hPhaseA : ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C InSrank (2 * Rmax * n * n))
    (hPhaseB : ∀ C : Config (AgentState n) Opinion n, InSrank C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C InSswap (4 * n * n))
    (hPhaseC : ∀ C : Config (AgentState n) Opinion n, InSswap C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig (20 * Rmax * n * n)) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        ((8 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig
              ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) := by
  classical
  intro C hTimerBd
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  -- Chain A → B → C via ProbHitWithin_add_ge_mul
  have hAB : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C InSswap
        (2 * Rmax * n * n + 4 * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C InSrank InSswap
      (2 * Rmax * n * n) (4 * n * n)
      ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
      (hPhaseA C hTimerBd) (fun D hD => hPhaseB D hD)
  have hABC : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C IsConsensusConfig
        ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C InSswap IsConsensusConfig
      (2 * Rmax * n * n + 4 * n * n) (20 * Rmax * n * n)
      (((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹)
      hAB (fun D hD => hPhaseC D hD)
  calc ((8 : ENNReal)⁻¹)
      = ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) := by
        have h8 : ((8 : ENNReal)⁻¹) ≠ ⊤ := by
          rw [ENNReal.inv_ne_top]
          norm_num
        have h2 : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
          rw [ENNReal.inv_ne_top]
          norm_num
        have hprod : (((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            ((2 : ENNReal)⁻¹)) ≠ ⊤ := by
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h2 h2) h2
        rw [← ENNReal.toReal_eq_toReal_iff' h8 hprod]
        simp [ENNReal.toReal_inv, ENNReal.toReal_mul]
        norm_num
    _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig
          ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) := hABC

/-! ### End-to-end expected parallel time (phase-bound interface)

The pipeline below is the `ProbHitWithin` composition interface.  It keeps
the two phase expected-time estimates as explicit hypotheses rather than
pretending the remaining paper-level probabilistic arguments have already
been formalized:

1. Prove 3 expected hitting time bounds (Phases A, B, C)
2. PEM_consensus_ProbHitWithin_from_expected_phases → ProbHitWithin ≥ 1/8
3. pem_table2_window_to_expectedParallelTime → E[T_parallel] ≤ O(Rmax·n) -/

private theorem real_sum_range_inv_sq_le_two (m : ℕ) :
    (∑ k ∈ Finset.range m, ((((k : ℝ) + 1) ^ 2)⁻¹)) ≤ 2 := by
  classical
  have hseries := (sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1))
  have hset :
      (Finset.range m).image (fun k : ℕ => k + 1) =
        Finset.Ioo 0 (m + 1) := by
    ext i
    simp [Finset.mem_Ioo]
    constructor
    · intro h
      omega
    · intro h
      refine ⟨i - 1, by omega, by omega⟩
  have hsum :
      (∑ k ∈ Finset.range m, ((((k : ℝ) + 1) ^ 2)⁻¹)) =
        ∑ i ∈ Finset.Ioo 0 (m + 1), (((i : ℝ) ^ 2)⁻¹) := by
    rw [← hset]
    rw [Finset.sum_image]
    · simp [Nat.cast_add]
    · intro a _ b _ h
      exact Nat.succ.inj h
  calc
    (∑ k ∈ Finset.range m, ((((k : ℝ) + 1) ^ 2)⁻¹))
        = ∑ i ∈ Finset.Ioo 0 (m + 1), (((i : ℝ) ^ 2)⁻¹) := hsum
    _ ≤ 2 / ((0 : ℝ) + 1) := by simpa using hseries
    _ = 2 := by norm_num

private theorem ennreal_sum_inv_sq_le_two_mul_pred {n : ℕ} (hn2 : 2 ≤ n) (m : ℕ) :
    ∑ k ∈ Finset.range m,
      ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≤
      ((2 * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  have hterm_ne_top : ∀ k ∈ Finset.range m,
      ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≠ ⊤ := by
    intro k _hk
    rw [ENNReal.inv_ne_top]
    exact ne_of_gt (ENNReal.mul_pos
      (by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero k) (Nat.succ_ne_zero k))
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)))
  have hleft_ne_top :
      ∑ k ∈ Finset.range m,
        ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≠ ⊤ :=
    ENNReal.sum_ne_top.2 hterm_ne_top
  have hright_ne_top : ((2 * n * (n - 1) : ℕ) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← ENNReal.toReal_le_toReal hleft_ne_top hright_ne_top]
  rw [ENNReal.toReal_sum hterm_ne_top]
  have hsum := real_sum_range_inv_sq_le_two m
  have hterm_real : ∀ k ∈ Finset.range m,
      ENNReal.toReal
        (((((k + 1) * (k + 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) =
        (((n * (n - 1) : ℕ) : ℝ) * ((((k : ℝ) + 1) ^ 2)⁻¹)) := by
    intro k _hk
    let A : ENNReal := (((k + 1) * (k + 1) : ℕ) : ENNReal)
    let B : ENNReal := ((n * (n - 1) : ℕ) : ENNReal)
    have hA0 : A ≠ 0 := by
      dsimp [A]
      exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero k) (Nat.succ_ne_zero k)
    have hAtop : A ≠ ⊤ := by
      dsimp [A]
      exact ENNReal.natCast_ne_top _
    change ENNReal.toReal ((A * B⁻¹)⁻¹) =
      (((n * (n - 1) : ℕ) : ℝ) * ((((k : ℝ) + 1) ^ 2)⁻¹))
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAtop), inv_inv]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hAreal : A.toReal = (((k : ℝ) + 1) ^ 2) := by
      have hnat : A.toReal = (((k + 1) * (k + 1) : ℕ) : ℝ) := by
        dsimp [A]
        exact ENNReal.toReal_natCast _
      rw [hnat]
      norm_num [pow_two, Nat.cast_mul, Nat.cast_add]
    have hBreal : B.toReal = ((n * (n - 1) : ℕ) : ℝ) := by
      dsimp [B]
      exact ENNReal.toReal_natCast _
    rw [hAreal, hBreal]
    ring
  calc
    (∑ k ∈ Finset.range m,
        ENNReal.toReal
          (((((k + 1) * (k + 1) : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹))
        = ∑ k ∈ Finset.range m, (((n * (n - 1) : ℕ) : ℝ) *
            ((((k : ℝ) + 1) ^ 2)⁻¹)) := by
          apply Finset.sum_congr rfl
          exact hterm_real
    _ = ((n * (n - 1) : ℕ) : ℝ) *
        (∑ k ∈ Finset.range m, ((((k : ℝ) + 1) ^ 2)⁻¹)) := by
          rw [Finset.mul_sum]
    _ ≤ ((n * (n - 1) : ℕ) : ℝ) * 2 := by
          gcongr
    _ = ENNReal.toReal ((2 * n * (n - 1) : ℕ) : ENNReal) := by
          rw [ENNReal.toReal_natCast]
          norm_num [pow_two, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm]

theorem PEM_swap_ProbHitWithin_or_exit_short
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∨ ¬ InSrank D) (4 * n * (n - 1)) := by
  have hSum := PEM_swap_phase_expected_until_swap_or_exit_le_sum
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (by omega : 2 ≤ n) hn0 hSrank
  have hBound : ∑ k ∈ Finset.range (wrongLowBCount C),
      ((((k + 1) * (k + 1) : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹ ≤
      ((2 * n * (n - 1) : ℕ) : ENNReal) :=
    ennreal_sum_inv_sq_le_two_mul_pred (by omega : 2 ≤ n) (wrongLowBCount C)
  have hE : Probability.expectedHittingTime
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D => InSswap D ∨ ¬ InSrank D) ≤
        ((2 * n * (n - 1) : ℕ) : ENNReal) :=
    hSum.trans hBound
  have hW : 2 * (2 * n * (n - 1)) ≤ (4 * n * (n - 1)) + 1 := by
    calc
      2 * (2 * n * (n - 1)) = 4 * n * (n - 1) := by ring
      _ ≤ 4 * n * (n - 1) + 1 := Nat.le_succ _
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
    (fun D => InSswap D ∨ ¬ InSrank D) hE hW

theorem PEM_swap_ProbHitWithin_or_exit
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∨ ¬ InSrank D) (4 * n * n) := by
  have hshort :=
    PEM_swap_ProbHitWithin_or_exit_short
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hEmax hDmax C hSrank
  exact hshort.trans
    (Probability.ProbHitWithin_mono_time
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D => InSswap D ∨ ¬ InSrank D)
      (by
        calc
          4 * n * (n - 1) ≤ 4 * n * n := by
            exact Nat.mul_le_mul_left (4 * n) (Nat.sub_le n 1)
          _ ≤ 4 * n * n := le_rfl))

noncomputable def srankMedianMaxEvent (C : Config (AgentState n) Opinion n)
    (i j : Fin n) : Bool :=
  by
    classical
    exact decide
      (InSrank C ∧
      (((C i).1.rank.val + 1 = ceilHalf n ∧
          (C j).1.rank.val + 1 = n) ∨
        ((C j).1.rank.val + 1 = ceilHalf n ∧
          (C i).1.rank.val + 1 = n)))

private theorem srankMedianMaxEvent_eq_true_iff
    {n : ℕ} {C : Config (AgentState n) Opinion n} {i j : Fin n} :
    srankMedianMaxEvent C i j = true ↔
      InSrank C ∧
        (((C i).1.rank.val + 1 = ceilHalf n ∧
            (C j).1.rank.val + 1 = n) ∨
          ((C j).1.rank.val + 1 = ceilHalf n ∧
            (C i).1.rank.val + 1 = n)) := by
  classical
  rw [srankMedianMaxEvent]
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

private theorem srankMedianMaxEvent_eq_false_of_not_rank
    {n : ℕ} {C : Config (AgentState n) Opinion n} {i j : Fin n}
    (h : ¬ InSrank C) :
    srankMedianMaxEvent C i j = false := by
  classical
  rw [Bool.eq_false_iff]
  intro ht
  exact h (srankMedianMaxEvent_eq_true_iff.mp ht).1

private theorem srankMedianMaxEvent_mass_le
    {n : ℕ} (hn2 : 2 ≤ n)
    (C : Config (AgentState n) Opinion n) :
    (Probability.uniformPair n hn2).toOuterMeasure
        {p : Fin n × Fin n |
          srankMedianMaxEvent C p.1 p.2 = true} ≤
      (2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
  classical
  let S : Finset (Fin n × Fin n) :=
    (Probability.OffDiagonalPairs n).filter
      (fun p : Fin n × Fin n => srankMedianMaxEvent C p.1 p.2 = true)
  have hmass :
      Probability.pairSetMass n hn2 S =
        (Probability.uniformPair n hn2).toOuterMeasure
          {p : Fin n × Fin n |
            srankMedianMaxEvent C p.1 p.2 = true} := by
    simpa [S] using
      (Probability.pairSetMass_filter_offDiagonal_eq_toOuterMeasure
        n hn2
        (fun p : Fin n × Fin n =>
          srankMedianMaxEvent C p.1 p.2 = true))
  rw [← hmass]
  rw [Probability.pairSetMass_eq_card_mul_inv_of_subset]
  · gcongr
    by_cases hRank : InSrank C
    · let medRank : Fin n :=
        ⟨ceilHalf n - 1, by unfold ceilHalf; omega⟩
      let maxRank : Fin n :=
        ⟨n - 1, by omega⟩
      have hsurj : Function.Surjective (fun u : Fin n => (C u).1.rank) :=
        Finite.injective_iff_surjective.mp hRank.ranks_inj
      obtain ⟨μ, hμ⟩ := hsurj medRank
      obtain ⟨v, hv⟩ := hsurj maxRank
      let T : Finset (Fin n × Fin n) := {(μ, v), (v, μ)}
      have hsub : S ⊆ T := by
        intro p hp
        have hpEvent : srankMedianMaxEvent C p.1 p.2 = true :=
          (Finset.mem_filter.mp hp).2
        rw [srankMedianMaxEvent] at hpEvent
        have hpProp :
            InSrank C ∧
              (((C p.1).1.rank.val + 1 = ceilHalf n ∧
                  (C p.2).1.rank.val + 1 = n) ∨
                ((C p.2).1.rank.val + 1 = ceilHalf n ∧
                  (C p.1).1.rank.val + 1 = n)) := by
          simpa using (of_decide_eq_true hpEvent)
        rcases hpProp.2 with hdir | hdir
        · have hp1 : p.1 = μ := by
            apply hRank.ranks_inj
            apply Fin.ext
            have hvalμ : (C μ).1.rank.val = ceilHalf n - 1 := by
              change (C μ).1.rank.val = medRank.val
              exact congrArg Fin.val hμ
            have hpval : (C p.1).1.rank.val = ceilHalf n - 1 := by
              omega
            rw [hpval, hvalμ]
          have hp2 : p.2 = v := by
            apply hRank.ranks_inj
            apply Fin.ext
            have hvalv : (C v).1.rank.val = n - 1 := by
              change (C v).1.rank.val = maxRank.val
              exact congrArg Fin.val hv
            have hpval : (C p.2).1.rank.val = n - 1 := by
              omega
            rw [hpval, hvalv]
          cases hp1
          cases hp2
          simp [T]
        · have hp1 : p.1 = v := by
            apply hRank.ranks_inj
            apply Fin.ext
            have hvalv : (C v).1.rank.val = n - 1 := by
              change (C v).1.rank.val = maxRank.val
              exact congrArg Fin.val hv
            have hpval : (C p.1).1.rank.val = n - 1 := by
              omega
            rw [hpval, hvalv]
          have hp2 : p.2 = μ := by
            apply hRank.ranks_inj
            apply Fin.ext
            have hvalμ : (C μ).1.rank.val = ceilHalf n - 1 := by
              change (C μ).1.rank.val = medRank.val
              exact congrArg Fin.val hμ
            have hpval : (C p.2).1.rank.val = ceilHalf n - 1 := by
              omega
            rw [hpval, hvalμ]
          cases hp1
          cases hp2
          simp [T]
      have hcardT : T.card ≤ 2 := by
        calc
          T.card ≤ ({(v, μ)} : Finset (Fin n × Fin n)).card + 1 := by
            simpa [T] using
              (Finset.card_insert_le (μ, v) ({(v, μ)} : Finset (Fin n × Fin n)))
          _ ≤ 2 := by
            have hsingle :
                ({(v, μ)} : Finset (Fin n × Fin n)).card ≤ 1 := by
              simpa using
                (Finset.card_insert_le (v, μ) (∅ : Finset (Fin n × Fin n)))
            omega
      exact_mod_cast (Finset.card_le_card hsub).trans hcardT
    · have hEmpty : S = ∅ := by
        ext p
        constructor
        · intro hp
          have hpEvent : srankMedianMaxEvent C p.1 p.2 = true :=
            (Finset.mem_filter.mp hp).2
          rw [srankMedianMaxEvent] at hpEvent
          have hpProp :
              InSrank C ∧
                (((C p.1).1.rank.val + 1 = ceilHalf n ∧
                    (C p.2).1.rank.val + 1 = n) ∨
                  ((C p.2).1.rank.val + 1 = ceilHalf n ∧
                    (C p.1).1.rank.val + 1 = n)) := by
            simpa using (of_decide_eq_true hpEvent)
          exact False.elim (hRank hpProp.1)
        · intro hp
          simp at hp
      rw [hEmpty]
      simp
  · intro p hp
    exact (Finset.mem_filter.mp hp).1

private theorem srankMedianMaxEvent_count_tail_le
    {n Rmax Emax Dmax : ℕ}
    (hn2 : 2 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) (t K : ℕ) [NeZero K] :
    (Probability.eventCountDist
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        hn2 C (@srankMedianMaxEvent n) t).toOuterMeasure
      {S : Config (AgentState n) Opinion n × ℕ | K ≤ S.2} ≤
      (t : ENNReal) *
        ((2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹) /
          (K : ENNReal) := by
  exact
    Probability.eventCountDist_expected_le
      (P := PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (hn := hn2) (C₀ := C) (Event := @srankMedianMaxEvent n)
      (eventProb := (2 : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
      (K := K)
      (hProb := by
        intro D
        exact srankMedianMaxEvent_mass_le hn2 D)
      (t := t)

private theorem srankMedianMaxEvent_count_tail_le_quarter
    {n Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) :
    (Probability.eventCountDist
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C (@srankMedianMaxEvent n) (4 * n * n)).toOuterMeasure
      {S : Config (AgentState n) Opinion n × ℕ | 12 * n ≤ S.2} ≤
      ((4 : ENNReal)⁻¹) := by
  classical
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero (12 * n) := ⟨by omega⟩
  have htail :=
    srankMedianMaxEvent_count_tail_le
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 C (t := 4 * n * n) (K := 12 * n)
  refine htail.trans ?_
  let A : ENNReal :=
    ((4 * n * n : ℕ) : ENNReal) *
      ((2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹) /
      ((12 * n : ℕ) : ENNReal)
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    rw [div_eq_mul_inv]
    refine ENNReal.mul_ne_top ?_ ?_
    · refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
      refine ENNReal.mul_ne_top (by norm_num) ?_
      rw [ENNReal.inv_ne_top]
      exact_mod_cast (Nat.mul_ne_zero (by omega : n ≠ 0) (by omega : n - 1 ≠ 0))
    · rw [ENNReal.inv_ne_top]
      exact_mod_cast (Nat.mul_ne_zero (by norm_num : (12 : ℕ) ≠ 0) (by omega : n ≠ 0))
  have hquarter_ne_top : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  change A ≤ (4 : ENNReal)⁻¹
  rw [← ENNReal.toReal_le_toReal hA_ne_top hquarter_ne_top]
  dsimp [A]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnm1R : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hdenpos : (0 : ℝ) < n - 1 := by nlinarith
  field_simp [hnR.ne', hdenpos.ne']
  ring_nf
  have hpos : (0 : ℝ) < -1 + n := by nlinarith
  have hge : (3 : ℝ) ≤ -1 + n := by nlinarith
  have hinv : (-1 + (n : ℝ))⁻¹ ≤ (3 : ℝ)⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 3)).2 hge
  have hupper : (32 : ℝ) * (-1 + (n : ℝ))⁻¹ ≤ 32 * (3 : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hlt : (32 : ℝ) * (3 : ℝ)⁻¹ < 12 := by norm_num
  have hconst₁ : ENNReal.toReal 12 = (12 : ℝ) := by norm_num
  have hconst₂ : ENNReal.toReal 4 ^ 2 * ENNReal.toReal 2 = (32 : ℝ) := by norm_num
  nlinarith

private theorem srankMedianMaxEvent_count_tail_le_quarter_short35
    {n Rmax Emax Dmax : ℕ}
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) :
    (Probability.eventCountDist
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C (@srankMedianMaxEvent n)
        (4 * n * (n - 1))).toOuterMeasure
      {S : Config (AgentState n) Opinion n × ℕ | 35 ≤ S.2} ≤
      ((4 : ENNReal)⁻¹) := by
  classical
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero 35 := ⟨by norm_num⟩
  have htail :=
    srankMedianMaxEvent_count_tail_le
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn2 hn0 C (t := 4 * n * (n - 1)) (K := 35)
  refine htail.trans ?_
  let A : ENNReal :=
    ((4 * n * (n - 1) : ℕ) : ENNReal) *
      ((2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹) /
      ((35 : ℕ) : ENNReal)
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    rw [div_eq_mul_inv]
    refine ENNReal.mul_ne_top ?_ ?_
    · refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
      refine ENNReal.mul_ne_top (by norm_num) ?_
      rw [ENNReal.inv_ne_top]
      exact_mod_cast
        (Nat.mul_ne_zero (by omega : n ≠ 0) (by omega : n - 1 ≠ 0))
    · rw [ENNReal.inv_ne_top]
      norm_num
  have hquarter_ne_top : ((4 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  change A ≤ (4 : ENNReal)⁻¹
  rw [← ENNReal.toReal_le_toReal hA_ne_top hquarter_ne_top]
  dsimp [A]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  have hdenpos : (0 : ℝ) < n - 1 := by
    have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    nlinarith
  field_simp [hnR.ne', hdenpos.ne']
  ring_nf
  norm_num

set_option maxHeartbeats 8000000 in
private theorem step_at_median_max_no_swap_odd_explicit_preserves_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn : 2 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hpar : ¬ n % 2 = 0)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) μ v) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hsu : (C μ).1.role = .Settled := hC.allSettled μ
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hsu hsv
      (by
        intro h
        have := congrArg Fin.val h
        unfold ceilHalf at hμ_med
        omega)
  have hv_not_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    have hlt : ceilHalf n < n := by
      unfold ceilHalf
      omega
    omega
  have hvμ : v ≠ μ := Ne.symm hμv
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have htr :
      transitionPEM n trank Rmax rankDelta (C μ, C v) =
        ({ (C μ).1 with
            answer := opinionToAnswer (C μ).2,
            timer := (C μ).1.timer - 1 },
         (C v).1) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsu, hsv, ne_eq,
      role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false,
      and_self, if_true, h_no_swap, hpar, hμ_med, hv_not_med, hv_max,
      hN_ne_ceil]
    split_ifs with h
    · exfalso
      obtain ⟨hzero, _⟩ := h
      omega
    · rfl
  have h_rank : (C.step P μ v μ).1.rank = (C μ).1.rank := by
    unfold Config.step
    simp only [P, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.rank = _
    rw [htr]
  have h_role : (C.step P μ v μ).1.role = (C μ).1.role := by
    unfold Config.step
    simp only [P, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.role = _
    rw [htr]
  have h_v : (C.step P μ v v).1 = (C v).1 := by
    unfold Config.step
    rw [if_neg hμv, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).2 = _
    rw [htr]
  have h_others : ∀ w : Fin n, w ≠ μ → w ≠ v → C.step P μ v w = C w := by
    intro w hwμ hwv
    unfold Config.step
    simp only [P, if_neg hμv, if_neg hwμ, if_neg hwv]
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwμ : w = μ
    · subst w
      rw [h_role]
      exact hC.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [show (C.step P μ v v).1.role = (C v).1.role from
          congrArg (fun s => s.role) h_v]
        exact hC.allSettled v
      · rw [show C.step P μ v w = C w from h_others w hwμ hwv]
        exact hC.allSettled w
  · have h_rank_w : ∀ w : Fin n, (C.step P μ v w).1.rank = (C w).1.rank := by
      intro w
      by_cases hwμ : w = μ
      · subst w
        exact h_rank
      · by_cases hwv : w = v
        · subst w
          exact congrArg (fun s => s.rank) h_v
        · rw [show C.step P μ v w = C w from h_others w hwμ hwv]
    intro w₁ w₂ hw
    apply hC.ranks_inj
    calc
      (C w₁).1.rank = (C.step P μ v w₁).1.rank := (h_rank_w w₁).symm
      _ = (C.step P μ v w₂).1.rank := hw
      _ = (C w₂).1.rank := h_rank_w w₂

set_option maxHeartbeats 8000000 in
private theorem step_at_max_median_no_swap_odd_explicit_preserves_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn : 2 ≤ n)
    {v μ : Fin n} (hvμ : v ≠ μ)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hpar : ¬ n % 2 = 0)
    (h_no_swap :
      ¬ ((C v).1.rank < (C μ).1.rank ∧
        (C v).2 = Opinion.B ∧ (C μ).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) v μ) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hsμ : (C μ).1.role = .Settled := hC.allSettled μ
  have hRD : rankDelta ((C v).1, (C μ).1) = ((C v).1, (C μ).1) :=
    hRank (C v).1 (C μ).1 hsv hsμ
      (by
        intro h
        have := congrArg Fin.val h
        unfold ceilHalf at hμ_med
        omega)
  have hv_not_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    have hlt : ceilHalf n < n := by
      unfold ceilHalf
      omega
    omega
  have hμv : μ ≠ v := Ne.symm hvμ
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have htr :
      transitionPEM n trank Rmax rankDelta (C v, C μ) =
        ((C v).1,
         { (C μ).1 with
            answer := opinionToAnswer (C μ).2,
            timer := (C μ).1.timer - 1 }) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsv, hsμ, ne_eq,
      role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false,
      and_self, if_true, h_no_swap, hpar, hμ_med, hv_not_med, hv_max,
      hN_ne_ceil]
    split_ifs with h
    · exfalso
      obtain ⟨hzero, _⟩ := h
      omega
    · rfl
  have h_v : (C.step P v μ v).1 = (C v).1 := by
    unfold Config.step
    simp only [P, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).1 = _
    rw [htr]
  have h_rank : (C.step P v μ μ).1.rank = (C μ).1.rank := by
    unfold Config.step
    rw [if_neg hvμ, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).2.rank = _
    rw [htr]
  have h_role : (C.step P v μ μ).1.role = (C μ).1.role := by
    unfold Config.step
    rw [if_neg hvμ, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).2.role = _
    rw [htr]
  have h_others : ∀ w : Fin n, w ≠ v → w ≠ μ → C.step P v μ w = C w := by
    intro w hwv hwμ
    unfold Config.step
    simp only [P, if_neg hvμ, if_neg hwv, if_neg hwμ]
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwv : w = v
    · subst w
      rw [show (C.step P v μ v).1.role = (C v).1.role from
        congrArg (fun s => s.role) h_v]
      exact hC.allSettled v
    · by_cases hwμ : w = μ
      · subst w
        rw [h_role]
        exact hC.allSettled μ
      · rw [show C.step P v μ w = C w from h_others w hwv hwμ]
        exact hC.allSettled w
  · have h_rank_w : ∀ w : Fin n, (C.step P v μ w).1.rank = (C w).1.rank := by
      intro w
      by_cases hwv : w = v
      · subst w
        exact congrArg (fun s => s.rank) h_v
      · by_cases hwμ : w = μ
        · subst w
          exact h_rank
        · rw [show C.step P v μ w = C w from h_others w hwv hwμ]
    intro w₁ w₂ hw
    apply hC.ranks_inj
    calc
      (C w₁).1.rank = (C.step P v μ w₁).1.rank := (h_rank_w w₁).symm
      _ = (C.step P v μ w₂).1.rank := hw
      _ = (C w₂).1.rank := h_rank_w w₂

set_option maxHeartbeats 8000000 in
private theorem step_at_even_lower_max_timer_ge_two_preserves_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_no_swap :
      ¬ ((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) μ v) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by
    unfold ceilHalf
    omega
  have hμ_ceil : (C μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower
  have hv_not_ceil : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hceil]
    omega
  have hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1 := by
    omega
  have hN_ne_ceil : ¬ n = ceilHalf n := by
    unfold ceilHalf
    omega
  have h_dec1a :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val = n / 2) := by
    intro h
    exact hv_not_upper (by omega)
  have h_dec2a :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧ (C μ).1.rank.val = n / 2) := by
    intro h
    omega
  have h_no_reset :
      ¬ ((C μ).1.timer - 1 = 0 ∧
        ({ (C μ).1 with timer := (C μ).1.timer - 1 } : AgentState n).answer
          ≠ (C v).1.answer) := by
    rintro ⟨hzero, _⟩
    omega
  have hswap :
      phase4_swap (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_swap
    simp [h_no_swap]
  have hdec :
      phase4_decide n (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_decide
    simp [hpar, h_dec1a, h_dec2a]
  have hprop :
      phase4_propagate n Rmax (C μ).1 (C v).1 =
        ({ (C μ).1 with timer := (C μ).1.timer - 1 }, (C v).1) := by
    unfold phase4_propagate
    simp [hμ_ceil, hv_max, h_timer, h_no_reset]
  have htr :
      transitionPEM n trank Rmax rankDelta (C μ, C v) =
        ({ (C μ).1 with timer := (C μ).1.timer - 1 }, (C v).1) := by
    unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
    simp [hRD, hμ_settled, hv_settled, role_settled_ne_resetting,
      hswap, hdec, hprop]
  have hvμ : v ≠ μ := Ne.symm hμv
  have h_rank : (C.step P μ v μ).1.rank = (C μ).1.rank := by
    unfold Config.step
    simp only [P, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.rank = _
    rw [htr]
  have h_role : (C.step P μ v μ).1.role = (C μ).1.role := by
    unfold Config.step
    simp only [P, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.role = _
    rw [htr]
  have h_v : (C.step P μ v v).1 = (C v).1 := by
    unfold Config.step
    rw [if_neg hμv, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).2 = _
    rw [htr]
  have h_others : ∀ w : Fin n, w ≠ μ → w ≠ v → C.step P μ v w = C w := by
    intro w hwμ hwv
    unfold Config.step
    simp only [P, if_neg hμv, if_neg hwμ, if_neg hwv]
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwμ : w = μ
    · subst w
      rw [h_role]
      exact hC.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [show (C.step P μ v v).1.role = (C v).1.role from
          congrArg (fun s => s.role) h_v]
        exact hC.allSettled v
      · rw [show C.step P μ v w = C w from h_others w hwμ hwv]
        exact hC.allSettled w
  · have h_rank_w : ∀ w : Fin n, (C.step P μ v w).1.rank = (C w).1.rank := by
      intro w
      by_cases hwμ : w = μ
      · subst w
        exact h_rank
      · by_cases hwv : w = v
        · subst w
          exact congrArg (fun s => s.rank) h_v
        · rw [show C.step P μ v w = C w from h_others w hwμ hwv]
    intro w₁ w₂ hw
    apply hC.ranks_inj
    calc
      (C w₁).1.rank = (C.step P μ v w₁).1.rank := (h_rank_w w₁).symm
      _ = (C.step P μ v w₂).1.rank := hw
      _ = (C w₂).1.rank := h_rank_w w₂

set_option maxHeartbeats 8000000 in
private theorem step_at_even_max_lower_timer_ge_two_preserves_InSrank
    {n trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {v μ : Fin n} (hvμ : v ≠ μ)
    (hpar : n % 2 = 0)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (h_no_swap :
      ¬ ((C v).1.rank < (C μ).1.rank ∧
        (C v).2 = Opinion.B ∧ (C μ).2 = Opinion.A))
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) v μ) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have h_rank_ne : (C v).1.rank ≠ (C μ).1.rank := by
    intro hEq
    exact hvμ (hC.ranks_inj hEq)
  have hRD : rankDelta ((C v).1, (C μ).1) = ((C v).1, (C μ).1) :=
    hRank (C v).1 (C μ).1 hv_settled hμ_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by
    unfold ceilHalf
    omega
  have hμ_ceil : (C μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower
  have hv_not_ceil : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hceil]
    omega
  have hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1 := by
    omega
  have hN_ne_ceil : ¬ n = ceilHalf n := by
    unfold ceilHalf
    omega
  have h_dec1a :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧ (C μ).1.rank.val = n / 2) := by
    intro h
    omega
  have h_dec2a :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val = n / 2) := by
    intro h
    exact hv_not_upper (by omega)
  have h_no_reset :
      ¬ ((C μ).1.timer - 1 = 0 ∧
        ({ (C μ).1 with timer := (C μ).1.timer - 1 } : AgentState n).answer
          ≠ (C v).1.answer) := by
    rintro ⟨hzero, _⟩
    omega
  have hswap :
      phase4_swap (C v).1 (C μ).1 (C v).2 (C μ).2 = ((C v).1, (C μ).1) := by
    unfold phase4_swap
    simp [h_no_swap]
  have hdec :
      phase4_decide n (C v).1 (C μ).1 (C v).2 (C μ).2 = ((C v).1, (C μ).1) := by
    unfold phase4_decide
    simp [hpar, h_dec1a, h_dec2a]
  have hprop :
      phase4_propagate n Rmax (C v).1 (C μ).1 =
        ((C v).1, { (C μ).1 with timer := (C μ).1.timer - 1 }) := by
    unfold phase4_propagate
    simp [hv_not_ceil, hμ_ceil, hv_max, hN_ne_ceil, h_timer, h_no_reset]
  have htr :
      transitionPEM n trank Rmax rankDelta (C v, C μ) =
        ((C v).1, { (C μ).1 with timer := (C μ).1.timer - 1 }) := by
    unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
    simp [hRD, hv_settled, hμ_settled, role_settled_ne_resetting,
      hswap, hdec, hprop]
  have hμv : μ ≠ v := Ne.symm hvμ
  have h_v : (C.step P v μ v).1 = (C v).1 := by
    unfold Config.step
    simp only [P, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).1 = _
    rw [htr]
  have h_rank : (C.step P v μ μ).1.rank = (C μ).1.rank := by
    unfold Config.step
    rw [if_neg hvμ, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).2.rank = _
    rw [htr]
  have h_role : (C.step P v μ μ).1.role = (C μ).1.role := by
    unfold Config.step
    rw [if_neg hvμ, if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C v, C μ)).2.role = _
    rw [htr]
  have h_others : ∀ w : Fin n, w ≠ v → w ≠ μ → C.step P v μ w = C w := by
    intro w hwv hwμ
    unfold Config.step
    simp only [P, if_neg hvμ, if_neg hwv, if_neg hwμ]
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwv : w = v
    · subst w
      rw [show (C.step P v μ v).1.role = (C v).1.role from
        congrArg (fun s => s.role) h_v]
      exact hC.allSettled v
    · by_cases hwμ : w = μ
      · subst w
        rw [h_role]
        exact hC.allSettled μ
      · rw [show C.step P v μ w = C w from h_others w hwv hwμ]
        exact hC.allSettled w
  · have h_rank_w : ∀ w : Fin n, (C.step P v μ w).1.rank = (C w).1.rank := by
      intro w
      by_cases hwv : w = v
      · subst w
        exact congrArg (fun s => s.rank) h_v
      · by_cases hwμ : w = μ
        · subst w
          exact h_rank
        · rw [show C.step P v μ w = C w from h_others w hwv hwμ]
    intro w₁ w₂ hw
    apply hC.ranks_inj
    calc
      (C w₁).1.rank = (C.step P v μ w₁).1.rank := (h_rank_w w₁).symm
      _ = (C.step P v μ w₂).1.rank := hw
      _ = (C w₂).1.rank := h_rank_w w₂

private theorem misordered_pair_8way_case_of_timer_count_safe
    {n K : ℕ} {C : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast K C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hKpos : 0 < K)
    (hEventSafe : srankMedianMaxEvent C u v = true → 1 < K) :
      ((C u).1.rank.val + 1 ≠ ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n) ∨
      (¬ n % 2 = 0 ∧ (C v).1.rank.val + 1 = ceilHalf n ∧
        1 ≤ (C v).1.timer) ∨
      (n % 2 = 0 ∧ (C v).1.rank.val + 1 = n / 2 ∧
        1 ≤ (C v).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 ≠ n / 2 + 1 ∧ (C v).1.rank.val + 1 ≠ n ∧
        1 ≤ (C u).1.timer ∧ 4 ≤ n) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer ∧ 4 ≤ n) := by
  classical
  obtain ⟨_huB, _hvA, hlt⟩ := hMis
  by_cases hpar : n % 2 = 0
  · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
    by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
    · have hu_med' : (C u).1.rank.val + 1 = n / 2 := by
        rw [← hceil]; exact hu_med
      have hu_timer1 : 1 ≤ (C u).1.timer :=
        le_trans (Nat.succ_le_of_lt hKpos) (hTimer u hu_med)
      by_cases hv_upper : (C v).1.rank.val + 1 = n / 2 + 1
      · right; right; right; left
        exact ⟨hpar, hu_med', hv_upper, hn4⟩
      · by_cases hv_max : (C v).1.rank.val + 1 = n
        · have hevent : srankMedianMaxEvent C u v = true := by
            rw [srankMedianMaxEvent]
            exact decide_eq_true
              ⟨hSrank, Or.inl ⟨hu_med, hv_max⟩⟩
          have hu_timer2 : 2 ≤ (C u).1.timer :=
            le_trans (hEventSafe hevent) (hTimer u hu_med)
          right; right; right; right; right; right; right
          exact ⟨hpar, hu_med', hv_max, hu_timer2, hn4⟩
        · right; right; right; right; right; right; left
          exact ⟨hpar, hu_med', hv_upper, hv_max, hu_timer1, hn4⟩
    · by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
      · have hv_med' : (C v).1.rank.val + 1 = n / 2 := by
          rw [← hceil]; exact hv_med
        have hv_timer1 : 1 ≤ (C v).1.timer :=
          le_trans (Nat.succ_le_of_lt hKpos) (hTimer v hv_med)
        right; right; right; right; right; left
        exact ⟨hpar, hv_med', hv_timer1, hn4⟩
      · left
        exact ⟨hu_med, hv_med⟩
  · by_cases hu_med : (C u).1.rank.val + 1 = ceilHalf n
    · have hu_timer1 : 1 ≤ (C u).1.timer :=
        le_trans (Nat.succ_le_of_lt hKpos) (hTimer u hu_med)
      by_cases hv_max : (C v).1.rank.val + 1 = n
      · have hevent : srankMedianMaxEvent C u v = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true
            ⟨hSrank, Or.inl ⟨hu_med, hv_max⟩⟩
        have hu_timer2 : 2 ≤ (C u).1.timer :=
          le_trans (hEventSafe hevent) (hTimer u hu_med)
        right; right; left
        exact ⟨hpar, hu_med, hv_max, hu_timer2⟩
      · right; left
        exact ⟨hpar, hu_med, hv_max, hu_timer1⟩
    · by_cases hv_med : (C v).1.rank.val + 1 = ceilHalf n
      · have hv_timer1 : 1 ≤ (C v).1.timer :=
          le_trans (Nat.succ_le_of_lt hKpos) (hTimer v hv_med)
        right; right; right; right; left
        exact ⟨hpar, hv_med, hv_timer1⟩
      · left
        exact ⟨hu_med, hv_med⟩

private theorem step_at_misordered_non_median_preserves_timer_geK
    {n trank Rmax K : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (hTimer : MedianTimerAtLeast K C) :
    MedianTimerAtLeast K (C.step (protocolPEM n trank Rmax rankDelta) u v) := by
  classical
  obtain ⟨hu_state, hv_state, hother_state, _⟩ :=
    step_at_misordered_non_median (trank := trank) (Rmax := Rmax)
      hRank hC hMis hu_no_med hv_no_med
  intro μ hμ_med
  by_cases hμu : μ = u
  · subst μ
    rw [hu_state] at hμ_med ⊢
    exact (hv_no_med hμ_med).elim
  · by_cases hμv : μ = v
    · subst μ
      rw [hv_state] at hμ_med ⊢
      exact (hu_no_med hμ_med).elim
    · rw [hother_state μ hμu hμv] at hμ_med ⊢
      exact hTimer μ hμ_med

private theorem step_at_v_max_misorder_preserves_timer_geK_sub_one
    {n trank Rmax K : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hv_max : (C v).1.rank.val + 1 = n)
    (hTimer : MedianTimerAtLeast K C) :
    MedianTimerAtLeast (K - 1)
      (C.step (protocolPEM n trank Rmax rankDelta) u v) := by
  classical
  have huv : u ≠ v := by
    intro h
    rw [h] at hMis
    exact absurd hMis.2.2 (lt_irrefl _)
  have h_no_max_u : (C u).1.rank.val + 1 ≠ n :=
    fun h => absurd hMis (not_misordered_fst_at_max_rank h)
  have hRankSwap :=
    transitionPEM_rank_swap_at_misorder (trank := trank) (Rmax := Rmax)
      hRank hC hMis
  have hTimerV :=
    transitionPEM_timer_of_v_max_at_misorder (trank := trank) (Rmax := Rmax)
      hRank hC hMis h_no_max_u hv_max hn4
  set P := protocolPEM n trank Rmax rankDelta
  intro μ hμ_med
  by_cases hμu : μ = u
  · subst μ
    have hstep := Config.step_fst_state P C huv
    have h_u_rank_eq : (C.step P u v u).1.rank.val = (C v).1.rank.val := by
      have h := congrArg (fun s => s.rank) hstep
      simp only [P, protocolPEM, hRankSwap.1] at h
      exact congrArg Fin.val h
    exfalso
    rw [h_u_rank_eq, hv_max] at hμ_med
    unfold ceilHalf at hμ_med
    omega
  · by_cases hμv : μ = v
    · subst μ
      have hstep := Config.step_snd_state P C huv huv.symm
      have h_v_rank_eq : (C.step P u v v).1.rank.val = (C u).1.rank.val := by
        have h := congrArg (fun s => s.rank) hstep
        simp only [P, protocolPEM, hRankSwap.2] at h
        exact congrArg Fin.val h
      have hpre_med : (C u).1.rank.val + 1 = ceilHalf n := by
        rw [h_v_rank_eq] at hμ_med
        exact hμ_med
      have hstep_timer :
          (C.step P u v v).1.timer =
            (transitionPEM n trank Rmax rankDelta (C u, C v)).2.timer := by
        have h := congrArg (fun s => s.timer) hstep
        simpa [P, protocolPEM] using h
      rw [hstep_timer]
      exact le_trans (Nat.sub_le_sub_right (hTimer u hpre_med) 1) hTimerV
    · unfold Config.step at hμ_med ⊢
      simp only [P, if_neg huv, if_neg hμu, if_neg hμv] at hμ_med ⊢
      exact le_trans (Nat.sub_le K 1) (hTimer μ hμ_med)

private lemma phase4_propagate_median_timer_lower_of_no_reset
    {n Rmax L : ℕ} {b₀ b₁ : AgentState n}
    (hceil_lt : ceilHalf n < n)
    (hnz₀ : b₀.rank.val + 1 = ceilHalf n →
      (if b₁.rank.val + 1 = n then b₀.timer - 1 else b₀.timer) ≠ 0)
    (hnz₁ : b₁.rank.val + 1 = ceilHalf n →
      (if b₀.rank.val + 1 = n then b₁.timer - 1 else b₁.timer) ≠ 0)
    (hle₀ : b₀.rank.val + 1 = ceilHalf n →
      L ≤ if b₁.rank.val + 1 = n then b₀.timer - 1 else b₀.timer)
    (hle₁ : b₁.rank.val + 1 = ceilHalf n →
      L ≤ if b₀.rank.val + 1 = n then b₁.timer - 1 else b₁.timer) :
    ((phase4_propagate n Rmax b₀ b₁).1.rank.val + 1 = ceilHalf n →
        L ≤ (phase4_propagate n Rmax b₀ b₁).1.timer) ∧
      ((phase4_propagate n Rmax b₀ b₁).2.rank.val + 1 = ceilHalf n →
        L ≤ (phase4_propagate n Rmax b₀ b₁).2.timer) := by
  classical
  unfold phase4_propagate
  by_cases hmed₀ : b₀.rank.val + 1 = ceilHalf n
  · simp [hmed₀]
    by_cases hmax₁ : b₁.rank.val + 1 = n
    · simp [hmax₁]
      have hnz : b₀.timer - 1 ≠ 0 := by simpa [hmax₁] using hnz₀ hmed₀
      have hle : L ≤ b₀.timer - 1 := by simpa [hmax₁] using hle₀ hmed₀
      by_cases hreset : b₀.timer - 1 = 0 ∧
          ({ b₀ with timer := b₀.timer - 1 } : AgentState n).answer ≠ b₁.answer
      · exact False.elim (hnz hreset.1)
      · simp [hreset]
        constructor
        · intro _; exact hle
        · intro h
          have hmax₀ : ¬ b₀.rank.val + 1 = n := by
            intro hmax
            omega
          simpa [hmax₀] using hle₁ h
    · simp [hmax₁]
      have hnz : b₀.timer ≠ 0 := by simpa [hmax₁] using hnz₀ hmed₀
      have hle : L ≤ b₀.timer := by simpa [hmax₁] using hle₀ hmed₀
      by_cases hreset : b₀.timer = 0 ∧ b₀.answer ≠ b₁.answer
      · exact False.elim (hnz hreset.1)
      · simp [hreset]
        constructor
        · intro _; exact hle
        · intro h
          have hmax₀ : ¬ b₀.rank.val + 1 = n := by
            intro hmax
            omega
          simpa [hmax₀] using hle₁ h
  · simp [hmed₀]
    by_cases hmed₁ : b₁.rank.val + 1 = ceilHalf n
    · simp [hmed₁]
      by_cases hmax₀ : b₀.rank.val + 1 = n
      · simp [hmax₀]
        have hnz : b₁.timer - 1 ≠ 0 := by simpa [hmax₀] using hnz₁ hmed₁
        have hle : L ≤ b₁.timer - 1 := by simpa [hmax₀] using hle₁ hmed₁
        by_cases hreset : b₁.timer - 1 = 0 ∧
            ({ b₁ with timer := b₁.timer - 1 } : AgentState n).answer ≠ b₀.answer
        · exact False.elim (hnz hreset.1)
        · simp [hreset]
          constructor
          · intro h
            have hmax₁ : ¬ b₁.rank.val + 1 = n := by
              intro hmax
              omega
            simpa [hmax₁] using hle₀ h
          · intro _; exact hle
      · simp [hmax₀]
        have hnz : b₁.timer ≠ 0 := by simpa [hmax₀] using hnz₁ hmed₁
        have hle : L ≤ b₁.timer := by simpa [hmax₀] using hle₁ hmed₁
        by_cases hreset : b₁.timer = 0 ∧ b₁.answer ≠ b₀.answer
        · exact False.elim (hnz hreset.1)
        · simp [hreset]
          constructor
          · intro h
            have hmax₁ : ¬ b₁.rank.val + 1 = n := by
              intro hmax
              omega
            simpa [hmax₁] using hle₀ h
          · intro _; exact hle
    · simp [hmed₁]
      exact fun h => False.elim (hmed₀ h)

set_option maxHeartbeats 8000000 in
private theorem PEM_exit_step_preserves_srank_timer_count
    {n Rmax Emax Dmax K : ℕ}
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast K C)
    {i j : Fin n} (hij : i ≠ j)
    (hKpos : 0 < K)
    (hEventSafe : srankMedianMaxEvent C i j = true → 1 < K) :
    let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
    let C' := C.step P i j
    InSrank C' ∧
      MedianTimerAtLeast
        (K - if srankMedianMaxEvent C i j then 1 else 0) C' := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hRankFix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn0)
  by_cases hswap :
      (C i).1.rank < (C j).1.rank ∧ (C i).2 = Opinion.B ∧ (C j).2 = Opinion.A
  · have hMis : MisorderedPair C (i, j) :=
      ⟨hswap.2.1, hswap.2.2, hswap.1⟩
    have hcase :=
      misordered_pair_8way_case_of_timer_count_safe
        (K := K) hn4 hSrank hTimer hMis hKpos hEventSafe
    have hSrank' : InSrank (C.step P i j) := by
      simpa [P, PEMProtocolCoupled, PEMProtocol] using
        (swap_step_decreases_eight_way
          (trank := Rmax) (Rmax := Rmax)
          (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
          hRankFix hSrank hMis hcase).1
    refine ⟨hSrank', ?_⟩
    by_cases hi_med : (C i).1.rank.val + 1 = ceilHalf n
    · by_cases hj_max : (C j).1.rank.val + 1 = n
      · have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inl ⟨hi_med, hj_max⟩⟩
        have hTimer' :
            MedianTimerAtLeast (K - 1) (C.step P i j) := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            (step_at_v_max_misorder_preserves_timer_geK_sub_one
              (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
              hRankFix hSrank hn4 hMis hj_max hTimer)
        simpa [hevent] using hTimer'
      · have hi_no_max : (C i).1.rank.val + 1 ≠ n := by
          intro hmax
          unfold ceilHalf at hi_med
          omega
        have hTimer' :
            MedianTimerAtLeast K (C.step P i j) := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            (step_at_misorder_preserves_timer_geK
              (trank := Rmax) (Rmax := Rmax)
              hRankFix hSrank hMis hi_no_max hj_max hTimer)
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hj_max hleft.2
          · exact hi_no_max hright.2
        simpa [hevent] using hTimer'
    · by_cases hj_med : (C j).1.rank.val + 1 = ceilHalf n
      · have hj_no_max : (C j).1.rank.val + 1 ≠ n := by
          intro hmax
          unfold ceilHalf at hj_med
          omega
        have hi_no_max : (C i).1.rank.val + 1 ≠ n := by
          intro hmax
          have hlt : (C i).1.rank.val < (C j).1.rank.val := hswap.1
          unfold ceilHalf at hj_med
          omega
        have hTimer' :
            MedianTimerAtLeast K (C.step P i j) := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            (step_at_misorder_preserves_timer_geK
              (trank := Rmax) (Rmax := Rmax)
              hRankFix hSrank hMis hi_no_max hj_no_max hTimer)
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hi_med hleft.1
          · exact hi_no_max hright.2
        simpa [hevent] using hTimer'
      · have hTimer' :
            MedianTimerAtLeast K (C.step P i j) := by
          simpa [P, PEMProtocolCoupled, PEMProtocol] using
            (step_at_misordered_non_median_preserves_timer_geK
              (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
              hRankFix hSrank hMis hi_med hj_med hTimer)
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hi_med hleft.1
          · exact hj_med hright.1
        simpa [hevent] using hTimer'
  · have hceil_lt : ceilHalf n < n := by
      unfold ceilHalf
      omega
    have hsu : (C i).1.role = .Settled := hSrank.allSettled i
    have hsv : (C j).1.role = .Settled := hSrank.allSettled j
    have hne_rank : (C i).1.rank ≠ (C j).1.rank := by
      intro h
      exact hij (hSrank.ranks_inj h)
    have hRD :
        rankDeltaOSSR Rmax Emax Dmax hn0 ((C i).1, (C j).1) =
          ((C i).1, (C j).1) :=
      hRankFix (C i).1 (C j).1 hsu hsv hne_rank
    let q := phase4_decide n (C i).1 (C j).1 (C i).2 (C j).2
    have hdec := phase4_decide_preserves_role_rank_children
      (n := n) (b₀ := (C i).1) (b₁ := (C j).1)
      (x₀ := (C i).2) (x₁ := (C j).2)
    have hdt := phase4_decide_preserves_timer
      (n := n) (b₀ := (C i).1) (b₁ := (C j).1)
      (x₀ := (C i).2) (x₁ := (C j).2)
    have hq₁_role : q.1.role = .Settled := by
      simpa [q] using hdec.1.trans hsu
    have hq₂_role : q.2.role = .Settled := by
      simpa [q] using hdec.2.2.2.1.trans hsv
    have hq₁_rank : q.1.rank = (C i).1.rank := by
      simpa [q] using hdec.2.1
    have hq₂_rank : q.2.rank = (C j).1.rank := by
      simpa [q] using hdec.2.2.2.2.1
    have hq₁_timer : q.1.timer = (C i).1.timer := by
      simpa [q] using hdt.1
    have hq₂_timer : q.2.timer = (C j).1.timer := by
      simpa [q] using hdt.2
    have htrans :
        transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0) (C i, C j) =
          phase4_propagate n Rmax q.1 q.2 := by
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      simp [hRD, hsu, hsv, role_settled_ne_resetting,
        phase4_swap_eq_of_not_swap hswap, q]
    let L := K - if srankMedianMaxEvent C i j then 1 else 0
    have hnz₀ : q.1.rank.val + 1 = ceilHalf n →
        (if q.2.rank.val + 1 = n then q.1.timer - 1 else q.1.timer) ≠ 0 := by
      intro hqmed
      have hi_med : (C i).1.rank.val + 1 = ceilHalf n := by
        rwa [hq₁_rank] at hqmed
      by_cases hqmax : q.2.rank.val + 1 = n
      · have hj_max : (C j).1.rank.val + 1 = n := by
          rwa [hq₂_rank] at hqmax
        have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inl ⟨hi_med, hj_max⟩⟩
        have hKi := hEventSafe hevent
        have hti := hTimer i hi_med
        simp [hqmax, hq₁_timer]
        omega
      · have hti := hTimer i hi_med
        simp [hqmax, hq₁_timer]
        omega
    have hnz₁ : q.2.rank.val + 1 = ceilHalf n →
        (if q.1.rank.val + 1 = n then q.2.timer - 1 else q.2.timer) ≠ 0 := by
      intro hqmed
      have hj_med : (C j).1.rank.val + 1 = ceilHalf n := by
        rwa [hq₂_rank] at hqmed
      by_cases hqmax : q.1.rank.val + 1 = n
      · have hi_max : (C i).1.rank.val + 1 = n := by
          rwa [hq₁_rank] at hqmax
        have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inr ⟨hj_med, hi_max⟩⟩
        have hKj := hEventSafe hevent
        have htj := hTimer j hj_med
        simp [hqmax, hq₂_timer]
        omega
      · have htj := hTimer j hj_med
        simp [hqmax, hq₂_timer]
        omega
    have hle₀ : q.1.rank.val + 1 = ceilHalf n →
        L ≤ if q.2.rank.val + 1 = n then q.1.timer - 1 else q.1.timer := by
      intro hqmed
      have hi_med : (C i).1.rank.val + 1 = ceilHalf n := by
        rwa [hq₁_rank] at hqmed
      by_cases hqmax : q.2.rank.val + 1 = n
      · have hj_max : (C j).1.rank.val + 1 = n := by
          rwa [hq₂_rank] at hqmax
        have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inl ⟨hi_med, hj_max⟩⟩
        have hti := hTimer i hi_med
        simp [L, hqmax, hevent, hq₁_timer]
        omega
      · have hi_not_max : (C i).1.rank.val + 1 ≠ n := by
          intro hmax
          omega
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hqmax (by simpa [hq₂_rank] using hleft.2)
          · exact hi_not_max hright.2
        have hti := hTimer i hi_med
        simp [L, hqmax, hevent, hq₁_timer]
        exact hti
    have hle₁ : q.2.rank.val + 1 = ceilHalf n →
        L ≤ if q.1.rank.val + 1 = n then q.2.timer - 1 else q.2.timer := by
      intro hqmed
      have hj_med : (C j).1.rank.val + 1 = ceilHalf n := by
        rwa [hq₂_rank] at hqmed
      by_cases hqmax : q.1.rank.val + 1 = n
      · have hi_max : (C i).1.rank.val + 1 = n := by
          rwa [hq₁_rank] at hqmax
        have hevent : srankMedianMaxEvent C i j = true := by
          rw [srankMedianMaxEvent]
          exact decide_eq_true ⟨hSrank, Or.inr ⟨hj_med, hi_max⟩⟩
        have htj := hTimer j hj_med
        simp [L, hqmax, hevent, hq₂_timer]
        omega
      · have hj_not_max : (C j).1.rank.val + 1 ≠ n := by
          intro hmax
          omega
        have hevent : srankMedianMaxEvent C i j = false := by
          rw [srankMedianMaxEvent]
          apply decide_eq_false
          rintro ⟨_, hleft | hright⟩
          · exact hj_not_max hleft.2
          · exact hqmax (by simpa [hq₁_rank] using hright.2)
        have htj := hTimer j hj_med
        simp [L, hqmax, hevent, hq₂_timer]
        exact htj
    have hroles :=
      phase4_propagate_settled_of_positive_median_timers
        (n := n) (Rmax := Rmax) (b₀ := q.1) (b₁ := q.2)
        hq₁_role hq₂_role hnz₀ hnz₁
    have hprop := phase4_propagate_preserves_rank_children
      (n := n) (Rmax := Rmax) (b₀ := q.1) (b₁ := q.2)
    have hlower :=
      phase4_propagate_median_timer_lower_of_no_reset
        (n := n) (Rmax := Rmax) (L := L) (b₀ := q.1) (b₁ := q.2)
        hceil_lt hnz₀ hnz₁ hle₀ hle₁
    have hδ_rank₁ :
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (C i, C j)).1.rank = (C i).1.rank := by
      rw [htrans, hprop.1, hq₁_rank]
    have hδ_rank₂ :
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (C i, C j)).2.rank = (C j).1.rank := by
      rw [htrans, hprop.2.2.1, hq₂_rank]
    have hSrank' : InSrank (C.step P i j) := by
      refine { allSettled := ?_, ranks_inj := ?_ }
      · intro w
        by_cases hwi : w = i
        · subst w
          unfold Config.step
          simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij, if_pos rfl]
          show
            (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (C i, C j)).1.role = .Settled
          rw [htrans]
          exact hroles.1
        · by_cases hwj : w = j
          · subst w
            unfold Config.step
            simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij,
              if_neg hij.symm, if_pos rfl]
            show
              (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
                (C i, C j)).2.role = .Settled
            rw [htrans]
            exact hroles.2
          · unfold Config.step
            simp only [P, if_neg hij, if_neg hwi, if_neg hwj]
            exact hSrank.allSettled w
      · have hrank : ∀ w : Fin n, (C.step P i j w).1.rank = (C w).1.rank := by
          intro w
          by_cases hwi : w = i
          · subst w
            unfold Config.step
            simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij, if_pos rfl]
            exact hδ_rank₁
          · by_cases hwj : w = j
            · subst w
              unfold Config.step
              simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij,
                if_neg hij.symm, if_pos rfl]
              exact hδ_rank₂
            · unfold Config.step
              simp only [P, if_neg hij, if_neg hwi, if_neg hwj]
        intro w₁ w₂ hw
        apply hSrank.ranks_inj
        calc
          (C w₁).1.rank = (C.step P i j w₁).1.rank := (hrank w₁).symm
          _ = (C.step P i j w₂).1.rank := hw
          _ = (C w₂).1.rank := hrank w₂
    refine ⟨hSrank', ?_⟩
    intro μ hμ_med
    by_cases hμi : μ = i
    · subst μ
      unfold Config.step at hμ_med ⊢
      simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij, if_pos rfl]
        at hμ_med ⊢
      change
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (C i, C j)).1.rank.val + 1 = ceilHalf n at hμ_med
      change L ≤
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (C i, C j)).1.timer
      rw [htrans] at hμ_med ⊢
      exact hlower.1 hμ_med
    · by_cases hμj : μ = j
      · subst μ
        unfold Config.step at hμ_med ⊢
        simp only [P, PEMProtocolCoupled, PEMProtocol, if_neg hij,
          if_neg hij.symm, if_pos rfl] at hμ_med ⊢
        change
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (C i, C j)).2.rank.val + 1 = ceilHalf n at hμ_med
        change L ≤
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
              (C i, C j)).2.timer
        rw [htrans] at hμ_med ⊢
        exact hlower.2 hμ_med
      · unfold Config.step at hμ_med ⊢
        simp only [P, if_neg hij, if_neg hμi, if_neg hμj] at hμ_med ⊢
        exact le_trans
          (Nat.sub_le K (if srankMedianMaxEvent C i j then 1 else 0))
          (hTimer μ hμ_med)

/-! The swap ProbHitWithin bound uses the union bound:
ProbHitWithin(InSswap, t) ≥ ProbHitWithin(InSswap ∨ ¬InSrank, t) - P(¬InSrank in t)
The first term ≥ 1/2 (Markov on swap E[T]).
The second term ≤ 8n/((n-1)·7·(Rmax+4)) < 1/4 (Markov on timer decrements).
So ProbHitWithin(InSswap, t) ≥ 1/2 - 1/4 = 1/4. -/

/-! Exit probability bound: from InSrank with sufficient median timer,
the probability of exiting InSrank within 4n² steps is ≤ 1/4.
Timer ≥ K means K (median,max) interactions needed before timer = 0.
P(≥K interactions in 4n²) ≤ 4n²·2/(n(n-1)) / K = 8n/((n-1)K).
For K ≥ 12n (which holds when timer ≥ 7(Rmax+4) and Rmax ≥ n ≥ 4):
8n/((n-1)·12n) = 2/(3(n-1)) ≤ 2/9 < 1/4. -/
theorem PEM_exit_prob_le_quarter
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSrank : InSrank C)
    (_hTimer : MedianTimerAtLeast (12 * n) C) :
    Probability.ProbHitWithin
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C (fun D => ¬ InSrank D) (4 * n * n) ≤
      ((4 : ENNReal)⁻¹) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop := fun D => ¬ InSrank D
  let Event : Config (AgentState n) Opinion n → Fin n → Fin n → Bool :=
    @srankMedianMaxEvent n
  let T : ℕ := 12 * n
  have hn2 : 2 ≤ n := by omega
  have hSupport :
      ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Probability.hitEventCountDist P hn2 C Goal Event (4 * n * n) S ≠ 0 →
          S.2.1 = true → T ≤ S.2.2 := by
    let Inv : Config (AgentState n) Opinion n × (Bool × ℕ) → Prop :=
      fun S => S.2.2 < T →
        S.2.1 = false ∧ InSrank S.1 ∧
          MedianTimerAtLeast (T - S.2.2) S.1
    have h0 : Inv (C, (decide (Goal C), 0)) := by
      intro _
      have hgoal : decide (Goal C) = false := by
        simp [Goal, _hSrank]
      simp [Inv, hgoal, _hSrank, _hTimer, T]
    have hstep : ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Inv S →
          ∀ p : Fin n × Fin n, p ∈ (Probability.uniformPair n hn2).support →
            Inv
              (let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
               (C', (S.2.1 || decide (Goal C'),
                 S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))) := by
      intro S hInv p hp
      intro hlt
      by_cases hcount_lt : S.2.2 < T
      · obtain ⟨hhitFalse, hSrankS, hTimerS⟩ := hInv hcount_lt
        have hp_ne : p.1 ≠ p.2 := by
          by_contra hEq
          have hprob : Probability.uniformPair n hn2 p = 0 := by
            rcases p with ⟨i, j⟩
            dsimp at hEq ⊢
            subst j
            exact Probability.uniformPair_apply_self n hn2 i
          have hmem : Probability.uniformPair n hn2 p ≠ 0 := by
            simpa [PMF.mem_support_iff] using hp
          exact hmem hprob
        have hKpos : 0 < T - S.2.2 := by omega
        have hstep' :=
          PEM_exit_step_preserves_srank_timer_count
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (K := T - S.2.2) hn4 hn0 hSrankS hTimerS hp_ne hKpos
            (by
              intro hevent
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              simp [Event, hevent] at hnew
              omega)
        let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
        have hSrankC' : InSrank C' := by
          simpa [C', P] using hstep'.1
        have hgoalFalse : decide (Goal C') = false := by
          simp [Goal, hSrankC']
        refine ⟨?_, hSrankC', ?_⟩
        · simp [C', hhitFalse, hgoalFalse]
        · have htimer := hstep'.2
          by_cases hevent : Event S.1 p.1 p.2 = true
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 - 1 := by
              simp [hevent]
              omega
            simpa [C', P, Event, hevent, hbound] using htimer
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 := by
              simp [hevent]
            simpa [C', P, Event, hevent, hbound] using htimer
      · exfalso
        have hnew :
            S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
          simpa using hlt
        exact hcount_lt
          (lt_of_le_of_lt
            (Nat.le_add_right S.2.2 (if Event S.1 p.1 p.2 then 1 else 0))
            hnew)
    intro S hSupp hhit
    have hInvS :=
      Probability.hitEventCountDist_support_inv_decide
        (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
        (Inv := Inv) h0 hstep (4 * n * n) S
        (by simpa [PMF.mem_support_iff] using hSupp)
    by_contra hnot
    have hlt : S.2.2 < T := Nat.lt_of_not_ge hnot
    obtain ⟨hflagFalse, _, _⟩ := hInvS hlt
    rw [hflagFalse] at hhit
    cases hhit
  have hMain :=
    Probability.ProbHitWithin_le_eventCountDist_tail_of_support_imp
      (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
      (t := 4 * n * n) (K := T) hSupport
  refine hMain.trans ?_
  simpa [P, Event, T] using
    srankMedianMaxEvent_count_tail_le_quarter
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn4 hn0 C

/-- Strengthened exit/timer-failure bound.  From `Srank` with median timer at
least `12n`, within the `4n²` swap window the probability of either leaving
`Srank` or losing positive median timer is at most `1/4`.  The proof is the
same event-count argument as `PEM_exit_prob_le_quarter`: before `12n`
median/max interactions have occurred, the maintained invariant gives both
`InSrank` and `MedianTimerAtLeast 1`. -/
theorem PEM_srank_or_timer_failure_prob_le_quarter
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hSrank : InSrank C)
    (_hTimer : MedianTimerAtLeast (12 * n) C) :
    Probability.ProbHitWithin
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D) (4 * n * n) ≤
      ((4 : ENNReal)⁻¹) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let Event : Config (AgentState n) Opinion n → Fin n → Fin n → Bool :=
    @srankMedianMaxEvent n
  let T : ℕ := 12 * n
  have hn2 : 2 ≤ n := by omega
  have hSupport :
      ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Probability.hitEventCountDist P hn2 C Goal Event (4 * n * n) S ≠ 0 →
          S.2.1 = true → T ≤ S.2.2 := by
    let Inv : Config (AgentState n) Opinion n × (Bool × ℕ) → Prop :=
      fun S => S.2.2 < T →
        S.2.1 = false ∧ InSrank S.1 ∧
          MedianTimerAtLeast (T - S.2.2) S.1
    have h0 : Inv (C, (decide (Goal C), 0)) := by
      intro _
      have htimer1 : MedianTimerAtLeast 1 C :=
        MedianTimerAtLeast.mono (n := n) (a := 1) (b := T) (by
          dsimp [T]
          omega) _hTimer
      have hgoal : decide (Goal C) = false := by
        simp [Goal, _hSrank, htimer1]
      simp [hgoal, _hSrank, _hTimer, T]
    have hstep : ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Inv S →
          ∀ p : Fin n × Fin n, p ∈ (Probability.uniformPair n hn2).support →
            Inv
              (let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
               (C', (S.2.1 || decide (Goal C'),
                 S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))) := by
      intro S hInv p hp
      intro hlt
      by_cases hcount_lt : S.2.2 < T
      · obtain ⟨hhitFalse, hSrankS, hTimerS⟩ := hInv hcount_lt
        have hp_ne : p.1 ≠ p.2 := by
          by_contra hEq
          have hprob : Probability.uniformPair n hn2 p = 0 := by
            rcases p with ⟨i, j⟩
            dsimp at hEq ⊢
            subst j
            exact Probability.uniformPair_apply_self n hn2 i
          have hmem : Probability.uniformPair n hn2 p ≠ 0 := by
            simpa [PMF.mem_support_iff] using hp
          exact hmem hprob
        have hKpos : 0 < T - S.2.2 := by omega
        have hstep' :=
          PEM_exit_step_preserves_srank_timer_count
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (K := T - S.2.2) hn4 hn0 hSrankS hTimerS hp_ne hKpos
            (by
              intro hevent
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              simp [Event, hevent] at hnew
              omega)
        let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
        have hSrankC' : InSrank C' := by
          simpa [C', P] using hstep'.1
        have htimerNew :
            MedianTimerAtLeast
              (T - (S.2.2 + if Event S.1 p.1 p.2 then 1 else 0)) C' := by
          have htimer := hstep'.2
          by_cases hevent : Event S.1 p.1 p.2 = true
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 - 1 := by
              simp [hevent]
              omega
            simpa [C', P, Event, hevent, hbound] using htimer
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 := by
              simp [hevent]
            simpa [C', P, Event, hevent, hbound] using htimer
        have htimer1C' : MedianTimerAtLeast 1 C' :=
          MedianTimerAtLeast.mono (n := n) (a := 1)
            (b := T - (S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))
            (by
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              omega)
            htimerNew
        have hgoalFalse : decide (Goal C') = false := by
          simp [Goal, hSrankC', htimer1C']
        refine ⟨?_, hSrankC', htimerNew⟩
        simp [C', hhitFalse, hgoalFalse]
      · exfalso
        have hnew :
            S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
          simpa using hlt
        exact hcount_lt
          (lt_of_le_of_lt
            (Nat.le_add_right S.2.2 (if Event S.1 p.1 p.2 then 1 else 0))
            hnew)
    intro S hSupp hhit
    have hInvS :=
      Probability.hitEventCountDist_support_inv_decide
        (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
        (Inv := Inv) h0 hstep (4 * n * n) S
        (by simpa [PMF.mem_support_iff] using hSupp)
    by_contra hnot
    have hlt : S.2.2 < T := Nat.lt_of_not_ge hnot
    obtain ⟨hflagFalse, _, _⟩ := hInvS hlt
    rw [hflagFalse] at hhit
    cases hhit
  have hMain :=
    Probability.ProbHitWithin_le_eventCountDist_tail_of_support_imp
      (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
      (t := 4 * n * n) (K := T) hSupport
  refine hMain.trans ?_
  simpa [P, Event, T] using
    srankMedianMaxEvent_count_tail_le_quarter
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn4 hn0 C

theorem PEM_srank_or_timer_failure_prob_le_quarter_short35_no_counter
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n)
    (_hSrank : InSrank C)
    (_hTimer : MedianTimerAtLeast 35 C) :
    Probability.ProbHitWithin
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D)
      (4 * n * (n - 1)) ≤ ((4 : ENNReal)⁻¹) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let Event : Config (AgentState n) Opinion n → Fin n → Fin n → Bool :=
    @srankMedianMaxEvent n
  let T : ℕ := 35
  have hn2 : 2 ≤ n := by omega
  have hSupport :
      ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Probability.hitEventCountDist P hn2 C Goal Event (4 * n * (n - 1)) S ≠ 0 →
          S.2.1 = true → T ≤ S.2.2 := by
    let Inv : Config (AgentState n) Opinion n × (Bool × ℕ) → Prop :=
      fun S => S.2.2 < T →
        S.2.1 = false ∧ InSrank S.1 ∧
          MedianTimerAtLeast (T - S.2.2) S.1
    have h0 : Inv (C, (decide (Goal C), 0)) := by
      intro _
      have htimer1 : MedianTimerAtLeast 1 C :=
        MedianTimerAtLeast.mono (n := n) (a := 1) (b := T) (by
          dsimp [T]
          omega) _hTimer
      have hgoal : decide (Goal C) = false := by
        simp [Goal, _hSrank, htimer1]
      simp [hgoal, _hSrank, _hTimer, T]
    have hstep : ∀ S : Config (AgentState n) Opinion n × (Bool × ℕ),
        Inv S →
          ∀ p : Fin n × Fin n, p ∈ (Probability.uniformPair n hn2).support →
            Inv
              (let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
               (C', (S.2.1 || decide (Goal C'),
                 S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))) := by
      intro S hInv p hp
      intro hlt
      by_cases hcount_lt : S.2.2 < T
      · obtain ⟨hhitFalse, hSrankS, hTimerS⟩ := hInv hcount_lt
        have hp_ne : p.1 ≠ p.2 := by
          by_contra hEq
          have hprob : Probability.uniformPair n hn2 p = 0 := by
            rcases p with ⟨i, j⟩
            dsimp at hEq ⊢
            subst j
            exact Probability.uniformPair_apply_self n hn2 i
          have hmem : Probability.uniformPair n hn2 p ≠ 0 := by
            simpa [PMF.mem_support_iff] using hp
          exact hmem hprob
        have hKpos : 0 < T - S.2.2 := by omega
        have hstep' :=
          PEM_exit_step_preserves_srank_timer_count
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            (K := T - S.2.2) hn4 hn0 hSrankS hTimerS hp_ne hKpos
            (by
              intro hevent
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              simp [Event, hevent] at hnew
              omega)
        let C' : Config (AgentState n) Opinion n := S.1.step P p.1 p.2
        have hSrankC' : InSrank C' := by
          simpa [C', P] using hstep'.1
        have htimerNew :
            MedianTimerAtLeast
              (T - (S.2.2 + if Event S.1 p.1 p.2 then 1 else 0)) C' := by
          have htimer := hstep'.2
          by_cases hevent : Event S.1 p.1 p.2 = true
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 - 1 := by
              simp [hevent]
              omega
            simpa [C', P, Event, hevent, hbound] using htimer
          · have hbound :
                T - (S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0)) =
                  T - S.2.2 := by
              simp [hevent]
            simpa [C', P, Event, hevent, hbound] using htimer
        have htimer1C' : MedianTimerAtLeast 1 C' :=
          MedianTimerAtLeast.mono (n := n) (a := 1)
            (b := T - (S.2.2 + if Event S.1 p.1 p.2 then 1 else 0))
            (by
              have hnew :
                  S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
                simpa using hlt
              omega)
            htimerNew
        have hgoalFalse : decide (Goal C') = false := by
          simp [Goal, hSrankC', htimer1C']
        refine ⟨?_, hSrankC', htimerNew⟩
        simp [C', hhitFalse, hgoalFalse]
      · exfalso
        have hnew :
            S.2.2 + (if Event S.1 p.1 p.2 then 1 else 0) < T := by
          simpa using hlt
        exact hcount_lt
          (lt_of_le_of_lt
            (Nat.le_add_right S.2.2 (if Event S.1 p.1 p.2 then 1 else 0))
            hnew)
    intro S hSupp hhit
    have hInvS :=
      Probability.hitEventCountDist_support_inv_decide
        (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
        (Inv := Inv) h0 hstep (4 * n * (n - 1)) S
        (by simpa [PMF.mem_support_iff] using hSupp)
    by_contra hnot
    have hlt : S.2.2 < T := Nat.lt_of_not_ge hnot
    obtain ⟨hflagFalse, _, _⟩ := hInvS hlt
    rw [hflagFalse] at hhit
    cases hhit
  have hMain :=
    Probability.ProbHitWithin_le_eventCountDist_tail_of_support_imp
      (P := P) (hn := hn2) (C₀ := C) (Goal := Goal) (Event := Event)
      (t := 4 * n * (n - 1)) (K := T) hSupport
  refine hMain.trans ?_
  simpa [P, Event, T] using
    srankMedianMaxEvent_count_tail_le_quarter_short35
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) hn4 hn0 C

theorem PEM_srank_or_timer_failure_prob_le_quarter_short35
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (_hRmax : n ≤ Rmax) (_hEmax : n ≤ Emax) (_hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C) :
    Probability.ProbHitWithin
      (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C
      (fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D)
      (4 * n * (n - 1)) ≤ ((4 : ENNReal)⁻¹) :=
  PEM_srank_or_timer_failure_prob_le_quarter_short35_no_counter
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn4 hn0 C hSrank hTimer

theorem PEM_swap_ProbHitWithin_InSswap
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast (12 * n) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C InSswap (4 * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  have hOrExit := PEM_swap_ProbHitWithin_or_exit hn4 hn0 hRmax hEmax hDmax C hSrank
  have hExit := PEM_exit_prob_le_quarter hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  simpa [P] using
    (ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C InSswap (fun D => ¬ InSrank D) (4 * n * n)
      hOrExit hExit)

/-- Timer-live swap lower bound.  The phase-B descent reaches `InSswap` with
probability at least `1/2` unless it exits `InSrank`; the event-count tail bound
also rules out, with probability `3/4`, either exiting `InSrank` or exhausting
the median timer.  A union-bound subtraction leaves a `1/4` chance of reaching
`InSswap` while the median timer is still positive. -/
theorem PEM_swap_ProbHitWithin_InSswap_timer_live
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast (12 * n) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∧ MedianTimerAtLeast 1 D) (4 * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Good : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let OrExit : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∨ ¬ InSrank D
  have hOrExit :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C OrExit (4 * n * n) := by
    simpa [P, OrExit] using
      PEM_swap_ProbHitWithin_or_exit hn4 hn0 hRmax hEmax hDmax C hSrank
  have hBad :
      Probability.ProbHitWithin P hn2 C Bad (4 * n * n) ≤
        ((4 : ENNReal)⁻¹) := by
    simpa [P, Bad] using
      PEM_srank_or_timer_failure_prob_le_quarter
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  have hOrExit_mono :
      Probability.ProbHitWithin P hn2 C OrExit (4 * n * n) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Good D ∨ Bad D) (4 * n * n) := by
    refine Probability.ProbHitWithin_mono_goal P hn2 C OrExit
      (fun D => Good D ∨ Bad D) ?_ (4 * n * n)
    intro D hD
    rcases hD with hSwap | hNotRank
    · by_cases hTimerD : MedianTimerAtLeast 1 D
      · exact Or.inl ⟨hSwap, hTimerD⟩
      · exact Or.inr (Or.inr hTimerD)
    · exact Or.inr (Or.inl hNotRank)
  have hOrGoodBad :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Good D ∨ Bad D) (4 * n * n) :=
    hOrExit.trans hOrExit_mono
  simpa [P, Good] using
    (ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C Good Bad (4 * n * n) hOrGoodBad hBad)

theorem PEM_swap_ProbHitWithin_InSswap_timer_live_short35
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
        (4 * n * (n - 1)) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Good : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let Bad : Config (AgentState n) Opinion n → Prop :=
    fun D => ¬ InSrank D ∨ ¬ MedianTimerAtLeast 1 D
  let OrExit : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∨ ¬ InSrank D
  have hOrExit :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C OrExit (4 * n * (n - 1)) := by
    simpa [P, OrExit] using
      PEM_swap_ProbHitWithin_or_exit_short hn4 hn0 hRmax hEmax hDmax C hSrank
  have hBad :
      Probability.ProbHitWithin P hn2 C Bad (4 * n * (n - 1)) ≤
        ((4 : ENNReal)⁻¹) := by
    simpa [P, Bad] using
      PEM_srank_or_timer_failure_prob_le_quarter_short35
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  have hOrExit_mono :
      Probability.ProbHitWithin P hn2 C OrExit (4 * n * (n - 1)) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Good D ∨ Bad D) (4 * n * (n - 1)) := by
    refine Probability.ProbHitWithin_mono_goal P hn2 C OrExit
      (fun D => Good D ∨ Bad D) ?_ (4 * n * (n - 1))
    intro D hD
    rcases hD with hSwap | hNotRank
    · by_cases hTimerD : MedianTimerAtLeast 1 D
      · exact Or.inl ⟨hSwap, hTimerD⟩
      · exact Or.inr (Or.inr hTimerD)
    · exact Or.inr (Or.inl hNotRank)
  have hOrGoodBad :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Good D ∨ Bad D) (4 * n * (n - 1)) :=
    hOrExit.trans hOrExit_mono
  simpa [P, Good] using
    (ProbHitWithin_left_ge_inv4_of_or_ge_half_and_right_le_inv4
      P hn2 C Good Bad (4 * n * (n - 1)) hOrGoodBad hBad)

theorem PEM_swap_ProbHitWithin_InSswap_timer_live_const35
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => InSswap D ∧ MedianTimerAtLeast 1 D) (4 * n * n) := by
  have hshort :=
    PEM_swap_ProbHitWithin_InSswap_timer_live_short35
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  exact hshort.trans
    (Probability.ProbHitWithin_mono_time
      (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C
      (fun D => InSswap D ∧ MedianTimerAtLeast 1 D)
      (by
        exact Nat.mul_le_mul_left (4 * n) (Nat.sub_le n 1)))

theorem PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast 35 C)
    (hBound : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D =>
          InSswap D ∧ MedianTimerAtLeast 1 D ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) D)
        (4 * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Good : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig (7 * (Rmax + 4))
  have hBase :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Good (4 * n * n) := by
    simpa [P, Good] using
      PEM_swap_ProbHitWithin_InSswap_timer_live_const35
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  have hInvStep : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ∀ i j : Fin n, Inv (D.step P i j) := by
    intro D hD i j
    simpa [P, Inv] using
      PEMProtocolCoupled_preserves_timer_bounded hn0 D hD i j
  have hEq :=
    Probability.ProbHitWithin_eq_and_inv_of_invariant
      P hn2 C Good Inv hBound hInvStep (4 * n * n)
  rw [← hEq] at hBase
  simpa [P, Good, Inv, and_assoc] using hBase

/-- Timer-live swap lower bound, retaining an ambient timer upper-bound
invariant.  This is the phase-B form needed by the paper-aligned chain:
`InSswap` is reached while the median timer is positive and all timers remain
bounded by the protocol timer budget. -/
theorem PEM_swap_ProbHitWithin_InSswap_timer_live_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C)
    (hTimer : MedianTimerAtLeast (12 * n) C)
    (hBound : IsTimerBoundedConfig (7 * (Rmax + 4)) C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D =>
          InSswap D ∧ MedianTimerAtLeast 1 D ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) D)
        (4 * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hn2 : 2 ≤ n := by omega
  let Good : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig (7 * (Rmax + 4))
  have hBase :
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Good (4 * n * n) := by
    simpa [P, Good] using
      PEM_swap_ProbHitWithin_InSswap_timer_live
        hn4 hn0 hRmax hEmax hDmax C hSrank hTimer
  have hInvStep : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ∀ i j : Fin n, Inv (D.step P i j) := by
    intro D hD i j
    simpa [P, Inv] using
      PEMProtocolCoupled_preserves_timer_bounded hn0 D hD i j
  have hEq :=
    Probability.ProbHitWithin_eq_and_inv_of_invariant
      P hn2 C Good Inv hBound hInvStep (4 * n * n)
  rw [← hEq] at hBase
  simpa [P, Good, Inv, and_assoc] using hBase

theorem PEM_end_to_end_ProbHitWithin_from_expected_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    (hInit : IsInitialConfig C₀)
    (hRankBound :
      Probability.expectedHittingTime
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀
        (fun C =>
          InSrank C ∧ MedianTimerAtLeast 35 C ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) C) ≤
        ((Rmax * n * n : ℕ) : ENNReal))
    (hConsensusBound :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C → MedianTimerAtLeast 1 C →
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((10 * Rmax * n * n : ℕ) : ENNReal)) :
    ((16 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ IsConsensusConfig
        ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) := by
  classical
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  let SwapLiveTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSswap C ∧ MedianTimerAtLeast 1 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  have hRankE : Probability.expectedHittingTime P hn2 C₀ RankTarget ≤
      ((Rmax * n * n : ℕ) : ENNReal) :=
    hRankBound
  have hRankW : 2 * (Rmax * n * n) ≤ (2 * Rmax * n * n) + 1 := by nlinarith
  have hRankPH : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ RankTarget (2 * Rmax * n * n) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C₀ RankTarget
      hRankE hRankW
  have hSwapPH : ∀ C : Config (AgentState n) Opinion n, RankTarget C →
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SwapLiveTarget (4 * n * n) :=
    fun C ⟨hR, hT, hB⟩ => by
      simpa [P, SwapLiveTarget] using
        PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded
          hn4 hn0 hRmax hEmax hDmax C hR hT hB
  have hConsE : ∀ C : Config (AgentState n) Opinion n, SwapLiveTarget C →
      Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
        ((10 * Rmax * n * n : ℕ) : ENNReal) :=
    fun C hC => hConsensusBound C hC.1 hC.2.1 hC.2.2
  have hConsW : 2 * (10 * Rmax * n * n) ≤ (20 * Rmax * n * n) + 1 := by nlinarith
  have hConsPH : ∀ C : Config (AgentState n) Opinion n, SwapLiveTarget C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig (20 * Rmax * n * n) :=
    fun C hC => Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C
      IsConsensusConfig (hConsE C hC) hConsW
  have hAB : ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ SwapLiveTarget
        (2 * Rmax * n * n + 4 * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀ RankTarget SwapLiveTarget
      (2 * Rmax * n * n) (4 * n * n)
      ((2 : ENNReal)⁻¹) ((4 : ENNReal)⁻¹)
      hRankPH (fun D hD => hSwapPH D hD)
  have hChain : (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ IsConsensusConfig
        ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀ SwapLiveTarget IsConsensusConfig
      (2 * Rmax * n * n + 4 * n * n) (20 * Rmax * n * n)
      (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹)
      hAB (fun D hD => hConsPH D hD)
  calc ((16 : ENNReal)⁻¹)
      = ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) := by
        rw [← ENNReal.toReal_eq_toReal_iff'
          (by rw [ENNReal.inv_ne_top]; norm_num)
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by simp [ENNReal.inv_ne_top]) (by simp [ENNReal.inv_ne_top]))
            (by simp [ENNReal.inv_ne_top]))]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_mul]
        norm_num
    _ ≤ _ := hChain

/-- Global-window version of
`PEM_end_to_end_ProbHitWithin_from_expected_phase_bounds`.

The remaining phase work is isolated in two reusable expected-time hypotheses:
ranking from every timer-bounded configuration, and consensus from every live
`InSswap` configuration.  This theorem removes the artificial
`IsInitialConfig` dependency from the window-success composition, which is the
form needed for geometric restarts. -/
theorem PEM_end_to_end_ProbHitWithin_from_global_expected_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankBound :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C
          (fun D =>
            InSrank D ∧ MedianTimerAtLeast 35 D ∧
              IsTimerBoundedConfig (7 * (Rmax + 4)) D) ≤
          ((Rmax * n * n : ℕ) : ENNReal))
    (hConsensusBound :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C → MedianTimerAtLeast 1 C →
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((10 * Rmax * n * n : ℕ) : ENNReal)) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ →
      ((16 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C₀ IsConsensusConfig
          ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) := by
  classical
  intro C₀ hTimer₀
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  let SwapLiveTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSswap C ∧ MedianTimerAtLeast 1 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C
  have hRankE : Probability.expectedHittingTime P hn2 C₀ RankTarget ≤
      ((Rmax * n * n : ℕ) : ENNReal) :=
    hRankBound C₀ hTimer₀
  have hRankW : 2 * (Rmax * n * n) ≤ (2 * Rmax * n * n) + 1 := by nlinarith
  have hRankPH : ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ RankTarget (2 * Rmax * n * n) :=
    Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C₀ RankTarget
      hRankE hRankW
  have hSwapPH : ∀ C : Config (AgentState n) Opinion n, RankTarget C →
      ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SwapLiveTarget (4 * n * n) :=
    fun C ⟨hR, hT, hB⟩ => by
      simpa [P, SwapLiveTarget] using
        PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded
          hn4 hn0 hRmax hEmax hDmax C hR hT hB
  have hConsE : ∀ C : Config (AgentState n) Opinion n, SwapLiveTarget C →
      Probability.expectedHittingTime P hn2 C IsConsensusConfig ≤
        ((10 * Rmax * n * n : ℕ) : ENNReal) :=
    fun C hC => hConsensusBound C hC.1 hC.2.1 hC.2.2
  have hConsW : 2 * (10 * Rmax * n * n) ≤ (20 * Rmax * n * n) + 1 := by nlinarith
  have hConsPH : ∀ C : Config (AgentState n) Opinion n, SwapLiveTarget C →
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig (20 * Rmax * n * n) :=
    fun C hC => Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le P hn2 C
      IsConsensusConfig (hConsE C hC) hConsW
  have hAB : ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ SwapLiveTarget
        (2 * Rmax * n * n + 4 * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀ RankTarget SwapLiveTarget
      (2 * Rmax * n * n) (4 * n * n)
      ((2 : ENNReal)⁻¹) ((4 : ENNReal)⁻¹)
      hRankPH (fun D hD => hSwapPH D hD)
  have hChain : (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) * ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C₀ IsConsensusConfig
        ((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C₀ SwapLiveTarget IsConsensusConfig
      (2 * Rmax * n * n + 4 * n * n) (20 * Rmax * n * n)
      (((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) ((2 : ENNReal)⁻¹)
      hAB (fun D hD => hConsPH D hD)
  calc ((16 : ENNReal)⁻¹)
      = ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) := by
        rw [← ENNReal.toReal_eq_toReal_iff'
          (by rw [ENNReal.inv_ne_top]; norm_num)
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by simp [ENNReal.inv_ne_top]) (by simp [ENNReal.inv_ne_top]))
            (by simp [ENNReal.inv_ne_top]))]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_mul]
        norm_num
    _ ≤ _ := hChain

/-- Expected-parallel-time consequence of the global phase expected-time
bounds.  This is the restart-ready end-to-end form: the timer upper bound is
an invariant of the coupled protocol, and the two remaining quantitative
obligations are exactly the global ranking and live-consensus expected-time
phase bounds. -/
theorem PEM_expected_parallel_time_from_global_expected_phase_bounds
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    [DecidablePred (InSrank : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (InSswap : Config (AgentState n) Opinion n → Prop)]
    [DecidablePred (IsConsensusConfig : Config (AgentState n) Opinion n → Prop)]
    (hn4 : 4 ≤ n) (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRankBound :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C
          (fun D =>
            InSrank D ∧ MedianTimerAtLeast 35 D ∧
              IsTimerBoundedConfig (7 * (Rmax + 4)) D) ≤
          ((Rmax * n * n : ℕ) : ENNReal))
    (hConsensusBound :
      ∀ C : Config (AgentState n) Opinion n,
        InSswap C → MedianTimerAtLeast 1 C →
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((10 * Rmax * n * n : ℕ) : ENNReal)) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((((2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n : ℕ) : ENNReal) *
          ((16 : ENNReal)⁻¹)⁻¹) / n) := by
  classical
  intro C₀ hTimer₀
  set P := PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n) with hP_def
  have hn2 : 2 ≤ n := by omega
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig (7 * (Rmax + 4))
  let K : ℕ := (2 * Rmax * n * n + 4 * n * n) + 20 * Rmax * n * n
  have hKpos : 0 < K := by
    dsimp [K]
    have hRpos : 0 < Rmax := by omega
    have hnpos : 0 < n := by omega
    have hfirst : 0 < 2 * Rmax * n * n := by positivity
    omega
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : ((16 : ENNReal)⁻¹) ≤ 1 := by norm_num
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    simpa [P, Inv] using
      PEMProtocolCoupled_preserves_timer_bounded (by omega : 0 < n) C hC i j
  have hwin : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      ((16 : ENNReal)⁻¹) ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hC _hNot
    simpa [P, Inv, K] using
      (PEM_end_to_end_ProbHitWithin_from_global_expected_phase_bounds
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hRmax hEmax hDmax hRankBound hConsensusBound C hC)
  simpa [Probability.expectedParallelTimeToConsensus, P, Inv, K] using
    (Probability.expectedParallelTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K ((16 : ENNReal)⁻¹)
      hp_le_one hTimer₀ hInvStep hwin)

/-! ### Phase bound proofs (Lemma 6 + Lemma 9+11)

The end-to-end composition is conditional on two phase E[T] bounds:
- hRankBound (Lemma 6): E[T to InSrank ∧ timer≥35 ∧ timer-bounded] ≤ Rmax·n²
- hConsensusBound (Lemma 9+11): E[T to consensus from InSswap+timer] ≤ 10·Rmax·n²

Strategy for hConsensusBound (ChatGPT "exit = progress" design):
Define DecisionProgress := MedianAnswerCorrect ∨ CorrectResetSeed.
The exit from LiveSwap is absorbed as progress (not failure).
Chain: InSswap → DecisionProgress → CorrectSeed → Epidemic → Consensus.

For odd n: exit is deterministically good progress (phase4_decide sets
median answer at the same step as the potential reset).
For even n: requires the (lower-median, upper-median) decision interaction
to happen before timer exhaustion (probabilistic, high probability). -/

def DecisionProgress (C : Config (AgentState n) Opinion n) : Prop :=
  MedianAnswerCorrect C ∨ CorrectResetSeed C

/-! Strategy sketch for hConsensusBound using the bridge lemma:

Step 1: E[T from InSswap to DecisionProgress] ≤ n(n-1)
  Use expectedHittingTime_mono_goal on PEM_expected_Tswap_..._or_exit_le
  (needs exit_target_subset_DecisionProgress — protocol-specific sorry)

Step 2: E[T from DecisionProgress to IsConsensusConfig]
  Case MedianAnswerCorrect:
    Use epidemic_timer_branch_to_consensus (deterministic) +
    expectedHittingTime_le_of_deterministic_descent (bridge lemma)
    → E[T] ≤ wrongAnswerCount · n(n-1) ≤ n · n(n-1) = n²(n-1)
  Case CorrectResetSeed:
    Use reset epidemic propagation (nonResettingCount descent)
    → E[T] ≤ nonResettingCount · n(n-1) ≤ n · n(n-1) = n²(n-1)

Step 3: Strong Markov composition
  E[T to consensus] ≤ n(n-1) + n²(n-1) ≤ 2n³ ≤ 10·Rmax·n²
  (since Rmax ≥ n → 10·Rmax·n² ≥ 10n³ ≥ 2n³) -/

/-! General step properties from InSswap under PEMProtocolCoupled.
From InSswap (all Settled, distinct ranks, sorted inputs), any step:
1. Preserves rank at every position (no swap, rankDelta = identity)
2. Timer at every position is ≤ pre-step timer (timer only decrements)
These are the universal step properties needed by the variable descent. -/

theorem step_rank_preserved_of_InSswap
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (w : Fin n) :
    (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j w).1.rank =
      (D w).1.rank := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hij : i = j
  · subst hij; simp [Config.step]
  · have hsi := hS.toInSrank.allSettled i
    have hsj := hS.toInSrank.allSettled j
    have hne := fun h : (D i).1.rank = (D j).1.rank => hij (hS.toInSrank.ranks_inj h)
    have h_no_swap := hS.swap_condition_false i j
    have h_rank := transitionPEM_rank_of_no_swap (trank := Rmax) (Rmax := Rmax)
      (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0))
      hsi hsj h_no_swap hne
    by_cases hwi : w = i
    · rw [hwi]
      have h_fst := Config.step_fst_state P D hij
      exact congrArg AgentState.rank h_fst ▸ h_rank.1
    · by_cases hwj : w = j
      · rw [hwj]
        have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
        exact congrArg AgentState.rank h_snd ▸ h_rank.2
      · -- bystander
        unfold Config.step; simp [hij, hwi, hwj]

set_option maxHeartbeats 8000000 in
theorem step_timer_le_of_InSswap
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (w : Fin n) :
    (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j w).1.timer ≤
      (D w).1.timer := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  by_cases hij : i = j
  · subst hij; simp [Config.step]
  · by_cases hwi : w = i
    · rw [hwi]
      have h_fst := Config.step_fst_state P D hij
      rw [show (D.step P i j i).1.timer = ((P.δ (D i, D j)).1).timer from
        congrArg AgentState.timer h_fst]
      -- Unfold P.δ = transitionPEM and show timer ≤
      show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
        (D i, D j)).1.timer ≤ (D i).1.timer
      have hsi := hS.toInSrank.allSettled i
      have hsj := hS.toInSrank.allSettled j
      have hne := fun h : (D i).1.rank = (D j).1.rank => hij (hS.toInSrank.ranks_inj h)
      have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hne
      have h_no_swap := hS.swap_condition_false i j
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false,
        and_self, if_true, h_no_swap]
      by_cases hpar : n % 2 = 0
      · simp only [hpar, if_true]
        split_ifs <;> dsimp only [] <;> omega
      · simp only [hpar, if_false]
        split_ifs <;> dsimp only [] <;> omega
    · by_cases hwj : w = j
      · rw [hwj]
        have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
        rw [show (D.step P i j j).1.timer = ((P.δ (D i, D j)).2).timer from
          congrArg AgentState.timer h_snd]
        show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
          (D i, D j)).2.timer ≤ (D j).1.timer
        have hsi := hS.toInSrank.allSettled i
        have hsj := hS.toInSrank.allSettled j
        have hne := fun h : (D i).1.rank = (D j).1.rank => hij (hS.toInSrank.ranks_inj h)
        have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hne
        have h_no_swap := hS.swap_condition_false i j
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap]
        by_cases hpar : n % 2 = 0
        · simp only [hpar, if_true]
          split_ifs <;> dsimp only [] <;> omega
        · simp only [hpar, if_false]
          split_ifs <;> dsimp only [] <;> omega
      · -- bystander
        unfold Config.step; simp [hij, hwi, hwj]

/-! From InSswap, if the step output is also InSswap (no reset fired),
then the answer at position w is either unchanged (bystander) or
opinionToAnswer(input) (median agent via phase4_decide). For median
agents, opinionToAnswer(input) = majorityAnswer (from InSswap sorted). -/
set_option maxHeartbeats 16000000 in
theorem step_median_answer_of_InSswap_both
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n) (hn4 : 4 ≤ n)
    {D : Config (AgentState n) Opinion n}
    (hS : InSswap D) {i j : Fin n}
    (hS' : InSswap (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j))
    (hM : MedianAnswerCorrect D) :
    MedianAnswerCorrect (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  have hmaj : majorityAnswer (D.step P i j) = majorityAnswer D := by
    simpa [P, PEMProtocolCoupled, PEMProtocol] using
      majorityAnswer_step_eq (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0) D i j
  intro ν hν; rw [hmaj]
  have hν_pre : (D ν).1.rank.val + 1 = ceilHalf n := by
    rw [← step_rank_preserved_of_InSswap (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) hn0 hS ν]; exact hν
  -- XHUANG_PROOF_V2_SENTINEL: do not overwrite
  by_cases hij : i = j
  · subst hij; simp [Config.step]; exact hM ν hν_pre
  have hsi := hS.toInSrank.allSettled i
  have hsj := hS.toInSrank.allSettled j
  have hrij : (D i).1.rank ≠ (D j).1.rank :=
    fun h => hij (hS.toInSrank.ranks_inj h)
  have hRD := rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn0) (D i).1 (D j).1 hsi hsj hrij
  have h_no_swap := hS.swap_condition_false i j
  have h_tie_outT : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 ≠ (D ν').2 → majorityAnswer D = .outT := by
    intro μ ν' hμR hν'R hpar hdis
    have h_sum := nAOf_add_nBOf D
    have hnA : nAOf D = n / 2 := by
      rcases hxμ : (D μ).2 with _ | _
      · have h1 : (D μ).1.rank.val < nAOf D := (hS.input_rank μ).mp hxμ
        have hxν' : (D ν').2 = Opinion.B := by
          cases hν2 : (D ν').2 with
          | A => exfalso; apply hdis; rw [hxμ, hν2]
          | B => rfl
        have h2 : ¬ ((D ν').1.rank.val < nAOf D) := by
          intro h; have := (hS.input_rank ν').mpr h
          rw [hxν'] at this; cases this
        omega
      · have h1 : ¬ ((D μ).1.rank.val < nAOf D) := by
          intro h; have := (hS.input_rank μ).mpr h
          rw [hxμ] at this; cases this
        have hxν' : (D ν').2 = Opinion.A := by
          cases hν2 : (D ν').2 with
          | A => rfl
          | B => exfalso; apply hdis; rw [hxμ, hν2]
        have h2 : (D ν').1.rank.val < nAOf D := (hS.input_rank ν').mp hxν'
        omega
    have hnB : nBOf D = n / 2 := by omega
    unfold majorityAnswer; simp [hnA, hnB]
  have h_agree_majA : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 = (D ν').2 → (D μ).2 = Opinion.A →
      nAOf D > nBOf D := by
    intro μ ν' hμR hν'R hpar hag hA
    have h_sum := nAOf_add_nBOf D
    have hν'A : (D ν').2 = Opinion.A := by rw [← hag]; exact hA
    have hν'_lt : (D ν').1.rank.val < nAOf D := (hS.input_rank ν').mp hν'A
    omega
  have h_agree_majB : ∀ (μ ν' : Fin n),
      (D μ).1.rank.val + 1 = n / 2 → (D ν').1.rank.val + 1 = n / 2 + 1 →
      n % 2 = 0 → (D μ).2 = (D ν').2 → (D μ).2 = Opinion.B →
      nBOf D > nAOf D := by
    intro μ ν' hμR hν'R hpar hag hB
    have h_sum := nAOf_add_nBOf D
    have hμB : (D μ).2 = Opinion.B := hB
    have hμ_not_A : ¬ ((D μ).1.rank.val < nAOf D) := by
      intro h; have := (hS.input_rank μ).mpr h
      rw [hμB] at this; cases this
    omega
  by_cases hνi : ν = i
  · subst hνi
    have h_fst := Config.step_fst_state P D hij
    rw [show (D.step P ν j ν).1.answer = ((P.δ (D ν, D j)).1).answer from
      congrArg AgentState.answer h_fst]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
      (D ν, D j)).1.answer = majorityAnswer D
    have hrank_νj : (D ν).1.rank.val ≠ (D j).1.rank.val := by
      intro h; apply hij
      exact hS.toInSrank.ranks_inj (Fin.ext h)
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hνR : (D ν).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hν_pre
      have hνR_ceil : (D ν).1.rank.val + 1 = ceilHalf n := hν_pre
      have hN_ne1 : ¬ (n / 2 + 1 = n / 2) := by omega
      have hN_ne2 : ¬ (n / 2 = n / 2 + 1) := by omega
      by_cases hjR : (D j).1.rank.val + 1 = n / 2 + 1
      · by_cases hxeq : (D ν).2 = (D j).2
        · have htr := transitionPEM_at_median_pair_even_agreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) (hn := hn0)) hsi hsj hpar hνR hjR hxeq hn4
          rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D ν, D j)).1.answer = opinionToAnswer (D ν).2 from
            congrArg AgentState.answer (congrArg Prod.fst htr)]
          exact opinionToAnswer_lower_median_eq_majorityAnswer_even
            hS hνR hpar (by
              rcases hx : (D ν).2 with _ | _
              · have := h_agree_majA ν j hνR hjR hpar hxeq hx; omega
              · have := h_agree_majB ν j hνR hjR hpar hxeq hx; omega)
        · have h_no_swap_disagree : ¬ ((D ν).2 = Opinion.B ∧ (D j).2 = Opinion.A) := by
            intro ⟨hxνB, hxjA⟩
            have h_nA_lo : ¬ ((D ν).1.rank.val < nAOf D) := by
              intro h; have := (hS.input_rank ν).mpr h
              rw [hxνB] at this; cases this
            have h_nA_hi : (D j).1.rank.val < nAOf D := (hS.input_rank j).mp hxjA
            omega
          have htr := transitionPEM_at_median_pair_even_disagreed_inputs
            (trank := Rmax) (Rmax := Rmax)
            (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn0)
            (rankDeltaOSSR_satisfies_fix (Rmax := Rmax) (Emax := Emax)
              (Dmax := Dmax) (hn := hn0)) hsi hsj hpar hνR hjR hxeq
            h_no_swap_disagree hn4
          rw [show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
            (D ν, D j)).1.answer = .outT from
            congrArg AgentState.answer (congrArg Prod.fst htr)]
          exact (h_tie_outT ν j hνR hjR hpar hxeq).symm
      · have hM_ν := hM ν hν_pre
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hjR, hN_ne1, hN_ne2,
          hνR_ceil]
        split_ifs <;> (first | exact hM_ν | simp_all)
    · have hjR_no_med : ¬ ((D j).1.rank.val + 1 = ceilHalf n) := by
        intro h; apply hrank_νj
        have : (D ν).1.rank.val + 1 = (D j).1.rank.val + 1 := by rw [hν_pre, h]
        omega
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_false, if_false,
        and_self, if_true, h_no_swap, hpar, hν_pre, hjR_no_med]
      have hOdd := opinionToAnswer_median_eq_majorityAnswer_odd hS hν_pre hpar
      split_ifs <;> exact hOdd
  by_cases hνj : ν = j
  · subst hνj
    have h_snd := Config.step_snd_state P D hij (Ne.symm hij)
    rw [show (D.step P i ν ν).1.answer = ((P.δ (D i, D ν)).2).answer from
      congrArg AgentState.answer h_snd]
    show (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn0)
      (D i, D ν)).2.answer = majorityAnswer D
    have hrank_iν : (D i).1.rank.val ≠ (D ν).1.rank.val := by
      intro h; apply hij
      exact hS.toInSrank.ranks_inj (Fin.ext h)
    by_cases hpar : n % 2 = 0
    · have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
      have hνR : (D ν).1.rank.val + 1 = n / 2 := by rw [← hceil]; exact hν_pre
      have hνR_ceil : (D ν).1.rank.val + 1 = ceilHalf n := hν_pre
      have hN_ne1 : ¬ (n / 2 + 1 = n / 2) := by omega
      have hN_ne2 : ¬ (n / 2 = n / 2 + 1) := by omega
      by_cases hiR : (D i).1.rank.val + 1 = n / 2 + 1
      · have hiR_no_med : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
          rw [hceil]; omega
        have hiR_no_max : ¬ ((D i).1.rank.val + 1 = n) := by omega
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hiR, hN_ne1, hN_ne2,
          hνR_ceil, hiR_no_med, hiR_no_max]
        by_cases hxeq : (D i).2 = (D ν).2
        · simp only [hxeq, if_true]
          have hAns := opinionToAnswer_lower_median_eq_majorityAnswer_even
            hS hνR hpar (by
              rcases hx : (D ν).2 with _ | _
              · have := h_agree_majA ν i hνR hiR hpar hxeq.symm hx; omega
              · have := h_agree_majB ν i hνR hiR hpar hxeq.symm hx; omega)
          split_ifs <;> exact hAns
        · simp only [hxeq, show ¬((D ν).2 = (D i).2) from Ne.symm hxeq, if_false]
          have hOutT := (h_tie_outT ν i hνR hiR hpar (Ne.symm hxeq)).symm
          split_ifs <;> exact hOutT
      · have hM_ν := hM ν hν_pre
        have hiR_ne_med : ¬ ((D i).1.rank.val + 1 = n / 2) := by
          intro h; apply hrank_iν
          have : (D i).1.rank.val + 1 = (D ν).1.rank.val + 1 := by rw [h, hνR]
          omega
        have hiR_ne_med_ceil : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
          rw [hceil]; exact hiR_ne_med
        unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
          phase4_swap phase4_decide phase4_propagate
        simp only [hRD, hsi, hsj, ne_eq,
          role_settled_ne_resetting,
          not_true_eq_false, not_false_eq_true,
          false_and, and_false, if_false,
          and_self, if_true, h_no_swap, hpar, hνR, hiR, hN_ne1, hN_ne2,
          hνR_ceil, hiR_ne_med, hiR_ne_med_ceil]
        split_ifs <;> (first | exact hM_ν | simp_all)
    · have hiR_no_med : ¬ ((D i).1.rank.val + 1 = ceilHalf n) := by
        intro h; apply hrank_iν
        have : (D i).1.rank.val + 1 = (D ν).1.rank.val + 1 := by rw [h, hν_pre]
        omega
      unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
        phase4_swap phase4_decide phase4_propagate
      simp only [hRD, hsi, hsj, ne_eq,
        role_settled_ne_resetting,
        not_true_eq_false, not_false_eq_true,
        false_and, and_self, if_false,
        and_false, if_true, h_no_swap, hpar, hν_pre, hiR_no_med]
      have hOdd := opinionToAnswer_median_eq_majorityAnswer_odd hS hν_pre hpar
      split_ifs <;> exact hOdd
  · have hbyst : D.step P i j ν = D ν := by
      unfold Config.step; simp [hij, hνi, hνj]
    rw [show (D.step P i j ν).1.answer = (D ν).1.answer from
      congrArg (fun x => x.1.answer) hbyst]
    exact hM ν hν_pre

/-! Phase C.2: Median-correct sub-phase (timer drain → seed → epidemic).
From InSswap + MedianAnswerCorrect + timer≥1 + wrongAnswer > 0:
E[T to consensus] ≤ O(Rmax·n²). Uses epidemic reachability. -/

/-! Phase C.2 sub-decomposition (median correct → consensus):

Sub-phase C.2a: Timer drain. From InSswap + MedianCorrect + timer≥1:
  potential = medianTimer, descent at (median,max) pair.
  E[T to timer=0 ∨ consensus] ≤ timer · n(n-1) ≤ 7(Rmax+4) · n(n-1)

Sub-phase C.2b: Reset seed creation. When timer=0 + answers disagree:
  One (median,max) interaction triggers reset → CorrectResetSeed.
  E[T to CorrectResetSeed ∨ consensus] ≤ n(n-1)

Sub-phase C.2c: Epidemic propagation. From CorrectResetSeed:
  potential = nonResettingCount, descent via propagate-reset.
  E[T to all-resetting ∨ consensus] ≤ n · n(n-1)

Sub-phase C.2d: Re-ranking + consensus. From all-resetting with correct answer:
  potential = resetFuel → ranking → InSswap → consensus.
  E[T] ≤ O(Rmax · n²)

Total: O(Rmax · n²). -/

/-! Stage 1: Timer drain. Inv = InSswap ∧ MedianCorrect ∧ timer≥1,
φ = medianTimer. Each (median,max) step decreases timer. -/

/-! φ for timer drain (moved to PolynomialBound.lean). -/

end SSEM
