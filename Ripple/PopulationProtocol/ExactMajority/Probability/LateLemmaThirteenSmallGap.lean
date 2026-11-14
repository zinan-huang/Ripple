-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaThirteenSmallGap.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaThirteenRoute
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseWinDrain
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeAveragingStops
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandDropSum
import Ripple.PopulationProtocol.ExactMajority.Probability.WeightedDriftDropSum

/-!
# Lemma 13: Phase-8 minority drain

From `LateLemmaThirteenDeterministic` and `LateLemmaThirteenRoute` we use:

* `latePhaseEightCredit`, `phaseEightFullCount`;
* `LemmaThirteenRouteReceipt` and
  `exists_lemmaThirteenRouteReceipt_of_smallHistory`;
* `lemmaThirteenRouteReceipt_bounds_at`, giving the `.544 M` credit,
  depth invariant, and homogeneous Phase-8 window at every requested time;
* `PhaseEightFiniteReceipt.work_before_nine`.

The stopped original-law argument is
`PhaseThreeAveragingStops.potential_drift_tail_at_pastTime`, with start
`homogeneousLatePhaseStart init 8`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaThirteenSmallGap

open TimeTheorem PairLog TraceDrain StageEventSpec
open PhaseOneDrain PhaseOneDrainStopping
open Phase7BandDefs Phase7MajorityBlockLedger
open Phase7Convergence Phase8WitnessSupply
open LateBiasedResourceCredit
open LateBiasedResourceCreditPhaseSeven
open LateLemmaTwelveSmallGap
open LateLemmaThirteenDeterministic
open LateLemmaThirteenRoute
open LateTimerUpperOriginalLaw
open LateTimerProtectionOriginalLaw

variable {L K n M R : ℕ}

/-! ## Compatible availability from J₈ -/

private theorem block_shallow_or_full
    (sigma : Sign) (ell : Fin (L + 1)) (a : AgentState L K)
    (hphase : a.phase.val = 8)
    (hblock : a ∈ majorityBand3 (L := L) (K := K) sigma ell.val) :
    majorityShallowSt (L := L) (K := K) sigma ell.val a ∨
      phaseEightFullSt a := by
  rw [majorityBand3, Finset.mem_filter] at hblock
  obtain ⟨_, hm, st, j, hst, hb, hlo, hhi⟩ := hblock
  by_cases hf : a.full
  · exact Or.inr ⟨hphase, hm, hf⟩
  · exact Or.inl ⟨hm, hf, st, j, hst, by omega, hb⟩

/-- Every fixed-block agent is either a compatible unused partner or is paid
for by `F₈`. -/
theorem majorityBlockCount_le_shallow_add_full
    (sigma : Sign) (ell : Fin (L + 1))
    {population : ℕ} {c : Config (AgentState L K)}
    (hEight : PhaseOnlyWindows.Phase8Win (L := L) (K := K) population c) :
    majorityBlockCount sigma ell.val c ≤
      majorityShallowCount sigma ell.val c + phaseEightFullCount c := by
  classical
  induction c using Multiset.induction_on generalizing population with
  | empty =>
      simp [majorityBlockCount, majorityShallowCount, phaseEightFullCount]
  | cons a c ih =>
      have haEight := hEight.2 a (by simp)
      have hcEight : PhaseOnlyWindows.Phase8Win
          (L := L) (K := K) c.card c :=
        ⟨rfl, fun b hb => hEight.2 b (by simp [hb])⟩
      have ih' := ih hcEight
      unfold majorityBlockCount majorityShallowCount phaseEightFullCount at ih' ⊢
      rw [Multiset.countP_cons, Multiset.countP_cons,
        Multiset.countP_cons]
      by_cases hq : a ∈ majorityBand3
          (L := L) (K := K) sigma ell.val
      · rcases block_shallow_or_full sigma ell a haEight hq with hsh | hfull
        · have hnfull : ¬ phaseEightFullSt a := fun h => hsh.2.1 h.2.2
          simp [hq, hsh, hnfull]
          omega
        · have hnsh : ¬ majorityShallowSt
              (L := L) (K := K) sigma ell.val a :=
            fun h => h.2.1 hfull.2.2
          simp [hq, hfull, hnsh]
          omega
      · simp [hq]
        omega

private theorem latePhaseEightCredit_le_core
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (c : Config (AgentState L K)) :
    latePhaseEightCredit sigma ell hell c ≤
      2 * (majorityBlockCount sigma ell.val c : ℤ) -
        (Lemma613OFloor.phase3BiasedMainCount c : ℤ) -
        (phaseEightFullCount c : ℤ) := by
  unfold latePhaseEightCredit lateBiasedResourceCredit phaseSixCharge
  omega

/-- Correct compatible form of (56). -/
theorem latePhaseEightCredit_le_shallowExcess
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {population : ℕ} {c : Config (AgentState L K)}
    (hEight : PhaseOnlyWindows.Phase8Win (L := L) (K := K) population c) :
    latePhaseEightCredit sigma ell hell c ≤
      (majorityShallowCount sigma ell.val c : ℤ) -
        (minorityU sigma c : ℤ) := by
  have hcore := latePhaseEightCredit_le_core sigma ell hell c
  have hpart := biasedMainCount_eq_majority_add_minority sigma c
  have hQA := majorityBlockCount_le_majorityBiasedCount sigma ell c
  have hQSF := majorityBlockCount_le_shallow_add_full sigma ell hEight
  have hpartZ :
      (Lemma613OFloor.phase3BiasedMainCount c : ℤ) =
        (majorityBiasedCount sigma c : ℤ) + (minorityU sigma c : ℤ) := by
    exact_mod_cast hpart
  have hQAZ :
      (majorityBlockCount sigma ell.val c : ℤ) ≤
        (majorityBiasedCount sigma c : ℤ) := by
    exact_mod_cast hQA
  have hQSFZ :
      (majorityBlockCount sigma ell.val c : ℤ) ≤
        (majorityShallowCount sigma ell.val c : ℤ) +
          (phaseEightFullCount c : ℤ) := by
    exact_mod_cast hQSF
  omega

/-- `.26112 n` compatible unused partners in excess of the current minority. -/
theorem phaseEightShallowAvailability_scaled
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {population mainCount : ℕ} {c : Config (AgentState L K)}
    (hpopulation : 1 ≤ population)
    (hmain : 12 * population ≤ 25 * mainCount)
    (hEight : PhaseOnlyWindows.Phase8Win
      (L := L) (K := K) population c)
    (hcredit : (544 : ℤ) * (mainCount : ℤ) ≤
      1000 * latePhaseEightCredit sigma ell hell c) :
    minorityU sigma c ≤ majorityShallowCount sigma ell.val c ∧
      26112 * population ≤
        100000 * (majorityShallowCount sigma ell.val c -
          minorityU sigma c) := by
  let A := majorityShallowCount sigma ell.val c
  let B := minorityU sigma c
  have hcreditExcess :
      (544 : ℤ) * (mainCount : ℤ) ≤
        1000 * ((A : ℤ) - (B : ℤ)) := by
    exact hcredit.trans
      (mul_le_mul_of_nonneg_left
        (latePhaseEightCredit_le_shallowExcess sigma ell hell hEight)
        (by norm_num))
  have hmainZ : (12 : ℤ) * population ≤ 25 * mainCount := by
    exact_mod_cast hmain
  have hscaledZ :
      (26112 : ℤ) * population ≤
        100000 * ((A : ℤ) - (B : ℤ)) := by
    nlinarith
  have hBA : B ≤ A := by
    by_contra hnot
    have hneg : (A : ℤ) - (B : ℤ) < 0 := by
      have := Nat.lt_of_not_ge hnot
      omega
    have hpositive : (0 : ℤ) < 26112 * population := by
      exact mul_pos (by norm_num) (by exact_mod_cast hpopulation)
    nlinarith
  refine ⟨hBA, ?_⟩
  exact_mod_cast hscaledZ

/-! ## Ready gate and one-step drift -/

structure PhaseEightDrainReady
    (n M : ℕ) (sigma : Sign)
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (c : Config (AgentState L K)) : Prop where
  phase_win : PhaseOnlyWindows.Phase8Win (L := L) (K := K) n c
  deep : AllMinorityIndicesAbove sigma ell c
  credit_scaled : (544 : ℤ) * (M : ℤ) ≤
    1000 * latePhaseEightCredit sigma ell hell c

open Classical in
def phaseEightShallowStates
    (sigma : Sign) (ell : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter
    (majorityShallowSt (L := L) (K := K) sigma ell.val)

open Classical in
def phaseEightMinorityStates
    (sigma : Sign) : Finset (AgentState L K) :=
  Finset.univ.filter (minoritySt sigma)

private theorem shallow_minority_disjoint
    (sigma : Sign) (ell : Fin (L + 1)) :
    Disjoint (phaseEightShallowStates (L := L) (K := K) sigma ell)
      (phaseEightMinorityStates (L := L) (K := K) sigma) := by
  classical
  rw [Finset.disjoint_left]
  intro a hsh hmin
  simp only [phaseEightShallowStates, phaseEightMinorityStates,
    Finset.mem_filter, Finset.mem_univ, true_and] at hsh hmin
  rcases hsh with ⟨_, _, st, j, hst, _, hsb⟩
  rcases hmin with ⟨_, i, hmb⟩
  rw [hmb] at hsb
  injection hsb with hs _
  exact hst hs.symm

private theorem shallowStates_sum
    (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K)) :
    (phaseEightShallowStates (L := L) (K := K) sigma ell).sum c.count =
      majorityShallowCount sigma ell.val c := by
  simpa [phaseEightShallowStates] using
    (majorityShallowCount_eq_sum
      (L := L) (K := K) sigma ell.val c).symm

private theorem minorityStates_sum
    (sigma : Sign) (c : Config (AgentState L K)) :
    (phaseEightMinorityStates (L := L) (K := K) sigma).sum c.count =
      minorityU sigma c := by
  unfold minorityU
  simpa [phaseEightMinorityStates] using
    (Phase6Convergence.countP_eq_sum_count6
      (L := L) (K := K) (minoritySt sigma) c).symm

private theorem countP_stepOrSelf_drop_of_pair
    (P : AgentState L K → Prop) [DecidablePred P]
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hpair : Multiset.countP P
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) + 1 ≤
      Multiset.countP P ({s, t} : Multiset (AgentState L K))) :
    Multiset.countP P
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1 ≤
      Multiset.countP P c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le : Multiset.countP P ({s, t} : Multiset (AgentState L K)) ≤
      Multiset.countP P c := Multiset.countP_le_of_le _ hsub
  omega

/-- The reverse scheduler orientation: shallow absorber first, minority second. -/
private theorem transition_pair_drop_shallow_first
    (sigma : Sign) (ell : Fin (L + 1))
    (s t : AgentState L K)
    (hsEight : s.phase.val = 8) (htEight : t.phase.val = 8)
    (hsh : majorityShallowSt (L := L) (K := K) sigma ell.val s)
    (hmin : minoritySt sigma t)
    (hdeep : ∀ i : Fin (L + 1),
      t.bias = Bias.dyadic sigma i → ell.val + 2 < i.val) :
    Multiset.countP (minoritySt sigma)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) + 1 ≤
      Multiset.countP (minoritySt sigma)
        ({s, t} : Multiset (AgentState L K)) := by
  classical
  rcases hsh with ⟨hsMain, hsUnfull, st, j, hst, hj, hsb⟩
  rcases hmin with ⟨htMain, i, htb⟩
  have hji : j.val < i.val := by
    have := hdeep i htb
    omega
  rw [Phase8Convergence.Transition_eq_absorbConsume_of_phase8_main
    s t hsEight htEight hsMain htMain]
  have hshape : absorbConsume L K s t =
      ({s with full := true}, {t with bias := Bias.zero}) := by
    cases st <;> cases sigma
    · exact (hst rfl).elim
    · unfold absorbConsume
      rw [hsb, htb]
      simp only [if_pos (show j.val < i.val ∧ ¬ s.full = true from ⟨hji, hsUnfull⟩)]
    · unfold absorbConsume
      rw [hsb, htb]
      simp only [if_pos (show j.val < i.val ∧ ¬ s.full = true from ⟨hji, hsUnfull⟩)]
    · exact (hst rfl).elim
  rw [hshape, countP_minoritySt_pair, countP_minoritySt_pair]
  have hsnot : ¬ minoritySt sigma s := by
    rw [minoritySt_iff]
    rintro ⟨_, hb⟩
    rw [hsb] at hb
    simp only [biasIsSigned] at hb
    exact hst hb
  have houtS : ¬ minoritySt sigma ({s with full := true}) :=
    fun h => hsnot ((minoritySt_full_true sigma s).mp h)
  have houtT : ¬ minoritySt sigma ({t with bias := Bias.zero}) :=
    not_minoritySt_bias_zero sigma t
  have htmin : minoritySt sigma t := ⟨htMain, i, htb⟩
  rw [if_neg houtS, if_neg houtT, if_neg hsnot, if_pos htmin]

private theorem minorityU_drop_shallow_first
    (sigma : Sign) (ell : Fin (L + 1)) (n : ℕ)
    (c : Config (AgentState L K))
    (hEight : PhaseOnlyWindows.Phase8Win (L := L) (K := K) n c)
    (hdeep : AllMinorityIndicesAbove sigma ell c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsh : majorityShallowSt (L := L) (K := K) sigma ell.val s)
    (hmin : minoritySt sigma t) :
    minorityU sigma (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1 ≤
      minorityU sigma c := by
  have hsMem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have htMem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hsEight := hEight.2 s hsMem
  have htEight := hEight.2 t htMem
  have htDeep : ∀ i : Fin (L + 1),
      t.bias = Bias.dyadic sigma i → ell.val + 2 < i.val :=
    fun i hb => hdeep t htMem hmin.1 i hb
  unfold minorityU
  exact countP_stepOrSelf_drop_of_pair (minoritySt sigma) c s t happ
    (transition_pair_drop_shallow_first
      sigma ell s t hsEight htEight hsh hmin htDeep)

private theorem interactionProb_le_weightedDrop
    (Phi : Config (AgentState L K) → ℕ)
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (hdrop : Phi (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1 ≤
      Phi c) :
    c.interactionProb s t ≤
      ((Phi c : ℝ≥0∞) -
        (Phi (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ≥0∞)) *
        c.interactionProb s t := by
  have hdropNat : 1 ≤ Phi c -
      Phi (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
    omega
  have hdropE : (1 : ℝ≥0∞) ≤
      (Phi c : ℝ≥0∞) -
        (Phi (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ≥0∞) := by
    have hcast : (1 : ℝ≥0∞) ≤
        ((Phi c - Phi (Protocol.stepOrSelf
          (NonuniformMajority L K) c s t) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hdropNat
    simpa only [ENNReal.natCast_sub] using hcast
  calc
    c.interactionProb s t = 1 * c.interactionProb s t := by rw [one_mul]
    _ ≤ _ := by gcongr

set_option maxHeartbeats 800000 in
/-- Generic two-orientation rectangle lower bound.  The scoped heartbeat allowance covers
the two ordered rectangle sums over a generic potential, elaborated in one declaration. -/
theorem twoRectangle_weightedDropSum
    (Phi : Config (AgentState L K) → ℕ)
    (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcard : c.card = n)
    (A B : Finset (AgentState L K)) (hdisj : Disjoint A B)
    (hAB : ∀ p ∈ A ×ˢ B, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 →
      Phi (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1 ≤ Phi c)
    (hBA : ∀ p ∈ B ×ˢ A, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 →
      Phi (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1 ≤ Phi c) :
    ENNReal.ofReal
        (((2 * (A.sum c.count * B.sum c.count) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      WeightedDriftDropSum.weightedDropSum
        (NonuniformMajority L K) Phi c := by
  classical
  let drop : AgentState L K × AgentState L K → ℝ≥0∞ := fun p =>
    (Phi c : ℝ≥0∞) -
      (Phi (Protocol.stepOrSelf
        (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)
  let Rab := A ×ˢ B
  let Rba := B ×ˢ A
  have hRdisj : Disjoint Rab Rba :=
    Finset.disjoint_product.mpr (Or.inl hdisj)
  have htermAB : ∀ p ∈ Rab,
      c.interactionProb p.1 p.2 ≤ drop p * c.interactionProb p.1 p.2 := by
    intro p hp
    have hp' : p ∈ A ×ˢ B := hp
    rw [Finset.mem_product] at hp'
    obtain ⟨ha, hb⟩ := hp'
    have hne : p.1 ≠ p.2 := by
      intro h
      rw [← h] at hb
      exact Finset.disjoint_left.mp hdisj ha hb
    by_cases hca : 1 ≤ c.count p.1
    · by_cases hcb : 1 ≤ c.count p.2
      · exact interactionProb_le_weightedDrop Phi c p.1 p.2
          (hAB p hp hca hcb)
      · have hz : c.count p.2 = 0 := by omega
        simp [drop, Config.interactionProb, Config.interactionCount, hne, hz]
    · have hz : c.count p.1 = 0 := by omega
      simp [drop, Config.interactionProb, Config.interactionCount, hne, hz]
  have htermBA : ∀ p ∈ Rba,
      c.interactionProb p.1 p.2 ≤ drop p * c.interactionProb p.1 p.2 := by
    intro p hp
    have hp' : p ∈ B ×ˢ A := hp
    rw [Finset.mem_product] at hp'
    obtain ⟨hb, ha⟩ := hp'
    have hne : p.1 ≠ p.2 := by
      intro h
      rw [h] at hb
      exact Finset.disjoint_left.mp hdisj ha hb
    by_cases hcb : 1 ≤ c.count p.1
    · by_cases hca : 1 ≤ c.count p.2
      · exact interactionProb_le_weightedDrop Phi c p.1 p.2
          (hBA p hp hcb hca)
      · have hz : c.count p.2 = 0 := by omega
        simp [drop, Config.interactionProb, Config.interactionCount, hne, hz]
    · have hz : c.count p.1 = 0 := by omega
      simp [drop, Config.interactionProb, Config.interactionCount, hne, hz]
  have hsumAB := Phase7BandDropSum.sum_interactionProb_cross_disjoint
    n c hcard A B
      (fun a ha b hb hab => Finset.disjoint_left.mp hdisj ha (hab ▸ hb))
  have hsumBA := Phase7BandDropSum.sum_interactionProb_cross_disjoint
    n c hcard B A
      (fun b hb a ha hab => Finset.disjoint_left.mp hdisj ha (hab ▸ hb))
  have hprob :
      ENNReal.ofReal
          (((2 * (A.sum c.count * B.sum c.count) : ℕ) : ℝ) /
            ((n : ℝ) * ((n : ℝ) - 1))) =
        (∑ p ∈ Rab, c.interactionProb p.1 p.2) +
          ∑ p ∈ Rba, c.interactionProb p.1 p.2 := by
    rw [Phase7BandDropSum.ofReal_phase7_rate_eq
      n (A.sum c.count * B.sum c.count) hn,
      show Rab = A ×ˢ B from rfl, show Rba = B ×ˢ A from rfl,
      hsumAB, hsumBA]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hprob]
  calc
    (∑ p ∈ Rab, c.interactionProb p.1 p.2) +
        ∑ p ∈ Rba, c.interactionProb p.1 p.2 ≤
      (∑ p ∈ Rab, drop p * c.interactionProb p.1 p.2) +
        ∑ p ∈ Rba, drop p * c.interactionProb p.1 p.2 :=
      add_le_add
        (Finset.sum_le_sum fun p hp => htermAB p hp)
        (Finset.sum_le_sum fun p hp => htermBA p hp)
    _ = ∑ p ∈ Rab ∪ Rba, drop p * c.interactionProb p.1 p.2 :=
      (Finset.sum_union hRdisj).symm
    _ ≤ ∑ p : AgentState L K × AgentState L K,
        drop p * c.interactionProb p.1 p.2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
      intro p _ _
      exact bot_le
    _ = WeightedDriftDropSum.weightedDropSum
        (NonuniformMajority L K) Phi c := rfl

/-- The paper rate `.52224 / n`. -/
def phaseEightDrainRate (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1632 / 3125 : ℝ) / (n : ℝ))

def phaseEightDrainHorizon (n : ℕ) : ℕ := logWindow n 8

def phaseEightDrainBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (n : ℝ) (-(9931 / 3125 : ℝ)))

private theorem phaseEightDrainRate_le_shallowRate
    (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (c : Config (AgentState L K))
    (h : PhaseEightDrainReady n M sigma ell hell c) :
    phaseEightDrainRate n ≤
      ENNReal.ofReal
        (((2 * majorityShallowCount sigma ell.val c : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) := by
  have havail := phaseEightShallowAvailability_scaled
    sigma ell hell (by omega) hM h.phase_win h.credit_scaled
  have hSscaled : 26112 * n ≤
      100000 * majorityShallowCount sigma ell.val c := by
    omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos hnpos (by linarith)
  have hSreal :
      (816 / 3125 : ℝ) * (n : ℝ) ≤
        (majorityShallowCount sigma ell.val c : ℝ) := by
    have hcast : (26112 : ℝ) * (n : ℝ) ≤
        100000 * (majorityShallowCount sigma ell.val c : ℝ) := by
      exact_mod_cast hSscaled
    nlinarith
  unfold phaseEightDrainRate
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ hnpos hden).2
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hSreal hnpos.le, hnpos]

/-- Two ordered shallow/minority rectangles give multiplicative drift. -/
theorem phaseEightDrainDrift
    (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) :
    DyadicMassDrainTight.WeightedDyadicMassDrift
      (L := L) (K := K)
      (fun c => PhaseEightDrainReady n M sigma ell hell c)
      (fun c => minorityU sigma c)
      (1 - phaseEightDrainRate n) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_on_of_dropSum
    (L := L) (K := K)
    (fun c => PhaseEightDrainReady n M sigma ell hell c)
    (fun c => minorityU sigma c)
    (phaseEightDrainRate n) (by simp [phaseEightDrainRate]) ?_ ?_ ?_
  · intro c hc
    rw [hc.phase_win.1]
    exact hn
  · intro c hc pair
    exact PhaseOnlyWindows.minorityU_stepOrSelf_le_of_phase8Win
      sigma n c hc.phase_win pair.1 pair.2
  · intro c hc
    let A := phaseEightShallowStates (L := L) (K := K) sigma ell
    let B := phaseEightMinorityStates (L := L) (K := K) sigma
    let Phi : Config (AgentState L K) → ℕ := fun d => minorityU sigma d
    have hraw := twoRectangle_weightedDropSum
      (L := L) (K := K) Phi n hn c hc.phase_win.1 A B
      (by simpa [A, B] using
        (shallow_minority_disjoint (L := L) (K := K) sigma ell))
      (by
        intro p hp hca hcb
        rw [Finset.mem_product] at hp
        obtain ⟨hsh, hmin⟩ := hp
        have hsm : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hca
        have htm : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hcb
        have hne : p.1 ≠ p.2 := by
          intro heq
          exact Finset.disjoint_left.mp
            (shallow_minority_disjoint (L := L) (K := K) sigma ell)
            (show p.1 ∈ phaseEightShallowStates (L := L) (K := K) sigma ell
              from hsh)
            (show p.1 ∈ phaseEightMinorityStates (L := L) (K := K) sigma by
              rw [heq]; exact hmin)
        have happ := Phase7BandDropSum.applicable_of_mem_distinct hsm htm hne
        exact minorityU_drop_shallow_first sigma ell n c hc.phase_win hc.deep
          p.1 p.2 happ (by simpa [A, phaseEightShallowStates] using hsh)
          (by simpa [B, phaseEightMinorityStates] using hmin))
      (by
        intro p hp hcb hca
        rw [Finset.mem_product] at hp
        obtain ⟨hmin, hsh⟩ := hp
        have hsm : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hcb
        have htm : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hca
        have hmin' : minoritySt sigma p.1 := by
          simpa [B, phaseEightMinorityStates] using hmin
        have hsh' : majorityShallowSt
            (L := L) (K := K) sigma ell.val p.2 := by
          simpa [A, phaseEightShallowStates] using hsh
        rcases hmin' with ⟨hsMain, i, hsb⟩
        rcases hsh' with ⟨htMain, htFull, st, j, hst, hj, htb⟩
        have hi := hc.deep p.1 hsm hsMain i hsb
        have hji : j.val < i.val := by omega
        have hsEight := hc.phase_win.2 p.1 hsm
        have htEight := hc.phase_win.2 p.2 htm
        have hne : p.1 ≠ p.2 := by
          intro heq
          exact Finset.disjoint_left.mp
            (shallow_minority_disjoint (L := L) (K := K) sigma ell)
            (show p.2 ∈ phaseEightShallowStates (L := L) (K := K) sigma ell
              from hsh)
            (show p.2 ∈ phaseEightMinorityStates (L := L) (K := K) sigma by
              rw [← heq]; exact hmin)
        have happ := Phase7BandDropSum.applicable_of_mem_distinct hsm htm hne
        exact PhaseWinDrain.minorityU_stepOrSelf_drop_of_phase8Win
          sigma st c p.1 p.2 hsEight htEight hsMain htMain happ
          i j hsb htb hst hji htFull)
    have hA : A.sum c.count = majorityShallowCount sigma ell.val c := by
      simpa [A] using shallowStates_sum
        (L := L) (K := K) sigma ell c
    have hB : B.sum c.count = minorityU sigma c := by
      simpa [B] using minorityStates_sum
        (L := L) (K := K) sigma c
    have hrate := phaseEightDrainRate_le_shallowRate
      (L := L) (K := K) hn hM sigma ell hell c hc
    calc
      phaseEightDrainRate n * (minorityU sigma c : ℝ≥0∞) ≤
          ENNReal.ofReal
            (((2 * majorityShallowCount sigma ell.val c : ℕ) : ℝ) /
              ((n : ℝ) * ((n : ℝ) - 1))) *
            (minorityU sigma c : ℝ≥0∞) := by gcongr
      _ = ENNReal.ofReal
          (((2 * (majorityShallowCount sigma ell.val c *
              minorityU sigma c) : ℕ) : ℝ) /
            ((n : ℝ) * ((n : ℝ) - 1))) := by
        rw [Phase7BandDropSum.ofReal_phase7_rate_eq n
              (majorityShallowCount sigma ell.val c) hn,
            Phase7BandDropSum.ofReal_phase7_rate_eq n
              (majorityShallowCount sigma ell.val c * minorityU sigma c) hn]
        push_cast
        simp only [div_eq_mul_inv]
        ring
      _ = ENNReal.ofReal
          (((2 * (A.sum c.count * B.sum c.count) : ℕ) : ℝ) /
            ((n : ℝ) * ((n : ℝ) - 1))) := by rw [hA, hB]
      _ ≤ WeightedDriftDropSum.weightedDropSum
          (NonuniformMajority L K) Phi c := hraw

/-! ## Scalar calibration and random start -/

private theorem phaseEightRealBudgetIdentity
    (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * Real.exp
        (-(1632 / 3125 : ℝ) * 8 * Real.log (n : ℝ)) =
      Real.rpow (n : ℝ) (-(9931 / 3125 : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  calc
    (n : ℝ) * Real.exp
        (-(1632 / 3125 : ℝ) * 8 * Real.log (n : ℝ)) =
      Real.exp (Real.log (n : ℝ)) *
        Real.exp (-(1632 / 3125 : ℝ) * 8 * Real.log (n : ℝ)) := by
          rw [Real.exp_log hnpos]
    _ = Real.exp (Real.log (n : ℝ) +
        (-(1632 / 3125 : ℝ) * 8 * Real.log (n : ℝ))) := by
          rw [Real.exp_add]
    _ = Real.exp (Real.log (n : ℝ) * (-(9931 / 3125 : ℝ))) := by
          congr 1
          ring
    _ = Real.rpow (n : ℝ) (-(9931 / 3125 : ℝ)) :=
      (Real.rpow_def_of_pos hnpos (-(9931 / 3125 : ℝ))).symm

/-- `n exp(-.52224·8 ln n) = n^(-3.17792)`. -/
theorem phaseEightDrainScalar
    (n : ℕ) (hn : 2 ≤ n) :
    (1 - phaseEightDrainRate n) ^ phaseEightDrainHorizon n * n ≤
      phaseEightDrainBudget n := by
  let r : ℝ := (1632 / 3125 : ℝ) / (n : ℝ)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrone : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one hnpos).2
    linarith
  have hbase : 0 ≤ 1 - r := by linarith
  have hcast : 1 - phaseEightDrainRate n = ENNReal.ofReal (1 - r) := by
    unfold phaseEightDrainRate
    dsimp [r]
    rw [ENNReal.ofReal_sub _ hr, ENNReal.ofReal_one]
  rw [hcast, ← ENNReal.ofReal_pow hbase]
  rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) by
    exact (ENNReal.ofReal_natCast n).symm]
  rw [← ENNReal.ofReal_mul (pow_nonneg hbase _)]
  unfold phaseEightDrainBudget phaseEightDrainHorizon
  apply ENNReal.ofReal_le_ofReal
  have hceil : (8 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
      (logWindow n 8 : ℝ) := by
    unfold logWindow
    exact Nat.le_ceil _
  have hprod := mul_le_mul_of_nonneg_left hceil hr
  have hexp : (13056 / 3125 : ℝ) * Real.log (n : ℝ) ≤
      r * (logWindow n 8 : ℝ) := by
    have heq : r * ((8 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) =
        (13056 / 3125 : ℝ) * Real.log (n : ℝ) := by
      dsimp [r]
      field_simp [hnpos.ne']
      ring
    rwa [heq] at hprod
  calc
    (1 - r) ^ logWindow n 8 * (n : ℝ) ≤
        Real.exp (-r) ^ logWindow n 8 * (n : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_left₀ hbase
          (by linarith [Real.add_one_le_exp (-r)]) _
      · positivity
    _ = Real.exp (-(r * (logWindow n 8 : ℝ))) * (n : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ Real.exp
          (-(13056 / 3125 : ℝ) * Real.log (n : ℝ)) * (n : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.exp_le_exp.mpr (by linarith only [hexp])
      · positivity
    _ = (n : ℝ) * Real.exp
        (-(1632 / 3125 : ℝ) * 8 * Real.log (n : ℝ)) := by
      rw [mul_comm]
      congr 1
      congr 1
      ring
    _ = Real.rpow (n : ℝ) (-(9931 / 3125 : ℝ)) :=
      phaseEightRealBudgetIdentity n hn

/-- One fixed witness branch, started at the random homogeneous Phase-8 time. -/
def phaseEightDrainFailureAtPast
    (init : InputCfg n) (M : ℕ) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    Set (InputLog n) :=
  PhaseThreeAveragingStops.driftFailureAt init
    (homogeneousLatePhaseStart init 8)
    (minorityU sigma)
    (fun c => PhaseEightDrainReady n M sigma ell hell c)
    (phaseEightDrainHorizon n) n

private theorem measurableSet_trace_state
    (init : Cfg L K) (t : ℕ) (P : Cfg L K → Prop) :
    MeasurableSet {omega : Ω L K | P (trace init omega t)} :=
  (Set.to_countable {c : Cfg L K | P c}).measurableSet.preimage
    ((measurable_pi_apply t).comp (measurable_trace init))

private theorem measurableSet_ready_alive
    (init : InputCfg n) (M : ℕ) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (s : ℕ) :
    MeasurableSet {omega | ∀ u,
      s ≤ u → u < s + phaseEightDrainHorizon n →
        PhaseEightDrainReady n M sigma ell hell (trace init omega u)} := by
  rw [show {omega | ∀ u,
      s ≤ u → u < s + phaseEightDrainHorizon n →
        PhaseEightDrainReady n M sigma ell hell (trace init omega u)} =
      ⋂ u : ℕ, {omega |
        s ≤ u → u < s + phaseEightDrainHorizon n →
          PhaseEightDrainReady n M sigma ell hell
            (trace init omega u)} by ext omega; simp]
  apply MeasurableSet.iInter
  intro u
  by_cases hsu : s ≤ u
  · by_cases hut : u < s + phaseEightDrainHorizon n
    · simpa [hsu, hut] using measurableSet_trace_state init u
        (fun c => PhaseEightDrainReady n M sigma ell hell c)
    · simp [hut]
  · simp [hsu]

/-- Measurability of the random-start branch. -/
theorem measurableSet_phaseEightDrainFailureAtPast
    (init : InputCfg n) (M : ℕ) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    MeasurableSet (phaseEightDrainFailureAtPast init M sigma ell hell) := by
  rw [show phaseEightDrainFailureAtPast init M sigma ell hell =
      ⋃ s : ℕ,
        {omega | homogeneousLatePhaseStart init 8 omega = (s : WithTop ℕ)} ∩
          ({omega | minorityU sigma (trace init omega s) ≤ n} ∩
            ({omega | ∀ u, s ≤ u → u < s + phaseEightDrainHorizon n →
              PhaseEightDrainReady n M sigma ell hell (trace init omega u)} ∩
             {omega | 1 ≤ minorityU sigma
                (trace init omega (s + phaseEightDrainHorizon n))})) by
    ext omega
    simp [phaseEightDrainFailureAtPast,
      PhaseThreeAveragingStops.driftFailureAt]]
  apply MeasurableSet.iUnion
  intro s
  have hfibre : MeasurableSet
      {omega | homogeneousLatePhaseStart init 8 omega = (s : WithTop ℕ)} :=
    ((pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256).le s) _
      ((homogeneousLatePhaseStart_past init 8) s)
  exact hfibre.inter
    ((measurableSet_trace_state init s
      (fun c => minorityU sigma c ≤ n)).inter
      ((measurableSet_ready_alive init M sigma ell hell s).inter
        (measurableSet_trace_state init
          (s + phaseEightDrainHorizon n)
          (fun c => 1 ≤ minorityU sigma c))))

/-- Prefix-weighted random-start equation-(57) bound for one witness branch. -/
theorem law_phaseEightDrainFailureAtPast
    (init : InputCfg n) (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    law init (phaseEightDrainFailureAtPast init M sigma ell hell) ≤
      phaseEightDrainBudget n := by
  have hraw := PhaseThreeAveragingStops.potential_drift_tail_at_pastTime
    init (homogeneousLatePhaseStart init 8)
    (homogeneousLatePhaseStart_past init 8)
    (minorityU sigma)
    (fun c => PhaseEightDrainReady n M sigma ell hell c)
    (phaseEightDrainRate n)
    (phaseEightDrainDrift hn hM sigma ell hell)
    (phaseEightDrainHorizon n) n
  exact hraw.trans (phaseEightDrainScalar n hn)

/-! ## Finite witness union -/

/-- Inadmissible witness choices contribute the empty event. -/
def phaseEightDrainWitnessBranch
    (init : InputCfg n) (M : Fin (n + 1)) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    Set (InputLog n) :=
  if hM : 12 * n ≤ 25 * M.val then
    if hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n then
      phaseEightDrainFailureAtPast init M.val sigma ell hell
    else ∅
  else ∅

/-- Union over `M ≤ n`, both signs, and all selected levels. -/
def phaseEightDrainWitnessFailure (init : InputCfg n) : Set (InputLog n) :=
  ⋃ M : Fin (n + 1),
    ⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      (phaseEightDrainWitnessBranch init M .pos ell ∪
        phaseEightDrainWitnessBranch init M .neg ell)

/-- The finite-union factor is exactly
`2 (n+1) (hourIndex n+1)`. -/
def phaseEightDrainWitnessCharge (n : ℕ) : ℝ≥0∞ :=
  ((2 * (n + 1) *
      (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ) : ℝ≥0∞) *
    phaseEightDrainBudget n

private theorem measurableSet_phaseEightDrainWitnessBranch
    (init : InputCfg n) (M : Fin (n + 1)) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    MeasurableSet (phaseEightDrainWitnessBranch init M sigma ell) := by
  unfold phaseEightDrainWitnessBranch
  by_cases hM : 12 * n ≤ 25 * M.val
  · simp only [hM, dite_true]
    by_cases hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n
    · simpa only [hell, dite_true] using
        measurableSet_phaseEightDrainFailureAtPast init M.val sigma ell hell
    · simp [hell]
  · simp [hM]

private theorem law_phaseEightDrainWitnessBranch
    (init : InputCfg n) (hn : 2 ≤ n)
    (M : Fin (n + 1)) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init (phaseEightDrainWitnessBranch init M sigma ell) ≤
      phaseEightDrainBudget n := by
  unfold phaseEightDrainWitnessBranch
  by_cases hM : 12 * n ≤ 25 * M.val
  · simp only [hM, dite_true]
    by_cases hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n
    · simpa only [hell, dite_true] using
        law_phaseEightDrainFailureAtPast init hn hM sigma ell hell
    · simp [hell]
  · simp [hM]

theorem measurableSet_phaseEightDrainWitnessFailure
    (init : InputCfg n) :
    MeasurableSet (phaseEightDrainWitnessFailure init) := by
  unfold phaseEightDrainWitnessFailure
  apply MeasurableSet.iUnion
  intro M
  apply MeasurableSet.iUnion
  intro ell
  exact
    (measurableSet_phaseEightDrainWitnessBranch init M .pos ell).union
      (measurableSet_phaseEightDrainWitnessBranch init M .neg ell)

/-- Unconditional original-law charge for all possible receipt witnesses. -/
theorem law_phaseEightDrainWitnessFailure
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseEightDrainWitnessFailure init) ≤
      phaseEightDrainWitnessCharge n := by
  have hn : 2 ≤ n := by
    have := (time_population_bounds hinput.1).2
    omega
  unfold phaseEightDrainWitnessFailure
  calc
    law init
        (⋃ M : Fin (n + 1),
          ⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
            (phaseEightDrainWitnessBranch init M .pos ell ∪
              phaseEightDrainWitnessBranch init M .neg ell)) ≤
      ∑ M : Fin (n + 1),
        law init
          (⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
            (phaseEightDrainWitnessBranch init M .pos ell ∪
              phaseEightDrainWitnessBranch init M .neg ell)) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ M : Fin (n + 1),
        ∑ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
          law init
            (phaseEightDrainWitnessBranch init M .pos ell ∪
              phaseEightDrainWitnessBranch init M .neg ell) := by
      refine Finset.sum_le_sum fun M _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ M : Fin (n + 1),
        ∑ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
          (phaseEightDrainBudget n + phaseEightDrainBudget n) := by
      refine Finset.sum_le_sum fun M _ => ?_
      refine Finset.sum_le_sum fun ell _ => ?_
      exact (measure_union_le _ _).trans
        (add_le_add
          (law_phaseEightDrainWitnessBranch init hn M .pos ell)
          (law_phaseEightDrainWitnessBranch init hn M .neg ell))
    _ = phaseEightDrainWitnessCharge n := by
      unfold phaseEightDrainWitnessCharge
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

private theorem not_actualBranch_of_not_witnessFailure
    {init : InputCfg n} {omega : InputLog n}
    {M : ℕ} {sigma : Sign}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hMupper : M ≤ n) (hMlower : 12 * n ≤ 25 * M)
    (hgood : omega ∉ phaseEightDrainWitnessFailure init) :
    omega ∉ phaseEightDrainFailureAtPast init M sigma ell hell := by
  intro hbad
  apply hgood
  let q : Fin (n + 1) := ⟨M, by omega⟩
  unfold phaseEightDrainWitnessFailure
  refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨ell, ?_⟩⟩
  cases sigma with
  | pos =>
      left
      simpa [phaseEightDrainWitnessBranch, q, hMlower, hell] using hbad
  | neg =>
      right
      simpa [phaseEightDrainWitnessBranch, q, hMlower, hell] using hbad

/-! ## Charged Lemma 13 event and conclusion -/

def lemmaThirteenFailure (init : InputCfg n) : Set (InputLog n) :=
  lemmaThirteenRouteFailure init ∪ phaseEightDrainWitnessFailure init

def lemmaThirteenFailureCharge (n : ℕ) : ℝ≥0∞ :=
  lemmaThirteenRouteFailureCharge n + phaseEightDrainWitnessCharge n

theorem measurableSet_lemmaThirteenFailure
    (init : InputCfg n) :
    MeasurableSet (lemmaThirteenFailure init) :=
  (measurableSet_lemmaThirteenRouteFailure init).union
    (measurableSet_phaseEightDrainWitnessFailure init)

theorem law_lemmaThirteenFailure
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lemmaThirteenFailure init) ≤ lemmaThirteenFailureCharge n := by
  unfold lemmaThirteenFailure lemmaThirteenFailureCharge
  exact (measure_union_le _ _).trans
    (add_le_add
      (law_lemmaThirteenRouteFailure init hinput)
      (law_phaseEightDrainWitnessFailure init hinput))

/-- Final deterministic payload for Lemma 14. -/
structure LemmaThirteenSmallGapReceipt {n M R : ℕ}
    (init : InputCfg n) (omega : InputLog n)
    (completed seven homogeneousSeven eight homogeneousEight t : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma tau : Sign) : Prop where
  route : LemmaThirteenRouteReceipt (M := M) (R := R)
    init omega completed seven homogeneousSeven eight homogeneousEight
      ell hell sigma tau
  homogeneous_le : homogeneousEight ≤ t
  deadline : t ≤ homogeneousEight + phaseEightDrainHorizon n
  before_nine : (t : WithTop ℕ) < phaseSeedTime init 9 omega
  phase_win : PhaseOnlyWindows.Phase8Win
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) n
      (trace init omega t)
  no_minority : minorityU sigma (trace init omega t) = 0
  credit_window : ∀ u, homogeneousEight ≤ u →
    u ≤ homogeneousEight + phaseEightDrainHorizon n →
      (544 : ℤ) * (M : ℤ) ≤
        1000 * latePhaseEightCredit sigma ell hell (trace init omega u)

/-- Lemma 13 on the small-gap branch. -/
theorem lemmaThirteen_smallGap
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ LateStrengthening.smallHistory init)
    (hgood : omega ∉ lemmaThirteenFailure init) :
    ∃ completed seven homogeneousSeven eight homogeneousEight t : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaThirteenSmallGapReceipt (M := M) (R := R)
          init omega completed seven homogeneousSeven eight homogeneousEight t
          ell hell sigma tau := by
  have hrouteGood : omega ∉ lemmaThirteenRouteFailure init := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hdrainGood : omega ∉ phaseEightDrainWitnessFailure init := by
    intro hbad
    exact hgood (Or.inr hbad)
  obtain ⟨completed, seven, homogeneousSeven, eight, homogeneousEight,
      ell, hell, sigma, tau, M, R, hroute⟩ :=
    exists_lemmaThirteenRouteReceipt_of_smallHistory
      hinput hsmall hrouteGood
  have hbranch : omega ∉
      phaseEightDrainFailureAtPast init M sigma ell hell :=
    not_actualBranch_of_not_witnessFailure hell
      hroute.twelve.main_upper hroute.twelve.main_lower hdrainGood
  let t := homogeneousEight + phaseEightDrainHorizon n
  have htWork : t = phaseEightWorkEnd n homogeneousEight := by
    rfl
  have hstartEight := phaseEightWin_during_work
    hroute.twelve hroute.timing le_rfl (by
      rw [← htWork]
      exact Nat.le_add_right _ _)
  have hstartBound :
      minorityU sigma (trace init omega homogeneousEight) ≤ n := by
    unfold minorityU
    exact (Multiset.countP_le_card _ _).trans_eq hstartEight.1
  have halive : ∀ u, homogeneousEight ≤ u → u < t →
      PhaseEightDrainReady n M sigma ell hell (trace init omega u) := by
    intro u hu hut
    have huWork : u ≤ phaseEightWorkEnd n homogeneousEight := by
      rw [← htWork]
      omega
    have hb := lemmaThirteenRouteReceipt_bounds_at hroute hu huWork
    exact
      { phase_win := phaseEightWin_during_work
          hroute.twelve hroute.timing hu huWork
        deep := hb.2.1
        credit_scaled := hb.2.2.1 }
  have hzero : minorityU sigma (trace init omega t) = 0 := by
    by_contra hne
    apply hbranch
    refine ⟨homogeneousEight, hroute.timing.homogeneous_time,
      hstartBound, ?_, ?_⟩
    · simpa [t] using halive
    · simpa [t] using Nat.one_le_iff_ne_zero.mpr hne
  have htEight : PhaseOnlyWindows.Phase8Win
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) n
      (trace init omega t) := by
    apply phaseEightWin_during_work hroute.twelve hroute.timing
    · exact Nat.le_add_right _ _
    · rw [← htWork]
  have hcredit : ∀ u, homogeneousEight ≤ u →
      u ≤ homogeneousEight + phaseEightDrainHorizon n →
      (544 : ℤ) * (M : ℤ) ≤
        1000 * latePhaseEightCredit sigma ell hell (trace init omega u) := by
    intro u hu hut
    have huWork : u ≤ phaseEightWorkEnd n homogeneousEight := by
      simpa [phaseEightWorkEnd, phaseEightDrainHorizon] using hut
    exact (lemmaThirteenRouteReceipt_bounds_at hroute hu huWork).2.2.1
  refine ⟨completed, seven, homogeneousSeven, eight, homogeneousEight, t,
    ell, hell, sigma, tau, M, R, ?_⟩
  exact
    { route := hroute
      homogeneous_le := Nat.le_add_right _ _
      deadline := le_rfl
      before_nine := by
        rw [htWork]
        exact hroute.timing.work_before_nine
      phase_win := htEight
      no_minority := hzero
      credit_window := hcredit }

/-!
THEOREM LIST
* `majorityBlockCount_le_shallow_add_full`
* `latePhaseEightCredit_le_shallowExcess`
* `phaseEightShallowAvailability_scaled`
* `PhaseEightDrainReady`
* `twoRectangle_weightedDropSum`
* `phaseEightDrainDrift`
* `phaseEightDrainScalar`
* `phaseEightDrainFailureAtPast`
* `measurableSet_phaseEightDrainFailureAtPast`
* `law_phaseEightDrainFailureAtPast`
* `phaseEightDrainWitnessFailure`, `phaseEightDrainWitnessCharge`
* `measurableSet_phaseEightDrainWitnessFailure`
* `law_phaseEightDrainWitnessFailure`
* `lemmaThirteenFailure`, `lemmaThirteenFailureCharge`
* `measurableSet_lemmaThirteenFailure`, `law_lemmaThirteenFailure`
* `LemmaThirteenSmallGapReceipt`, `lemmaThirteen_smallGap`

CLOSES ITEM 1
* Proves `minorityU` non-increase from the phase_win Phase-8 transition.
* Replaces the too-broad public availability count by the compatible unfull
  fixed block and proves its `.26112 n` excess from `J₈`.
* Counts both ordered scheduler rectangles, obtaining rate `.52224/n`.
* Starts the drift at the random homogeneous Phase-8 time by the available
  prefix-weighted past-time splice.
* Gives the exact `n^(-3.17792)` branch budget and the finite-union factor
  `2 (n+1) (hourIndex n+1)`.

CLOSES ITEM 2
* `lemmaThirteenFailure` is the measurable union of the route and drain
  failures, with charge
  `lemmaThirteenRouteFailureCharge + phaseEightDrainWitnessCharge`.

CLOSES ITEM 3
* Outside that failure, the work endpoint is still before the first Phase-9
  seed, is homogeneous Phase 8, and has `minorityU = 0`.
* The same receipt records `J₈ ≥ .544 M` at every homogeneous Phase-8 time in
  the complete work window.
* This is the exact Lemma-14 handoff: Phase 9 begins from a minority-free
  Phase-8 configuration while the majority block and winning sign are still
  retained. Lemma 14 must next prove the finite Phase-9 seed/spread and the
  correct output-bit propagation; no Phase-9 probability is charged here.

CARRIED PREMISES AND PRODUCERS
* `GoodInput` and `omega ∈ smallHistory init`: caller premises.
* `LemmaThirteenRouteReceipt`: produced by
  `exists_lemmaThirteenRouteReceipt_of_smallHistory` outside
  `lemmaThirteenRouteFailure`.
* Homogeneous Phase-8 window, depth, and the `.544 M` credit throughout the
  work interval: `lemmaThirteenRouteReceipt_bounds_at` and
  `phaseEightWin_during_work`.
* `12*n ≤ 25*M` and `M ≤ n`: retained in
  `LemmaTwelveRouteReceipt.main_lower/main_upper`.
* Phase-9 exclusion: `PhaseEightFiniteReceipt.work_before_nine`.
* No premise quantifies over all logs or arbitrary configurations.

UNFINISHED
* Nothing in Lemma 13 on the small-gap branch.
* Lemma 14's Phase-9 timing, sign/output propagation, and stabilization tail
  remain separate.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaThirteenSmallGap

end
