/-
# HonestDrainSlotsCore — the core mathematical content of the honest-window drain slots.

Split from `HonestDrainSlots.lean`: this file contains the core hdrop lemmas, honest-window
monotonicity proofs, and the `slot{1,7,8}Honest` `PhaseConvergenceW` constructors.  These
depend only on `DrainEngine` (for `qHat`) — NOT on `SlotEngine` (which carries the heavy
`SeedTrigWiring`/`PaperRegime`/`BudgetTightening` chain).

The adapter layer (`WorkInputsHonestFull`, `workHonestFull`, `workHonestFull_carried_eq`) lives
in `HonestDrainSlots.lean`, which imports this file + `SlotEngine`.

**Namespace:** `ExactMajority.HonestDrainSlots` (unchanged, so qualified names work).

No sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestWindows
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainRates
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainEngine
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamOvershootBridge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ExactMajority
namespace HonestDrainSlots

variable {L K : ℕ}

/-! ## Part A — the generic honest step-decomposition for a strict drop.

`drop_prob_of_rect` (consumed by every rectangle floor) only needs `c.card = n` plus a
per-cell strict drop `Φ(stepOrSelf c s t) + 1 ≤ Φ c`.  The existing per-cell drops
(`extremeU_stepOrSelf_drop_pos` etc.) take an all-Main window `hInv` solely to extract the
interacting pair's phase; on the honest window we supply the pair's phase directly and the
pair's Main-ness from the drop-cell finset.  We lift the per-pair countP drop to the
config-level strict drop via the standard `c − {s,t} + {out₁,out₂}` decomposition. -/

private theorem countP_stepOrSelf_drop_of_pair
    (P : AgentState L K → Prop) [DecidablePred P]
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hpair : Multiset.countP (fun a => P a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => P a) ({s, t} : Multiset (AgentState L K))) :
    Multiset.countP (fun a => P a) (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Multiset.countP (fun a => P a) c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le : Multiset.countP (fun a => P a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => P a) c := Multiset.countP_le_of_le _ hsub
  omega

/-! ## Part B — SLOT 1: the honest `extremeU` drop rectangle / floor / hdrop.

The drop cell is `extremePosSet ×ˢ pullPosSet` (both finsets pin `role = main`); the per-cell
strict drop `Transition_extremeU_pair_drop_pos` already takes the PAIR's phase-1 (window-free).
So the rectangle floor holds on `Phase1Honest` with the pair phase from the honest window. -/

/-- **Honest slot-1 drop rectangle** — the `extremeU` strict-drop probability floor on the
chain-honest phase-1 window.  Identical to `DrainThreading.extremeU_drop_prob_rect_pos` but
over `Phase1Honest` (phase-only): the cell pair's Main-ness comes from the finsets, its
phase-1 from the honest window's phase pin. -/
theorem extremeU_drop_prob_rect_honest (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase1Honest (L := L) (K := K) n c) :
    ENNReal.ofReal
        (((DrainThreading.extremePosSet L K).sum c.count
            * (DrainThreading.pullPosSet L K).sum c.count : ℕ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU c} := by
  obtain ⟨hcardn, hph⟩ := hInv
  refine Phase7Convergence.drop_prob_of_rect (fun c => Phase1Convergence.extremeU c) n hn c
    hcardn ((DrainThreading.extremePosSet L K) ×ˢ (DrainThreading.pullPosSet L K)) _ ?_
    (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
    have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
    have hs1 : s.phase.val = 1 := hph s hsm
    have ht1 : t.phase.val = 1 := hph t htm
    simp only [DrainThreading.extremePosSet, Finset.mem_filter] at hsmem
    simp only [DrainThreading.pullPosSet, Finset.mem_filter] at htmem
    obtain ⟨_, hsE⟩ := hsmem
    obtain ⟨_, htP⟩ := htmem
    have hne : s ≠ t := DrainThreading.extremePos_pullPos_disjoint s
      (by simp only [DrainThreading.extremePosSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsE⟩) t
      (by simp only [DrainThreading.pullPosSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htP⟩)
    have happ : Protocol.Applicable c s t := Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact countP_stepOrSelf_drop_of_pair (fun a => Phase1Convergence.extremeSt a) c s t happ
      (DrainThreading.Transition_extremeU_pair_drop_pos s t hs1 ht1 hsE htP)
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      DrainThreading.extremePos_pullPos_disjoint]

/-- **Honest slot-1 structural drop floor** — from the `+3` extreme witness `hext` and the
partner-pool floor `hpull` (both over `Phase1Honest`), the one-step `extremeU` drop is
`≥ ofReal(P/(n(n−1)))`. -/
theorem phase1_drop_floor_honest (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase1Honest (L := L) (K := K) n c) (P : ℕ)
    (hext : 1 ≤ (DrainThreading.extremePosSet L K).sum c.count)
    (hpull : P ≤ (DrainThreading.pullPosSet L K).sum c.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU c} := by
  refine le_trans ?_ (extremeU_drop_prob_rect_honest n hn c hInv)
  have hprod : (P : ℕ) ≤
      (DrainThreading.extremePosSet L K).sum c.count * (DrainThreading.pullPosSet L K).sum c.count := by
    calc (P : ℕ) ≤ 1 * P := by omega
      _ ≤ (DrainThreading.extremePosSet L K).sum c.count * P := Nat.mul_le_mul_right _ hext
      _ ≤ (DrainThreading.extremePosSet L K).sum c.count * (DrainThreading.pullPosSet L K).sum c.count :=
          Nat.mul_le_mul_left _ hpull
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Honest slot-1 per-level `hdrop`** — the levels-engine drop binder on `Phase1Honest`,
at the calibrated rate `DrainRates.levelRate P n`. -/
theorem hdrop1_honest (n : ℕ) (hn : 2 ≤ n) (P : ℕ)
    (hext : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
      1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
      P ≤ (DrainThreading.pullPosSet L K).sum b.count) :
    ∀ m, ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
      Phase1Convergence.extremeU b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ ≤ DrainRates.levelRate P n m := by
  intro m b hInv hbm
  unfold DrainRates.levelRate
  exact DrainThreading.extremeU_hdrop_of_floor m
    (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase1_drop_floor_honest n hn b hInv P (hext b hInv) (hpull b hInv))

/-! ## Part C — SLOT 8: the honest `minorityU` drop rectangle / floor / hdrop.

The drop cell is `minorityAt σ i ×ˢ elimAbove σ i` (both pin `role = main`); the per-cell
strict drop `absorbConsume_minorityU_pair_drop` takes the pair's Main-ness directly.  We
supply the pair's phase-8 from the honest window's phase pin. -/

/-- **Honest slot-8 per-cell `minorityU` strict drop** — the both-Main phase-8 pair drop,
window-free (phase + Main supplied directly). -/
theorem minorityU_stepOrSelf_drop_honest (σ st : Sign) (c : Config (AgentState L K))
    (s t : AgentState L K) (hs8 : s.phase.val = 8) (ht8 : t.phase.val = 8)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (happ : Protocol.Applicable c s t)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic σ i)
    (htb : t.bias = Bias.dyadic st j) (hsts : st ≠ σ) (hlt : i.val < j.val) (htf : ¬ t.full) :
    Phase7Convergence.minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase7Convergence.minorityU σ c := by
  refine countP_stepOrSelf_drop_of_pair (fun a => Phase7Convergence.minoritySt σ a) c s t happ ?_
  rw [Phase8Convergence.Transition_eq_absorbConsume_of_phase8_main s t hs8 ht8 hsM htM]
  exact Phase8Convergence.absorbConsume_minorityU_pair_drop σ st s t hsM htM i j hsb htb hsts hlt htf

/-- **Honest slot-8 drop rectangle** — the `minorityU` strict-drop probability floor on the
chain-honest phase-8 window. -/
theorem minorityU_drop_prob_rect_honest8 (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase8Honest (L := L) (K := K) n c)
    (i : Fin (L + 1)) :
    ENNReal.ofReal
        (((Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count
            * (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count : ℕ)
          / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ c} := by
  obtain ⟨hcardn, hph⟩ := hInv
  refine Phase7Convergence.drop_prob_of_rect (fun c => Phase7Convergence.minorityU σ c) n hn c
    hcardn ((Phase8Convergence.minorityAt (L := L) (K := K) σ i)
      ×ˢ (Phase8Convergence.elimAbove (L := L) (K := K) σ i)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
    have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
    have hs8 : s.phase.val = 8 := hph s hsm
    have ht8 : t.phase.val = 8 := hph t htm
    simp only [Phase8Convergence.minorityAt, Finset.mem_filter] at hsmem
    simp only [Phase8Convergence.elimAbove, Finset.mem_filter] at htmem
    obtain ⟨_, hsM, hsb⟩ := hsmem
    obtain ⟨_, htM, htf, stt, j, hst, hij, htb⟩ := htmem
    have hne : s ≠ t := Phase8Convergence.minorityAt_elimAbove_disjoint σ i s
      (by simp only [Phase8Convergence.minorityAt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsM, hsb⟩) t
      (by simp only [Phase8Convergence.elimAbove, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, htM, htf, stt, j, hst, hij, htb⟩)
    have happ : Protocol.Applicable c s t := Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact minorityU_stepOrSelf_drop_honest σ stt c s t hs8 ht8 hsM htM happ i j hsb htb hst hij htf
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      (Phase8Convergence.minorityAt_elimAbove_disjoint σ i)]

/-- **Honest slot-8 structural drop floor.** -/
theorem phase8_drop_floor_honest (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase8Honest (L := L) (K := K) n c)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ c} := by
  refine le_trans ?_ (minorityU_drop_prob_rect_honest8 σ n hn c hInv i)
  have hprod : (E : ℕ) ≤
      (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count *
        (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count := by
    calc (E : ℕ) ≤ 1 * E := by omega
      _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count * E :=
          Nat.mul_le_mul_right _ hmin
      _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count *
            (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count :=
          Nat.mul_le_mul_left _ helim
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Honest slot-8 per-level `hdrop`** — at the calibrated rate `DrainRates.levelRate E n`,
the carried witness being the above-level eliminator margin (`hmin`/`helim` over the honest
window, the genuine probabilistic input). -/
theorem hdrop8_honest (σ : Sign) (n : ℕ) (hn : 2 ≤ n) (E : ℕ)
    (hwit : ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
      Phase7Convergence.minorityU σ b ≥ 1 →
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
      Phase7Convergence.minorityU σ b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ ≤ DrainRates.levelRate E n m := by
  intro m hm1 b hInv hbm
  have hmin1 : Phase7Convergence.minorityU σ b ≥ 1 := by omega
  obtain ⟨i, hmin, helim⟩ := hwit b hInv hmin1
  unfold DrainRates.levelRate
  -- Markov complement packaging (no window needed — `minorityU_hdrop_of_floor` carries a
  -- spurious all-Main argument we cannot honestly supply; we inline the floor → tail step).
  set p := ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) with hp
  have hfloor := phase8_drop_floor_honest σ n hn b hInv i E hmin helim
  classical
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) |
        Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ b}
      = OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m) :=
    OneSidedCancel.potBelow_measurable (Phase7Convergence.minorityU σ (L := L) (K := K)) m
  haveI hprob : IsProbabilityMeasure (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), hprob.measure_univ]
  rw [hKb, hcompl]
  have hp_le : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m) := by
    rw [← hsucc_eq]; exact hfloor
  exact tsub_le_tsub_left hp_le 1

/-! ## Part D — SLOT 7: the honest `classMassN` monotonicity + drop rectangle / floor.

Slot 7 drains the σ-class MASS `classMassN` (the F3-honest potential: a `minorityU`-`hmono`
would be FALSE, see `Phase7HonestDrain`).  `classMass` reads `bias` (not role), so we cannot
quote a "Main-only" argument; instead the honest non-increase rests on:
  * both-Main pair → `cancelSplit`, mass non-increase UNCONDITIONAL
    (`cancelSplit_classMass_pair_le`, no `hgap`);
  * mixed pair → the Main side is `clockCounterStep`-untouched and the non-Main side keeps
    its bias (phase-≥5 `stdCounterSubroutine_bias_ge_five`), so each agent's `agentClassMass`
    is preserved ⇒ pair mass equal.
The `hgap`/eliminator-margin carry survives ONLY in the DROP FLOOR (`hPhase6Post7`), not in
the monotonicity. -/

/-- **Per-side: the `Phase7Transition` output's phase is `≠ 10` and bias `=` the input**, on
a NOT-both-main phase-7 pair.  Each agent is either non-clock (returned identically → phase 7,
bias unchanged) or a clock (`stdCounterSubroutine` → phase `≤ 8`, bias preserved at phase `≥ 5`).
The first projection; the second is symmetric. -/
private theorem phase7_side_fst_of_not_both (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    (Phase7Transition L K s t).1.phase.val ≠ 10 ∧ (Phase7Transition L K s t).1.bias = s.bias := by
  unfold Phase7Transition; simp only [if_neg hnb]
  by_cases hc : s.role = Role.clock
  · rw [if_pos hc]
    refine ⟨?_, Phase6Convergence.stdCounterSubroutine_bias_ge_five (L := L) (K := K) s (by omega)⟩
    have hle : (stdCounterSubroutine L K s).phase.val ≤ s.phase.val + 1 :=
      SeamNoOvershoot.stdCounterSubroutine_phase_le_succ_of_clock s hc
        (by rw [hs7]; decide) (by rw [hs7]; decide) (by rw [hs7]; decide)
    rw [hs7] at hle; omega
  · rw [if_neg hc]; exact ⟨by rw [hs7]; decide, rfl⟩

private theorem phase7_side_snd_of_not_both (s t : AgentState L K)
    (ht7 : t.phase.val = 7) (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    (Phase7Transition L K s t).2.phase.val ≠ 10 ∧ (Phase7Transition L K s t).2.bias = t.bias := by
  unfold Phase7Transition; simp only [if_neg hnb]
  by_cases hc : t.role = Role.clock
  · rw [if_pos hc]
    refine ⟨?_, Phase6Convergence.stdCounterSubroutine_bias_ge_five (L := L) (K := K) t (by omega)⟩
    have hle : (stdCounterSubroutine L K t).phase.val ≤ t.phase.val + 1 :=
      SeamNoOvershoot.stdCounterSubroutine_phase_le_succ_of_clock t hc
        (by rw [ht7]; decide) (by rw [ht7]; decide) (by rw [ht7]; decide)
    rw [ht7] at hle; omega
  · rw [if_neg hc]; exact ⟨by rw [ht7]; decide, rfl⟩

/-- The mixed-pair `agentClassMass` is preserved on a phase-7 pair: each output keeps its
input's bias (Main untouched; clock bias preserved at phase `≥ 5`; Reserve identical), and
neither side enters phase 10, so the trailing `finishPhase10Entry` is the identity. -/
theorem Transition_agentClassMass_pair_eq_of_not_both_main7 (σ : Sign) (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Phase7Convergence.agentClassMass σ (Transition L K s t).1
        + Phase7Convergence.agentClassMass σ (Transition L K s t).2
      = Phase7Convergence.agentClassMass σ s + Phase7Convergence.agentClassMass σ t := by
  obtain ⟨hno1, hb1⟩ := phase7_side_fst_of_not_both s t hs7 hnb
  obtain ⟨hno2, hb2⟩ := phase7_side_snd_of_not_both s t ht7 hnb
  have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7 (L := L) (K := K) s t hs7 ht7
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
  -- The full Transition is the Phase7Transition (no phase-10 finish), so biases carry through.
  have hT1 : (Transition L K s t).1.bias = s.bias := by
    unfold Transition; rw [hepi]; simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ hno1]; exact hb1
  have hT2 : (Transition L K s t).2.bias = t.bias := by
    unfold Transition; rw [hepi]; simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ hno2]; exact hb2
  unfold Phase7Convergence.agentClassMass; rw [hT1, hT2]

/-- **Honest per-pair `classMass` non-increase on the phase-7 window (ANY roles).**  Both-Main:
the unconditional `cancelSplit` bound (NO `hgap`).  Mixed: the pair mass is *equal* (biases
preserved). -/
theorem Transition_classMass_pair_le_honest7 (σ : Sign) (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7) :
    Phase7Convergence.agentClassMass σ (Transition L K s t).1
        + Phase7Convergence.agentClassMass σ (Transition L K s t).2
      ≤ Phase7Convergence.agentClassMass σ s + Phase7Convergence.agentClassMass σ t := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main s t hs7 ht7 hboth.1 hboth.2]
    exact Phase7Convergence.cancelSplit_classMass_pair_le σ s t
  · exact le_of_eq (Transition_agentClassMass_pair_eq_of_not_both_main7 σ s t hs7 ht7 hboth)

/-! ### Lift to the engine `PotNonincrOn classMass` on `Phase7Honest`. -/

private theorem mem_of_app_left7H {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right7H {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- **`classMass σ` is non-increasing under any chosen-pair update on `Phase7Honest`.** -/
theorem classMass_stepOrSelf_le_honest7 (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : HonestWindows.Phase7Honest (L := L) (K := K) n c) (r₁ r₂ : AgentState L K) :
    Phase7Convergence.classMass σ (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ Phase7Convergence.classMass σ c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left7H happ
    have hm2 := mem_of_app_right7H happ
    have h17 : r₁.phase.val = 7 := hph r₁ hm1
    have h27 : r₂.phase.val = 7 := hph r₂ hm2
    have hpair := Transition_classMass_pair_le_honest7 σ r₁ r₂ h17 h27
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have happ_le : (r₁ ::ₘ {r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hrestore : c - r₁ ::ₘ {r₂} + r₁ ::ₘ {r₂} = c := Multiset.sub_add_cancel happ_le
    have hsum_c : Phase7Convergence.classMass σ c
        = Phase7Convergence.classMass σ (c - r₁ ::ₘ {r₂})
            + (Phase7Convergence.agentClassMass σ r₁ + Phase7Convergence.agentClassMass σ r₂) := by
      rw [← hrestore]; simp [Phase7Convergence.classMass, add_left_comm]
    have hsum_c' : Phase7Convergence.classMass σ
          (c - r₁ ::ₘ {r₂} + (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2})
        = Phase7Convergence.classMass σ (c - r₁ ::ₘ {r₂})
            + (Phase7Convergence.agentClassMass σ (Transition L K r₁ r₂).1
              + Phase7Convergence.agentClassMass σ (Transition L K r₁ r₂).2) := by
      simp [Phase7Convergence.classMass, add_left_comm]
    rw [hc']
    show Phase7Convergence.classMass σ
        (c - r₁ ::ₘ {r₂} + (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2})
      ≤ Phase7Convergence.classMass σ c
    rw [hsum_c', hsum_c]; linarith [hpair]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- **The engine `PotNonincrOn classMassN` for the HONEST slot-7 window.**  `classMassN = (classMass).toNat`
inherits the non-increase from `classMass_stepOrSelf_le_honest7` (the `toNat` of a non-increasing
nonnegative integer sequence is non-increasing).  No `hgap` enters the monotonicity. -/
theorem potNonincrOn_classMassN_honest7 (σ : Sign) (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => HonestWindows.Phase7Honest (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel (fun c => Phase7Convergence.classMassN σ c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | Phase7Convergence.classMassN σ c < Phase7Convergence.classMassN σ x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  -- a support member x has classMass σ x ≤ classMass σ c, so its toNat is ≤ too.
  have hle : Phase7Convergence.classMassN σ x ≤ Phase7Convergence.classMassN σ c := by
    by_cases hc : 2 ≤ c.card
    · rw [show (NonuniformMajority L K).stepDistOrSelf c
          = (NonuniformMajority L K).stepDist c hc by
          unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hsupp
      obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc x hsupp
      have hmass : Phase7Convergence.classMass σ x ≤ Phase7Convergence.classMass σ c := by
        rw [← hr]; exact classMass_stepOrSelf_le_honest7 σ n c hInv r₁ r₂
      unfold Phase7Convergence.classMassN
      exact Int.toNat_le_toNat hmass
    · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
          unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hsupp
      rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; exact le_rfl
  omega

/-! ### Honest slot-7 drop rectangle / floor / hdrop (`classMassN`). -/

/-- **Honest slot-7 per-cell `classMassN` strict drop** — the both-Main gap-1 phase-7 pair
mass-drop, window-free (phase from the honest window, Main from the drop-cell finsets). -/
theorem classMassN_stepOrSelf_drop_honest (σ ss : Sign) (c : Config (AgentState L K))
    (s t : AgentState L K) (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (happ : Protocol.Applicable c s t)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic ss i)
    (htb : t.bias = Bias.dyadic σ j) (hss : ss ≠ σ) (hg1 : i.val + 1 = j.val) :
    Phase7Convergence.classMassN σ (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase7Convergence.classMassN σ c := by
  -- per-pair MASS strict drop (cancelSplit gap-1), lifted to the config classMass, then toNat.
  have hpair : Phase7Convergence.agentClassMass σ (Transition L K s t).1
        + Phase7Convergence.agentClassMass σ (Transition L K s t).2 + 1
      ≤ Phase7Convergence.agentClassMass σ s + Phase7Convergence.agentClassMass σ t := by
    rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main s t hs7 ht7 hsM htM]
    exact Phase7Convergence.cancelSplit_classMass_pair_drop σ ss s t i j hsb htb hss hg1
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  have happ_le : (s ::ₘ {t} : Multiset (AgentState L K)) ≤ c := happ
  have hrestore : c - s ::ₘ {t} + s ::ₘ {t} = c := Multiset.sub_add_cancel happ_le
  have hsum_c : Phase7Convergence.classMass σ c
      = Phase7Convergence.classMass σ (c - s ::ₘ {t})
          + (Phase7Convergence.agentClassMass σ s + Phase7Convergence.agentClassMass σ t) := by
    rw [← hrestore]; simp [Phase7Convergence.classMass, add_left_comm]
  have hsum_c' : Phase7Convergence.classMass σ
        (c - s ::ₘ {t} + (Transition L K s t).1 ::ₘ {(Transition L K s t).2})
      = Phase7Convergence.classMass σ (c - s ::ₘ {t})
          + (Phase7Convergence.agentClassMass σ (Transition L K s t).1
            + Phase7Convergence.agentClassMass σ (Transition L K s t).2) := by
    simp [Phase7Convergence.classMass, add_left_comm]
  have hZ : Phase7Convergence.classMass σ (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase7Convergence.classMass σ c := by
    rw [hc']
    show Phase7Convergence.classMass σ
        (c - s ::ₘ {t} + (Transition L K s t).1 ::ₘ {(Transition L K s t).2}) + 1
      ≤ Phase7Convergence.classMass σ c
    rw [hsum_c', hsum_c]; linarith [hpair]
  have hnn := Phase7Convergence.classMass_nonneg σ (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
  have hnnc := Phase7Convergence.classMass_nonneg σ c
  unfold Phase7Convergence.classMassN
  omega

/-- **Honest slot-7 drop rectangle** — the `classMassN` strict-drop probability floor on the
chain-honest phase-7 window. -/
theorem classMassN_drop_prob_rect_honest7 (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase7Honest (L := L) (K := K) n c)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) :
    ENNReal.ofReal
        (((Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count
            * (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count : ℕ)
          / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.classMassN σ c' + 1 ≤ Phase7Convergence.classMassN σ c} := by
  obtain ⟨hcardn, hph⟩ := hInv
  refine Phase7Convergence.drop_prob_of_rect (fun c => Phase7Convergence.classMassN σ c) n hn c
    hcardn ((Phase7Convergence.elimGap1 (L := L) (K := K) σ i)
      ×ˢ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
    have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
    have hs7 : s.phase.val = 7 := hph s hsm
    have ht7 : t.phase.val = 7 := hph t htm
    simp only [Phase7Convergence.elimGap1, Finset.mem_filter] at hsmem
    simp only [Phase7Convergence.minorityAt7, Finset.mem_filter] at htmem
    obtain ⟨_, hsM, ss, hss, hsb⟩ := hsmem
    obtain ⟨_, htM, htb⟩ := htmem
    have hne : s ≠ t := Phase7Convergence.elimGap1_minorityAt7_disjoint σ i j hg1 s
      (by simp only [Phase7Convergence.elimGap1, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hsM, ss, hss, hsb⟩) t
      (by simp only [Phase7Convergence.minorityAt7, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htM, htb⟩)
    have happ : Protocol.Applicable c s t := Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact classMassN_stepOrSelf_drop_honest σ ss c s t hs7 ht7 hsM htM happ i j hsb htb hss hg1
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      (Phase7Convergence.elimGap1_minorityAt7_disjoint σ i j hg1)]

/-- **Honest slot-7 structural drop floor.** -/
theorem phase7_drop_floor_honest (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase7Honest (L := L) (K := K) n c)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) (E : ℕ)
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.classMassN σ c' + 1 ≤ Phase7Convergence.classMassN σ c} := by
  refine le_trans ?_ (classMassN_drop_prob_rect_honest7 σ n hn c hInv i j hg1)
  have hprod : (E : ℕ) ≤
      (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count *
        (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count := by
    calc (E : ℕ) ≤ E * 1 := by omega
      _ ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count * 1 :=
          Nat.mul_le_mul_right _ helim
      _ ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count *
            (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count :=
          Nat.mul_le_mul_left _ hmin
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Honest slot-7 per-level `hdrop`** — at the calibrated rate `DrainRates.levelRate E n`,
the carried witness being the gap-1 eliminator margin over the honest window (the genuine
`hgap`/eliminator-margin probabilistic input). -/
theorem hdrop7_honest (σ : Sign) (n : ℕ) (hn : 2 ≤ n) (E : ℕ)
    (hwit : ∀ b : Config (AgentState L K), HonestWindows.Phase7Honest (L := L) (K := K) n b →
      Phase7Convergence.classMassN σ b ≥ 1 →
      ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
        E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count) :
    ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K), HonestWindows.Phase7Honest (L := L) (K := K) n b →
      Phase7Convergence.classMassN σ b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ ≤ DrainRates.levelRate E n m := by
  intro m hm1 b hInv hbm
  have hmass1 : Phase7Convergence.classMassN σ b ≥ 1 := by omega
  obtain ⟨i, j, hg1, hmin, helim⟩ := hwit b hInv hmass1
  unfold DrainRates.levelRate
  exact Phase7Convergence.classMassN_hdrop_of_floor7 σ m
    (ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase7_drop_floor_honest σ n hn b hInv i j hg1 E hmin helim)

/-! ## Part E — the three honest slot `PhaseConvergenceW` instances.

Each is `OneSidedCancel.levels_PhaseConvergenceW` over the honest phase-only window
(`Phase{1,7,8}Honest`), with:
* `hClosed` — CARRIED as an explicit input (the named seam/working-window gap, mirroring
  `Phase6Convergence.phase6Convergence'`; the phase-only window is NOT closed because a
  Clock can advance — `HonestWindows.clock_advance_breaks_phase_closure`);
* `hmono` — the PROVED honest `PotNonincrOn` (`HonestWindows.potNonincrOn_extremeU_honest`
  / `potNonincrOn_classMassN_honest7` / `HonestWindows.potNonincrOn_minorityU_honest8`);
* `hdrop` — the honest per-level rate (`hdrop{1,7,8}_honest`), padded at `m = 0`. -/

/-- **Honest slot 1 (V3)** — `extremeU` drain on `Phase1Honest`.  `Pre = Phase1Honest ∧ extremeU ≤ M₀`,
`Post = Phase1Honest ∧ extremeU = 0`.  `hClosed` is the carried seam gap; `hmono`/`hdrop` proved. -/
noncomputable def slot1Honest {n : ℕ} (P1 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => HonestWindows.Phase1Honest (L := L) (K := K) n c))
    (hext : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
      1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
      P1 ≤ (DrainThreading.pullPosSet L K).sum b.count)
    (tWin1 : ℕ → ℕ)
    (hpt1 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat P1 n m) ^ (tWin1 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => HonestWindows.Phase1Honest (L := L) (K := K) n c)
    hClosed
    (fun c => Phase1Convergence.extremeU c)
    (HonestWindows.potNonincrOn_extremeU_honest n)
    (SlotEngine.qHat P1 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact SlotEngine.qHat_zero_bound _ _ _ _
      · rw [SlotEngine.qHat_eq_on_pos _ _ _ hmpos]
        exact hdrop1_honest n hn P1 hext hpull m b hInv hbm)
    tWin1 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (SlotEngine.qHat_sum_budget hn hM1 tWin1 hpt1)

/-- **Honest slot 7 (V3)** — `classMassN` eliminator drain on `Phase7Honest`.  The carried
`hwit` (the gap-1 eliminator margin over the honest window) is the genuine probabilistic input
(`hgap`-family); `hmono`/`hdrop` proved honest, `hClosed` carried. -/
noncomputable def slot7Honest {n : ℕ} (σ : Sign) (E7 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => HonestWindows.Phase7Honest (L := L) (K := K) n c))
    (hwit : ∀ b : Config (AgentState L K), HonestWindows.Phase7Honest (L := L) (K := K) n b →
      Phase7Convergence.classMassN σ b ≥ 1 →
      ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
        E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count)
    (tWin7 : ℕ → ℕ)
    (hpt7 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E7 n m) ^ (tWin7 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => HonestWindows.Phase7Honest (L := L) (K := K) n c)
    hClosed
    (fun c => Phase7Convergence.classMassN σ c)
    (potNonincrOn_classMassN_honest7 σ n)
    (SlotEngine.qHat E7 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact SlotEngine.qHat_zero_bound _ _ _ _
      · rw [SlotEngine.qHat_eq_on_pos _ _ _ hmpos]
        exact hdrop7_honest σ n hn E7 hwit m hmpos b hInv hbm)
    tWin7 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (SlotEngine.qHat_sum_budget hn hM1 tWin7 hpt7)

/-- **Honest slot 8 (V3)** — `minorityU` eliminator drain on `Phase8Honest`.  The carried
`hwit` (the above-level eliminator margin over the honest window) is the genuine probabilistic
input; `hmono`/`hdrop` proved honest, `hClosed` carried. -/
noncomputable def slot8Honest {n : ℕ} (σ : Sign) (E8 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => HonestWindows.Phase8Honest (L := L) (K := K) n c))
    (hwit : ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
      Phase7Convergence.minorityU σ b ≥ 1 →
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count)
    (tWin8 : ℕ → ℕ)
    (hpt8 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E8 n m) ^ (tWin8 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => HonestWindows.Phase8Honest (L := L) (K := K) n c)
    hClosed
    (fun c => Phase7Convergence.minorityU σ c)
    (HonestWindows.potNonincrOn_minorityU_honest8 σ n)
    (SlotEngine.qHat E8 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact SlotEngine.qHat_zero_bound _ _ _ _
      · rw [SlotEngine.qHat_eq_on_pos _ _ _ hmpos]
        exact hdrop8_honest σ n hn E8 hwit m hmpos b hInv hbm)
    tWin8 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (SlotEngine.qHat_sum_budget hn hM1 tWin8 hpt8)

end HonestDrainSlots
end ExactMajority
