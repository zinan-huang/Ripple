import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time
import Ripple.PopulationProtocol.Majority.SSEM.Probability.RandomScheduler
import Mathlib.Tactic

namespace SSEM

open scoped BigOperators

variable {n : ℕ}

/-- Total resetcount mass over all agents. -/
def resetMass {n : ℕ} (C : Config (AgentState n) Opinion n) : ℕ :=
  Finset.univ.sum fun w : Fin n => (C w).1.resetcount

/-- Resetcount mass away from the two scheduled endpoints. -/
def resetMassExcept {n : ℕ} (C : Config (AgentState n) Opinion n)
    (i j : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun w => w ≠ i ∧ w ≠ j).sum
    fun w => (C w).1.resetcount

theorem resetMass_eq_pair_add_except
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j) :
    resetMass C =
      (C i).1.resetcount + (C j).1.resetcount + resetMassExcept C i j := by
  classical
  let f : Fin n → ℕ := fun w => (C w).1.resetcount
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    simp [hij.symm]
  have h₁ := Finset.add_sum_erase (s := (Finset.univ : Finset (Fin n))) (f := f) hi
  have h₂ := Finset.add_sum_erase (s := (Finset.univ : Finset (Fin n)).erase i)
    (f := f) hj
  have hrest :
      ((Finset.univ : Finset (Fin n)).erase i).erase j =
        ((Finset.univ : Finset (Fin n)).filter fun w => w ≠ i ∧ w ≠ j) := by
    ext w
    by_cases hwi : w = i
    · subst w
      simp [hij]
    · by_cases hwj : w = j
      · subst w
        simp [hij.symm]
      · simp [hwi, hwj]
  unfold resetMass resetMassExcept
  calc
    (Finset.univ.sum fun w : Fin n => (C w).1.resetcount)
        = f i + ∑ w ∈ (Finset.univ : Finset (Fin n)).erase i, f w := h₁.symm
    _ = f i +
          (f j + ∑ w ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, f w) := by
            rw [h₂.symm]
    _ = (C i).1.resetcount + (C j).1.resetcount + resetMassExcept C i j := by
            rw [hrest]
            simp [f, resetMassExcept, add_assoc]

theorem resetMassExcept_step_eq
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j) :
    resetMassExcept (C.step P i j) i j = resetMassExcept C i j := by
  classical
  unfold resetMassExcept
  apply Finset.sum_congr rfl
  intro w hw
  have hwi : w ≠ i := (Finset.mem_filter.mp hw).2.1
  have hwj : w ≠ j := (Finset.mem_filter.mp hw).2.2
  simp [Config.step, hij, hwi, hwj]

/-- Per-step reset-mass identity: only the selected ordered pair can change. -/
theorem resetMass_step_eq
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j) :
    resetMass (C.step P i j) =
      ((P.δ (C i, C j)).1).resetcount +
        ((P.δ (C i, C j)).2).resetcount +
        resetMassExcept C i j := by
  rw [resetMass_eq_pair_add_except (C.step P i j) hij,
    resetMassExcept_step_eq P C hij]
  have hfst := congrArg AgentState.resetcount (Config.step_fst_state P C hij)
  have hsnd := congrArg AgentState.resetcount (Config.step_snd_state P C hij hij.symm)
  rw [hfst, hsnd]

theorem resetMass_step_add_pair_eq
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j) :
    resetMass (C.step P i j) + (C i).1.resetcount + (C j).1.resetcount =
      resetMass C + ((P.δ (C i, C j)).1).resetcount +
        ((P.δ (C i, C j)).2).resetcount := by
  rw [resetMass_step_eq P C hij, resetMass_eq_pair_add_except C hij]
  omega

theorem resetMass_step_le_add_two_mul_of_pair_post_bound
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j) {B : ℕ}
    (hiB : (C.step P i j i).1.resetcount ≤ B)
    (hjB : (C.step P i j j).1.resetcount ≤ B) :
    resetMass (C.step P i j) ≤ resetMass C + 2 * B := by
  rw [resetMass_step_eq P C hij, resetMass_eq_pair_add_except C hij]
  have hfst := congrArg AgentState.resetcount (Config.step_fst_state P C hij)
  have hsnd := congrArg AgentState.resetcount (Config.step_snd_state P C hij hij.symm)
  have hiB' : ((P.δ (C i, C j)).1).resetcount ≤ B := by
    rw [← hfst]
    exact hiB
  have hjB' : ((P.δ (C i, C j)).2).resetcount ≤ B := by
    rw [← hsnd]
    exact hjB
  omega

theorem resetMass_step_add_two_eq_of_endpoint_drop
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j)
    (hi_pos : 0 < (C i).1.resetcount)
    (hj_pos : 0 < (C j).1.resetcount)
    (hi_drop : (C.step P i j i).1.resetcount = (C i).1.resetcount - 1)
    (hj_drop : (C.step P i j j).1.resetcount = (C j).1.resetcount - 1) :
    resetMass (C.step P i j) + 2 = resetMass C := by
  rw [resetMass_step_eq P C hij, resetMass_eq_pair_add_except C hij]
  have hfst := congrArg AgentState.resetcount (Config.step_fst_state P C hij)
  have hsnd := congrArg AgentState.resetcount (Config.step_snd_state P C hij hij.symm)
  have hi_drop' : ((P.δ (C i, C j)).1).resetcount =
      (C i).1.resetcount - 1 := by
    rw [← hfst]
    exact hi_drop
  have hj_drop' : ((P.δ (C i, C j)).2).resetcount =
      (C j).1.resetcount - 1 := by
    rw [← hsnd]
    exact hj_drop
  omega

/-- Ordered pairs internal to a finite agent set. -/
def OrderedPairsIn {n : ℕ} (A : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (A.product A).filter fun p => p.1 ≠ p.2

theorem mem_OrderedPairsIn {A : Finset (Fin n)} (p : Fin n × Fin n) :
    p ∈ OrderedPairsIn A ↔ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 := by
  simp [OrderedPairsIn, and_assoc]

theorem OrderedPairsIn_card {n : ℕ} (A : Finset (Fin n)) :
    (OrderedPairsIn A).card = A.card * (A.card - 1) := by
  classical
  let diag : Finset (Fin n × Fin n) := (A.product A).filter fun p => p.1 = p.2
  have hdiag_eq : diag = A.image fun i => (i, i) := by
    ext p
    rcases p with ⟨i, j⟩
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      have hiA : i ∈ A := (Finset.mem_product.mp hp.1).1
      exact Finset.mem_image.mpr ⟨i, hiA, Prod.ext rfl hp.2⟩
    · intro hp
      rw [Finset.mem_image] at hp
      rcases hp with ⟨k, hkA, hkp⟩
      rw [← hkp]
      simp [diag, hkA]
  have hdiag_card : diag.card = A.card := by
    rw [hdiag_eq, Finset.card_image_of_injective]
    intro a b h
    exact congrArg Prod.fst h
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := A.product A) (p := fun p : Fin n × Fin n => p.1 = p.2)
  have hoff : diag.card + (OrderedPairsIn A).card = A.card * A.card := by
    simpa [diag, OrderedPairsIn, Finset.card_product, Nat.add_comm] using hsplit
  have harith : A.card + A.card * (A.card - 1) = A.card * A.card := by
    cases A.card with
    | zero => simp
    | succ k =>
        simp [Nat.succ_mul, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
  have hcancel : A.card + (OrderedPairsIn A).card =
      A.card + A.card * (A.card - 1) := by
    rw [hdiag_card] at hoff
    rw [hoff, harith]
  exact Nat.add_left_cancel hcancel

/-- Agents currently Resetting at exactly resetcount `r`. -/
def resettingLevel {n : ℕ} (C : Config (AgentState n) Opinion n) (r : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun w => (C w).1.role = .Resetting ∧ (C w).1.resetcount = r

/-- Equal-positive-rc Resetting pairs.  These are the clean drain pairs for `resetMass`. -/
def DrainPairsAtRC {n : ℕ} (C : Config (AgentState n) Opinion n) (r : ℕ) :
    Finset (Fin n × Fin n) :=
  OrderedPairsIn (resettingLevel C r)

theorem mem_DrainPairsAtRC
    (C : Config (AgentState n) Opinion n) (r : ℕ) (p : Fin n × Fin n) :
    p ∈ DrainPairsAtRC C r ↔
      p.1 ≠ p.2 ∧
      (C p.1).1.role = .Resetting ∧ (C p.2).1.role = .Resetting ∧
      (C p.1).1.resetcount = r ∧ (C p.2).1.resetcount = r := by
  simp [DrainPairsAtRC, mem_OrderedPairsIn, resettingLevel]
  constructor
  · rintro ⟨⟨h1r, h1rc⟩, ⟨h2r, h2rc⟩, hne⟩
    exact ⟨hne, h1r, h2r, h1rc, h2rc⟩
  · rintro ⟨hne, h1r, h2r, h1rc, h2rc⟩
    exact ⟨⟨h1r, h1rc⟩, ⟨h2r, h2rc⟩, hne⟩

theorem DrainPairsAtRC_card
    (C : Config (AgentState n) Opinion n) (r : ℕ) :
    (DrainPairsAtRC C r).card =
      (resettingLevel C r).card * ((resettingLevel C r).card - 1) := by
  exact OrderedPairsIn_card (resettingLevel C r)

theorem DrainPairsAtRC_nonempty_of_pair
    (C : Config (AgentState n) Opinion n) {r : ℕ} {i j : Fin n}
    (hij : i ≠ j)
    (hi : (C i).1.role = .Resetting ∧ (C i).1.resetcount = r)
    (hj : (C j).1.role = .Resetting ∧ (C j).1.resetcount = r) :
    (DrainPairsAtRC C r).Nonempty := by
  exact ⟨(i, j), (mem_DrainPairsAtRC C r (i, j)).mpr
    ⟨hij, hi.1, hj.1, hi.2, hj.2⟩⟩

theorem two_le_DrainPairsAtRC_card_of_two_le_level
    (C : Config (AgentState n) Opinion n) {r : ℕ}
    (h : 2 ≤ (resettingLevel C r).card) :
    2 ≤ (DrainPairsAtRC C r).card := by
  rw [DrainPairsAtRC_card]
  have hpos : 0 < (resettingLevel C r).card - 1 := by omega
  nlinarith

theorem DrainPairsAtRC_subset_offDiagonalPairs
    (C : Config (AgentState n) Opinion n) (r : ℕ) :
    DrainPairsAtRC C r ⊆ SSEM.Probability.OffDiagonalPairs n := by
  intro p hp
  rw [SSEM.Probability.mem_offDiagonalPairs]
  exact (mem_DrainPairsAtRC C r p).mp hp |>.1

theorem resetMass_balanced_drain_step_add_two_eq
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n) {i j : Fin n} (hij : i ≠ j)
    (hi_res : (C i).1.role = .Resetting)
    (hj_res : (C j).1.role = .Resetting)
    (hi_rc : 0 < (C i).1.resetcount)
    (hij_rc : (C i).1.resetcount = (C j).1.resetcount) :
    resetMass (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn) i j) + 2 =
      resetMass C := by
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn
  have hj_rc_pos : 0 < (C j).1.resetcount := by omega
  have hstep := step_both_rc_pos (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hDmax C hij hi_res hj_res hi_rc hj_rc_pos
  have hi_drop : (C.step P i j i).1.resetcount = (C i).1.resetcount - 1 := by
    dsimp [P, PEMProtocolCoupled, PEMProtocol]
    rw [hstep.2.2.1]
    rw [hij_rc]
    simp
  have hj_drop : (C.step P i j j).1.resetcount = (C j).1.resetcount - 1 := by
    dsimp [P, PEMProtocolCoupled, PEMProtocol]
    rw [hstep.2.2.2.1]
    rw [← hij_rc]
    simp
  exact resetMass_step_add_two_eq_of_endpoint_drop P C hij hi_rc hj_rc_pos hi_drop hj_drop

theorem resetMass_drain_pair_step_add_two_eq
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n) {r : ℕ} (hr : 0 < r)
    {p : Fin n × Fin n} (hp : p ∈ DrainPairsAtRC C r) :
    resetMass (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn) p.1 p.2) + 2 =
      resetMass C := by
  have h := (mem_DrainPairsAtRC C r p).mp hp
  exact resetMass_balanced_drain_step_add_two_eq
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C h.1 h.2.1 h.2.2.1 (by omega)
    (by rw [h.2.2.2.1, h.2.2.2.2])

/-- Pairs on which `resetMass` strictly increases. -/
def ResetIncreasePairs {n : ℕ} (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) : Finset (Fin n × Fin n) :=
  (SSEM.Probability.OffDiagonalPairs n).filter fun p =>
    resetMass C < resetMass (C.step P p.1 p.2)

theorem mem_ResetIncreasePairs
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) (p : Fin n × Fin n) :
    p ∈ ResetIncreasePairs P C ↔
      p.1 ≠ p.2 ∧ resetMass C < resetMass (C.step P p.1 p.2) := by
  simp [ResetIncreasePairs, SSEM.Probability.mem_offDiagonalPairs]

theorem ResetIncreasePairs_card_le
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) :
    (ResetIncreasePairs P C).card ≤ n * (n - 1) := by
  rw [← SSEM.Probability.offDiagonalPairs_card n]
  exact Finset.card_filter_le _ _

/-- Fresh-reset-like positive pairs: both changed endpoints are Resetting and
their post-step resetcounts are bounded by `Rmax`. -/
def FreshResetPairs {n : ℕ} (Rmax : ℕ)
    (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) : Finset (Fin n × Fin n) :=
  (SSEM.Probability.OffDiagonalPairs n).filter fun p =>
    (C.step P p.1 p.2 p.1).1.role = .Resetting ∧
      (C.step P p.1 p.2 p.2).1.role = .Resetting ∧
      (C.step P p.1 p.2 p.1).1.resetcount ≤ Rmax ∧
      (C.step P p.1 p.2 p.2).1.resetcount ≤ Rmax ∧
      resetMass C < resetMass (C.step P p.1 p.2)

theorem FreshResetPairs_card_le
    (Rmax : ℕ) (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) :
    (FreshResetPairs Rmax P C).card ≤ n * (n - 1) := by
  rw [← SSEM.Probability.offDiagonalPairs_card n]
  exact Finset.card_filter_le _ _

theorem FreshResetPairs_step_le_add_two_Rmax
    (Rmax : ℕ) (P : Protocol (AgentState n) Opinion Output)
    (C : Config (AgentState n) Opinion n) {p : Fin n × Fin n}
    (hp : p ∈ FreshResetPairs Rmax P C) :
    resetMass (C.step P p.1 p.2) ≤ resetMass C + 2 * Rmax := by
  have h := Finset.mem_filter.mp hp
  have hij : p.1 ≠ p.2 := (SSEM.Probability.mem_offDiagonalPairs n p).mp h.1
  exact resetMass_step_le_add_two_mul_of_pair_post_bound P C hij h.2.2.2.1 h.2.2.2.2.1

/-- Collision-detection candidate pairs: same-rank Settled endpoints. -/
def RankCollisionPairs {n : ℕ} (C : Config (AgentState n) Opinion n) :
    Finset (Fin n × Fin n) :=
  (SSEM.Probability.OffDiagonalPairs n).filter fun p =>
    (C p.1).1.role = .Settled ∧ (C p.2).1.role = .Settled ∧
      (C p.1).1.rank = (C p.2).1.rank

theorem RankCollisionPairs_card_le
    (C : Config (AgentState n) Opinion n) :
    (RankCollisionPairs C).card ≤ n * (n - 1) := by
  rw [← SSEM.Probability.offDiagonalPairs_card n]
  exact Finset.card_filter_le _ _

/-- The first endpoint can recruit the second in the rankDelta branch. -/
def RecruitFirstToSecond {n : ℕ} (C : Config (AgentState n) Opinion n)
    (p : Fin n × Fin n) : Prop :=
  (C p.1).1.role = .Settled ∧ (C p.2).1.role = .Unsettled ∧
    (C p.1).1.children < 2 ∧
    2 * (C p.1).1.rank.val + (C p.1).1.children + 1 < n

/-- The second endpoint can recruit the first in the rankDelta branch. -/
def RecruitSecondToFirst {n : ℕ} (C : Config (AgentState n) Opinion n)
    (p : Fin n × Fin n) : Prop :=
  (C p.2).1.role = .Settled ∧ (C p.1).1.role = .Unsettled ∧
    (C p.2).1.children < 2 ∧
    2 * (C p.2).1.rank.val + (C p.2).1.children + 1 < n

/-- Error-monitoring fresh-reset candidates: after excluding earlier
`rankDeltaOSSR` branches, at least one Unsettled endpoint has counter `0` or
`1`, so decrementing by one trips the reset branch. -/
noncomputable def ErrorTimeoutPairs {n : ℕ} (C : Config (AgentState n) Opinion n) :
    Finset (Fin n × Fin n) := by
  classical
  exact (SSEM.Probability.OffDiagonalPairs n).filter fun p =>
    (C p.1).1.role ≠ .Resetting ∧
      (C p.2).1.role ≠ .Resetting ∧
      ¬ ((C p.1).1.role = .Settled ∧ (C p.2).1.role = .Settled ∧
          (C p.1).1.rank = (C p.2).1.rank) ∧
      ¬ RecruitFirstToSecond C p ∧
      ¬ RecruitSecondToFirst C p ∧
      (((C p.1).1.role = .Unsettled ∧ (C p.1).1.errorcount ≤ 1) ∨
        ((C p.2).1.role = .Unsettled ∧ (C p.2).1.errorcount ≤ 1))

theorem ErrorTimeoutPairs_card_le
    (C : Config (AgentState n) Opinion n) :
    (ErrorTimeoutPairs C).card ≤ n * (n - 1) := by
  classical
  rw [← SSEM.Probability.offDiagonalPairs_card n]
  unfold ErrorTimeoutPairs
  exact Finset.card_filter_le _ _

end SSEM
