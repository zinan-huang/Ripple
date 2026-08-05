/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionPhysicalClockProjection
import Tri.HitThenReaches
import Tri.InfectionTriEntry

/-!
# Raw infection-clock consequences of the Lemma 16--19 schedule

The scheduled physical analysis is transferred to the genuine coarse
infection chain.  A separate first-hit composition then starts ordinary Tri
convergence at the activation checkpoint without pretending that the
positive-gap checkpoint is itself absorbing.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Explicit raw interaction clock occupied by all Lemma 16--19 blocks. -/
def lemma16To19TotalClock
    (n q16 cStar m clockBudget : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 3),
    lemma16To19BlockHorizon
      n q16 cStar m clockBudget j

theorem lemma16To19TotalClock_pos
    (n q16 cStar m clockBudget : ℕ)
    (hn : 0 < n) (hq16 : 0 < q16) (hcStar : 0 < cStar) :
    0 <
      lemma16To19TotalClock
        n q16 cStar m clockBudget := by
  unfold lemma16To19TotalClock
  apply Finset.sum_pos'
  · intro j hj
    exact Nat.zero_le _
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    exact
      lemma16To19BlockHorizon_pos
        n q16 cStar m clockBudget
        hn hq16 hcStar 0 (by omega)

theorem lemma16To19TotalClock_eq
    (n q16 cStar m clockBudget : ℕ) :
    lemma16To19TotalClock n q16 cStar m clockBudget =
      cStar * q16 * n +
        (m + 1) * (cStar * n) +
        lemma19FullActivationClockCap n clockBudget := by
  let f := lemma16To19BlockHorizon
    n q16 cStar m clockBudget
  have hmiddle :
      (∑ j ∈ Finset.range (m + 1), f (j + 1)) =
        (m + 1) * (cStar * n) := by
    calc
      (∑ j ∈ Finset.range (m + 1), f (j + 1)) =
          ∑ _j ∈ Finset.range (m + 1), cStar * n := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjm : j ≤ m := by
              simp only [Finset.mem_range] at hj
              omega
            simp [f, lemma16To19BlockHorizon, hjm]
      _ = (m + 1) * (cStar * n) := by
        simp
  unfold lemma16To19TotalClock
  rw [show m + 3 = (m + 2) + 1 by omega]
  rw [Finset.sum_range_succ']
  change
    (∑ j ∈ Finset.range (m + 2), f (j + 1)) + f 0 =
      _
  rw [Finset.sum_range_succ, hmiddle]
  simp [f, lemma16To19BlockHorizon]
  ring

/-- A simple headline-scale envelope for the explicit activation clock. -/
theorem lemma16To19TotalClock_le
    (n q16 cStar m clockBudget : ℕ)
    (hq16 : 1 ≤ q16)
    (hm : m + 1 ≤ q16)
    (hbudget : clockBudget ≤ q16)
    (hlog : Nat.log 2 n ≤ q16) :
    lemma16To19TotalClock n q16 cStar m clockBudget ≤
      (2 * cStar + 5120) * q16 * n := by
  have hmiddle :
      (m + 1) * (cStar * n) ≤
        q16 * (cStar * n) :=
    Nat.mul_le_mul_right (cStar * n) hm
  have hcapInner :
      3 * clockBudget + Nat.log 2 n + 1 ≤
        5 * q16 := by
    omega
  have hcap :
      lemma19FullActivationClockCap n clockBudget ≤
        1024 * n * (5 * q16) := by
    unfold lemma19FullActivationClockCap
    exact Nat.mul_le_mul_left (1024 * n) hcapInner
  rw [lemma16To19TotalClock_eq]
  calc
    cStar * q16 * n +
          (m + 1) * (cStar * n) +
          lemma19FullActivationClockCap n clockBudget
        ≤
      cStar * q16 * n +
          q16 * (cStar * n) +
          1024 * n * (5 * q16) :=
      add_le_add (add_le_add le_rfl hmiddle) hcap
    _ = (2 * cStar + 5120) * q16 * n := by
      ring

/-- Clock envelope adapted to the common-error choice
`clockBudget = 2q16`. -/
theorem lemma16To19TotalClock_le_two_budget
    (n q16 cStar m clockBudget : ℕ)
    (hq16 : 1 ≤ q16)
    (hm : m + 1 ≤ q16)
    (hbudget : clockBudget ≤ 2 * q16)
    (hlog : Nat.log 2 n ≤ q16) :
    lemma16To19TotalClock n q16 cStar m clockBudget ≤
      (2 * cStar + 8192) * q16 * n := by
  have hmiddle :
      (m + 1) * (cStar * n) ≤
        q16 * (cStar * n) :=
    Nat.mul_le_mul_right (cStar * n) hm
  have hcapInner :
      3 * clockBudget + Nat.log 2 n + 1 ≤
        8 * q16 := by
    omega
  have hcap :
      lemma19FullActivationClockCap n clockBudget ≤
        1024 * n * (8 * q16) := by
    unfold lemma19FullActivationClockCap
    exact Nat.mul_le_mul_left (1024 * n) hcapInner
  rw [lemma16To19TotalClock_eq]
  calc
    cStar * q16 * n +
          (m + 1) * (cStar * n) +
          lemma19FullActivationClockCap n clockBudget
        ≤
      cStar * q16 * n +
          q16 * (cStar * n) +
          1024 * n * (8 * q16) :=
      add_le_add (add_le_add le_rfl hmiddle) hcap
    _ = (2 * cStar + 8192) * q16 * n := by
      ring

/-- Any bound for the composed physical schedule transfers to a first-hitting
bound for the genuine coarse infection chain at the explicit total clock. -/
theorem lemma16To19_coarse_clock_failure_le_of_schedule
    (n q16 k16 cStar m D clockBudget targetGap : ℕ)
    (scale rho : ℕ → ℕ)
    (h3 : 3 ≤ n)
    (hq16 : 0 < q16)
    (hcStar : 0 < cStar)
    (s : InfectionRevealPhysicalState n)
    (ε : ℝ≥0∞)
    (hschedule :
      terminalFailureMass
          (((lemma16PhysicalStageKernel
                n h3 k16 (cStar * q16 * n) s).bind
              (fun z =>
                stagedIter
                  (lemma17LadderKernel
                    n h3 cStar scale rho)
                  m z)).bind
            (fun z =>
              (lemma18FromGapBoundaryKernel
                  n h3 (scale m) D cStar z).bind
                (lemma19FullActivationBudgetKernel
                  n h3 clockBudget)))
          (Lemma19PhysicalStageRangeGood n targetGap)
        ≤ ε) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          (lemma16To19TotalClock
            n q16 cStar m clockBudget)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤ ε := by
  rw [← infectionRevealPhysicalStep_iter_freeze_failure_eq
    n h3 targetGap
      (lemma16To19TotalClock n q16 cStar m clockBudget) s]
  exact
    (lemma16To19_physical_clock_failure_le
      n q16 k16 cStar m D clockBudget targetGap
      scale rho h3 hq16 hcStar s).trans hschedule

/-- The complete parameterized Lemma 16--19 estimate on the genuine coarse
infection clock. -/
theorem lemma16_to_19_coarse_clock_closed
    (n q16 qStage qLadderMajor a16 k16 u16 nu R B
      rho16 cStar m DLadder kLadder uLadder
      qGap F H kGap uGap
      qPrefix qEnd q18Major rhoPrefix rhoEnd D d r18
      Dlabel M targetGap clockBudget : ℕ)
    (scale rho rStage : ℕ → ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q16)
    (hquarter16 : 4 * a16 ≤ n)
    (hcStar16 : 640 ≤ cStar)
    (hroot16 : a16 ^ 5 * q16 * n ≤ n ^ 5)
    (hqa16 : q16 * a16 ≤ rho16 ^ 2)
    (hqaOrder16 : q16 ≤ a16)
    (hrho16 : 1 ≤ rho16)
    (hnu : nu + 1 = n)
    (hk16 : k16 + 1 = a16)
    (hu16 : u16 + k16 + 1 = nu)
    (hRB : R + B = nu)
    (hmajor0 : R ≤ B)
    (hk16pos : 0 < k16)
    (hscale0 : scale 0 = a16)
    (hrho0 : rho 0 = rho16)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (hdouble :
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (hroot :
      ∀ j < m, 19 * rho j ≤ 14 * rho (j + 1))
    (ha :
      ∀ j < m, 4 ≤ scale j)
    (hquarter :
      ∀ j < m, 4 * scale j ≤ n)
    (htarget :
      ∀ j < m, 2 * scale j ≤ n)
    (hrho :
      ∀ j < m, 1 ≤ rho j)
    (hbias :
      ∀ j < m,
        38 * cStar * rho j ≤ scale j)
    (hactiveScale :
      ∀ j < m,
        76 * cStar * rStage j ≤ scale j)
    (hmean :
      ∀ j < m,
        (2 * scale j) ^ 3 ≤
          rStage j * n ^ 2)
    (hqa :
      ∀ j < m,
        qStage * (scale j + 1) ≤
          (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m,
        5 * (scale j + 1) ≤ n + 1)
    (hLadderBR :
      B + R = uLadder + kLadder + 1)
    (hLadderGap :
      R + DLadder ≤ B)
    (hkLadder : 0 < kLadder)
    (hLadderQa :
      qLadderMajor * (kLadder + 1) ≤
        DLadder ^ 2)
    (hLadderQuarter :
      4 * (kLadder + 1) ≤ B + R + 1)
    (hLadderClock :
      ∀ j < m,
        scale j + 1 ≤ 1 + kLadder)
    (hGapBR :
      B + R = uGap + kGap + 1)
    (hInitialGap :
      R + (F + H) ≤ B)
    (hGapShrink :
      (60 * d * D) * (B + R) ≤
        H * (uGap + 1))
    (hkGap : 0 < kGap)
    (hGapQa :
      qGap * (kGap + 1) ≤ F ^ 2)
    (hGapQuarter :
      4 * (kGap + 1) ≤ B + R + 1)
    (hGapClock :
      scale m + 1 ≤ 1 + kGap)
    (ha18 : 4 ≤ scale m)
    (hquarterClock18 :
      4 * scale m ≤ n)
    (hstageRoom18 :
      2 * scale m + 4 ≤ n)
    (hquarterLate :
      n ≤ 4 * (2 * scale m))
    (hpriorRadius :
      cStar * rho m ≤ D)
    (hprefixRadius :
      rhoPrefix + 1 = D)
    (hendRadius :
      rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (scale m + 1) ≤
        rhoPrefix ^ 2)
    (hendQa :
      qEnd * (scale m + 1) ≤
        rhoEnd ^ 2)
    (hmajorQa :
      q18Major * (scale m + 2) ≤
        (60 * d * D) ^ 2)
    (hlabelRoom18 :
      5 * scale m + 8 ≤ n)
    (hmeanActive18 :
      (2 * scale m) ^ 3 ≤ r18 * n ^ 2)
    (hguardScale :
      60 * D ≤ scale m)
    (hreactionScale :
      1200 * cStar * r18 ≤ 7 * scale m)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hlabelScale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (hPoolScale :
      ∀ z : InfectionRevealPhysicalState n,
        Lemma17GapBoundaryGood
            (scale m) cStar (rho m) z →
          z.inactive.ids.card ≤
            lemma17StageRemaining (scale m) z * d)
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          (lemma16To19TotalClock
            n q16 cStar m clockBudget)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤
        ((3 * lemma16UrnError q16 +
            ∑ j ∈ Finset.range m,
              (lemma17StageError
                  (scale j) qStage cStar
                  (rho j) (rStage j) +
                lemma16UrnError qLadderMajor)) +
          lemma16UrnError qGap) +
        ((lemma18StageError
              qPrefix qEnd (scale m) cStar r18 D +
            lemma16UrnError q18Major) +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget M targetGap L) := by
  have hq16pos : 0 < q16 := by
    have hlogpos :
        0 < Nat.log 2 n :=
      Nat.log_pos (by omega) (by omega)
    omega
  apply
    lemma16To19_coarse_clock_failure_le_of_schedule
      n q16 k16 cStar m D clockBudget targetGap
      scale rho h3 hq16pos (by omega) s
  exact
    lemma16_to_19_positive_gap_closed
      n q16 qStage qLadderMajor a16 k16 u16 nu R B
      rho16 cStar m DLadder kLadder uLadder
      qGap F H kGap uGap
      qPrefix qEnd q18Major rhoPrefix rhoEnd D d r18
      Dlabel M targetGap clockBudget
      scale rho rStage L
      h3 hlog hquarter16 hcStar16 hroot16 hqa16
      hqaOrder16 hrho16 hnu hk16 hu16 hRB hmajor0
      hk16pos hscale0 hrho0 hcStar hcTwo hdouble
      hroot ha hquarter htarget hrho hbias hactiveScale
      hmean hqa hlabelRoom hLadderBR hLadderGap
      hkLadder hLadderQa hLadderQuarter hLadderClock
      hGapBR hInitialGap hGapShrink hkGap hGapQa
      hGapQuarter hGapClock ha18 hquarterClock18
      hstageRoom18 hquarterLate hpriorRadius
      hprefixRadius hendRadius hprefixQa hendQa hmajorQa
      hlabelRoom18 hmeanActive18 hguardScale
      hreactionScale hbudget hgap0 hgapn hDlabel hL
      hlabelScale hPoolScale s hx0 hy0

/-- A fully activated coarse endpoint with the stated positive gap satisfies
the ordinary-Tri initial condition. -/
theorem infectionActivationGapRangeGood_to_assemblyInitial
    (n γ targetGap : ℕ)
    (s : InfectionState n)
    (hs : InfectionActivationGapRangeGood n targetGap s)
    (hgapSq :
      γ * n * Nat.log 2 n ≤ targetGap ^ 2) :
    s.1.AllActive ∧ AssemblyInitial n γ s.1.ax := by
  have hinv := s.2
  have hall :
      s.1.AllActive :=
    InfectionState.allActive_of_total_le_active s hs.1
  rcases hall with ⟨hix, hiy⟩
  unfold InfectionActivationGapRangeGood at hs
  simp only [InfectionCfg.Inv, InfectionCfg.total,
    InfectionCfg.active, InfectionCfg.inactive] at hinv
  refine
    ⟨⟨hix, hiy⟩,
      ?_⟩
  constructor
  · omega
  · refine ⟨targetGap, ?_, hgapSq⟩
    omega

/-- Starting from one physical refinement, a frozen activation hit followed
immediately by ordinary-Tri convergence yields consensus for the unpaused
coarse infection chain. -/
theorem infectionRawHit_then_tri_consensus
    (n γ targetGap Tactivate Ttri : ℕ)
    (h3 : 3 ≤ n)
    (hTactivate : 0 < Tactivate)
    (hTtri : 0 < Ttri)
    (s : InfectionRevealPhysicalState n)
    (εactivate εtri : ℝ≥0∞)
    (hgapSq :
      γ * n * Nat.log 2 n ≤ targetGap ^ 2)
    (hactivate :
      terminalFailureMass
          (iter
            (freeze
              (InfectionActivationGapRangeGood n targetGap)
              (infectionStateStep n h3))
            Tactivate (infectionRevealPhysicalForget s))
          (InfectionActivationGapRangeGood n targetGap)
        ≤ εactivate)
    (htri :
      Reaches
        (triChain n) Ttri
        (AssemblyInitial n γ)
        (fun x => n ≤ x) εtri) :
    terminalFailureMass
        (iter
          (infectionStateStep n h3)
          (Tactivate + Ttri)
          (infectionRevealPhysicalForget s))
        InfectionXConsensus
      ≤ εactivate + εtri := by
  have hpost :
      Reaches
        (infectionStateStep n h3) Ttri
        (InfectionActivationGapRangeGood n targetGap)
        InfectionXConsensus εtri := by
    have hbase :=
      infectionReaches_consensus_of_triReaches
        n h3 htri
    intro z hz
    exact hbase z
      (infectionActivationGapRangeGood_to_assemblyInitial
        n γ targetGap z hz hgapSq)
  have hfull :
      Reaches
        (infectionStateStep n h3)
        (Tactivate + Ttri)
        (fun z =>
          z = infectionRevealPhysicalForget s)
        InfectionXConsensus
        (εactivate + εtri) := by
    apply Reaches.comp_of_frozen_hit
      (infectionStateStep n h3)
      (A := fun z =>
        z = infectionRevealPhysicalForget s)
      (P := InfectionActivationGapRangeGood n targetGap)
      (R := InfectionXConsensus)
      (T₁ := Tactivate) (T₂ := Ttri)
      (ε₁ := εactivate) (ε₂ := εtri)
      hTactivate hTtri
    · intro z hz
      subst z
      exact hactivate
    · exact hpost
    · exact infectionStateStep_consensus n h3
  exact hfull (infectionRevealPhysicalForget s) rfl

/-- The proved ordinary-Tri headline supplies the continuation uniformly after
any quantitative full-activation hit. -/
theorem infectionRawHit_then_theorem1b :
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ targetGap Tactivate : ℕ,
        ∀ h3 : 3 ≤ n,
        ∀ s : InfectionRevealPhysicalState n,
        ∀ εactivate : ℝ≥0∞,
        n₀ ≤ n →
        1 ≤ γ →
        6 * γ * Nat.log 2 n ≤ n →
        γ * n * Nat.log 2 n ≤ targetGap ^ 2 →
        0 < Tactivate →
        terminalFailureMass
            (iter
              (freeze
                (InfectionActivationGapRangeGood n targetGap)
                (infectionStateStep n h3))
              Tactivate (infectionRevealPhysicalForget s))
            (InfectionActivationGapRangeGood n targetGap)
          ≤ εactivate →
        terminalFailureMass
            (iter
              (infectionStateStep n h3)
              (Tactivate +
                C * γ * n * Nat.log 2 n)
              (infectionRevealPhysicalForget s))
            InfectionXConsensus
          ≤
            εactivate +
              (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ)) := by
  rcases theorem1b_reaches_top with
    ⟨C, n₀, c, hC, hc, hn₀, htri⟩
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro n γ targetGap Tactivate h3 s εactivate
    hn hγ hsize hgapSq hTactivate hactivate
  have hTtri :
      0 < C * γ * n * Nat.log 2 n := by
    have hlogpos :
        0 < Nat.log 2 n :=
      Nat.log_pos (by omega) (by omega)
    positivity
  exact
    infectionRawHit_then_tri_consensus
      n γ targetGap Tactivate
      (C * γ * n * Nat.log 2 n)
      h3 hTactivate hTtri s
      εactivate
      ((n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ)))
      hgapSq hactivate
      (htri n γ hn hγ hsize)

end

end Tri

#print axioms Tri.lemma16To19_coarse_clock_failure_le_of_schedule
#print axioms Tri.lemma16_to_19_coarse_clock_closed
#print axioms Tri.lemma16To19TotalClock_pos
#print axioms Tri.lemma16To19TotalClock_eq
#print axioms Tri.lemma16To19TotalClock_le
#print axioms Tri.lemma16To19TotalClock_le_two_budget
#print axioms Tri.infectionActivationGapRangeGood_to_assemblyInitial
#print axioms Tri.infectionRawHit_then_tri_consensus
#print axioms Tri.infectionRawHit_then_theorem1b
