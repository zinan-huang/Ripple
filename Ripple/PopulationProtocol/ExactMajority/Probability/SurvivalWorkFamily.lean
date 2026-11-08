/-
# Hypotheses — the TRULY-FRESH V5.1 work inputs and survival work family.

Extracted from `WorkBuilder.lean` to isolate the `SurvivalWorkHypotheses` record and `workSurvivalFull`
work family from the chain-level residual bundle (`ResidualAtomsFull`) and the headline theorems.

These definitions depend on `WindowSurvival` (which provides `HonestDrainSlots` → `SlotEngine` →
`DrainEngine` → `DrainRates` + all Phase*Convergence transitively) — no `AtomsV2`, `ChainEndRecut`,
`OffEventEndgame`, `TimelineReconciliation`, or `SurvivalInputs`.

`WorkBuilder.lean` imports this file and re-exports all names in the same `Ripple.PopulationProtocol.ExactMajority.WorkBuilder`
namespace, so downstream consumers that import `WorkBuilder` see these definitions unchanged.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.WindowSurvival
import Ripple.PopulationProtocol.ExactMajority.Probability.TightEpidemicWork

namespace Ripple.PopulationProtocol.ExactMajority
namespace WorkBuilder

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — `SurvivalWorkHypotheses`: the TRULY-FRESH work inputs (no nested `LevelsWorkHypotheses`).

Flat record carrying EXACTLY the live fields the V5 proof terms consume.  No `base`, hence none of the
eight dead V2 fields (`hM₀`, `hext1`, `hpull1`, `hClosed6`, `hPhase6Post7`, `hE7`, `hPhase7Post8`,
`hE8`).  Slots 1/6/7/8 on the `WindowSurvival` survival engine (escape budgets `hescW*` + `hescε*`
REPLACE the exact closures); slots 0/2/3/4/5/9/10 carried via the thin constructors directly. -/
structure SurvivalWorkHypotheses (n : ℕ) where
  -- ===== common scalars / regime data (consumed across many slots) =====
  /-- The dyadic minority sign (slots 7/8). -/
  σ : Sign
  /-- Common budget level `M₀`. -/
  M₀ : ℕ
  hn : 2 ≤ n
  hM1 : 1 ≤ M₀
  -- ===== slots 0/3 — carried finished instances =====
  work0 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work3 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  -- ===== slot 1 — survival inputs (escape budget REPLACES `hClosed1`) =====
  /-- slot-1 partner-pool floor `P1 ≤ pullPos`. -/
  P1 : ℕ
  tWin1 : ℕ → ℕ
  /-- slot-1 per-step ESCAPE budget probability `η₁` (the at-risk counter tail). -/
  η1 : ℝ≥0∞
  /-- slot-1 escape budget `hescW1` — REPLACES `hClosed1`. -/
  hescW1 : ∀ x, PhaseOnlyWindows.Phase1Win (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n y} ≤ η1
  hext1H : ∀ b : Config (AgentState L K), PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b →
    1 ≤ (DrainThreading.extremePosSet L K).sum b.count
  hpull1H : ∀ b : Config (AgentState L K), PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b →
    P1 ≤ (DrainThreading.pullPosSet L K).sum b.count
  hpt1 : ∀ m ∈ Finset.Icc 1 M₀, (DrainEngine.qHat P1 n m) ^ (tWin1 m) ≤
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε1 : ℝ≥0
  hescε1 : (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η1 ≤ (escapeε1 : ℝ≥0∞)
  -- ===== slot 5 — HONEST levels drain + concentration (closure CARRIED — the honest exception) =====
  i5 : Fin (L + 1)
  K₀ : ℕ
  /-- slot-5 biased-Main floor `P5 ≤ usefulMains` (Theorem 6.2 biased structure). -/
  P5 : ℕ
  tWin5 : ℕ → ℕ
  hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
  hmain5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
    P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count
  hpt5 : ∀ m ∈ Finset.Icc 1 M₀, (DrainEngine.qHat P5 n m) ^ (tWin5 m) ≤
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  εConc : ℝ≥0
  hConc : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
    ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
    ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
      {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} ≤ (εConc : ℝ≥0∞)
  -- ===== slot 6 — generic survival inputs (escape budget REPLACES `hClosed6`) =====
  /-- The Phase-6 band level `l`. -/
  l : ℕ
  q6 : ℕ → ℝ≥0∞
  tWin6 : ℕ → ℕ
  hdrop6 : ∀ m, ∀ b : Config (AgentState L K),
    Phase6Convergence.Phase6Win (L := L) (K := K) n b →
    Phase6Convergence.highMass (L := L) (K := K) l b = m →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potBelow
        (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ ≤ q6 m
  hpt6 : ∀ m ∈ Finset.Icc 1 M₀, (q6 m) ^ (tWin6 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  η6 : ℝ≥0∞
  hescW6 : ∀ x, Phase6Convergence.Phase6Win (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y} ≤ η6
  /-- slot-6 per-level rate floor `1 ≤ q6 0` (the survival engine's `m = 0` filler). -/
  hq6zero : (1 : ℝ≥0∞) ≤ q6 0
  escapeε6 : ℝ≥0
  hescε6 : (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) * η6 ≤ (escapeε6 : ℝ≥0∞)
  -- ===== slot 7 — survival inputs (escape budget REPLACES `hClosed7`) =====
  /-- The Phase-7 eliminator-margin count `E7` (Lemma 7.4). -/
  E7 : ℕ
  tWin7 : ℕ → ℕ
  η7 : ℝ≥0∞
  hescW7 : ∀ x, PhaseOnlyWindows.Phase7Win (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ PhaseOnlyWindows.Phase7Win (L := L) (K := K) n y} ≤ η7
  hwit7 : ∀ b : Config (AgentState L K), PhaseOnlyWindows.Phase7Win (L := L) (K := K) n b →
    Phase7Convergence.classMassN σ b ≥ 1 →
    ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
      E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count
  hpt7 : ∀ m ∈ Finset.Icc 1 M₀, (DrainEngine.qHat E7 n m) ^ (tWin7 m) ≤
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε7 : ℝ≥0
  hescε7 : (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) * η7 ≤ (escapeε7 : ℝ≥0∞)
  -- ===== slot 8 — survival inputs (escape budget REPLACES `hClosed8`) =====
  /-- The Phase-8 above-level eliminator-margin count `E8` (Lemma 7.6). -/
  E8 : ℕ
  tWin8 : ℕ → ℕ
  η8 : ℝ≥0∞
  hescW8 : ∀ x, PhaseOnlyWindows.Phase8Win (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ PhaseOnlyWindows.Phase8Win (L := L) (K := K) n y} ≤ η8
  hwit8 : ∀ b : Config (AgentState L K), PhaseOnlyWindows.Phase8Win (L := L) (K := K) n b →
    Phase7Convergence.minorityU σ b ≥ 1 →
    ∃ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
      E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count
  hpt8 : ∀ m ∈ Finset.Icc 1 M₀, (DrainEngine.qHat E8 n m) ^ (tWin8 m) ≤
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε8 : ℝ≥0
  hescε8 : (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) * η8 ≤ (escapeε8 : ℝ≥0∞)
  -- ===== slot 10 — Phase-10 block-geometric (carried scalar inputs) =====
  s10 : ℕ
  hs10 : 0 < s10
  hsB10 : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
    ≤ (s10 : ℝ≥0∞)
  k10 : ℕ

/-- **The V5.1 SURVIVAL work family** `Fin 11 → PhaseConvergenceW`, built from the FRESH
`SurvivalWorkHypotheses`.  Slots 1/7/8 on `WindowSurvival.slot{1,7,8}Survival`, slot 6 on the generic
`WindowSurvival.slotSurvival`; slots 0/2/3/4/5/9/10 restated AGAINST THE FRESH FIELDS via the thin
constructors directly (no `levelsWorkFamily wi.base`, hence no dead V2 baggage). -/
noncomputable def workSurvivalFull {n : ℕ} (wi : SurvivalWorkHypotheses (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun k =>
    match k with
    | ⟨0, _⟩ => wi.work0
    | ⟨1, _⟩ => WindowSurvival.phase1Survival (L := L) (Kp := K) wi.P1 wi.M₀ wi.hn
        wi.hM1 wi.η1 wi.hescW1 wi.hext1H wi.hpull1H wi.tWin1 wi.hpt1 wi.escapeε1 wi.hescε1
    | ⟨2, _⟩ => TightEpidemicWork.work2Tight (L := L) (K := K) wi.hn
    | ⟨3, _⟩ => wi.work3
    | ⟨4, _⟩ => TightEpidemicWork.work4Tight (L := L) (K := K) wi.hn
    | ⟨5, _⟩ =>
        DrainEngine.phase5LevelsWork wi.i5 wi.K₀ wi.M₀ wi.P5 wi.hClosed5 wi.hn wi.hM1 wi.hmain5
          wi.tWin5 wi.hpt5 wi.εConc wi.hConc
    | ⟨6, _⟩ => WindowSurvival.slotSurvival (NonuniformMajority L K).transitionKernel
        (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c)
        (fun c => Phase6Convergence.highMass (L := L) (K := K) wi.l c)
        (Phase6Convergence.potNonincrOn_highMass (L := L) (K := K) wi.l n)
        wi.q6 wi.hq6zero wi.hdrop6 wi.η6 wi.hescW6
        wi.tWin6 wi.M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) wi.escapeε6
        (DrainCalibration.rect_sum_le_phase_budget wi.hn wi.hM1 wi.q6 wi.tWin6
          wi.hpt6 |>.trans_eq (by rw [show ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞)
            = ENNReal.ofReal (1 / (n : ℝ) ^ 2) from by rw [ENNReal.ofReal]]))
        wi.hescε6
    | ⟨7, _⟩ => WindowSurvival.phase7Survival (L := L) (Kp := K) wi.σ wi.E7 wi.M₀
        wi.hn wi.hM1 wi.η7 wi.hescW7 wi.hwit7 wi.tWin7 wi.hpt7 wi.escapeε7 wi.hescε7
    | ⟨8, _⟩ => WindowSurvival.phase8Survival (L := L) (Kp := K) wi.σ wi.E8 wi.M₀
        wi.hn wi.hM1 wi.η8 wi.hescW8 wi.hwit8 wi.tWin8 wi.hpt8 wi.escapeε8 wi.hescε8
    | ⟨9, _⟩ => TightEpidemicWork.work9Tight (L := L) (K := K) wi.hn
    | ⟨10, _⟩ =>
        Phase10Drop.phase10Convergence (L := L) (K := K) n wi.hn wi.s10 wi.hs10 wi.hsB10 wi.k10
    | ⟨m + 11, h⟩ => absurd h (by omega)

end WorkBuilder
end Ripple.PopulationProtocol.ExactMajority
