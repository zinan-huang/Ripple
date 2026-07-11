/-
# DrainEngine — the guarded per-level rate `qHat` and the four honest levels-engine slots.

Extracted from `SlotEngine.lean` to isolate the drain-engine utility definitions (qHat, the
per-level rate padding, and the honest slot constructors for slots 1/5/7/8) from the chain-level
assembly types (`ResidualAtoms`, `WorkInputsHonest`, `workHonest`, `phases'`, the whp headline).

These definitions depend only on `DrainRates` (which transitively provides `DrainCalibration`,
`OneSidedCancel`, `EliminatorMargins`, `Phase{1,5,6,7,8}Convergence`, `ReserveSampling`,
`DrainThreading`, etc.) — no `SeedTrigWiring`, `BudgetTightening`, or `PaperRegime`.

`SlotEngine.lean` imports this file and re-exports all names in the same `ExactMajority.SlotEngine`
namespace, so downstream consumers that import `SlotEngine` see these definitions unchanged.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainRates

namespace ExactMajority
namespace SlotEngine

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 0 — the guarded per-level rate `qHat`.

`levels_PhaseConvergenceW` requires the per-level drop binder `hdrop` at EVERY `m` (including `m = 0`),
but the landed `DrainRates.hdrop{5,7,8}_of_chain` are guarded by `1 ≤ m` (the honest floor is only
defined for a positive active mass).  `qHat E n` is the per-level rate `levelRate E n` capped at `1`
for `m = 0`; since `potBelow Φ 0 = ∅` (every config is "not below 0"), the `m = 0` binder is the
trivial probability bound `K b univ ≤ 1`, and the failure budget — a sum over `Icc 1 M₀` — never sees
`m = 0`, so `qHat` agrees with `levelRate` everywhere the budget reads.  This is the standard
level-engine padding, not a weakening: the honest per-level rate is used at every `m ≥ 1`. -/

/-- The guarded per-level drain rate: `1` at level `0`, the honest `levelRate E n m` at `m ≥ 1`. -/
noncomputable def qHat (E n : ℕ) : ℕ → ℝ≥0∞ :=
  fun m => if 1 ≤ m then DrainRates.levelRate E n m else 1

theorem qHat_eq_on_pos (E n m : ℕ) (hm : 1 ≤ m) : qHat E n m = DrainRates.levelRate E n m := by
  simp [qHat, hm]

theorem qHat_zero (E n : ℕ) : qHat E n 0 = 1 := by simp [qHat]

/-- The `m = 0` binder is trivial: `K b (potBelow Φ 0)ᶜ ≤ 1 = qHat E n 0` (any probability ≤ 1). -/
theorem qHat_zero_bound {α : Type*} [MeasurableSpace α] {Kr : ProbabilityTheory.Kernel α α}
    [IsMarkovKernel Kr] (E n : ℕ) (Φ : α → ℕ) (b : α) :
    Kr b (OneSidedCancel.potBelow Φ 0)ᶜ ≤ qHat E n 0 := by
  rw [qHat_zero]
  exact le_trans (measure_mono (Set.subset_univ _)) (by simp [prob_le_one])

/-- The level-sum budget at `qHat` reduces to `ENNReal.ofReal (1/n²)` via `rect_sum_le_phase_budget`
(the sum is over `Icc 1 M₀`, where `qHat = levelRate`, so the budget calibration applies). -/
theorem qHat_sum_budget {E n M₀ : ℕ} (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (tWin : ℕ → ℕ)
    (hpt : ∀ m ∈ Finset.Icc 1 M₀, (qHat E n m) ^ (tWin m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    (∑ m ∈ Finset.Icc 1 M₀, (qHat E n m) ^ (tWin m))
      ≤ ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) := by
  have h := DrainCalibration.rect_sum_le_phase_budget hn hM1 (qHat E n) tWin hpt
  rwa [show ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (1 / (n : ℝ) ^ 2) from by rw [ENNReal.ofReal]]

/-! ## Part 1 — the four honest levels-engine slots (1, 5, 7, 8).

Each is `OneSidedCancel.levels_PhaseConvergenceW` over the SAME `Inv`/`Φ` as the crude slot (so the
`Pre = Inv ∧ Φ ≤ M₀`, `Post = Inv ∧ Φ = 0` profile matches the crude family exactly and the bridges
connect), with:
* `hClosed`/`hmono` the PROVED structural inputs (`invClosed_*`/`potNonincrOn_*`);
* `hdrop` the LANDED per-level rate (`DrainRates.hdrop{1,5,7,8}_of_chain`) padded at `m = 0`;
* the per-level budget `hpt` carried (the genuinely-probabilistic geometric-tail input). -/

/-- **Honest slot 1** — `extremeU` averaging drain on the LEVELS engine (Lemma 5.3 / [45]).  Consumes
the per-level rate `DrainRates.hdrop1_of_chain` (from the +3 extreme witness `hext` and the partner
pool floor `hpull`); the crude single-step `potDone` rate is GONE. -/
noncomputable def slot1Honest {n : ℕ} (P1 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hext : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      P1 ≤ (DrainThreading.pullPosSet L K).sum b.count)
    (tWin1 : ℕ → ℕ)
    (hpt1 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P1 n m) ^ (tWin1 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase1Convergence.Phase1AllMain (L := L) (K := K) n c)
    (Phase1Convergence.invClosed_phase1AllMain n)
    (fun c => Phase1Convergence.extremeU c)
    (Phase1Convergence.potNonincrOn_extremeU n)
    (qHat P1 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact qHat_zero_bound _ _ _ _
      · rw [qHat_eq_on_pos _ _ _ hmpos]
        exact DrainRates.hdrop1_of_chain hn P1 hext hpull m b hInv hbm)
    tWin1 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (qHat_sum_budget hn hM1 tWin1 hpt1)

/-- The slot-7 per-level drop floor from the eliminator margin, INLINED (replicates
`AssemblyWiring.slot7_levels_hdrop` without a `WorkInputs` wrapper, so the margin field is consumed
directly).  At any `Inv7Sum` config with `classMassN σ = m ≥ 1`, the gap-1 eliminator margin
`hPhase6Post7` gives the per-level drop floor `≤ levelRate E7 n m`. -/
theorem slot7_hdrop_direct {n : ℕ} (σ : Sign) (E7 : ℕ) (hn : 2 ≤ n)
    (hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15)
    (hPhase6Post7 : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b)
    {m : ℕ} (hmpos : 1 ≤ m) (b : Config (AgentState L K))
    (hInv : Phase7Convergence.Inv7Sum n b) (hbm : Phase7Convergence.classMassN σ b = m) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ
      ≤ DrainRates.levelRate E7 n m := by
  have hb7 : Phase7Convergence.Phase7AllMain (L := L) (K := K) n b := hInv.1
  have hmass : 1 ≤ Phase7Convergence.classMassN σ b := by omega
  have hfloor :
      ∃ i j : Fin (L + 1),
        i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
        E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count :=
    EliminatorMargins.lemma7_4_phase7_elimGap1_floor σ hb7 E7 (hPhase6Post7 b hInv) hmass hE7
  exact EliminatorMargins.phase7_hdrop_wired_from_lemma7_4 σ n m hn b hb7 hbm hmpos E7 hfloor

/-- The slot-8 per-level drop floor from the above-level eliminator margin, INLINED (replicates
`AssemblyWiring.slot8_levels_hdrop`). -/
theorem slot8_hdrop_direct {n : ℕ} (σ : Sign) (E8 : ℕ) (hn : 2 ≤ n)
    (hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5)
    (hPhase7Post8 : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b)
    {m : ℕ} (hmpos : 1 ≤ m) (b : Config (AgentState L K))
    (hb8 : Phase8Convergence.Phase8AllMain n b) (hbm : Phase7Convergence.minorityU σ b = m) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
      ≤ DrainRates.levelRate E8 n m := by
  have hmin : 1 ≤ Phase7Convergence.minorityU σ b := by omega
  have hexists :
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count := by
    obtain ⟨i, hmini⟩ := EliminatorMargins.exists_minorityAt_of_minorityU_pos σ b hmin
    exact ⟨i, hmini, EliminatorMargins.lemma7_6_phase8_elimAbove_floor σ hb8 E8
      (hPhase7Post8 b hb8) i hmini hE8⟩
  exact EliminatorMargins.phase8_hdrop_wired_from_lemma7_6 σ n m hn b hb8 hbm hmpos E8 hexists

/-- **Honest slot 7** — `classMassN` eliminator drain on the LEVELS engine (Doty Lemma 7.4).  Consumes
the gap-1 eliminator margin `hPhase6Post7` directly (the PROVED minority witness is inside
`slot7_hdrop_direct`).  The crude `hstep7` rate is GONE; the eliminator margin is now ON the proof
path. -/
noncomputable def slot7Honest {n : ℕ} (σ : Sign) (E7 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15)
    (hPhase6Post7 : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b)
    (tWin7 : ℕ → ℕ)
    (hpt7 : ∀ m ∈ Finset.Icc 1 M₀, (qHat E7 n m) ^ (tWin7 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase7Convergence.Inv7Sum (L := L) (K := K) n c)
    (Phase7Convergence.invClosed_Inv7Sum n)
    (fun c => Phase7Convergence.classMassN σ c)
    (Phase7Convergence.potNonincrOn_classMassN σ n)
    (qHat E7 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact qHat_zero_bound _ _ _ _
      · rw [qHat_eq_on_pos _ _ _ hmpos]
        exact slot7_hdrop_direct σ E7 hn hE7 hPhase6Post7 hmpos b hInv hbm)
    tWin7 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (qHat_sum_budget hn hM1 tWin7 hpt7)

/-- **Honest slot 8** — `minorityU` eliminator drain on the LEVELS engine (Doty Lemma 7.6).  Consumes
the above-level eliminator margin `hPhase7Post8` directly.  The crude `hstep8` rate is GONE; the
margin is ON the proof path. -/
noncomputable def slot8Honest {n : ℕ} (σ : Sign) (E8 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5)
    (hPhase7Post8 : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b)
    (tWin8 : ℕ → ℕ)
    (hpt8 : ∀ m ∈ Finset.Icc 1 M₀, (qHat E8 n m) ^ (tWin8 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase8Convergence.Phase8AllMain (L := L) (K := K) n c)
    (Phase8Convergence.invClosed_phase8AllMain n)
    (fun c => Phase7Convergence.minorityU σ c)
    (Phase8Convergence.potNonincrOn_minorityU σ n)
    (qHat E8 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact qHat_zero_bound _ _ _ _
      · rw [qHat_eq_on_pos _ _ _ hmpos]
        exact slot8_hdrop_direct σ E8 hn hE8 hPhase7Post8 hmpos b hInv hbm)
    tWin8 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (qHat_sum_budget hn hM1 tWin8 hpt8)

/-! ## Part 2 — the honest slot 5 (levels drain ∘ sampling concentration).

Slot 5 is the composite drain (`unsampledReserveU → 0`) ∩ concentration (`sampledFloor`).  The honest
build replaces the crude drain (`ReserveSampling.phase5SampledConvergence`, crude `potDone`) with the
LEVELS drain on `unsampledReserveU` (consuming `DrainRates.hdrop5_of_chain`), then composes with the
carried sampling concentration `hConc` at the levels horizon `∑ tWin5 m` — mirroring
`Phase5Convergence.phase5Convergence`, with the same `Pre`/`Post` profile
(`Pre = Phase5AllWin ∧ unsampledReserveU ≤ M₀`, `Post = Phase5AllWin ∧ ReserveSampleGood`). -/

/-- The honest levels drain for `unsampledReserveU` (slot-5 drain half), consuming
`DrainRates.hdrop5_of_chain` (the biased-Main floor `hmain5`).  Post `= Phase5AllWin ∧
unsampledReserveU = 0 = ReserveSampled`. -/
noncomputable def slot5DrainLevels {n : ℕ} (P5 M₀ : ℕ)
    (hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c))
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hmain5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count)
    (tWin5 : ℕ → ℕ)
    (hpt5 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P5 n m) ^ (tWin5 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    hClosed5
    (fun c => ReserveSampling.unsampledReserveU (L := L) (K := K) c)
    (ReserveSampling.potNonincrOn_unsampledReserveU n)
    (qHat P5 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact qHat_zero_bound _ _ _ _
      · rw [qHat_eq_on_pos _ _ _ hmpos]
        exact DrainRates.hdrop5_of_chain hn P5 hmain5 m hmpos b hInv hbm)
    tWin5 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (qHat_sum_budget hn hM1 tWin5 hpt5)

/-- **Honest slot 5** — the levels drain composed with the sampling concentration `hConc` (Lemma 7.1)
at the levels horizon `∑ tWin5 m`.  `Pre = Phase5AllWin ∧ unsampledReserveU ≤ M₀`,
`Post = Phase5AllWin ∧ ReserveSampleGood i5 K₀`.  The crude reserve-drain rate `hstep5` is GONE. -/
noncomputable def slot5Honest {n : ℕ} (i5 : Fin (L + 1)) (K₀ M₀ P5 : ℕ)
    (hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c))
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hmain5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count)
    (tWin5 : ℕ → ℕ)
    (hpt5 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P5 n m) ^ (tWin5 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (εConc : ℝ≥0)
    (hConc : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
      ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
        {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} ≤ (εConc : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
    ReserveSampling.unsampledReserveU (L := L) (K := K) c ≤ M₀
  Post c := ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
    Phase5Convergence.ReserveSampleGood (L := L) (K := K) i5 K₀ c
  t := ∑ m ∈ Finset.Icc 1 M₀, tWin5 m
  ε := Real.toNNReal (1 / (n : ℝ) ^ 2) + εConc
  convergence := by
    intro c₀ hPre
    obtain ⟨hwin, hbud⟩ := hPre
    set P5d := slot5DrainLevels P5 M₀ hClosed5 hn hM1 hmain5 tWin5 hpt5 with hP5d
    have hsampled := P5d.convergence c₀ ⟨hwin, hbud⟩
    have hcover : {c : Config (AgentState L K) |
        ¬ (ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
            Phase5Convergence.ReserveSampleGood (L := L) (K := K) i5 K₀ c)}
          ⊆ {c | ¬ P5d.Post c} ∪ {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} := by
      intro c hc
      simp only [Set.mem_setOf_eq, Set.mem_union] at hc ⊢
      by_cases hfloor : Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c
      · left; intro hContra
        exact hc ⟨hContra.1, hContra.2, hfloor⟩
      · exact Or.inr hfloor
    calc ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
            {c | ¬ (ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
              Phase5Convergence.ReserveSampleGood (L := L) (K := K) i5 K₀ c)}
        ≤ ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
            ({c | ¬ P5d.Post c} ∪ {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
            {c | ¬ P5d.Post c}
          + ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
            {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} := measure_union_le _ _
      _ ≤ (Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0∞) + (εConc : ℝ≥0∞) := by
          gcongr
          · exact hsampled
          · exact hConc c₀ hwin hbud
      _ = ((Real.toNNReal (1 / (n : ℝ) ^ 2) + εConc : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_add]

end SlotEngine
end ExactMajority
