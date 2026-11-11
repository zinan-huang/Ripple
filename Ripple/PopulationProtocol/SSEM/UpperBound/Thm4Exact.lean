import Ripple.PopulationProtocol.SSEM.UpperBound.Thm4Final

/-!
# Exact Kanaya Theorem 4 window and time constants


Retain the unrounded six-stage horizon and success product, transfer them
to every finite configuration, and derive the constants 5213 and 4170.
-/

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped ENNReal

/-- The exact six-stage success probability, with no probability rounding. -/
theorem paper_stage_success_product :
    ENNReal.ofReal 0.86 *
      (ENNReal.ofReal 0.915 *
        (ENNReal.ofReal 0.515 *
          (ENNReal.ofReal 0.997 *
            (ENNReal.ofReal 0.515 * ENNReal.ofReal 0.999)))) =
        ENNReal.ofReal ((83148542562663 : ℝ) / 400000000000000) ∧
    (5 : ℝ≥0∞)⁻¹ <
      ENNReal.ofReal ((83148542562663 : ℝ) / 400000000000000) := by
  constructor
  · rw [← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1 <;> norm_num
  · rw [show (5 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 5) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

/-- Export of the local `sAll` in `pemPaperWindow_of_stages`, before
either the horizon or the success probability is rounded. -/
theorem pemPaperWindow_exact_of_stages
    (hA : StageA) (hA' : StageA') (h1 : Epoch1) (hC : StageC)
    (h2 : Epoch2) (hE : StageE) :
    ∀ (n : ℕ), 1608 ≤ n → ∀ (hn : 0 < n) (hn2 : 2 ≤ n)
      (X : Config (AgentState n) Opinion n), GoodPaper X →
      ENNReal.ofReal 0.86 *
        (ENNReal.ofReal 0.915 *
          (ENNReal.ofReal 0.515 *
            (ENNReal.ofReal 0.997 *
              (ENNReal.ofReal 0.515 * ENNReal.ofReal 0.999)))) ≤
        probHitBy (PEM40 n hn) hn2 X IsSilentConsensus
          (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) := by
  classical
  intro n hN hn hn2 X hX
  set P := PEM40 n hn
  have hG : ∀ C, GoodPaper C → ∀ i j : Fin n, GoodPaper (C.step P i j) :=
    fun C hC i j => goodPaper_step hn2 C hC i j
  set KB := tOne n + 4 * n * (n - 1) + 75 * n ^ 2
  set qA := ENNReal.ofReal 0.86
  set qA' := ENNReal.ofReal 0.915
  set qB := ENNReal.ofReal 0.515
  set qC := ENNReal.ofReal 0.997
  set qE := ENNReal.ofReal 0.999
  have hqB1 : qB ≤ 1 := ENNReal.ofReal_le_one.mpr (by norm_num)
  have hqA'1 : qA' ≤ 1 := ENNReal.ofReal_le_one.mpr (by norm_num)
  have sE := hE n hN hn hn2
  have sZ := stage_compose P hn2 GoodPaper hG ZTwo IsConsensusConfig IsSilentConsensus KB
    (308 * n ^ 2) qB qE (h2 n hN hn hn2) sE
  have sEmZ := stage_or P hn2 GoodPaper IsSilentConsensus ZTwo IsSilentConsensus
    (KB + 308 * n ^ 2) (qB * qE)
    (stage_goal P hn2 GoodPaper IsSilentConsensus _ _
      (mul_le_one' hqB1 (ENNReal.ofReal_le_one.mpr (by norm_num)))) sZ
  have sD := stage_compose P hn2 GoodPaper hG Decided
    (fun C => IsSilentConsensus C ∨ ZTwo C) IsSilentConsensus
    (311 * n ^ 2) (KB + 308 * n ^ 2) qC (qB * qE) (hC n hN hn hn2) sEmZ
  set VD := 311 * n ^ 2 + (KB + 308 * n ^ 2)
  set qD := qC * (qB * qE)
  have sPT := stage_compose P hn2 GoodPaper hG PTL Decided IsSilentConsensus KB VD qB qD
    (h1 n hN hn hn2) sD
  have sDPT := stage_or P hn2 GoodPaper Decided PTL IsSilentConsensus (KB + VD) (qB * qD)
    (stage_mono P hn2 GoodPaper Decided IsSilentConsensus VD (KB + VD) qD (qB * qD) sD
      (Nat.le_add_left _ _) (mul_le_of_le_one_left zero_le hqB1)) sPT
  have sSR := stage_compose P hn2 GoodPaper hG SRank (fun C => Decided C ∨ PTL C)
    IsSilentConsensus (23 * n ^ 2) (KB + VD) qA' (qB * qD) (hA' n hN hn hn2) sDPT
  have sSRPT := stage_or P hn2 GoodPaper SRank PTL IsSilentConsensus
    (23 * n ^ 2 + (KB + VD)) (qA' * (qB * qD)) sSR
    (stage_mono P hn2 GoodPaper PTL IsSilentConsensus (KB + VD)
      (23 * n ^ 2 + (KB + VD)) (qB * qD) (qA' * (qB * qD)) sPT
      (Nat.le_add_left _ _) (mul_le_of_le_one_left zero_le hqA'1))
  have sAll := stage_compose P hn2 GoodPaper hG (fun _ => True) (fun C => SRank C ∨ PTL C)
    IsSilentConsensus (tOne n + 241 * n ^ 2) (23 * n ^ 2 + (KB + VD))
    qA (qA' * (qB * qD)) (hA n hN hn hn2) sSRPT X hX trivial
  have htime :
      tOne n + 241 * n ^ 2 + (23 * n ^ 2 + (KB + VD)) =
        3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2 := by
    dsimp [KB, VD]
    ring
  rw [htime] at sAll
  simpa only [P, qA, qA', qB, qD, qC, qE] using sAll

/-- The exact window, with all six stage hypotheses discharged by the
existing paper-instance stage theorems. -/
theorem P_EM_paper_window_exact
    (n : ℕ) (hN : 1608 ≤ n) (hn : 0 < n) (hn2 : 2 ≤ n)
    (X : Config (AgentState n) Opinion n) (hX : GoodPaper X) :
    ENNReal.ofReal 0.86 *
      (ENNReal.ofReal 0.915 *
        (ENNReal.ofReal 0.515 *
          (ENNReal.ofReal 0.997 *
            (ENNReal.ofReal 0.515 * ENNReal.ofReal 0.999)))) ≤
      probHitBy (PEM40 n hn) hn2 X IsSilentConsensus
        (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) :=
  pemPaperWindow_exact_of_stages stageA stageA'
    (epoch1_of_stages stageB1 stageB2 stageB34 stageB56) stageC
    (epoch2_of_stages stageB1Z stageB2M stageB34M stageB56M) stageE
    n hN hn hn2 X hX

/-- The same exact flat-protocol bound with its probability written as
the explicit reduced rational. -/
theorem P_EM_paper_window_exact_rational
    (n : ℕ) (hN : 1608 ≤ n) (hn : 0 < n) (hn2 : 2 ≤ n)
    (X : Config (AgentState n) Opinion n) (hX : GoodPaper X) :
    ENNReal.ofReal ((83148542562663 : ℝ) / 400000000000000) ≤
      probHitBy (PEM40 n hn) hn2 X IsSilentConsensus
        (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) := by
  rw [← paper_stage_success_product.1]
  exact P_EM_paper_window_exact n hN hn hn2 X hX

/-- The proof of `window_fin_of_window`, generalized to an arbitrary
interaction horizon. The conclusion covers every finite configuration. -/
theorem window_fin_of_window_at {trank e d n : ℕ} {p₀ : ℝ≥0∞}
    (W : ℕ) (hd : 1 ≤ d) (hn : 0 < n) (hn2 : 2 ≤ n)
    (hW : ∀ X : Config (AgentState n) Opinion n,
      (∀ v, GoodPEM (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n) (X v).1) →
      p₀ ≤ probHitBy (protocolPEMPaper n trank e d hn) hn2 X IsSilentConsensus W)
    (D : Config (PEMFinState n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)) Opinion n) :
    p₀ ≤ probHitBy (protocolPEMPaperFin n trank e d hn) hn2 D
      (fun C => C.isSilent (protocolPEMPaperFin n trank e d hn)) W := by
  set S := pemPaperSimulation (trank := trank) (e := e) hn hn2 hd
  have hX : S.GoodC (S.embC D) := S.goodC_embC D
  rw [← S.encC_embC D, S.probHitBy_encC hn2 _ hX]
  have hw := hW (S.embC D) hX
  have he := probHitBy_eq_and_inv_of_invariant _ hn2 (S.embC D) IsSilentConsensus S.GoodC hX
    (fun C hC i j => S.goodC_step hC i j) W
  have hw' : p₀ ≤ ProbHitWithin (protocolPEMPaper n trank e d hn) hn2 (S.embC D)
      (fun C => IsSilentConsensus C ∧ S.GoodC C) W := by
    rw [he]
    exact hw
  refine hw'.trans (probHitBy_mono_goal _ hn2 _ _ _ (fun C hC => ?_) _)
  exact S.isSilent_encC hC.2 (IsSilentConsensus.isSilent rankDeltaOSSR_satisfies_fix hC.1)

/-- The unrounded success product at the unrounded horizon, transferred
to silence of the finite protocol from every finite configuration. -/
theorem P_EM_paper_window_exact_fin
    (n : ℕ) (hN : 1608 ≤ n) (hn : 0 < n) (hn2 : 2 ≤ n)
    (D : Config (PEMFinState n (7 * (40 + 4)) (208 * n) (rmaxPaper n) (32 * n)) Opinion n) :
    ENNReal.ofReal 0.86 *
      (ENNReal.ofReal 0.915 *
        (ENNReal.ofReal 0.515 *
          (ENNReal.ofReal 0.997 *
            (ENNReal.ofReal 0.515 * ENNReal.ofReal 0.999)))) ≤
      probHitBy (protocolPEMPaperFin n 40 208 32 hn) hn2 D
        (fun C => C.isSilent (protocolPEMPaperFin n 40 208 32 hn))
        (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) :=
  window_fin_of_window_at (trank := 40) (e := 208) (d := 32) (n := n)
    (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2)
    (by norm_num : 1 ≤ 32) hn hn2
    (fun X hX => P_EM_paper_window_exact n hN hn hn2 X hX) D

/-- The finite-protocol exact window with its reduced rational probability. -/
theorem P_EM_paper_window_exact_fin_rational
    (n : ℕ) (hN : 1608 ≤ n) (hn : 0 < n) (hn2 : 2 ≤ n)
    (D : Config (PEMFinState n (7 * (40 + 4)) (208 * n) (rmaxPaper n) (32 * n)) Opinion n) :
    ENNReal.ofReal ((83148542562663 : ℝ) / 400000000000000) ≤
      probHitBy (protocolPEMPaperFin n 40 208 32 hn) hn2 D
        (fun C => C.isSilent (protocolPEMPaperFin n 40 208 32 hn))
        (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) := by
  rw [← paper_stage_success_product.1]
  exact P_EM_paper_window_exact_fin n hN hn hn2 D

/-- A uniform one-fifth restart window, retaining the exact horizon. -/
theorem P_EM_paper_window_exact_fin_one_fifth
    (n : ℕ) (hN : 1608 ≤ n) (hn : 0 < n) (hn2 : 2 ≤ n)
    (D : Config (PEMFinState n (7 * (40 + 4)) (208 * n) (rmaxPaper n) (32 * n)) Opinion n) :
    (5 : ℝ≥0∞)⁻¹ ≤ probHitBy (protocolPEMPaperFin n 40 208 32 hn) hn2 D
      (fun C => C.isSilent (protocolPEMPaperFin n 40 208 32 hn))
      (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) :=
  paper_stage_success_product.2.le.trans
    (P_EM_paper_window_exact_fin_rational n hN hn hn2 D)

/-- The unrounded six-stage window is strictly positive. -/
theorem paperExactWindow_pos {n : ℕ} (hn : 0 < n) :
    0 < 3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2 := by
  positivity

/-- The doubled unrounded window, using the sharper `two_tOne_le` estimate. -/
theorem two_paperExactWindow_le {n : ℕ} (hN : 1608 ≤ n) :
    2 * (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) ≤
      2085 * n ^ 2 := by
  have ht := two_tOne_le hN
  have hnn : 8 * n * (n - 1) ≤ 8 * n ^ 2 := by
    calc
      8 * n * (n - 1) ≤ 8 * n * n :=
        Nat.mul_le_mul_left (8 * n) (Nat.sub_le n 1)
      _ = 8 * n ^ 2 := by ring
  nlinarith

/-- Four exact windows fit within the paper's improved high-probability constant. -/
theorem four_paperExactWindow_le {n : ℕ} (hN : 1608 ≤ n) :
    4 * (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) ≤
      4170 * n ^ 2 := by
  have h := two_paperExactWindow_le hN
  nlinarith

/-- Five exact windows fit within the improved expected-time numerator. -/
theorem five_paperExactWindow_le {n : ℕ} (hN : 1608 ≤ n) :
    5 * (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2) ≤
      5213 * n ^ 2 := by
  have h := two_paperExactWindow_le hN
  nlinarith

/-- Kanaya et al. Theorem 4 with the sharper constants obtained from the
unrounded six-stage window, from every finite starting configuration. -/
theorem P_EM_paper_thm4_time_exact :
    KanayaThm4TimeExpected 40 208 32 1608 5213 ∧
      KanayaThm4TimeWhp 40 208 32 1608 4170 := by
  refine ⟨?_, ?_⟩
  · intro n hN hn hn2 C₀
    let K : ℕ := 3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2
    have hK : 0 < K := paperExactWindow_pos hn
    haveI : NeZero K := ⟨ne_of_gt hK⟩
    have h := expectedParallelTime_le_window_mul_inv_of_invariant
      (protocolPEMPaperFin n 40 208 32 hn) hn2 C₀
      (fun C => C.isSilent (protocolPEMPaperFin n 40 208 32 hn))
      (fun _ => True) K 5⁻¹ (by simp) trivial (fun _ _ _ _ => trivial)
      (fun D _ _ => P_EM_paper_window_exact_fin_one_fifth n hN hn hn2 D)
    refine h.trans ?_
    rw [inv_inv]
    apply ENNReal.div_le_of_le_mul
    have h5 : 5 * K ≤ 5213 * n ^ 2 := five_paperExactWindow_le hN
    calc
      (K : ℝ≥0∞) * 5 = ((5 * K : ℕ) : ℝ≥0∞) := by
        push_cast
        ring
      _ ≤ ((5213 * n ^ 2 : ℕ) : ℝ≥0∞) := by exact_mod_cast h5
      _ = 5213 * n * n := by
        push_cast
        ring
  · intro n hN hn hn2 C₀
    let P := protocolPEMPaperFin n 40 208 32 hn
    let c := Nat.clog 2 n
    let K : ℕ := 3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2
    have hr := probNotHitBy_mul_window_le_initial_mul_pow P hn2 C₀
      (fun C => C.isSilent P) K 5⁻¹
      (fun D _ => P_EM_paper_window_exact_fin_one_fifth n hN hn hn2 D) (4 * c)
    have h4 : 4 * K ≤ 4170 * n ^ 2 := four_paperExactWindow_le hN
    have ht : 4 * c * K ≤ 4170 * n ^ 2 * c := by
      calc
        4 * c * K = (4 * K) * c := by ring
        _ ≤ (4170 * n ^ 2) * c := Nat.mul_le_mul_right c h4
    refine (probNotHitBy_le_of_le P hn2 C₀ (fun C => C.isSilent P) ht).trans
      (hr.trans ?_)
    have h0 : probNotHitBy P hn2 C₀ (fun C => C.isSilent P) 0 ≤ 1 := by
      rw [← probHitBy_add_probNotHitBy P hn2 C₀ _ 0]
      exact le_add_self
    calc
      probNotHitBy P hn2 C₀ (fun C => C.isSilent P) 0 * (1 - 5⁻¹) ^ (4 * c)
          ≤ 1 * ((1 - 5⁻¹) ^ 4) ^ c := by
            rw [pow_mul]
            exact mul_le_mul_right' h0 _
      _ ≤ 1 * (2⁻¹) ^ c := by
        gcongr
        exact one_sub_inv_five_pow_four_le
      _ = ((2 : ℝ≥0∞) ^ c)⁻¹ := by
        rw [one_mul, ENNReal.inv_pow]
      _ ≤ (n : ℝ≥0∞)⁻¹ := by
        apply ENNReal.inv_le_inv.mpr
        have := Nat.le_pow_clog (by norm_num : 1 < 2) n
        exact_mod_cast this

/-- The complete row-32 statement: the exact flat-protocol window and
the improved expected-time and high-probability constants. -/
theorem P_EM_paper_thm4_exact :
    (∀ (n : ℕ), 1608 ≤ n → ∀ (hn : 0 < n) (hn2 : 2 ≤ n)
      (X : Config (AgentState n) Opinion n), GoodPaper X →
      ENNReal.ofReal 0.86 *
        (ENNReal.ofReal 0.915 *
          (ENNReal.ofReal 0.515 *
            (ENNReal.ofReal 0.997 *
              (ENNReal.ofReal 0.515 * ENNReal.ofReal 0.999)))) ≤
        probHitBy (PEM40 n hn) hn2 X IsSilentConsensus
          (3 * tOne n + 8 * n * (n - 1) + 1033 * n ^ 2)) ∧
      KanayaThm4TimeExpected 40 208 32 1608 5213 ∧
      KanayaThm4TimeWhp 40 208 32 1608 4170 :=
  ⟨P_EM_paper_window_exact, P_EM_paper_thm4_time_exact⟩

end Ripple.PopulationProtocol.SSEM
