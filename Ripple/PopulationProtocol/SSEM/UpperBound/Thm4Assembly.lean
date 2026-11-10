/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kanaya Theorem 4 (time part) from a uniform window

`PEMPaperWindow trank e d N₀ Kc p₀` states P3's Theorem W for the flat paper instance: from every
configuration whose agents satisfy `GoodPEM`, the final set `S_em` (`IsSilentConsensus`) is hit
within `Kc · n²` interactions with probability at least `p₀`.

`kanayaThm4Time_of_window`: the window with `Kc = 1043`, `p₀ = 1/5` gives `KanayaThm4Time` for the
finite paper instance with `c₁ = 5215` (expected parallel time) and `c₂ = 4172` (w.h.p.). The
transfer goes through `pemPaperSimulation` (every finite configuration is `encC` of a good one) and
the restart lemmas of `ExpectedTime.lean` (P3 Corollary 23).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.SimulationTransfer

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped ENNReal

variable {n : ℕ}

/-- **Uniform window for the flat paper instance** (P3 Theorem W). -/
def PEMPaperWindow (trank e d N₀ Kc : ℕ) (p₀ : ℝ≥0∞) : Prop :=
  ∀ n, N₀ ≤ n → ∀ (hn : 0 < n) (hn2 : 2 ≤ n) (X : Config (AgentState n) Opinion n),
    (∀ v, GoodPEM (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n) (X v).1) →
    p₀ ≤ probHitBy (protocolPEMPaper n trank e d hn) hn2 X IsSilentConsensus (Kc * n ^ 2)

namespace StateSimulation

variable {Q Q' : Type*} {P : Protocol Q Opinion Output}
  {P' : Protocol Q' Opinion Output} (S : StateSimulation P P')

include S

theorem probHitBy_encC (hn : 2 ≤ n) (G' : Config Q' Opinion n → Prop)
    {C : Config Q Opinion n} (hC : S.GoodC C) (t : ℕ) :
    probHitBy P' hn (S.encC C) G' t = probHitBy P hn C (fun D => G' (S.encC D)) t := by
  have h1 := probHitBy_add_probNotHitBy P' hn (S.encC C) G' t
  have h2 := probHitBy_add_probNotHitBy P hn C (fun D => G' (S.encC D)) t
  rw [S.probNotHitBy_encC hn G' hC t] at h1
  have hne : probNotHitBy P hn C (fun D => G' (S.encC D)) t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← h2]; exact le_add_self)
  exact (ENNReal.add_left_inj hne).mp (h1.trans h2.symm)

end StateSimulation

/-- The window, transferred to every configuration of the finite paper instance. -/
theorem window_fin_of_window {trank e d N₀ Kc : ℕ} {p₀ : ℝ≥0∞}
    (hW : PEMPaperWindow trank e d N₀ Kc p₀) (hd : 1 ≤ d) {n : ℕ} (hN : N₀ ≤ n) (hn : 0 < n)
    (hn2 : 2 ≤ n)
    (D : Config (PEMFinState n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)) Opinion n) :
    p₀ ≤ probHitBy (protocolPEMPaperFin n trank e d hn) hn2 D
      (fun C => C.isSilent (protocolPEMPaperFin n trank e d hn)) (Kc * n ^ 2) := by
  set S := pemPaperSimulation (trank := trank) (e := e) hn hn2 hd
  have hX : S.GoodC (S.embC D) := S.goodC_embC D
  rw [← S.encC_embC D, S.probHitBy_encC hn2 _ hX]
  have hw := hW n hN hn hn2 (S.embC D) hX
  have he := probHitBy_eq_and_inv_of_invariant _ hn2 (S.embC D) IsSilentConsensus S.GoodC hX
    (fun C hC i j => S.goodC_step hC i j) (Kc * n ^ 2)
  have hw' : p₀ ≤ ProbHitWithin (protocolPEMPaper n trank e d hn) hn2 (S.embC D)
      (fun C => IsSilentConsensus C ∧ S.GoodC C) (Kc * n ^ 2) := by
    rw [he]; exact hw
  refine hw'.trans (probHitBy_mono_goal _ hn2 _ _ _ (fun C hC => ?_) _)
  exact S.isSilent_encC hC.2 (IsSilentConsensus.isSilent rankDeltaOSSR_satisfies_fix hC.1)

theorem one_sub_inv_five_pow_four_le : ((1 : ℝ≥0∞) - 5⁻¹) ^ 4 ≤ 2⁻¹ := by
  have h5 : (5 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 5) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
  have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
  rw [h5, h2, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_pow (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **Kanaya Theorem 4, time part, from the uniform window** (P3 Corollary 23): `trank = 40`,
`e = 208`, `d = 32`, `N₀ = 1608`, expected parallel time `≤ 5215 n`, and silence within
`4172 n² ⌈log₂ n⌉` interactions except with probability `≤ 1/n`. -/
theorem kanayaThm4Time_explicit_of_window (hW : PEMPaperWindow 40 208 32 1608 1043 5⁻¹) :
    KanayaThm4TimeExpected 40 208 32 1608 5215 ∧ KanayaThm4TimeWhp 40 208 32 1608 4172 := by
  refine ⟨?_, ?_⟩
  · intro n hN hn hn2 C₀
    haveI : NeZero (1043 * n ^ 2) := ⟨by positivity⟩
    have h := expectedParallelTime_le_window_mul_inv_of_invariant
      (protocolPEMPaperFin n 40 208 32 hn) hn2 C₀
      (fun C => C.isSilent (protocolPEMPaperFin n 40 208 32 hn)) (fun _ => True)
      (1043 * n ^ 2) 5⁻¹ (by simp) trivial (fun _ _ _ _ => trivial)
      (fun D _ _ => window_fin_of_window hW (by norm_num) hN hn hn2 D)
    refine h.trans ?_
    rw [inv_inv]
    apply ENNReal.div_le_of_le_mul
    have : ((1043 * n ^ 2 : ℕ) : ℝ≥0∞) * 5 = 5215 * n * n := by
      push_cast; ring
    rw [this]
  · intro n hN hn hn2 C₀
    set P := protocolPEMPaperFin n 40 208 32 hn
    set c := Nat.clog 2 n
    have hr := probNotHitBy_mul_window_le_initial_mul_pow P hn2 C₀ (fun C => C.isSilent P)
      (1043 * n ^ 2) 5⁻¹ (fun D _ => window_fin_of_window hW (by norm_num) hN hn hn2 D) (4 * c)
    have ht : 4172 * n ^ 2 * c = 4 * c * (1043 * n ^ 2) := by ring
    rw [ht]
    refine hr.trans ?_
    have h0 : probNotHitBy P hn2 C₀ (fun C => C.isSilent P) 0 ≤ 1 := by
      rw [← probHitBy_add_probNotHitBy P hn2 C₀ _ 0]; exact le_add_self
    calc probNotHitBy P hn2 C₀ (fun C => C.isSilent P) 0 * (1 - 5⁻¹) ^ (4 * c)
        ≤ 1 * ((1 - 5⁻¹) ^ 4) ^ c := by
          rw [pow_mul]; exact mul_le_mul_right' h0 _
      _ ≤ 1 * (2⁻¹) ^ c := by
          gcongr; exact one_sub_inv_five_pow_four_le
      _ = ((2 : ℝ≥0∞) ^ c)⁻¹ := by rw [one_mul, ENNReal.inv_pow]
      _ ≤ (n : ℝ≥0∞)⁻¹ := by
          apply ENNReal.inv_le_inv.mpr
          have := Nat.le_pow_clog (by norm_num : 1 < 2) n
          exact_mod_cast this

theorem kanayaThm4Time_of_window (hW : PEMPaperWindow 40 208 32 1608 1043 5⁻¹) :
    KanayaThm4Time :=
  ⟨40, 208, 32, 1608, 5215, 4172, by norm_num, by simp, kanayaThm4Time_explicit_of_window hW⟩

end Ripple.PopulationProtocol.SSEM
