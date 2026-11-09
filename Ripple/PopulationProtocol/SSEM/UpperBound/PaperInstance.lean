/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# P_EM with the paper's parameters, and the target statements of Kanaya Theorem 4 (time)

Kanaya et al. (arXiv:2503.17652v1, §5.2) run P_EM with Optimal-Silent-SSR of Burman et al.
(arXiv:1907.06068v5, §3–4) at `Rmax = 60 ln n`, `Emax, Dmax = Θ(n)` and a constant `trank`
with `s_rank ≤ trank · n` (timer range `7 (trank + 4)`). The instance proved silent SSEM in
`SilentPEM.lean` uses `trank = Rmax = n`; with `trank = n` the median countdown alone takes
`Θ(n²)` parallel time ([K] Lemma 11), so the time part of Theorem 4 cannot hold for it by the
paper's argument.

This file defines the paper-parameter instance `protocolPEMPaper` and its finite role-indexed
version `protocolPEMPaperFin`, proves that both are silent SSEM for `n ≥ 4`
(`P_EM_paper_fin_solves_silent_SSEM`, from the `Rmax ≥ 2⌈log₂ n⌉ + 2` convergence proof
`burmanConvergence_concrete_log`) with an `O(n)` state bound (`card_PEMPaperFin_le`), and
states the time part of Theorem 4 as propositions (`KanayaThm4Time`). The time statements are
**not proved**: the paper phase is `docs/audit/FIX2-BURMAN.md`; no theorem here assumes them.

The time targets quantify over configurations of the *finite* protocol: on the flat
`AgentState n` (unbounded counters) they are false (a median timer `M` costs `M (n-1)/2`
parallel time), so the paper's state space is the finite one.
-/

import Ripple.PopulationProtocol.SSEM.Convergence.FiniteStatePEM
import Ripple.PopulationProtocol.SSEM.Convergence.BurmanConvergenceLog
import Ripple.PopulationProtocol.SSEM.Probability.ExpectedTime
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Ripple.PopulationProtocol.SSEM

variable {n : ℕ}

/-- `Rmax = ⌈60 ln n⌉` (Burman et al. §3). -/
noncomputable def rmaxPaper (n : ℕ) : ℕ := ⌈60 * Real.log n⌉₊

theorem one_le_rmaxPaper {n : ℕ} (hn : 2 ≤ n) : 1 ≤ rmaxPaper n := by
  unfold rmaxPaper
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h
    rw [Nat.ceil_eq_zero] at h
    linarith)

/-- `2⌈log₂ n⌉ + 2 ≤ ⌈60 ln n⌉` for `n ≥ 2`. -/
theorem two_clog_add_two_le_rmaxPaper {n : ℕ} (hn : 2 ≤ n) :
    2 * Nat.clog 2 n + 2 ≤ rmaxPaper n := by
  have h1 : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hk : Nat.clog 2 n ≤ (Nat.clog 2 n - 1) + 1 := by omega
  set m : ℕ := Nat.clog 2 n - 1 with hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2 : (m : ℝ) * Real.log 2 < Real.log n := by
    have h1' : ((2 : ℝ) ^ m) < n := by exact_mod_cast h1
    have := Real.log_lt_log (by positivity) h1'
    rwa [Real.log_pow] at this
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hln : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have h3 : (m : ℝ) * 0.69 ≤ (m : ℝ) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_left (le_of_lt hl2) hm0
  have h4 : ((2 * Nat.clog 2 n + 2 : ℕ) : ℝ) ≤ 60 * Real.log n := by
    have hk' : ((Nat.clog 2 n : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hk
    push_cast
    nlinarith
  have h5 := h4.trans (Nat.le_ceil (60 * Real.log n))
  unfold rmaxPaper
  exact_mod_cast h5

/-- **P_EM with the paper's parameters**: timer constant `trank`, `Rmax = ⌈60 ln n⌉`,
`Emax = e·n`, `Dmax = d·n`. -/
noncomputable def protocolPEMPaper (n trank e d : ℕ) (hn : 0 < n) :
    Protocol (AgentState n) Opinion Output :=
  protocolPEM n trank (rmaxPaper n) (rankDeltaOSSR (rmaxPaper n) (e * n) (d * n) hn)

/-- The finite role-indexed version of `protocolPEMPaper`. -/
noncomputable def protocolPEMPaperFin (n trank e d : ℕ) (hn : 0 < n) :
    Protocol (PEMFinState n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)) Opinion Output :=
  protocolPEMFin n trank (rmaxPaper n) (e * n) (d * n) hn

/-- `protocolPEMPaperFin` simulates `protocolPEMPaper` (for `n ≥ 2`, `d ≥ 1`). -/
noncomputable def pemPaperSimulation {n trank e d : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) (hd : 1 ≤ d) :
    StateSimulation (protocolPEMPaper n trank e d hn) (protocolPEMPaperFin n trank e d hn) :=
  pemSimulation (trank := trank) hn (one_le_rmaxPaper hn2) (by nlinarith)

/-- **State count of the paper instance**: `24 n + 24 (7 (trank + 4) + 1) + 8 (e n + 1)
+ 8 ⌈60 ln n⌉ + 8 (d n + 1)` states, `O(n)` for constant `trank, e, d`. -/
theorem card_PEMPaperFin_le (n trank e d : ℕ) :
    Fintype.card (PEMFinState n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)) ≤
      24 * n + 24 * (7 * (trank + 4) + 1) + 8 * (e * n + 1) + 8 * rmaxPaper n +
        8 * (d * n + 1) :=
  card_PEMFinState_le n _ _ _ _

/-- **The paper instance is silent SSEM** (`n ≥ 4`, `d ≥ 1`), from the log-`Rmax`
convergence proof. -/
theorem P_EM_paper_solves_silent_SSEM [Inhabited (Fin n × Fin n)] {trank e d : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hd : 1 ≤ d) :
    SolvesSilentSSEM (protocolPEMPaper n trank e d hn) n := by
  have hD : 1 < d * n := by nlinarith
  have hR := two_clog_add_two_le_rmaxPaper (n := n) (by omega)
  exact ⟨P_EM_solves_SSEM_log (τ := trank) (Emax := e * n) hn4 hD hR,
    P_EM_silent_of_consensus_reachable rankDeltaOSSR_satisfies_fix (by omega)
      (P_EM_consensus_reachable_of_BurmanConvergence rankDeltaOSSR_satisfies_fix hn4
        (burmanConvergence_concrete_log (τ := trank) (Emax := e * n) hn4 hD hR))⟩

/-- **The finite paper instance is silent SSEM**, with `card_PEMPaperFin_le` states. -/
theorem P_EM_paper_fin_solves_silent_SSEM [Inhabited (Fin n × Fin n)] {trank e d : ℕ}
    {hn : 0 < n} (hn4 : 4 ≤ n) (hd : 1 ≤ d) :
    SolvesSilentSSEM (protocolPEMPaperFin n trank e d hn) n :=
  (pemPaperSimulation hn (by omega) hd).solvesSilentSSEM (P_EM_paper_solves_silent_SSEM hn4 hd)

/-- Non-vacuity at `n = 4`, `trank = e = d = 1`. -/
example : SolvesSilentSSEM (protocolPEMPaperFin 4 1 1 1 (by norm_num)) 4 :=
  P_EM_paper_fin_solves_silent_SSEM le_rfl le_rfl

open Probability in
/-- **Kanaya Theorem 4, expected silence time (target).** From every configuration of the
finite paper instance the expected parallel time to a silent configuration is at most
`c₁ n`. -/
def KanayaThm4TimeExpected (trank e d N₀ : ℕ) (c₁ : ENNReal) : Prop :=
  ∀ n, N₀ ≤ n → ∀ (hn : 0 < n) (hn2 : 2 ≤ n)
    (C₀ : Config (PEMFinState n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)) Opinion n),
    expectedParallelTimeToSilent (protocolPEMPaperFin n trank e d hn) hn2 C₀ ≤ c₁ * n

open Probability in
/-- **Kanaya Theorem 4, w.h.p. silence time (target).** From every configuration a silent
configuration is reached within `c₂ · n · ⌈log₂ n⌉` parallel time (`c₂ · n² · ⌈log₂ n⌉`
interactions) except with probability at most `1/n`. -/
def KanayaThm4TimeWhp (trank e d N₀ c₂ : ℕ) : Prop :=
  ∀ n, N₀ ≤ n → ∀ (hn : 0 < n) (hn2 : 2 ≤ n)
    (C₀ : Config (PEMFinState n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)) Opinion n),
    probNotHitBy (protocolPEMPaperFin n trank e d hn) hn2 C₀
        (fun C => C.isSilent (protocolPEMPaperFin n trank e d hn)) (c₂ * n ^ 2 * Nat.clog 2 n) ≤
      (n : ENNReal)⁻¹

/-- **Kanaya Theorem 4, time part (target)**: for some constants `trank, e, d` (with `d ≥ 1`)
the paper instance has `O(n)` expected and `O(n log n)` w.h.p. silence time. Open. -/
def KanayaThm4Time : Prop :=
  ∃ trank e d N₀ : ℕ, ∃ c₁ : ENNReal, ∃ c₂ : ℕ, 1 ≤ d ∧ c₁ ≠ ⊤ ∧
    KanayaThm4TimeExpected trank e d N₀ c₁ ∧ KanayaThm4TimeWhp trank e d N₀ c₂

end Ripple.PopulationProtocol.SSEM
