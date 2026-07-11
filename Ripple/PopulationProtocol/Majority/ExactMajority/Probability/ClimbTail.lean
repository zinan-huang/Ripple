/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ClimbTail — the gated leading-edge climb tail (Doty §6 brick 3.2, the `ClimbBound` engine)

`ClockFrontProfile.ClimbBound θ W₂ c` (`frac k < θ → rBeyond (k+W₂) = 0`) is the sub-floor half of
Doty Theorem 6.5's first claim: while the bulk has not arrived at level `k`, the leading edge cannot
climb `W₂` levels above `k`.  The paper's mechanism (proof of Thm 6.5, lines 1912–1930): while the
tail count above `k+1` stays at most `B'` (`= n^{0.2}` at paper scales, supplied by the early-drip
analysis), every NEW level seeding — the only move that raises the leading edge — is a same-minute
drip at the current edge, firing with probability `≤ (B'/n)²` (`= n^{-1.6}`); accumulating
`W₂ = Θ(log log n)` of them inside the window has probability `n^{-ω(1)}`.

## The design (this file)

* `climbN k c` — the climb height: the number of nonempty cumulative levels strictly above `k+1`
  (`#{j ∈ [k+2, capMinute] | rBeyond j c > 0}`).  Because `rBeyond` is antitone in its threshold,
  this set is an initial segment `[k+2, k+1+climbN]` — no "holes", so `climbN` is exactly
  `(leading edge) − (k+1)` truncated, WITHOUT needing a max-minute function.
* `climbN` rises by at most `1` per step (`climbN_le_succ_on_support`) — only a drip at the current
  edge crosses a new threshold (sync only copies an existing minute; the per-pair upper bound
  `transition_p3_minute_le_succ_max` caps the produced minutes at `max(inputs)+1`).
* The rise event is included in the fresh seeding of the frontier level
  (`{climbN rises} ⊆ {1 ≤ rBeyond (frontier+1)}`), whose probability is
  `≤ (frontMinuteCount frontier / n)² ≤ (rBeyond (k+1) / n)² ≤ (B'/n)²` on the gate
  (`ClockFrontShape.real_front_advance_squares` — the proven one-step squaring).
* `mgf_one_step` — the GENERIC one-step MGF contraction for a rare `+1`-increment count over ANY
  probability measure (the kernel-generic form of `EarlyDrip.earlyDrip_mgf_one_step`).
* `climbPot` — the TRUNCATED exponential potential: `exp(s·climbN)` while the bulk has not arrived
  at `k` (`rBeyond k < θn`), and `0` after.  Because `rBeyond k` is monotone along steps, the
  truncated potential's drift holds on the UNION gate
  `G = {card = n ∧ AllClockP3} ∩ ({rBeyond (k+1) ≤ B'} ∪ {θn ≤ rBeyond k})`:
  on the bulk-arrived part the potential is `0` and stays `0` (monotonicity), and on the pre-bulk
  part the MGF factor applies.  Killing happens exactly on the DANGEROUS event
  `{rBeyond (k+1) > B' ∧ rBeyond k < θn}` (the early-drip blowup before bulk arrival — the escape
  mass to be bounded by the brick-3.4 tainted-set analysis) or on leaving the `AllClockP3` hour
  window (benign: the hour completed).
* `climb_real_tail` — the capstone, via the brick-2 engine `GatedDrift.gated_real_tail`:

  `(K^t) c₀ {rBeyond k < θn ∧ 0 < rBeyond (k+W₂)} ≤ escape + r^t · climbPot c₀ / e^{s(W₂−1)}`,

  `r = 1 + (B'/n)²(e^s−1)`.  At paper scales (`B'/n = n^{-0.8}`, `t = O(n log n)`,
  `s = Θ(log n)`, `W₂ = Θ(log log n)`) the second term is `n^{-ω(1)}` — the very-high-probability
  climb bound, CONDITIONAL only on the escape mass.

Everything here is 0-sorry, axiom-clean, on the REAL `NonuniformMajority` kernel.

Reference: Doty et al. (arXiv:2106.10201v2), proof of Theorem 6.5 (the "first claim"), lines
1912–1930; `DOTY_LEMMA63_DOCTRINE.md` brick 3.2.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontShape
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedGeometricDrift
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClimbTail

open ClockRealKernel ClockFrontShape HabsDischarge

variable {L K : ℕ}

/-! ## Part 0 — the generic one-step MGF contraction (kernel-generic `earlyDrip_mgf_one_step`).

The clockProto-specific `EarlyDrip.earlyDrip_mgf_one_step` is re-proven here over an arbitrary
probability measure with the step hypotheses supplied almost everywhere — so it applies to the real
`NonuniformMajority` kernel (and later to the marked kernel of brick 3.3). -/

/-- **The generic one-step MGF contraction of a rare `+1`-increment count.**  Over any probability
measure `μ`: if a.e. `N ≤ n₀ + 1`, and the increase event `{n₀ < N}` has measure at most `q ≥ 0`,
then for `s ≥ 0`:  `∫ exp(s·N) dμ ≤ (1 + q(e^s − 1)) · exp(s·n₀)`. -/
theorem mgf_one_step {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : ℝ) (hs : 0 ≤ s)
    (N : α → ℕ) (n₀ : ℕ)
    (hstep : ∀ᵐ y ∂μ, N y ≤ n₀ + 1)
    (q : ℝ) (hq0 : 0 ≤ q)
    (hprob : μ {y | n₀ < N y} ≤ ENNReal.ofReal q) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (s * (N y : ℝ))) ∂μ ≤
      ENNReal.ofReal ((1 + q * (Real.exp s - 1)) * Real.exp (s * (n₀ : ℝ))) := by
  classical
  set D : Set α := {y | n₀ < N y} with hD
  have hD_meas : MeasurableSet D := DiscreteMeasurableSpace.forall_measurableSet _
  -- Pointwise a.e. bound: split on whether y ∈ D.
  have hpt : ∀ᵐ y ∂μ,
      ENNReal.ofReal (Real.exp (s * (N y : ℝ))) ≤
        (if y ∈ D then ENNReal.ofReal (Real.exp s * Real.exp (s * (n₀ : ℝ)))
          else ENNReal.ofReal (Real.exp (s * (n₀ : ℝ)))) := by
    filter_upwards [hstep] with y hy
    by_cases hdrip : y ∈ D
    · simp only [hdrip, if_true]
      have hlt : n₀ < N y := hdrip
      have heq : N y = n₀ + 1 := by omega
      apply ENNReal.ofReal_le_ofReal
      rw [heq]
      have : s * ((n₀ + 1 : ℕ) : ℝ) = s + s * (n₀ : ℝ) := by push_cast; ring
      rw [this, Real.exp_add]
    · simp only [hdrip, if_false]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hle : N y ≤ n₀ := by
        by_contra h; exact hdrip (not_le.mp h)
      have hcast : ((N y : ℕ) : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hle
      nlinarith [hs, hcast]
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (s * (N y : ℝ))) ∂μ
      ≤ ∫⁻ y, (if y ∈ D then ENNReal.ofReal (Real.exp s * Real.exp (s * (n₀ : ℝ)))
          else ENNReal.ofReal (Real.exp (s * (n₀ : ℝ)))) ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp s * Real.exp (s * (n₀ : ℝ))) * μ D
        + ENNReal.ofReal (Real.exp (s * (n₀ : ℝ))) * μ Dᶜ := by
        rw [← lintegral_add_compl _ hD_meas]
        congr 1
        · rw [setLIntegral_congr_fun hD_meas
              (g := fun _ => ENNReal.ofReal (Real.exp s * Real.exp (s * (n₀ : ℝ))))
              (fun y hy => by simp only [hy, if_true])]
          rw [lintegral_const, Measure.restrict_apply_univ]
        · rw [setLIntegral_congr_fun hD_meas.compl
              (g := fun _ => ENNReal.ofReal (Real.exp (s * (n₀ : ℝ))))
              (fun y hy => by simp only [Set.mem_compl_iff] at hy; simp only [hy, if_false])]
          rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal ((1 + q * (Real.exp s - 1)) * Real.exp (s * (n₀ : ℝ))) := by
        have hexp_ge : (1 : ℝ) ≤ Real.exp s := Real.one_le_exp hs
        have hΦnn : (0 : ℝ) ≤ Real.exp (s * (n₀ : ℝ)) := (Real.exp_pos _).le
        have hμD_le_one : μ D ≤ 1 := by
          calc μ D ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hμD_ne_top : μ D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμD_le_one
        set qr := (μ D).toReal with hqr
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_q : qr ≤ q := by
          rw [hqr]
          calc (μ D).toReal ≤ (ENNReal.ofReal q).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
            _ = q := ENNReal.toReal_ofReal hq0
        have hμD_eq : μ D = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hμD_ne_top).symm
        have hμDc_eq : μ Dᶜ = ENNReal.ofReal (1 - qr) := by
          have hcompl := measure_compl hD_meas hμD_ne_top
          rw [show μ Set.univ = 1 from measure_univ] at hcompl
          rw [hcompl, hμD_eq,
            show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
            ← ENNReal.ofReal_sub 1 hqr_nonneg]
        have hqr_le_one : qr ≤ 1 := by
          rw [hqr, show (1:ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
          exact ENNReal.toReal_mono ENNReal.one_ne_top hμD_le_one
        rw [hμD_eq, hμDc_eq,
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.exp s * Real.exp (s * (n₀ : ℝ))),
          ← ENNReal.ofReal_mul hΦnn,
          ← ENNReal.ofReal_add
            (mul_nonneg (by positivity) hqr_nonneg)
            (mul_nonneg hΦnn (by linarith : (0:ℝ) ≤ 1 - qr))]
        apply ENNReal.ofReal_le_ofReal
        have hfac : Real.exp s * Real.exp (s * (n₀ : ℝ)) * qr
              + Real.exp (s * (n₀ : ℝ)) * (1 - qr)
            = Real.exp (s * (n₀ : ℝ)) * (1 + (Real.exp s - 1) * qr) := by ring
        rw [hfac]
        have hbound : 1 + (Real.exp s - 1) * qr ≤ 1 + q * (Real.exp s - 1) := by
          have : (Real.exp s - 1) * qr ≤ (Real.exp s - 1) * q :=
            mul_le_mul_of_nonneg_left hqr_le_q (by linarith)
          nlinarith [this]
        calc Real.exp (s * (n₀ : ℝ)) * (1 + (Real.exp s - 1) * qr)
            ≤ Real.exp (s * (n₀ : ℝ)) * (1 + q * (Real.exp s - 1)) :=
              mul_le_mul_of_nonneg_left hbound hΦnn
          _ = (1 + q * (Real.exp s - 1)) * Real.exp (s * (n₀ : ℝ)) := by ring

/-! ## Part 1 — the climb height `climbN` and its combinatorics. -/

/-- The climb height above level `k`: the number of nonempty cumulative levels strictly above
`k+1`.  By the threshold-antitonicity of `rBeyond` this is exactly `(leading edge) − (k+1)`
truncated at `0` — the filtered set is the initial segment `[k+2, k+1+climbN]`. -/
def climbN (k : ℕ) (c : Config (AgentState L K)) : ℕ :=
  ((Finset.Icc (k + 2) (capMinute (L := L) (K := K))).filter
    (fun j => 0 < rBeyond (L := L) (K := K) j c)).card

/-- No clock minute exceeds `capMinute` (the `minute` field is `Fin (capMinute + 1)`), so
`rBeyond j c = 0` above the cap. -/
theorem rBeyond_eq_zero_of_cap_lt (j : ℕ) (hj : capMinute (L := L) (K := K) < j)
    (c : Config (AgentState L K)) :
    rBeyond (L := L) (K := K) j c = 0 := by
  unfold rBeyond
  rw [Multiset.countP_eq_zero]
  rintro a _ ⟨_, hmin⟩
  have hle : a.minute.val ≤ K * (L + 1) := Nat.lt_succ_iff.mp a.minute.isLt
  have hcap : capMinute (L := L) (K := K) = K * (L + 1) := rfl
  omega

/-- **The initial-segment fact**: every level in `[k+2, k+1+climbN]` is nonempty.  (If some `j` in
the segment were empty, antitonicity would empty everything above `j`, capping the filtered card
strictly below `climbN`.) -/
theorem rBeyond_pos_of_le_frontier (k j : ℕ) (c : Config (AgentState L K))
    (hjlo : k + 2 ≤ j) (hjhi : j ≤ k + 1 + climbN (L := L) (K := K) k c) :
    0 < rBeyond (L := L) (K := K) j c := by
  by_contra h0
  have hj0 : rBeyond (L := L) (K := K) j c = 0 := by omega
  set m := climbN (L := L) (K := K) k c with hm
  have hmpos : 1 ≤ m := by omega
  -- every filtered element is < j (antitonicity kills ≥ j)
  have hsub : ((Finset.Icc (k + 2) (capMinute (L := L) (K := K))).filter
      (fun j' => 0 < rBeyond (L := L) (K := K) j' c)) ⊆ Finset.Icc (k + 2) (j - 1) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hxlo, _⟩, hxpos⟩ := hx
    rw [Finset.mem_Icc]
    refine ⟨hxlo, ?_⟩
    by_contra hxj
    have hjx : j ≤ x := by omega
    have := rBeyond_antitone_threshold (L := L) (K := K) j x hjx c
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  -- card ≤ (j−1) + 1 − (k+2) = j − k − 2 ≤ m − 1 < m = card: contradiction
  have : m ≤ j - 1 + 1 - (k + 2) := by rw [hm]; exact hcard
  omega

/-- **The frontier is empty**: `rBeyond (k+2+climbN) c = 0`.  (Else the segment would have
`climbN + 1` elements.) -/
theorem rBeyond_frontier_succ_eq_zero (k : ℕ) (c : Config (AgentState L K)) :
    rBeyond (L := L) (K := K) (k + 2 + climbN (L := L) (K := K) k c) c = 0 := by
  set m := climbN (L := L) (K := K) k c with hm
  by_contra h0
  have hpos : 0 < rBeyond (L := L) (K := K) (k + 2 + m) c := by omega
  by_cases hcap : k + 2 + m ≤ capMinute (L := L) (K := K)
  · -- the whole segment [k+2, k+2+m] sits in the filter: card ≥ m+1 > m.
    have hsub : Finset.Icc (k + 2) (k + 2 + m) ⊆
        ((Finset.Icc (k + 2) (capMinute (L := L) (K := K))).filter
          (fun j => 0 < rBeyond (L := L) (K := K) j c)) := by
      intro x hx
      rw [Finset.mem_Icc] at hx
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hx.1, by omega⟩, ?_⟩
      have := rBeyond_antitone_threshold (L := L) (K := K) x (k + 2 + m) hx.2 c
      omega
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    -- m + 1 ≤ filter.card = m: contradiction
    have : k + 2 + m + 1 - (k + 2) ≤ m := by rw [hm] at hcard ⊢; exact hcard
    omega
  · exact h0 (rBeyond_eq_zero_of_cap_lt _ (by omega) c)

/-- **A climb rise seeds the frontier**: any configuration with a strictly larger climb height has
a clock at level `k+2+climbN k c` — unconditionally in both configurations. -/
theorem climbN_rise_subset (k : ℕ) (c : Config (AgentState L K)) :
    {c' : Config (AgentState L K) |
        climbN (L := L) (K := K) k c < climbN (L := L) (K := K) k c'} ⊆
      {c' | 1 ≤ rBeyond (L := L) (K := K) (k + 2 + climbN (L := L) (K := K) k c) c'} := by
  intro c' hc'
  rw [Set.mem_setOf_eq] at hc' ⊢
  have := rBeyond_pos_of_le_frontier (L := L) (K := K) k
    (k + 2 + climbN (L := L) (K := K) k c) c' (by omega) (by omega)
  omega

/-- **The climb height witnesses the bad event**: `0 < rBeyond (k+W₂)` forces
`W₂ − 1 ≤ climbN k`. -/
theorem climbN_ge_of_beyond_pos (k W₂ : ℕ) (hW₂ : 2 ≤ W₂) (c : Config (AgentState L K))
    (h : 0 < rBeyond (L := L) (K := K) (k + W₂) c) :
    W₂ - 1 ≤ climbN (L := L) (K := K) k c := by
  have hcap : k + W₂ ≤ capMinute (L := L) (K := K) := by
    by_contra hc
    rw [rBeyond_eq_zero_of_cap_lt (L := L) (K := K) (k + W₂) (by omega) c] at h
    omega
  have hsub : Finset.Icc (k + 2) (k + W₂) ⊆
      ((Finset.Icc (k + 2) (capMinute (L := L) (K := K))).filter
        (fun j => 0 < rBeyond (L := L) (K := K) j c)) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hx.1, by omega⟩, ?_⟩
    have := rBeyond_antitone_threshold (L := L) (K := K) x (k + W₂) hx.2 c
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  unfold climbN
  omega

/-! ## Part 2 — the per-pair minute upper bound and the `≤ 1` climb step. -/

/-- **Per-pair minute upper bound** on a Phase-3 clock-clock pair: both `Transition` outputs have
minute at most `max(inputs) + 1` (drip adds one; sync copies the max; the synced-at-cap counter
keeps minutes). -/
theorem transition_p3_minute_le_succ_max (s t : AgentState L K)
    (hsc : s.role = .clock) (htc : t.role = .clock)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3) :
    (Transition L K s t).1.minute.val ≤ max s.minute.val t.minute.val + 1 ∧
      (Transition L K s t).2.minute.val ≤ max s.minute.val t.minute.val + 1 := by
  classical
  have hout := HourCoupling.phase3_clock_out_phase_le_four (L := L) (K := K) s t hsc htc hs3 ht3
  have heq := HourCoupling.transition_eq_phase3 (L := L) (K := K) s t hs3 ht3
    (by rcases hout.1 with h | h <;> omega)
    (by rcases hout.2 with h | h <;> omega)
  rw [heq]
  have hsc' := stdCounterSubroutine_clock_minute (L := L) (K := K) s hsc (by omega)
  have htc' := stdCounterSubroutine_clock_minute (L := L) (K := K) t htc (by omega)
  by_cases hmin : s.minute = t.minute
  · by_cases hcap : s.minute.val < K * (L + 1)
    · -- DRIP: outputs ({s with minute := s.minute+1}, t).
      have hcap_t : t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hP3 : Phase3Transition L K s t =
          ({ s with minute := ⟨s.minute.val + 1, by omega⟩ }, t) := by
        unfold Phase3Transition
        simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap, hcap_t, ↓reduceDIte, reduceCtorEq, false_and, and_false, true_and,
          if_false]
      rw [hP3]
      exact ⟨by simp <;> omega, by simp <;> omega⟩
    · -- synced-at-cap: counter subroutine keeps minutes.
      have hcap_t : ¬ t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hP3 : Phase3Transition L K s t =
          (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
        unfold Phase3Transition
        simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap, hcap_t, dif_neg, not_false_eq_true]
        simp only [hsc'.1, htc'.1, reduceCtorEq, false_and, if_false, and_false]
      rw [hP3]
      constructor
      · rw [hsc'.2]; omega
      · rw [htc'.2]; omega
  · -- SYNC: both outputs at minute max(inputs).
    have hP3 : Phase3Transition L K s t =
        ({ s with minute := max s.minute t.minute },
          { t with minute := max s.minute t.minute }) := by
      unfold Phase3Transition
      simp only [hsc, htc, and_self, if_true, if_neg hmin, ne_eq, hmin,
        not_false_eq_true, reduceCtorEq, false_and, and_false, if_false]
    rw [hP3]
    have hmax : (max s.minute t.minute).val ≤ max s.minute.val t.minute.val := by
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]; exact le_max_right _ _
      · rw [max_eq_left h]; exact le_max_left _ _
    exact ⟨by simpa using Nat.le_succ_of_le hmax, by simpa using Nat.le_succ_of_le hmax⟩

/-- **The climb height rises by at most one per step** on the `AllClockP3` window: only the pair's
own outputs can cross a new threshold, all output minutes are `≤ max(inputs)+1`, and both inputs
sit strictly below any newly crossed threshold — so the new threshold is unique. -/
theorem climbN_le_succ_on_support (k : ℕ) (c c' : Config (AgentState L K))
    (hw : AllClockP3 (L := L) (K := K) c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    climbN (L := L) (K := K) k c' ≤ climbN (L := L) (K := K) k c + 1 := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hsupp
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hsupp
    rw [Protocol.scheduledStep] at hr
    subst hr
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hmem1 := mem_of_applicable_left happ
      have hmem2 := mem_of_applicable_right happ
      obtain ⟨h1c, h1p⟩ := hw r₁ hmem1
      obtain ⟨h2c, h2p⟩ := hw r₂ hmem2
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
              (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]
      have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
      set c' := Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ with hcdef
      -- the only possible new threshold
      set jstar := max r₁.minute.val r₂.minute.val + 1 with hjstar
      have hminute := transition_p3_minute_le_succ_max (L := L) (K := K) r₁ r₂ h1c h2c h1p h2p
      -- filter(c') ⊆ insert jstar (filter(c))
      have hsubset : ((Finset.Icc (k + 2) (capMinute (L := L) (K := K))).filter
          (fun j => 0 < rBeyond (L := L) (K := K) j c')) ⊆
            insert jstar ((Finset.Icc (k + 2) (capMinute (L := L) (K := K))).filter
              (fun j => 0 < rBeyond (L := L) (K := K) j c)) := by
        intro j hj
        rw [Finset.mem_filter] at hj
        obtain ⟨hjIcc, hjpos⟩ := hj
        rw [Finset.mem_insert]
        by_cases hjold : 0 < rBeyond (L := L) (K := K) j c
        · exact Or.inr (Finset.mem_filter.mpr ⟨hjIcc, hjold⟩)
        · -- new threshold: some agent of c' is a clock at minute ≥ j, none of c is.
          left
          have hj0 : rBeyond (L := L) (K := K) j c = 0 := by omega
          have hex : ∃ a ∈ c', clockBeyondP (L := L) (K := K) j a := by
            have : 0 < Multiset.countP (fun a => clockBeyondP (L := L) (K := K) j a) c' := hjpos
            rwa [Multiset.countP_pos] at this
          obtain ⟨a, ha, hap⟩ := hex
          rw [hc', hδ] at ha
          rw [Multiset.mem_add] at ha
          have hnotc : ∀ b ∈ c, ¬ clockBeyondP (L := L) (K := K) j b := by
            intro b hb hbp
            have hposc : 0 < rBeyond (L := L) (K := K) j c :=
              Multiset.countP_pos.mpr ⟨b, hb, hbp⟩
            omega
          rcases ha with ha | ha
          · exact absurd hap (hnotc a (Multiset.mem_of_le (tsub_le_self (a := c)) ha))
          · -- a is one of the two outputs: j ≤ a.minute ≤ max(inputs)+1, and both inputs < j.
            have hr1lt : r₁.minute.val < j := by
              by_contra hlt
              exact hnotc r₁ hmem1 ⟨h1c, by omega⟩
            have hr2lt : r₂.minute.val < j := by
              by_contra hlt
              exact hnotc r₂ hmem2 ⟨h2c, by omega⟩
            have hjle : j ≤ a.minute.val := hap.2
            have hamin : a.minute.val ≤ max r₁.minute.val r₂.minute.val + 1 := by
              rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
                  Multiset (AgentState L K))
                  = (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2} from rfl] at ha
              rcases Multiset.mem_cons.mp ha with ha | ha
              · rw [ha]; exact hminute.1
              · rw [Multiset.mem_singleton.mp ha]; exact hminute.2
            rw [hjstar]
            rcases max_cases r₁.minute.val r₂.minute.val with ⟨hm, _⟩ | ⟨hm, _⟩ <;> omega
      calc climbN (L := L) (K := K) k c' ≤
          (insert jstar ((Finset.Icc (k + 2) (capMinute (L := L) (K := K))).filter
            (fun j => 0 < rBeyond (L := L) (K := K) j c))).card :=
            Finset.card_le_card hsubset
        _ ≤ climbN (L := L) (K := K) k c + 1 := Finset.card_insert_le _ _
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; omega
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; omega

/-! ## Part 3 — the one-step climb probability on the gate. -/

/-- **The climb-rise probability is at most `(B'/n)²`** when the tail above `k+1` is capped at
`B'`: the rise event seeds the empty frontier level, whose one-step probability is the squared
frontier-minute fraction (`real_front_advance_squares`), and the frontier minute count is at most
`rBeyond (k+1) ≤ B'`. -/
theorem climb_prob_le_sq (k B' : ℕ) (c : Config (AgentState L K))
    (hw : AllClockP3 (L := L) (K := K) c) (hc : 2 ≤ c.card)
    (hB' : rBeyond (L := L) (K := K) (k + 1) c ≤ B') :
    (NonuniformMajority L K).transitionKernel c
        {c' | climbN (L := L) (K := K) k c < climbN (L := L) (K := K) k c'} ≤
      ENNReal.ofReal (((B' : ℝ) / (c.card : ℝ)) ^ 2) := by
  set M := k + 1 + climbN (L := L) (K := K) k c with hM
  have h0 : rBeyond (L := L) (K := K) (M + 1) c = 0 := by
    rw [hM, show k + 1 + climbN (L := L) (K := K) k c + 1
      = k + 2 + climbN (L := L) (K := K) k c from by ring]
    exact rBeyond_frontier_succ_eq_zero (L := L) (K := K) k c
  have hsub : {c' : Config (AgentState L K) |
      climbN (L := L) (K := K) k c < climbN (L := L) (K := K) k c'} ⊆
        {c' | 1 ≤ rBeyond (L := L) (K := K) (M + 1) c'} := by
    rw [hM, show k + 1 + climbN (L := L) (K := K) k c + 1
      = k + 2 + climbN (L := L) (K := K) k c from by ring]
    exact climbN_rise_subset (L := L) (K := K) k c
  refine le_trans (measure_mono hsub) (le_trans
    (real_front_advance_squares (L := L) (K := K) M c hw hc h0) ?_)
  apply ENNReal.ofReal_le_ofReal
  have hcardpos : (0 : ℝ) < (c.card : ℝ) := by
    have : 0 < c.card := by omega
    exact_mod_cast this
  have hfle : frontMinuteCount (L := L) (K := K) M c ≤ B' := by
    calc frontMinuteCount (L := L) (K := K) M c
        ≤ rBeyond (L := L) (K := K) M c :=
          frontMinuteCount_le_rBeyond (L := L) (K := K) M c
      _ ≤ rBeyond (L := L) (K := K) (k + 1) c :=
          rBeyond_antitone_threshold (L := L) (K := K) (k + 1) M (by omega) c
      _ ≤ B' := hB'
  have hfle' : (frontMinuteCount (L := L) (K := K) M c : ℝ) ≤ (B' : ℝ) := by
    exact_mod_cast hfle
  apply pow_le_pow_left₀ (by positivity)
  gcongr

/-! ## Part 4 — the truncated climb potential, its gate, and the gated drift. -/

/-- The pre-bulk gate with the union escape: population `n`, the Phase-3 clock window, and EITHER
the tail above `k+1` capped at `B'` (pre-bulk, drift active) OR the bulk arrived at `k`
(`θn ≤ rBeyond k`, potential frozen at `0`).  Leaving this gate = the DANGEROUS event
`{rBeyond (k+1) > B' ∧ rBeyond k < θn}` (early-drip blowup before bulk arrival, the brick-3.4
escape) or leaving the hour window. -/
def climbGate (n k B' θn : ℕ) : Set (Config (AgentState L K)) :=
  {c | c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
    (rBeyond (L := L) (K := K) (k + 1) c ≤ B' ∨ θn ≤ rBeyond (L := L) (K := K) k c)}

/-- The truncated climb potential: `exp(s·climbN)` while the bulk has not arrived at `k`, frozen
to `0` after.  The freeze makes the drift hold on the bulk-arrived part of the gate (monotonicity
of `rBeyond k` keeps it frozen). -/
noncomputable def climbPot (k θn : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if rBeyond (L := L) (K := K) k c < θn then
    ENNReal.ofReal (Real.exp (s * (climbN (L := L) (K := K) k c : ℝ)))
  else 0

theorem climbPot_measurable (k θn : ℕ) (s : ℝ) :
    Measurable (climbPot (L := L) (K := K) k θn s) := Measurable.of_discrete

/-- Almost-every one-step successor satisfies any support-closed property (one-step transfer of
the PMF support to the kernel measure). -/
theorem ae_step_of_support (c : Config (AgentState L K))
    (P : Config (AgentState L K) → Prop)
    (h : ∀ c', c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → P c') :
    ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c), P c' := by
  change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, P c'
  rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (h c' hsupp)

/-- **The gated drift of the truncated climb potential.**  On the union gate the one-step drift
holds with the MGF factor `r = 1 + (B'/n)²(e^s − 1)`: on the pre-bulk part by the generic MGF
contraction at the squared frontier rate, on the bulk-arrived part trivially (the potential is
frozen at `0` and stays `0`). -/
theorem climbPot_drift_on_gate (n k B' θn : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∀ c ∈ climbGate (L := L) (K := K) n k B' θn,
      ∫⁻ c', climbPot (L := L) (K := K) k θn s c'
          ∂((NonuniformMajority L K).transitionKernel c) ≤
        ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)) *
          climbPot (L := L) (K := K) k θn s c := by
  rintro c ⟨hcard, hw, hgate⟩
  by_cases hbulk : θn ≤ rBeyond (L := L) (K := K) k c
  · -- bulk arrived: potential frozen at 0, successors stay frozen.
    have hzero : climbPot (L := L) (K := K) k θn s c = 0 := by
      unfold climbPot; rw [if_neg (by omega)]
    have hae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        climbPot (L := L) (K := K) k θn s c' = 0 := by
      apply ae_step_of_support
      intro c' hsupp
      have hmono := rBeyond_ge_monotone (L := L) (K := K) k θn c c' hw hbulk hsupp
      unfold climbPot; rw [if_neg (by omega)]
    rw [hzero, mul_zero, lintegral_congr_ae hae, lintegral_zero]
  · -- pre-bulk: the gate supplies the B' cap; apply the generic MGF contraction.
    have hpre : rBeyond (L := L) (K := K) k c < θn := by omega
    have hB' : rBeyond (L := L) (K := K) (k + 1) c ≤ B' := by
      rcases hgate with h | h
      · exact h
      · omega
    have hval : climbPot (L := L) (K := K) k θn s c
        = ENNReal.ofReal (Real.exp (s * (climbN (L := L) (K := K) k c : ℝ))) := by
      unfold climbPot; rw [if_pos hpre]
    by_cases hc : 2 ≤ c.card
    · haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
        (inferInstance : IsMarkovKernel
          (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
      have hstep_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          climbN (L := L) (K := K) k c' ≤ climbN (L := L) (K := K) k c + 1 :=
        ae_step_of_support c _ (fun c' hsupp =>
          climbN_le_succ_on_support (L := L) (K := K) k c c' hw hsupp)
      have hprob : (NonuniformMajority L K).transitionKernel c
          {c' | climbN (L := L) (K := K) k c < climbN (L := L) (K := K) k c'} ≤
            ENNReal.ofReal (((B' : ℝ) / (n : ℝ)) ^ 2) := by
        rw [← hcard]
        exact climb_prob_le_sq (L := L) (K := K) k B' c hw hc hB'
      have hmgf := mgf_one_step ((NonuniformMajority L K).transitionKernel c) s hs
        (climbN (L := L) (K := K) k) (climbN (L := L) (K := K) k c) hstep_ae
        (((B' : ℝ) / (n : ℝ)) ^ 2) (by positivity) hprob
      calc ∫⁻ c', climbPot (L := L) (K := K) k θn s c'
            ∂((NonuniformMajority L K).transitionKernel c)
          ≤ ∫⁻ c', ENNReal.ofReal (Real.exp (s * (climbN (L := L) (K := K) k c' : ℝ)))
              ∂((NonuniformMajority L K).transitionKernel c) := by
            apply lintegral_mono
            intro c'
            unfold climbPot
            split_ifs
            · exact le_rfl
            · exact zero_le'
        _ ≤ ENNReal.ofReal ((1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)) *
              Real.exp (s * (climbN (L := L) (K := K) k c : ℝ))) := hmgf
        _ = ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)) *
              climbPot (L := L) (K := K) k θn s c := by
            rw [hval, ← ENNReal.ofReal_mul]
            have hexp_ge : (1 : ℝ) ≤ Real.exp s := Real.one_le_exp hs
            nlinarith [sq_nonneg ((B' : ℝ) / (n : ℝ))]
    · -- degenerate population (< 2): the kernel is a point mass at c itself.
      have hpure : (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c := by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]
      have hker : (NonuniformMajority L K).transitionKernel c
          = (PMF.pure c).toMeasure := by
        change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure = _
        rw [hpure]
      rw [hker, PMF.toMeasure_pure,
        lintegral_dirac' _ (climbPot_measurable (L := L) (K := K) k θn s)]
      have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal
          (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)) := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
        apply ENNReal.ofReal_le_ofReal
        have hexp_ge : (1 : ℝ) ≤ Real.exp s := Real.one_le_exp hs
        nlinarith [sq_nonneg ((B' : ℝ) / (n : ℝ))]
      calc climbPot (L := L) (K := K) k θn s c
          = 1 * climbPot (L := L) (K := K) k θn s c := (one_mul _).symm
        _ ≤ ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)) *
              climbPot (L := L) (K := K) k θn s c := by gcongr

/-! ## Part 5 — the capstone: the gated climb tail on the real kernel. -/

/-- **The gated climb tail (brick 3.2 capstone).**  Over `t` steps of the real kernel from `c₀`,
the probability that the bulk has NOT arrived at level `k` yet the leading edge has climbed `W₂`
levels above it is at most the ESCAPE mass (the gate was left: the early-drip count above `k+1`
blew past `B'` pre-bulk — the brick-3.4 obligation — or the hour window closed) plus the gated
geometric tail

  `r^t · climbPot c₀ / e^{s(W₂−1)}`,   `r = 1 + (B'/n)²(e^s − 1)`.

At paper scales (`B'/n = n^{-0.8}`, `t = O(n log n)`, `s = Θ(log n)`, `W₂ = Θ(log log n)`) the
second term is `n^{-ω(1)}` — the very-high-probability `ClimbBound`. -/
theorem climb_real_tail (n k B' θn W₂ : ℕ) (hW₂ : 2 ≤ W₂)
    (s : ℝ) (hs : 0 ≤ s) (t : ℕ) (c₀ : Config (AgentState L K)) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | rBeyond (L := L) (K := K) k c < θn ∧
          0 < rBeyond (L := L) (K := K) (k + W₂) c} ≤
      (GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
          (climbGate (L := L) (K := K) n k B' θn) ^ t) (some c₀) {none} +
        (ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1))) ^ t *
          climbPot (L := L) (K := K) k θn s c₀ /
          ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1))) := by
  have hexp_ge : (1 : ℝ) ≤ Real.exp s := Real.one_le_exp hs
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal
      (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg ((B' : ℝ) / (n : ℝ))]
  -- the bad event is inside the high-potential event {e^{s(W₂−1)} ≤ climbPot}
  have hbad_sub : {c : Config (AgentState L K) |
      rBeyond (L := L) (K := K) k c < θn ∧ 0 < rBeyond (L := L) (K := K) (k + W₂) c} ⊆
        {c | ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1))) ≤
          climbPot (L := L) (K := K) k θn s c} := by
    rintro c ⟨hpre, hclimb⟩
    rw [Set.mem_setOf_eq]
    have hN := climbN_ge_of_beyond_pos (L := L) (K := K) k W₂ hW₂ c hclimb
    unfold climbPot
    rw [if_pos hpre]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : ((W₂ : ℝ) - 1) ≤ (climbN (L := L) (K := K) k c : ℝ) := by
      have h1 : ((W₂ - 1 : ℕ) : ℝ) ≤ (climbN (L := L) (K := K) k c : ℝ) := by
        exact_mod_cast hN
      rwa [Nat.cast_sub (by omega), Nat.cast_one] at h1
    nlinarith [hs, hcast]
  refine le_trans (measure_mono hbad_sub) ?_
  exact GatedDrift.gated_real_tail (G := climbGate (L := L) (K := K) n k B' θn)
    (climbPot (L := L) (K := K) k θn s)
    (ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1))) hr1
    (climbPot_drift_on_gate (L := L) (K := K) n k B' θn s hs) t c₀
    (ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1))))
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top

end ClimbTail

end ExactMajority
