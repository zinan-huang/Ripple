import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStages
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1Persistence

/-!
# The Phase-1 drain producer (Doty plan node N11b)

The three stage estimates (21), (23), (25) of DOTY-PHASE02 §3 and the residual clock
exit are restated from a start time `s` on a recorded-past event `A` at `s`, and
composed at the fixed offsets `s`, `s + 16000 n`, `s + 16000 n + T_far`,
`s + weakHorizon n`. Summing over the values of a pair-log stopping time with
`genuine_seed_splice` gives the joint failure bound `1 / n ^ 2` of PHASE02 (28).

The one protocol fact used beyond the compiled stage lemmas is that a Phase-1 step
keeps non-Main agents neutral; it enters the composition as the hypothesis
`hneutral` and is discharged separately.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseOneDrainProducer

open TimeTheorem PairLog TraceDrain PhaseOneDrainStages PhaseOneDrain

variable {L K : ℕ}

/-! ## Deterministic facts along the trace -/

/-- A quantity that does not increase in one step from the window `W` does not
increase along a stretch of the trace that stays in `W`. -/
theorem trace_le_of_window (init : Cfg L K) (ω : Ω L K) (f : Cfg L K → ℕ)
    (W : Cfg L K → Prop) (hf : ∀ c, W c → ∀ d, f (applyDraw c d) ≤ f c)
    (u v : ℕ) (huv : u ≤ v) (hW : ∀ k, u ≤ k → k < v → W (trace init ω k)) :
    f (trace init ω v) ≤ f (trace init ω u) := by
  induction v, huv using Nat.le_induction with
  | base => exact le_rfl
  | succ v huv ih =>
      rw [TraceDrain.trace_succ]
      exact (hf _ (hW v huv (Nat.lt_succ_self v)) _).trans
        (ih fun k hk hk' => hW k hk (by omega))

/-- A quantity preserved in one step from `W` is constant along a stretch in `W`. -/
theorem trace_eq_of_window (init : Cfg L K) (ω : Ω L K) (f : Cfg L K → ℕ)
    (W : Cfg L K → Prop) (hf : ∀ c, W c → ∀ d, f (applyDraw c d) = f c)
    (u v : ℕ) (huv : u ≤ v) (hW : ∀ k, u ≤ k → k < v → W (trace init ω k)) :
    f (trace init ω v) = f (trace init ω u) := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
      rw [TraceDrain.trace_succ, hf _ (hW v huv (Nat.lt_succ_self v)) _]
      exact ih fun k hk hk' => hW k hk (by omega)

/-- A property kept in one step from `W` persists along a stretch in `W`. -/
theorem trace_persist_of_window (init : Cfg L K) (ω : Ω L K) (P : Cfg L K → Prop)
    (W : Cfg L K → Prop) (hP : ∀ c, W c → P c → ∀ d, P (applyDraw c d))
    (u v : ℕ) (huv : u ≤ v) (hW : ∀ k, u ≤ k → k < v → W (trace init ω k))
    (hu : P (trace init ω u)) :
    P (trace init ω v) := by
  induction v, huv using Nat.le_induction with
  | base => exact hu
  | succ v huv ih =>
      rw [TraceDrain.trace_succ]
      exact hP _ (hW v huv (Nat.lt_succ_self v))
        (ih fun k hk hk' => hW k hk (by omega)) _

theorem mainCount_applyDraw_eq {n : ℕ} (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) (d : Draw L K) :
    RoleSplitConcentration.mainCount (applyDraw c d) =
      RoleSplitConcentration.mainCount c := by
  cases d with
  | none => rfl
  | some p =>
      exact Phase1GapFloorEntryClosure.mainCount_stepOrSelf_eq_of_phase1Win n c hwin _ _

/-- With safe Main biases, the Phase-1 mass is at most the population. -/
theorem phaseOneMass_le_card (c : Cfg L K) (h : Phase1FarPhi.MainBiasSafe c) :
    PhaseOneMass c ≤ c.card := by
  unfold PhaseOneMass
  calc (c.map (fun a => (AveragingRate.biasZ a).natAbs)).sum
      ≤ (c.map (fun _ => 1)).sum := by
        apply Multiset.sum_map_le_sum_map
        intro a ha
        by_cases hm : a.role = Role.main
        · have hs := h a ha hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with hs | hs | hs <;> simp [AveragingRate.biasZ, hm, hs]
        · simp [AveragingRate.biasZ, hm]
    _ = c.card := by simp

/-- One Main contributes at most two units to `farPhiN`. -/
theorem farPhiMainN_le_two (a : AgentState L K) :
    Phase1FarPhi.farPhiMainN a ≤ 2 := by
  have hphi : ∀ v : Fin 7, Phase1FarPhi.farPhi v ≤ 2 := by decide
  unfold Phase1FarPhi.farPhiMainN
  by_cases hmain : a.role = Role.main
  · rw [if_pos hmain]
    exact hphi a.smallBias
  · rw [if_neg hmain]
    omega

theorem farPhiN_le_two_mul_card (c : Cfg L K) :
    Phase1FarPhi.farPhiN c ≤ 2 * c.card := by
  unfold Phase1FarPhi.farPhiN
  induction c using Multiset.induction with
  | empty => simp
  | cons a c ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      have ha := farPhiMainN_le_two a
      omega

theorem farPhiN_le_two_mul_n {n g mc : ℕ} (c : Cfg L K)
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    Phase1FarPhi.farPhiN c ≤ 2 * n := by
  rw [← hentry.1.1]
  exact farPhiN_le_two_mul_card c

/-! ## Stage estimates from a past-measurable start -/

/-- Drain from a start time: a nat potential that does not increase on `W` and
drops with kernel probability at least `r` on `W` off the target `T` keeps the
trace in `W` off `T` for `N` steps after `s` (on a prefix event `A` at `s` with
potential at most `Ψ`) with probability at most `(1 - r/2)^N 2^Ψ P(A)`. -/
theorem drain_tail_from (init : Cfg L K) (ψ : Cfg L K → ℕ)
    (W T : Cfg L K → Prop)
    (hmono : ∀ c, W c → ∀ d, ψ (applyDraw c d) ≤ ψ c) (r : ℝ≥0∞)
    (hdrop : ∀ c, W c → ¬ T c →
      r ≤ (NonuniformMajority L K).transitionKernel c {c' | ψ c' + 1 ≤ ψ c})
    (s N : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K)) (Ψ : ℕ)
    (hΨ : ∀ p ∈ A, ψ (prefixCfg init s p) ≤ Ψ) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∀ u, s ≤ u → u < s + N → W (trace init ω u) ∧ ¬ T (trace init ω u)} ≤
      (1 - r / 2) ^ N * ((2 ^ Ψ : ℕ) : ℝ≥0∞) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  have h := potential_drift_tail_from init (fun c => 2 ^ ψ c)
    (fun c => W c ∧ ¬ T c) (r / 2)
    (fun c hc => exp_drift_of_drop ψ c (hmono c hc.1) r (hdrop c hc.1 hc.2))
    s N A (2 ^ Ψ)
    (fun p hp => Nat.pow_le_pow_right (by norm_num) (hΨ p hp))
  refine le_trans (measure_mono ?_) h
  intro ω hω
  exact ⟨hω.1, hω.2, Nat.one_le_two_pow⟩

/-- Clock exit from a start time, with genuine residual counters at `s`. -/
theorem clock_exit_from (init : Cfg L K) {n : ℕ} (hn : 2 ≤ n) (g M R : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (s T : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, Phase1ClockDepthStopped.Good n g M (prefixCfg init s p) ∧
      ∀ a ∈ prefixCfg init s p, a.role = Role.clock → R ≤ a.counter.val) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∃ u, s ≤ u ∧ u ≤ s + T ∧
          ¬ Phase1ClockDepthStopped.Good n g M (trace init ω u)} ≤
      ClockCounterDepthCover.counterDepthTail n T R θ *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  have hdrift : ∀ c, Phase1ClockDepthStopped.Good (L := L) (K := K) n g M c →
      ∫⁻ c', Phase1ClockDepthStopped.stoppedDepthMass n g M R θ c'
          ∂(NonuniformMajority L K).transitionKernel c ≤
        ClockCounterDepthCover.counterDepthRate n θ *
          Phase1ClockDepthStopped.stoppedDepthMass n g M R θ c := by
    intro c hc
    have h := Phase1ClockDepthStopped.stoppedDepthMass_drift
      (L := L) (K := K) n g M R hn θ hθ c
    rwa [Phase1ClockDepthStopped.stopK_eq_real_of_good n g M c hc] at h
  have hthr : ∀ c, ¬ Phase1ClockDepthStopped.Good (L := L) (K := K) n g M c →
      ClockCounterDepthCover.counterDepthThreshold R θ ≤
        Phase1ClockDepthStopped.stoppedDepthMass n g M R θ c := by
    intro c hc
    unfold Phase1ClockDepthStopped.stoppedDepthMass
    rw [if_neg hc]
  have hΨ : ∀ p ∈ A,
      Phase1ClockDepthStopped.stoppedDepthMass n g M R θ (prefixCfg init s p) ≤
        (n : ℝ≥0∞) := by
    intro p hp
    obtain ⟨hgood, hres⟩ := hA p hp
    unfold Phase1ClockDepthStopped.stoppedDepthMass
    rw [if_pos hgood]
    have h := counterDepthMass_start_le_card_of_residual 1 R θ
      (prefixCfg init s p) hgood.1.1.2 hres
    simpa only [hgood.1.1.1] using h
  have h := growth_exit_tail_from init
    (Phase1ClockDepthStopped.stoppedDepthMass n g M R θ)
    (Phase1ClockDepthStopped.Good n g M) (ClockCounterDepthCover.counterDepthRate n θ)
    (Phase1ClockDepthStopped.one_le_counterDepthRate n θ) hdrift
    (ClockCounterDepthCover.counterDepthThreshold R θ) hthr s T A (n : ℝ≥0∞) hΨ
  have h0 := ClockCounterDepthCover.counterDepthThreshold_ne_zero R θ
  have htop := ClockCounterDepthCover.counterDepthThreshold_ne_top R θ
  calc _ = (ClockCounterDepthCover.counterDepthThreshold R θ)⁻¹ *
        (ClockCounterDepthCover.counterDepthThreshold R θ *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
            ∃ u, s ≤ u ∧ u ≤ s + T ∧
              ¬ Phase1ClockDepthStopped.Good n g M (trace init ω u)}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
    _ ≤ (ClockCounterDepthCover.counterDepthThreshold R θ)⁻¹ *
        (ClockCounterDepthCover.counterDepthRate n θ ^ T * (n : ℝ≥0∞) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}) :=
        mul_le_mul_left' h _
    _ = _ := by
        unfold ClockCounterDepthCover.counterDepthTail
        rw [div_eq_mul_inv]
        ring

/-! ## Scalar bounds -/

theorem drain_scalar (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (N Ψ : ℕ) :
    (1 - ENNReal.ofReal r / 2) ^ N * ((2 ^ Ψ : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp ((Ψ : ℝ) * Real.log 2 - (N : ℝ) * r / 2)) := by
  have hhalf : ENNReal.ofReal r / 2 = ENNReal.ofReal (r / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  have hsub : 1 - ENNReal.ofReal r / 2 = ENNReal.ofReal (1 - r / 2) := by
    rw [hhalf, ENNReal.ofReal_sub _ (by linarith), ENNReal.ofReal_one]
  have hb0 : 0 ≤ 1 - r / 2 := by linarith
  have hpow2 : ((2 ^ Ψ : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ Ψ) := by
    rw [← ENNReal.ofReal_natCast]
    norm_num
  rw [hsub, hpow2, ← ENNReal.ofReal_pow hb0, ← ENNReal.ofReal_mul (pow_nonneg hb0 N)]
  apply ENNReal.ofReal_le_ofReal
  have he : (1 - r / 2) ^ N ≤ Real.exp (-(r / 2)) ^ N :=
    pow_le_pow_left₀ hb0 (by linarith [Real.add_one_le_exp (-(r / 2))]) N
  have h2 : (2 : ℝ) ^ Ψ = Real.exp ((Ψ : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  calc (1 - r / 2) ^ N * (2 : ℝ) ^ Ψ
      ≤ Real.exp (-(r / 2)) ^ N * (2 : ℝ) ^ Ψ :=
        mul_le_mul_of_nonneg_right he (by positivity)
    _ = Real.exp ((Ψ : ℝ) * Real.log 2 - (N : ℝ) * r / 2) := by
        rw [h2, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring

theorem preliminary_scalar {n : ℕ} :
    (1 - ENNReal.ofReal (1 / 4000 : ℝ) / 2) ^ (16000 * n) *
        ((2 ^ (2 * n) : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)) := by
  refine (drain_scalar _ (by norm_num) (by norm_num) _ _).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hlog := Real.log_two_lt_d9
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith

theorem mass_scalar {n : ℕ} :
    (1 - ENNReal.ofReal (1 / 400000 : ℝ) / 2) ^ (800000 * n) *
        ((2 ^ n : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 4)) := by
  refine (drain_scalar _ (by norm_num) (by norm_num) _ _).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hlog := Real.log_two_lt_d9
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith

/-- The far-extinction ceiling. -/
noncomputable def farTime (n : ℕ) : ℕ :=
  Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ))

theorem far_scalar {n : ℕ} (hn : 2 ≤ n) (Φ : ℕ) (hΦ : 100 * Φ ≤ n) :
    (1 - partnerRate n ((229 * n + 999) / 1000)) ^ farTime n * (Φ : ℝ≥0∞) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) * Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ))) := by
  set T : ℕ := farTime n with hT
  set x : ℝ := (229 : ℝ) / (1000 * (n : ℝ)) with hx
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]
    linarith
  have hρ : ENNReal.ofReal x ≤ partnerRate n ((229 * n + 999) / 1000) :=
    refined_partnerRate_lower hn
  have h1 : 1 - partnerRate n ((229 * n + 999) / 1000) ≤ ENNReal.ofReal (1 - x) := by
    calc 1 - partnerRate n ((229 * n + 999) / 1000)
        ≤ 1 - ENNReal.ofReal x := tsub_le_tsub_left hρ 1
      _ = ENNReal.ofReal (1 - x) := by rw [ENNReal.ofReal_sub _ hx0, ENNReal.ofReal_one]
  have h2 : (1 - partnerRate n ((229 * n + 999) / 1000)) ^ T ≤
      ENNReal.ofReal ((1 - x) ^ T) := by
    rw [ENNReal.ofReal_pow (by linarith)]
    gcongr
  have hψ : (Φ : ℝ) ≤ (n : ℝ) / 100 := by
    have : ((100 * Φ : ℕ) : ℝ) ≤ n := by exact_mod_cast hΦ
    push_cast at this
    linarith
  have hreal : (1 - x) ^ T * (Φ : ℝ) ≤
      (1 / 100 : ℝ) * Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ)) := by
    have he : (1 - x) ^ T ≤ Real.exp (-x * (T : ℝ)) := by
      calc (1 - x) ^ T ≤ (Real.exp (-x)) ^ T :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-x)]) T
        _ = Real.exp (-x * (T : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    have hcal := far_decay_calibration hnpos
    calc (1 - x) ^ T * (Φ : ℝ)
        ≤ Real.exp (-x * (T : ℝ)) * ((n : ℝ) / 100) :=
          mul_le_mul he hψ (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = ((n : ℝ) / 100) * Real.exp (-((229 : ℝ) / (1000 * (n : ℝ))) *
            (Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) : ℝ)) := by
          rw [hx, hT, farTime]; ring
      _ ≤ _ := hcal
  calc (1 - partnerRate n ((229 * n + 999) / 1000)) ^ T * (Φ : ℝ≥0∞)
      ≤ ENNReal.ofReal ((1 - x) ^ T) * ENNReal.ofReal (Φ : ℝ) := by
        rw [ENNReal.ofReal_natCast]
        gcongr
    _ = ENNReal.ofReal ((1 - x) ^ T * (Φ : ℝ)) :=
        (ENNReal.ofReal_mul (pow_nonneg (by linarith) T)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-! ## Composition at fixed offsets from the start time -/

/-- The failure scale of the composed stages. -/
noncomputable def stageBudget (n R : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  ClockCounterDepthCover.counterDepthTail n
      (16000 * n + farTime n + 800000 * n) R θ +
    (1 - ENNReal.ofReal (1 / 4000 : ℝ) / 2) ^ (16000 * n) *
      ((2 ^ (2 * n) : ℕ) : ℝ≥0∞) +
    (1 - partnerRate n ((229 * n + 999) / 1000)) ^ farTime n *
      ((n / 100 : ℕ) : ℝ≥0∞) +
    (1 - ENNReal.ofReal (1 / 400000 : ℝ) / 2) ^ (800000 * n) *
      ((2 ^ n : ℕ) : ℝ≥0∞)

/-- From a recorded-past event at `s` whose states are in the clock gate with
residual counters and neutral non-Mains, the trace fails to be drained at
`s + 16000 n + T_far + 800000 n` with probability at most `stageBudget` times the
probability of the event. -/
theorem stage_composition (init : Cfg L K) {n : ℕ} (hn : 2 ≤ n) (d M R : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hM99 : 99 * n ≤ 200 * M) (hM40 : 40 * d ≤ M)
    (hneutral : ∀ c : Cfg L K, PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c →
      Phase1FarPhi.NonMainNeutral c → ∀ dr, Phase1FarPhi.NonMainNeutral (applyDraw c dr))
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, Phase1ClockDepthStopped.Good n d M (prefixCfg init s p) ∧
      (∀ a ∈ prefixCfg init s p, a.role = Role.clock → R ≤ a.counter.val) ∧
      Phase1FarPhi.NonMainNeutral (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ PhaseOneDrained
          (trace init ω (s + (16000 * n + farTime n + 800000 * n)))} ≤
      stageBudget n R θ *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  set N1 := 16000 * n with hN1
  set T := farTime n with hT
  set N3 := 800000 * n with hN3
  set t1 := s + N1 with ht1
  set t2 := t1 + T with ht2
  have hst1 : s ≤ t1 := Nat.le_add_right s N1
  have hst2 : s ≤ t2 := by omega
  -- prefix events at the later stage boundaries
  set A1 : Set ((k : Finset.Iic t1) → Draw L K) :=
    {q | restrictPrefix hst1 q ∈ A ∧ PreliminaryTarget n (prefixCfg init t1 q)} with hA1
  set A2 : Set ((k : Finset.Iic t2) → Draw L K) :=
    {q | restrictPrefix hst2 q ∈ A ∧ Phase1FarPhi.farPhiN (prefixCfg init t2 q) = 0 ∧
      PhaseOnlyWindows.Phase1Win (L := L) (K := K) n (prefixCfg init t2 q)} with hA2
  set PA := law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} with hPA
  -- window facts from the gate
  have hwinG : ∀ c, Phase1ClockDepthStopped.Good (L := L) (K := K) n d M c → PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c :=
    fun c hc => hc.1.1
  have hprelG : ∀ c, Phase1ClockDepthStopped.Good (L := L) (K := K) n d M c → PreliminaryWindow n d c := by
    intro c hc
    obtain ⟨⟨hwin, hgap, hmc⟩, _⟩ := hc
    exact ⟨hwin, by omega, by omega, hgap⟩
  have hmassG : ∀ c, Phase1ClockDepthStopped.Good (L := L) (K := K) n d M c → Phase1FarPhi.farPhiN c = 0 → MassWindow n d c := by
    intro c hc hphi
    obtain ⟨⟨hwin, hgap, hmc⟩, _⟩ := hc
    exact ⟨hwin, (Phase1FarPhi.farPhiN_eq_zero_iff_mainBiasSafe c).mp hphi,
      by omega, by omega, hgap⟩
  -- the four bounds
  have hC := clock_exit_from init hn d M R θ hθ s (N1 + T + N3) A
    (fun p hp => ⟨(hA p hp).1, (hA p hp).2.1⟩)
  have hE1 := drain_tail_from init Phase1FarPhi.farPhiN (PreliminaryWindow n d)
    (PreliminaryTarget n) (fun c hc dr => farPhiN_applyDraw_le c hc.1 dr)
    (ENNReal.ofReal (1 / 4000 : ℝ))
    (fun c hc htarget => by
      obtain ⟨hwin, hmain, hsmall, hgap⟩ := hc
      have hphi : n < 100 * Phase1FarPhi.farPhiN c := by
        unfold PreliminaryTarget at htarget
        omega
      exact preliminary_drop_probability hn c hwin hmain hsmall hgap hphi)
    s N1 A (2 * n)
    (fun p hp => farPhiN_le_two_mul_n _ (hA p hp).1.1)
  have hE2 := potential_drift_tail_from init Phase1FarPhi.farPhiN (FarWindow n d) _
    (fun c hc => refined_farPhi_drift hn d c hc.1.1 hc.1.2.1 hc.1.2.2.1
      hc.1.2.2.2 hc.2) t1 T A1 (n / 100)
    (fun q hq => by
      have h := hq.2
      unfold PreliminaryTarget at h
      exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
  have hE3 := drain_tail_from init PhaseOneMass (MassWindow n d) MassTarget
    (fun c hc dr => mass_applyDraw_le c hc.1 dr) (ENNReal.ofReal (1 / 400000 : ℝ))
    (fun c hc htarget => mass_drop_probability hn c hc htarget) t2 N3 A2 n
    (fun q hq => by
      have hsafe := (Phase1FarPhi.farPhiN_eq_zero_iff_mainBiasSafe _).mp hq.2.1
      have h := phaseOneMass_le_card _ hsafe
      rwa [hq.2.2.1] at h)
  have hPA1 : law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t1 ω ∈ A1} ≤ PA :=
    measure_mono fun ω hω => hω.1
  have hPA2 : law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t2 ω ∈ A2} ≤ PA :=
    measure_mono fun ω hω => hω.1
  -- the pointwise covering
  have hcover :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ PhaseOneDrained (trace init ω (s + (N1 + T + N3)))} ⊆
      ({ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
          ∃ u, s ≤ u ∧ u ≤ s + (N1 + T + N3) ∧ ¬ Phase1ClockDepthStopped.Good n d M (trace init ω u)} ∪
        {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
          ∀ u, s ≤ u → u < s + N1 →
            PreliminaryWindow n d (trace init ω u) ∧
              ¬ PreliminaryTarget n (trace init ω u)}) ∪
      ({ω | frestrictLe (π := fun _ : ℕ => Draw L K) t1 ω ∈ A1 ∧
          (∀ u, t1 ≤ u → u < t1 + T → FarWindow n d (trace init ω u)) ∧
          1 ≤ Phase1FarPhi.farPhiN (trace init ω (t1 + T))} ∪
        {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t2 ω ∈ A2 ∧
          ∀ u, t2 ≤ u → u < t2 + N3 →
            MassWindow n d (trace init ω u) ∧ ¬ MassTarget (trace init ω u)}) := by
    rintro ω ⟨hAω, hbad⟩
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hnot
    obtain ⟨⟨hC', hE1'⟩, hE2', hE3'⟩ := hnot
    have hgood : ∀ u, s ≤ u → u ≤ s + (N1 + T + N3) → Phase1ClockDepthStopped.Good n d M (trace init ω u) := by
      intro u hu hu'
      by_contra hg
      exact hC' ⟨hAω, u, hu, hu', hg⟩
    have hwin : ∀ k, s ≤ k → k < s + (N1 + T + N3) →
        PhaseOnlyWindows.Phase1Win (L := L) (K := K) n (trace init ω k) :=
      fun k hk hk' => hwinG _ (hgood k hk hk'.le)
    -- stage 1
    have hPT1 : PreliminaryTarget n (trace init ω t1) := by
      by_contra hno
      apply hE1'
      refine ⟨hAω, fun u hu hu' => ⟨hprelG _ (hgood u hu (by omega)), fun hpt => hno ?_⟩⟩
      unfold PreliminaryTarget at hpt ⊢
      have hmono := trace_le_of_window init ω Phase1FarPhi.farPhiN
        (PhaseOnlyWindows.Phase1Win (L := L) (K := K) n)
        (fun c hc dr => farPhiN_applyDraw_le c hc dr) u t1 hu'.le
        (fun k hk hk' => hwin k (by omega) (by omega))
      omega
    -- stage 2
    have hphi2 : Phase1FarPhi.farPhiN (trace init ω t2) = 0 := by
      by_contra hno
      apply hE2'
      refine ⟨⟨hAω, hPT1⟩, fun u hu hu' => ⟨hprelG _ (hgood u (by omega) (by omega)), ?_⟩,
        Nat.one_le_iff_ne_zero.mpr hno⟩
      unfold PreliminaryTarget at hPT1 ⊢
      have hmono := trace_le_of_window init ω Phase1FarPhi.farPhiN
        (PhaseOnlyWindows.Phase1Win (L := L) (K := K) n)
        (fun c hc dr => farPhiN_applyDraw_le c hc dr) t1 u hu
        (fun k hk hk' => hwin k (by omega) (by omega))
      omega
    have hphiz : ∀ u, t2 ≤ u → u ≤ s + (N1 + T + N3) →
        Phase1FarPhi.farPhiN (trace init ω u) = 0 := by
      intro u hu hu'
      have hmono := trace_le_of_window init ω Phase1FarPhi.farPhiN
        (PhaseOnlyWindows.Phase1Win (L := L) (K := K) n)
        (fun c hc dr => farPhiN_applyDraw_le c hc dr) t2 u hu
        (fun k hk hk' => hwin k (by omega) (by omega))
      omega
    -- stage 3
    obtain ⟨u, hu, hu', hMT⟩ : ∃ u, t2 ≤ u ∧ u < t2 + N3 ∧ MassTarget (trace init ω u) := by
      by_contra hno
      push Not at hno
      apply hE3'
      refine ⟨⟨hAω, hphi2, hwin t2 (by omega) (by omega)⟩, fun u hu hu' =>
        ⟨hmassG _ (hgood u (by omega) (by omega)) (hphiz u hu (by omega)), hno u hu hu'⟩⟩
    apply hbad
    have hend : s + (N1 + T + N3) = t2 + N3 := by omega
    rw [hend] at hgood hwin ⊢
    have hG3 := hgood (t2 + N3) (by omega) le_rfl
    refine ⟨hG3.1.1.2, ?_, ?_⟩
    · intro a ha
      by_cases hm : a.role = Role.main
      · exact (Phase1FarPhi.farPhiN_eq_zero_iff_mainBiasSafe _).mp
          (hphiz (t2 + N3) (by omega) (by omega)) a ha hm
      · have hnm := trace_persist_of_window init ω Phase1FarPhi.NonMainNeutral
          (PhaseOnlyWindows.Phase1Win (L := L) (K := K) n) hneutral s (t2 + N3)
          (by omega) (fun k hk hk' => hwin k hk hk') (hA _ hAω).2.2
        rw [hnm a ha hm]
        simp
    · have hmass := trace_le_of_window init ω PhaseOneMass
        (PhaseOnlyWindows.Phase1Win (L := L) (K := K) n)
        (fun c hc dr => mass_applyDraw_le c hc dr) u (t2 + N3) hu'.le
        (fun k hk hk' => hwin k (by omega) hk')
      have hmc := trace_eq_of_window init ω RoleSplitConcentration.mainCount
        (PhaseOnlyWindows.Phase1Win (L := L) (K := K) n)
        (fun c hc dr => mainCount_applyDraw_eq c hc dr) u (t2 + N3) hu'.le
        (fun k hk hk' => hwin k (by omega) hk')
      unfold MassTarget at hMT
      rw [hmc]
      omega
  calc law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ PhaseOneDrained (trace init ω (s + (N1 + T + N3)))}
      ≤ _ := measure_mono hcover
    _ ≤ _ := measure_union_le _ _
    _ ≤ (law init _ + law init _) + (law init _ + law init _) :=
        add_le_add (measure_union_le _ _) (measure_union_le _ _)
    _ ≤ (ClockCounterDepthCover.counterDepthTail n (N1 + T + N3) R θ * PA +
          (1 - ENNReal.ofReal (1 / 4000 : ℝ) / 2) ^ N1 *
            ((2 ^ (2 * n) : ℕ) : ℝ≥0∞) * PA) +
        ((1 - partnerRate n ((229 * n + 999) / 1000)) ^ T * ((n / 100 : ℕ) : ℝ≥0∞) * PA +
          (1 - ENNReal.ofReal (1 / 400000 : ℝ) / 2) ^ N3 * ((2 ^ n : ℕ) : ℝ≥0∞) * PA) :=
        add_le_add (add_le_add hC hE1)
          (add_le_add (hE2.trans (mul_le_mul_left' hPA1 _))
            (hE3.trans (mul_le_mul_left' hPA2 _)))
    _ = stageBudget n R θ * PA := by
        simp only [stageBudget, ← hN1, ← hT, ← hN3]
        ring

/-! ## The producer -/

theorem weakHorizon_eq (n : ℕ) :
    weakHorizon n = 16000 * n + farTime n + 800000 * n := by
  unfold weakHorizon farTime
  omega

/-- PHASE02 (28): the stage budget at the literal deadline is at most `1 / n ^ 2`. -/
theorem stageBudget_le {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    stageBudget n (30 * PhaseThreeModel.Numeric.clockHours n) (Real.log (3 / 2 : ℝ)) ≤
      1 / (n : ℝ≥0∞) ^ 2 := by
  have h40 : 40 ≤ n := (time_population_bounds hn).2
  have ha : 0 ≤ Real.rpow (n : ℝ) (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hb : 0 ≤ Real.exp (-(n : ℝ) / 2) := (Real.exp_pos _).le
  have hc : 0 ≤ (1 / 100 : ℝ) * Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ)) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hd : 0 ≤ Real.exp (-(n : ℝ) / 4) := (Real.exp_pos _).le
  have hnpos : (0 : ℝ) < n := by
    have : (40 : ℝ) ≤ n := by exact_mod_cast h40
    linarith
  calc stageBudget n (30 * PhaseThreeModel.Numeric.clockHours n) (Real.log (3 / 2 : ℝ))
      ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(5 / 2 : ℝ))) +
          ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)) +
          ENNReal.ofReal ((1 / 100 : ℝ) * Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ))) +
          ENNReal.ofReal (Real.exp (-(n : ℝ) / 4)) := by
        unfold stageBudget
        rw [← weakHorizon_eq]
        exact add_le_add (add_le_add (add_le_add (residual_counterDepthTail_le hn)
          preliminary_scalar) (far_scalar (by omega) (n / 100) (by omega))) mass_scalar
    _ = ENNReal.ofReal (Real.rpow (n : ℝ) (-(5 / 2 : ℝ)) + Real.exp (-(n : ℝ) / 2) +
          (1 / 100 : ℝ) * Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ)) +
          Real.exp (-(n : ℝ) / 4)) := by
        rw [ENNReal.ofReal_add (by positivity) hd, ENNReal.ofReal_add (by positivity) hc,
          ENNReal.ofReal_add ha hb]
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        linarith [drain_error_budget_of_population hn]
    _ = 1 / (n : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-- The Phase-1 drain producer of DOTY-LEAN-PLAN N11b: at a pair-log stopping time,
an observed drain entry is followed by a drained configuration within the literal
three-stage deadline, except with probability at most `1 / n ^ 2`. -/
theorem phaseOneDrain_conditional_producer
    {n : ℕ} (init : InputCfg n)
    (hinit : ThresholdEpidemic.GoodInput n init)
    (σ : InputLog n → WithTop ℕ)
    (hσ : PairLogPastTime σ) :
    law init (phaseOneDrainFailure init n (initialGap init) σ) ≤
      1 / (n : ℝ≥0∞) ^ 2 := by
  obtain ⟨hn, -, -⟩ := hinit
  have h40 : 40 ≤ n := (time_population_bounds hn).2
  set g := initialGap init with hg
  set d := g.natAbs with hd
  set M := max ((99 * n + 199) / 200) (40 * d) with hM
  set R := 30 * PhaseThreeModel.Numeric.clockHours n with hR
  set θ := Real.log (3 / 2 : ℝ) with hθ
  have hθ0 : 0 ≤ θ := Real.log_nonneg (by norm_num)
  have hM99 : 99 * n ≤ 200 * M := by omega
  have hM40 : 40 * d ≤ M := le_max_right _ _
  refine (genuine_seed_splice (law init) σ (phaseOneDrainFailure init n g σ)
    (stageBudget n R θ) (phaseOneDrainFailure_measurable init n g σ hσ)
    (fun s => (pairLogFiltration _ _).le s _ (hσ s))
    (fun ω hω => phaseOneDrainFailure_finite init n g σ hω) (fun s => ?_)).trans
      (stageBudget_le hn)
  have hσs := hσ s
  rw [pairLogFiltration_eq_comap] at hσs
  obtain ⟨Aσ, -, hAσ⟩ := hσs
  set A : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {p | p ∈ Aσ ∧ PhaseOneDrainEntry n g (prefixCfg init s p)} with hA
  have hAgood : ∀ p ∈ A, Phase1ClockDepthStopped.Good n d M (prefixCfg init s p) ∧
      (∀ a ∈ prefixCfg init s p, a.role = Role.clock → R ≤ a.counter.val) ∧
      Phase1FarPhi.NonMainNeutral (prefixCfg init s p) := by
    intro p hp
    have hentry := hp.2
    have hgood := hentry.clock_depth_good
    obtain ⟨_, _, h99, _, _, _, hcounter, hneut, _, h40g⟩ := hentry
    have hMle : M ≤ RoleSplitConcentration.mainCount (prefixCfg init s p) :=
      max_le (by omega) h40g
    refine ⟨⟨⟨hgood.1.1, hgood.1.2.1, hMle⟩, hgood.2⟩, ?_, hneut⟩
    intro a ha hc
    simpa only [hR, PhaseThreeModel.Numeric.clockHours] using hcounter a ha hc
  have hcomp := stage_composition init (by omega : 2 ≤ n) d M R θ hθ0 hM99 hM40
    (fun c hc hn' dr => Phase1Persistence.nonMainNeutral_applyDraw_of_phase1Win n c hc hn' dr)
    s A hAgood
  have hmemσ : ∀ ω, frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ Aσ ↔
      σ ω = (s : WithTop ℕ) := by
    intro ω
    change ω ∈ frestrictLe (π := fun _ : ℕ => Draw _ _) s ⁻¹' Aσ ↔ ω ∈ {ω | σ ω = (s : WithTop ℕ)}
    rw [hAσ]
  calc law init (phaseOneDrainFailure init n g σ ∩ {ω | σ ω = (s : WithTop ℕ)})
      ≤ law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A ∧
          ¬ PhaseOneDrained (trace init ω (s + (16000 * n + farTime n + 800000 * n)))} := by
        apply measure_mono
        rintro ω ⟨⟨s', hs', hentry, hbad⟩, hs⟩
        have hss : s' = s := WithTop.coe_injective (hs'.symm.trans hs)
        subst hss
        refine ⟨⟨(hmemσ ω).mpr hs, hentry⟩, ?_⟩
        rw [← weakHorizon_eq]
        exact hbad (weakHorizon n) le_rfl
    _ ≤ stageBudget n R θ *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A} := hcomp
    _ ≤ stageBudget n R θ * law init {ω | σ ω = (s : WithTop ℕ)} :=
        mul_le_mul_left' (measure_mono fun ω hω => (hmemσ ω).mp hω.1) _

end Ripple.PopulationProtocol.ExactMajority.PhaseOneDrainProducer

end
