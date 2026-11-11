import Ripple.sCRNUniversality.ClockedCTM.UnboundedOccupation
import Ripple.sCRNUniversality.ClockedCTM.UnboundedTime
import Ripple.sCRNUniversality.ClockedCTM.Theorem
import Ripple.sCRNUniversality.Stochastic.MassAction.Lyapunov

/-!
# Work-duration, restart, and terminal-clock layer for SCWB T41

The buffer work bounds, prefix continuation, window entry decomposition,
schedule parameters, and scalar terminal identities are proved below.
RawStateRestart, the remaining phase estimates, actual terminal occupation,
the quantitative volume bound, and qualitative tail finiteness are explicit
inputs of the reducers here; `UnboundedMarkov` and `UnboundedClockOccupation`
prove them.
-/

noncomputable section

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-- Continuation under the actual law at a deterministic prefix cut. -/
theorem rawLaw_prefix_continuation
    (hPos : N.hasPositiveRates) (z₀ : State S) (n : ℕ)
    (A : Set ((i : Finset.Iic n) → Option N.I))
    (B : Set (ℕ → Option N.I)) (hB : MeasurableSet B) :
    rawLaw N hPos z₀ ({ω | frestrictLe n ω ∈ A} ∩ B) =
      ∫⁻ p in A,
        Kernel.traj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z₀ k) n p B
        ∂Kernel.partialTraj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z₀ k) 0 n
          (fun _ => none) := by
  have h := congrArg
    (fun ν : Measure (((i : Finset.Iic n) → Option N.I) ×
        (ℕ → Option N.I)) => ν (A ×ˢ B))
    (Kernel.partialTraj_compProd_traj (X := fun _ => Option N.I)
      (κ := fun k => stepKernel N hPos z₀ k) (Nat.zero_le n)
      (fun _ => none))
  dsimp only at h
  rw [Measure.compProd_apply_prod (measurableSet_prefixSet N n A) hB,
    Measure.map_apply (by fun_prop)
      ((measurableSet_prefixSet N n A).prod hB)] at h
  exact h.symm

theorem rawLaw_prefix_continuation_le
    (hPos : N.hasPositiveRates) (z₀ : State S) (n : ℕ)
    (A : Set ((i : Finset.Iic n) → Option N.I))
    (B : Set (ℕ → Option N.I)) (hB : MeasurableSet B)
    (ε : ℝ≥0∞)
    (hbound : ∀ p ∈ A,
      Kernel.traj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z₀ k) n p B ≤ ε) :
    rawLaw N hPos z₀ ({ω | frestrictLe n ω ∈ A} ∩ B) ≤
      ε * rawLaw N hPos z₀ {ω | frestrictLe n ω ∈ A} := by
  rw [rawLaw_prefix_continuation N hPos z₀ n A B hB]
  calc
    _ ≤ ∫⁻ _p in A, ε
        ∂Kernel.partialTraj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z₀ k) 0 n
          (fun _ => none) :=
      setLIntegral_mono' (measurableSet_prefixSet N n A) hbound
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ,
        rawLaw_prefix_eq N hPos z₀ n A]

/-- Finite slices of a stopping index; no assertion of almost-sure finiteness
is needed for this identity. -/
theorem rawLaw_stopped_prefix_formula
    (hPos : N.hasPositiveRates) (z₀ : State S)
    (A : (n : ℕ) → Set ((i : Finset.Iic n) → Option N.I))
    (B : ℕ → Set (ℕ → Option N.I))
    (hB : ∀ n, MeasurableSet (B n))
    (hdisjoint : Pairwise (Function.onFun Disjoint
      (fun n => {ω : ℕ → Option N.I | frestrictLe n ω ∈ A n}))) :
    rawLaw N hPos z₀
        (⋃ n, {ω | frestrictLe n ω ∈ A n} ∩ B n) =
      ∑' n, ∫⁻ p in A n,
        Kernel.traj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z₀ k) n p (B n)
        ∂Kernel.partialTraj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z₀ k) 0 n
          (fun _ => none) := by
  rw [measure_iUnion
    (fun i j hij => (hdisjoint hij).mono
      Set.inter_subset_left Set.inter_subset_left)
    (fun n => ((measurable_frestrictLe n)
      (measurableSet_prefixSet N n (A n))).inter (hB n))]
  exact tsum_congr fun n =>
    rawLaw_prefix_continuation N hPos z₀ n (A n) (B n) (hB n)

/-- A uniform estimate for the actual continuation kernels passes through
disjoint random-entry slices. Fresh-state identification is a separate task. -/
theorem rawLaw_stopped_prefix_le
    (hPos : N.hasPositiveRates) (z₀ : State S)
    (A : (n : ℕ) → Set ((i : Finset.Iic n) → Option N.I))
    (B : ℕ → Set (ℕ → Option N.I))
    (hB : ∀ n, MeasurableSet (B n))
    (hdisjoint : Pairwise (Function.onFun Disjoint
      (fun n => {ω : ℕ → Option N.I | frestrictLe n ω ∈ A n})))
    (ε : ℝ≥0∞)
    (hbound : ∀ n p, p ∈ A n →
      Kernel.traj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z₀ k) n p (B n) ≤ ε) :
    rawLaw N hPos z₀
        (⋃ n, {ω | frestrictLe n ω ∈ A n} ∩ B n) ≤ ε := by
  letI := rawLaw_isProbabilityMeasure N hPos z₀
  calc
    _ ≤ ∑' n, rawLaw N hPos z₀
        ({ω | frestrictLe n ω ∈ A n} ∩ B n) := measure_iUnion_le _
    _ ≤ ∑' n, ε * rawLaw N hPos z₀
        {ω | frestrictLe n ω ∈ A n} :=
      ENNReal.tsum_le_tsum fun n =>
        rawLaw_prefix_continuation_le N hPos z₀ n (A n) (B n)
          (hB n) ε (hbound n)
    _ = ε * rawLaw N hPos z₀
        (⋃ n, {ω | frestrictLe n ω ∈ A n}) := by
      rw [ENNReal.tsum_mul_left, measure_iUnion hdisjoint
        (fun n => (measurable_frestrictLe n)
          (measurableSet_prefixSet N n (A n)))]
    _ ≤ ε * 1 := mul_le_mul_left' prob_le_one ε
    _ = ε := mul_one ε

/-- Coordinate zero is unused and is reset at a restart. -/
def restartLabels (cut : ℕ) (ω : ℕ → Option N.I) : ℕ → Option N.I
  | 0 => none
  | j + 1 => ω (cut + j + 1)

theorem measurable_restartLabels (cut : ℕ) :
    Measurable (restartLabels N cut) := by
  apply measurable_pi_lambda
  intro j
  cases j with
  | zero => exact measurable_const
  | succ j => exact measurable_pi_apply (cut + j + 1)

theorem pathState_restartLabels (z₀ : State S) (ω : ℕ → Option N.I)
    (cut j : ℕ) :
    pathState N (pathState N z₀ ω cut) (restartLabels N cut ω) j =
      pathState N z₀ ω (cut + j) := by
  induction j with
  | zero => simp only [pathState, Nat.add_zero]
  | succ j ih =>
      change
        stateStep N
            (pathState N (pathState N z₀ ω cut) (restartLabels N cut ω) j)
            (ω (cut + j + 1)) =
          stateStep N (pathState N z₀ ω (cut + j))
            (ω (cut + j + 1))
      rw [ih]

theorem pathFired_restartLabels (z₀ : State S) (ω : ℕ → Option N.I)
    (cut j : ℕ) :
    pathFired N (pathState N z₀ ω cut) (restartLabels N cut ω) j =
      pathFired N z₀ ω (cut + j) := by
  unfold pathFired
  rw [pathState_restartLabels]
  rfl

/-- The fresh-state identity remains the explicit hRestart premise. -/
theorem rawLaw_stopped_prefix_le_of_restart
    (hPos : N.hasPositiveRates) (z₀ : State S)
    (A : (n : ℕ) → Set ((i : Finset.Iic n) → Option N.I))
    (start : ℕ → State S) (E : ℕ → Set (ℕ → Option N.I))
    (hE : ∀ n, MeasurableSet (E n))
    (hdisjoint : Pairwise (Function.onFun Disjoint
      (fun n => {ω : ℕ → Option N.I | frestrictLe n ω ∈ A n})))
    (hRestart : ∀ n p, p ∈ A n →
      (Kernel.traj (X := fun _ => Option N.I)
        (fun k => stepKernel N hPos z₀ k) n p).map
          (restartLabels N n) = rawLaw N hPos (start n))
    (ε : ℝ≥0∞)
    (hFresh : ∀ n, rawLaw N hPos (start n) (E n) ≤ ε) :
    rawLaw N hPos z₀
        (⋃ n, {ω | frestrictLe n ω ∈ A n} ∩
          (restartLabels N n) ⁻¹' E n) ≤ ε := by
  apply rawLaw_stopped_prefix_le N hPos z₀ A
    (fun n => (restartLabels N n) ⁻¹' E n)
    (fun n => (hE n).preimage (measurable_restartLabels N n))
    hdisjoint ε
  intro n p hp
  rw [← Measure.map_apply (measurable_restartLabels N n) (hE n),
    hRestart n p hp]
  exact hFresh n

end Ripple.sCRNUniversality.Stochastic.MassAction

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction MeasureTheory ProbabilityTheory Classical
open Ripple.sCRNUniversality.Stochastic.ClockOccupation
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace StandaloneWork

/-- A samplewise decrease bounds the reward on every sanitized work path. -/
theorem duration_le_of_step_potential (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    (V : State (Sp C) → ℝ≥0∞)
    (hdrop : ∀ x y, P.inv x → WorkStep C x y →
      holdingMean C x + V y ≤ V x)
    (ω : ℕ → Option (workNet C).I) :
    duration C start ω ≤ V start := by
  have hstep : ∀ n,
      holdingMean C (pathState (workNet C) start ω n) +
          V (pathState (workNet C) start ω (n + 1)) ≤
        V (pathState (workNet C) start ω n) := by
    intro n
    have hi := path_invariant C P ω n
    by_cases ht : WorkTerminal C (pathState (workNet C) start ω n)
    · change holdingMean C (pathState (workNet C) start ω n) +
        V (stateStep (workNet C) (pathState (workNet C) start ω n)
          (ω (n + 1))) ≤ _
      rw [stateStep_of_terminal C _ _ ht]
      simp [holdingMean, ht]
    · exact hdrop _ _ hi (stateStep_is_workStep C _ _ ht)
  have hpartial : ∀ n,
      (∑ j ∈ Finset.range n,
        holdingMean C (pathState (workNet C) start ω j)) +
          V (pathState (workNet C) start ω n) ≤ V start := by
    intro n
    induction n with
    | zero => simp [pathState]
    | succ n ih =>
        rw [Finset.sum_range_succ, add_assoc]
        exact (add_le_add le_rfl (hstep n)).trans ih
  unfold duration
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  exact (show (∑ j ∈ Finset.range n,
      holdingMean C (pathState (workNet C) start ω j)) ≤
      (∑ j ∈ Finset.range n,
        holdingMean C (pathState (workNet C) start ω j)) +
          V (pathState (workNet C) start ω n) from le_self_add).trans (hpartial n)

theorem meanDuration_le_of_step_potential (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    (V : State (Sp C) → ℝ≥0∞)
    (hdrop : ∀ x y, P.inv x → WorkStep C x y →
      holdingMean C x + V y ≤ V x) :
    meanDuration C start ≤ V start := by
  letI : IsProbabilityMeasure
      (rawLaw (workNet C) (workNet_hasPositiveRates C) start) :=
    rawLaw_isProbabilityMeasure _ _ _
  calc
    meanDuration C start ≤
        ∫⁻ _ω : ℕ → Option (workNet C).I, V start
          ∂rawLaw (workNet C) (workNet_hasPositiveRates C) start :=
      lintegral_mono (duration_le_of_step_potential C P V hdrop)
    _ = V start := by simp

theorem holdingMean_le_reaction_reciprocal (C : XCTM Q)
    (x : State (Sp C)) (r : Rx C) (hr : isClock r = false)
    (he : (rxn C r).enabled x) :
    holdingMean C x ≤ ENNReal.ofReal (1 / (rate C r x : ℝ)) := by
  classical
  have ht : ¬ WorkTerminal C x := fun h => h r hr he
  have hpos : 0 < rate C r x :=
    Nat.pos_of_ne_zero ((enabled_iff C r x).mp he)
  have hle : rate C r x ≤ totalWorkRate C x :=
    Finset.single_le_sum
      (f := fun i : {r : Rx C // isClock r = false} => rate C i.val x)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨r, hr⟩ : {r : Rx C // isClock r = false}))
  have hcast : (rate C r x : ℝ≥0∞) ≤ (totalWorkRate C x : ℝ≥0∞) := by
    exact_mod_cast hle
  have hreal : (0 : ℝ) < rate C r x := by exact_mod_cast hpos
  rw [holdingMean, if_neg ht, one_div, ENNReal.ofReal_inv_of_pos hreal,
    ENNReal.ofReal_natCast]
  exact ENNReal.inv_le_inv.mpr hcast

/-- The W1/W3 transition potential on the unbounded network. -/
noncomputable def bufferPotential (C : XCTM Q) (b : Buffer C)
    (x : State (Sp C)) : ℝ :=
  (if x .signal = 1 then 1 / (Buffer.count C b : ℝ) else 0) +
    aut (Buffer.count C b) (max (x (Buffer.new C b)) 1)

theorem bufferPotential_nonneg (C : XCTM Q) (b : Buffer C)
    (x : State (Sp C)) : 0 ≤ bufferPotential C b x := by
  unfold bufferPotential
  exact add_nonneg (by split_ifs <;> positivity) (aut_nonneg _ _)

private theorem buffer_seed_observables (C : XCTM Q)
    (b : Buffer C) (x : State (Sp C)) :
    rate C (Buffer.seed C b) x = x .signal * x (Buffer.old C b) ∧
      (rxn C (Buffer.seed C b)).fire x .signal = x .signal - 1 ∧
      (rxn C (Buffer.seed C b)).fire x (Buffer.new C b) =
        x (Buffer.new C b) + 1 := by
  cases b <;>
    simp [Buffer.seed, Buffer.old, Buffer.new, rate, fire_apply,
      sourceLeft, sourceRight, products, unit]

private theorem buffer_grow_observables (C : XCTM Q)
    (b : Buffer C) (x : State (Sp C)) :
    rate C (Buffer.grow C b) x =
        x (Buffer.old C b) * x (Buffer.new C b) ∧
      (rxn C (Buffer.grow C b)).fire x .signal = x .signal ∧
      (rxn C (Buffer.grow C b)).fire x (Buffer.new C b) =
        x (Buffer.new C b) - 1 + 2 := by
  cases b <;>
    simp [Buffer.grow, Buffer.old, Buffer.new, rate, fire_apply,
      sourceLeft, sourceRight, products, unit, Pi.smul_apply]

private theorem buffer_seed_potential (C : XCTM Q) (b : Buffer C)
    (x : State (Sp C)) (hx : BufferWindow C b x)
    (he : (rxn C (Buffer.seed C b)).enabled x) :
    bufferPotential C b x =
      1 / (rate C (Buffer.seed C b) x : ℝ) +
        bufferPotential C b ((rxn C (Buffer.seed C b)).fire x) := by
  have ho := buffer_seed_observables C b x
  have hrate := (enabled_iff C (Buffer.seed C b) x).mp he
  rw [ho.1] at hrate
  have hp := (mul_ne_zero_iff.mp hrate).1
  rcases hx with ⟨hcontrol, hcount, hsignal, hprogress, hexclusive, hpassive⟩
  have hs : x .signal = 1 := by omega
  have hn : x (Buffer.new C b) = 0 := by omega
  have hold : x (Buffer.old C b) = Buffer.count C b := by omega
  have hs' : (rxn C (Buffer.seed C b)).fire x .signal = 0 := by
    rw [ho.2.1, hs]
  have hn' : (rxn C (Buffer.seed C b)).fire x (Buffer.new C b) = 1 := by
    rw [ho.2.2, hn]
  unfold bufferPotential
  rw [hs', hn', ho.1, hs, hn, hold]
  norm_num

private theorem buffer_grow_potential (C : XCTM Q) (b : Buffer C)
    (x : State (Sp C)) (hx : BufferWindow C b x)
    (he : (rxn C (Buffer.grow C b)).enabled x) :
    bufferPotential C b x =
      1 / (rate C (Buffer.grow C b) x : ℝ) +
        bufferPotential C b ((rxn C (Buffer.grow C b)).fire x) := by
  have ho := buffer_grow_observables C b x
  have hrate := (enabled_iff C (Buffer.grow C b) x).mp he
  rw [ho.1] at hrate
  have hp := mul_ne_zero_iff.mp hrate
  rcases hx with ⟨hcontrol, hcount, hsignal, hprogress, hexclusive, hpassive⟩
  have holdpos : 0 < x (Buffer.old C b) := Nat.pos_of_ne_zero hp.1
  have hnpos : 0 < x (Buffer.new C b) := Nat.pos_of_ne_zero hp.2
  have hs : x .signal = 0 := by omega
  have hn : 1 ≤ x (Buffer.new C b) := by omega
  have hlt : x (Buffer.new C b) < Buffer.count C b := by omega
  have hold : x (Buffer.old C b) =
      Buffer.count C b - x (Buffer.new C b) := by omega
  have hs' : (rxn C (Buffer.grow C b)).fire x .signal = 0 := by
    rw [ho.2.1, hs]
  have hn' : (rxn C (Buffer.grow C b)).fire x (Buffer.new C b) =
      x (Buffer.new C b) + 1 := by
    rw [ho.2.2]
    omega
  have hr : (rate C (Buffer.grow C b) x : ℝ) =
      (x (Buffer.new C b) : ℝ) *
        ((Buffer.count C b : ℝ) - x (Buffer.new C b)) := by
    rw [ho.1, Nat.cast_mul, hold, Nat.cast_sub hlt.le]
    ring
  unfold bufferPotential
  rw [hs', hn', hs, hr]
  simpa [max_eq_left hn,
    max_eq_left (show 1 ≤ x (Buffer.new C b) + 1 by omega)]
    using (aut_eq_add hlt)

theorem bufferPotential_step (C : XCTM Q) (b : Buffer C)
    (x y : State (Sp C)) (hx : BufferWindow C b x) (hstep : WorkStep C x y) :
    holdingMean C x + ENNReal.ofReal (bufferPotential C b y) ≤
      ENNReal.ofReal (bufferPotential C b x) := by
  rcases hstep with ⟨r, hr, he, rfl⟩
  have hdrop : bufferPotential C b x =
      1 / (rate C r x : ℝ) +
        bufferPotential C b ((rxn C r).fire x) := by
    rcases buffer_enabled C hx hr he with h | h
    · subst r
      exact buffer_seed_potential C b x hx he
    · subst r
      exact buffer_grow_potential C b x hx he
  calc
    holdingMean C x + ENNReal.ofReal (bufferPotential C b ((rxn C r).fire x))
        ≤ ENNReal.ofReal (1 / (rate C r x : ℝ)) +
          ENNReal.ofReal (bufferPotential C b ((rxn C r).fire x)) :=
      add_le_add (holdingMean_le_reaction_reciprocal C x r hr he) le_rfl
    _ = ENNReal.ofReal
        (1 / (rate C r x : ℝ) + bufferPotential C b ((rxn C r).fire x)) :=
      (ENNReal.ofReal_add (by positivity) (bufferPotential_nonneg C b _)).symm
    _ = ENNReal.ofReal (bufferPotential C b x) := congrArg ENNReal.ofReal hdrop.symm

theorem bufferPotential_initial (C : XCTM Q) (b : Buffer C) :
    bufferPotential C b (Plan.workState C (Buffer.before C b) + unit .signal) =
      1 / (Buffer.count C b : ℝ) + aut (Buffer.count C b) 1 := by
  cases b <;>
    simp [bufferPotential, Buffer.new, Buffer.before, Buffer.count, Plan.tape,
      Plan.workState, payload, unit]

/-- §13 W1/W3, including the transition into a halting control. -/
theorem buffer_meanDuration_le_aut (C : XCTM Q) (b : Buffer C) :
    meanDuration C (Plan.workState C (Buffer.before C b) + unit .signal) ≤
      ENNReal.ofReal
        (1 / (Buffer.count C b : ℝ) + aut (Buffer.count C b) 1) := by
  have h := meanDuration_le_of_step_potential C (bufferCertificate C b)
    (fun x => ENNReal.ofReal (bufferPotential C b x))
    (bufferPotential_step C b)
  simpa only [bufferPotential_initial] using h

theorem buffer_meanDuration_le_log (C : XCTM Q) (b : Buffer C) :
    meanDuration C (Plan.workState C (Buffer.before C b) + unit .signal) ≤
      ENNReal.ofReal
        ((1 + 2 * (1 + Real.log (Buffer.count C b))) / (Buffer.count C b : ℝ)) := by
  have hdNat : 0 < Buffer.count C b := by
    unfold Buffer.count stateCount
    positivity
  have hd : (0 : ℝ) < Buffer.count C b := by exact_mod_cast hdNat
  have hbound :
      1 / (Buffer.count C b : ℝ) + aut (Buffer.count C b) 1 ≤
        (1 + 2 * (1 + Real.log (Buffer.count C b))) / (Buffer.count C b : ℝ) := by
    apply (le_div_iff₀ hd).mpr
    have he :
        (1 / (Buffer.count C b : ℝ) + aut (Buffer.count C b) 1) * Buffer.count C b =
          1 + (Buffer.count C b : ℝ) * aut (Buffer.count C b) 1 := by
      field_simp [hd.ne'] <;> ring
    rw [he]
    linarith [mul_aut_one_le (Buffer.count C b), hrm_le_log (Buffer.count C b)]
  exact (buffer_meanDuration_le_aut C b).trans (ENNReal.ofReal_le_ofReal hbound)

noncomputable def workDurationDetailedBound (s a : ℕ) : ℝ :=
  ((1039 / 100 : ℝ) * (1 + Real.log (stateCount s)) +
    (1445 / 100 : ℝ) + Real.log ((a : ℝ) + 2)) / (stateCount s : ℝ)

noncomputable def workDurationBound (s a : ℕ) : ℝ :=
  16 * ((s : ℝ) + Real.log ((a : ℝ) + 2)) / (stateCount s : ℝ)

theorem buffer_meanDuration_le_detailed (C : XCTM Q) (b : Buffer C) (a : ℕ) :
    meanDuration C (Plan.workState C (Buffer.before C b) + unit .signal) ≤
      ENNReal.ofReal
        (workDurationDetailedBound (Buffer.before C b).tape.length a) := by
  have hdNat : 0 < Buffer.count C b := by
    unfold Buffer.count stateCount
    positivity
  have hd : (0 : ℝ) < Buffer.count C b := by exact_mod_cast hdNat
  have hlogd : 0 ≤ Real.log (Buffer.count C b) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hdNat)
  have hloga : 0 ≤ Real.log ((a : ℝ) + 2) :=
    Real.log_nonneg (by have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)
  refine (buffer_meanDuration_le_log C b).trans (ENNReal.ofReal_le_ofReal ?_)
  change (1 + 2 * (1 + Real.log (Buffer.count C b))) / (Buffer.count C b : ℝ) ≤
    ((1039 / 100 : ℝ) * (1 + Real.log (Buffer.count C b)) +
      (1445 / 100 : ℝ) + Real.log ((a : ℝ) + 2)) / (Buffer.count C b : ℝ)
  apply div_le_div_of_nonneg_right _ hd.le
  nlinarith

theorem buffer_meanDuration_le_workDurationBound (C : XCTM Q)
    (b : Buffer C) (a : ℕ) (hs : 3 ≤ (Buffer.before C b).tape.length) :
    meanDuration C (Plan.workState C (Buffer.before C b) + unit .signal) ≤
      ENNReal.ofReal (workDurationBound (Buffer.before C b).tape.length a) := by
  have hdNat : 0 < Buffer.count C b := by
    unfold Buffer.count stateCount
    positivity
  have hd : (0 : ℝ) < Buffer.count C b := by exact_mod_cast hdNat
  have hsreal : (3 : ℝ) ≤ (Buffer.before C b).tape.length := by exact_mod_cast hs
  have hloga : 0 ≤ Real.log ((a : ℝ) + 2) :=
    Real.log_nonneg (by have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)
  have hlogd : Real.log (Buffer.count C b) ≤
      2 * ((Buffer.before C b).tape.length : ℝ) := by
    rw [show (Buffer.count C b : ℝ) =
        (3 : ℝ) ^ ((Buffer.before C b).tape.length - 1) by
      simp only [Buffer.count, stateCount, Nat.cast_pow, Nat.cast_ofNat],
      Real.log_pow]
    have hsub : (((Buffer.before C b).tape.length - 1 : ℕ) : ℝ) ≤
        ((Buffer.before C b).tape.length : ℝ) := by
      exact_mod_cast Nat.sub_le (Buffer.before C b).tape.length 1
    have hnonneg : (0 : ℝ) ≤
        (((Buffer.before C b).tape.length - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlogthree : Real.log (3 : ℝ) ≤ 2 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
    nlinarith
  refine (buffer_meanDuration_le_log C b).trans (ENNReal.ofReal_le_ofReal ?_)
  change (1 + 2 * (1 + Real.log (Buffer.count C b))) / (Buffer.count C b : ℝ) ≤
    (16 * (((Buffer.before C b).tape.length : ℝ) + Real.log ((a : ℝ) + 2))) /
      (Buffer.count C b : ℝ)
  apply div_le_div_of_nonneg_right _ hd.le
  nlinarith

theorem initial_meanDuration_eq_zero (C : XCTM Q) (i : ℕ) (w : List Bool) :
    meanDuration C (workView C (initial C i w)) = 0 :=
  meanDuration_eq_zero_of_terminal C _
    ((workTerminal_view C _).mpr (initial_terminal C i w))

theorem halted_next_meanDuration_eq_zero (C : XCTM Q) (p : Plan C)
    (hh : Plan.halted C p = true) :
    meanDuration C (Plan.workState C p + unit .signal) = 0 := by
  apply meanDuration_eq_zero_of_terminal C
  cases p with
  | first q w a latent =>
      have hm : C.mode q = .halt := by
        cases he : C.mode q <;> simp_all [Plan.halted]
      simpa only [one_smul] using
        (halted_payload_terminal C q w a latent 1 hm)
  | _ => simp [Plan.halted] at hh

/-- Expected drift, specialized to the defined work reward. -/
theorem meanDuration_le_of_drift (C : XCTM Q) (start : State (Sp C))
    (V : State (Sp C) → ℝ≥0∞)
    (hdrift : ∀ x,
      holdingMean C x +
        ∑ o, massActionPMF (workNet C) (workNet_hasPositiveRates C) x o *
          V (stateStep (workNet C) x o) ≤ V x) :
    meanDuration C start ≤ V start := by
  have h := lintegral_tsum_cost_le (workNet C) (workNet_hasPositiveRates C) start
    (fun (_ : Unit) (_ : State (Sp C)) (_ : Option (workNet C).I) => ())
    () (fun y => V y.2) (fun y => holdingMean C y.2)
    (fun y => hdrift y.2)
  have hprefix (n : ℕ) (ω : ℕ → Option (workNet C).I) :
      prefixToState (workNet C) start n (Preorder.frestrictLe n ω) =
        pathState (workNet C) start ω n :=
    prefixToState_eq_pathState (workNet C) start ω n
  simpa only [meanDuration, duration, extState_snd, hprefix] using h

theorem certificate_stateStep_invariant (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    {x : State (Sp C)} (hx : P.inv x) (o : Option (workNet C).I) :
    P.inv (stateStep (workNet C) x o) := by
  by_cases ht : WorkTerminal C x
  · rw [stateStep_of_terminal C x o ht]
    exact hx
  · exact P.closed _ _ hx (stateStep_is_workStep C x o ht)

theorem meanDuration_le_of_certificate_drift (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    (V : State (Sp C) → ℝ≥0∞)
    (hdrift : ∀ x, P.inv x →
      holdingMean C x +
        ∑ o, massActionPMF (workNet C) (workNet_hasPositiveRates C) x o *
          V (stateStep (workNet C) x o) ≤ V x) :
    meanDuration C start ≤ V start := by
  classical
  let W : State (Sp C) → ℝ≥0∞ := fun x => if P.inv x then V x else ∞
  have hglobal : ∀ x,
      holdingMean C x +
        ∑ o, massActionPMF (workNet C) (workNet_hasPositiveRates C) x o *
          W (stateStep (workNet C) x o) ≤ W x := by
    intro x
    by_cases hx : P.inv x
    · have hsum :
          (∑ o, massActionPMF (workNet C) (workNet_hasPositiveRates C) x o *
            W (stateStep (workNet C) x o)) =
          ∑ o, massActionPMF (workNet C) (workNet_hasPositiveRates C) x o *
            V (stateStep (workNet C) x o) := by
        apply Finset.sum_congr rfl
        intro o _
        simp only [W, if_pos (certificate_stateStep_invariant C P hx o)]
      rw [hsum]
      simpa only [W, if_pos hx] using hdrift x hx
    · simp only [W, if_neg hx, le_top]
  have h := meanDuration_le_of_drift C start W hglobal
  simpa only [W, if_pos P.initial] using h

/-- The local inequalities remain explicit for the W2/W4r/W4e phases. -/
theorem next_window_meanDuration_le_of_work_drift (C : XCTM Q)
    (p : Plan C) (hs : 3 ≤ p.tape.length) (hh : Plan.halted C p = false)
    (a : ℕ) (V : State (Sp C) → ℝ≥0∞)
    (hLemmaEightFour_drift : ∀ x, (planCertificate C p hs hh).inv x →
      holdingMean C x +
        ∑ o, massActionPMF (workNet C) (workNet_hasPositiveRates C) x o *
          V (stateStep (workNet C) x o) ≤ V x)
    (hLemmaEightFour_initial :
      V (Plan.workState C p + unit .signal) ≤
        ENNReal.ofReal (workDurationBound p.tape.length a)) :
    meanDuration C (WindowAnalysis.nextWindowWork C p).val ≤
      ENNReal.ofReal (workDurationBound p.tape.length a) :=
  (meanDuration_le_of_certificate_drift C (planCertificate C p hs hh)
    V hLemmaEightFour_drift).trans hLemmaEightFour_initial

end StandaloneWork

namespace WindowAnalysis

theorem plan_add (C : XCTM Q) (i : ℕ) (w : List Bool) (m n : ℕ) :
    plan C i w (m + n) = Plan.iterate C (plan C i w m) n :=
  Plan.iterate_add C (.first C.start w i false) m n

theorem plan_configuration_tape (C : XCTM Q) (p : Plan C) :
    (Plan.configuration C p).2 = p.tape := by
  cases p <;> rfl

theorem active_plan_run_nonhalt (C : XCTM Q) (i : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (m : ℕ) (hm : Plan.halted C (plan C i w m) = false) :
    ∀ j, 4 * j ≤ m → C.mode (C.runT (C.start, w) j).1 ≠ .halt := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj hhalt
      have hbefore : ∀ l < j, C.mode (C.runT (C.start, w) l).1 ≠ .halt :=
        fun l hl => ih l hl (by omega)
      have hp := plan_at_step C i w hs j hbefore
      have hfreeze :
          plan C i w m =
            .first (C.runT (C.start, w) j).1 (C.runT (C.start, w) j).2
              (i + j) (previousExtension C w j) := by
        rw [show m = 4 * j + (m - 4 * j) by omega, plan_add, hp]
        exact Plan.iterate_halt C _ _ _ _ hhalt _
      rw [hfreeze] at hm
      simp [Plan.halted, hhalt] at hm

theorem first_plan_offset_data (C : XCTM Q) (q : Q) (w : List Bool)
    (a : ℕ) (latent : Bool) (hh : C.mode q ≠ .halt) :
    ((Plan.iterate C (.first q w a latent) 1).tape = w ∧
      nextLowerRatio (Plan.iterate C (.first q w a latent) 1) = (a : ℝ) + 1) ∧
    ((Plan.iterate C (.first q w a latent) 2).tape = w ∧
      nextLowerRatio (Plan.iterate C (.first q w a latent) 2) = (a : ℝ) + 1) ∧
    nextLowerRatio (Plan.iterate C (.first q w a latent) 3) = (a : ℝ) + 1 := by
  cases hmode : C.mode q with
  | read =>
      have hfirst :
          Plan.advance C (.first q w a latent) =
            .second (.inl ⟨q, hmode⟩) w (a + 1) := by
        dsimp only [Plan.advance]
        split <;> first
          | rfl
          | (exfalso; rename_i hm; rw [hmode] at hm; cases hm)
          | simp_all
      simp only [Plan.iterate, hfirst]
      simp [Plan.advance, Plan.tape, nextLowerRatio]
  | extend q' =>
      have hfirst :
          Plan.advance C (.first q w a latent) =
            .second (.inr ⟨q, ⟨q', hmode⟩⟩) w (a + 1) := by
        dsimp only [Plan.advance]
        split <;> first
          | rfl
          | (exfalso; rename_i hm; rw [hmode] at hm; cases hm)
          | simp_all
      simp only [Plan.iterate, hfirst]
      simp [Plan.advance, Plan.tape, nextLowerRatio]
  | halt => exact False.elim (hh hmode)

theorem next_window_schedule_parameters_of_length (C : XCTM Q)
    (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length) (hwi : w.length ≤ i)
    (n r : ℕ) (hr : r < 4) (hk : 0 < 4 * n + r)
    (hactive : Plan.halted C (plan C i w (4 * n + r - 1)) = false) :
    (plan C i w (4 * n + r - 1)).tape.length ≤ i + n ∧
      (if r = 1 then ((i : ℝ) + n) / 3 else (i : ℝ) + n) ≤
        nextLowerRatio (plan C i w (4 * n + r - 1)) := by
  have hnonhalt := active_plan_run_nonhalt C i w hs (4 * n + r - 1) hactive
  have hspace (j : ℕ) : (C.runT (C.start, w) j).2.length ≤ i + j :=
    run_space_le_accuracy C (C.start, w) i hwi j
  interval_cases r
  · have hn : 1 ≤ n := by omega
    have he : 4 * n + 0 - 1 = 4 * (n - 1) + 3 := by omega
    have hbefore : ∀ j ≤ n - 1, C.mode (C.runT (C.start, w) j).1 ≠ .halt :=
      fun j hj => hnonhalt j (by omega)
    have hp := plan_at_step C i w hs (n - 1) (fun j hj => hbefore j (by omega))
    have hdata := first_plan_offset_data C
      (C.runT (C.start, w) (n - 1)).1 (C.runT (C.start, w) (n - 1)).2
      (i + (n - 1)) (previousExtension C w (n - 1)) (hbefore (n - 1) le_rfl)
    have hconf := plan_at_tick_completion C i w hs (n - 1) hbefore
    have htape :
        (plan C i w (4 * n + 0 - 1)).tape = (C.runT (C.start, w) n).2 := by
      rw [he]
      simpa only [plan_configuration_tape, show n - 1 + 1 = n by omega]
        using congrArg Prod.snd hconf
    have hratio :
        nextLowerRatio (plan C i w (4 * n + 0 - 1)) =
          ((i + (n - 1) : ℕ) : ℝ) + 1 := by
      rw [he, plan_add, hp]
      exact hdata.2.2
    constructor
    · rw [htape]
      exact hspace n
    · change (i : ℝ) + n ≤ nextLowerRatio (plan C i w (4 * n + 0 - 1))
      rw [hratio]
      have heq : ((i + (n - 1) : ℕ) : ℝ) + 1 = (i : ℝ) + n := by
        exact_mod_cast (show i + (n - 1) + 1 = i + n by omega)
      simpa only [heq] using (le_refl ((i : ℝ) + n))
  · have he : 4 * n + 1 - 1 = 4 * n := by omega
    have hp := plan_at_step C i w hs n
      (fun j hj => hnonhalt j (by omega))
    constructor
    · rw [he, hp]
      exact hspace n
    · change ((i : ℝ) + n) / 3 ≤ nextLowerRatio (plan C i w (4 * n + 1 - 1))
      rw [he, hp]
      simp [nextLowerRatio]
  · have he : 4 * n + 2 - 1 = 4 * n + 1 := by omega
    have hp := plan_at_step C i w hs n
      (fun j hj => hnonhalt j (by omega))
    have hdata := first_plan_offset_data C
      (C.runT (C.start, w) n).1 (C.runT (C.start, w) n).2
      (i + n) (previousExtension C w n) (hnonhalt n (by omega))
    constructor
    · rw [he, plan_add, hp, hdata.1.1]
      exact hspace n
    · change (i : ℝ) + n ≤ nextLowerRatio (plan C i w (4 * n + 2 - 1))
      rw [he, plan_add, hp, hdata.1.2]
      push_cast
      linarith
  · have he : 4 * n + 3 - 1 = 4 * n + 2 := by omega
    have hp := plan_at_step C i w hs n
      (fun j hj => hnonhalt j (by omega))
    have hdata := first_plan_offset_data C
      (C.runT (C.start, w) n).1 (C.runT (C.start, w) n).2
      (i + n) (previousExtension C w n) (hnonhalt n (by omega))
    constructor
    · rw [he, plan_add, hp, hdata.2.1.1]
      exact hspace n
    · change (i : ℝ) + n ≤ nextLowerRatio (plan C i w (4 * n + 3 - 1))
      rw [he, plan_add, hp, hdata.2.1.2]
      push_cast
      linarith

theorem next_window_schedule_parameters (C : XCTM Q)
    (i : ℕ) (w : List Bool) (δ : ℝ) (hacc : AdmissibleAccuracy w i δ)
    (n r : ℕ) (hr : r < 4) (hk : 0 < 4 * n + r)
    (hactive : Plan.halted C (plan C i w (4 * n + r - 1)) = false) :
    (plan C i w (4 * n + r - 1)).tape.length ≤ i + n ∧
      (if r = 1 then ((i : ℝ) + n) / 3 else (i : ℝ) + n) ≤
        nextLowerRatio (plan C i w (4 * n + r - 1)) := by
  have hwiReal : (w.length : ℝ) ≤ (i : ℝ) :=
    (le_max_left _ _).trans hacc.2.2.2
  have hwi : w.length ≤ i := by exact_mod_cast hwiReal
  exact next_window_schedule_parameters_of_length C i w hacc.1 hwi n r hr hk hactive

/-- The W1 predecessor already carries the updated tape. -/
theorem next_window_schedule_tape (C : XCTM Q)
    (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (n r : ℕ) (hr : r < 4) (hk : 0 < 4 * n + r)
    (hactive : Plan.halted C (plan C i w (4 * n + r - 1)) = false) :
    (plan C i w (4 * n + r - 1)).tape = (C.runT (C.start, w) n).2 := by
  have hnonhalt := active_plan_run_nonhalt C i w hs (4 * n + r - 1) hactive
  interval_cases r
  · have he : 4 * n + 0 - 1 = 4 * (n - 1) + 3 := by omega
    have hbefore : ∀ j ≤ n - 1, C.mode (C.runT (C.start, w) j).1 ≠ .halt :=
      fun j hj => hnonhalt j (by omega)
    have hconf := plan_at_tick_completion C i w hs (n - 1) hbefore
    rw [he]
    simpa only [plan_configuration_tape, show n - 1 + 1 = n by omega]
      using congrArg Prod.snd hconf
  · have he : 4 * n + 1 - 1 = 4 * n := by omega
    rw [he, plan_at_step C i w hs n (fun j hj => hnonhalt j (by omega))]
    rfl
  · have he : 4 * n + 2 - 1 = 4 * n + 1 := by omega
    have hp := plan_at_step C i w hs n
      (fun j hj => hnonhalt j (by omega))
    have hdata := first_plan_offset_data C
      (C.runT (C.start, w) n).1 (C.runT (C.start, w) n).2
      (i + n) (previousExtension C w n) (hnonhalt n (by omega))
    rw [he, plan_add, hp]
    exact hdata.1.1
  · have he : 4 * n + 3 - 1 = 4 * n + 2 := by omega
    have hp := plan_at_step C i w hs n
      (fun j hj => hnonhalt j (by omega))
    have hdata := first_plan_offset_data C
      (C.runT (C.start, w) n).1 (C.runT (C.start, w) n).2
      (i + n) (previousExtension C w n) (hnonhalt n (by omega))
    rw [he, plan_add, hp]
    exact hdata.2.1.1

end WindowAnalysis

/-- The first erroneous tick has exactly k preceding ticks. -/
def firstErrorWindow (C : XCTM Q) (z₀ : State (Sp C))
    (k : ℕ) : Set (LabelPath C) :=
  {ω | ∃ j, FirstErrorAt C z₀ ω j ∧ tickCount C z₀ ω j = k}

theorem measurableSet_firstErrorWindow (C : XCTM Q)
    (z₀ : State (Sp C)) (k : ℕ) :
    MeasurableSet (firstErrorWindow C z₀ k) := by
  have heq : firstErrorWindow C z₀ k =
      ⋃ j, {ω | FirstErrorAt C z₀ ω j} ∩
        {ω | tickCount C z₀ ω j = k} := by
    ext ω
    simp [firstErrorWindow]
  rw [heq]
  exact MeasurableSet.iUnion fun j =>
    (measurableSet_firstErrorAt C z₀ j).inter
      (measurableSet_eq_fun (measurable_tickCount C z₀ j) measurable_const)

theorem firstErrorStep_eq_four_windows (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) :
    firstErrorStep C z₀ n =
      ⋃ r ∈ Finset.range 4, firstErrorWindow C z₀ (4 * n + r) := by
  ext ω
  simp only [firstErrorStep, firstErrorWindow, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj, hn⟩
    refine ⟨tickCount C z₀ ω j % 4,
      Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)), j, hj, ?_⟩
    omega
  · rintro ⟨r, hr, j, hj, hk⟩
    have hr' : r < 4 := Finset.mem_range.mp hr
    exact ⟨j, hj, by omega⟩

theorem firstErrorWindow_zero_eq_prematureTickEvent
    (C : XCTM Q) (z₀ : State (Sp C)) :
    firstErrorWindow C z₀ 0 = WindowAnalysis.prematureTickEvent C z₀ := by
  ext ω
  constructor
  · rintro ⟨j, hj, hzero⟩
    exact Set.mem_iUnion.mpr ⟨j, hzero, hj.1⟩
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    have hzero : tickCount C z₀ ω j = 0 := hj.1
    have hbad : BadTickAt C z₀ ω j := hj.2
    refine ⟨j, ⟨hbad, ?_⟩, hzero⟩
    intro m hm hbadm
    have hsucc := tickCount_succ_of_tick C z₀ ω m hbadm.1
    have hmono := tickCount_mono C z₀ ω (show m + 1 ≤ j by omega)
    change tickCount C z₀ ω (m + 1) ≤ tickCount C z₀ ω j at hmono
    omega

/-- Only the finite past is needed for the concrete window invariant. -/
theorem window_of_noBadTick_before
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (ω : LabelPath C) (j : ℕ)
    (hNo : ∀ m < j, ¬ BadTickAt C (initial C i₀ w) ω m) :
    Window C i₀ w (tickCount C (initial C i₀ w) ω j)
      (pathState (net C) (initial C i₀ w) ω j) := by
  revert hNo
  induction j with
  | zero =>
      intro _
      change workView C (initial C i₀ w) = gamma C i₀ w 0
      exact initial_workView C i₀ w
  | succ j ih =>
      intro hNo
      have hW := ih (fun m hm => hNo m (by omega))
      have hv := pathFired_valid (net C) (initial C i₀ w) ω j
      cases hF : pathFired (net C) (initial C i₀ w) ω j with
      | none =>
          simp only [hF] at hv
          have hcount : tickCount C (initial C i₀ w) ω (j + 1) =
              tickCount C (initial C i₀ w) ω j := by
            simp [tickCount, TickAt, firedTick, hF]
          rw [hcount, hv.1]
          exact hW
      | some r =>
          simp only [hF] at hv
          have he : (rxn C r).enabled
              (pathState (net C) (initial C i₀ w) ω j) := hv.1
          have hstate : pathState (net C) (initial C i₀ w) ω (j + 1) =
              (rxn C r).fire (pathState (net C) (initial C i₀ w) ω j) := hv.2
          cases ht : isTick r with
          | false =>
              have hcount : tickCount C (initial C i₀ w) ω (j + 1) =
                  tickCount C (initial C i₀ w) ω j := by
                simp [tickCount, TickAt, firedTick, hF, ht]
              rw [hcount, hstate]
              cases hc : isClock r with
              | false => exact window_work_fire C i₀ w _ _ hW r hc he
              | true =>
                  exact window_of_workView_eq C i₀ w _
                    (clock_move_workView C r _ hc ht he) hW
          | true =>
              have hTick : TickAt C (initial C i₀ w) ω j := by
                simpa only [TickAt, firedTick, hF] using ht
              have hterminal : WorkTerminal C
                  (pathState (net C) (initial C i₀ w) ω j) := by
                by_contra h
                exact hNo j (Nat.lt_succ_self j) ⟨hTick, h⟩
              have hclean := window_terminal_clean C i₀ w hs _ _ hW hterminal
              have hcount := tickCount_succ_of_tick C (initial C i₀ w) ω j hTick
              have hcases : ∃ latent : Bool, r = .tick latent := by
                cases r <;> simp_all [isTick]
              obtain ⟨latent, rfl⟩ := hcases
              rw [hcount, hstate]
              exact window_after_tick C i₀ w _ _ hclean latent he

theorem firstErrorWindow_initial_empty
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length) :
    firstErrorWindow C (initial C i₀ w) 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  obtain ⟨j, hj, hcount⟩ := hω
  have hW := window_of_noBadTick_before C i₀ w hs ω j hj.2
  rw [hcount] at hW
  have ht : WorkTerminal C (pathState (net C) (initial C i₀ w) ω j) :=
    (workTerminal_view C _).mp (by
      rw [hW]
      exact Plan.workState_terminal C (plan C i₀ w 0))
  exact hj.1.2 ht

theorem firstErrorWindow_predecessor_active
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (ω : LabelPath C) (k : ℕ)
    (hω : ω ∈ firstErrorWindow C (initial C i₀ w) (k + 1)) :
    Plan.halted C (plan C i₀ w k) = false := by
  obtain ⟨j, hj, hcount⟩ := hω
  have hW := window_of_noBadTick_before C i₀ w hs ω j hj.2
  rw [hcount] at hW
  cases hh : Plan.halted C (plan C i₀ w k) with
  | false => rfl
  | true =>
      have ht := halted_clean_terminal C (plan C i₀ w k)
        (pathState (net C) (initial C i₀ w) ω j) hh
        (by simpa [Window, hh, gamma] using hW)
      exact False.elim (hj.1.2 ht)

open WindowAnalysis

/-- Entry into window k+1 with a correct finite past. -/
def goodWindowEntry (C : XCTM Q) (z₀ : State (Sp C))
    (k : ℕ) : ℕ → Set (LabelPath C)
  | 0 => ∅
  | j + 1 => {ω | tickCount C z₀ ω j = k ∧ TickAt C z₀ ω j ∧
      ∀ m < j + 1, ¬ BadTickAt C z₀ ω m}

theorem goodWindowEntry_count (C : XCTM Q) (z₀ : State (Sp C))
    (k cut : ℕ) (ω : LabelPath C)
    (h : ω ∈ goodWindowEntry C z₀ k cut) :
    tickCount C z₀ ω cut = k + 1 := by
  cases cut with
  | zero => exact False.elim h
  | succ j =>
      exact (tickCount_succ_of_tick C z₀ ω j h.2.1).trans
        (congrArg (fun x : ℕ => x + 1) h.1)

theorem goodWindowEntry_noBad (C : XCTM Q) (z₀ : State (Sp C))
    (k cut : ℕ) (ω : LabelPath C)
    (h : ω ∈ goodWindowEntry C z₀ k cut) :
    ∀ m < cut, ¬ BadTickAt C z₀ ω m := by
  cases cut with
  | zero => exact False.elim h
  | succ j => exact h.2.2

theorem goodWindowEntry_pairwise (C : XCTM Q) (z₀ : State (Sp C))
    (k : ℕ) : Pairwise (Function.onFun Disjoint (goodWindowEntry C z₀ k)) := by
  intro cut cut' hne
  refine Set.disjoint_left.mpr ?_
  intro ω h h'
  cases cut with
  | zero => exact False.elim h
  | succ j =>
      cases cut' with
      | zero => exact False.elim h'
      | succ j' =>
          have hafter := goodWindowEntry_count C z₀ k (j + 1) ω h
          have hafter' := goodWindowEntry_count C z₀ k (j' + 1) ω h'
          rcases lt_trichotomy j j' with hj | hj | hj
          · have hm := tickCount_mono C z₀ ω (show j + 1 ≤ j' by omega)
            change tickCount C z₀ ω (j + 1) ≤ tickCount C z₀ ω j' at hm
            have hb : tickCount C z₀ ω j' = k := h'.1
            omega
          · exact hne (congrArg Nat.succ hj)
          · have hm := tickCount_mono C z₀ ω (show j' + 1 ≤ j by omega)
            change tickCount C z₀ ω (j' + 1) ≤ tickCount C z₀ ω j at hm
            have hb : tickCount C z₀ ω j = k := h.1
            omega

theorem tick_fire_eq_nextWindowStart (C : XCTM Q)
    (p : Plan C) (z : State (Sp C)) (b : Bool)
    (hwork : workView C z = Plan.workState C p)
    (hclock : clockMoleculeCount C z = 1)
    (he : (rxn C (.tick b)).enabled z) :
    (rxn C (.tick b)).fire z = clockInsert C (nextWindowWork C p) 4 := by
  have hp := (enabled_iff C (.tick b) z).mp he
  have hpos : 0 < z (.clock 0) := by
    by_contra h
    have hz : z (.clock 0) = 0 := by omega
    apply hp
    cases b <;> simp [rate, sourceLeft, sourceRight, hz]
  have hc : ∀ c : Fin 5, z (.clock c) = if c = 0 then 1 else 0 := by
    simp [clockMoleculeCount, Fin.sum_univ_succ] at hclock
    intro c
    fin_cases c <;> simp <;> omega
  have hw := tick_workView C b z he
  rw [hwork] at hw
  funext s
  have hws := congrFun hw s
  cases s with
  | clock c =>
      rw [clockInsert_clock]
      cases b <;> fin_cases c <;>
        simp [fire_apply, sourceLeft, sourceRight, products, unit, hc]
  | _ => simpa [workView, clockInsert, nextWindowWork, unit] using hws

theorem goodWindowEntry_state
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (k : ℕ) (hh : Plan.halted C (plan C i₀ w k) = false)
    (cut : ℕ) (ω : LabelPath C)
    (h : ω ∈ goodWindowEntry C (initial C i₀ w) k cut) :
    pathState (net C) (initial C i₀ w) ω cut =
      clockInsert C (nextWindowWork C (plan C i₀ w k)) 4 := by
  cases cut with
  | zero => exact False.elim h
  | succ j =>
      obtain ⟨hcount, hTick, hNo⟩ := h
      have hW := window_of_noBadTick_before C i₀ w hs ω j
        (fun m hm => hNo m (by omega))
      have ht : WorkTerminal C (pathState (net C) (initial C i₀ w) ω j) := by
        by_contra hn
        exact hNo j (Nat.lt_succ_self j) ⟨hTick, hn⟩
      have hclean := window_terminal_clean C i₀ w hs _ _ hW ht
      rw [hcount] at hclean
      have hwork : workView C (pathState (net C) (initial C i₀ w) ω j) =
          Plan.workState C (plan C i₀ w k) := by
        simpa only [Clean, hh, cleanView_false, gamma] using hclean
      have hclock : clockMoleculeCount C
          (pathState (net C) (initial C i₀ w) ω j) = 1 := by
        rw [clockMoleculeCount_path]
        simp [clockMoleculeCount, initial, Fin.sum_univ_succ]
      have hv := pathFired_valid (net C) (initial C i₀ w) ω j
      cases hF : pathFired (net C) (initial C i₀ w) ω j with
      | none => simp [TickAt, firedTick, hF] at hTick
      | some r =>
          simp only [hF] at hv
          have hrt : isTick r = true := by
            simpa only [TickAt, firedTick, hF] using hTick
          have hcases : ∃ b : Bool, r = .tick b := by
            cases r <;> simp_all [isTick]
          obtain ⟨b, rfl⟩ := hcases
          rw [hv.2]
          exact tick_fire_eq_nextWindowStart C (plan C i₀ w k) _ b hwork hclock hv.1

theorem tickCount_restartLabels_add (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (cut j : ℕ) :
    tickCount C z₀ ω (cut + j) = tickCount C z₀ ω cut +
      tickCount C (pathState (net C) z₀ ω cut)
        (restartLabels (net C) cut ω) j := by
  induction j with
  | zero => simp only [Nat.add_zero, tickCount]
  | succ j ih =>
      have ht : TickAt C (pathState (net C) z₀ ω cut)
          (restartLabels (net C) cut ω) j ↔ TickAt C z₀ ω (cut + j) := by
        unfold TickAt firedTick
        rw [pathFired_restartLabels]
      change tickCount C z₀ ω (cut + j) +
          (if TickAt C z₀ ω (cut + j) then 1 else 0) =
        tickCount C z₀ ω cut +
          (tickCount C (pathState (net C) z₀ ω cut)
            (restartLabels (net C) cut ω) j +
              (if TickAt C (pathState (net C) z₀ ω cut)
                (restartLabels (net C) cut ω) j then 1 else 0))
      rw [ih, ht, Nat.add_assoc]

theorem badTickAt_restartLabels (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (cut j : ℕ) :
    BadTickAt C (pathState (net C) z₀ ω cut)
        (restartLabels (net C) cut ω) j ↔ BadTickAt C z₀ ω (cut + j) := by
  unfold BadTickAt TickAt firedTick
  rw [pathFired_restartLabels, pathState_restartLabels]

theorem firstErrorAt_has_goodWindowEntry
    (C : XCTM Q) (z₀ : State (Sp C)) (ω : LabelPath C) (k j : ℕ)
    (hfirst : FirstErrorAt C z₀ ω j) (hcount : tickCount C z₀ ω j = k + 1) :
    ∃ cut ≤ j, ω ∈ goodWindowEntry C z₀ k cut := by
  classical
  let hex : ∃ n : ℕ, k + 1 ≤ tickCount C z₀ ω n := ⟨j, hcount.ge⟩
  let cut := Nat.find hex
  have hcut : cut ≤ j := Nat.find_min' hex hcount.ge
  have hfound : k + 1 ≤ tickCount C z₀ ω cut := Nat.find_spec hex
  have hpos : 0 < cut := by
    by_contra h
    have hz : cut = 0 := by omega
    rw [hz] at hfound
    change k + 1 ≤ 0 at hfound
    omega
  let m := cut - 1
  have hm : m + 1 = cut := by dsimp only [m]; omega
  have hbefore : ¬ k + 1 ≤ tickCount C z₀ ω m :=
    Nat.find_min hex (by dsimp only [m]; omega)
  have hstep := tickCount_succ_le C z₀ ω m
  rw [hm] at hstep
  have hmc : tickCount C z₀ ω m = k := by omega
  have hTick : TickAt C z₀ ω m := by
    by_contra h
    have hflat : tickCount C z₀ ω (m + 1) = tickCount C z₀ ω m := by
      simp only [tickCount, if_neg h, Nat.add_zero]
    rw [hm] at hflat
    omega
  refine ⟨m + 1, by omega, hmc, hTick, ?_⟩
  intro l hl
  exact hfirst.2 l (by omega)

/-- An observed first error supplies its finite entry; progress is not needed. -/
theorem firstErrorWindow_eq_entry_restart
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (k : ℕ) (hh : Plan.halted C (plan C i₀ w k) = false) :
    firstErrorWindow C (initial C i₀ w) (k + 1) =
      ⋃ cut, goodWindowEntry C (initial C i₀ w) k cut ∩
        (restartLabels (net C) cut) ⁻¹'
          prematureTickEvent C
            (clockInsert C (nextWindowWork C (plan C i₀ w k)) 4) := by
  let z₀ := initial C i₀ w
  let start := clockInsert C (nextWindowWork C (plan C i₀ w k)) 4
  ext ω
  constructor
  · rintro ⟨j, hfirst, hcount⟩
    obtain ⟨cut, hcut, hentry⟩ :=
      firstErrorAt_has_goodWindowEntry C z₀ ω k j hfirst hcount
    have hstart := goodWindowEntry_state C i₀ w hs k hh cut ω hentry
    have hcc := goodWindowEntry_count C z₀ k cut ω hentry
    let q := j - cut
    have hsum : cut + q = j := Nat.add_sub_of_le hcut
    have hshift := tickCount_restartLabels_add C z₀ ω cut q
    rw [hsum, hcount, hcc, hstart] at hshift
    have hzero : tickCount C start (restartLabels (net C) cut ω) q = 0 := by
      dsimp only [start]
      omega
    have hbad : BadTickAt C start (restartLabels (net C) cut ω) q := by
      change BadTickAt C
        (clockInsert C (nextWindowWork C (plan C i₀ w k)) 4)
        (restartLabels (net C) cut ω) q
      rw [← hstart]
      apply (badTickAt_restartLabels C z₀ ω cut q).mpr
      simpa only [hsum] using hfirst.1
    exact Set.mem_iUnion.mpr ⟨cut, hentry,
      Set.mem_iUnion.mpr ⟨q, hzero, hbad⟩⟩
  · intro h
    obtain ⟨cut, hentry, htail⟩ := Set.mem_iUnion.mp h
    change restartLabels (net C) cut ω ∈ prematureTickEvent C start at htail
    obtain ⟨q, hzero, hbad⟩ := Set.mem_iUnion.mp htail
    have hstart := goodWindowEntry_state C i₀ w hs k hh cut ω hentry
    have hcc := goodWindowEntry_count C z₀ k cut ω hentry
    have hshift := tickCount_restartLabels_add C z₀ ω cut q
    rw [hstart, hzero, hcc, Nat.add_zero] at hshift
    have hbad' : BadTickAt C z₀ ω (cut + q) := by
      apply (badTickAt_restartLabels C z₀ ω cut q).mp
      rw [hstart]
      exact hbad
    refine ⟨cut + q, ⟨hbad', ?_⟩, hshift⟩
    intro m hm hbadm
    by_cases hmc : m < cut
    · exact goodWindowEntry_noBad C z₀ k cut ω hentry m hmc hbadm
    · have hlo := tickCount_mono C z₀ ω (show cut ≤ m by omega)
      have hhi := tickCount_mono C z₀ ω (show m + 1 ≤ cut + q by omega)
      change tickCount C z₀ ω cut ≤ tickCount C z₀ ω m at hlo
      change tickCount C z₀ ω (m + 1) ≤ tickCount C z₀ ω (cut + q) at hhi
      have hsucc := tickCount_succ_of_tick C z₀ ω m hbadm.1
      omega

private theorem entry_state_congr
    (C : XCTM Q) (z₀ : State (Sp C)) (ω ω' : LabelPath C)
    (cut j : ℕ) (hj : j ≤ cut)
    (h : Preorder.frestrictLe cut ω = Preorder.frestrictLe cut ω') :
    pathState (net C) z₀ ω j = pathState (net C) z₀ ω' j := by
  rw [← prefixToState_eq_pathState (net C) z₀ ω j,
    ← prefixToState_eq_pathState (net C) z₀ ω' j]
  congr 1
  funext r
  exact congrFun h ⟨r.val,
    Finset.mem_Iic.mpr ((Finset.mem_Iic.mp r.property).trans hj)⟩

private theorem entry_fired_congr
    (C : XCTM Q) (z₀ : State (Sp C)) (ω ω' : LabelPath C)
    (cut j : ℕ) (hj : j + 1 ≤ cut)
    (h : Preorder.frestrictLe cut ω = Preorder.frestrictLe cut ω') :
    pathFired (net C) z₀ ω j = pathFired (net C) z₀ ω' j := by
  have hz := entry_state_congr C z₀ ω ω' cut j (by omega) h
  have ho : ω (j + 1) = ω' (j + 1) :=
    congrFun h ⟨j + 1, Finset.mem_Iic.mpr hj⟩
  unfold pathFired
  rw [ho]
  by_cases hT : (net C).Terminal (pathState (net C) z₀ ω' j)
  · have hT' : (net C).Terminal (pathState (net C) z₀ ω j) := hz ▸ hT
    rw [dif_pos hT', dif_pos hT]
  · have hT' : ¬ (net C).Terminal (pathState (net C) z₀ ω j) := hz ▸ hT
    rw [dif_neg hT', dif_neg hT]
    simp only [hz]

private theorem entry_tick_congr
    (C : XCTM Q) (z₀ : State (Sp C)) (ω ω' : LabelPath C)
    (cut j : ℕ) (hj : j + 1 ≤ cut)
    (h : Preorder.frestrictLe cut ω = Preorder.frestrictLe cut ω') :
    TickAt C z₀ ω j ↔ TickAt C z₀ ω' j := by
  simp only [TickAt, firedTick, entry_fired_congr C z₀ ω ω' cut j hj h]

private theorem entry_count_congr
    (C : XCTM Q) (z₀ : State (Sp C)) (ω ω' : LabelPath C)
    (cut : ℕ) (h : Preorder.frestrictLe cut ω = Preorder.frestrictLe cut ω')
    (j : ℕ) (hj : j ≤ cut) :
    tickCount C z₀ ω j = tickCount C z₀ ω' j := by
  revert hj
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hc := ih (by omega)
      have ht := entry_tick_congr C z₀ ω ω' cut j hj h
      simp only [tickCount, hc]
      split_ifs with hfirst hsecond <;> first | rfl | (exfalso; tauto)

theorem goodWindowEntry_prefix_congr
    (C : XCTM Q) (z₀ : State (Sp C)) (k cut : ℕ)
    (ω ω' : LabelPath C)
    (h : Preorder.frestrictLe cut ω = Preorder.frestrictLe cut ω') :
    ω ∈ goodWindowEntry C z₀ k cut ↔ ω' ∈ goodWindowEntry C z₀ k cut := by
  cases cut with
  | zero => simp [goodWindowEntry]
  | succ j =>
      have hc := entry_count_congr C z₀ ω ω' (j + 1) h j (by omega)
      have ht := entry_tick_congr C z₀ ω ω' (j + 1) j le_rfl h
      have hb : ∀ m < j + 1,
          BadTickAt C z₀ ω m ↔ BadTickAt C z₀ ω' m := by
        intro m hm
        have hs := entry_state_congr C z₀ ω ω' (j + 1) m (by omega) h
        have htick := entry_tick_congr C z₀ ω ω' (j + 1) m (by omega) h
        simp only [BadTickAt, hs, htick]
      simp only [goodWindowEntry, Set.mem_setOf_eq, hc, ht]
      constructor
      · rintro ⟨hcount, htick, hgood⟩
        exact ⟨hcount, htick, fun m hm hb' => hgood m hm ((hb m hm).mpr hb')⟩
      · rintro ⟨hcount, htick, hgood⟩
        exact ⟨hcount, htick, fun m hm hb' => hgood m hm ((hb m hm).mp hb')⟩

def goodWindowEntryPrefix (C : XCTM Q) (z₀ : State (Sp C))
    (k cut : ℕ) : Set ((i : Finset.Iic cut) → Option (Rx C)) :=
  Preorder.frestrictLe cut '' goodWindowEntry C z₀ k cut

theorem goodWindowEntryPrefix_event (C : XCTM Q) (z₀ : State (Sp C))
    (k cut : ℕ) :
    {ω : LabelPath C | Preorder.frestrictLe cut ω ∈ goodWindowEntryPrefix C z₀ k cut} =
      goodWindowEntry C z₀ k cut := by
  ext ω
  constructor
  · rintro ⟨ω', hω', heq⟩
    exact (goodWindowEntry_prefix_congr C z₀ k cut ω' ω heq).mp hω'
  · intro hω
    exact ⟨ω, hω, rfl⟩

theorem measurableSet_goodWindowEntry (C : XCTM Q) (z₀ : State (Sp C))
    (k cut : ℕ) : MeasurableSet (goodWindowEntry C z₀ k cut) := by
  rw [← goodWindowEntryPrefix_event C z₀ k cut]
  exact (Preorder.measurable_frestrictLe cut)
    (measurableSet_prefixSet (net C) cut (goodWindowEntryPrefix C z₀ k cut))

theorem goodWindowEntryPrefix_state
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (k : ℕ) (hh : Plan.halted C (plan C i₀ w k) = false)
    (cut : ℕ) (p : (i : Finset.Iic cut) → Option (Rx C))
    (hp : p ∈ goodWindowEntryPrefix C (initial C i₀ w) k cut) :
    prefixToState (net C) (initial C i₀ w) cut p =
      clockInsert C (nextWindowWork C (plan C i₀ w k)) 4 := by
  obtain ⟨ω, hω, rfl⟩ := hp
  change
    prefixToState (net C) (initial C i₀ w) cut (fun j => ω j.1) =
      clockInsert C (nextWindowWork C (plan C i₀ w k)) 4
  rw [prefixToState_eq_pathState (net C) (initial C i₀ w) ω cut]
  exact goodWindowEntry_state C i₀ w hs k hh cut ω hω

/-- The deterministic-cut state-law identity remains an explicit premise. -/
def RawStateRestart (C : XCTM Q) (z₀ : State (Sp C)) : Prop :=
  ∀ (cut : ℕ) (p : (i : Finset.Iic cut) → Option (Rx C)),
    (ProbabilityTheory.Kernel.traj (X := fun _ => Option (net C).I)
      (fun j => stepKernel (net C) (net_hasPositiveRates C) z₀ j)
      cut p).map (restartLabels (net C) cut) =
      windowLaw C (prefixToState (net C) z₀ cut p)

theorem firstErrorWindow_le_fresh
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (k : ℕ) (hh : Plan.halted C (plan C i₀ w k) = false)
    (hLemmaEightRestart : RawStateRestart C (initial C i₀ w)) :
    jumpLaw C i₀ w (firstErrorWindow C (initial C i₀ w) (k + 1)) ≤
      windowLaw C (clockInsert C (nextWindowWork C (plan C i₀ w k)) 4)
        (prematureTickEvent C
          (clockInsert C (nextWindowWork C (plan C i₀ w k)) 4)) := by
  let start := clockInsert C (nextWindowWork C (plan C i₀ w k)) 4
  have hdisjoint : Pairwise (Function.onFun Disjoint
      (fun cut => {ω : LabelPath C | Preorder.frestrictLe cut ω ∈
        goodWindowEntryPrefix C (initial C i₀ w) k cut})) := by
    intro cut cut' hne
    simpa only [goodWindowEntryPrefix_event] using
      (goodWindowEntry_pairwise C (initial C i₀ w) k hne)
  have hrestart : ∀ (cut : ℕ)
      (p : (i : Finset.Iic cut) → Option (Rx C)),
      p ∈ goodWindowEntryPrefix C (initial C i₀ w) k cut →
      (ProbabilityTheory.Kernel.traj (X := fun _ => Option (net C).I)
        (fun j => stepKernel (net C) (net_hasPositiveRates C)
          (initial C i₀ w) j) cut p).map (restartLabels (net C) cut) =
        rawLaw (net C) (net_hasPositiveRates C) start := by
    intro cut p hp
    have hr := hLemmaEightRestart cut p
    rw [goodWindowEntryPrefix_state C i₀ w hs k hh cut p hp] at hr
    exact hr
  have hbound := rawLaw_stopped_prefix_le_of_restart
    (net C) (net_hasPositiveRates C) (initial C i₀ w)
    (goodWindowEntryPrefix C (initial C i₀ w) k)
    (fun _ => start) (fun _ => prematureTickEvent C start)
    (fun _ => measurableSet_prematureTickEvent C start)
    hdisjoint hrestart
    (windowLaw C start (prematureTickEvent C start)) (fun _ => le_rfl)
  change rawLaw (net C) (net_hasPositiveRates C) (initial C i₀ w)
      (firstErrorWindow C (initial C i₀ w) (k + 1)) ≤
    windowLaw C start (prematureTickEvent C start)
  rw [firstErrorWindow_eq_entry_restart C i₀ w hs k hh]
  refine (measure_mono ?_).trans hbound
  intro ω hω
  rcases Set.mem_iUnion.mp hω with ⟨cut, hentry, htail⟩
  refine Set.mem_iUnion.mpr ⟨cut, ?_, htail⟩
  exact ⟨ω, hentry, rfl⟩

theorem firstErrorWindow_le_meanDuration
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (k : ℕ) (hh : Plan.halted C (plan C i₀ w k) = false)
    (ha : 0 < (plan C i₀ w k).accuracy)
    (hLemmaEightRestart : RawStateRestart C (initial C i₀ w)) :
    jumpLaw C i₀ w (firstErrorWindow C (initial C i₀ w) (k + 1)) ≤
      ENNReal.ofReal ((1 / geomWeight (nextLowerRatio (plan C i₀ w k)) 5) *
        (stateCount (plan C i₀ w k).tape.length : ℝ)) *
      StandaloneWork.meanDuration C
        (Plan.workState C (plan C i₀ w k) + unit .signal) := by
  exact (firstErrorWindow_le_fresh C i₀ w hs k hh hLemmaEightRestart).trans
    (next_window_prematureTick_le_meanDuration C (plan C i₀ w k)
      (plan_valid C i₀ w hs k) hh ha)

theorem firstErrorWindow_empty_of_halted
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (k : ℕ) (hh : Plan.halted C (plan C i₀ w k) = true) :
    firstErrorWindow C (initial C i₀ w) (k + 1) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  have hf := firstErrorWindow_predecessor_active C i₀ w hs ω k hω
  rw [hh] at hf
  cases hf

namespace WindowAnalysis

/-- The geometric clock weight yields the reciprocal fourth-power bound. -/
theorem prematureTickEvent_le_power_bound (C : XCTM Q)
    (x₀ : ClocklessState C) {b F B : ℝ}
    (hb : 0 < b) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hparams : ∀ x : ClocklessState C, WorkReach C x₀.val x.val →
      b * (backwardCount C x.val : ℝ) ≤ (forwardCount C x.val : ℝ) ∧
        (backwardCount C x.val : ℝ) ≤ F)
    (hLemmaEightFour : StandaloneWork.meanDuration C x₀.val ≤ ENNReal.ofReal B) :
    windowLaw C (clockInsert C x₀ 4)
        (prematureTickEvent C (clockInsert C x₀ 4)) ≤
      ENNReal.ofReal (F * B / b ^ 4) := by
  have hgeom : b ^ 4 ≤ geomWeight b 5 := by
    unfold geomWeight
    exact Finset.single_le_sum (fun n _ => pow_nonneg hb.le n)
      (by norm_num : 4 ∈ Finset.range 5)
  have hgeompos : 0 < geomWeight b 5 := (pow_pos hb 4).trans_le hgeom
  have hinv : 1 / geomWeight b 5 ≤ 1 / b ^ 4 :=
    one_div_le_one_div_of_le (pow_pos hb 4) hgeom
  calc
    _ ≤ ENNReal.ofReal ((1 / geomWeight b 5) * F) *
        StandaloneWork.meanDuration C x₀.val :=
      prematureTickEvent_le_meanDuration C x₀ hb hparams
    _ ≤ ENNReal.ofReal ((1 / geomWeight b 5) * F) * ENNReal.ofReal B :=
      mul_le_mul_left' hLemmaEightFour _
    _ = ENNReal.ofReal (((1 / geomWeight b 5) * F) * B) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (one_div_nonneg.mpr hgeompos.le) hF)]
    _ ≤ ENNReal.ofReal (F * B / b ^ 4) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        ((1 / geomWeight b 5) * F) * B ≤ ((1 / b ^ 4) * F) * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinv hF) hB
        _ = F * B / b ^ 4 := by ring

/-- Cancellation of the work population in the one-window error estimate. -/
theorem prematureTickEvent_le_work_budget (C : XCTM Q)
    (x₀ : ClocklessState C) {b d L : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hL : 0 ≤ L)
    (hparams : ∀ x : ClocklessState C, WorkReach C x₀.val x.val →
      b * (backwardCount C x.val : ℝ) ≤ (forwardCount C x.val : ℝ) ∧
        (backwardCount C x.val : ℝ) ≤ d)
    (hLemmaEightFour :
      StandaloneWork.meanDuration C x₀.val ≤ ENNReal.ofReal (16 * L / d)) :
    windowLaw C (clockInsert C x₀ 4)
        (prematureTickEvent C (clockInsert C x₀ 4)) ≤
      ENNReal.ofReal (16 * L / b ^ 4) := by
  have h := prematureTickEvent_le_power_bound C x₀ hb hd.le
    (by positivity : 0 ≤ 16 * L / d) hparams hLemmaEightFour
  have heq : d * (16 * L / d) / b ^ 4 = 16 * L / b ^ 4 := by
    field_simp [hd.ne', hb.ne'] <;> ring
  simpa only [heq] using h

end WindowAnalysis

/-- Four first-error windows give the cubic step budget. -/
theorem firstErrorStep_le_of_window_charges
    (C : XCTM Q) (z₀ : State (Sp C)) (μ : Measure (LabelPath C))
    (n : ℕ) {a s : ℝ} (ha : 2 ≤ a) (hszero : 0 ≤ s) (hs : s ≤ a)
    (hwindow : ∀ r ∈ Finset.range 4,
      μ (firstErrorWindow C z₀ (4 * n + r)) ≤
        ENNReal.ofReal
          ((if r = 1 then (81 : ℝ) else 1) * 16 *
            (s + Real.log (a + 2)) / a ^ 4)) :
    μ (firstErrorStep C z₀ n) ≤ ENNReal.ofReal (2688 / a ^ 3) := by
  have hlog : 0 ≤ Real.log (a + 2) := Real.log_nonneg (by linarith)
  have hnonneg : ∀ r ∈ Finset.range 4,
      0 ≤ (if r = 1 then (81 : ℝ) else 1) * 16 *
        (s + Real.log (a + 2)) / a ^ 4 := by
    intro r _
    positivity
  rw [firstErrorStep_eq_four_windows]
  calc
    _ ≤ ∑ r ∈ Finset.range 4,
        μ (firstErrorWindow C z₀ (4 * n + r)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.range 4,
        ENNReal.ofReal
          ((if r = 1 then (81 : ℝ) else 1) * 16 *
            (s + Real.log (a + 2)) / a ^ 4) :=
      Finset.sum_le_sum hwindow
    _ = ENNReal.ofReal
        (∑ r ∈ Finset.range 4,
          (if r = 1 then (81 : ℝ) else 1) * 16 *
            (s + Real.log (a + 2)) / a ^ 4) :=
      (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
    _ ≤ ENNReal.ofReal (2688 / a ^ 3) :=
      ENNReal.ofReal_le_ofReal (four_window_charge_le ha hs)

theorem error_measure_le_of_window_charges
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hi : 2 ≤ (i₀ : ℝ))
    (space : ℕ → ℝ)
    (hspacezero : ∀ n, 0 ≤ space n)
    (hspace : ∀ n, space n ≤ (i₀ : ℝ) + (n : ℝ))
    (hwindow : ∀ n r, r ∈ Finset.range 4 →
      jumpLaw C i₀ w (firstErrorWindow C (initial C i₀ w) (4 * n + r)) ≤
        ENNReal.ofReal
          ((if r = 1 then (81 : ℝ) else 1) * 16 *
            (space n + Real.log ((i₀ : ℝ) + (n : ℝ) + 2)) /
              ((i₀ : ℝ) + (n : ℝ)) ^ 4)) :
    jumpLaw C i₀ w {ω | Error C (initial C i₀ w) ω} ≤
      ENNReal.ofReal (errorBound i₀) := by
  apply error_measure_le_of_firstErrorStep C i₀ w (by linarith)
  intro n
  exact firstErrorStep_le_of_window_charges C (initial C i₀ w)
    (jumpLaw C i₀ w) n
    (hi.trans (le_add_of_nonneg_right (Nat.cast_nonneg n)))
    (hspacezero n) (hspace n) (hwindow n)

namespace TimeAnalysis

open WindowAnalysis

/-- Only a tick creates a signal molecule. -/
theorem signal_fire_le_tick (C : XCTM Q) (r : Rx C) (z : State (Sp C)) :
    (rxn C r).fire z .signal ≤
      z .signal + if isTick r then 1 else 0 := by
  have hp : products C r .signal = if isTick r then 1 else 0 := by
    cases r <;>
      simp [products, isTick, unit, Pi.add_apply, Pi.smul_apply] <;>
      split_ifs <;> simp_all
  rw [fire_apply, hp]
  exact Nat.add_le_add_right (Nat.sub_le _ _) _

theorem signal_path_le_ticks (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (n : ℕ) :
    pathState (net C) z₀ ω n .signal ≤
      z₀ .signal + tickCount C z₀ ω n := by
  induction n with
  | zero => simp only [pathState, tickCount, Nat.add_zero, le_refl]
  | succ n ih =>
      have hv := pathFired_valid (net C) z₀ ω n
      cases hF : pathFired (net C) z₀ ω n with
      | none =>
          simp only [hF] at hv
          have hc : tickCount C z₀ ω (n + 1) = tickCount C z₀ ω n := by
            simp [tickCount, TickAt, firedTick, hF]
          rw [hv.1, hc]
          exact ih
      | some r =>
          simp only [hF] at hv
          have hc : tickCount C z₀ ω (n + 1) =
              tickCount C z₀ ω n + if isTick r then 1 else 0 := by
            simp [tickCount, TickAt, firedTick, hF]
          have hs := signal_fire_le_tick C r (pathState (net C) z₀ ω n)
          rw [hv.2, hc]
          change (rxn C r).fire (pathState (net C) z₀ ω n) .signal ≤
            z₀ .signal + (tickCount C z₀ ω n + if isTick r then 1 else 0)
          omega

private theorem state_le_workView_add_clockCount (C : XCTM Q)
    (z : State (Sp C)) (s : Sp C) :
    z s ≤ workView C z s + clockMoleculeCount C z := by
  have hc : ∀ c : Fin 5, z (.clock c) ≤ clockMoleculeCount C z := by
    intro c
    change z (.clock c) ≤ ∑ a : Fin 5, z (.clock a)
    exact Finset.single_le_sum
      (f := fun a : Fin 5 => z (.clock a))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  cases s <;> simp only [workView, zero_add]
  all_goals first | omega | exact hc _

private theorem state_le_cleanView_add_clock_signal (C : XCTM Q)
    (z : State (Sp C)) (s : Sp C) :
    z s ≤ cleanView C true z s + clockMoleculeCount C z + z .signal := by
  have hc : ∀ c : Fin 5, z (.clock c) ≤ clockMoleculeCount C z := by
    intro c
    change z (.clock c) ≤ ∑ a : Fin 5, z (.clock a)
    exact Finset.single_le_sum
      (f := fun a : Fin 5 => z (.clock a))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  cases s <;> simp only [cleanView, ite_true, zero_add]
  all_goals first | omega | exact (hc _).trans (Nat.le_add_right _ _)

/-- A qualitative bound in every fixed correct window, including halted
windows. This does not assert the quantitative volume constant of §14.3. -/
theorem exists_window_species_bound (C : XCTM Q) (i : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (k : ℕ) :
    ∃ b : Sp C → ℕ, ∀ z : State (Sp C),
      Window C i w k z → clockMoleculeCount C z = 1 → z .signal ≤ k →
        ∀ s : Sp C, z s ≤ b s := by
  cases k with
  | zero =>
      refine ⟨fun s => gamma C i w 0 s + 1, ?_⟩
      intro z hW hc _hI s
      change workView C z = gamma C i w 0 at hW
      simpa only [hW, hc] using state_le_workView_add_clockCount C z s
  | succ k =>
      cases hh : Plan.halted C (plan C i w k) with
      | true =>
          refine ⟨fun s => gamma C i w k s + 1 + (k + 1), ?_⟩
          intro z hW hc hI s
          have hz : cleanView C true z = gamma C i w k := by
            simpa only [Window, hh] using hW
          have hb := state_le_cleanView_add_clock_signal C z s
          rw [hz, hc] at hb
          exact hb.trans (Nat.add_le_add_left hI _)
      | false =>
          let P := planCertificate C (plan C i w k) (plan_valid C i w hs k) hh
          let start : State (Sp C) := gamma C i w k + unit .signal
          refine ⟨fun s => start s +
            P.rank start * windowProductBound C + 1, ?_⟩
          intro z hW hc _hI s
          have hr : WorkReach C (gamma C i w k + unit .signal) (workView C z) := by
            simpa only [Window, hh] using hW
          have hb := workCertificate_reachable_species_bound C P hr s
          have hz := state_le_workView_add_clockCount C z s
          rw [hc] at hz
          exact hz.trans (Nat.add_le_add_right hb 1)

theorem finite_window_support (C : XCTM Q) (i : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (k : ℕ) :
    Set.Finite {z : State (Sp C) |
      Window C i w k z ∧ clockMoleculeCount C z = 1 ∧ z .signal ≤ k} := by
  classical
  obtain ⟨b, hb⟩ := exists_window_species_bound C i w hs k
  let encode :
      {z : State (Sp C) //
        Window C i w k z ∧ clockMoleculeCount C z = 1 ∧ z .signal ≤ k} →
          ((s : Sp C) → Fin (b s + 1)) :=
    fun z s => ⟨z.val s, Nat.lt_succ_of_le
      (hb z.val z.property.1 z.property.2.1 z.property.2.2 s)⟩
  have hencode : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    funext s
    exact congrArg Fin.val (congrFun h s)
  exact Set.finite_coe_iff.mp (Finite.of_injective encode hencode)

theorem noError_window_rate_bound (C : XCTM Q) (i : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (k : ℕ) :
    ∃ R : ℝ≥0∞, R ≠ ⊤ ∧ ∀ j ω,
      ¬ Error C (initial C i w) ω → tickCount C (initial C i w) ω j = k →
        ((net C).totalPropensity (pathState (net C) (initial C i w) ω j) : ℝ≥0∞) ≤ R := by
  classical
  have hfinite := finite_window_support C i w hs k
  let D := hfinite.toFinset
  let R : ℝ≥0∞ := ∑ z ∈ D, ((net C).totalPropensity z : ℝ≥0∞)
  have hR : R ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro z _
    rw [← ENNReal.coe_nnratCast]
    exact ENNReal.coe_ne_top
  refine ⟨R, hR, ?_⟩
  intro j ω hNo hk
  have hclockInitial : clockMoleculeCount C (initial C i w) = 1 := by
    change (∑ c : Fin 5, if c = Fin.last 4 then (1 : ℕ) else 0) = 1
    norm_num [Fin.sum_univ_succ]
  have hclock := clockMoleculeCount_path_one C (initial C i w) hclockInitial ω j
  have hI : pathState (net C) (initial C i w) ω j .signal ≤ k := by
    have h := signal_path_le_ticks C (initial C i w) ω j
    have hi : initial C i w .signal = 0 := rfl
    rw [hi, hk, zero_add] at h
    exact h
  have hW : Window C i w k (pathState (net C) (initial C i w) ω j) := by
    simpa only [hk] using noError_window C i w hs ω hNo j
  have hD : pathState (net C) (initial C i w) ω j ∈ D :=
    hfinite.mem_toFinset.mpr ⟨hW, hclock, hI⟩
  change ((net C).totalPropensity
      (pathState (net C) (initial C i w) ω j) : ℝ≥0∞) ≤
    ∑ z ∈ D, ((net C).totalPropensity z : ℝ≥0∞)
  exact Finset.single_le_sum
    (f := fun z : State (Sp C) => ((net C).totalPropensity z : ℝ≥0∞))
    (fun _ _ => zero_le') hD

private theorem bounded_count_stabilizes (f : ℕ → ℕ) (hmono : Monotone f)
    (K : ℕ) (hbound : ∀ n, f n ≤ K) :
    ∃ j k : ℕ, ∀ n, j ≤ n → f n = k := by
  revert hbound
  induction K with
  | zero =>
      intro hbound
      exact ⟨0, 0, fun n _ => Nat.eq_zero_of_le_zero (hbound n)⟩
  | succ K ih =>
      intro hbound
      by_cases hhit : ∃ j, f j = K + 1
      · obtain ⟨j, hj⟩ := hhit
        refine ⟨j, K + 1, ?_⟩
        intro n hn
        exact le_antisymm (hbound n) (by simpa only [hj] using hmono hn)
      · apply ih
        intro n
        have hn : f n ≠ K + 1 := fun h => hhit ⟨n, h⟩
        have hb := hbound n
        omega

/-- The premise covers all windows, including those after halting. -/
theorem ae_noError_progress_of_finite_unit_means (C : XCTM Q)
    (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (hLemmaFourteenFour_finite : ∀ k,
      goodWindowUnitMean C (initial C i w) k ≠ ⊤) :
    ∀ᵐ ω ∂jumpLaw C i w,
      ¬ Error C (initial C i w) ω → TickProgress C (initial C i w) ω := by
  classical
  have hcost : ∀ k, ∀ᵐ ω ∂jumpLaw C i w,
      maskedUnitCost C (initial C i w)
        (windowActive C (initial C i w) k) ω < ⊤ := by
    intro k
    exact ae_lt_top
      (measurable_maskedUnitCost C (initial C i w)
        (windowActive C (initial C i w) k)
        (measurableSet_windowActive C (initial C i w) k))
      (hLemmaFourteenFour_finite k)
  have hall : ∀ᵐ ω ∂jumpLaw C i w, ∀ k,
      maskedUnitCost C (initial C i w)
        (windowActive C (initial C i w) k) ω < ⊤ := ae_all_iff.2 hcost
  filter_upwards [hall] with ω hω hNo
  by_contra hprogress
  change ¬ (∀ k : ℕ, ∃ j : ℕ, k ≤ tickCount C (initial C i w) ω j) at hprogress
  obtain ⟨K, hK⟩ := not_forall.mp hprogress
  have hbounded : ∀ j, tickCount C (initial C i w) ω j ≤ K := by
    intro j
    have hn : ¬ K ≤ tickCount C (initial C i w) ω j := fun h => hK ⟨j, h⟩
    omega
  obtain ⟨j, k, hstable⟩ := bounded_count_stabilizes
    (tickCount C (initial C i w) ω) (tickCount_mono C (initial C i w) ω) K hbounded
  obtain ⟨R, hR, hrate⟩ := noError_window_rate_bound C i w hs k
  have hactive : ∀ n, windowActive C (initial C i w) k (j + n) ω := by
    intro n
    refine ⟨hstable (j + n) (Nat.le_add_right j n), ?_⟩
    intro m _hm hbad
    exact hNo ⟨m, hbad⟩
  let term : ℕ → ℝ≥0∞ := fun n =>
    if windowActive C (initial C i w) k n ω then
      CTMCBridge.meanHolding (net C) (initial C i w) n ω else 0
  have hdiv : (∑' n : ℕ, term (j + n)) = ⊤ := by
    apply tsum_eq_top_of_le (ENNReal.inv_ne_zero.mpr hR)
    intro n
    dsimp only [term]
    rw [if_pos (hactive n)]
    change R⁻¹ ≤
      ((net C).totalPropensity
        (pathState (net C) (initial C i w) ω (j + n)) : ℝ≥0∞)⁻¹
    exact ENNReal.inv_le_inv.mpr (hrate (j + n) ω hNo (hactive n).1)
  have hinj : Function.Injective (fun n : ℕ => j + n) := by
    intro a b h
    change j + a = j + b at h
    exact Nat.add_left_cancel h
  have hshift : (∑' n : ℕ, term (j + n)) ≤ ∑' n : ℕ, term n :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj term
  have htop : maskedUnitCost C (initial C i w)
      (windowActive C (initial C i w) k) ω = ⊤ := by
    apply top_unique
    change ⊤ ≤ ∑' n : ℕ, term n
    rw [← hdiv]
    exact hshift
  exact (ne_of_lt (hω k)) htop

end TimeAnalysis

namespace TimeAnalysis

open WindowAnalysis

/-- Finite real terminal occupation vectors are determined by weighted
entry mass. Finiteness of actual terminal occupation is a separate obligation. -/
theorem terminal_balance_weighted_entry {a f : ℝ} {w e : ℕ → ℝ}
    (hf : 0 < f) (h : PhysicalBalance a f 0 w e) :
    psum w 5 = ∑ c ∈ Finset.range 5,
      e c * tickWait (a / f) f (c + 1) := by
  let m : ℕ → ℝ := tickWait (a / f) f
  have hmzero : m 0 = 0 := tickWait_zero (a / f) f
  have hrec (c : ℕ) (hc : 1 ≤ c) (hclast : c < 5) :
      f * (m c - m (c - 1)) = 1 + a * (m (c + 1) - m c) := by
    have hh := tickWait_backward (r := a / f) (f := f) (ne_of_gt hf) hc hclast
    rw [div_mul_cancel₀ a (ne_of_gt hf)] at hh
    exact hh
  have hrlast : f * (m 5 - m 4) = 1 :=
    tickWait_reflecting (r := a / f) (f := f) (ne_of_gt hf)
  have hrfirst := hrec 1 (by norm_num) (by norm_num)
  have hrsecond := hrec 2 (by norm_num) (by norm_num)
  have hrthird := hrec 3 (by norm_num) (by norm_num)
  have hrfourth := hrec 4 (by norm_num) (by norm_num)
  have hbzero := h 0 (by norm_num)
  have hbfirst := h 1 (by norm_num)
  have hbsecond := h 2 (by norm_num)
  have hbthird := h 3 (by norm_num)
  have hblast := h 4 (by norm_num)
  norm_num [hmzero] at hrfirst hrsecond hrthird hrfourth
  norm_num at hbzero hbfirst hbsecond hbthird hblast
  change psum w 5 = ∑ c ∈ Finset.range 5, e c * m (c + 1)
  norm_num [psum, Finset.sum_range_succ]
  linear_combination
    m 1 * hbzero + m 2 * hbfirst + m 3 * hbsecond +
      m 4 * hbthird + m 5 * hblast -
      w 0 * hrfirst - w 1 * hrsecond - w 2 * hrthird -
      w 3 * hrfourth - w 4 * hrlast

theorem terminal_balance_le_entry_top {a f : ℝ} {w e : ℕ → ℝ}
    (ha : 0 ≤ a) (hf : 0 < f) (h : PhysicalBalance a f 0 w e)
    (he : ∀ c, c < 5 → 0 ≤ e c) :
    psum w 5 ≤ tickWait (a / f) f 5 * psum e 5 := by
  rw [terminal_balance_weighted_entry hf h]
  unfold psum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  have hclast : c + 1 ≤ 5 := by
    have := Finset.mem_range.mp hc
    omega
  calc
    e c * tickWait (a / f) f (c + 1) ≤
        e c * tickWait (a / f) f 5 :=
      mul_le_mul_of_nonneg_left
        (tickWait_le_top (div_nonneg ha hf.le) hf hclast)
        (he c (Finset.mem_range.mp hc))
    _ = _ := mul_comm _ _

theorem tickWait_restored_bound {α d : ℝ} (hα : 3 ≤ α) (hd : 0 < d) :
    tickWait (α + 1) d 5 ≤ (16 / 9 : ℝ) * (α + 1) ^ 4 / d := by
  have hb : 0 ≤ α - 3 := sub_nonneg.mpr hα
  have hpoly :
      (α + 1) ^ 4 + 2 * (α + 1) ^ 3 + 3 * (α + 1) ^ 2 +
        4 * (α + 1) + 5 ≤ (16 / 9 : ℝ) * (α + 1) ^ 4 := by
    have hid : (16 / 9 : ℝ) * (α + 1) ^ 4 -
        ((α + 1) ^ 4 + 2 * (α + 1) ^ 3 + 3 * (α + 1) ^ 2 +
          4 * (α + 1) + 5) =
        (7 / 9 : ℝ) * (α - 3) ^ 4 + (94 / 9 : ℝ) * (α - 3) ^ 3 +
          (143 / 3 : ℝ) * (α - 3) ^ 2 + (676 / 9 : ℝ) * (α - 3) + 19 / 9 := by
      ring
    apply sub_nonneg.mp
    rw [hid]
    positivity
  rw [tickWait_top_polynomial]
  exact div_le_div_of_nonneg_right hpoly hd.le

theorem tickWait_first_bound {α d f : ℝ} (hα : 3 ≤ α) (hd : 0 < d)
    (hf : d / 3 ≤ f) :
    tickWait α f 5 ≤ 3 * (α + 1) ^ 4 / d := by
  have hfpos : 0 < f := (div_pos hd (by norm_num : (0 : ℝ) < 3)).trans_le hf
  have hb : 0 ≤ α - 1 := by linarith
  have hpoly : α ^ 4 + 2 * α ^ 3 + 3 * α ^ 2 + 4 * α + 5 ≤ (α + 1) ^ 4 := by
    have hid : (α + 1) ^ 4 - (α ^ 4 + 2 * α ^ 3 + 3 * α ^ 2 + 4 * α + 5) =
        2 * (α - 1) ^ 3 + 9 * (α - 1) ^ 2 + 12 * (α - 1) + 1 := by
      ring
    apply sub_nonneg.mp
    rw [hid]
    positivity
  calc
    tickWait α f 5 = (α ^ 4 + 2 * α ^ 3 + 3 * α ^ 2 + 4 * α + 5) / f :=
      tickWait_top_polynomial α f
    _ ≤ (α + 1) ^ 4 / f := div_le_div_of_nonneg_right hpoly hfpos.le
    _ ≤ (α + 1) ^ 4 / (d / 3) :=
      div_le_div_of_nonneg_left (by positivity)
        (div_pos hd (by norm_num : (0 : ℝ) < 3)) hf
    _ = 3 * (α + 1) ^ 4 / d := by
      field_simp [ne_of_gt hd]
      <;> ring

theorem terminal_tickWait_budget {α d r f : ℝ} (hα : 3 ≤ α) (hd : 0 < d)
    (hparams : (r = α + 1 ∧ f = d) ∨ (r = α ∧ d / 3 ≤ f)) :
    tickWait r f 5 ≤ 3 * (α + 1) ^ 4 / d := by
  rcases hparams with ⟨rfl, rfl⟩ | ⟨rfl, hf⟩
  · apply (tickWait_restored_bound hα hd).trans
    apply div_le_div_of_nonneg_right _ hd.le
    exact mul_le_mul_of_nonneg_right
      (by norm_num : (16 / 9 : ℝ) ≤ 3) (by positivity)
  · exact tickWait_first_bound hα hd hf

theorem work_plus_tick_budget {α d r f : ℝ} (hα : 3 ≤ α) (hd : 0 < d)
    (hparams : (r = α + 1 ∧ f = d) ∨ (r = α ∧ d / 3 ≤ f)) :
    32 * α / d + tickWait r f 5 ≤ (27 / 8 : ℝ) * (α + 1) ^ 4 / d := by
  have hw := div_le_div_of_nonneg_right (work_mean_relaxation hα) hd.le
  have ht := terminal_tickWait_budget hα hd hparams
  calc
    32 * α / d + tickWait r f 5 ≤
        ((3 / 8 : ℝ) * (α + 1) ^ 4) / d + 3 * (α + 1) ^ 4 / d :=
      add_le_add hw ht
    _ = _ := by ring

end TimeAnalysis

namespace StandaloneWork

/-- Only the restoration and fourth-phase work estimates remain here.
The three buffer constructors are discharged below. -/
def PendingWorkEstimate (C : XCTM Q) (p : Plan C) (a : ℕ) : Prop :=
  match p with
  | .first _ _ _ _ | .third _ _ _ =>
      meanDuration C (Plan.workState C p + unit .signal) ≤
        ENNReal.ofReal (workDurationBound p.tape.length a)
  | _ => True

theorem next_window_meanDuration_le_of_pending (C : XCTM Q)
    (p : Plan C) (a : ℕ) (hs : 3 ≤ p.tape.length)
    (hLemmaEightFour : PendingWorkEstimate C p a) :
    meanDuration C (Plan.workState C p + unit .signal) ≤
      ENNReal.ofReal (workDurationBound p.tape.length a) := by
  cases p with
  | first q w accuracy latent => exact hLemmaEightFour
  | third q w accuracy => exact hLemmaEightFour
  | second q w accuracy =>
      exact buffer_meanDuration_le_workDurationBound C (.toThird q w accuracy) a hs
  | write q bit w accuracy =>
      exact buffer_meanDuration_le_workDurationBound C (.fromRead q bit w accuracy) a hs
  | extend e w accuracy =>
      exact buffer_meanDuration_le_workDurationBound C (.fromExtension e w accuracy) a hs

end StandaloneWork

/-- Only W2/W4r/W4e are assumptions; W1/W3 are proved above.
The accuracy parameter is the step accuracy i+n, not blindly p.accuracy. -/
def LemmaEightFourPhases (C : XCTM Q) : Prop :=
  ∀ (w : List Bool) (i : ℕ) (δ : ℝ), AdmissibleAccuracy w i δ →
    ∀ n r : ℕ, r < 4 → 0 < 4 * n + r →
      Plan.halted C (plan C i w (4 * n + r - 1)) = false →
        StandaloneWork.PendingWorkEstimate C
          (plan C i w (4 * n + r - 1)) (i + n)

/-- The qualitative time premise includes every window after halting. -/
def AllGoodWindowMeansFinite (C : XCTM Q) : Prop :=
  ∀ (w : List Bool) (i : ℕ) (δ : ℝ), AdmissibleAccuracy w i δ →
    ∀ k, TimeAnalysis.goodWindowUnitMean C (initial C i w) k ≠ ⊤

theorem firstErrorWindow_le_of_note_estimates
    (C : XCTM Q) (w : List Bool) (i : ℕ) (δ : ℝ)
    (hacc : AdmissibleAccuracy w i δ)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaEightRestart : RawStateRestart C (initial C i w))
    (n r : ℕ) (hr : r < 4) :
    jumpLaw C i w (firstErrorWindow C (initial C i w) (4 * n + r)) ≤
      ENNReal.ofReal
        ((if r = 1 then (81 : ℝ) else 1) * 16 *
          (((i : ℝ) + (n : ℝ)) + Real.log ((i : ℝ) + (n : ℝ) + 2)) /
            ((i : ℝ) + (n : ℝ)) ^ 4) := by
  by_cases hzero : 4 * n + r = 0
  · rw [hzero, firstErrorWindow_initial_empty C i w hacc.1, measure_empty]
    exact bot_le
  have hpos : 0 < 4 * n + r := by omega
  have hsucc : 4 * n + r = (4 * n + r - 1) + 1 := by omega
  cases hh : Plan.halted C (plan C i w (4 * n + r - 1)) with
  | true =>
      rw [hsucc, firstErrorWindow_empty_of_halted C i w hacc.1 _ hh, measure_empty]
      exact bot_le
  | false =>
      let p := plan C i w (4 * n + r - 1)
      let a : ℝ := (i : ℝ) + (n : ℝ)
      let d : ℝ := (stateCount p.tape.length : ℝ)
      let b : ℝ := if r = 1 then a / 3 else a
      have hs := plan_valid C i w hacc.1 (4 * n + r - 1)
      have hi : 3 ≤ (i : ℝ) := by
        have hlen : (w.length : ℝ) ≤ (i : ℝ) :=
          (le_max_left _ _).trans hacc.2.2.2
        have hlenmin : (3 : ℝ) ≤ w.length := by exact_mod_cast hacc.1
        linarith
      have ha : 2 ≤ a := by
        dsimp [a]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hapos : 0 < a := by linarith
      have hd : 0 < d := by dsimp [d]; unfold stateCount; positivity
      have hb : 0 < b := by dsimp [b]; split_ifs <;> positivity
      have hlog : 0 ≤ Real.log (a + 2) := Real.log_nonneg (by linarith)
      have hL : 0 ≤ a + Real.log (a + 2) := add_nonneg hapos.le hlog
      have hschedule := next_window_schedule_parameters C i w δ hacc n r hr hpos hh
      have hspace : (p.tape.length : ℝ) ≤ a := by
        dsimp [p, a]
        exact_mod_cast hschedule.1
      have hratio : b ≤ nextLowerRatio p := hschedule.2
      have hwork := StandaloneWork.next_window_meanDuration_le_of_pending C p (i + n) hs
        (hLemmaEightFour_phases w i δ hacc n r hr hpos hh)
      have hwork' : StandaloneWork.meanDuration C (nextWindowWork C p).val ≤
          ENNReal.ofReal (16 * ((p.tape.length : ℝ) + Real.log (a + 2)) / d) := by
        simpa only [nextWindowWork, StandaloneWork.workDurationBound,
          Nat.cast_add, a, d] using hwork
      have hbudget : StandaloneWork.meanDuration C (nextWindowWork C p).val ≤
          ENNReal.ofReal (16 * (a + Real.log (a + 2)) / d) := by
        refine hwork'.trans (ENNReal.ofReal_le_ofReal ?_)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add hspace le_rfl) (by norm_num)) hd.le
      have hparams : ∀ x : ClocklessState C,
          WorkReach C (nextWindowWork C p).val x.val →
          b * (backwardCount C x.val : ℝ) ≤ (forwardCount C x.val : ℝ) ∧
            (backwardCount C x.val : ℝ) ≤ d := by
        intro x hx
        have hp := next_window_sharp_parameters C p hs hh hx
        have hf : (0 : ℝ) < backwardCount C x.val := by exact_mod_cast hp.1
        refine ⟨(le_div_iff₀ hf).mp (hratio.trans hp.2.2), ?_⟩
        change (backwardCount C x.val : ℝ) ≤ (stateCount p.tape.length : ℝ)
        exact_mod_cast hp.2.1
      have hfresh := prematureTickEvent_le_work_budget C (nextWindowWork C p)
        hb hd hL hparams hbudget
      have heq : 16 * (a + Real.log (a + 2)) / b ^ 4 =
          (if r = 1 then (81 : ℝ) else 1) * 16 *
            (a + Real.log (a + 2)) / a ^ 4 := by
        dsimp only [b]
        split_ifs <;> field_simp [hapos.ne'] <;> ring
      rw [heq] at hfresh
      rw [hsucc]
      exact (firstErrorWindow_le_fresh C i w hacc.1 _ hh hLemmaEightRestart).trans hfresh

/-- hE follows from local work estimates, schedule arithmetic, and the
explicit deterministic-cut state law; no step-error hypothesis is assumed. -/
theorem firstErrorStep_le_of_note_estimates
    (C : XCTM Q) (w : List Bool) (i : ℕ) (δ : ℝ)
    (hacc : AdmissibleAccuracy w i δ)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaEightRestart : RawStateRestart C (initial C i w)) (n : ℕ) :
    jumpLaw C i w (firstErrorStep C (initial C i w) n) ≤
      ENNReal.ofReal (2688 / ((i : ℝ) + (n : ℝ)) ^ 3) := by
  have hi : 3 ≤ (i : ℝ) := by
    have hlen : (w.length : ℝ) ≤ (i : ℝ) :=
      (le_max_left _ _).trans hacc.2.2.2
    have hlenmin : (3 : ℝ) ≤ w.length := by exact_mod_cast hacc.1
    linarith
  have ha : 2 ≤ (i : ℝ) + (n : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  apply firstErrorStep_le_of_window_charges C (initial C i w) (jumpLaw C i w) n
    (a := (i : ℝ) + (n : ℝ)) (s := (i : ℝ) + (n : ℝ))
    ha (by positivity) le_rfl
  intro r hr
  exact firstErrorWindow_le_of_note_estimates C w i δ hacc
    hLemmaEightFour_phases hLemmaEightRestart n r
    (Finset.mem_range.mp hr)

/-- ErrorClaim with herror and hprogress derived from explicit note inputs. -/
theorem errorClaim_of_note_window_estimates (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaEightRestart : ∀ (w : List Bool) (i : ℕ) (δ : ℝ),
      AdmissibleAccuracy w i δ → RawStateRestart C (initial C i w))
    (hLemmaFourteenFour_finite : AllGoodWindowMeansFinite C) :
    ErrorClaim C := by
  apply errorClaim_of_estimates C
  · intro w i δ hacc
    apply error_measure_le_of_firstErrorStep C i w (admissibleAccuracy_gt_one hacc)
    intro n
    exact firstErrorStep_le_of_note_estimates C w i δ hacc
      hLemmaEightFour_phases
      (hLemmaEightRestart w i δ hacc) n
  · intro w i δ hacc
    exact TimeAnalysis.ae_noError_progress_of_finite_unit_means C i w hacc.1
      (hLemmaFourteenFour_finite w i δ hacc)

namespace TimeAnalysis

/-- Window zero is initialized; subsequent work starts use the preceding
clean plan. Idle signals after halting do not create work. -/
noncomputable def scheduledWorkStart (C : XCTM Q) (i : ℕ) (w : List Bool) :
    ℕ → State (Sp C)
  | 0 => workView C (initial C i w)
  | k + 1 => Plan.workState C (plan C i w k) + unit .signal

theorem scheduled_workMean_le (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (w : List Bool) (i : ℕ) (δ : ℝ) (hacc : AdmissibleAccuracy w i δ)
    (k : ℕ) :
    StandaloneWork.meanDuration C (scheduledWorkStart C i w k) ≤
      ENNReal.ofReal (32 * windowAccuracy i k / windowPopulation C w k) := by
  cases k with
  | zero =>
      rw [scheduledWorkStart, StandaloneWork.initial_meanDuration_eq_zero]
      exact bot_le
  | succ m =>
      let n := (m + 1) / 4
      let r := (m + 1) % 4
      let p := plan C i w m
      have hr : r < 4 := Nat.mod_lt _ (by norm_num)
      have hindex : 4 * n + r = m + 1 := by dsimp [n, r]; omega
      have hk : 0 < 4 * n + r := by omega
      have hpred : 4 * n + r - 1 = m := by omega
      cases hh : Plan.halted C p with
      | true =>
          change StandaloneWork.meanDuration C (Plan.workState C p + unit .signal) ≤ _
          rw [StandaloneWork.halted_next_meanDuration_eq_zero C p hh]
          exact bot_le
      | false =>
          have hactive : Plan.halted C (plan C i w (4 * n + r - 1)) = false := by
            simpa only [hpred] using hh
          have hs := plan_valid C i w hacc.1 m
          have hphase : StandaloneWork.PendingWorkEstimate C p (i + n) := by
            simpa only [hpred] using
              hLemmaEightFour_phases w i δ hacc n r hr hk hactive
          have hmean := StandaloneWork.next_window_meanDuration_le_of_pending C p (i + n)
            hs hphase
          have htape := next_window_schedule_tape C i w hacc.1 n r hr hk hactive
          have hpop : (stateCount p.tape.length : ℝ) = windowPopulation C w (m + 1) := by
            change (stateCount (plan C i w m).tape.length : ℝ) =
              (stateCount (C.runT (C.start, w) n).2.length : ℝ)
            rw [← hpred, htape]
          have hacast : ((i + n : ℕ) : ℝ) = windowAccuracy i (m + 1) := by
            simp only [Nat.cast_add, windowAccuracy, n]
          have hschedule := next_window_schedule_parameters C i w δ hacc n r hr hk hactive
          have hspace : (p.tape.length : ℝ) ≤ windowAccuracy i (m + 1) := by
            have hnat : p.tape.length ≤ i + n := by simpa only [hpred] using hschedule.1
            rw [← hacast]
            exact_mod_cast hnat
          have hα := windowAccuracy_ge_three w i (m + 1) δ hacc
          have hlog := log_add_two_le_self (show 2 ≤ windowAccuracy i (m + 1) by linarith)
          have hmean' : StandaloneWork.meanDuration C (scheduledWorkStart C i w (m + 1)) ≤
              ENNReal.ofReal
                (16 * ((p.tape.length : ℝ) + Real.log (windowAccuracy i (m + 1) + 2)) /
                  windowPopulation C w (m + 1)) := by
            simpa only [scheduledWorkStart, StandaloneWork.workDurationBound,
              hpop, hacast] using hmean
          refine hmean'.trans (ENNReal.ofReal_le_ofReal ?_)
          apply div_le_div_of_nonneg_right _ (windowPopulation_pos C w (m + 1)).le
          linarith

/-- Worst terminal parameters in the two cases of §14.4. -/
noncomputable def terminalRatioBudget (i k : ℕ) : ℝ :=
  if k % 4 = 0 then windowAccuracy i k else windowAccuracy i k + 1

noncomputable def terminalBackwardBudget (C : XCTM Q) (w : List Bool) (k : ℕ) : ℝ :=
  if k % 4 = 0 then windowPopulation C w k / 3 else windowPopulation C w k

/-- The actual occupation/restart estimate remains explicit. This is where
the missing terminal occupation argument belongs. -/
def LemmaFourteenFourOccupation (C : XCTM Q) : Prop :=
  ∀ (w : List Bool) (i : ℕ) (δ : ℝ), AdmissibleAccuracy w i δ →
    ∀ n, BeforeHalt C w n → ∀ k, k < 4 * n →
      goodWindowUnitMean C (initial C i w) k ≤
        StandaloneWork.meanDuration C (scheduledWorkStart C i w k) +
          ENNReal.ofReal (tickWait (terminalRatioBudget i k)
            (terminalBackwardBudget C w k) 5)

def LemmaFourteenThreeVolume (C : XCTM Q) : Prop :=
  ∀ (w : List Bool) (i : ℕ) (δ : ℝ), AdmissibleAccuracy w i δ →
    ∀ n, BeforeHalt C w n → ∀ k, k < 4 * n → ∀ j ω,
      windowActive C (initial C i w) k j ω →
        (moleculeCount C (pathState (net C) (initial C i w) ω j) : ℝ) ≤
          (windowAccuracy i k + 24) * windowPopulation C w k

theorem goodWindowUnitMean_le_of_work_clock_split (C : XCTM Q)
    (z₀ workStart : State (Sp C)) (k : ℕ) {α d r f : ℝ}
    (hα : 3 ≤ α) (hd : 0 < d)
    (hparams : (r = α + 1 ∧ f = d) ∨ (r = α ∧ d / 3 ≤ f))
    (hLemmaEightFour : StandaloneWork.meanDuration C workStart ≤
      ENNReal.ofReal (32 * α / d))
    (hLemmaFourteenFour_occupation : goodWindowUnitMean C z₀ k ≤
      StandaloneWork.meanDuration C workStart + ENNReal.ofReal (tickWait r f 5)) :
    goodWindowUnitMean C z₀ k ≤ ENNReal.ofReal ((27 / 8 : ℝ) * (α + 1) ^ 4 / d) := by
  have ht : 0 ≤ tickWait r f 5 := by
    rcases hparams with ⟨rfl, rfl⟩ | ⟨rfl, hf⟩
    · exact tickWait_nonneg (by linarith) hd 5
    · exact tickWait_nonneg (by linarith)
        ((div_pos hd (by norm_num : (0 : ℝ) < 3)).trans_le hf) 5
  have hw : 0 ≤ 32 * α / d := by positivity
  calc
    goodWindowUnitMean C z₀ k ≤
        StandaloneWork.meanDuration C workStart + ENNReal.ofReal (tickWait r f 5) :=
      hLemmaFourteenFour_occupation
    _ ≤ ENNReal.ofReal (32 * α / d) + ENNReal.ofReal (tickWait r f 5) :=
      add_le_add hLemmaEightFour le_rfl
    _ = ENNReal.ofReal (32 * α / d + tickWait r f 5) :=
      (ENNReal.ofReal_add hw ht).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (work_plus_tick_budget hα hd hparams)

/-- The exact original hLemmaFourteenFour_unitTime premise, derived from
the remaining phase estimates and the explicit actual occupation split. -/
theorem unitTime_of_phase_and_occupation_estimates (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaFourteenFour_occupation : LemmaFourteenFourOccupation C)
    (w : List Bool) (i : ℕ) (δ : ℝ) (hacc : AdmissibleAccuracy w i δ)
    (n : ℕ) (hbefore : BeforeHalt C w n) (k : ℕ) (hk : k < 4 * n) :
    goodWindowUnitMean C (initial C i w) k ≤
      ENNReal.ofReal ((27 / 8 : ℝ) * (windowAccuracy i k + 1) ^ 4 /
        windowPopulation C w k) := by
  have hp :
      (terminalRatioBudget i k = windowAccuracy i k + 1 ∧
        terminalBackwardBudget C w k = windowPopulation C w k) ∨
      (terminalRatioBudget i k = windowAccuracy i k ∧
        windowPopulation C w k / 3 ≤ terminalBackwardBudget C w k) := by
    by_cases hz : k % 4 = 0
    · right
      simp [terminalRatioBudget, terminalBackwardBudget, hz]
    · left
      simp [terminalRatioBudget, terminalBackwardBudget, hz]
  exact goodWindowUnitMean_le_of_work_clock_split C (initial C i w)
    (scheduledWorkStart C i w k) k
    (windowAccuracy_ge_three w i k δ hacc) (windowPopulation_pos C w k) hp
    (scheduled_workMean_le C hLemmaEightFour_phases w i δ hacc k)
    (hLemmaFourteenFour_occupation w i δ hacc n hbefore k hk)

theorem timeClaim_of_note_window_estimates (C : XCTM Q)
    (hLemmaSevenOne : ErrorClaim C)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaFourteenThree : LemmaFourteenThreeVolume C)
    (hLemmaFourteenFour_occupation : LemmaFourteenFourOccupation C) :
    TimeClaim C :=
  timeClaim_of_volume_and_unit_estimates C hLemmaSevenOne hLemmaFourteenThree
    (unitTime_of_phase_and_occupation_estimates C
      hLemmaEightFour_phases hLemmaFourteenFour_occupation)

/-- The windows not covered by any before-halt time estimate need only
qualitative finiteness for the repository's all-window progress assertion.
This includes the W1 transition into a halt. -/
def LemmaFourteenFourTailFinite (C : XCTM Q) : Prop :=
  ∀ (w : List Bool) (i : ℕ) (δ : ℝ), AdmissibleAccuracy w i δ →
    ∀ k, (∀ n, BeforeHalt C w n → 4 * n ≤ k) →
      goodWindowUnitMean C (initial C i w) k ≠ ⊤

theorem allGoodWindowMeansFinite_of_occupation_and_tail (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaFourteenFour_occupation : LemmaFourteenFourOccupation C)
    (hLemmaFourteenFour_tail : LemmaFourteenFourTailFinite C) :
    AllGoodWindowMeansFinite C := by
  classical
  intro w i δ hacc k
  by_cases hbefore : ∃ n, BeforeHalt C w n ∧ k < 4 * n
  · obtain ⟨n, hn, hk⟩ := hbefore
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (unitTime_of_phase_and_occupation_estimates C hLemmaEightFour_phases
        hLemmaFourteenFour_occupation w i δ hacc n hn k hk)
  · apply hLemmaFourteenFour_tail w i δ hacc k
    intro n hn
    by_contra hk
    exact hbefore ⟨n, hn, by omega⟩

end TimeAnalysis

/-- Combined reducer: none of hE, herror, hprogress, or the original
hLemmaFourteenFour_unitTime is an input. The five remaining note obligations
are explicit and are not asserted by this theorem. -/
theorem error_and_timeClaims_of_note_estimates (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaEightRestart : ∀ (w : List Bool) (i : ℕ) (δ : ℝ),
      AdmissibleAccuracy w i δ → RawStateRestart C (initial C i w))
    (hLemmaFourteenThree : TimeAnalysis.LemmaFourteenThreeVolume C)
    (hLemmaFourteenFour_occupation : TimeAnalysis.LemmaFourteenFourOccupation C)
    (hLemmaFourteenFour_tail : TimeAnalysis.LemmaFourteenFourTailFinite C) :
    ErrorClaim C ∧ TimeClaim C := by
  have hfinite := TimeAnalysis.allGoodWindowMeansFinite_of_occupation_and_tail C
    hLemmaEightFour_phases hLemmaFourteenFour_occupation hLemmaFourteenFour_tail
  have herror := errorClaim_of_note_window_estimates C
    hLemmaEightFour_phases hLemmaEightRestart hfinite
  exact ⟨herror, TimeAnalysis.timeClaim_of_note_window_estimates C herror
    hLemmaEightFour_phases hLemmaFourteenThree hLemmaFourteenFour_occupation⟩

/-- Counterexample: the exact-ratio sentence in §8.3 of the note fails during ordinary
restoration. This defect is already recorded in the note's §18. -/
theorem ordinary_restore_ratio_strict_between :
    WorkReach RatioWitness.machine RatioWitness.start RatioWitness.restored ∧
      (38 : ℚ) <
        (forwardCount RatioWitness.machine RatioWitness.restored : ℚ) /
          backwardCount RatioWitness.machine RatioWitness.restored ∧
      (forwardCount RatioWitness.machine RatioWitness.restored : ℚ) /
          backwardCount RatioWitness.machine RatioWitness.restored < 39 := by
  have h := RatioWitness.ordinary_restore_ratio_counterexample
  refine ⟨RatioWitness.ordinary_restore_reachable, ?_, ?_⟩
  all_goals
    rw [h.2.2.1, h.2.2.2.1]
    norm_num

end Ripple.sCRNUniversality.ClockedCTM.Unbounded
