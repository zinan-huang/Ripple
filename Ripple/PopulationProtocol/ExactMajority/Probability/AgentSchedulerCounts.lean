/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Counts of scheduler words as probabilities of the configuration chain

This file proves Corollary 5 of `docs/audit/AGENT-SCHEDULER-LUMPING.md`: a count of labelled
scheduler words of length `T`, as a model checker computes it, divided by `(n (n - 1)) ^ T`, is a
probability of the configuration chain of the protocol.

The configuration chain is Mathlib's Ionescu–Tulcea trajectory measure
`ProbabilityTheory.Kernel.trajMeasure` for the time-homogeneous family of history kernels
`Protocol.historyKernel t`, each of which applies `Protocol.transitionKernel` to the configuration
at time `t`; `Protocol.chainLaw P c` is this measure started from the point mass at `c`. Hitting
times of the chain are Mathlib's `MeasureTheory.hittingBtwn` of the coordinate process.

* `Protocol.map_agentPath_eq_chainLaw` (path lumping): under the scheduler measure, the whole
  configuration path of the labelled run has law `Protocol.chainLaw P (Config.ofAgents a)`. This is
  the extension of Theorem 4 to joint laws. Its finite-dimensional form
  `Protocol.map_history_eq_partialTraj` is proved by induction on the horizon, using that the
  letter at time `b` is independent of the earlier letters (`infinitePi_eq_map_update`).
* `Protocol.survivalNumerator_div_eq_chainLaw`: surviving words / `(n (n - 1)) ^ T` is the
  probability that the chain avoids `Q` at times `0, …, T`.
* `Protocol.firstHitNumerator_div_eq_chainLaw`: first-hit words / `(n (n - 1)) ^ T` is the
  probability that the chain first visits `Q` at time `T`.
* `Protocol.costNumerator_div_eq_lintegral_chainLaw`: total truncated cost / `(n (n - 1)) ^ T` is
  the expectation of the hitting time of `Q` truncated at `T`.

The counts are those of `Ripple.CountingBridge.FirstHit` for the alphabet `AgentPair n`, the
transition `Protocol.agentStep` on assignments and the target `fun b => Q (Config.ofAgents b)`.
The last section evaluates both sides for the two-agent "or" protocol.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.AgentScheduler
import Ripple.Probability.CountingBridge.Events
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.HittingTime
import Mathlib.Logic.Equiv.List

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

/-! ### Hitting times of letter-driven runs -/

section Hitting

variable {S α C : Type*}

/-- The run survives strictly past time `T` iff it avoids the target at times `0, …, T`. -/
theorem lt_τ_iff_forall_not (next : S → α → S) (P : S → Prop) (x : S) (ω : ℕ → α) (T : ℕ) :
    (T : ℕ∞) < CountingBridge.τ next P x ω ↔
      ∀ t ≤ T, ¬ P (CountingBridge.run next x ω t) := by
  classical
  by_cases h : ∃ t, P (CountingBridge.run next x ω t)
  · rw [CountingBridge.τ, dif_pos h, Nat.cast_lt, Nat.lt_find_iff]
  · rw [CountingBridge.τ, dif_neg h]
    exact iff_of_true (ENat.natCast_lt_top T) fun t _ ht => h ⟨t, ht⟩

/-- The hitting time equals `T` iff the run is in the target at time `T` and not before. -/
theorem τ_eq_natCast_iff (next : S → α → S) (P : S → Prop) (x : S) (ω : ℕ → α) (T : ℕ) :
    CountingBridge.τ next P x ω = T ↔
      P (CountingBridge.run next x ω T) ∧ ∀ t < T, ¬ P (CountingBridge.run next x ω t) := by
  classical
  by_cases h : ∃ t, P (CountingBridge.run next x ω t)
  · rw [CountingBridge.τ, dif_pos h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [CountingBridge.τ, dif_neg h]
    exact iff_of_false (ENat.top_ne_natCast T) fun hT => h ⟨T, hT.1⟩

/-- The truncated hitting time of a coordinate process depends only on the coordinates up to the
truncation time. -/
theorem hittingBtwn_eval_congr (s : Set C) (T : ℕ) {x x' : ℕ → C}
    (h : ∀ t ≤ T, x t = x' t) :
    hittingBtwn (ι := ℕ) (fun t (y : ℕ → C) => y t) s 0 T x =
      hittingBtwn (ι := ℕ) (fun t (y : ℕ → C) => y t) s 0 T x' := by
  have hset : Set.Icc 0 T ∩ {i | x i ∈ s} = Set.Icc 0 T ∩ {i | x' i ∈ s} := by
    ext i
    constructor
    · rintro ⟨hi, his⟩
      refine ⟨hi, ?_⟩
      have hx : x i ∈ s := his
      rw [h i hi.2] at hx
      exact hx
    · rintro ⟨hi, his⟩
      refine ⟨hi, ?_⟩
      have hx : x' i ∈ s := his
      rw [← h i hi.2] at hx
      exact hx
  have hex : (∃ j ∈ Set.Icc 0 T, x j ∈ s) ↔ ∃ j ∈ Set.Icc 0 T, x' j ∈ s := by
    constructor
    · rintro ⟨j, hj, hjs⟩
      exact ⟨j, hj, h j hj.2 ▸ hjs⟩
    · rintro ⟨j, hj, hjs⟩
      exact ⟨j, hj, (h j hj.2).symm ▸ hjs⟩
  simp only [hittingBtwn]
  by_cases hc : ∃ j ∈ Set.Icc 0 T, x j ∈ s
  · rw [if_pos hc, if_pos (hex.1 hc), hset]
  · rw [if_neg hc, if_neg (mt hex.2 hc)]

/-- The hitting time of a letter-driven run, truncated at `T`, is Mathlib's `hittingBtwn` of the
observed path on `[0, T]`. -/
theorem min_τ_eq_hittingBtwn (next : S → α → S) (f : S → C) (Q : C → Prop) (x : S)
    (ω : ℕ → α) (T : ℕ) :
    min (CountingBridge.τ next (fun s => Q (f s)) x ω) T =
      (hittingBtwn (ι := ℕ) (fun t (y : ℕ → C) => y t) {c | Q c} 0 T
        (fun t => f (CountingBridge.run next x ω t)) : ℕ∞) := by
  by_cases hex : ∃ j ∈ Set.Icc 0 T, f (CountingBridge.run next x ω j) ∈ {c | Q c}
  · have hmem := hittingBtwn_mem_set (u := fun (t : ℕ) (y : ℕ → C) => y t) hex
    have hle := hittingBtwn_le (u := fun (t : ℕ) (y : ℕ → C) => y t) (s := {c | Q c}) (n := 0)
      (m := T) (fun t => f (CountingBridge.run next x ω t))
    have hτ := (τ_eq_natCast_iff next (fun s => Q (f s)) x ω _).2
      ⟨hmem, fun t ht => notMem_of_lt_hittingBtwn ht (Nat.zero_le t)⟩
    rw [hτ]
    exact min_eq_left (by exact_mod_cast hle)
  · have hT := (hittingBtwn_eq_end_iff (u := fun (t : ℕ) (y : ℕ → C) => y t) (s := {c | Q c})
      (n := 0) (m := T) (ω := fun t => f (CountingBridge.run next x ω t))).2
      fun h => absurd h hex
    rw [hT]
    exact min_eq_right ((lt_τ_iff_forall_not next (fun s => Q (f s)) x ω T).2
      fun t ht hQ => hex ⟨t, ⟨Nat.zero_le t, ht⟩, hQ⟩).le

/-- The ratio of a count to `card α ^ T`, computed in `ℚ` and cast to `ℝ≥0∞`. -/
theorem ofReal_count_div_card_pow [Fintype α] [Nonempty α] (k T : ℕ) :
    ENNReal.ofReal (((k : ℚ) / (Fintype.card α : ℚ) ^ T : ℚ) : ℝ) =
      (k : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ T := by
  have hn : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
    ENNReal.ofReal_div_of_pos (pow_pos hn T), ENNReal.ofReal_pow hn.le, ENNReal.ofReal_natCast]

end Hitting

/-! ### Resampling one letter -/

/-- Under the product of a probability measure `ν` over `ℕ`, the coordinate `b` is independent of
the others: replacing it by an independent `ν`-sample does not change the law. -/
theorem infinitePi_eq_map_update {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (b : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => ν).prod ν).map (fun q => Function.update q.1 b q.2) =
      Measure.infinitePi fun _ : ℕ => ν := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hmeas : MeasurableSet (Set.pi (↑s : Set ℕ) t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  have hpre : (fun q : (ℕ → X) × X => Function.update q.1 b q.2) ⁻¹' Set.pi (↑s) t =
      Set.pi (↑(s.erase b)) t ×ˢ (if b ∈ s then t b else Set.univ) := by
    ext ⟨ω, x⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i ⟨hib, hi⟩ => ?_, ?_⟩
      · have hω := h i hi
        rwa [Function.update_of_ne hib] at hω
      · split_ifs with hb
        · have hx := h b hb
          rwa [Function.update_self] at hx
        · exact Set.mem_univ x
    · rintro ⟨h, hx⟩ i hi
      by_cases hib : i = b
      · subst hib
        rw [if_pos hi] at hx
        rw [Function.update_self]
        exact hx
      · rw [Function.update_of_ne hib]
        exact h i ⟨hib, hi⟩
  rw [Measure.map_apply measurable_update' hmeas, hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ fun i _ => ht i]
  split_ifs with hb
  · exact (mul_comm _ _).trans (Finset.mul_prod_erase s (fun i => ν (t i)) hb)
  · rw [measure_univ, mul_one, Finset.erase_eq_of_notMem hb]

/-! ### The configuration chain as a trajectory measure -/

/-- The state space of the configuration chain at each time. -/
abbrev ConfigAt (Λ : Type*) : ℕ → Type _ := fun _ => Config Λ

/-- `MeasurableEquiv.piSingleton` puts the configuration at every point of `Ioc t (t + 1)`. -/
theorem piSingleton_apply {Λ : Type*} (t : ℕ) (x : ConfigAt Λ (t + 1)) (j : Finset.Ioc t (t + 1)) :
    MeasurableEquiv.piSingleton (X := ConfigAt Λ) t x j = x := by
  obtain ⟨j, hj⟩ := j
  have hjt : j = t + 1 := Nat.mem_Ioc_succ.1 hj
  subst hjt
  exact (MeasurableEquiv.piSingleton (X := ConfigAt Λ) t).symm_apply_apply x

/-! ### Events of the chain -/

/-- The chain avoids `Q` at times `0, …, T`. -/
theorem measurableSet_forall_le_not {Λ : Type*} [Countable Λ] (Q : Config Λ → Prop) (T : ℕ) :
    MeasurableSet {x : Π t, ConfigAt Λ t | ∀ t ≤ T, ¬ Q (x t)} := by
  have hset : {x : Π t, ConfigAt Λ t | ∀ t ≤ T, ¬ Q (x t)} =
      frestrictLe T ⁻¹' {y | ∀ i, ¬ Q (y i)} := by
    ext x
    exact ⟨fun h i => h i (Finset.mem_Iic.1 i.2), fun h t ht => h ⟨t, Finset.mem_Iic.2 ht⟩⟩
  rw [hset]
  exact measurable_frestrictLe T MeasurableSet.of_discrete

/-- The chain visits `Q` for the first time at time `T`. -/
theorem measurableSet_firstHit {Λ : Type*} [Countable Λ] (Q : Config Λ → Prop) (T : ℕ) :
    MeasurableSet {x : Π t, ConfigAt Λ t | Q (x T) ∧ ∀ t < T, ¬ Q (x t)} := by
  have hset : {x : Π t, ConfigAt Λ t | Q (x T) ∧ ∀ t < T, ¬ Q (x t)} =
      frestrictLe T ⁻¹' {y | Q (y ⟨T, Finset.mem_Iic.2 le_rfl⟩) ∧
        ∀ i : Finset.Iic T, (i : ℕ) < T → ¬ Q (y i)} := by
    ext x
    exact ⟨fun h => ⟨h.1, fun i hi => h.2 i hi⟩,
      fun h => ⟨h.1, fun t ht => h.2 ⟨t, Finset.mem_Iic.2 ht.le⟩ ht⟩⟩
  rw [hset]
  exact measurable_frestrictLe T MeasurableSet.of_discrete

/-- The hitting time of `Q` truncated at `T` is a measurable function of the path. -/
theorem measurable_hittingBtwn_coord {Λ : Type*} [Countable Λ] (Q : Config Λ → Prop) (T : ℕ) :
    Measurable fun x : Π t, ConfigAt Λ t =>
      (hittingBtwn (ι := ℕ) (fun t (y : ℕ → Config Λ) => y t) {c | Q c} 0 T x : ℝ≥0∞) := by
  let extend : (Π i : Finset.Iic T, ConfigAt Λ i) → Π t, ConfigAt Λ t :=
    fun y t => y ⟨min t T, Finset.mem_Iic.2 (min_le_right t T)⟩
  have hfac : (fun x : Π t, ConfigAt Λ t =>
      (hittingBtwn (ι := ℕ) (fun t (y : ℕ → Config Λ) => y t) {c | Q c} 0 T x : ℝ≥0∞)) =
      (fun y => (hittingBtwn (ι := ℕ) (fun t (y : ℕ → Config Λ) => y t) {c | Q c} 0 T
        (extend y) : ℝ≥0∞)) ∘ frestrictLe T := by
    funext x
    change (hittingBtwn (ι := ℕ) (fun t (y : ℕ → Config Λ) => y t) {c | Q c} 0 T x : ℝ≥0∞) =
      (hittingBtwn (ι := ℕ) (fun t (y : ℕ → Config Λ) => y t) {c | Q c} 0 T
        (extend (frestrictLe T x)) : ℝ≥0∞)
    rw [hittingBtwn_eval_congr (C := Config Λ) {c | Q c} T
      (x := x) (x' := extend (frestrictLe T x)) fun t ht => ?_]
    change x t = x (min t T)
    rw [min_eq_left ht]
  rw [hfac]
  exact (measurable_of_countable _).comp (measurable_frestrictLe T)

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {n : ℕ}

namespace Protocol

/-- The configuration chain as a family of history kernels: given the configurations up to time
`t`, the configuration at time `t + 1` has law `P.transitionKernel` at the configuration at time
`t`. -/
noncomputable def historyKernel (P : Protocol Λ) (t : ℕ) :
    Kernel (Π i : Finset.Iic t, ConfigAt Λ i) (ConfigAt Λ (t + 1)) :=
  P.transitionKernel.comap (fun x => x ⟨t, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance historyKernel_isMarkovKernel (P : Protocol Λ) (t : ℕ) :
    IsMarkovKernel (P.historyKernel t) := by
  unfold historyKernel
  infer_instance

/-- The law of the configuration chain started at `c`: the Ionescu–Tulcea trajectory measure of
the history kernels, started from the point mass at `c`. -/
noncomputable def chainLaw (P : Protocol Λ) (c : Config Λ) : Measure (Π t, ConfigAt Λ t) :=
  Kernel.trajMeasure (X := ConfigAt Λ) (Measure.dirac c) P.historyKernel

theorem chainLaw_eq_traj (P : Protocol Λ) (c : Config Λ) :
    P.chainLaw c = Kernel.traj P.historyKernel 0 (fun _ => c) := by
  rw [chainLaw, Kernel.trajMeasure, Measure.map_dirac' (MeasurableEquiv.measurable _),
    Measure.dirac_bind (Kernel.measurable _)]
  congr 1

/-! ### Path lumping -/

/-- The configuration path of the labelled run. -/
def agentPath (P : Protocol Λ) (a : Fin n → Λ) (ω : ℕ → AgentPair n) : Π t, ConfigAt Λ t :=
  fun t => Config.ofAgents (P.agentRun a ω t)

theorem measurable_agentPath (P : Protocol Λ) (a : Fin n → Λ) :
    Measurable (P.agentPath a) :=
  measurable_pi_lambda _ fun t => measurable_ofAgents_agentRun P a t

/-- The labelled run up to time `t` depends only on the letters before time `t`. -/
theorem agentRun_congr (P : Protocol Λ) (t : ℕ) :
    ∀ (a : Fin n → Λ) {ω ω' : ℕ → AgentPair n}, (∀ j < t, ω j = ω' j) →
      P.agentRun a ω t = P.agentRun a ω' t := by
  induction t with
  | zero => intro a ω ω' _; rfl
  | succ t ih =>
      intro a ω ω' h
      rw [agentRun_succ, agentRun_succ, h 0 (Nat.succ_pos t)]
      exact ih _ fun j hj => h (j + 1) (by omega)

/-- The scheduler measure is unchanged when the letter at time `b` is resampled. -/
theorem schedulerMeasure_eq_map_update (hn : 2 ≤ n) (b : ℕ) :
    schedulerMeasure n hn =
      ((schedulerMeasure n hn).prod (letterPMF n hn).toMeasure).map
        (fun q => Function.update q.1 b q.2) :=
  (infinitePi_eq_map_update _ b).symm

/-- **Markov step.** Given the configuration history up to time `b`, the configuration at time
`b + 1` has law `historyKernel b`: the letter at time `b` is independent of the history, and
Proposition 3 identifies the law of the next configuration. -/
theorem map_history_step (P : Protocol Λ) (hn : 2 ≤ n) (a : Fin n → Λ) (b : ℕ) :
    (schedulerMeasure n hn).map (fun ω => (frestrictLe b (P.agentPath a ω),
        MeasurableEquiv.piSingleton (X := ConfigAt Λ) b (P.agentPath a ω (b + 1)))) =
      (schedulerMeasure n hn).map (fun ω => frestrictLe b (P.agentPath a ω)) ⊗ₘ
        (P.historyKernel b).map (MeasurableEquiv.piSingleton (X := ConfigAt Λ) b) := by
  have hH : Measurable fun ω => frestrictLe b (P.agentPath a ω) :=
    (measurable_frestrictLe b).comp (measurable_agentPath P a)
  have hc : Measurable fun ω =>
      MeasurableEquiv.piSingleton (X := ConfigAt Λ) b (P.agentPath a ω (b + 1)) :=
    (MeasurableEquiv.measurable _).comp (measurable_ofAgents_agentRun P a (b + 1))
  have hHupd : ∀ (ω : ℕ → AgentPair n) (p : AgentPair n),
      frestrictLe b (P.agentPath a (Function.update ω b p)) = frestrictLe b (P.agentPath a ω) := by
    intro ω p
    funext i
    have hib : (i : ℕ) ≤ b := Finset.mem_Iic.1 i.2
    change Config.ofAgents (P.agentRun a (Function.update ω b p) i) =
      Config.ofAgents (P.agentRun a ω i)
    rw [agentRun_congr P i a fun j hj =>
      Function.update_of_ne (show j ≠ b by omega) p ω]
  have hcupd : ∀ (ω : ℕ → AgentPair n) (p : AgentPair n),
      P.agentPath a (Function.update ω b p) (b + 1) =
        Config.ofAgents (P.agentStep (P.agentRun a ω b) p) := by
    intro ω p
    change Config.ofAgents (P.agentRun a (Function.update ω b p) (b + 1)) = _
    rw [agentRun_succ', Function.update_self,
      agentRun_congr P b a fun j hj => Function.update_of_ne (Nat.ne_of_lt hj) p ω]
  ext s hs
  have hF := (hH.prodMk hc) hs
  rw [Measure.map_apply (hH.prodMk hc) hs, Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hH]
  conv_lhs => rw [schedulerMeasure_eq_map_update hn b]
  rw [Measure.map_apply measurable_update' hF, Measure.prod_apply (measurable_update' hF)]
  refine lintegral_congr fun ω => ?_
  have hk : P.historyKernel b (frestrictLe b (P.agentPath a ω)) =
      (letterPMF n hn).toMeasure.map fun p => Config.ofAgents (P.agentStep (P.agentRun a ω b) p) :=
    transitionKernel_ofAgents P hn _
  rw [Kernel.map_apply' _ (MeasurableEquiv.measurable _) _ (measurable_prodMk_left hs), hk,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  congr 1
  ext p
  simp only [Set.mem_preimage]
  rw [hHupd ω p, hcupd ω p]

/-- **Finite-dimensional path lumping.** The configuration history up to time `b` of the labelled
run has the law `partialTraj` of the history kernels started at the configuration of `a`. -/
theorem map_history_eq_partialTraj (P : Protocol Λ) (hn : 2 ≤ n) (a : Fin n → Λ) (b : ℕ) :
    (schedulerMeasure n hn).map (fun ω => frestrictLe b (P.agentPath a ω)) =
      Kernel.partialTraj P.historyKernel 0 b (fun _ => Config.ofAgents a) := by
  induction b with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_apply]
      have hconst : (fun ω => frestrictLe 0 (P.agentPath a ω)) =
          fun _ => (fun _ => Config.ofAgents a : Π i : Finset.Iic 0, ConfigAt Λ i) := by
        funext ω i
        have hi : (i : ℕ) = 0 := Nat.le_zero.1 (Finset.mem_Iic.1 i.2)
        change Config.ofAgents (P.agentRun a ω i) = Config.ofAgents a
        rw [hi, agentRun_zero]
      rw [hconst, Measure.map_const, measure_univ, one_smul]
  | succ b ih =>
      have hH : Measurable fun ω => frestrictLe b (P.agentPath a ω) :=
        (measurable_frestrictLe b).comp (measurable_agentPath P a)
      have hc : Measurable fun ω =>
          MeasurableEquiv.piSingleton (X := ConfigAt Λ) b (P.agentPath a ω (b + 1)) :=
        (MeasurableEquiv.measurable _).comp (measurable_ofAgents_agentRun P a (b + 1))
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le b), Kernel.comp_apply, ← ih,
        Kernel.partialTraj_succ_self,
        ← Measure.map_comp _ _ (measurable_IicProdIoc (X := ConfigAt Λ) (m := b) (n := b + 1)),
        ← Measure.compProd_eq_comp_prod, ← map_history_step P hn a b,
        Measure.map_map (measurable_IicProdIoc (X := ConfigAt Λ) (m := b) (n := b + 1))
          (hH.prodMk hc)]
      congr 1
      funext ω i
      simp only [Function.comp_apply, IicProdIoc]
      split_ifs with h
      · rfl
      · rw [piSingleton_apply]
        have hi : (i : ℕ) = b + 1 := by
          have := Finset.mem_Iic.1 i.2
          omega
        change Config.ofAgents (P.agentRun a ω i) = Config.ofAgents (P.agentRun a ω (b + 1))
        rw [hi]

/-- **Path lumping.** Under the scheduler measure, the configuration path of the labelled run has
the law of the configuration chain started at the configuration of `a`. -/
theorem map_agentPath_eq_chainLaw (P : Protocol Λ) (hn : 2 ≤ n) (a : Fin n → Λ) :
    (schedulerMeasure n hn).map (P.agentPath a) = P.chainLaw (Config.ofAgents a) := by
  have hfin : ∀ I : Finset ℕ, IsFiniteMeasure (inducedFamily
      (fun b => Kernel.partialTraj P.historyKernel 0 b (fun _ => Config.ofAgents a)) I) := by
    intro I
    rw [inducedFamily]
    exact Measure.isFiniteMeasure_map _ _
  rw [chainLaw_eq_traj, Kernel.traj_apply]
  refine IsProjectiveLimit.unique ?_ (Kernel.isProjectiveLimit_trajFun _ 0 _)
  refine (isProjectiveLimit_nat_iff (Kernel.isProjectiveMeasureFamily_partialTraj _ _) _).2
    fun b => ?_
  rw [inducedFamily_Iic, Measure.map_map (measurable_frestrictLe b) (measurable_agentPath P a)]
  exact map_history_eq_partialTraj P hn a b

/-! ### Corollary 5 -/

/-- The run of the counting bridge driven by `agentStep` is the labelled run. -/
theorem run_agentStep (P : Protocol Λ) (a : Fin n → Λ) (ω : ℕ → AgentPair n) (t : ℕ) :
    CountingBridge.run P.agentStep a ω t = P.agentRun a ω t := by
  induction t generalizing a ω with
  | zero => rw [CountingBridge.run_zero, agentRun_zero]
  | succ t ih => rw [CountingBridge.run_succ_tail, ih, agentRun_succ]

/-- **Corollary 5 (survival).** The number of scheduler words of length `T` along which the
configuration of the labelled run avoids `Q` at times `0, …, T`, divided by `(n (n - 1)) ^ T`, is
the probability that the configuration chain started at the configuration of `a` avoids `Q` at
times `0, …, T`. -/
theorem survivalNumerator_div_eq_chainLaw (P : Protocol Λ) (hn : 2 ≤ n) (Q : Config Λ → Prop)
    (a : Fin n → Λ) (T : ℕ) :
    (CountingBridge.FirstHit.survivalNumerator P.agentStep (fun b => Q (Config.ofAgents b)) a T :
        ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ^ T =
      P.chainLaw (Config.ofAgents a) {x | ∀ t ≤ T, ¬ Q (x t)} := by
  have := AgentPair.nonempty hn
  rw [← AgentPair.card_eq n, ← CountingBridge.survival_measure_count,
    show CountingBridge.μ (AgentPair n) = schedulerMeasure n hn from rfl,
    ← map_agentPath_eq_chainLaw P hn a,
    Measure.map_apply (measurable_agentPath P a) (measurableSet_forall_le_not Q T)]
  congr 1
  ext ω
  change (T : ℕ∞) < CountingBridge.τ _ _ a ω ↔ ∀ t ≤ T, ¬ Q (Config.ofAgents (P.agentRun a ω t))
  rw [lt_τ_iff_forall_not]
  simp only [run_agentStep]

/-- **Corollary 5 (first hit).** The number of scheduler words of length `T` along which the
configuration of the labelled run visits `Q` for the first time at time `T`, divided by
`(n (n - 1)) ^ T`, is the probability that the configuration chain first visits `Q` at time
`T`. -/
theorem firstHitNumerator_div_eq_chainLaw (P : Protocol Λ) (hn : 2 ≤ n) (Q : Config Λ → Prop)
    (a : Fin n → Λ) (T : ℕ) :
    (CountingBridge.FirstHit.firstHitNumerator P.agentStep (fun b => Q (Config.ofAgents b)) a T :
        ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ^ T =
      P.chainLaw (Config.ofAgents a) {x | Q (x T) ∧ ∀ t < T, ¬ Q (x t)} := by
  have := AgentPair.nonempty hn
  rw [← AgentPair.card_eq n, ← ofReal_count_div_card_pow]
  change ENNReal.ofReal (CountingBridge.FirstHit.firstHitProb P.agentStep
    (fun b => Q (Config.ofAgents b)) a T : ℝ) = _
  rw [← CountingBridge.firstHit_measure,
    show CountingBridge.μ (AgentPair n) = schedulerMeasure n hn from rfl,
    ← map_agentPath_eq_chainLaw P hn a,
    Measure.map_apply (measurable_agentPath P a) (measurableSet_firstHit Q T)]
  congr 1
  ext ω
  change CountingBridge.τ _ _ a ω = (T : ℕ∞) ↔ Q (Config.ofAgents (P.agentRun a ω T)) ∧
    ∀ t < T, ¬ Q (Config.ofAgents (P.agentRun a ω t))
  rw [τ_eq_natCast_iff]
  simp only [run_agentStep]

/-- **Corollary 5 (truncated expected hitting time).** The total number of letters consumed before
the configuration of the labelled run first visits `Q`, capped at `T`, summed over the scheduler
words of length `T` and divided by `(n (n - 1)) ^ T`, is the expectation of the hitting time of `Q`
by the configuration chain, truncated at `T`. -/
theorem costNumerator_div_eq_lintegral_chainLaw (P : Protocol Λ) (hn : 2 ≤ n)
    (Q : Config Λ → Prop) (a : Fin n → Λ) (T : ℕ) :
    (CountingBridge.FirstHit.costNumerator P.agentStep (fun b => Q (Config.ofAgents b)) a T :
        ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ^ T =
      ∫⁻ x, (hittingBtwn (ι := ℕ) (fun t (y : ℕ → Config Λ) => y t) {c | Q c} 0 T x : ℝ≥0∞)
        ∂P.chainLaw (Config.ofAgents a) := by
  have := AgentPair.nonempty hn
  rw [← AgentPair.card_eq n, ← CountingBridge.lintegral_min_hit_eq,
    show CountingBridge.μ (AgentPair n) = schedulerMeasure n hn from rfl,
    ← map_agentPath_eq_chainLaw P hn a,
    lintegral_map (measurable_hittingBtwn_coord Q T) (measurable_agentPath P a)]
  refine lintegral_congr fun ω => ?_
  have h := congrArg ENat.toENNReal
    (min_τ_eq_hittingBtwn P.agentStep Config.ofAgents Q a ω T)
  simp only [run_agentStep, ENat.toENNReal_min, ENat.toENNReal_coe] at h
  exact h

end Protocol

/-! ### Example: the two-agent "or" protocol -/

/-- The "or" protocol on `Bool`: both agents leave an interaction with the disjunction of their
states. -/
def orProtocol : Protocol Bool := ⟨fun x y => (x || y, x || y)⟩

/-- All agents are in state `true`. -/
def AllTrue (c : Config Bool) : Prop := ∀ s ∈ c, s = true

/-- Two agents, the first in state `true` and the second in state `false`. -/
def oneTrue : Fin 2 → Bool := ![true, false]

theorem oneTrue_or (p : AgentPair 2) :
    (oneTrue p.initiator || oneTrue p.responder) = true := by
  have hij := p.initiator_ne_responder
  generalize p.initiator = i at hij ⊢
  generalize p.responder = j at hij ⊢
  fin_cases i <;> fin_cases j <;> simp_all [oneTrue]

theorem orProtocol_agentStep_oneTrue (p : AgentPair 2) (k : Fin 2) :
    orProtocol.agentStep oneTrue p k = true := by
  have hv := oneTrue_or p
  have hij := p.initiator_ne_responder
  unfold Protocol.agentStep
  by_cases hkj : k = p.responder
  · rw [hkj, Function.update_self]
    exact hv
  · rw [Function.update_of_ne hkj]
    have hki : k = p.initiator := by
      generalize p.initiator = i at hij ⊢
      generalize p.responder = j at hij hkj ⊢
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    rw [hki, Function.update_self]
    exact hv

theorem allTrue_ofAgents_agentStep (p : AgentPair 2) :
    AllTrue (Config.ofAgents (orProtocol.agentStep oneTrue p)) := by
  intro s hs
  obtain ⟨k, _, rfl⟩ := Multiset.mem_map.1 hs
  exact orProtocol_agentStep_oneTrue p k

theorem not_allTrue_ofAgents_oneTrue : ¬ AllTrue (Config.ofAgents oneTrue) := by
  intro h
  have hfalse := h false (Multiset.mem_map.2 ⟨1, by simp, rfl⟩)
  exact Bool.false_ne_true hfalse

theorem wordSum_zero {α : Type*} [Fintype α] (f : CountingBridge.Words.Word α → ℕ) :
    CountingBridge.Words.wordSum α 0 f = f [] := by
  simp [CountingBridge.Words.wordSum, CountingBridge.Words.allWords]

/-- No scheduler word of length one keeps the "or" protocol away from the all-true
configuration. -/
theorem survivalNumerator_oneTrue :
    CountingBridge.FirstHit.survivalNumerator orProtocol.agentStep
      (fun b => AllTrue (Config.ofAgents b)) oneTrue 1 = 0 := by
  rw [CountingBridge.FirstHit.survivalNumerator, CountingBridge.Words.wordSum_succ]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [wordSum_zero, CountingBridge.FirstHit.survivalWord,
    if_neg not_allTrue_ofAgents_oneTrue, CountingBridge.FirstHit.survivalWord,
    if_pos (allTrue_ofAgents_agentStep p)]

/-- Every scheduler word of length one consumes exactly one letter before the all-true
configuration. -/
theorem costNumerator_oneTrue :
    CountingBridge.FirstHit.costNumerator orProtocol.agentStep
      (fun b => AllTrue (Config.ofAgents b)) oneTrue 1 = 2 := by
  rw [CountingBridge.FirstHit.costNumerator, CountingBridge.Words.wordSum_succ]
  have hterm : ∀ p : AgentPair 2, CountingBridge.Words.wordSum (AgentPair 2) 0
      (fun u => CountingBridge.FirstHit.costWord orProtocol.agentStep
        (fun b => AllTrue (Config.ofAgents b)) oneTrue (p :: u)) = 1 := by
    intro p
    rw [wordSum_zero, CountingBridge.FirstHit.costWord, if_neg not_allTrue_ofAgents_oneTrue,
      CountingBridge.FirstHit.costWord]
  rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, Finset.card_univ,
    AgentPair.card_eq, smul_eq_mul, mul_one]

/-- For the "or" protocol from one `true` agent among two, the configuration chain reaches the
all-true configuration by time one almost surely. -/
theorem orProtocol_chainLaw_survival :
    orProtocol.chainLaw (Config.ofAgents oneTrue) {x | ∀ t ≤ 1, ¬ AllTrue (x t)} = 0 := by
  rw [← Protocol.survivalNumerator_div_eq_chainLaw orProtocol le_rfl AllTrue oneTrue 1,
    survivalNumerator_oneTrue, Nat.cast_zero, ENNReal.zero_div]

/-- For the "or" protocol from one `true` agent among two, the hitting time of the all-true
configuration, truncated at one, has expectation one. -/
theorem orProtocol_chainLaw_truncatedHitting :
    ∫⁻ x, (hittingBtwn (ι := ℕ) (fun t (y : ℕ → Config Bool) => y t) {c | AllTrue c} 0 1 x :
      ℝ≥0∞) ∂orProtocol.chainLaw (Config.ofAgents oneTrue) = 1 := by
  rw [← Protocol.costNumerator_div_eq_lintegral_chainLaw orProtocol le_rfl AllTrue oneTrue 1,
    costNumerator_oneTrue]
  rw [show (((2 * (2 - 1) : ℕ) : ℝ≥0∞) ^ 1) = 2 by norm_num, Nat.cast_ofNat]
  exact ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top

end Ripple.PopulationProtocol.ExactMajority
