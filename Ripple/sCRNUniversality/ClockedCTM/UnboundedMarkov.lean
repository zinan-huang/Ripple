import Ripple.sCRNUniversality.ClockedCTM.UnboundedRestart

/-!
# Raw-law restart and standalone phase bounds for SCWB Theorem 4.1

The general raw jump law is identified after a deterministic prefix cut by
finite-prefix agreement and uniqueness of its projective limit. The three
remaining work phases are bounded for the actual standalone work law.
The reducer here retains only volume, actual clock occupation, and tail
finiteness as assumptions; `UnboundedClockOccupation` discharges all three.
-/

noncomputable section

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

private def markovSnoc (n : ℕ)
    (q : (i : Finset.Iic n) → Option N.I) (o : Option N.I) :
    (i : Finset.Iic (n + 1)) → Option N.I :=
  fun i => if hi : i.val ≤ n then
    q ⟨i.val, Finset.mem_Iic.mpr hi⟩ else o

private theorem markovSnoc_restrict (n : ℕ)
    (q : (i : Finset.Iic n) → Option N.I) (o : Option N.I) :
    frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n)
        (markovSnoc N n q o) = q := by
  funext i
  exact dif_pos (Finset.mem_Iic.mp i.property)

private theorem markovSnoc_last (n : ℕ)
    (q : (i : Finset.Iic n) → Option N.I) (o : Option N.I) :
    markovSnoc N n q o ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ = o := by
  simp [markovSnoc]

private theorem markovSnoc_eta (n : ℕ)
    (q : (i : Finset.Iic (n + 1)) → Option N.I) :
    markovSnoc N n
        (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n) q)
        (q ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) = q := by
  funext i
  by_cases hi : i.val ≤ n
  · exact dif_pos hi
  · have heq : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply Subtype.ext
      change i.val = n + 1
      have hib : i.val ≤ n + 1 := Finset.mem_Iic.mp i.property
      omega
    subst i
    rw [markovSnoc_last]

private theorem markovSnoc_eq_glue (n : ℕ)
    (q : (i : Finset.Iic n) → Option N.I) (o : Option N.I) :
    IicProdIoc (X := fun _ => Option N.I) n (n + 1)
        (q, MeasurableEquiv.piSingleton (X := fun _ => Option N.I) n o) =
      markovSnoc N n q o := by
  funext i
  by_cases hi : i.val ≤ n
  · simp [IicProdIoc, markovSnoc, hi]
  · have heq : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply Subtype.ext
      change i.val = n + 1
      have hib : i.val ≤ n + 1 := Finset.mem_Iic.mp i.property
      omega
    subst i
    simp [IicProdIoc, markovSnoc, MeasurableEquiv.piSingleton]

private theorem markov_partialTraj_succ
    (κ : (n : ℕ) →
      Kernel ((i : Finset.Iic n) → Option N.I) (Option N.I))
    [∀ n, IsMarkovKernel (κ n)]
    {a b : ℕ} (hab : a ≤ b)
    (p : (i : Finset.Iic a) → Option N.I)
    (f : ((i : Finset.Iic (b + 1)) → Option N.I) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ q, f q ∂Kernel.partialTraj
        (X := fun _ => Option N.I) κ a (b + 1) p) =
      ∫⁻ q, ∫⁻ o, f (markovSnoc N b q o) ∂κ b q
        ∂Kernel.partialTraj (X := fun _ => Option N.I) κ a b p := by
  rw [Kernel.partialTraj_succ_eq_comp
      (X := fun _ => Option N.I) hab,
    Kernel.lintegral_comp _ _ _ hf]
  apply lintegral_congr
  intro q
  have hglue :
      Measurable (IicProdIoc (X := fun _ => Option N.I) b (b + 1)) :=
    measurable_IicProdIoc
  have hsection :
      Measurable (fun y : (i : Finset.Ioc b (b + 1)) → Option N.I =>
        f (IicProdIoc (X := fun _ => Option N.I) b (b + 1) (q, y))) :=
    (hf.comp hglue).comp (measurable_const.prodMk measurable_id)
  rw [Kernel.partialTraj_succ_self
    (X := fun _ => Option N.I) (κ := κ) b]
  rw [Kernel.lintegral_map _ hglue q hf]
  rw [Kernel.lintegral_id_prod
    (f := fun z => f (IicProdIoc (X := fun _ => Option N.I) b (b + 1) z)) (hf.comp hglue) _ q]
  rw [Kernel.lintegral_map (κ b)
    (MeasurableEquiv.piSingleton (X := fun _ => Option N.I) b).measurable
    q hsection] <;>
    exact lintegral_congr fun o =>
      congrArg f (markovSnoc_eq_glue N b q o)

/-- Prepend the old prefix to a fresh finite prefix. Fresh coordinate zero
is ignored, as it is by the raw state reconstruction. -/
def prependLabelPrefix (cut n : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I)
    (q : (i : Finset.Iic n) → Option N.I) :
    (i : Finset.Iic (cut + n)) → Option N.I :=
  fun i => if hi : i.val ≤ cut then
    p ⟨i.val, Finset.mem_Iic.mpr hi⟩
  else
    q ⟨i.val - cut, Finset.mem_Iic.mpr (by
      have hib : i.val ≤ cut + n := Finset.mem_Iic.mp i.property
      omega)⟩

theorem measurable_prependLabelPrefix (cut n : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I) :
    Measurable (prependLabelPrefix N cut n p) := by
  intro A _
  exact measurableSet_prefixSet N n _

private theorem prependLabelPrefix_zero (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I)
    (q : (i : Finset.Iic 0) → Option N.I) :
    prependLabelPrefix N cut 0 p q = p := by
  funext i
  exact dif_pos (Finset.mem_Iic.mp i.property)

private theorem prependLabelPrefix_snoc (cut n : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I)
    (q : (i : Finset.Iic n) → Option N.I) (o : Option N.I) :
    prependLabelPrefix N cut (n + 1) p (markovSnoc N n q o) =
      markovSnoc N (cut + n) (prependLabelPrefix N cut n p q) o := by
  funext i
  by_cases hc : i.val ≤ cut
  · have hn : i.val ≤ cut + n := by omega
    simp [prependLabelPrefix, markovSnoc, hc, hn]
  · by_cases hn : i.val ≤ cut + n
    · have hr : i.val - cut ≤ n := by omega
      simp [prependLabelPrefix, markovSnoc, hc, hn, hr]
    · have hr : ¬ i.val - cut ≤ n := by omega
      simp [prependLabelPrefix, markovSnoc, hc, hn, hr]

private theorem prefixToState_markovSnoc (z₀ : State S) (n : ℕ)
    (q : (i : Finset.Iic n) → Option N.I) (o : Option N.I) :
    prefixToState N z₀ (n + 1) (markovSnoc N n q o) =
      stateStep N (prefixToState N z₀ n q) o := by
  change stateStep N
      (prefixToState N z₀ n
        (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n)
          (markovSnoc N n q o)))
      (markovSnoc N n q o ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) = _
  rw [markovSnoc_restrict, markovSnoc_last]

/-- State reconstruction commutes with adjoining a fresh label prefix. -/
theorem prefixToState_prependLabelPrefix
    (z₀ : State S) (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I)
    (n : ℕ) (q : (i : Finset.Iic n) → Option N.I) :
    prefixToState N z₀ (cut + n) (prependLabelPrefix N cut n p q) =
      prefixToState N (prefixToState N z₀ cut p) n q := by
  induction n with
  | zero =>
      rw [prependLabelPrefix_zero]
      rfl
  | succ n ih =>
      let r : (i : Finset.Iic n) → Option N.I :=
        frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n) q
      let o : Option N.I := q ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
      have hq : markovSnoc N n r o = q := markovSnoc_eta N n q
      calc
        prefixToState N z₀ (cut + (n + 1))
            (prependLabelPrefix N cut (n + 1) p q) =
            prefixToState N z₀ (cut + (n + 1))
              (prependLabelPrefix N cut (n + 1) p (markovSnoc N n r o)) := by
                rw [hq]
        _ = stateStep N
            (prefixToState N z₀ (cut + n)
              (prependLabelPrefix N cut n p r)) o := by
                rw [prependLabelPrefix_snoc]
                exact prefixToState_markovSnoc (N := N) (z₀ := z₀) (n := cut + n) (q := _) (o := o)
        _ = stateStep N
            (prefixToState N (prefixToState N z₀ cut p) n r) o :=
              congrArg (fun x => stateStep N x o) (ih r)
        _ = prefixToState N (prefixToState N z₀ cut p) (n + 1) q := by
              rw [← prefixToState_markovSnoc, hq]

/-- Naturality of the mass-action step kernel under a deterministic restart. -/
theorem stepKernel_prependLabelPrefix
    (hPos : N.hasPositiveRates) (z₀ : State S) (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I)
    (n : ℕ) (q : (i : Finset.Iic n) → Option N.I) :
    stepKernel N hPos z₀ (cut + n) (prependLabelPrefix N cut n p q) =
      stepKernel N hPos (prefixToState N z₀ cut p) n q := by
  change
    (massActionPMF N hPos
      (prefixToState N z₀ (cut + n) (prependLabelPrefix N cut n p q))).toMeasure =
    (massActionPMF N hPos
      (prefixToState N (prefixToState N z₀ cut p) n q)).toMeasure
  rw [prefixToState_prependLabelPrefix]

private theorem partialTraj_prependLabelPrefix
    (hPos : N.hasPositiveRates) (z₀ : State S) (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I) (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => Option N.I)
      (fun j => stepKernel N hPos (prefixToState N z₀ cut p) j)
      0 n (fun _ => none)).map (prependLabelPrefix N cut n p) =
      Kernel.partialTraj (X := fun _ => Option N.I)
        (fun j => stepKernel N hPos z₀ j) cut (cut + n) p := by
  induction n with
  | zero =>
      simp only [Nat.add_zero, Kernel.partialTraj_self, Kernel.id_apply,
        Measure.map_dirac' (measurable_prependLabelPrefix N cut 0 p),
        prependLabelPrefix_zero]
  | succ n ih =>
      apply Measure.ext_of_lintegral
      intro f hf
      rw [lintegral_map hf (measurable_prependLabelPrefix N cut (n + 1) p)]
      rw [markov_partialTraj_succ N
        (fun j => stepKernel N hPos (prefixToState N z₀ cut p) j)
        (Nat.zero_le n) (fun _ => none) (fun q => f (prependLabelPrefix N cut (n + 1) p q))
        (hf.comp (measurable_prependLabelPrefix N cut (n + 1) p))]
      refine Eq.trans ?_ (markov_partialTraj_succ N
        (fun j => stepKernel N hPos z₀ j)
        (by omega : cut ≤ cut + n) p f hf).symm
      have hnext :
          Measurable
            (fun q : (i : Finset.Iic (cut + n)) → Option N.I =>
              ∫⁻ o, f (markovSnoc N (cut + n) q o)
                ∂stepKernel N hPos z₀ (cut + n) q) := by
        intro A _
        exact measurableSet_prefixSet N (cut + n) _
      rw [← ih, lintegral_map hnext (measurable_prependLabelPrefix N cut n p)]
      apply lintegral_congr
      intro q
      rw [stepKernel_prependLabelPrefix N hPos z₀ cut p n q]
      apply lintegral_congr
      intro o
      rw [prependLabelPrefix_snoc]

private def prependLabels (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I)
    (ω : ℕ → Option N.I) : ℕ → Option N.I :=
  fun j => if hj : j ≤ cut then
    p ⟨j, Finset.mem_Iic.mpr hj⟩ else ω (j - cut)

private theorem measurable_prependLabels (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I) :
    Measurable (prependLabels N cut p) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j ≤ cut
  · simpa only [prependLabels, dif_pos hj] using
      (measurable_const :
        Measurable (fun _ : ℕ → Option N.I =>
          p ⟨j, Finset.mem_Iic.mpr hj⟩))
  · simpa only [prependLabels, dif_neg hj] using
      (measurable_pi_apply (j - cut) :
        Measurable (fun ω : ℕ → Option N.I => ω (j - cut)))

private theorem prependLabels_prefix (cut n : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I) :
    frestrictLe (π := fun _ => Option N.I) (cut + n) ∘ prependLabels N cut p =
      prependLabelPrefix N cut n p ∘
        frestrictLe (π := fun _ => Option N.I) n := by
  funext ω i
  rfl

private theorem rawLaw_prependLabels
    (hPos : N.hasPositiveRates) (z₀ : State S) (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I) :
    (rawLaw N hPos (prefixToState N z₀ cut p)).map (prependLabels N cut p) =
      Kernel.traj (X := fun _ => Option N.I)
        (fun j => stepKernel N hPos z₀ j) cut p := by
  let κ := fun j => stepKernel N hPos z₀ j
  let z := prefixToState N z₀ cut p
  have hfamily :=
    Kernel.isProjectiveMeasureFamily_partialTraj
      (X := fun _ => Option N.I) κ p
  have hsource :
      IsProjectiveLimit
        ((rawLaw N hPos z).map (prependLabels N cut p))
        (inducedFamily (X := fun _ => Option N.I) (fun b =>
          Kernel.partialTraj (X := fun _ => Option N.I) κ cut b p)) := by
    apply (isProjectiveLimit_nat_iff' hfamily _ cut).2
    intro b hb
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hb
    rw [inducedFamily_Iic,
      Measure.map_map
        (measurable_frestrictLe (X := fun _ => Option N.I) (cut + n))
        (measurable_prependLabels N cut p),
      prependLabels_prefix,
      ← Measure.map_map (measurable_prependLabelPrefix N cut n p)
        (measurable_frestrictLe (X := fun _ => Option N.I) n)]
    have hraw : rawLaw N hPos z =
        Kernel.traj (X := fun _ => Option N.I)
          (fun j => stepKernel N hPos z j) 0 (fun _ => none) := rfl
    rw [hraw, Kernel.traj_map_frestrictLe_apply
      (X := fun _ => Option N.I)]
    exact partialTraj_prependLabelPrefix N hPos z₀ cut p n
  haveI : ∀ i, IsFiniteMeasure (inducedFamily (X := fun _ => Option N.I)
      (fun b => Kernel.partialTraj (X := fun _ => Option N.I) κ cut b p) i) := by
    intro i
    unfold inducedFamily
    infer_instance
  exact hsource.unique
    (Kernel.isProjectiveLimit_trajFun
      (X := fun _ => Option N.I) κ cut p)

private theorem restartLabels_prependLabels (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I) :
    restartLabels N cut ∘ prependLabels N cut p =
      (fun ω : ℕ → Option N.I =>
        Function.updateFinset (π := fun _ => Option N.I)
          ω (Finset.Iic 0) (fun _ => none)) := by
  funext ω j
  cases j with
  | zero =>
      simp [Function.comp_def, restartLabels, Function.updateFinset]
  | succ j =>
      have hj : ¬ cut + j + 1 ≤ cut := by omega
      simp [Function.comp_def, restartLabels, prependLabels, hj,
        Function.updateFinset, Nat.add_assoc]

/-- The raw jump law restarts at every deterministic prefix, with the state
computed from that prefix. Coordinate zero is reset to the usual dummy. -/
theorem rawLaw_restartLabels
    (hPos : N.hasPositiveRates) (z₀ : State S) (cut : ℕ)
    (p : (i : Finset.Iic cut) → Option N.I) :
    (Kernel.traj (X := fun _ => Option N.I)
      (fun j => stepKernel N hPos z₀ j) cut p).map (restartLabels N cut) =
      rawLaw N hPos (prefixToState N z₀ cut p) := by
  rw [← rawLaw_prependLabels N hPos z₀ cut p,
    Measure.map_map (measurable_restartLabels N cut)
      (measurable_prependLabels N cut p),
    restartLabels_prependLabels]
  exact Kernel.traj_map_updateFinset
    (X := fun _ => Option N.I)
    (κ := fun j => stepKernel N hPos (prefixToState N z₀ cut p) j)
    (n := 0) (fun _ => none)

end Ripple.sCRNUniversality.Stochastic.MassAction

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The deterministic-cut restart input holds for every XCTM and every state. -/
theorem rawStateRestart (C : XCTM Q) (z₀ : State (Sp C)) :
    RawStateRestart C z₀ := by
  intro cut p
  exact rawLaw_restartLabels (net C) (net_hasPositiveRates C) z₀ cut p

end Ripple.sCRNUniversality.ClockedCTM.Unbounded


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace StandaloneWork

/-- The unit-rate generator restricted to non-clock reactions. -/
noncomputable def workDrift (C : XCTM Q)
    (V : State (Sp C) → ℝ) (x : State (Sp C)) : ℝ :=
  ∑ r : {r : Rx C // isClock r = false},
    (rate C r.val x : ℝ) * (V ((rxn C r.val).fire x) - V x)

theorem workDrift_eq_sum (C : XCTM Q)
    (V : State (Sp C) → ℝ) (x : State (Sp C)) :
    workDrift C V x =
      ∑ r : Rx C, if isClock r = false then
        (rate C r x : ℝ) * (V ((rxn C r).fire x) - V x) else 0 := by
  classical
  rw [workDrift, ← Finset.sum_subtype (p := fun r : Rx C => isClock r = false)
    (Finset.univ.filter (fun r : Rx C => isClock r = false))
    (by simp) (fun r : Rx C => (rate C r x : ℝ) * (V ((rxn C r).fire x) - V x))]
  exact Finset.sum_filter _ _

theorem workDrift_eq_sum_of_enabled_subset (C : XCTM Q)
    (V : State (Sp C) → ℝ) (x : State (Sp C))
    (allowed : Finset (Rx C))
    (hclock : ∀ r ∈ allowed, isClock r = false)
    (hcover : ∀ r, isClock r = false → (rxn C r).enabled x → r ∈ allowed) :
    workDrift C V x =
      ∑ r ∈ allowed, (rate C r x : ℝ) * (V ((rxn C r).fire x) - V x) := by
  classical
  rw [workDrift, ← Finset.sum_subtype (p := fun r : Rx C => isClock r = false)
    (Finset.univ.filter (fun r : Rx C => isClock r = false))
    (by simp) (fun r : Rx C => (rate C r x : ℝ) * (V ((rxn C r).fire x) - V x))]
  symm
  apply Finset.sum_subset
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hclock r hr⟩
  · intro r hr hnot
    have hz : rate C r x = 0 := by
      by_contra hne
      exact hnot (hcover r (Finset.mem_filter.mp hr).2
        ((enabled_iff C r x).mpr hne))
    simp only [hz, Nat.cast_zero, zero_mul]

theorem workDrift_le_sum (C : XCTM Q)
    (V : State (Sp C) → ℝ) (x : State (Sp C))
    (hmono : ∀ r, isClock r = false → (rxn C r).enabled x →
      V ((rxn C r).fire x) ≤ V x)
    (allowed : Finset (Rx C)) :
    workDrift C V x ≤
      ∑ r ∈ allowed, if isClock r = false then
        (rate C r x : ℝ) * (V ((rxn C r).fire x) - V x) else 0 := by
  classical
  rw [workDrift_eq_sum, ← Finset.sum_add_sum_compl allowed]
  have hn :
      (∑ r ∈ allowedᶜ, if isClock r = false then
        (rate C r x : ℝ) * (V ((rxn C r).fire x) - V x) else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro r _
    split_ifs with hc
    · by_cases hr : rate C r x = 0
      · simp only [hr, Nat.cast_zero, zero_mul, le_refl]
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
          (sub_nonpos.mpr (hmono r hc ((enabled_iff C r x).mpr hr)))
    · exact le_refl _
  linarith

theorem work_stateStep_of_rate (C : XCTM Q) (x : State (Sp C))
    (r : (workNet C).I) (hr : rate C r.val x ≠ 0) :
    stateStep (workNet C) x (some r) = (rxn C r.val).fire x := by
  have he : (workNet C).EnabledAt x r := (enabled_iff C r.val x).mpr hr
  have ht : ¬ (workNet C).Terminal x := fun h => h r he
  rw [stateStep, dif_neg ht,
    fireOptionSanitized_of_enabled (workNet C) x r ht he]
  rfl

theorem work_pmf_none (C : XCTM Q) (x : State (Sp C))
    (ht : ¬ WorkTerminal C x) :
    massActionPMF (workNet C) (workNet_hasPositiveRates C) x none = 0 := by
  have ht' : ¬ (workNet C).Terminal x :=
    fun h => ht ((workNet_terminal_iff C x).mp h)
  change massActionWeight (workNet C) (workNet_hasPositiveRates C) x none = 0
  simp only [massActionWeight, ht', dite_false]

theorem work_pmf_some (C : XCTM Q) (x : State (Sp C))
    (ht : ¬ WorkTerminal C x) (r : (workNet C).I) :
    massActionPMF (workNet C) (workNet_hasPositiveRates C) x (some r) =
      (rate C r.val x : ℝ≥0∞) / (totalWorkRate C x : ℝ≥0∞) := by
  have ht' : ¬ (workNet C).Terminal x :=
    fun h => ht ((workNet_terminal_iff C x).mp h)
  have hB : (totalWorkRate C x : NNReal) ≠ 0 := by
    exact_mod_cast (totalWorkRate_pos C x ht).ne'
  change massActionWeight (workNet C) (workNet_hasPositiveRates C) x (some r) = _
  simp only [massActionWeight, ht', dite_false]
  rw [jumpProbAt, show (workNet C).rxn r = rxn C r.val from rfl,
    propensity_rxn, workNet_totalPropensity, ← ENNReal.coe_nnratCast,
    NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    ENNReal.coe_div hB, ENNReal.coe_natCast, ENNReal.coe_natCast]
  rfl

/-- Convert the real generator inequality to the exact standalone PMF drift. -/
theorem work_drift_real (C : XCTM Q) (x : State (Sp C))
    (ht : ¬ WorkTerminal C x) {cost : ℝ≥0∞}
    {Pn : Option (workNet C).I → ℝ≥0∞} {p c : ℝ}
    {pn : (workNet C).I → ℝ}
    (hcost : cost = ENNReal.ofReal c / (totalWorkRate C x : ℝ≥0∞))
    (hc : 0 ≤ c)
    (hPn : ∀ r, rate C r.val x ≠ 0 → Pn (some r) ≤ ENNReal.ofReal (pn r))
    (hpn : ∀ r, 0 ≤ pn r)
    (h : c + ∑ r : (workNet C).I,
      (rate C r.val x : ℝ) * (pn r - p) ≤ 0) :
    cost + ∑ o : Option (workNet C).I,
      massActionPMF (workNet C) (workNet_hasPositiveRates C) x o * Pn o ≤
        ENNReal.ofReal p := by
  have hB : (0 : ℝ) < totalWorkRate C x := by
    exact_mod_cast totalWorkRate_pos C x ht
  rw [Fintype.sum_option, work_pmf_none C x ht, zero_mul, zero_add]
  have hterm : ∀ r : (workNet C).I,
      massActionPMF (workNet C) (workNet_hasPositiveRates C) x (some r) *
        Pn (some r) ≤
          ENNReal.ofReal ((rate C r.val x : ℝ) * pn r / totalWorkRate C x) := by
    intro r
    rw [work_pmf_some C x ht r]
    by_cases hr : rate C r.val x = 0
    · simp [hr]
    · calc
        (rate C r.val x : ℝ≥0∞) / (totalWorkRate C x : ℝ≥0∞) * Pn (some r)
            ≤ (rate C r.val x : ℝ≥0∞) / (totalWorkRate C x : ℝ≥0∞) *
              ENNReal.ofReal (pn r) := by
                gcongr
                exact hPn r hr
        _ = ENNReal.ofReal ((rate C r.val x : ℝ) * pn r / totalWorkRate C x) := by
          rw [ENNReal.ofReal_div_of_pos hB,
            ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
          simp only [div_eq_mul_inv]
          ring
  have hnn : ∀ r : (workNet C).I,
      0 ≤ (rate C r.val x : ℝ) * pn r / totalWorkRate C x :=
    fun r => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpn r)) hB.le
  calc
    cost + ∑ r : (workNet C).I,
        massActionPMF (workNet C) (workNet_hasPositiveRates C) x (some r) *
          Pn (some r)
        ≤ ENNReal.ofReal (c / totalWorkRate C x) +
          ∑ r : (workNet C).I,
            ENNReal.ofReal ((rate C r.val x : ℝ) * pn r / totalWorkRate C x) := by
          rw [hcost, ENNReal.ofReal_div_of_pos hB, ENNReal.ofReal_natCast]
          gcongr with r
          exact hterm r
    _ = ENNReal.ofReal
        (c / totalWorkRate C x +
          ∑ r : (workNet C).I, (rate C r.val x : ℝ) * pn r / totalWorkRate C x) := by
      rw [ENNReal.ofReal_add (div_nonneg hc hB.le)
        (Finset.sum_nonneg fun r _ => hnn r),
        ENNReal.ofReal_sum_of_nonneg fun r _ => hnn r]
    _ ≤ ENNReal.ofReal p := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.sum_div, ← add_div, div_le_iff₀ hB]
      have hsum :
          (∑ r : (workNet C).I, (rate C r.val x : ℝ) * pn r) =
            (∑ r : (workNet C).I, (rate C r.val x : ℝ) * (pn r - p)) +
              (totalWorkRate C x : ℝ) * p := by
        have h2 : (totalWorkRate C x : ℝ) * p =
            ∑ r : (workNet C).I, (rate C r.val x : ℝ) * p := by
          rw [totalWorkRate, Nat.cast_sum, Finset.sum_mul]
          rfl
        rw [h2, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hsum]
      linarith

theorem meanDuration_le_of_certificate_generator (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    (V : State (Sp C) → ℝ)
    (hnonneg : ∀ x, P.inv x → 0 ≤ V x)
    (hdrift : ∀ x, P.inv x → ¬ WorkTerminal C x → workDrift C V x ≤ -1) :
    meanDuration C start ≤ ENNReal.ofReal (V start) := by
  classical
  apply meanDuration_le_of_certificate_drift C P (fun x => ENNReal.ofReal (V x))
  intro x hx
  by_cases ht : WorkTerminal C x
  · rw [holdingMean, if_pos ht, zero_add]
    simp_rw [stateStep_of_terminal C x _ ht]
    rw [← Finset.sum_mul]
    have hs :
        (∑ o, massActionPMF (workNet C) (workNet_hasPositiveRates C) x o) = 1 :=
      massActionWeight_sum_eq_one (workNet C) (workNet_hasPositiveRates C) x
    rw [hs, one_mul] <;> exact le_rfl
  · apply work_drift_real C x ht
      (c := 1) (p := V x) (pn := fun r => max (V ((rxn C r.val).fire x)) 0)
    · simp [holdingMean, ht, one_div]
    · norm_num
    · intro r hr
      rw [work_stateStep_of_rate C x r hr]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    · intro r
      exact le_max_right _ _
    · have hs :
          (∑ r : (workNet C).I, (rate C r.val x : ℝ) *
            (max (V ((rxn C r.val).fire x)) 0 - V x)) = workDrift C V x := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : rate C r.val x = 0
        · simp only [hr, Nat.cast_zero, zero_mul]
        · have hv := hnonneg _ (P.closed _ _ hx
            ⟨r.val, r.property, (enabled_iff C r.val x).mpr hr, rfl⟩)
          rw [max_eq_left hv]
      rw [hs]
      linarith [hdrift x hx ht]

end StandaloneWork

end Ripple.sCRNUniversality.ClockedCTM.Unbounded


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork

open Stochastic Stochastic.MassAction
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

def restoreConversionLabels (C : XCTM Q) (q : ActiveState C) : Finset (Rx C) :=
  {.restoreM q, .restoreT q, .restoreD q, .restoreB q,
    .restoreForward q, .restoreBackward q}

def restorePendingCount (C : XCTM Q) (x : State (Sp C)) : ℕ :=
  x (.mem .md) + x (.mem .td) + x (.mem .ds) + x (.mem .bs) +
    x .forwardLatent + x .backwardLatent

def restoreComparisonCount (C : XCTM Q) (x : State (Sp C)) : ℕ :=
  min (x (.mem .m) + x (.mem .md)) (x (.mem .t) + x (.mem .td))

noncomputable def restoreTransitionPotential (C : XCTM Q) (q : ActiveState C)
    (d : ℕ) (x : State (Sp C)) : ℝ :=
  (if x .signal = 1 then 1 / (d : ℝ) else 0) +
    aut d (max (x (.second q)) 1)

/-- Restoration and comparison are charged even when they overlap the
control transition. Every extra work channel is nonincreasing for this sum. -/
noncomputable def restorePotential (C : XCTM Q) (q : ActiveState C)
    (d g : ℕ) (x : State (Sp C)) : ℝ :=
  restoreTransitionPotential C q d x +
    hrm (restorePendingCount C x) / (d : ℝ) +
    hrm (restoreComparisonCount C x) / (g : ℝ)

theorem restorePotential_nonneg (C : XCTM Q) (q : ActiveState C)
    (d g : ℕ) (x : State (Sp C)) : 0 ≤ restorePotential C q d g x := by
  unfold restorePotential restoreTransitionPotential
  have ht : 0 ≤ (if x .signal = 1 then 1 / (d : ℝ) else 0) := by
    split_ifs <;> positivity
  exact add_nonneg
    (add_nonneg (add_nonneg ht (aut_nonneg _ _))
      (div_nonneg (hrm_nonneg _) (Nat.cast_nonneg _)))
    (div_nonneg (hrm_nonneg _) (Nat.cast_nonneg _))

private theorem restore_reaction_cases (C : XCTM Q)
    {q : ActiveState C} {d T v a : ℕ} {x : State (Sp C)} {r : Rx C}
    (hx : RestoreWindow C q d T v a x)
    (hc : isClock r = false) (he : (rxn C r).enabled x) :
    r = .startSecond q ∨ r = .growSecond q ∨
      r ∈ restoreConversionLabels C q ∨ r = .pair := by
  have h := restore_enabled_at C hx hc he
  cases r <;> simp_all [RestoreAt, restoreConversionLabels]

private theorem restore_seed_data (C : XCTM Q) (q : ActiveState C)
    (x : State (Sp C)) :
    (rxn C (.startSecond q)).fire x .signal = x .signal - 1 ∧
      (rxn C (.startSecond q)).fire x (.second q) = x (.second q) + 1 ∧
      restorePendingCount C ((rxn C (.startSecond q)).fire x) =
        restorePendingCount C x ∧
      restoreComparisonCount C ((rxn C (.startSecond q)).fire x) =
        restoreComparisonCount C x := by
  simp [restorePendingCount, restoreComparisonCount, fire_apply,
    sourceLeft, sourceRight, products, unit]

private theorem restore_grow_data (C : XCTM Q) (q : ActiveState C)
    (x : State (Sp C)) :
    (rxn C (.growSecond q)).fire x .signal = x .signal ∧
      (rxn C (.growSecond q)).fire x (.second q) = x (.second q) - 1 + 2 ∧
      restorePendingCount C ((rxn C (.growSecond q)).fire x) =
        restorePendingCount C x ∧
      restoreComparisonCount C ((rxn C (.growSecond q)).fire x) =
        restoreComparisonCount C x := by
  simp [restorePendingCount, restoreComparisonCount, fire_apply,
    sourceLeft, sourceRight, products, unit, Pi.smul_apply]

-- Six concrete reactions are expanded; the budget is local to this enumeration.
set_option maxHeartbeats 600000 in
private theorem restore_conversion_data (C : XCTM Q) (q : ActiveState C)
    (x : State (Sp C)) (r : Rx C)
    (hr : r ∈ restoreConversionLabels C q) (he : (rxn C r).enabled x) :
    (rxn C r).fire x .signal = x .signal ∧
      (rxn C r).fire x (.second q) = x (.second q) ∧
      restorePendingCount C ((rxn C r).fire x) + 1 =
        restorePendingCount C x ∧
      restoreComparisonCount C ((rxn C r).fire x) =
        restoreComparisonCount C x := by
  have hp := (enabled_iff C r x).mp he
  simp only [restoreConversionLabels, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rate, sourceLeft, sourceRight, ne_eq, mul_eq_zero, not_or] at hp <;>
    simp_all [restorePendingCount, restoreComparisonCount, fire_apply,
      sourceLeft, sourceRight, products, unit, Pi.smul_apply] <;> omega

private theorem restore_pair_data (C : XCTM Q) (q : ActiveState C)
    (x : State (Sp C)) (he : (rxn C .pair).enabled x) :
    (rxn C .pair).fire x .signal = x .signal ∧
      (rxn C .pair).fire x (.second q) = x (.second q) ∧
      restorePendingCount C ((rxn C .pair).fire x) =
        restorePendingCount C x ∧
      restoreComparisonCount C ((rxn C .pair).fire x) + 1 =
        restoreComparisonCount C x := by
  have hp := (enabled_iff C .pair x).mp he
  simp only [rate, sourceLeft, sourceRight, ne_eq, mul_eq_zero, not_or] at hp
  simp [restorePendingCount, restoreComparisonCount, fire_apply,
    sourceLeft, sourceRight, products, unit] <;> omega

private theorem restore_seed_potential (C : XCTM Q)
    {q : ActiveState C} {d T v a g : ℕ} {x : State (Sp C)}
    (hx : RestoreWindow C q d T v a x)
    (he : (rxn C (.startSecond q)).enabled x) :
    restorePotential C q d g x =
      1 / (rate C (.startSecond q) x : ℝ) +
        restorePotential C q d g ((rxn C (.startSecond q)).fire x) := by
  have ho := restore_seed_data C q x
  have hp := (enabled_iff C (.startSecond q) x).mp he
  simp only [rate, sourceLeft, sourceRight, ne_eq, mul_eq_zero, not_or] at hp
  rcases hx with ⟨_, hcount, hsignal, hprogress, hexclusive, _, _⟩
  have hs : x .signal = 1 := by omega
  have hn : x (.second q) = 0 := by omega
  have hold : x (.first (activeControl C q)) = d := by omega
  have hs' : (rxn C (.startSecond q)).fire x .signal = 0 := by
    rw [ho.1, hs]
  have hn' : (rxn C (.startSecond q)).fire x (.second q) = 1 := by
    rw [ho.2.1, hn]
  unfold restorePotential restoreTransitionPotential
  rw [ho.2.2.1, ho.2.2.2, hs', hn', hs, hn]
  simp only [rate, sourceLeft, sourceRight, hs, hold, one_mul]
  norm_num <;> ring

private theorem restore_grow_potential (C : XCTM Q)
    {q : ActiveState C} {d T v a g : ℕ} {x : State (Sp C)}
    (hx : RestoreWindow C q d T v a x)
    (he : (rxn C (.growSecond q)).enabled x) :
    restorePotential C q d g x =
      1 / (rate C (.growSecond q) x : ℝ) +
        restorePotential C q d g ((rxn C (.growSecond q)).fire x) := by
  have ho := restore_grow_data C q x
  have hp := (enabled_iff C (.growSecond q) x).mp he
  simp only [rate, sourceLeft, sourceRight, ne_eq, mul_eq_zero, not_or] at hp
  rcases hx with ⟨_, hcount, hsignal, hprogress, hexclusive, _, _⟩
  have hn : 1 ≤ x (.second q) := Nat.one_le_iff_ne_zero.mpr hp.2
  have hs : x .signal = 0 := by omega
  have hlt : x (.second q) < d := by omega
  have hold : x (.first (activeControl C q)) = d - x (.second q) := by omega
  have hs' : (rxn C (.growSecond q)).fire x .signal = 0 := by rw [ho.1, hs]
  have hn' : (rxn C (.growSecond q)).fire x (.second q) = x (.second q) + 1 := by
    rw [ho.2.1]
    omega
  have hr : (rate C (.growSecond q) x : ℝ) =
      (x (.second q) : ℝ) * ((d : ℝ) - x (.second q)) := by
    rw [rate, sourceLeft, sourceRight, Nat.cast_mul, hold, Nat.cast_sub hlt.le]
    ring
  unfold restorePotential restoreTransitionPotential
  rw [ho.2.2.1, ho.2.2.2, hs', hn', hs, hr]
  have hau := aut_eq_add hlt
  simp only [show ¬ (0 : ℕ) = 1 by omega, if_false, zero_add,
    max_eq_left hn, max_eq_left (show 1 ≤ x (.second q) + 1 by omega)]
  linarith

private theorem restore_conversion_change (C : XCTM Q) (q : ActiveState C)
    (d g : ℕ) (x : State (Sp C)) (r : Rx C)
    (hr : r ∈ restoreConversionLabels C q) (he : (rxn C r).enabled x) :
    restorePotential C q d g ((rxn C r).fire x) - restorePotential C q d g x =
      -(1 / ((restorePendingCount C x : ℝ) * d)) := by
  have ho := restore_conversion_data C q x r hr he
  simp only [restorePotential, restoreTransitionPotential, ho.1, ho.2.1, ho.2.2.2]
  rw [← ho.2.2.1, hrm_succ]
  simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem restore_pair_change (C : XCTM Q) (q : ActiveState C)
    (d g : ℕ) (x : State (Sp C)) (he : (rxn C .pair).enabled x) :
    restorePotential C q d g ((rxn C .pair).fire x) - restorePotential C q d g x =
      -(1 / ((restoreComparisonCount C x : ℝ) * g)) := by
  have ho := restore_pair_data C q x he
  simp only [restorePotential, restoreTransitionPotential, ho.1, ho.2.1, ho.2.2.1]
  rw [← ho.2.2.2, hrm_succ]
  simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
  ring

theorem restorePotential_nonincreasing (C : XCTM Q)
    {q : ActiveState C} {d T v a g : ℕ} {x : State (Sp C)}
    (hx : RestoreWindow C q d T v a x)
    (r : Rx C) (hc : isClock r = false) (he : (rxn C r).enabled x) :
    restorePotential C q d g ((rxn C r).fire x) ≤ restorePotential C q d g x := by
  rcases restore_reaction_cases C hx hc he with rfl | rfl | hr | rfl
  · have h := restore_seed_potential C (g := g) hx he
    have hn : (0 : ℝ) ≤ 1 / (rate C (.startSecond q) x : ℝ) := by positivity
    linarith
  · have h := restore_grow_potential C (g := g) hx he
    have hn : (0 : ℝ) ≤ 1 / (rate C (.growSecond q) x : ℝ) := by positivity
    linarith
  · apply sub_nonpos.mp
    rw [restore_conversion_change C q d g x r hr he]
    exact neg_nonpos.mpr (by positivity)
  · apply sub_nonpos.mp
    rw [restore_pair_change C q d g x he]
    exact neg_nonpos.mpr (by positivity)

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork

open Stochastic Stochastic.MassAction
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

private theorem workDrift_le_neg_one_of_reaction (C : XCTM Q)
    (V : State (Sp C) → ℝ) (x : State (Sp C))
    (hmono : ∀ r, isClock r = false → (rxn C r).enabled x →
      V ((rxn C r).fire x) ≤ V x)
    (r : Rx C) (hc : isClock r = false) (he : (rxn C r).enabled x)
    (hdrop : V x = 1 / (rate C r x : ℝ) + V ((rxn C r).fire x)) :
    workDrift C V x ≤ -1 := by
  have hrate : (rate C r x : ℝ) ≠ 0 := by
    exact_mod_cast (enabled_iff C r x).mp he
  have hdelta : V ((rxn C r).fire x) - V x = -(1 / (rate C r x : ℝ)) := by
    linarith
  refine (workDrift_le_sum C V x hmono {r}).trans ?_
  rw [Finset.sum_singleton, if_pos hc, hdelta,
    mul_neg, mul_one_div_cancel hrate]

private theorem restore_terminal_of_empty (C : XCTM Q)
    {q : ActiveState C} {d T v a : ℕ} {x : State (Sp C)}
    (hd : 0 < d) (hx : RestoreWindow C q d T v a x)
    (hnew : x (.second q) = d) (hy : restorePendingCount C x = 0)
    (hu : restoreComparisonCount C x = 0) : WorkTerminal C x := by
  have hwin := hx
  rcases hx with ⟨_, hcount, _, _, hexclusive, _, _⟩
  have hold : x (.first (activeControl C q)) = 0 := by omega
  have hsignal : x .signal = 0 := by omega
  intro r hc he
  rcases restore_reaction_cases C hwin hc he with rfl | rfl | hr | rfl
  · exact ((enabled_iff C (.startSecond q) x).mp he)
      (by simp [rate, sourceLeft, sourceRight, hsignal])
  · exact ((enabled_iff C (.growSecond q) x).mp he)
      (by simp [rate, sourceLeft, sourceRight, hold])
  · have h := (restore_conversion_data C q x r hr he).2.2.1
    omega
  · have h := (restore_pair_data C q x he).2.2.2
    omega

private theorem restore_conversions_generator (C : XCTM Q)
    {q : ActiveState C} {d g : ℕ} {x : State (Sp C)}
    (hd : 0 < d) (hnew : x (.second q) = d)
    (hy : 0 < restorePendingCount C x) :
    (∑ r ∈ restoreConversionLabels C q, if isClock r = false then
      (rate C r x : ℝ) *
        (restorePotential C q d g ((rxn C r).fire x) -
          restorePotential C q d g x) else 0) = -1 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hyr : (0 : ℝ) < restorePendingCount C x := by exact_mod_cast hy
  have key (r : Rx C) (s : Sp C)
      (hr : r ∈ restoreConversionLabels C q)
      (hc : isClock r = false)
      (hl : sourceLeft C r = .second q) (hs : sourceRight C r = s) :
      (if isClock r = false then (rate C r x : ℝ) *
        (restorePotential C q d g ((rxn C r).fire x) -
          restorePotential C q d g x) else 0) =
          -(x s : ℝ) / restorePendingCount C x := by
    rw [if_pos hc]
    by_cases hz : x s = 0
    · simp [rate, hl, hs, hz]
    · have he : (rxn C r).enabled x := by
        apply (enabled_iff C r x).mpr
        simp only [rate, hl, hs, hnew]
        exact mul_ne_zero (Nat.ne_of_gt hd) hz
      rw [restore_conversion_change C q d g x r hr he,
        rate, hl, hs, hnew, Nat.cast_mul]
      field_simp [hdr.ne', hyr.ne'] <;> ring
  rw [restoreConversionLabels, Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [key (.restoreM q) (.mem .md) (by simp [restoreConversionLabels]) rfl rfl rfl,
    key (.restoreT q) (.mem .td) (by simp [restoreConversionLabels]) rfl rfl rfl,
    key (.restoreD q) (.mem .ds) (by simp [restoreConversionLabels]) rfl rfl rfl,
    key (.restoreB q) (.mem .bs) (by simp [restoreConversionLabels]) rfl rfl rfl,
    key (.restoreForward q) .forwardLatent (by simp [restoreConversionLabels]) rfl rfl rfl,
    key (.restoreBackward q) .backwardLatent (by simp [restoreConversionLabels]) rfl rfl rfl]
  have hsum :
      (x (.mem .md) : ℝ) + x (.mem .td) + x (.mem .ds) + x (.mem .bs) +
        x .forwardLatent + x .backwardLatent = restorePendingCount C x := by
    simp only [restorePendingCount, Nat.cast_add]
  field_simp [hyr.ne'] <;> linarith

theorem restorePotential_drift (C : XCTM Q)
    {q : ActiveState C} {d T v a g : ℕ} {x : State (Sp C)}
    (hd : 0 < d) (hg : 0 < g)
    (hgap : v + g ≤ T ∨ T + g ≤ v)
    (hx : RestoreWindow C q d T v a x) (ht : ¬ WorkTerminal C x) :
    workDrift C (restorePotential C q d g) x ≤ -1 := by
  have hmono := restorePotential_nonincreasing C (g := g) hx
  have hwin := hx
  rcases hx with ⟨_, hcount, hsignal, hprogress, hexclusive, hmem, _⟩
  by_cases hs : x .signal = 1
  · have hzero : x (.second q) = 0 := by omega
    have hold : x (.first (activeControl C q)) = d := by omega
    have he : (rxn C (.startSecond q)).enabled x := by
      rw [enabled_iff, rate, sourceLeft, sourceRight, hs, hold, one_mul]
      exact Nat.ne_of_gt hd
    exact workDrift_le_neg_one_of_reaction C _ x hmono _ rfl he
      (restore_seed_potential C hwin he)
  · have hs' : x .signal = 0 := by omega
    have hn : 0 < x (.second q) := by omega
    by_cases hlt : x (.second q) < d
    · have hold : 0 < x (.first (activeControl C q)) := by omega
      have he : (rxn C (.growSecond q)).enabled x := by
        rw [enabled_iff, rate, sourceLeft, sourceRight]
        exact mul_ne_zero (Nat.ne_of_gt hold) (Nat.ne_of_gt hn)
      exact workDrift_le_neg_one_of_reaction C _ x hmono _ rfl he
        (restore_grow_potential C hwin he)
    · have hnew : x (.second q) = d := by omega
      by_cases hy : 0 < restorePendingCount C x
      · exact (workDrift_le_sum C _ x hmono (restoreConversionLabels C q)).trans_eq
          (restore_conversions_generator C hd hnew hy)
      · have hyzero : restorePendingCount C x = 0 := by omega
        have hup : 0 < restoreComparisonCount C x := by
          by_contra h
          exact ht (restore_terminal_of_empty C hd hwin hnew hyzero (by omega))
        have hmd : x (.mem .md) = 0 := by
          unfold restorePendingCount at hyzero
          omega
        have htd : x (.mem .td) = 0 := by
          unfold restorePendingCount at hyzero
          omega
        have hmin : 0 < min (x (.mem .m)) (x (.mem .t)) := by
          simpa only [restoreComparisonCount, hmd, htd, Nat.add_zero] using hup
        have hmpos : 0 < x (.mem .m) :=
          lt_of_lt_of_le hmin (min_le_left _ _)
        have htpos : 0 < x (.mem .t) :=
          lt_of_lt_of_le hmin (min_le_right _ _)
        have he : (rxn C .pair).enabled x := by
          rw [enabled_iff, rate, sourceLeft, sourceRight]
          exact mul_ne_zero (Nat.ne_of_gt htpos) (Nat.ne_of_gt hmpos)
        have hmemM : x (.mem .m) + x (.mem .ms) + x (.mem .md) = v := hmem.1
        have hmemT : x (.mem .t) + x (.mem .ts) + x (.mem .td) = T := hmem.2.1
        have hstars : x (.mem .ms) = x (.mem .ts) := hmem.2.2.1
        have hrate : restoreComparisonCount C x * g ≤ rate C .pair x := by
          simp only [restoreComparisonCount, hmd, htd, Nat.add_zero,
            rate, sourceLeft, sourceRight]
          rcases hgap with hgap | hgap
          · have hmt : x (.mem .m) ≤ x (.mem .t) := by omega
            have hgt : g ≤ x (.mem .t) := by omega
            rw [min_eq_left hmt, Nat.mul_comm (x (.mem .t))]
            exact Nat.mul_le_mul_left _ hgt
          · have htm : x (.mem .t) ≤ x (.mem .m) := by omega
            have hgm : g ≤ x (.mem .m) := by omega
            rw [min_eq_right htm]
            exact Nat.mul_le_mul_left _ hgm
        have hrateReal :
            (restoreComparisonCount C x : ℝ) * g ≤ (rate C .pair x : ℝ) := by
          exact_mod_cast hrate
        have hden : (0 : ℝ) < (restoreComparisonCount C x : ℝ) * g := by
          exact_mod_cast Nat.mul_pos hup hg
        have hquot : 1 ≤ (rate C .pair x : ℝ) /
            ((restoreComparisonCount C x : ℝ) * g) :=
          (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hrateReal)
        refine (workDrift_le_sum C _ x hmono {.pair}).trans ?_
        rw [Finset.sum_singleton, if_pos (show isClock (.pair : Rx C) = false from rfl),
          restore_pair_change C q d g x he]
        calc
          (rate C .pair x : ℝ) * -(1 / ((restoreComparisonCount C x : ℝ) * g)) =
              -((rate C .pair x : ℝ) / ((restoreComparisonCount C x : ℝ) * g)) := by ring
          _ ≤ -1 := neg_le_neg hquot

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork

/-- The harmonic W2 restoration budget fits the uniform §13 work bound. -/
theorem restore_harmonic_budget (s a : ℕ) (hs : 3 ≤ s) :
    1 / (stateCount s : ℝ) + aut (stateCount s) 1 +
        hrm ((a + 9) * stateCount s) / (stateCount s : ℝ) +
        hrm (3 * stateCount s) / ((2 * 3 ^ (s - 3) : ℕ) : ℝ) ≤
      workDurationBound s a := by
  let d : ℕ := stateCount s
  let g : ℕ := 2 * 3 ^ (s - 3)
  have hdNat : 0 < d := by
    dsimp [d, stateCount]
    positivity
  have hgNat : 0 < g := by
    dsimp [g]
    positivity
  have hd : (0 : ℝ) < d := by exact_mod_cast hdNat
  have hg : (0 : ℝ) < g := by exact_mod_cast hgNat
  have hsreal : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hareal : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hrelationNat : 2 * d = 9 * g := by
    dsimp [d, g, stateCount]
    rw [show s - 1 = (s - 3) + 2 by omega, pow_add]
    ring
  have hrelation : 2 * (d : ℝ) = 9 * (g : ℝ) := by
    exact_mod_cast hrelationNat
  have hgEq : (g : ℝ) = 2 * (d : ℝ) / 9 := by
    linarith
  have hlogthree : Real.log (3 : ℝ) ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 3 by norm_num)]
  have hlogd : Real.log (d : ℝ) ≤ 2 * ((s : ℝ) - 1) := by
    rw [show (d : ℝ) = (3 : ℝ) ^ (s - 1) by
      simp only [d, stateCount, Nat.cast_pow, Nat.cast_ofNat],
      Real.log_pow,
      Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    have hnonneg : (0 : ℝ) ≤ (s : ℝ) - 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlogthree hnonneg
    nlinarith
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hloga : (1 / 2 : ℝ) ≤ Real.log ((a : ℝ) + 2) :=
    hlogtwo.trans
      (Real.log_le_log (by norm_num) (by linarith))
  have hlogaNine :
      Real.log ((a : ℝ) + 9) ≤
        Real.log ((a : ℝ) + 2) + (7 / 2 : ℝ) := by
    have hmul :
        (a : ℝ) + 9 ≤ ((a : ℝ) + 2) * (9 / 2 : ℝ) := by
      nlinarith
    have h :=
      Real.log_le_log (by positivity : (0 : ℝ) < (a : ℝ) + 9) hmul
    rw [Real.log_mul (by positivity) (by norm_num)] at h
    have hc : Real.log (9 / 2 : ℝ) ≤ (7 / 2 : ℝ) := by
      have hbase := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 9 / 2 by norm_num)
      linarith
    linarith
  have haut :
      (d : ℝ) * aut d 1 ≤ 2 * (1 + Real.log (d : ℝ)) :=
    (mul_aut_one_le d).trans
      (mul_le_mul_of_nonneg_left (hrm_le_log d) (by norm_num))
  have hlarge :
      hrm ((a + 9) * d) ≤
        1 + Real.log ((a : ℝ) + 2) + (7 / 2 : ℝ) +
          Real.log (d : ℝ) := by
    have h := hrm_le_log ((a + 9) * d)
    rw [Nat.cast_mul, Real.log_mul (by positivity) hd.ne'] at h
    simp only [Nat.cast_add, Nat.cast_ofNat] at h
    linarith
  have hsmall :
      hrm (3 * d) ≤ 1 + Real.log (3 : ℝ) + Real.log (d : ℝ) := by
    have h := hrm_le_log (3 * d)
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num) hd.ne'] at h
    linarith
  have hnum :
      1 + (d : ℝ) * aut d 1 + hrm ((a + 9) * d) +
          (9 / 2 : ℝ) * hrm (3 * d) ≤
        16 * ((s : ℝ) + Real.log ((a : ℝ) + 2)) := by
    nlinarith [haut, hlarge, hsmall, hlogd, hlogthree, hloga]
  have hfraction :
      1 / (d : ℝ) + aut d 1 +
          hrm ((a + 9) * d) / (d : ℝ) +
          hrm (3 * d) / (g : ℝ) =
        (1 + (d : ℝ) * aut d 1 + hrm ((a + 9) * d) +
          (9 / 2 : ℝ) * hrm (3 * d)) / (d : ℝ) := by
    rw [hgEq]
    field_simp [hd.ne'] <;> ring
  change
    1 / (d : ℝ) + aut d 1 +
        hrm ((a + 9) * d) / (d : ℝ) +
        hrm (3 * d) / (g : ℝ) ≤
      (16 * ((s : ℝ) + Real.log ((a : ℝ) + 2))) / (d : ℝ)
  rw [hfraction]
  exact div_le_div_of_nonneg_right hnum hd.le

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork

open Stochastic Stochastic.MassAction
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

theorem restorePotential_initial_le (C : XCTM Q) (q : ActiveState C)
    (w : List Bool) (a : ℕ) (latent : Bool) (hs : 3 ≤ w.length) :
    restorePotential C q (stateCount w.length) (2 * 3 ^ (w.length - 3))
        (Plan.workState C (.first (activeControl C q) w a latent) + unit .signal) ≤
      1 / (stateCount w.length : ℝ) + aut (stateCount w.length) 1 +
        hrm ((a + 9) * stateCount w.length) / (stateCount w.length : ℝ) +
        hrm (3 * stateCount w.length) /
          ((2 * 3 ^ (w.length - 3) : ℕ) : ℝ) := by
  let d := stateCount w.length
  let start := Plan.workState C (.first (activeControl C q) w a latent) + unit .signal
  have hd : 0 < d := by
    dsimp [d, stateCount]
    positivity
  have hv : tval w < 3 * d := by
    have h := (tape_facts (n := w.length - 3) (w := w) (by omega) false).2.2.2.2.2
    simpa only [d, stateCount_eq w.length hs] using h
  have hT : threshold w.length ≤ 3 * d := by
    dsimp [d]
    rw [threshold_eq w.length hs, stateCount_eq w.length hs]
    omega
  have hy :
      restorePendingCount C start =
        tval w + threshold w.length + d + 1 +
          (if latent then a * (d / 3) + d / 3 else 0) := by
    cases latent <;>
      simp [start, restorePendingCount, Plan.workState, payload, storedMemory, unit, d] <;>
      omega
  have hybound : restorePendingCount C start ≤ (a + 9) * d := by
    rw [hy]
    have hdiv : d / 3 ≤ d := Nat.div_le_self d 3
    have hamul : a * (d / 3) ≤ a * d := Nat.mul_le_mul_left a hdiv
    cases latent <;> simp <;> nlinarith
  have hu :
      restoreComparisonCount C start = min (tval w) (threshold w.length) := by
    cases latent <;>
      simp [start, restoreComparisonCount, Plan.workState, payload, storedMemory, unit]
  have hubound : restoreComparisonCount C start ≤ 3 * d := by
    rw [hu]
    exact (min_le_left _ _).trans hv.le
  have htransition :
      restoreTransitionPotential C q d start = 1 / (d : ℝ) + aut d 1 := by
    cases latent <;>
      simp [start, restoreTransitionPotential, Plan.workState, payload, unit, d]
  change restoreTransitionPotential C q d start +
      hrm (restorePendingCount C start) / (d : ℝ) +
      hrm (restoreComparisonCount C start) /
        ((2 * 3 ^ (w.length - 3) : ℕ) : ℝ) ≤ _
  rw [htransition]
  exact add_le_add
    (add_le_add le_rfl
      (div_le_div_of_nonneg_right (hrm_mono hybound) (Nat.cast_nonneg _)))
    (div_le_div_of_nonneg_right (hrm_mono hubound) (Nat.cast_nonneg _))

/-- W2, including restoration of latent clock-catalyst species. -/
theorem restore_meanDuration_le_workDurationBound (C : XCTM Q)
    (q : ActiveState C) (w : List Bool) (a : ℕ) (latent : Bool)
    (hs : 3 ≤ w.length) :
    meanDuration C
        (Plan.workState C (.first (activeControl C q) w a latent) + unit .signal) ≤
      ENNReal.ofReal (workDurationBound w.length a) := by
  have hd : 0 < stateCount w.length := by unfold stateCount; positivity
  have hg : 0 < 2 * 3 ^ (w.length - 3) := by positivity
  have hgap :
      tval w + 2 * 3 ^ (w.length - 3) ≤ threshold w.length ∨
        threshold w.length + 2 * 3 ^ (w.length - 3) ≤ tval w := by
    have h := tape_facts (n := w.length - 3) (w := w) (by omega) false
    cases hb : w.headD false with
    | false =>
        left
        rw [threshold_eq w.length hs]
        exact h.2.1 hb
    | true =>
        right
        rw [threshold_eq w.length hs]
        exact h.2.2.1 hb
  have hmean := meanDuration_le_of_certificate_generator C
    (restoreCertificate C q w a latent hs)
    (restorePotential C q (stateCount w.length) (2 * 3 ^ (w.length - 3)))
    (fun x _ => restorePotential_nonneg C q _ _ x)
    (fun x hx ht => restorePotential_drift C hd hg hgap hx ht)
  exact hmean.trans (ENNReal.ofReal_le_ofReal
    ((restorePotential_initial_le C q w a latent hs).trans
      (restore_harmonic_budget w.length a hs)))

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork

open Stochastic Stochastic.MassAction
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-! ### W4r: transfer of the compiled read-window potential -/

private def readShadowMachine (C : XCTM Q) (q : ReadState C) : ClockedCTM.CTM Unit where
  next _ b := ((), (C.next q.val b).2)

private def readShadow (C : XCTM Q) (q : ReadState C)
    (z : State (Sp C)) : State (ClockedCTM.Sp Unit 0)
  | .s3 _ => z (.third (.inl q))
  | .rq _ => z (.reader q)
  | .u _ b => z (.write q b)
  | .i => z .signal
  | .mem a => z (.mem a)
  | _ => 0

private inductive ReadChannel
  | seed | select | grow | restoreMemory | restoreThresholdStar | restoreThreshold
  | shift | zero | write | compare | single | double
  deriving DecidableEq, Fintype

private def readChannel (C : XCTM Q) (q : ReadState C) (b : Bool) :
    ReadChannel → Rx C
  | .seed => .startRead q
  | .select => .chooseRead q b
  | .grow => .growWrite q b
  | .restoreMemory => .readRestoreM q b
  | .restoreThresholdStar => .readRestoreTs q b
  | .restoreThreshold => .readRestoreT q b
  | .shift => .readShift q b
  | .zero => .readZero q b
  | .write => .readWrite q b
  | .compare => .pair
  | .single => .consumeSingle
  | .double => .consumeDouble

private def readOldChannel (b : Bool) : ReadChannel → ClockedCTM.Rx Unit 0
  | .seed => .adv3 ()
  | .select => if b then .rm () else .rt ()
  | .grow => .auto34 () b
  | .restoreMemory => .cMs () b
  | .restoreThresholdStar => .cTs () b
  | .restoreThreshold => .cT () b
  | .shift => .cM () b
  | .zero => .cD () b
  | .write => .cB () b
  | .compare => .pair
  | .single => .k1
  | .double => .k2

private theorem readChannel_injective (C : XCTM Q) (q : ReadState C) (b : Bool) :
    Function.Injective (readChannel C q b) := by
  intro c c' h
  cases c <;> cases c' <;> simp_all [readChannel]

private theorem readOldChannel_injective (b : Bool) :
    Function.Injective (readOldChannel b) := by
  intro c c' h
  cases b <;> cases c <;> cases c' <;> simp_all [readOldChannel]

private theorem readChannel_not_clock (C : XCTM Q) (q : ReadState C)
    (b : Bool) (c : ReadChannel) : isClock (readChannel C q b c) = false := by
  cases c <;> rfl

private theorem readOldChannel_not_clock (b : Bool) (c : ReadChannel) :
    ¬ (readOldChannel b c).IsClock := by
  cases b <;> cases c <;> simp [readOldChannel, ClockedCTM.Rx.IsClock]

private theorem readShadow_rate (C : XCTM Q) (q : ReadState C)
    (b : Bool) (c : ReadChannel) (z : State (Sp C)) :
    ClockedCTM.rate (readShadowMachine C q) (readOldChannel b c) (readShadow C q z) =
      rate C (readChannel C q b c) z := by
  cases b <;> cases c <;> rfl

-- The proof enumerates twelve corresponding channels and their finite species cases.
set_option maxHeartbeats 600000 in
private theorem readShadow_fire (C : XCTM Q) (q : ReadState C)
    (b : Bool) (c : ReadChannel) (z : State (Sp C)) :
    readShadow C q ((rxn C (readChannel C q b c)).fire z) =
      (ClockedCTM.rxn (readShadowMachine C q) (readOldChannel b c)).fire
        (readShadow C q z) := by
  cases b <;> cases c <;> funext s
  all_goals
    cases s with
    | mem a =>
        cases a <;>
          simp [readShadow, readChannel, readOldChannel, readShadowMachine,
            fire_apply, sourceLeft, sourceRight, products, unit,
            ClockedCTM.fire_apply, ClockedCTM.src1, ClockedCTM.src2,
            ClockedCTM.out, ClockedCTM.one, Pi.add_apply, Pi.smul_apply]
    | s1 u | s2 u | s3 u | rq u =>
        cases u
        simp [readShadow, readChannel, readOldChannel, readShadowMachine,
          fire_apply, sourceLeft, sourceRight, products, unit,
          ClockedCTM.fire_apply, ClockedCTM.src1, ClockedCTM.src2,
          ClockedCTM.out, ClockedCTM.one, Pi.add_apply, Pi.smul_apply]
    | u u b' =>
        cases u
        cases b' <;>
          simp [readShadow, readChannel, readOldChannel, readShadowMachine,
            fire_apply, sourceLeft, sourceRight, products, unit,
            ClockedCTM.fire_apply, ClockedCTM.src1, ClockedCTM.src2,
            ClockedCTM.out, ClockedCTM.one, Pi.add_apply, Pi.smul_apply]
    | _ =>
        simp [readShadow, readChannel, readOldChannel, readShadowMachine,
          fire_apply, sourceLeft, sourceRight, products, unit,
          ClockedCTM.fire_apply, ClockedCTM.src1, ClockedCTM.src2,
          ClockedCTM.out, ClockedCTM.one, Pi.add_apply, Pi.smul_apply]

private theorem readShadow_only_signal (C : XCTM Q) (q : ReadState C)
    (z : State (Sp C))
    (h : OnlyControl C [.third (.inl q), .signal] z) :
    ClockedCTM.OnlyState [.s3 (), .i] (readShadow C q z) := by
  intro s hs hn
  cases s with
  | rq u => exact h (.reader q) trivial (by simp)
  | u u b => exact h (.write q b) trivial (by simp)
  | s3 u => cases u; exact False.elim (hn (by simp))
  | i => exact False.elim (hn (by simp))
  | s1 _ | s2 _ => rfl
  | clk _ | acc | accS | mem _ => exact False.elim hs

private theorem readShadow_only_reader (C : XCTM Q) (q : ReadState C)
    (z : State (Sp C))
    (h : OnlyControl C [.third (.inl q), .reader q] z) :
    ClockedCTM.OnlyState [.s3 (), .rq ()] (readShadow C q z) := by
  intro s hs hn
  cases s with
  | u u b => exact h (.write q b) trivial (by simp)
  | i => exact h .signal trivial (by simp)
  | s3 u => cases u; exact False.elim (hn (by simp))
  | rq u => cases u; exact False.elim (hn (by simp))
  | s1 _ | s2 _ => rfl
  | clk _ | acc | accS | mem _ => exact False.elim hs

private theorem readShadow_only_write (C : XCTM Q) (q : ReadState C)
    (b : Bool) (z : State (Sp C))
    (h : OnlyControl C [.third (.inl q), .write q b] z) :
    ClockedCTM.OnlyState [.s3 (), .u () b] (readShadow C q z) := by
  intro s hs hn
  cases s with
  | rq u => exact h (.reader q) trivial (by simp)
  | i => exact h .signal trivial (by simp)
  | u u b' =>
      have hb : b' ≠ b := by
        intro he
        subst b'
        exact hn (by cases u; simp)
      exact h (.write q b') trivial (by simp [hb])
  | s3 u => cases u; exact False.elim (hn (by simp))
  | s1 _ | s2 _ => rfl
  | clk _ | acc | accS | mem _ => exact False.elim hs

private theorem readShadow_window (C : XCTM Q) (q : ReadState C)
    {m T g x x' : ℕ} {b : Bool} {z : State (Sp C)}
    (h : ReadWindow C m T g q b x x' z) :
    ClockedCTM.Win34 (readShadowMachine C q) m T g () b x x'
      (readShadow C q z) := by
  rcases h with ⟨hO, hI, hs, hM⟩ | ⟨hO, hR, hs, hM⟩ | ⟨hO, hs, hu, hM⟩
  · exact Or.inl ⟨readShadow_only_signal C q z hO, hI, hs, hM⟩
  · exact Or.inr (Or.inl ⟨readShadow_only_reader C q z hO, hR, hs, hM⟩)
  · exact Or.inr (Or.inr ⟨readShadow_only_write C q b z hO, hs, hu, hM⟩)

private theorem readShadow_terminal (C : XCTM Q) (q : ReadState C)
    {m T g x x' : ℕ} {b : Bool} {z : State (Sp C)}
    (h : ReadWindow C m T g q b x x' z)
    (hK : ClockedCTM.K4 m T () b x' (readShadow C q z)) :
    WorkTerminal C z := by
  have hi : z .signal = 0 := hK.1 .i trivial (by simp)
  have hr : z (.reader q) = 0 := hK.1 (.rq ()) trivial (by simp)
  have hs : z (.third (.inl q)) = 0 := hK.1 (.s3 ()) trivial (by simp)
  rcases h with ⟨hO, hI, hcount, hM⟩ | ⟨hO, hR, hcount, hM⟩ |
    ⟨hO, hcount, hu, hM⟩
  · omega
  · omega
  · apply read_normal_terminal C (m := m) (T := T) (x' := x') (q := q) (b := b)
    refine ⟨?_, hK.2.1, hK.2.2⟩
    intro s hstate hnot
    by_cases he : s = .third (.inl q)
    · subst s
      exact hs
    · have hne : s ≠ .write q b := by simpa using hnot
      exact hO s hstate (by simp [he, hne])

private theorem readChannel_cover (C : XCTM Q) (q : ReadState C)
    {m T g x x' : ℕ} {b : Bool} {z : State (Sp C)}
    (h : ReadWindow C m T g q b x x' z)
    (r : Rx C) (hc : isClock r = false) (he : (rxn C r).enabled z) :
    r ∈ Finset.univ.image (readChannel C q b) := by
  rcases h with ⟨hO, hI, hs, hM⟩ | ⟨hO, hR, hs, hM⟩ | ⟨hO, hs, hu, hM⟩
  · have hr := read_start_enabled C hO hM r hc he
    subst r
    exact Finset.mem_image.mpr ⟨.seed, Finset.mem_univ _, rfl⟩
  · have hr := read_choose_enabled C hO hM r hc he
    subst r
    exact Finset.mem_image.mpr ⟨.select, Finset.mem_univ _, rfl⟩
  · have hr := read_work_enabled C hO r hc he
    simp only [readWorkLabels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨.grow, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.restoreMemory, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.restoreThresholdStar, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.restoreThreshold, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.shift, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.zero, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.write, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.compare, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.single, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.double, Finset.mem_univ _, rfl⟩

private theorem readOldChannel_cover (C : XCTM Q) (q : ReadState C)
    {m T g x x' : ℕ} {b : Bool} {z : State (ClockedCTM.Sp Unit 0)}
    (h : ClockedCTM.Win34 (readShadowMachine C q) m T g () b x x' z)
    (r : ClockedCTM.Rx Unit 0) (hc : ¬ r.IsClock)
    (he : ClockedCTM.rate (readShadowMachine C q) r z ≠ 0) :
    r ∈ Finset.univ.image (readOldChannel b) := by
  rcases h with ⟨hO, hI, hs, hM⟩ | ⟨hO, hR, hs, hM⟩ | ⟨hO, hs, hu, hM⟩
  · have hr := ClockedCTM.win34a_enabled (readShadowMachine C q) hO hM r hc he
    subst r
    exact Finset.mem_image.mpr ⟨.seed, Finset.mem_univ _, rfl⟩
  · rcases ClockedCTM.win34b_enabled (readShadowMachine C q) hO hM r hc he with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.mem_image.mpr ⟨.select, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.select, Finset.mem_univ _, rfl⟩
  · have hr := ClockedCTM.win34c_enabled (readShadowMachine C q) hO r hc he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨.grow, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.restoreMemory, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.restoreThresholdStar, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.restoreThreshold, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.shift, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.zero, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.write, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.compare, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.single, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.double, Finset.mem_univ _, rfl⟩

private theorem readShadow_drift_sum (C : XCTM Q) (q : ReadState C)
    {m T g x x' : ℕ} {b : Bool} {z : State (ClockedCTM.Sp Unit 0)}
    (h : ClockedCTM.Win34 (readShadowMachine C q) m T g () b x x' z)
    (V : State (ClockedCTM.Sp Unit 0) → ℝ) :
    ClockedCTM.drift (readShadowMachine C q) V z =
      ∑ c : ReadChannel,
        (ClockedCTM.rate (readShadowMachine C q) (readOldChannel b c) z : ℝ) *
          (V ((ClockedCTM.rxn (readShadowMachine C q) (readOldChannel b c)).fire z) -
            V z) := by
  let F : ClockedCTM.Rx Unit 0 → ℝ := fun r =>
    if r.IsClock then 0 else
      (ClockedCTM.rate (readShadowMachine C q) r z : ℝ) *
        (V ((ClockedCTM.rxn (readShadowMachine C q) r).fire z) - V z)
  have hsum :
      (∑ r ∈ Finset.univ.image (readOldChannel b), F r) = ∑ r, F r := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro r hr hn
    by_cases hc : r.IsClock
    · simp [F, hc]
    · by_cases he : ClockedCTM.rate (readShadowMachine C q) r z = 0
      · simp [F, hc, he]
      · exact False.elim (hn (readOldChannel_cover C q h r hc he))
  change (∑ r, F r) = _
  rw [← hsum, Finset.sum_image (readOldChannel_injective b).injOn]
  apply Finset.sum_congr rfl
  intro c _
  simp only [F, if_neg (readOldChannel_not_clock b c)]

private noncomputable def readPotential (C : XCTM Q) (q : ReadState C)
    (m g x' : ℕ) (b : Bool) (z : State (Sp C)) : ℝ :=
  ClockedCTM.V34 m g x' () b (readShadow C q z)

private theorem readPotential_workDrift (C : XCTM Q) (q : ReadState C)
    {m T g x x' : ℕ} {b : Bool} {z : State (Sp C)}
    (h : ReadWindow C m T g q b x x' z) :
    workDrift C (readPotential C q m g x' b) z =
      ClockedCTM.drift (readShadowMachine C q)
        (ClockedCTM.V34 m g x' () b) (readShadow C q z) := by
  rw [workDrift_eq_sum_of_enabled_subset C _ z
    (Finset.univ.image (readChannel C q b))
    (by
      intro r hr
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hr
      exact readChannel_not_clock C q b c)
    (readChannel_cover C q h)]
  rw [Finset.sum_image (readChannel_injective C q b).injOn,
    readShadow_drift_sum C q (readShadow_window C q h)]
  apply Finset.sum_congr rfl
  intro c _
  simp only [readPotential, readShadow_fire, readShadow_rate]

private theorem readPotential_drift (C : XCTM Q) (q : ReadState C)
    {m T g x x' : ℕ} {b : Bool} {z : State (Sp C)}
    (hm : 2 ≤ m) (hg : 1 ≤ g) (hx : 1 ≤ x')
    (hnext : x' + 3 * bw b * m = 3 * x + bw (C.next q.val b).2)
    (h : ReadWindow C m T g q b x x' z) (hnt : ¬ WorkTerminal C z) :
    workDrift C (readPotential C q m g x' b) z ≤ -1 := by
  rw [readPotential_workDrift C q h]
  exact ClockedCTM.win34_drift (readShadowMachine C q) hm hg hx hnext
    (readShadow_window C q h) (fun hK => hnt (readShadow_terminal C q h hK))

private theorem readShadow_add_signal (C : XCTM Q) (q : ReadState C)
    (z : State (Sp C)) :
    readShadow C q (z + unit .signal) =
      readShadow C q z + ClockedCTM.one .i := by
  funext s
  cases s <;> simp [readShadow, unit, ClockedCTM.one, Pi.add_apply]

private theorem readShadow_initial_class (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    ClockedCTM.K3 (stateCount w.length) (threshold w.length) () (tval w)
      (readShadow C q (Plan.workState C (.third (.inl q) w a))) := by
  have hM := comparedMemory_read w hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hstate hnot
    cases s with
    | s3 u => cases u; exact False.elim (hnot (by simp))
    | clk _ | acc | accS | mem _ => exact False.elim hstate
    | _ => simp [readShadow, Plan.workState, payload, unit]
  · simp [readShadow, Plan.workState, payload, unit]
  · exact hM.1
  · exact hM.2.1
  · cases hb : w.headD false with
    | false =>
        right
        simpa [readShadow, Plan.workState, payload, unit] using (hM.2.2.1 hb).1
    | true =>
        left
        simpa [readShadow, Plan.workState, payload, unit] using (hM.2.2.2 hb).1

private theorem readPotential_initial_le_theta (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    readPotential C q (stateCount w.length) (2 * 3 ^ (w.length - 3))
        (tval (w.tail ++ [(C.next q.val (w.headD false)).2])) (w.headD false)
        (Plan.workState C (.third (.inl q) w a) + unit .signal) ≤
      ClockedCTM.Θ34 (w.length - 3) := by
  let n := w.length - 3
  have hw : w.length = n + 3 := by dsimp [n]; omega
  have hm : stateCount w.length = 9 * 3 ^ n := stateCount_eq w.length hs
  have ht : threshold w.length = 20 * 3 ^ n := threshold_eq w.length hs
  have hp : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hmr : (0 : ℝ) < (9 * 3 ^ n : ℕ) := by exact_mod_cast (by omega : 0 < 9 * 3 ^ n)
  obtain ⟨hnext, hb, hb', hx, hxlt, hvlt⟩ :=
    tape_facts hw (C.next q.val (w.headD false)).2
  have hK := readShadow_initial_class C q w a hs
  rw [hm, ht] at hK
  have hstart := (ClockedCTM.win34_start (readShadowMachine C q)
    (x' := tval (w.tail ++ [(C.next q.val (w.headD false)).2]))
    (by omega : 1 ≤ 2 * 3 ^ n) hb hb' hK).2
  rw [← readShadow_add_signal] at hstart
  unfold readPotential
  rw [hm]
  apply hstart.trans
  unfold ClockedCTM.Θ34
  have hl :
      Real.log (1 + ((9 * 3 ^ n + 1 + 2 * (20 * 3 ^ n) + 2 * tval w : ℕ) : ℝ)) ≤
        Real.log (1 + ((13 * (9 * 3 ^ n) : ℕ) : ℝ)) := by
    apply Real.log_le_log (by positivity)
    have hbnd : 9 * 3 ^ n + 1 + 2 * (20 * 3 ^ n) + 2 * tval w ≤
        13 * (9 * 3 ^ n) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hbnd
    linarith
  have hln : 0 ≤ Real.log (1 + ((6 * (9 * 3 ^ n) : ℕ) : ℝ)) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (6 * (9 * 3 ^ n)); linarith)
  have hxr : ((9 * 3 ^ n : ℕ) : ℝ) ≤
      (tval (w.tail ++ [(C.next q.val (w.headD false)).2]) : ℝ) := by exact_mod_cast hx
  have hfour := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hmr hxr
  have hlast := mul_le_mul_of_nonneg_right hfour hln
  have hfirst := mul_le_mul_of_nonneg_left hl
    (by positivity : (0 : ℝ) ≤ 4 / ((9 * 3 ^ n : ℕ) : ℝ))
  push_cast at hlast hfirst ⊢
  linarith

/-- The compiled read-window potential fits the T41 constant already without
the extra logarithmic accuracy allowance. -/
theorem readTheta_le_length (n : ℕ) :
    ClockedCTM.Θ34 n ≤ 16 * ((n : ℝ) + 3) / (9 * 3 ^ n : ℝ) := by
  have hp : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hm : (0 : ℝ) < 9 * 3 ^ n := by positivity
  have hmone : (1 : ℝ) ≤ 9 * 3 ^ n := by linarith
  have ha : (9 * 3 ^ n : ℝ) * aut (9 * 3 ^ n) 1 ≤
      2 * (1 + Real.log (9 * 3 ^ n)) := by
    have hfirst := mul_aut_one_le (9 * 3 ^ n)
    have hsecond := hrm_le_log (9 * 3 ^ n)
    push_cast at hfirst hsecond
    linarith
  have hlfirst :
      Real.log (1 + ((13 * (9 * 3 ^ n) : ℕ) : ℝ)) ≤
        Real.log 2 + Real.log 7 + Real.log (9 * 3 ^ n) := by
    push_cast
    rw [← Real.log_mul (x := 2) (y := 7) (by norm_num) (by norm_num),
      ← Real.log_mul (x := 2 * 7) (y := 9 * 3 ^ n) (by norm_num) hm.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hlsecond :
      Real.log (1 + ((6 * (9 * 3 ^ n) : ℕ) : ℝ)) ≤
        Real.log 7 + Real.log (9 * 3 ^ n) := by
    push_cast
    rw [← Real.log_mul (x := 7) (y := 9 * 3 ^ n) (by norm_num) hm.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hlog : Real.log (9 * 3 ^ n : ℝ) = ((n : ℝ) + 2) * Real.log 3 := by
    rw [show (9 : ℝ) * 3 ^ n = 3 ^ (n + 2) by ring, Real.log_pow]
    push_cast
    ring
  have he :
      ClockedCTM.Θ34 n * (9 * 3 ^ n : ℝ) =
        11 / 2 + (9 * 3 ^ n : ℝ) * aut (9 * 3 ^ n) 1 +
          4 * Real.log (1 + ((13 * (9 * 3 ^ n) : ℕ) : ℝ)) +
          4 * Real.log (1 + ((6 * (9 * 3 ^ n) : ℕ) : ℝ)) := by
    unfold ClockedCTM.Θ34
    push_cast
    have hpow : (3 : ℝ) ^ n ≠ 0 := by positivity
    field_simp <;> ring
  apply (le_div_iff₀ hm).mpr
  rw [he]
  have hseven := ClockedCTM.log_seven_le
  have htwo := Real.log_two_lt_d9
  have hthree := ClockedCTM.log_three_le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hscaled := mul_le_mul_of_nonneg_left hthree
    (by linarith : (0 : ℝ) ≤ (n : ℝ) + 2)
  rw [hlog] at ha hlfirst hlsecond
  nlinarith

/-- W4r, retaining the original unbounded network and standalone law. -/
theorem read_meanDuration_le_theta (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    meanDuration C (Plan.workState C (.third (.inl q) w a) + unit .signal) ≤
      ENNReal.ofReal (ClockedCTM.Θ34 (w.length - 3)) := by
  let b := w.headD false
  let w' := w.tail ++ [(C.next q.val b).2]
  have hd : 2 ≤ stateCount w.length := by
    rw [stateCount_eq w.length hs]
    have hp := Nat.one_le_pow (w.length - 3) 3 (by norm_num)
    omega
  have hg : 1 ≤ 2 * 3 ^ (w.length - 3) := by
    have hp := Nat.one_le_pow (w.length - 3) 3 (by norm_num)
    omega
  have hx : 1 ≤ tval w' := by
    have hb := (tape_facts (n := w.length - 3) (w := w) (by omega)
      (C.next q.val b).2).2.2.2.1
    have hp := Nat.one_le_pow (w.length - 3) 3 (by norm_num)
    dsimp [w'] at *
    omega
  have hnext :
      tval w' + 3 * bw b * stateCount w.length =
        3 * tval w + bw (C.next q.val b).2 :=
    read_value w hs _
  let V := readPotential C q (stateCount w.length) (2 * 3 ^ (w.length - 3))
    (tval w') b
  have hbound := meanDuration_le_of_certificate_generator C
    (readCertificate C q w a hs) V
    (fun z _ => ClockedCTM.V34_nonneg _ _ _ _ _ _)
    (fun z hz hnt => readPotential_drift C q hd hg hx hnext hz.1 hnt)
  exact hbound.trans
    (ENNReal.ofReal_le_ofReal (readPotential_initial_le_theta C q w a hs))

theorem read_meanDuration_le_workDurationBound (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (accuracy a : ℕ) (hs : 3 ≤ w.length) :
    meanDuration C (Plan.workState C (.third (.inl q) w accuracy) + unit .signal) ≤
      ENNReal.ofReal (workDurationBound w.length a) := by
  refine (read_meanDuration_le_theta C q w accuracy hs).trans
    (ENNReal.ofReal_le_ofReal ((readTheta_le_length (w.length - 3)).trans ?_))
  have hn : (((w.length - 3 : ℕ) : ℝ) + 3) = w.length := by
    rw [Nat.cast_sub hs, Nat.cast_ofNat]
    ring
  have hlog : 0 ≤ Real.log ((a : ℝ) + 2) :=
    Real.log_nonneg (by have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)
  unfold workDurationBound
  rw [hn, stateCount_eq w.length hs]
  push_cast
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork

open Stochastic Stochastic.MassAction
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-! W4e: an autocatalytic transition plus a harmonic cleanup rank. -/

def extensionCleanRank (C : XCTM Q) (x : State (Sp C)) : ℕ :=
  x (.mem .b) + x (.mem .d) + x (.mem .m) +
    2 * x (.mem .ms) + 3 * x (.mem .t) + x (.mem .ts) +
    x .forward + x .backward

noncomputable def extensionTransitionPotential (C : XCTM Q)
    (e : ExtendState C) (d : ℕ) (x : State (Sp C)) : ℝ :=
  (if x .signal = 1 then 1 / (d : ℝ) else 0) +
    aut d (max (d - x (.third (.inr e))) 1) / 3

noncomputable def extensionWorkPotential (C : XCTM Q)
    (e : ExtendState C) (d : ℕ) (x : State (Sp C)) : ℝ :=
  extensionTransitionPotential C e d x + hrm (extensionCleanRank C x) / d

theorem extensionTransitionPotential_nonneg (C : XCTM Q)
    (e : ExtendState C) (d : ℕ) (x : State (Sp C)) :
    0 ≤ extensionTransitionPotential C e d x := by
  unfold extensionTransitionPotential
  exact add_nonneg (by split_ifs <;> positivity)
    (div_nonneg (aut_nonneg _ _) (by norm_num))

theorem extensionWorkPotential_nonneg (C : XCTM Q)
    (e : ExtendState C) (d : ℕ) (x : State (Sp C)) :
    0 ≤ extensionWorkPotential C e d x :=
  add_nonneg (extensionTransitionPotential_nonneg C e d x)
    (div_nonneg (hrm_nonneg _) (Nat.cast_nonneg _))

private theorem extensionCleanRank_fire_le
    (C : XCTM Q) (e : ExtendState C) (r : Rx C)
    (hr : ExtensionLabel C e r) (x : State (Sp C))
    (he : (rxn C r).enabled x) :
    extensionCleanRank C ((rxn C r).fire x) ≤ extensionCleanRank C x := by
  have hp := (enabled_iff C r x).mp he
  unfold ExtensionLabel at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [extensionCleanRank, rate, fire_apply, sourceLeft, sourceRight,
      products, unit, Pi.smul_apply] at hp ⊢ <;> omega

private theorem extensionTransitionPotential_seed
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (x : State (Sp C)) (hx : ExtensionInvariant C e d v th a f x)
    (he : (rxn C (.startExtension e)).enabled x) :
    (rate C (.startExtension e) x : ℝ) *
      (extensionTransitionPotential C e d
        ((rxn C (.startExtension e)).fire x) -
        extensionTransitionPotential C e d x) = -1 := by
  have hp := (enabled_iff C (.startExtension e) x).mp he
  simp only [rate, sourceLeft, sourceRight, ne_eq, mul_eq_zero, not_or] at hp
  have hs : x .signal = 1 := by have h := hx.signal; omega
  have hold : x (.third (.inr e)) = d := by
    have h := hx.control
    have h' := hx.exclusive
    omega
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs' : ((rxn C (.startExtension e)).fire x) .signal = 0 := by
    simp [fire_apply, sourceLeft, sourceRight, products, unit, hs]
  have hold' :
      ((rxn C (.startExtension e)).fire x) (.third (.inr e)) = d - 1 := by
    simp [fire_apply, sourceLeft, sourceRight, products, unit, hold]
  have hsub : d - (d - 1) = 1 := by omega
  have hr : rate C (.startExtension e) x = d := by
    simp [rate, sourceLeft, sourceRight, hs, hold]
  rw [hr]
  simp only [extensionTransitionPotential, hs', hold', hs, hold,
    hsub, Nat.sub_self, max_self, max_eq_right (show 0 ≤ (1 : ℕ) by omega),
    if_pos rfl, if_neg (by omega : (0 : ℕ) ≠ 1)]
  field_simp [hd.ne']
  <;> (try simp only [ite_true])
  <;> (try simp only [if_true])
  <;> (try field_simp [hd.ne'])
  <;> ring

private theorem extensionTransitionPotential_grow
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (x : State (Sp C)) (hx : ExtensionInvariant C e d v th a f x)
    (he : (rxn C (.growExtension e)).enabled x) :
    (rate C (.growExtension e) x : ℝ) *
      (extensionTransitionPotential C e d
        ((rxn C (.growExtension e)).fire x) -
        extensionTransitionPotential C e d x) = -1 := by
  have hp := (enabled_iff C (.growExtension e) x).mp he
  simp only [rate, sourceLeft, sourceRight, ne_eq, mul_eq_zero, not_or] at hp
  let j := d - x (.third (.inr e))
  have hc := hx.control
  have hex := hx.exclusive
  have hs : x .signal = 0 := by omega
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjd : j < d := by dsimp [j]; omega
  have hold : x (.third (.inr e)) = d - j := by dsimp [j]; omega
  have hnew : x (.extend e) = 3 * j := by dsimp [j]; omega
  have hs' : ((rxn C (.growExtension e)).fire x) .signal = 0 := by
    simp [fire_apply, sourceLeft, sourceRight, products, unit, hs]
  have hold' :
      d - ((rxn C (.growExtension e)).fire x) (.third (.inr e)) = j + 1 := by
    have hi : d - (x (.third (.inr e)) - 1) = j + 1 := by
      dsimp [j]
      omega
    simpa [fire_apply, sourceLeft, sourceRight, products, unit, Pi.smul_apply] using hi
  have hr : rate C (.growExtension e) x = 3 * (j * (d - j)) := by
    simp only [rate, sourceLeft, sourceRight, hold, hnew]
    ring
  have h := aut_drift hj hjd
  unfold extensionTransitionPotential
  rw [hs', hs, hold', show d - x (.third (.inr e)) = j from rfl,
    max_eq_left hj, max_eq_left (show 1 ≤ j + 1 by omega), hr]
  simp only [if_neg (by omega : (0 : ℕ) ≠ 1), zero_add]
  calc
    (((3 * (j * (d - j)) : ℕ) : ℝ) *
        (aut d (j + 1) / 3 - aut d j / 3)) =
        ((j * (d - j) : ℕ) : ℝ) *
          (aut d (j + 1) - aut d j) := by push_cast; ring
    _ = -1 := h

private theorem extensionTransitionPotential_other
    (C : XCTM Q) (e : ExtendState C) (d : ℕ)
    (x : State (Sp C)) (r : Rx C) (hr : ExtensionLabel C e r)
    (hs : r ≠ .startExtension e) (hg : r ≠ .growExtension e) :
    extensionTransitionPotential C e d ((rxn C r).fire x) =
      extensionTransitionPotential C e d x := by
  unfold ExtensionLabel at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hs rfl).elim
  · exact (hg rfl).elim
  all_goals
    simp [extensionTransitionPotential, fire_apply, sourceLeft, sourceRight,
      products, unit, Pi.smul_apply]

private theorem extensionTransitionPotential_mono
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (x : State (Sp C)) (hx : ExtensionInvariant C e d v th a f x)
    (r : Rx C) (hr : ExtensionLabel C e r) (he : (rxn C r).enabled x) :
    extensionTransitionPotential C e d ((rxn C r).fire x) ≤
      extensionTransitionPotential C e d x := by
  have hrpos : (0 : ℝ) < rate C r x := by
    exact_mod_cast Nat.pos_of_ne_zero ((enabled_iff C r x).mp he)
  by_cases hs : r = .startExtension e
  · subst r
    have h := extensionTransitionPotential_seed C e d v th a f x hx he
    nlinarith
  by_cases hg : r = .growExtension e
  · subst r
    have h := extensionTransitionPotential_grow C e d v th a f x hx he
    nlinarith
  exact (extensionTransitionPotential_other C e d x r hr hs hg).le

private theorem extensionWorkPotential_mono
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (x : State (Sp C)) (hx : ExtensionInvariant C e d v th a f x)
    (r : Rx C) (hr : ExtensionLabel C e r) (he : (rxn C r).enabled x) :
    extensionWorkPotential C e d ((rxn C r).fire x) ≤
      extensionWorkPotential C e d x := by
  exact add_le_add
    (extensionTransitionPotential_mono C e d v th a f x hx r hr he)
    (div_le_div_of_nonneg_right
      (hrm_mono (extensionCleanRank_fire_le C e r hr x he))
      (Nat.cast_nonneg d))

private theorem extension_hrm_drop_of_lt {m n : ℕ} (h : m < n) :
    hrm m - hrm n ≤ -(1 / (n : ℝ)) := by
  cases n with
  | zero => omega
  | succ n =>
      have hm := hrm_mono (show m ≤ n by omega)
      rw [hrm_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

theorem extensionWorkPotential_drift
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ) (hd : 0 < d)
    (x : State (Sp C)) (hx : ExtensionInvariant C e d v th a f x)
    (hnt : ¬ WorkTerminal C x) :
    workDrift C (extensionWorkPotential C e d) x ≤ -1 := by
  have hmono : ∀ r : Rx C, isClock r = false → (rxn C r).enabled x →
      extensionWorkPotential C e d ((rxn C r).fire x) ≤
        extensionWorkPotential C e d x := by
    intro r hw he
    exact extensionWorkPotential_mono C e d v th a f x hx r
      (extension_enabled_label C e d v th a f x hx r hw he) he
  by_cases hs : x .signal = 1
  · have hold : x (.third (.inr e)) = d := by
      have hc := hx.control
      have hex := hx.exclusive
      omega
    have he : (rxn C (.startExtension e)).enabled x := by
      rw [enabled_iff]
      simp [rate, sourceLeft, sourceRight, hs, hold, Nat.ne_of_gt hd]
    have hclean : extensionCleanRank C ((rxn C (.startExtension e)).fire x) =
        extensionCleanRank C x := by
      simp [extensionCleanRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.smul_apply]
    have hdrop :
        (rate C (.startExtension e) x : ℝ) *
          (extensionWorkPotential C e d ((rxn C (.startExtension e)).fire x) -
            extensionWorkPotential C e d x) = -1 := by
      have h := extensionTransitionPotential_seed C e d v th a f x hx he
      unfold extensionWorkPotential
      rw [hclean]
      nlinarith
    have hsingle :
        workDrift C (extensionWorkPotential C e d) x ≤
          (rate C (.startExtension e) x : ℝ) *
            (extensionWorkPotential C e d ((rxn C (.startExtension e)).fire x) -
              extensionWorkPotential C e d x) := by
      simpa [isClock] using
        (workDrift_le_sum C (extensionWorkPotential C e d) x hmono
          {.startExtension e})
    exact hsingle.trans_eq hdrop
  have hs : x .signal = 0 := by have h := hx.signal; omega
  by_cases holdpos : 0 < x (.third (.inr e))
  · have hnew : 0 < x (.extend e) := by
      have h := hx.progress
      omega
    have he : (rxn C (.growExtension e)).enabled x := by
      rw [enabled_iff]
      simp [rate, sourceLeft, sourceRight, Nat.ne_of_gt holdpos, Nat.ne_of_gt hnew]
    have hclean : extensionCleanRank C ((rxn C (.growExtension e)).fire x) =
        extensionCleanRank C x := by
      simp [extensionCleanRank, fire_apply, sourceLeft, sourceRight,
        products, unit, Pi.smul_apply]
    have hdrop :
        (rate C (.growExtension e) x : ℝ) *
          (extensionWorkPotential C e d ((rxn C (.growExtension e)).fire x) -
            extensionWorkPotential C e d x) = -1 := by
      have h := extensionTransitionPotential_grow C e d v th a f x hx he
      unfold extensionWorkPotential
      rw [hclean]
      nlinarith
    have hsingle :
        workDrift C (extensionWorkPotential C e d) x ≤
          (rate C (.growExtension e) x : ℝ) *
            (extensionWorkPotential C e d ((rxn C (.growExtension e)).fire x) -
              extensionWorkPotential C e d x) := by
      simpa [isClock] using
        (workDrift_le_sum C (extensionWorkPotential C e d) x hmono
          {.growExtension e})
    exact hsingle.trans_eq hdrop
  have hold : x (.third (.inr e)) = 0 := by omega
  have hnew : x (.extend e) = 3 * d := by have h := hx.control; omega
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hzero : extensionTransitionPotential C e d x = 0 := by
    simp [extensionTransitionPotential, hs, hold,
      max_eq_left (show 1 ≤ d by omega), aut_self]
  have hcleanlt (r : Rx C) (hw : isClock r = false)
      (he : (rxn C r).enabled x) :
      extensionCleanRank C ((rxn C r).fire x) < extensionCleanRank C x := by
    have hdrop := extension_rank_drop C e r
      (extension_enabled_label C e d v th a f x hx r hw he) x he
    have hle :
        extensionCleanRank C ((rxn C r).fire x) ≤
          extensionRank C e ((rxn C r).fire x) := by
      unfold extensionCleanRank extensionRank
      omega
    have heq : extensionRank C e x = extensionCleanRank C x := by
      simp [extensionRank, extensionCleanRank, hs, hold]
    exact hle.trans_lt (hdrop.trans_eq heq)
  have hR : 0 < extensionCleanRank C x := by
    by_contra hn
    apply hnt
    intro r hw he
    have h := hcleanlt r hw he
    omega
  have hRreal : (0 : ℝ) < extensionCleanRank C x := by exact_mod_cast hR
  have hdiff (r : Rx C) (hw : isClock r = false)
      (he : (rxn C r).enabled x) :
      extensionWorkPotential C e d ((rxn C r).fire x) -
          extensionWorkPotential C e d x ≤
        -(1 / ((d : ℝ) * (extensionCleanRank C x : ℝ))) := by
    have hTle := extensionTransitionPotential_mono C e d v th a f x hx r
      (extension_enabled_label C e d v th a f x hx r hw he) he
    have hTnonneg := extensionTransitionPotential_nonneg C e d ((rxn C r).fire x)
    have hTzero : extensionTransitionPotential C e d ((rxn C r).fire x) = 0 := by
      rw [hzero] at hTle
      linarith
    have hh := div_le_div_of_nonneg_right
      (extension_hrm_drop_of_lt (hcleanlt r hw he)) hdreal.le
    unfold extensionWorkPotential
    rw [hTzero, hzero]
    calc
      0 + hrm (extensionCleanRank C ((rxn C r).fire x)) / d -
          (0 + hrm (extensionCleanRank C x) / d) =
          (hrm (extensionCleanRank C ((rxn C r).fire x)) -
            hrm (extensionCleanRank C x)) / d := by ring
      _ ≤ -(1 / (extensionCleanRank C x : ℝ)) / d := hh
      _ = -(1 / ((d : ℝ) * (extensionCleanRank C x : ℝ))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  let selected : Finset (Rx C) :=
    {.extendRestoreM e, .extendShift e, .extendWrite e, .extendRestoreTs e,
      .extendRestoreT e, .extendD e, .extendForward e, .extendBackward e}
  have hclock : ∀ r ∈ selected, isClock r = false := by
    intro r hr
    simp only [selected, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  let S : ℝ := (x (.mem .b) : ℝ) + x (.mem .d) + x (.mem .m) +
    x (.mem .ms) + x (.mem .t) + x (.mem .ts) + x .forward + x .backward
  have hrank : (extensionCleanRank C x : ℝ) ≤ 3 * S := by
    have hn : extensionCleanRank C x ≤
        3 * (x (.mem .b) + x (.mem .d) + x (.mem .m) + x (.mem .ms) +
          x (.mem .t) + x (.mem .ts) + x .forward + x .backward) := by
      unfold extensionCleanRank
      omega
    dsimp [S]
    exact_mod_cast hn
  calc
    workDrift C (extensionWorkPotential C e d) x ≤
        ∑ r ∈ selected, if isClock r = false then
          (rate C r x : ℝ) *
            (extensionWorkPotential C e d ((rxn C r).fire x) -
              extensionWorkPotential C e d x) else 0 :=
      workDrift_le_sum C (extensionWorkPotential C e d) x hmono selected
    _ ≤ ∑ r ∈ selected,
        -(rate C r x : ℝ) / ((d : ℝ) * (extensionCleanRank C x : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [if_pos (hclock r hr)]
      by_cases he : (rxn C r).enabled x
      · have h := mul_le_mul_of_nonneg_left (hdiff r (hclock r hr) he)
          (Nat.cast_nonneg (rate C r x))
        convert h using 1 <;> ring
      · have hz : rate C r x = 0 := by
          by_contra hn
          exact he ((enabled_iff C r x).mpr hn)
        simp [hz]
    _ = -(3 * S) / (extensionCleanRank C x : ℝ) := by
      simp [selected, rate, sourceLeft, sourceRight, hnew, S, Nat.cast_mul] <;>
        field_simp [hdreal.ne', hRreal.ne'] <;> ring
    _ ≤ -1 := by
      apply (div_le_iff₀ hRreal).mpr
      linarith

theorem extension_meanDuration_le_potential (C : XCTM Q)
    (e : ExtendState C) (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    meanDuration C (Plan.workState C (.third (.inr e) w a) + unit .signal) ≤
      ENNReal.ofReal
        (1 / (stateCount w.length : ℝ) + aut (stateCount w.length) 1 / 3 +
          hrm (extensionCleanRank C
            (Plan.workState C (.third (.inr e) w a) + unit .signal)) /
              (stateCount w.length : ℝ)) := by
  have hd : 0 < stateCount w.length := by unfold stateCount; positivity
  have h := meanDuration_le_of_certificate_generator C (extensionCertificate C e w a hs)
    (extensionWorkPotential C e (stateCount w.length))
    (fun x _ => extensionWorkPotential_nonneg C e _ x)
    (fun x hx hnt => extensionWorkPotential_drift C e _ _ _ _ _ hd x hx hnt)
  simpa [extensionWorkPotential, extensionTransitionPotential, Plan.workState,
    payload, unit] using h

private theorem extensionCleanRank_bound
    (C : XCTM Q) (e : ExtendState C) (d v th a f : ℕ)
    (x : State (Sp C)) (hx : ExtensionInvariant C e d v th a f x) :
    extensionCleanRank C x ≤ a + f + 2 * v + 3 * th + d + 1 := by
  have hm : x (.mem .m) + x (.mem .ms) ≤ v := by
    have h := hx.memory
    omega
  have ht : x (.mem .t) + x (.mem .ts) ≤ th := by
    have h := hx.threshold
    omega
  have hsize : x (.mem .d) ≤ d := by have h := hx.size; omega
  have hb : x (.mem .b) ≤ 1 := by have h := hx.button; omega
  have ha : x .forward ≤ a := by have h := hx.forward; omega
  have hf : x .backward ≤ f := by have h := hx.backward; omega
  unfold extensionCleanRank
  omega

theorem extensionCleanRank_initial_bound (C : XCTM Q)
    (e : ExtendState C) (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    extensionCleanRank C
        (Plan.workState C (.third (.inr e) w (a + 1)) + unit .signal) ≤
      10 * (a + 2) * stateCount w.length := by
  let d := stateCount w.length
  let start := Plan.workState C (.third (.inr e) w (a + 1)) + unit .signal
  have hd : 0 < d := by dsimp [d]; unfold stateCount; positivity
  have hx :
      ExtensionInvariant C e d (tval w) (threshold w.length)
        ((a + 1) * d) d start :=
    (extensionCertificate C e w (a + 1) hs).initial
  have hv : tval w ≤ 3 * d := by
    have h := (tape_facts (n := w.length - 3) (w := w) (by omega) false).2.2.2.2.2
    dsimp [d]
    rw [stateCount_eq w.length hs]
    exact h.le
  have ht : threshold w.length ≤ 3 * d := by
    dsimp [d]
    rw [threshold_eq w.length hs, stateCount_eq w.length hs]
    omega
  have hbound := extensionCleanRank_bound C e d (tval w) (threshold w.length)
    ((a + 1) * d) d start hx
  have hcoarse : extensionCleanRank C start ≤ (a + 19) * d := by
    nlinarith
  exact hcoarse.trans
    (Nat.mul_le_mul_right d (show a + 19 ≤ 10 * (a + 2) by omega))

private theorem extension_scalar_budget (s a R : ℕ) (hs : 3 ≤ s)
    (hR : R ≤ 10 * (a + 2) * stateCount s) :
    1 / (stateCount s : ℝ) + aut (stateCount s) 1 / 3 +
        hrm R / (stateCount s : ℝ) ≤
      workDurationBound s a := by
  let d := stateCount s
  have hdNat : 0 < d := by dsimp [d]; unfold stateCount; positivity
  have hd : (0 : ℝ) < d := by exact_mod_cast hdNat
  have hsreal : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hloga : 0 ≤ Real.log ((a : ℝ) + 2) :=
    Real.log_nonneg (by have h : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)
  have hlogd : Real.log (d : ℝ) ≤ 2 * (s : ℝ) := by
    have heq : (d : ℝ) = (3 : ℝ) ^ (s - 1) := by
      simp only [d, stateCount, Nat.cast_pow, Nat.cast_ofNat]
    rw [heq, Real.log_pow]
    have hsub : ((s - 1 : ℕ) : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast Nat.sub_le s 1
    have hsubnonneg : (0 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlogthree : Real.log (3 : ℝ) ≤ 2 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
    nlinarith
  have hlogten : Real.log (10 : ℝ) ≤ 9 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)]
  have hprod :
      Real.log ((10 * (a + 2) * d : ℕ) : ℝ) =
        Real.log (10 : ℝ) + Real.log ((a : ℝ) + 2) + Real.log (d : ℝ) := by
    have hcast :
        ((10 * (a + 2) * d : ℕ) : ℝ) = 10 * ((a : ℝ) + 2) * (d : ℝ) := by
      push_cast
      ring
    rw [hcast, Real.log_mul (by positivity) hd.ne',
      Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) (by positivity)]
  have hhar : hrm R ≤ 10 + Real.log ((a : ℝ) + 2) + 2 * (s : ℝ) := by
    calc
      hrm R ≤ hrm (10 * (a + 2) * d) := hrm_mono hR
      _ ≤ 1 + Real.log ((10 * (a + 2) * d : ℕ) : ℝ) := hrm_le_log _
      _ ≤ 10 + Real.log ((a : ℝ) + 2) + 2 * (s : ℝ) := by
        rw [hprod]
        linarith
  have haut : (d : ℝ) * aut d 1 ≤ 2 * (1 + 2 * (s : ℝ)) := by
    exact (mul_aut_one_le d).trans
      (mul_le_mul_of_nonneg_left
        ((hrm_le_log d).trans (add_le_add le_rfl hlogd)) (by norm_num))
  change 1 / (d : ℝ) + aut d 1 / 3 + hrm R / (d : ℝ) ≤
    16 * ((s : ℝ) + Real.log ((a : ℝ) + 2)) / (d : ℝ)
  apply (le_div_iff₀ hd).mpr
  have heq :
      (1 / (d : ℝ) + aut d 1 / 3 + hrm R / (d : ℝ)) * d =
        1 + ((d : ℝ) * aut d 1) / 3 + hrm R := by
    field_simp [hd.ne']
    <;> ring
  rw [heq]
  nlinarith

/-- The W4e estimate with the step accuracy a; the active third-phase payload
has accuracy a+1 because restoration has already occurred. -/
theorem extension_meanDuration_le_workDurationBound (C : XCTM Q)
    (e : ExtendState C) (w : List Bool) (a : ℕ) (hs : 3 ≤ w.length) :
    meanDuration C (Plan.workState C (.third (.inr e) w (a + 1)) + unit .signal) ≤
      ENNReal.ofReal (workDurationBound w.length a) := by
  exact (extension_meanDuration_le_potential C e w (a + 1) hs).trans
    (ENNReal.ofReal_le_ofReal
      (extension_scalar_budget w.length a _ hs
        (extensionCleanRank_initial_bound C e w a hs)))


end Ripple.sCRNUniversality.ClockedCTM.Unbounded.StandaloneWork


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open MeasureTheory ProbabilityTheory
open Stochastic Stochastic.MassAction
open WindowAnalysis StandaloneWork
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The pending estimates at all four positions of one active cycle.
The buffer positions allow an arbitrary budget parameter. -/
private theorem pending_first_cycle
    (C : XCTM Q) (q : Q) (w : List Bool) (a budget : ℕ)
    (latent : Bool) (hs : 3 ≤ w.length) (hh : C.mode q ≠ .halt) :
    PendingWorkEstimate C (.first q w a latent) a ∧
      PendingWorkEstimate C
        (Plan.iterate C (.first q w a latent) 1) budget ∧
      PendingWorkEstimate C
        (Plan.iterate C (.first q w a latent) 2) a ∧
      PendingWorkEstimate C
        (Plan.iterate C (.first q w a latent) 3) budget := by
  cases hmode : C.mode q with
  | read =>
      let qr : ReadState C := ⟨q, hmode⟩
      have hfirst :
          Plan.advance C (.first q w a latent) =
            .second (.inl qr) w (a + 1) := by
        dsimp only [Plan.advance]
        split <;> first
          | rfl
          | (exfalso; rename_i hm; rw [hmode] at hm; cases hm)
          | simp_all
      have hone :
          Plan.iterate C (.first q w a latent) 1 =
            .second (.inl qr) w (a + 1) :=
        hfirst
      have htwo :
          Plan.iterate C (.first q w a latent) 2 =
            .third (.inl qr) w (a + 1) :=
        congrArg (Plan.advance C) hone
      have hthree :
          Plan.iterate C (.first q w a latent) 3 =
            .write qr (w.headD false)
              (w.tail ++ [(C.next qr.val (w.headD false)).2]) (a + 1) :=
        congrArg (Plan.advance C) htwo
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact restore_meanDuration_le_workDurationBound C (.inl qr)
          w a latent hs
      · simpa only [hone, PendingWorkEstimate] using (True.intro)
      · simpa only [htwo, PendingWorkEstimate, Plan.tape] using
          read_meanDuration_le_workDurationBound C qr w (a + 1) a hs
      · simpa only [hthree, PendingWorkEstimate] using (True.intro)
  | extend q' =>
      let e : ExtendState C := ⟨q, ⟨q', hmode⟩⟩
      have hfirst :
          Plan.advance C (.first q w a latent) =
            .second (.inr e) w (a + 1) := by
        dsimp only [Plan.advance]
        split <;> first
          | rfl
          | (exfalso; rename_i hm; rw [hmode] at hm; cases hm)
          | simp_all
      have hone :
          Plan.iterate C (.first q w a latent) 1 =
            .second (.inr e) w (a + 1) :=
        hfirst
      have htwo :
          Plan.iterate C (.first q w a latent) 2 =
            .third (.inr e) w (a + 1) :=
        congrArg (Plan.advance C) hone
      have hthree :
          Plan.iterate C (.first q w a latent) 3 =
            .extend e (w ++ [false]) (a + 1) :=
        congrArg (Plan.advance C) htwo
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact restore_meanDuration_le_workDurationBound C (.inr e)
          w a latent hs
      · simpa only [hone, PendingWorkEstimate] using (True.intro)
      · simpa only [htwo, PendingWorkEstimate, Plan.tape] using
          extension_meanDuration_le_workDurationBound C e w a hs
      · simpa only [hthree, PendingWorkEstimate] using (True.intro)
  | halt =>
      exact False.elim (hh hmode)

/-- §13, assembled at the actual scheduled predecessor of each window.
The budget accuracy is i+n, including the extension fourth phase. -/
theorem lemmaEightFourPhases (C : XCTM Q) : LemmaEightFourPhases C := by
  intro w i δ hacc n r hr hk hactive
  have hnonhalt :=
    active_plan_run_nonhalt C i w hacc.1
      (4 * n + r - 1) hactive
  interval_cases r
  · have hn : 1 ≤ n := by omega
    have he : 4 * n + 0 - 1 = 4 * (n - 1) + 3 := by omega
    have hp := plan_at_step C i w hacc.1 (n - 1)
      (fun j hj => hnonhalt j (by omega))
    have hcur :
        C.mode (C.runT (C.start, w) (n - 1)).1 ≠ .halt :=
      hnonhalt (n - 1) (by omega)
    have hsrun : 3 ≤ (C.runT (C.start, w) (n - 1)).2.length := by
      have hv := plan_valid C i w hacc.1 (4 * (n - 1))
      simpa only [hp, Plan.tape] using hv
    rw [he, plan_add, hp]
    exact (pending_first_cycle C
      (C.runT (C.start, w) (n - 1)).1
      (C.runT (C.start, w) (n - 1)).2
      (i + (n - 1)) (i + n) (previousExtension C w (n - 1))
      hsrun hcur).2.2.2
  · have he : 4 * n + 1 - 1 = 4 * n := by omega
    have hp := plan_at_step C i w hacc.1 n
      (fun j hj => hnonhalt j (by omega))
    have hcur : C.mode (C.runT (C.start, w) n).1 ≠ .halt :=
      hnonhalt n (by omega)
    have hsrun : 3 ≤ (C.runT (C.start, w) n).2.length := by
      have hv := plan_valid C i w hacc.1 (4 * n)
      simpa only [hp, Plan.tape] using hv
    rw [he, hp]
    exact (pending_first_cycle C
      (C.runT (C.start, w) n).1 (C.runT (C.start, w) n).2
      (i + n) (i + n) (previousExtension C w n) hsrun hcur).1
  · have he : 4 * n + 2 - 1 = 4 * n + 1 := by omega
    have hp := plan_at_step C i w hacc.1 n
      (fun j hj => hnonhalt j (by omega))
    have hcur : C.mode (C.runT (C.start, w) n).1 ≠ .halt :=
      hnonhalt n (by omega)
    have hsrun : 3 ≤ (C.runT (C.start, w) n).2.length := by
      have hv := plan_valid C i w hacc.1 (4 * n)
      simpa only [hp, Plan.tape] using hv
    rw [he, plan_add, hp]
    exact (pending_first_cycle C
      (C.runT (C.start, w) n).1 (C.runT (C.start, w) n).2
      (i + n) (i + n) (previousExtension C w n) hsrun hcur).2.1
  · have he : 4 * n + 3 - 1 = 4 * n + 2 := by omega
    have hp := plan_at_step C i w hacc.1 n
      (fun j hj => hnonhalt j (by omega))
    have hcur : C.mode (C.runT (C.start, w) n).1 ≠ .halt :=
      hnonhalt n (by omega)
    have hsrun : 3 ≤ (C.runT (C.start, w) n).2.length := by
      have hv := plan_valid C i w hacc.1 (4 * n)
      simpa only [hp, Plan.tape] using hv
    rw [he, plan_add, hp]
    exact (pending_first_cycle C
      (C.runT (C.start, w) n).1 (C.runT (C.start, w) n).2
      (i + n) (i + n) (previousExtension C w n) hsrun hcur).2.2.1

/-- The first-error estimate now has no restart or work-duration premise. -/
theorem firstErrorStep_le_markov
    (C : XCTM Q) (w : List Bool) (i : ℕ) (δ : ℝ)
    (hacc : AdmissibleAccuracy w i δ) (n : ℕ) :
    jumpLaw C i w (firstErrorStep C (initial C i w) n) ≤
      ENNReal.ofReal (2688 / ((i : ℝ) + (n : ℝ)) ^ 3) :=
  firstErrorStep_le_of_note_estimates C w i δ hacc
    (lemmaEightFourPhases C) (rawStateRestart C (initial C i w)) n

/-- ErrorClaim needs only actual occupation and qualitative tail finiteness. -/
theorem errorClaim_of_terminal_estimates (C : XCTM Q)
    (hLemmaFourteenFour_occupation : TimeAnalysis.LemmaFourteenFourOccupation C)
    (hLemmaFourteenFour_tail : TimeAnalysis.LemmaFourteenFourTailFinite C) :
    ErrorClaim C :=
  errorClaim_of_note_window_estimates C (lemmaEightFourPhases C)
    (fun w i δ _ => rawStateRestart C (initial C i w))
    (TimeAnalysis.allGoodWindowMeansFinite_of_occupation_and_tail C
      (lemmaEightFourPhases C)
      hLemmaFourteenFour_occupation hLemmaFourteenFour_tail)

/-- The two mechanism inputs are discharged. These are exactly the three
remaining note inputs of the combined error/time reducer. -/
theorem error_and_timeClaims_of_remaining_estimates (C : XCTM Q)
    (hLemmaFourteenThree : TimeAnalysis.LemmaFourteenThreeVolume C)
    (hLemmaFourteenFour_occupation : TimeAnalysis.LemmaFourteenFourOccupation C)
    (hLemmaFourteenFour_tail : TimeAnalysis.LemmaFourteenFourTailFinite C) :
    ErrorClaim C ∧ TimeClaim C :=
  error_and_timeClaims_of_note_estimates C
    (lemmaEightFourPhases C)
    (fun w i δ _ => rawStateRestart C (initial C i w))
    hLemmaFourteenThree
    hLemmaFourteenFour_occupation hLemmaFourteenFour_tail

/-- The time conclusion with precisely the remaining three named inputs. -/
theorem timeClaim_of_remaining_estimates (C : XCTM Q)
    (hLemmaFourteenThree : TimeAnalysis.LemmaFourteenThreeVolume C)
    (hLemmaFourteenFour_occupation : TimeAnalysis.LemmaFourteenFourOccupation C)
    (hLemmaFourteenFour_tail : TimeAnalysis.LemmaFourteenFourTailFinite C) :
    TimeClaim C :=
  (error_and_timeClaims_of_remaining_estimates C
    hLemmaFourteenThree
    hLemmaFourteenFour_occupation hLemmaFourteenFour_tail).2

end Ripple.sCRNUniversality.ClockedCTM.Unbounded

end
