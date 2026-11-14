-- Ripple/Kurtz/StrongApprox/PoissonStoppingLine.lean
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
import Ripple.Kurtz.StrongApprox.PoissonCellDriverLaw
import Ripple.Kurtz.StrongApprox.RecordPastFreshness
import Ripple.Kurtz.StrongApprox.PoissonCellTimeChangeFactor

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Topology Preorder
open scoped ENNReal NNReal BigOperators
open ExponentialRace

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace E]

/-- One real-valued independent Poisson driver family, flattened over channel
and nonnegative internal time.  The values are integer-valued on the support
of `flatPoissonLaw`; using `ℝ` makes telescoping adjacent increments exact. -/
abbrev FlatDriver (ι : Type*) := (ι × ℝ≥0) → ℝ

/-- Complete family of cell-built Poisson paths, flattened and cast to `ℝ`. -/
def flatCellDriver (c : CellFamily ι) : FlatDriver ι :=
  fun p => (cellPath (p.2 : ℝ) (c p.1) : ℝ)

@[fun_prop]
theorem measurable_flatCellDriver :
    Measurable (flatCellDriver (ι := ι)) := by
  apply measurable_pi_lambda
  intro p
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    ((measurable_cellPath (p.2 : ℝ)).comp (measurable_pi_apply p.1))

/-- The universal law of the flattened cell driver. -/
noncomputable def flatPoissonLaw (ι : Type*) [Fintype ι] :
    Measure (FlatDriver ι) :=
  (cellFamilyLaw ι).map flatCellDriver

instance flatPoissonLaw_isProbabilityMeasure :
    IsProbabilityMeasure (flatPoissonLaw ι) := by
  unfold flatPoissonLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_flatCellDriver (ι := ι)).aemeasurable

/-- Deterministic truncation, followed by one artificial unit arrival in each
successive unit interval.  It agrees with the original driver through `u` and
always supplies a later arrival.  This is the causal replay used below. -/
def completePast (u : ι → ℝ≥0) (Y : FlatDriver ι) : FlatDriver ι :=
  fun p =>
    if p.2 ≤ u p.1 then Y p
    else Y (p.1, u p.1) + ⌊((p.2 : ℝ) - (u p.1 : ℝ))⌋₊

@[fun_prop]
theorem measurable_completePast (u : ι → ℝ≥0) :
    Measurable (completePast u : FlatDriver ι → FlatDriver ι) := by
  apply measurable_pi_lambda
  intro p
  by_cases hp : p.2 ≤ u p.1
  · simpa [completePast, hp] using
      (measurable_pi_apply p : Measurable fun Y : FlatDriver ι => Y p)
  · simpa [completePast, hp] using
      ((measurable_pi_apply (p.1, u p.1)).add measurable_const)

@[simp]
theorem completePast_apply_of_le
    (u : ι → ℝ≥0) (Y : FlatDriver ι) {l : ι} {t : ℝ≥0}
    (ht : t ≤ u l) :
    completePast u Y (l, t) = Y (l, t) := by
  simp [completePast, ht]

@[simp]
theorem completePast_idem (u : ι → ℝ≥0) (Y : FlatDriver ι) :
    completePast u (completePast u Y) = completePast u Y := by
  funext p
  by_cases hp : p.2 ≤ u p.1 <;> simp [completePast, hp]

/-- Driver increments after the deterministic or random internal-clock vector
`u`. -/
def shiftDriver (u : ι → ℝ≥0) (Y : FlatDriver ι) : FlatDriver ι :=
  fun p => Y (p.1, u p.1 + p.2) - Y (p.1, u p.1)

@[fun_prop]
theorem measurable_shiftDriver (u : ι → ℝ≥0) :
    Measurable (shiftDriver u : FlatDriver ι → FlatDriver ι) := by
  apply measurable_pi_lambda
  intro p
  exact (measurable_pi_apply (p.1, u p.1 + p.2)).sub
    (measurable_pi_apply (p.1, u p.1))

/-- The first strictly positive rational observation time.  The infimum is
formed in `ℝ≥0∞`, so the value is `⊤` if the path has no later arrival. -/
def firstWaitENN (Y : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0,
    if 0 < q ∧ 0 < Y (q : ℝ≥0) then ((q : ℝ≥0) : ℝ≥0∞) else ⊤

/-- Real readout of `firstWaitENN`; the exceptional value `⊤` is sent to zero.
That exceptional event has measure zero under every shifted Poisson law. -/
def firstWait (Y : ℝ≥0 → ℝ) : ℝ :=
  if firstWaitENN Y = ⊤ then 0 else (firstWaitENN Y).toReal

@[fun_prop]
theorem measurable_firstWait :
    Measurable (firstWait : (ℝ≥0 → ℝ) → ℝ) := by
  have hi : Measurable (firstWaitENN : (ℝ≥0 → ℝ) → ℝ≥0∞) := by
    unfold firstWaitENN
    apply Measurable.iInf
    intro q
    have hset : MeasurableSet
        {Y : ℝ≥0 → ℝ | 0 < q ∧ 0 < Y (q : ℝ≥0)} := by
      by_cases hq : 0 < q
      · simp only [hq, true_and]
        exact measurableSet_lt measurable_const (measurable_pi_apply _)
      · simp [hq]
    exact Measurable.ite hset measurable_const measurable_const
  unfold firstWait
  exact Measurable.ite
    (hi (measurableSet_singleton ⊤)) measurable_const
    (ENNReal.measurable_toReal.comp hi)

/-- Vector of first waits in a flattened family. -/
def firstWaitVector (Y : FlatDriver ι) : ι → ℝ :=
  fun l => firstWait fun t => Y (l, t)

@[fun_prop]
theorem measurable_firstWaitVector :
    Measurable (firstWaitVector : FlatDriver ι → ι → ℝ) := by
  apply measurable_pi_lambda
  intro l
  exact measurable_firstWait.comp
    (measurable_pi_lambda _ fun t => measurable_pi_apply (l, t))

/-- Waits from an internal-clock vector. -/
def residualWait (u : ι → ℝ≥0) (Y : FlatDriver ι) : ι → ℝ :=
  firstWaitVector (shiftDriver u Y)

@[fun_prop]
theorem measurable_residualWait (u : ι → ℝ≥0) :
    Measurable (residualWait u : FlatDriver ι → ι → ℝ) :=
  measurable_firstWaitVector.comp (measurable_shiftDriver u)

/-! ### Deterministic past/future independence -/

theorem measurable_cellPathR (s : ℝ) :
    Measurable (fun c : ℕ → CellSpace => (cellPath s c : ℝ)) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_cellPath s)

/-- The real-valued cell path has independent increments.  This is transferred
from the SIP realization through the complete path-law identity. -/
theorem hasIndepIncrements_cellPath_real :
    HasIndepIncrements
      (fun t : ℝ≥0 => fun c : ℕ → CellSpace =>
        (cellPath (t : ℝ) c : ℝ)) cellArrayLaw := by
  intro n t ht
  have hpath := cellPath_law measurable_sipN iIndepFun_sipN
    sipMeasure_sipN_eq
  have hmSip : Measurable
      (fun x : PathSpace SIPSpace => fun s : ℝ => sipPath s x) :=
    measurable_pathMap measurable_sipN
  have hlaw : ∀ {B : Type} [MeasurableSpace B] (G : (ℝ → ℕ) → B),
      Measurable G →
      cellArrayLaw.map (fun c => G (fun s => cellPath s c)) =
        (pathMeasure sipMeasure).map (fun x => G (fun s => sipPath s x)) := by
    intro B _ G hG
    calc
      cellArrayLaw.map (fun c => G (fun s => cellPath s c)) =
          (cellArrayLaw.map cellPathMap).map G :=
        (Measure.map_map hG measurable_cellPathMap).symm
      _ = ((pathMeasure sipMeasure).map
            (fun x t => poisPath sipN t x)).map G := by rw [hpath]
      _ = (pathMeasure sipMeasure).map
            (fun x => G (fun s => sipPath s x)) :=
        Measure.map_map hG hmSip
  let F : (ℝ → ℕ) → Fin n → ℝ := fun Y i =>
    (Y (t i.succ : ℝ) : ℝ) - Y (t i.castSucc : ℝ)
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_pi_apply (t i.succ : ℝ))).sub
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (measurable_pi_apply (t i.castSucc : ℝ)))
  have hFi : ∀ i : Fin n, Measurable
      (fun Y : ℝ → ℕ => (Y (t i.succ : ℝ) : ℝ) - Y (t i.castSucc : ℝ)) := by
    intro i
    exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_pi_apply (t i.succ : ℝ))).sub
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (measurable_pi_apply (t i.castSucc : ℝ)))
  have hsip := hasIndepIncrements_poisPath_real
    measurable_sipN iIndepFun_sipN sipMeasure_sipN_eq
      n (fun i => (t i : ℝ)) (fun _ _ h => by exact_mod_cast ht h)
  have hcellAE : ∀ i : Fin n, AEMeasurable
      (fun c : ℕ → CellSpace => (cellPath (t i.succ : ℝ) c : ℝ) -
        cellPath (t i.castSucc : ℝ) c) cellArrayLaw := fun i =>
    ((measurable_cellPathR _).sub (measurable_cellPathR _)).aemeasurable
  have hsipAE : ∀ i : Fin n, AEMeasurable
      (fun x : PathSpace SIPSpace => (poisPath sipN (t i.succ : ℝ) x : ℝ) -
        poisPath sipN (t i.castSucc : ℝ) x) (pathMeasure sipMeasure) := fun i =>
    (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_poisPath measurable_sipN _)).sub
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_poisPath measurable_sipN _))).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hsipAE] at hsip
  rw [iIndepFun_iff_map_fun_eq_pi_map hcellAE]
  calc
    cellArrayLaw.map (fun (c : ℕ → CellSpace) (i : Fin n) =>
        (cellPath (t i.succ : ℝ) c : ℝ) - cellPath (t i.castSucc : ℝ) c) =
        (pathMeasure sipMeasure).map
          (fun (x : PathSpace SIPSpace) (i : Fin n) =>
            (sipPath (t i.succ : ℝ) x : ℝ) -
              sipPath (t i.castSucc : ℝ) x) := hlaw F hF
    _ = Measure.pi (fun i : Fin n => (pathMeasure sipMeasure).map
          (fun x : PathSpace SIPSpace => (sipPath (t i.succ : ℝ) x : ℝ) -
            sipPath (t i.castSucc : ℝ) x)) := hsip
    _ = Measure.pi (fun i : Fin n => cellArrayLaw.map
          (fun c : ℕ → CellSpace => (cellPath (t i.succ : ℝ) c : ℝ) -
            cellPath (t i.castSucc : ℝ) c)) := by
      congr 1
      funext i
      exact (hlaw _ (hFi i)).symm

/-- Telescoping over the first `a` increments. -/
private theorem telescope_fin (g : ℕ → ℝ) (n a : ℕ) (ha : a ≤ n) :
    ∑ r : Fin n, (if r.val < a then g (r.val + 1) - g r.val else 0) =
      g a - g 0 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if j < a then g (j + 1) - g j else 0) n,
    ← Finset.sum_filter]
  have : (Finset.range n).filter (· < a) = Finset.range a := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.sum_range_sub]

/-- Finite observations before `u` are independent of finite observations of
the shifted future.  The proof puts all requested times on one sorted grid,
uses adjacent independent increments, and reconstructs values by telescoping
sums over increment indices. -/
theorem finite_before_after_indep
    (u : ℝ≥0) (I J : Finset ℝ≥0) :
    IndepFun
      (fun c : ℕ → CellSpace => fun i : I =>
        (cellPath (min i.1 u : ℝ) c : ℝ))
      (fun c : ℕ → CellSpace => fun j : J =>
        (cellPath (u + j.1 : ℝ) c : ℝ) -
          cellPath (u : ℝ) c) cellArrayLaw := by
  classical
  let K : Finset ℝ≥0 :=
    insert 0 ((I.image fun t => min t u) ∪ insert u (J.image fun t => u + t))
  have hKpos : 0 < K.card := Finset.card_pos.mpr ⟨0, by simp [K]⟩
  obtain ⟨n, hn⟩ : ∃ n, K.card = n + 1 :=
    ⟨K.card - 1, (Nat.succ_pred_eq_of_pos hKpos).symm⟩
  let e := K.orderIsoOfFin hn
  let τ : Fin (n + 1) → ℝ≥0 := fun k => (e k).1
  have hτs : StrictMono τ := fun a b h => e.strictMono h
  have hmemK0 : (0 : ℝ≥0) ∈ K := by simp [K]
  have hmemKu : u ∈ K := by simp [K]
  have hmemKi : ∀ i : I, min i.1 u ∈ K := fun i => by
    simp only [K, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inl ⟨i.1, i.2, rfl⟩)
  have hmemKj : ∀ j : J, u + j.1 ∈ K := fun j => by
    simp only [K, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inr ⟨j.1, j.2, rfl⟩))
  let idxOf : ℝ≥0 → Fin (n + 1) := fun s =>
    if h : s ∈ K then e.symm ⟨s, h⟩ else 0
  have hτidx : ∀ s, s ∈ K → τ (idxOf s) = s := by
    intro s hs
    simp [idxOf, hs, τ]
  have hτ0 : τ 0 = 0 := by
    have h0 : τ (idxOf 0) = 0 := hτidx 0 hmemK0
    have hle : τ 0 ≤ τ (idxOf 0) := hτs.monotone (Fin.zero_le _)
    rw [h0] at hle
    exact le_antisymm hle zero_le
  have hΔ := hasIndepIncrements_cellPath_real n τ hτs.monotone
  let X : ℝ≥0 → (ℕ → CellSpace) → ℝ := fun s c => (cellPath (s : ℝ) c : ℝ)
  let Δ : Fin n → (ℕ → CellSpace) → ℝ := fun r c =>
    X (τ r.succ) c - X (τ r.castSucc) c
  let Lidx : Finset (Fin n) := Finset.univ.filter fun r => τ r.succ ≤ u
  let Ridx : Finset (Fin n) := Finset.univ.filter fun r => u < τ r.succ
  have hdisj : Disjoint Lidx Ridx := by
    rw [Finset.disjoint_left]
    intro r hrL hrR
    simp only [Lidx, Ridx, Finset.mem_filter, Finset.mem_univ,
      true_and] at hrL hrR
    exact absurd hrL (not_le.mpr hrR)
  have hΔm : ∀ r : Fin n, Measurable (Δ r) := fun r =>
    (measurable_cellPathR _).sub (measurable_cellPathR _)
  have hgroups := iIndepFun.indepFun_finset Lidx Ridx hdisj hΔ hΔm
  -- telescoping at a grid index
  have htele : ∀ (c : ℕ → CellSpace) (a : Fin (n + 1)),
      ∑ r : Fin n, (if r.val < a.val then Δ r c else 0) =
        X (τ a) c - X (τ 0) c := by
    intro c a
    let g : ℕ → ℝ := fun j => if h : j < n + 1 then X (τ ⟨j, h⟩) c else 0
    have hg : ∀ r : Fin n, Δ r c = g (r.val + 1) - g r.val := by
      intro r
      simp only [Δ, g, dif_pos (Nat.lt_succ_of_lt r.isLt), dif_pos (Nat.succ_lt_succ r.isLt)]
      rfl
    have := telescope_fin g n a.val (Nat.lt_succ_iff.mp a.isLt)
    have h1 : ∑ r : Fin n, (if r.val < a.val then Δ r c else 0) =
        ∑ r : Fin n, (if r.val < a.val then g (r.val + 1) - g r.val else 0) :=
      Finset.sum_congr rfl fun r _ => by rw [hg r]
    rw [h1, this]
    simp only [g, dif_pos a.isLt, dif_pos (Nat.succ_pos n)]
    rfl
  have hX0 : ∀ c, X 0 c = 0 := fun c => by
    simp [X, cellPath, cellHit, hitCount]
  let A : (ℕ → CellSpace) → (Lidx → ℝ) := fun c r => Δ r.1 c
  let B : (ℕ → CellSpace) → (Ridx → ℝ) := fun c r => Δ r.1 c
  let readLeft : (Lidx → ℝ) → (I → ℝ) := fun z i =>
    ∑ r : Lidx, if r.1.val < (idxOf (min i.1 u)).val then z r else 0
  let readRight : (Ridx → ℝ) → (J → ℝ) := fun z j =>
    ∑ r : Ridx, if r.1.val < (idxOf (u + j.1)).val then z r else 0
  have hreadLeftM : Measurable readLeft := by
    apply measurable_pi_lambda
    intro i
    apply Finset.measurable_sum
    intro r _
    split_ifs
    · exact measurable_pi_apply r
    · exact measurable_const
  have hreadRightM : Measurable readRight := by
    apply measurable_pi_lambda
    intro j
    apply Finset.measurable_sum
    intro r _
    split_ifs
    · exact measurable_pi_apply r
    · exact measurable_const
  have hleftEq :
      (fun c : ℕ → CellSpace => fun i : I =>
        (cellPath (min i.1 u : ℝ) c : ℝ)) = readLeft ∘ A := by
    funext c i
    simp only [Function.comp_apply, readLeft, A]
    have hm : (min (i.1 : ℝ) (u : ℝ)) = ((min i.1 u : ℝ≥0) : ℝ) :=
      (NNReal.coe_min _ _).symm
    set a := idxOf (min i.1 u) with ha
    have hτa : τ a = min i.1 u := hτidx _ (hmemKi i)
    have hsub : ∀ r : Fin n, r.val < a.val → τ r.succ ≤ u := by
      intro r hr
      have : r.succ ≤ a := by
        rw [Fin.le_def]
        simp only [Fin.val_succ]
        omega
      exact (hτs.monotone this).trans (hτa ▸ min_le_right _ _)
    refine Eq.trans ?_ (Finset.sum_coe_sort Lidx
      (fun r => if r.val < a.val then Δ r c else 0)).symm
    have hall : ∑ r ∈ Lidx, (if r.val < a.val then Δ r c else 0) =
        ∑ r : Fin n, (if r.val < a.val then Δ r c else 0) := by
      simp only [Lidx]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : r.val < a.val
      · simp [hr, hsub r hr]
      · simp [hr]
    rw [hall, htele c a, hτa, hτ0, hX0, sub_zero, hm]
  have hrightEq :
      (fun c : ℕ → CellSpace => fun j : J =>
        (cellPath (u + j.1 : ℝ) c : ℝ) - cellPath (u : ℝ) c) =
        readRight ∘ B := by
    funext c j
    simp only [Function.comp_apply, readRight, B]
    set b := idxOf (u + j.1) with hb
    set a0 := idxOf u with ha0
    have hτb : τ b = u + j.1 := hτidx _ (hmemKj j)
    have hτa0 : τ a0 = u := hτidx _ hmemKu
    have hab : a0 ≤ b := by
      refine hτs.le_iff_le.mp ?_
      rw [hτb, hτa0]
      exact le_add_of_nonneg_right zero_le
    refine Eq.trans ?_ (Finset.sum_coe_sort Ridx
      (fun r => if r.val < b.val then Δ r c else 0)).symm
    have hall : ∑ r ∈ Ridx, (if r.val < b.val then Δ r c else 0) =
        ∑ r : Fin n, (if r.val < b.val then Δ r c else 0) -
          ∑ r : Fin n, (if r.val < a0.val then Δ r c else 0) := by
      rw [← Finset.sum_sub_distrib]
      simp only [Ridx]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : a0.val ≤ r.val
      · have : u < τ r.succ := by
          rw [← hτa0]
          refine hτs ?_
          rw [Fin.lt_def]
          simp only [Fin.val_succ]
          omega
        have hnot : ¬ r.val < a0.val := not_lt.mpr hr
        simp [this, hnot]
      · have hlt : r.val < a0.val := not_le.mp hr
        have : ¬ u < τ r.succ := by
          rw [← hτa0]
          refine not_lt.mpr (hτs.monotone ?_)
          rw [Fin.le_def]
          simp only [Fin.val_succ]
          omega
        have hrb : r.val < b.val := lt_of_lt_of_le hlt hab
        simp [this, hlt, hrb]
    rw [hall, htele c b, htele c a0, hτb, hτa0]
    simp only [X, NNReal.coe_add]
    ring
  rw [hleftEq, hrightEq]
  exact hgroups.comp hreadLeftM hreadRightM

/-- One channel: the completed deterministic past and the complete shifted
future process are independent. -/
theorem indepFun_completePast_shift_one (u : ℝ≥0) :
    IndepFun
      (fun c : ℕ → CellSpace => fun t : ℝ≥0 =>
        if t ≤ u then (cellPath (t : ℝ) c : ℝ)
        else (cellPath (u : ℝ) c : ℝ) +
          ⌊((t : ℝ) - (u : ℝ))⌋₊)
      (fun c : ℕ → CellSpace => fun t : ℝ≥0 =>
        (cellPath (u + t : ℝ) c : ℝ) -
          cellPath (u : ℝ) c) cellArrayLaw := by
  classical
  apply IndepFun.process_indepFun_process
  · intro t
    by_cases ht : t ≤ u
    · simpa [ht] using measurable_cellPathR (t : ℝ)
    · simpa [ht] using (measurable_cellPathR (u : ℝ)).add_const _
  · intro t
    exact (measurable_cellPathR _).sub (measurable_cellPathR _)
  · intro I J
    let I' : Finset ℝ≥0 := I ∪ {u}
    have hI : ∀ i : I, i.1 ∈ I' := fun i => Finset.mem_union_left _ i.2
    have hu : u ∈ I' := Finset.mem_union_right _ (Finset.mem_singleton_self u)
    let φ : (I' → ℝ) → (I → ℝ) := fun z i =>
      if i.1 ≤ u then z ⟨i.1, hI i⟩ else z ⟨u, hu⟩ + ⌊((i.1 : ℝ) - (u : ℝ))⌋₊
    have hφ : Measurable φ := by
      apply measurable_pi_lambda
      intro i
      by_cases hi : i.1 ≤ u
      · simpa [φ, hi] using measurable_pi_apply (⟨i.1, hI i⟩ : I')
      · simpa [φ, hi] using (measurable_pi_apply (⟨u, hu⟩ : I')).add_const _
    have hind := finite_before_after_indep u I' J
    have hcomp := hind.comp hφ measurable_id
    have key : (fun (c : ℕ → CellSpace) (i : I) =>
        if i.1 ≤ u then (cellPath (i.1 : ℝ) c : ℝ)
        else (cellPath (u : ℝ) c : ℝ) + ⌊((i.1 : ℝ) - (u : ℝ))⌋₊) =
        φ ∘ (fun (c : ℕ → CellSpace) (i : I') =>
          (cellPath (min i.1 u : ℝ) c : ℝ)) := by
      funext c i
      simp only [Function.comp_apply, φ]
      by_cases hi : i.1 ≤ u
      · have : (min (i.1 : ℝ) (u : ℝ)) = (i.1 : ℝ) :=
          min_eq_left (by exact_mod_cast hi)
        simp [hi, this]
      · have : (min (u : ℝ) (u : ℝ)) = (u : ℝ) := min_self _
        simp [hi, this]
    rw [← key] at hcomp
    exact hcomp

/-! ### Elementary properties of `cellPath` -/

theorem cellPath_eq_poisPath (c : ℕ → CellSpace) (s : ℝ) :
    cellPath s c = poisPath canonicalCount s (cellSample c) :=
  (poisPath_cellSample c s).symm

theorem cellPath_mono {s t : ℝ} (h : s ≤ t) (c : ℕ → CellSpace) :
    cellPath s c ≤ cellPath t c := by
  rw [cellPath_eq_poisPath, cellPath_eq_poisPath]
  exact poisPath_mono _ h _

theorem cellPath_eventually_right (t : ℝ) (c : ℕ → CellSpace) :
    ∀ᶠ s in 𝓝[≥] t, cellPath s c = cellPath t c := by
  simp only [cellPath_eq_poisPath]
  exact poisPath_eventually_right _ t _

theorem cellPath_zero (c : ℕ → CellSpace) : cellPath 0 c = 0 := by
  rw [cellPath_eq_poisPath]
  exact poisPath_zero _ _

/-- Transfer of path functionals from the cell law to the SIP realization. -/
theorem cellArrayLaw_map_path {B : Type} [MeasurableSpace B]
    (G : (ℝ → ℕ) → B) (hG : Measurable G) :
    cellArrayLaw.map (fun c => G (fun s => cellPath s c)) =
      (pathMeasure sipMeasure).map (fun x => G (fun s => sipPath s x)) := by
  have hpath := cellPath_law measurable_sipN iIndepFun_sipN
    sipMeasure_sipN_eq
  have hmSip : Measurable
      (fun x : PathSpace SIPSpace => fun s : ℝ => sipPath s x) :=
    measurable_pathMap measurable_sipN
  calc
    cellArrayLaw.map (fun c => G (fun s => cellPath s c)) =
        (cellArrayLaw.map cellPathMap).map G :=
      (Measure.map_map hG measurable_cellPathMap).symm
    _ = ((pathMeasure sipMeasure).map
          (fun x t => poisPath sipN t x)).map G := by rw [hpath]
    _ = (pathMeasure sipMeasure).map
          (fun x => G (fun s => sipPath s x)) :=
      Measure.map_map hG hmSip

/-- Exact probability of no arrival in a window. -/
theorem cellPath_increment_zero (u t : ℝ≥0) :
    cellArrayLaw {c | cellPath ((u : ℝ) + t) c - cellPath (u : ℝ) c = 0} =
      ENNReal.ofReal (Real.exp (-(t : ℝ))) := by
  let G : (ℝ → ℕ) → ℕ := fun Y => Y ((u : ℝ) + t) - Y (u : ℝ)
  have hG : Measurable G := by
    have : Measurable (fun Y : ℝ → ℕ => (Y ((u : ℝ) + t), Y (u : ℝ))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact (measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp this
  have h := cellArrayLaw_map_path G hG
  have hmeas : MeasurableSet ({0} : Set ℕ) := measurableSet_singleton 0
  have h1 := congrArg (fun μ : Measure ℕ => μ {0}) h
  dsimp only at h1
  rw [Measure.map_apply
      (show Measurable (fun c : ℕ → CellSpace => G (fun s => cellPath s c)) from
        hG.comp measurable_cellPathMap) hmeas,
    Measure.map_apply
      (show Measurable (fun x : PathSpace SIPSpace => G (fun s => sipPath s x)) from
        hG.comp (measurable_pathMap measurable_sipN)) hmeas] at h1
  have h2 := sipPathMeasure_increment_eq (s := (u : ℝ)) (t := (u : ℝ) + t)
    u.2 (by simp) 0
  calc
    cellArrayLaw {c | cellPath ((u : ℝ) + t) c - cellPath (u : ℝ) c = 0} =
        cellArrayLaw ((fun c : ℕ → CellSpace => G (fun s => cellPath s c)) ⁻¹' {0}) :=
      rfl
    _ = (pathMeasure sipMeasure)
          ((fun x : PathSpace SIPSpace => G (fun s => sipPath s x)) ⁻¹' {0}) := h1
    _ = (pathMeasure sipMeasure)
          {x | sipPath ((u : ℝ) + t) x - sipPath (u : ℝ) x = ((0 : ℕ) : ℕ)} := rfl
    _ = ENNReal.ofReal (poisTerm 0 (((u : ℝ) + t) - u)) := h2
    _ = ENNReal.ofReal (Real.exp (-(t : ℝ))) := by simp [poisTerm]

/-! ### First wait of an integer-valued right-continuous path -/

theorem count_eq_zero_of_lt_firstWait
    {Y : ℝ≥0 → ℕ} (hmono : Monotone Y) (hY0 : Y 0 = 0) {t : ℝ≥0}
    (h : (t : ℝ) < firstWait fun s => (Y s : ℝ)) : Y t = 0 := by
  by_contra hne
  have hpos : 0 < Y t := Nat.pos_of_ne_zero hne
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hne hY0
  have hle : firstWaitENN (fun s => (Y s : ℝ)) ≤ (t : ℝ≥0∞) := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (show ((t : ℝ)) < (t : ℝ) + ε by
        have : (0 : ℝ) < ε := by exact_mod_cast hε
        linarith)
    have hq0 : (0 : ℚ) ≤ q := by
      have : (0 : ℝ) ≤ (t : ℝ) := t.2
      exact_mod_cast (this.trans hq1.le)
    let qn : ℚ≥0 := ⟨q, hq0⟩
    have hqt : t ≤ (qn : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      show (t : ℝ) ≤ (q : ℝ)
      exact hq1.le
    have hqpos : 0 < qn := by
      have : (0 : ℝ) < q := lt_of_le_of_lt t.2 hq1
      exact_mod_cast this
    calc
      firstWaitENN (fun s => (Y s : ℝ)) ≤ ((qn : ℝ≥0) : ℝ≥0∞) := by
        unfold firstWaitENN
        refine (iInf_le _ qn).trans ?_
        have hY : 0 < (Y (qn : ℝ≥0) : ℝ) := by
          exact_mod_cast lt_of_lt_of_le hpos (hmono hqt)
        rw [if_pos ⟨hqpos, hY⟩]
      _ ≤ (t : ℝ≥0∞) + (ε : ℝ≥0∞) := by
        have : ((qn : ℝ≥0) : ℝ≥0∞) ≤ ((t + ε : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
          show (q : ℝ) ≤ (t : ℝ) + ε
          exact hq2.le
        simpa using this
  have hne_top : firstWaitENN (fun s => (Y s : ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  have : firstWait (fun s => (Y s : ℝ)) ≤ t := by
    unfold firstWait
    rw [if_neg hne_top]
    have := ENNReal.toReal_mono ENNReal.coe_ne_top hle
    simpa using this
  linarith

theorem lt_firstWait_of_count_eq_zero
    {Y : ℝ≥0 → ℕ} (hmono : Monotone Y)
    (hright : ∀ s, ∀ᶠ r in 𝓝[≥] s, Y r = Y s)
    (hnz : ∃ s, 0 < Y s) {t : ℝ≥0} (ht : Y t = 0) :
    (t : ℝ) < firstWait fun s => (Y s : ℝ) := by
  obtain ⟨u', hu', hIco⟩ := (mem_nhdsGE_iff_exists_Ico_subset).mp (hright t)
  have hlow : (u' : ℝ≥0∞) ≤ firstWaitENN (fun s => (Y s : ℝ)) := by
    unfold firstWaitENN
    refine le_iInf fun q => ?_
    split_ifs with hq
    · have hYq : 0 < Y (q : ℝ≥0) := by
        have h2 := hq.2
        dsimp only at h2
        exact_mod_cast h2
      by_contra hlt
      push_neg at hlt
      have hqu : (q : ℝ≥0) < u' := by exact_mod_cast hlt
      by_cases htq : t ≤ (q : ℝ≥0)
      · have := hIco ⟨htq, hqu⟩
        simp only [Set.mem_setOf_eq] at this
        omega
      · have : Y (q : ℝ≥0) ≤ Y t := hmono (le_of_not_ge htq)
        omega
    · exact le_top
  obtain ⟨s, hs⟩ := hnz
  have hfin : firstWaitENN (fun s => (Y s : ℝ)) ≠ ⊤ := by
    obtain ⟨q, hq⟩ := exists_rat_gt (s : ℝ)
    have hq0 : (0 : ℚ) ≤ q := by
      have : (0 : ℝ) ≤ s := s.2
      exact_mod_cast (this.trans hq.le)
    let qn : ℚ≥0 := ⟨q, hq0⟩
    have hqs : s ≤ (qn : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      exact hq.le
    have hqpos : 0 < qn := by
      have : (0 : ℝ) < q := lt_of_le_of_lt s.2 hq
      exact_mod_cast this
    have hY : 0 < (Y (qn : ℝ≥0) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hs (hmono hqs)
    apply ne_top_of_le_ne_top (b := ((qn : ℝ≥0) : ℝ≥0∞)) ENNReal.coe_ne_top
    unfold firstWaitENN
    refine (iInf_le _ qn).trans ?_
    rw [if_pos ⟨hqpos, hY⟩]
  unfold firstWait
  rw [if_neg hfin]
  have := ENNReal.toReal_mono hfin hlow
  simp only [ENNReal.coe_toReal] at this
  have hut : (t : ℝ) < u' := by exact_mod_cast hu'
  linarith

/-- The first future waiting time of one channel has the unit exponential
law. -/
theorem firstWait_shift_law_one (u : ℝ≥0) :
    cellArrayLaw.map
        (fun c => firstWait fun t =>
          (cellPath (u + t : ℝ) c : ℝ) -
            cellPath (u : ℝ) c) =
      expMeasure 1 := by
  let W : (ℕ → CellSpace) → ℝ := fun c =>
    firstWait fun t =>
      (cellPath (u + t : ℝ) c : ℝ) - cellPath (u : ℝ) c
  have hWm : Measurable W := by
    exact measurable_firstWait.comp
      (measurable_pi_lambda _ fun t =>
        (measurable_cellPathR _).sub (measurable_cellPathR _))
  letI : IsProbabilityMeasure (cellArrayLaw.map W) :=
    Measure.isProbabilityMeasure_map hWm.aemeasurable
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  -- the increment counts
  let Yc : (ℕ → CellSpace) → ℝ≥0 → ℕ := fun c s =>
    cellPath ((u : ℝ) + s) c - cellPath (u : ℝ) c
  have hYmono : ∀ c, Monotone (Yc c) := fun c a b hab =>
    Nat.sub_le_sub_right (cellPath_mono (by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith) c) _
  have hY0 : ∀ c, Yc c 0 = 0 := fun c => by simp [Yc]
  have hYright : ∀ c s, ∀ᶠ r in 𝓝[≥] s, Yc c r = Yc c s := by
    intro c s
    have h1 := cellPath_eventually_right ((u : ℝ) + s) c
    -- transport along r ↦ u + r
    have hcont : Tendsto (fun r : ℝ≥0 => (u : ℝ) + r) (𝓝[≥] s)
        (𝓝[≥] ((u : ℝ) + s)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (tendsto_const_nhds.add NNReal.continuous_coe.continuousAt.tendsto).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        have : (s : ℝ) ≤ r := by exact_mod_cast hr
        simp only [Set.mem_Ici]
        linarith
    filter_upwards [hcont.eventually h1] with r hr
    simp only [Yc, hr]
  -- the exceptional event
  have hnull : cellArrayLaw {c | ∀ s, Yc c s = 0} = 0 := by
    have hle : ∀ n : ℕ, cellArrayLaw {c | ∀ s, Yc c s = 0} ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
      intro n
      have h0 := cellPath_increment_zero u (n : ℝ≥0)
      simp only [NNReal.coe_natCast] at h0
      rw [← h0]
      refine measure_mono fun c hc => ?_
      have := hc (n : ℝ≥0)
      simpa [Yc] using this
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ))))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      simpa using ENNReal.tendsto_ofReal h1
    exact le_antisymm (ge_of_tendsto' htend hle) bot_le
  -- upper and lower bounds on the preimage of `Ioi t`
  have hcast : ∀ c s, ((Yc c s : ℕ) : ℝ) =
      (cellPath ((u : ℝ) + s) c : ℝ) - cellPath (u : ℝ) c := by
    intro c s
    simp only [Yc]
    exact Nat.cast_sub (cellPath_mono (by
      have : (0 : ℝ) ≤ s := s.2
      linarith) c)
  have hWeq : ∀ c, W c = firstWait (fun s => (Yc c s : ℝ)) := by
    intro c
    unfold W
    congr 1
    funext s
    exact (hcast c s).symm
  have hsub1 : ∀ t : ℝ≥0, W ⁻¹' Ioi (t : ℝ) ⊆ {c | Yc c t = 0} := by
    intro t c hc
    exact count_eq_zero_of_lt_firstWait (Y := Yc c) (hYmono c) (hY0 c)
      (by rw [← hWeq]; exact hc)
  have hsub2 : ∀ t : ℝ≥0, {c | Yc c t = 0} ⊆
      W ⁻¹' Ioi (t : ℝ) ∪ {c | ∀ s, Yc c s = 0} := by
    intro t c hc
    by_cases hall : ∀ s, Yc c s = 0
    · exact Or.inr hall
    · push_neg at hall
      obtain ⟨s, hs⟩ := hall
      left
      have := lt_firstWait_of_count_eq_zero (Y := Yc c) (hYmono c) (hYright c)
        ⟨s, Nat.pos_of_ne_zero hs⟩ hc
      rw [Set.mem_preimage, Set.mem_Ioi, hWeq]
      exact this
  have htail : ∀ t : ℝ≥0, cellArrayLaw (W ⁻¹' Ioi (t : ℝ)) =
      ENNReal.ofReal (Real.exp (-(t : ℝ))) := by
    intro t
    have hz : cellArrayLaw {c | Yc c t = 0} =
        ENNReal.ofReal (Real.exp (-(t : ℝ))) := cellPath_increment_zero u t
    apply le_antisymm
    · rw [← hz]
      exact measure_mono (hsub1 t)
    · rw [← hz]
      calc
        cellArrayLaw {c | Yc c t = 0} ≤
            cellArrayLaw (W ⁻¹' Ioi (t : ℝ) ∪ {c | ∀ s, Yc c s = 0}) :=
          measure_mono (hsub2 t)
        _ ≤ cellArrayLaw (W ⁻¹' Ioi (t : ℝ)) +
            cellArrayLaw {c | ∀ s, Yc c s = 0} := measure_union_le _ _
        _ = cellArrayLaw (W ⁻¹' Ioi (t : ℝ)) := by rw [hnull, add_zero]
  have hnonneg : ∀ c, 0 ≤ W c := by
    intro c
    unfold W firstWait
    split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  apply Measure.eq_of_cdf
  ext t
  by_cases ht : t < 0
  · have hleft : (cellArrayLaw.map W).real (Iic t) = 0 := by
      rw [measureReal_def, Measure.map_apply hWm measurableSet_Iic]
      have : cellArrayLaw (W ⁻¹' Iic t) = 0 := by
        refine measure_mono_null (t := ∅) (fun c hc => ?_) (by simp)
        exact absurd ((hnonneg c).trans hc) (not_le.mpr ht)
      rw [this]; simp
    have hR : (cdf (expMeasure (1 : ℝ))) t = 0 := by
      rw [cdf_expMeasure_eq zero_lt_one t, if_neg (not_le.mpr ht)]
    calc
      (cdf (cellArrayLaw.map W)) t = (cellArrayLaw.map W).real (Iic t) :=
        cdf_eq_real _ _
      _ = 0 := hleft
      _ = (cdf (expMeasure (1 : ℝ))) t := hR.symm
  · have ht0 : 0 ≤ t := le_of_not_gt ht
    have hrealTail : (cellArrayLaw.map W).real (Ioi t) = Real.exp (-t) := by
      rw [measureReal_def, Measure.map_apply hWm measurableSet_Ioi]
      have this : cellArrayLaw (W ⁻¹' Ioi t) =
          ENNReal.ofReal (Real.exp (-t)) := htail ⟨t, ht0⟩
      rw [this, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    have hcdf : (cellArrayLaw.map W).real (Iic t) = 1 - Real.exp (-t) := by
      rw [show Iic t = (Ioi t)ᶜ by ext x; simp,
        measureReal_compl measurableSet_Ioi, hrealTail, probReal_univ]
    calc
      (cdf (cellArrayLaw.map W)) t = (cellArrayLaw.map W).real (Iic t) :=
        cdf_eq_real _ _
      _ = 1 - Real.exp (-t) := hcdf
      _ = (cdf (expMeasure (1 : ℝ))) t := by
        rw [cdf_expMeasure_eq zero_lt_one t, if_pos ht0, one_mul]

/-- The vector of first waits under the full independent family law is exactly
`clockLaw`. -/
theorem firstWaitVector_law :
    (flatPoissonLaw ι).map firstWaitVector = clockLaw ι := by
  unfold flatPoissonLaw
  rw [Measure.map_map measurable_firstWaitVector measurable_flatCellDriver]
  let w : (ℕ → CellSpace) → ℝ := fun c =>
    firstWait fun t : ℝ≥0 => (cellPath (t : ℝ) c : ℝ)
  have hw : Measurable w :=
    measurable_firstWait.comp
      (measurable_pi_lambda _ fun t => measurable_cellPathR _)
  have hfun : firstWaitVector ∘ flatCellDriver =
      fun (C : CellFamily ι) (l : ι) => w (C l) := rfl
  have hlaw : cellArrayLaw.map w = expMeasure 1 := by
    have h0 := firstWait_shift_law_one 0
    simpa [cellPath_zero] using h0
  letI : IsProbabilityMeasure (cellArrayLaw.map w) :=
    Measure.isProbabilityMeasure_map hw.aemeasurable
  rw [hfun]
  unfold cellFamilyLaw
  rw [Measure.infinitePi_eq_pi,
    Measure.pi_map_pi (μ := fun _ : ι => cellArrayLaw) (f := fun _ => w)
      (fun _ => hw.aemeasurable)]
  simp_rw [hlaw]
  rfl

/-- Deterministic strong memorylessness: completed past and the next-wait
vector factor as a product. -/
theorem deterministic_past_wait_law (u : ι → ℝ≥0) :
    (flatPoissonLaw ι).map
        (fun Y => (completePast u Y, residualWait u Y)) =
      ((flatPoissonLaw ι).map (completePast u)).prod (clockLaw ι) := by
  classical
  let past : ι → (ℕ → CellSpace) → (ℝ≥0 → ℝ) := fun l c t =>
    if t ≤ u l then (cellPath (t : ℝ) c : ℝ)
    else (cellPath (u l : ℝ) c : ℝ) + ⌊((t : ℝ) - (u l : ℝ))⌋₊
  let wait : ι → (ℕ → CellSpace) → ℝ := fun l c =>
    firstWait fun t => (cellPath (u l + t : ℝ) c : ℝ) - cellPath (u l : ℝ) c
  have hpastM : ∀ l, Measurable (past l) := by
    intro l
    apply measurable_pi_lambda
    intro t
    by_cases ht : t ≤ u l
    · simpa [past, ht] using measurable_cellPathR (t : ℝ)
    · simpa [past, ht] using (measurable_cellPathR (u l : ℝ)).add_const _
  have hwaitM : ∀ l, Measurable (wait l) := fun l =>
    measurable_firstWait.comp
      (measurable_pi_lambda _ fun t =>
        (measurable_cellPathR _).sub (measurable_cellPathR _))
  have hindep : ∀ l, IndepFun (past l) (wait l) cellArrayLaw := fun l =>
    (indepFun_completePast_shift_one (u l)).comp measurable_id
      measurable_firstWait
  have hwaitLaw : ∀ l, cellArrayLaw.map (wait l) = expMeasure 1 := fun l =>
    firstWait_shift_law_one (u l)
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (l : ι) : IsProbabilityMeasure (cellArrayLaw.map (past l)) :=
    Measure.isProbabilityMeasure_map (hpastM l).aemeasurable
  have hpair : ∀ l,
      cellArrayLaw.map (fun c => (past l c, wait l c)) =
        (cellArrayLaw.map (past l)).prod (expMeasure 1) := by
    intro l
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hpastM l).aemeasurable
      (hwaitM l).aemeasurable).mp (hindep l), hwaitLaw l]
  let g : CellFamily ι → (ι → (ℝ≥0 → ℝ) × ℝ) := fun C l =>
    (past l (C l), wait l (C l))
  let g1 : CellFamily ι → (ι → (ℝ≥0 → ℝ)) := fun C l => past l (C l)
  let Ψ1 : (ι → (ℝ≥0 → ℝ)) → FlatDriver ι := fun w p => w p.1 p.2
  have hΨ1 : Measurable Ψ1 := by
    apply measurable_pi_lambda
    intro p
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hflat1 : completePast u ∘ flatCellDriver = Ψ1 ∘ g1 := by
    funext C p
    rcases p with ⟨l, t⟩
    simp [completePast, flatCellDriver, Ψ1, g1, past]
  have hflat2 : (fun Y => (completePast u Y, residualWait u Y)) ∘ flatCellDriver
      = Prod.map Ψ1 id ∘ (MeasurableEquiv.arrowProdEquivProdArrow
          (ℝ≥0 → ℝ) ℝ ι) ∘ g := by
    funext C
    refine Prod.ext ?_ ?_
    · funext p
      rcases p with ⟨l, t⟩
      simp [completePast, flatCellDriver, Ψ1, g, past,
        MeasurableEquiv.arrowProdEquivProdArrow]
    · funext l
      simp only [Function.comp_apply, Prod.map, id,
        MeasurableEquiv.arrowProdEquivProdArrow, residualWait,
        firstWaitVector, shiftDriver, flatCellDriver, g, wait]
      congr 1
  have hgM : Measurable g := by
    apply measurable_pi_lambda
    intro l
    exact ((hpastM l).comp (measurable_pi_apply l)).prodMk
      ((hwaitM l).comp (measurable_pi_apply l))
  have hg1M : Measurable g1 := by
    apply measurable_pi_lambda
    intro l
    exact (hpastM l).comp (measurable_pi_apply l)
  have hlawG : (cellFamilyLaw ι).map g =
      Measure.pi (fun l => (cellArrayLaw.map (past l)).prod (expMeasure 1)) := by
    unfold cellFamilyLaw
    rw [Measure.infinitePi_eq_pi]
    have := Measure.pi_map_pi (μ := fun _ : ι => cellArrayLaw)
      (f := fun l c => (past l c, wait l c))
      (fun l => ((hpastM l).prodMk (hwaitM l)).aemeasurable)
    simp_rw [hpair] at this
    exact this
  have hlawG1 : (cellFamilyLaw ι).map g1 =
      Measure.pi (fun l => cellArrayLaw.map (past l)) := by
    unfold cellFamilyLaw
    rw [Measure.infinitePi_eq_pi]
    exact Measure.pi_map_pi (μ := fun _ : ι => cellArrayLaw)
      (f := fun l c => past l c) (fun l => (hpastM l).aemeasurable)
  unfold flatPoissonLaw
  rw [Measure.map_map (by fun_prop) measurable_flatCellDriver,
    Measure.map_map (measurable_completePast u) measurable_flatCellDriver,
    hflat2, hflat1,
    ← Measure.map_map (hΨ1.prodMap measurable_id)
      ((MeasurableEquiv.arrowProdEquivProdArrow (ℝ≥0 → ℝ) ℝ ι).measurable.comp hgM),
    ← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow
      (ℝ≥0 → ℝ) ℝ ι).measurable hgM, hlawG,
    ← Measure.map_map hΨ1 hg1M, hlawG1]
  have hmp := MeasureTheory.measurePreserving_arrowProdEquivProdArrow
    (ℝ≥0 → ℝ) ℝ ι (fun l => cellArrayLaw.map (past l)) (fun _ => expMeasure 1)
  rw [hmp.map_eq, ← Measure.map_prod_map _ _ hΨ1 measurable_id, Measure.map_id]
  rfl

/-! ### Countably valued approximations of a stopping line -/

/-- Grid denominator `m+1`. -/
def gridDenom (m : ℕ) : ℕ := m + 1

/-- Coordinatewise upward grid code. -/
def gridCode (m : ℕ) (u : ι → ℝ≥0) : ι → ℕ :=
  fun l => ⌈((gridDenom m : ℝ) * (u l : ℝ))⌉₊

/-- Point represented by a grid code. -/
def gridPoint (m : ℕ) (q : ι → ℕ) : ι → ℝ≥0 :=
  fun l => ⟨(q l : ℝ) / gridDenom m, by positivity⟩

@[fun_prop]
theorem measurable_gridCode (m : ℕ) :
    Measurable (gridCode (ι := ι) m) := by
  apply measurable_pi_lambda
  intro l
  exact Nat.measurable_ceil.comp
    (measurable_const.mul ((measurable_pi_apply l).coe_nnreal_real))

theorem le_gridPoint_gridCode (m : ℕ) (u : ι → ℝ≥0) (l : ι) :
    u l ≤ gridPoint m (gridCode m u) l := by
  rw [← NNReal.coe_le_coe]
  show (u l : ℝ) ≤ (⌈((gridDenom m : ℕ) : ℝ) * (u l : ℝ)⌉₊ : ℝ) /
    ((gridDenom m : ℕ) : ℝ)
  have hpos : (0 : ℝ) < ((gridDenom m : ℕ) : ℝ) := by
    unfold gridDenom
    positivity
  rw [le_div_iff₀ hpos, mul_comm]
  exact Nat.le_ceil _

theorem gridPoint_gridCode_tendsto (u : ι → ℝ≥0) :
    Tendsto (fun m => gridPoint m (gridCode m u)) atTop (𝓝 u) := by
  rw [tendsto_pi_nhds]
  intro l
  rw [← NNReal.tendsto_coe]
  have hup : Tendsto (fun m : ℕ => (u l : ℝ) + 1 / ((m : ℝ) + 1)) atTop
      (𝓝 (u l)) := by
    simpa using
      (tendsto_const_nhds (x := (u l : ℝ))).add
        tendsto_one_div_add_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun m => ?_) (fun m => ?_)
  · exact_mod_cast le_gridPoint_gridCode m u l
  · show (⌈((gridDenom m : ℕ) : ℝ) * (u l : ℝ)⌉₊ : ℝ) /
      ((gridDenom m : ℕ) : ℝ) ≤ (u l : ℝ) + 1 / ((m : ℝ) + 1)
    have hD : ((gridDenom m : ℕ) : ℝ) = (m : ℝ) + 1 := by
      unfold gridDenom
      push_cast
      ring
    rw [hD]
    have hc := Nat.ceil_lt_add_one
      (mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1) (u l).2)
    rw [div_le_iff₀ (by positivity)]
    have e : ((u l : ℝ) + 1 / ((m : ℝ) + 1)) * ((m : ℝ) + 1) =
        ((m : ℝ) + 1) * u l + 1 := by
      field_simp
    rw [e]
    exact hc.le

/-- A jointly causal stopping line and a history readout.  The two equivalences
say that truncating/completing the driver at `u` decides whether the line has
already occurred; once it has occurred, it also reproduces the exact line and
history. -/
structure StoppingLineHistory
    (line : FlatDriver ι → ι → ℝ≥0)
    (history : FlatDriver ι → E) : Prop where
  measurable_line : Measurable line
  measurable_history : Measurable history
  le_complete_iff : ∀ Y u,
    (∀ l, line Y l ≤ u l) ↔
      (∀ l, line (completePast u Y) l ≤ u l)
  line_complete : ∀ Y u, (∀ l, line Y l ≤ u l) →
    line (completePast u Y) = line Y
  history_complete : ∀ Y u, (∀ l, line Y l ≤ u l) →
    history (completePast u Y) = history Y

namespace StoppingLineHistory

variable {line : FlatDriver ι → ι → ℝ≥0}
variable {history : FlatDriver ι → E}
variable (H : StoppingLineHistory line history)

/-- Rounded residual vector. -/
def roundedResidual (_H : StoppingLineHistory line history) (m : ℕ)
    (Y : FlatDriver ι) : ι → ℝ :=
  residualWait (gridPoint m (gridCode m (line Y))) Y

theorem measurable_roundedResidual (m : ℕ) :
    Measurable (H.roundedResidual m) := by
  have hF : Measurable (fun p : (ι → ℕ) × FlatDriver ι =>
      residualWait (gridPoint m p.1) p.2) := by
    apply measurable_from_prod_countable_right
    intro q
    exact measurable_residualWait (gridPoint m q)
  have hcode : Measurable (fun Y : FlatDriver ι => gridCode m (line Y)) :=
    (measurable_gridCode m).comp H.measurable_line
  have hpair : Measurable (fun Y : FlatDriver ι => (gridCode m (line Y), Y)) :=
    hcode.prodMk measurable_id
  have key : H.roundedResidual m =
      (fun p : (ι → ℕ) × FlatDriver ι => residualWait (gridPoint m p.1) p.2) ∘
        (fun Y : FlatDriver ι => (gridCode m (line Y), Y)) := by
    funext Y
    rfl
  rw [key]
  exact hF.comp hpair

/-- Each rounded line is countably valued, so deterministic memorylessness can
be summed over its grid fibres. -/
theorem rounded_residual_law (m : ℕ) :
    (flatPoissonLaw ι).map
        (fun Y => (history Y, H.roundedResidual m Y)) =
      ((flatPoissonLaw ι).map history).prod (clockLaw ι) := by
  refine (Measure.prod_eq ?_).symm
  intro A B hA hB
  rw [Measure.map_apply
      (H.measurable_history.prodMk (H.measurable_roundedResidual m))
      (hA.prod hB),
    Measure.map_apply H.measurable_history hA]
  have hset : (fun a => (history a, H.roundedResidual m a)) ⁻¹' A ×ˢ B =
      {Y | history Y ∈ A ∧ H.roundedResidual m Y ∈ B} := rfl
  rw [hset]
  let code : FlatDriver ι → (ι → ℕ) := fun Y => gridCode m (line Y)
  have hcode : Measurable code :=
    (measurable_gridCode m).comp H.measurable_line
  have hlevel_mass : ∀ q : ι → ℕ,
      flatPoissonLaw ι {Y | code Y = q ∧ history Y ∈ A ∧
          H.roundedResidual m Y ∈ B} =
        flatPoissonLaw ι {Y | code Y = q ∧ history Y ∈ A} * clockLaw ι B := by
    intro q
    let u := gridPoint m q
    have hle : ∀ Y, code Y = q → ∀ l, line Y l ≤ u l := by
      intro Y hY l
      have h := le_gridPoint_gridCode m (line Y) l
      have hq : gridCode m (line Y) = q := hY
      rw [hq] at h
      exact h
    have hcodeIff : ∀ Y, code (completePast u Y) = q ↔ code Y = q := by
      intro Y
      constructor
      · intro hY
        have hleC : ∀ l, line (completePast u Y) l ≤ u l := hle _ hY
        have hleY := (H.le_complete_iff Y u).2 hleC
        have heq := H.line_complete Y u hleY
        show gridCode m (line Y) = q
        rw [← heq]
        exact hY
      · intro hY
        have hleY := hle Y hY
        have heq := H.line_complete Y u hleY
        show gridCode m (line (completePast u Y)) = q
        rw [heq]
        exact hY
    have hhist : ∀ Y, code Y = q → history (completePast u Y) = history Y :=
      fun Y hY => H.history_complete Y u (hle Y hY)
    have hres : ∀ Y, code Y = q → H.roundedResidual m Y = residualWait u Y := by
      intro Y hY
      show residualWait (gridPoint m (gridCode m (line Y))) Y = residualWait u Y
      have hq : gridCode m (line Y) = q := hY
      rw [hq]
    let P : Set (FlatDriver ι) := {Y | code Y = q ∧ history Y ∈ A}
    have hPM : MeasurableSet P :=
      (hcode (measurableSet_singleton q)).inter (H.measurable_history hA)
    have hP : completePast u ⁻¹' P = P := by
      ext Y
      simp only [P, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        have hY := (hcodeIff Y).1 h1
        exact ⟨hY, by rw [← hhist Y hY]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hcodeIff Y).2 h1, by rw [hhist Y h1]; exact h2⟩
    have hpre : {Y | code Y = q ∧ history Y ∈ A ∧ H.roundedResidual m Y ∈ B} =
        (fun Y => (completePast u Y, residualWait u Y)) ⁻¹' (P ×ˢ B) := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod]
      simp only [P, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact (hcodeIff Y).2 h1
        · rw [hhist Y h1]
          exact h2
        · rw [← hres Y h1]
          exact h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hY := (hcodeIff Y).1 h1
        refine ⟨hY, ?_, ?_⟩
        · rw [← hhist Y hY]
          exact h2
        · rw [hres Y hY]
          exact h3
    have hind := deterministic_past_wait_law (ι := ι) u
    rw [hpre]
    have hmeasPair : Measurable
        (fun Y : FlatDriver ι => (completePast u Y, residualWait u Y)) :=
      (measurable_completePast u).prodMk (measurable_residualWait u)
    have h1 := congrArg
      (fun μ : Measure (FlatDriver ι × (ι → ℝ)) => μ (P ×ˢ B)) hind
    dsimp only at h1
    rw [Measure.map_apply hmeasPair (hPM.prod hB), Measure.prod_prod,
      Measure.map_apply (measurable_completePast u) hPM, hP] at h1
    exact h1
  have hdisj : Pairwise (Function.onFun Disjoint
      fun q : ι → ℕ => {Y | code Y = q ∧ history Y ∈ A}) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro Y hq hr
    exact hqr (hq.1.symm.trans hr.1)
  have hdisj' : Pairwise (Function.onFun Disjoint
      fun q : ι → ℕ => {Y | code Y = q ∧ history Y ∈ A ∧
          H.roundedResidual m Y ∈ B}) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro Y hq hr
    exact hqr (hq.1.symm.trans hr.1)
  have hmeas1 : ∀ q : ι → ℕ, MeasurableSet {Y | code Y = q ∧ history Y ∈ A} :=
    fun q => (hcode (measurableSet_singleton q)).inter (H.measurable_history hA)
  have hmeas2 : ∀ q : ι → ℕ, MeasurableSet {Y | code Y = q ∧ history Y ∈ A ∧
          H.roundedResidual m Y ∈ B} := fun q =>
    (hcode (measurableSet_singleton q)).inter
      ((H.measurable_history hA).inter (H.measurable_roundedResidual m hB))
  have hU1 : {Y | history Y ∈ A} =
      ⋃ q : ι → ℕ, {Y | code Y = q ∧ history Y ∈ A} := by
    ext Y
    simp
  have hU2 : {Y | history Y ∈ A ∧ H.roundedResidual m Y ∈ B} =
      ⋃ q : ι → ℕ, {Y | code Y = q ∧ history Y ∈ A ∧
          H.roundedResidual m Y ∈ B} := by
    ext Y
    simp
  have hH : history ⁻¹' A = {Y | history Y ∈ A} := rfl
  rw [hH, hU2, hU1, measure_iUnion hdisj' hmeas2, measure_iUnion hdisj hmeas1,
    ← ENNReal.tsum_mul_right]
  exact tsum_congr hlevel_mass

end StoppingLineHistory

end Ripple.Kurtz.StrongApprox

end
