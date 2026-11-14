-- Ripple/Kurtz/StrongApprox/AllTimeKMTPoissonLaw.lean
import Ripple.Kurtz.StrongApprox.AllTimeKMTBrownianLaw
import Ripple.Kurtz.StrongApprox.PoissonDriverFamily
import Ripple.Kurtz.StrongApprox.PoissonCellDriverLaw

/-!
# Increments of the all-time Poisson path

The all-time Poisson path is the counting path `cellPath t a` of one iid
sequence `a` of Poisson-count / uniform-position cells: global cell
`n = (2^J - 1) + c` is cell `c` of block `J`.  The cells are independent across
blocks (coordinates of the infinite product) and inside a block (the block cell
data are independent), so the sequence has the universal law `cellArrayLaw`.
Increments over any finite monotone grid starting at `0` then have the product
Poisson law and are independent, by the corresponding statements for the
canonical cell source.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.AllTimeKMTPoissonLaw

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology
open AllTimeKMT ContinuousFiniteHorizonKMT AllTimeKMTLaws AllTimeKMTBrownianLaw
open AllTimeKurtzMoment
open DyadicConditionalPoissonPath PoissonDriverFamily

/-! ## Independence transfers along a measurable map -/

theorem iIndepFun_comp_map_iff {Ω Ω' ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace β] {μ : Measure Ω} {φ : Ω → Ω'}
    (hφ : Measurable φ) {G : ι → Ω' → β} (hG : ∀ i, Measurable (G i)) :
    iIndepFun (fun i => G i ∘ φ) μ ↔ iIndepFun G (μ.map φ) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul,
    iIndepFun_iff_measure_inter_preimage_eq_mul]
  constructor
  · intro h S sets hsets
    have hm : MeasurableSet (⋂ i ∈ S, G i ⁻¹' sets i) :=
      Finset.measurableSet_biInter _ fun i hi => hG i (hsets i hi)
    rw [Measure.map_apply hφ hm]
    have e1 : φ ⁻¹' (⋂ i ∈ S, G i ⁻¹' sets i) =
        ⋂ i ∈ S, (G i ∘ φ) ⁻¹' sets i := by
      ext x
      simp [Function.comp]
    rw [e1, h S hsets]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Measure.map_apply hφ (hG i (hsets i hi))]
    rfl
  · intro h S sets hsets
    have hm : MeasurableSet (⋂ i ∈ S, G i ⁻¹' sets i) :=
      Finset.measurableSet_biInter _ fun i hi => hG i (hsets i hi)
    have e1 : (⋂ i ∈ S, (G i ∘ φ) ⁻¹' sets i) =
        φ ⁻¹' (⋂ i ∈ S, G i ⁻¹' sets i) := by
      ext x
      simp [Function.comp]
    rw [e1, ← Measure.map_apply hφ hm, h S hsets]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Measure.map_apply hφ (hG i (hsets i hi))]
    rfl

/-! ## Increments of the cell-sequence path under `cellArrayLaw` -/

/-- Increment vector of the counting path read from a cell sequence. -/
def cellIncrementVector {r : ℕ} (t : Fin (r + 1) → ℝ) (a : ℕ → CellSpace) :
    Fin r → ℕ :=
  fun i => cellPath (t i.succ) a - cellPath (t i.castSucc) a

theorem measurable_cellIncrementVector {r : ℕ} (t : Fin (r + 1) → ℝ) :
    Measurable (cellIncrementVector t) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_cellPath (t i.succ)).sub (measurable_cellPath (t i.castSucc))

theorem grid_nonneg_of_monotone {r : ℕ} {t : Fin (r + 1) → ℝ}
    (hzero : t 0 = 0) (ht : Monotone t) (i : Fin (r + 1)) : 0 ≤ t i := by
  have h := ht (show (0 : Fin (r + 1)) ≤ i from bot_le)
  simpa only [hzero] using h

theorem cellArrayLaw_incrementVector_iIndep {r : ℕ} (t : Fin (r + 1) → ℝ)
    (hmono : Monotone t) :
    iIndepFun (fun (i : Fin r) (a : ℕ → CellSpace) =>
      cellPath (t i.succ) a - cellPath (t i.castSucc) a) cellArrayLaw := by
  have hind := hasIndepIncrements_poisPath
    driver_measurable driver_indep driver_law r t hmono
  rw [← cellSequence_law (N := canonicalCount) (P := driverMeasure)
    driver_measurable driver_indep driver_law]
  rw [← iIndepFun_comp_map_iff (measurable_cellSequence driver_measurable)
    (G := fun (i : Fin r) (a : ℕ → CellSpace) =>
      cellPath (t i.succ) a - cellPath (t i.castSucc) a)
    (fun i => (measurable_cellPath _).sub (measurable_cellPath _))]
  exact hind

theorem cellArrayLaw_incrementVector_law {r : ℕ} (t : Fin (r + 1) → ℝ)
    (hzero : t 0 = 0) (hmono : Monotone t) :
    cellArrayLaw.map (cellIncrementVector t) =
      DyadicConditionalPoissonPath.poissonIncrementProduct t := by
  have hind := cellArrayLaw_incrementVector_iIndep t hmono
  have hmeas : ∀ i : Fin r, Measurable (fun a : ℕ → CellSpace =>
      cellPath (t i.succ) a - cellPath (t i.castSucc) a) := fun i =>
    (measurable_cellPath _).sub (measurable_cellPath _)
  have hlaw : ∀ i : Fin r, cellArrayLaw.map (fun a : ℕ → CellSpace =>
      cellPath (t i.succ) a - cellPath (t i.castSucc) a) =
      poisMeasure (t i.succ - t i.castSucc) := by
    intro i
    apply Measure.ext_of_singleton
    intro k
    rw [Measure.map_apply (hmeas i) (measurableSet_singleton k),
      poisMeasure_singleton]
    have h := pathMeasure_increment_eq
      driver_measurable driver_indep driver_law
      (grid_nonneg_of_monotone hzero hmono i.castSucc)
      (hmono (Fin.castSucc_le_succ i)) k
    rw [← cellSequence_law (N := canonicalCount) (P := driverMeasure)
      driver_measurable driver_indep driver_law,
      Measure.map_apply (measurable_cellSequence driver_measurable)
        ((hmeas i) (measurableSet_singleton k))]
    exact h
  calc
    cellArrayLaw.map (cellIncrementVector t) =
        Measure.infinitePi fun i : Fin r => cellArrayLaw.map
          (fun a : ℕ → CellSpace =>
            cellPath (t i.succ) a - cellPath (t i.castSucc) a) :=
      hind.map_fun_eq_infinitePi_map hmeas
    _ = Measure.infinitePi (fun i : Fin r =>
        poisMeasure (t i.succ - t i.castSucc)) := by
      congr 1
      funext i
      exact hlaw i
    _ = DyadicConditionalPoissonPath.poissonIncrementProduct t := rfl


/-! ## The global cell sequence of the all-time Poisson path -/

/-- Natural-number start of block `J`: the number of cells before it. -/
def natStart (J : ℕ) : ℕ := 2 ^ J - 1

theorem natStart_cast (J : ℕ) : ((natStart J : ℕ) : ℝ) = allTimeBlockStart J := by
  have h : 1 ≤ 2 ^ J := Nat.one_le_two_pow
  unfold natStart allTimeBlockStart allTimeBlockLength
  push_cast [Nat.cast_sub h]
  ring

theorem natStart_succ (J : ℕ) : natStart (J + 1) = natStart J + 2 ^ J := by
  have h : 1 ≤ 2 ^ J := Nat.one_le_two_pow
  unfold natStart
  rw [pow_succ]
  omega

/-- Cell `L` of block `J`, as a function of the all-time sample. -/
def blockCellData (J L : ℕ) (h : L < 2 ^ J) (ω : AllTimeKMTSpace) : CellSpace :=
  dyadicCellBlock J (continuousKMTToContinuous J (ω J)) ⟨L, h⟩

theorem measurable_blockCellData (J L : ℕ) (h : L < 2 ^ J) :
    Measurable (blockCellData J L h) := by
  unfold blockCellData
  have h1 : Measurable (fun z : ContinuousKMTSpace J =>
      dyadicCellData J ⟨L, h⟩ (continuousKMTToContinuous J z)) :=
    (measurable_dyadicCellData J ⟨L, h⟩).comp
      (measurable_continuousKMTToContinuous J)
  exact h1.comp (measurable_pi_apply J)

theorem blockCellData_congr {J J' L L' : ℕ} (hJ : J = J') (hL : L = L')
    (h : L < 2 ^ J) (h' : L' < 2 ^ J') (ω : AllTimeKMTSpace) :
    blockCellData J L h ω = blockCellData J' L' h' ω := by
  subst hJ
  subst hL
  rfl

/-- The global cell sequence: global cell `n` is cell `AllTimeKMTBrownianLaw.cellLocal 0 n` of block
`AllTimeKMTBrownianLaw.cellBlock 0 n`. -/
def poissonCellSeq (ω : AllTimeKMTSpace) (n : ℕ) : CellSpace :=
  blockCellData (AllTimeKMTBrownianLaw.cellBlock 0 n) (AllTimeKMTBrownianLaw.cellLocal 0 n)
    (by simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n) ω

theorem measurable_poissonCellSeq : Measurable poissonCellSeq := by
  apply measurable_pi_lambda
  intro n
  exact measurable_blockCellData _ _ _

theorem cellBlock_zero_of (j c : ℕ) (hc : c < 2 ^ j) :
    AllTimeKMTBrownianLaw.cellBlock 0 (natStart j + c) = j := by
  unfold AllTimeKMTBrownianLaw.cellBlock
  have hcast : (((natStart j + c : ℕ) : ℝ)) / (2 : ℝ) ^ 0 =
      allTimeBlockStart j + (c : ℝ) := by
    push_cast
    rw [natStart_cast]
    simp
  rw [hcast]
  have hc' : (c : ℝ) < (2 : ℝ) ^ j := by exact_mod_cast hc
  have hs0 := allTimeBlockStart_nonneg j
  apply allTimeBlock_eq_of_bounds (by positivity)
  · linarith [Nat.cast_nonneg (α := ℝ) c]
  · rw [allTimeBlockStart_succ]
    unfold allTimeBlockLength
    linarith

theorem cellLocal_zero_of (j c : ℕ) (hc : c < 2 ^ j) :
    AllTimeKMTBrownianLaw.cellLocal 0 (natStart j + c) = c := by
  unfold AllTimeKMTBrownianLaw.cellLocal
  rw [cellBlock_zero_of j c hc]
  simp [natStart]

theorem poissonCellSeq_eq (j c : ℕ) (hc : c < 2 ^ j) (ω : AllTimeKMTSpace) :
    poissonCellSeq ω (natStart j + c) =
      dyadicCellBlock j (continuousKMTToContinuous j (ω j)) ⟨c, hc⟩ := by
  unfold poissonCellSeq
  exact blockCellData_congr (cellBlock_zero_of j c hc)
    (cellLocal_zero_of j c hc) _ _ ω


/-! ## The all-time path is the counting path of the global cell sequence -/

theorem cellHit_Ioc_of_one_le' {s : ℝ} (hs : 1 ≤ s) (v : CellSpace) :
    cellHit (Ioc 0 s) v = v.1 := by
  unfold cellHit
  exact hitCount_Ioc_of_one_le hs v.1 v.2

theorem cellPath_eq_sum_range (a : ℕ → CellSpace) {t : ℝ} {M : ℕ}
    (ht : t ≤ (M : ℝ)) :
    cellPath t a = ∑ n ∈ range M, cellHit (Ioc 0 (t - (n : ℝ))) (a n) := by
  rw [← finiteCellPath_restrict_eq_cellPath M a ht,
    finiteCellPath_eq_sum M (fun j => a j.1) ht]
  exact Fin.sum_univ_eq_sum_range
    (fun n => cellHit (Ioc 0 (t - (n : ℝ))) (a n)) M

theorem sum_range_natStart (g : ℕ → ℕ) (L : ℕ) :
    ∑ n ∈ range (natStart L), g n =
      ∑ j ∈ range L, ∑ c ∈ range (2 ^ j), g (natStart j + c) := by
  induction L with
  | zero => simp [natStart]
  | succ L ih =>
    rw [natStart_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem blockPoisson_sum (j : ℕ) (z : ContinuousKMTSpace j) {u : ℝ}
    (hu : u ≤ (2 : ℝ) ^ j) :
    continuousKMTPoisson j u z =
      ∑ c ∈ range (2 ^ j), cellHit (Ioc 0 (u - (c : ℝ)))
        (extendCellBlock (2 ^ j)
          (dyadicCellBlock j (continuousKMTToContinuous j z)) c) := by
  show cellPath u (extendCellBlock (2 ^ j)
      (dyadicCellBlock j (continuousKMTToContinuous j z))) = _
  exact cellPath_eq_sum_range _ (by exact_mod_cast hu)

theorem extendCellBlock_eq_poissonCellSeq (j c : ℕ) (hc : c < 2 ^ j)
    (ω : AllTimeKMTSpace) :
    extendCellBlock (2 ^ j)
        (dyadicCellBlock j (continuousKMTToContinuous j (ω j))) c =
      poissonCellSeq ω (natStart j + c) := by
  rw [poissonCellSeq_eq j c hc ω]
  unfold extendCellBlock
  rw [dif_pos hc]

theorem allTimeKMTPoisson_eq_cellPath {t : ℝ} (ht : 0 ≤ t)
    (ω : AllTimeKMTSpace) :
    allTimeKMTPoisson t ω = cellPath t (poissonCellSeq ω) := by
  rw [allTimeKMTPoisson_of_nonneg t ht ω]
  obtain ⟨J, hJ⟩ : ∃ J, J = allTimeBlock t := ⟨_, rfl⟩
  have hb := allTimeBlock_bounds ht
  rw [← hJ] at hb
  have htM : t ≤ ((natStart (J + 1) : ℕ) : ℝ) := by
    rw [natStart_cast]
    exact hb.2.le
  rw [cellPath_eq_sum_range _ htM, sum_range_natStart, Finset.sum_range_succ,
    ← hJ]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hjJ : j < J := Finset.mem_range.mp hj
    have hlen : allTimeBlockLength j = (2 : ℝ) ^ j := rfl
    rw [blockPoisson_sum j (ω j) (by rw [hlen])]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' : c < 2 ^ j := Finset.mem_range.mp hc
    rw [← extendCellBlock_eq_poissonCellSeq j c hc' ω]
    have hcr : (c : ℝ) + 1 ≤ (2 : ℝ) ^ j := by exact_mod_cast hc'
    have h1 : 1 ≤ allTimeBlockLength j - (c : ℝ) := by
      rw [hlen]; linarith
    have hmono := allTimeBlockStart_mono (Nat.succ_le_of_lt hjJ)
    have h2 : 1 ≤ t - ((natStart j + c : ℕ) : ℝ) := by
      push_cast
      rw [natStart_cast]
      have := allTimeBlockStart_succ j
      unfold allTimeBlockLength at this
      linarith [hb.1]
    rw [cellHit_Ioc_of_one_le' h1, cellHit_Ioc_of_one_le' h2]
  · have hloc := allTimeLocalTime_mem ht
    rw [← hJ] at hloc
    have hlen : allTimeBlockLength J = (2 : ℝ) ^ J := rfl
    rw [blockPoisson_sum J (ω J) (by rw [← hlen]; exact hloc.2)]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' : c < 2 ^ J := Finset.mem_range.mp hc
    rw [← extendCellBlock_eq_poissonCellSeq J c hc' ω]
    congr 2
    unfold allTimeLocalTime
    rw [← hJ]
    push_cast
    rw [natStart_cast]
    ring


/-! ## The law of the global cell sequence -/

theorem poissonCellSeq_iIndep :
    iIndepFun (fun (n : ℕ) ω => poissonCellSeq ω n) allTimeKMTMeasure := by
  classical
  let C : ℕ → Type := fun J => Fin (2 ^ J)
  let Wf : ∀ J, C J → ContinuousKMTSpace J → CellSpace := fun J c z =>
    dyadicCellData J c (continuousKMTToContinuous J z)
  have hblk : ∀ J, iIndepFun (fun c : C J => Wf J c) (continuousKMTMeasure J) := by
    intro J
    have h := dyadicCellData_iIndep J
    rw [← (continuousKMTMeasure_toContinuous J).map_eq] at h
    exact (iIndepFun_comp_map_iff (continuousKMTMeasure_toContinuous J).measurable
      (G := fun c : C J => dyadicCellData J c)
      (fun c => measurable_dyadicCellData J c)).mpr h
  have hsig := iIndepFun_sigmaCells (fun J => continuousKMTMeasure J) Wf
    (fun J c => (measurable_dyadicCellData J c).comp
      (measurable_continuousKMTToContinuous J))
    hblk
  let g : ℕ → Σ J, C J := fun n =>
    ⟨AllTimeKMTBrownianLaw.cellBlock 0 n,
      ⟨AllTimeKMTBrownianLaw.cellLocal 0 n, by
        simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n⟩⟩
  have hinj : Function.Injective g := by
    intro n n' h
    have h1 : AllTimeKMTBrownianLaw.cellBlock 0 n =
        AllTimeKMTBrownianLaw.cellBlock 0 n' := congrArg Sigma.fst h
    have h2 : AllTimeKMTBrownianLaw.cellLocal 0 n =
        AllTimeKMTBrownianLaw.cellLocal 0 n' :=
      congrArg (fun p : Σ J, C J => (p.2 : ℕ)) h
    have a1 := AllTimeKMTBrownianLaw.cellLocal_add 0 n
    have a2 := AllTimeKMTBrownianLaw.cellLocal_add 0 n'
    rw [h1, h2] at a1
    omega
  have hcomp := hsig.precomp hinj
  have hfun : (fun (n : ℕ) ω => poissonCellSeq ω n) =
      fun n ω => Wf (g n).1 (g n).2 (ω (g n).1) := by
    funext n ω
    rfl
  rw [hfun]
  exact hcomp

theorem poissonCellSeq_coord_map (n : ℕ) :
    allTimeKMTMeasure.map (fun ω => poissonCellSeq ω n) = cellLaw := by
  have hfun : (fun ω => poissonCellSeq ω n) = fun ω =>
      dyadicCellData (AllTimeKMTBrownianLaw.cellBlock 0 n)
        ⟨AllTimeKMTBrownianLaw.cellLocal 0 n, by
          simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n⟩
        (continuousKMTToContinuous (AllTimeKMTBrownianLaw.cellBlock 0 n)
          (ω (AllTimeKMTBrownianLaw.cellBlock 0 n))) := by
    funext ω
    rfl
  rw [hfun]
  set J := AllTimeKMTBrownianLaw.cellBlock 0 n with hJ
  have hm := (measurable_dyadicCellData J
      ⟨AllTimeKMTBrownianLaw.cellLocal 0 n, by
        simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n⟩).comp
    (measurable_continuousKMTToContinuous J)
  calc
    allTimeKMTMeasure.map (fun ω => dyadicCellData J
        ⟨AllTimeKMTBrownianLaw.cellLocal 0 n, by
          simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n⟩
        (continuousKMTToContinuous J (ω J))) =
      (allTimeKMTMeasure.map (fun ω : AllTimeKMTSpace => ω J)).map
        (fun z => dyadicCellData J
          ⟨AllTimeKMTBrownianLaw.cellLocal 0 n, by
            simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n⟩
          (continuousKMTToContinuous J z)) :=
      (Measure.map_map hm (measurable_pi_apply J)).symm
    _ = (continuousKMTMeasure J).map (fun z => dyadicCellData J
          ⟨AllTimeKMTBrownianLaw.cellLocal 0 n, by
            simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n⟩
          (continuousKMTToContinuous J z)) := by
      rw [(allTimeEval_measurePreserving' J).map_eq]
    _ = ((continuousKMTMeasure J).map (continuousKMTToContinuous J)).map
          (dyadicCellData J ⟨AllTimeKMTBrownianLaw.cellLocal 0 n, by
            simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n⟩) :=
      (Measure.map_map (measurable_dyadicCellData J
        ⟨AllTimeKMTBrownianLaw.cellLocal 0 n, by
          simpa using AllTimeKMTBrownianLaw.cellLocal_lt 0 n⟩)
        (measurable_continuousKMTToContinuous J)).symm
    _ = cellLaw := by
      rw [(continuousKMTMeasure_toContinuous J).map_eq]
      exact dyadicCellData_map J _

theorem poissonCellSeq_law :
    allTimeKMTMeasure.map poissonCellSeq = cellArrayLaw := by
  calc
    allTimeKMTMeasure.map poissonCellSeq =
        Measure.infinitePi fun n : ℕ =>
          allTimeKMTMeasure.map (fun ω => poissonCellSeq ω n) :=
      poissonCellSeq_iIndep.map_fun_eq_infinitePi_map
        (fun n => (measurable_pi_apply n).comp measurable_poissonCellSeq)
    _ = Measure.infinitePi (fun _ : ℕ => cellLaw) := by
      congr 1
      funext n
      exact poissonCellSeq_coord_map n
    _ = cellArrayLaw := rfl

/-! ## Increments of the all-time Poisson path over a finite grid -/

/-- Increment vector of the all-time Poisson path along a real grid. -/
def allTimeKMTPoissonIncrementVector {r : ℕ} (grid : Fin (r + 1) → ℝ)
    (ω : AllTimeKMTSpace) : Fin r → ℕ :=
  fun i => allTimeKMTPoisson (grid i.succ) ω -
    allTimeKMTPoisson (grid i.castSucc) ω

theorem allTimeKMTPoissonIncrementVector_eq {r : ℕ} (grid : Fin (r + 1) → ℝ)
    (hzero : grid 0 = 0) (hmono : Monotone grid) (ω : AllTimeKMTSpace) :
    allTimeKMTPoissonIncrementVector grid ω =
      cellIncrementVector grid (poissonCellSeq ω) := by
  funext i
  unfold allTimeKMTPoissonIncrementVector cellIncrementVector
  rw [allTimeKMTPoisson_eq_cellPath (grid_nonneg_of_monotone hzero hmono _) ω,
    allTimeKMTPoisson_eq_cellPath (grid_nonneg_of_monotone hzero hmono _) ω]

@[fun_prop]
theorem measurable_allTimeKMTPoissonIncrementVector {r : ℕ}
    (grid : Fin (r + 1) → ℝ) :
    Measurable (allTimeKMTPoissonIncrementVector grid) := by
  apply measurable_pi_lambda
  intro i
  have h1 : Measurable (allTimeKMTPoisson (grid i.succ)) :=
    measurable_allTimeKMTPoisson _
  have h2 : Measurable (allTimeKMTPoisson (grid i.castSucc)) :=
    measurable_allTimeKMTPoisson _
  exact h1.sub h2

/-- **Product Poisson law of increments**, for every monotone grid from `0`. -/
theorem allTimeKMTPoisson_incrementVector_law_of_monotone {r : ℕ}
    (grid : Fin (r + 1) → ℝ) (hzero : grid 0 = 0) (hmono : Monotone grid) :
    allTimeKMTMeasure.map (allTimeKMTPoissonIncrementVector grid) =
      poissonIncrementProduct grid := by
  have hfun : allTimeKMTPoissonIncrementVector grid =
      cellIncrementVector grid ∘ poissonCellSeq := by
    funext ω
    exact allTimeKMTPoissonIncrementVector_eq grid hzero hmono ω
  rw [hfun, ← Measure.map_map (measurable_cellIncrementVector grid)
    measurable_poissonCellSeq, poissonCellSeq_law]
  exact cellArrayLaw_incrementVector_law grid hzero hmono

/-- The increments are independent. -/
theorem allTimeKMTPoisson_increment_iIndep_of_monotone {r : ℕ}
    (grid : Fin (r + 1) → ℝ) (hzero : grid 0 = 0) (hmono : Monotone grid) :
    iIndepFun
      (fun i ω => allTimeKMTPoissonIncrementVector grid ω i)
      allTimeKMTMeasure := by
  have hG : ∀ i : Fin r, Measurable (fun a : ℕ → CellSpace =>
      cellPath (grid i.succ) a - cellPath (grid i.castSucc) a) := fun i =>
    (measurable_cellPath _).sub (measurable_cellPath _)
  have h := (iIndepFun_comp_map_iff measurable_poissonCellSeq
    (μ := allTimeKMTMeasure)
    (G := fun (i : Fin r) (a : ℕ → CellSpace) =>
      cellPath (grid i.succ) a - cellPath (grid i.castSucc) a) hG).mpr
    (by rw [poissonCellSeq_law]; exact cellArrayLaw_incrementVector_iIndep grid hmono)
  have hfun : (fun i ω => allTimeKMTPoissonIncrementVector grid ω i) =
      fun i => (fun a : ℕ → CellSpace =>
        cellPath (grid i.succ) a - cellPath (grid i.castSucc) a) ∘ poissonCellSeq := by
    funext i ω
    have := congrFun (allTimeKMTPoissonIncrementVector_eq grid hzero hmono ω) i
    exact this
  rw [hfun]
  exact h

/-- Strictly increasing grids, in the form of the finite-horizon statement. -/
theorem allTimeKMTPoisson_incrementVector_law {r : ℕ}
    (grid : Fin (r + 1) → ℝ) (hzero : grid 0 = 0)
    (hstrict : StrictMono grid) :
    allTimeKMTMeasure.map (allTimeKMTPoissonIncrementVector grid) =
      poissonIncrementProduct grid :=
  allTimeKMTPoisson_incrementVector_law_of_monotone grid hzero hstrict.monotone

theorem allTimeKMTPoisson_increment_iIndep {r : ℕ}
    (grid : Fin (r + 1) → ℝ) (hzero : grid 0 = 0)
    (hstrict : StrictMono grid) :
    iIndepFun
      (fun i ω => allTimeKMTPoissonIncrementVector grid ω i)
      allTimeKMTMeasure :=
  allTimeKMTPoisson_increment_iIndep_of_monotone grid hzero hstrict.monotone

end Ripple.Kurtz.StrongApprox.AllTimeKMTPoissonLaw

end
