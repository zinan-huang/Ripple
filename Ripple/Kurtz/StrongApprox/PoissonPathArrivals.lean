-- Ripple/Kurtz/StrongApprox/PoissonPathArrivals.lean
import Ripple.Kurtz.StrongApprox.PoissonSIP

/-!
# Finite labelled arrivals behind `poisPath`

On a bounded clock interval, a sample of `poisPath` is exactly the counting
function of finitely many labelled positions. Labels are retained, so repeated
positions represent a finite jump batch rather than being collapsed.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Counting a finite labelled family of arrivals, retaining multiplicity. -/
noncomputable def finiteArrivalCount {κ : Type*} [Fintype κ]
    (a : κ → ℝ) (u : ℝ) : ℕ :=
  ((Finset.univ : Finset κ).filter fun q => a q ≤ u).card

theorem finiteArrivalCount_mono {κ : Type*} [Fintype κ]
    (a : κ → ℝ) {u w : ℝ} (huw : u ≤ w) :
    finiteArrivalCount a u ≤ finiteArrivalCount a w := by
  classical
  unfold finiteArrivalCount
  exact Finset.card_le_card fun q hq => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact hq.trans huw

theorem finiteArrivalCount_zero {κ : Type*} [Fintype κ]
    (a : κ → ℝ) (ha : ∀ q, 0 < a q) :
    finiteArrivalCount a 0 = 0 := by
  classical
  unfold finiteArrivalCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  exact not_le.mpr (ha q)

/-- Number of cells sufficient to represent a path up to clock horizon `U`. -/
noncomputable def arrivalCellBound (U : ℝ) : ℕ := ⌊U⌋₊ + 1

/-- A labelled point in one of the first `arrivalCellBound U` cells. -/
abbrev RawArrival (N : ℕ → Ω → ℕ) (U : ℝ) (x : PathSpace Ω) :=
  Σ i : Fin (arrivalCellBound U), Fin (N i.1 x.1)

/-- Absolute clock position of a labelled cell point. -/
noncomputable def rawArrivalTime (N : ℕ → Ω → ℕ) (U : ℝ)
    (x : PathSpace Ω) (q : RawArrival N U x) : ℝ :=
  (q.1.1 : ℝ) + clip (x.2 q.1.1 q.2.1)

theorem arrivalTime_pos (N : ℕ → Ω → ℕ) (U : ℝ)
    (x : PathSpace Ω) (q : RawArrival N U x) :
    0 < rawArrivalTime N U x q := by
  unfold rawArrivalTime
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (clip_pos _)

/-- Keep only the labelled points whose absolute clock position is at most `U`. -/
abbrev HorizonArrival (N : ℕ → Ω → ℕ) (U : ℝ) (x : PathSpace Ω) :=
  {q : RawArrival N U x // rawArrivalTime N U x q ≤ U}

noncomputable def horizonArrivalTime (N : ℕ → Ω → ℕ) (U : ℝ)
    (x : PathSpace Ω) (q : HorizonArrival N U x) : ℝ :=
  rawArrivalTime N U x q.1

@[simp]
theorem horizonArrivalTime_pos (N : ℕ → Ω → ℕ) (U : ℝ)
    (x : PathSpace Ω) (q : HorizonArrival N U x) :
    0 < horizonArrivalTime N U x q :=
  arrivalTime_pos N U x q.1

private theorem rawArrivalCount_eq_cellSum (N : ℕ → Ω → ℕ)
    (U t : ℝ) (x : PathSpace Ω) :
    finiteArrivalCount (rawArrivalTime N U x) t =
      ∑ i : Fin (arrivalCellBound U),
        cellHit (Ioc 0 (t - (i.1 : ℝ))) (cellData N i.1 x) := by
  classical
  unfold finiteArrivalCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  unfold cellHit hitCount cellData
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hq : rawArrivalTime N U x ⟨i, m⟩ ≤ t
  · have hmem : clip (x.2 i.1 m.1) ∈ Ioc 0 (t - (i.1 : ℝ)) := by
      have hq' : (i.1 : ℝ) + clip (x.2 i.1 m.1) ≤ t := hq
      exact ⟨clip_pos _, by linarith⟩
    simp [hq, Set.indicator_of_mem hmem]
  · have hnot : clip (x.2 i.1 m.1) ∉ Ioc 0 (t - (i.1 : ℝ)) := by
      intro hm
      apply hq
      show (i.1 : ℝ) + clip (x.2 i.1 m.1) ≤ t
      linarith [hm.2]
    simp [hq, Set.indicator_of_notMem hnot]

/-- Exact finite labelled-arrival representation using all points in the
bounded family of cells. -/
theorem poisPath_eq_rawArrivalCount (N : ℕ → Ω → ℕ)
    {U t : ℝ} (ht : t ≤ U) (x : PathSpace Ω) :
    poisPath N t x = finiteArrivalCount (rawArrivalTime N U x) t := by
  have hU : U < (arrivalCellBound U : ℝ) := by
    unfold arrivalCellBound
    push_cast
    exact Nat.lt_floor_add_one U
  have htK : t < (arrivalCellBound U : ℝ) := ht.trans_lt hU
  rw [poisPath_eq_sum N htK x, rawArrivalCount_eq_cellSum]
  rw [← Fin.sum_univ_eq_sum_range]

private noncomputable def horizonSubtypeEquiv (N : ℕ → Ω → ℕ)
    {U t : ℝ} (ht : t ≤ U) (x : PathSpace Ω) :
    {q : RawArrival N U x // rawArrivalTime N U x q ≤ t} ≃
      {q : HorizonArrival N U x // horizonArrivalTime N U x q ≤ t} where
  toFun q := ⟨⟨q.1, q.2.trans ht⟩, q.2⟩
  invFun q := ⟨q.1.1, q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q with | mk q hq => cases q; rfl

/-- Exact representation using only arrivals lying in the requested horizon. -/
theorem poisPath_eq_horizonArrivalCount (N : ℕ → Ω → ℕ)
    {U t : ℝ} (ht : t ≤ U) (x : PathSpace Ω) :
    poisPath N t x =
      finiteArrivalCount (horizonArrivalTime N U x) t := by
  rw [poisPath_eq_rawArrivalCount N ht x]
  unfold finiteArrivalCount
  simp only [← Fintype.card_subtype]
  exact Fintype.card_congr (horizonSubtypeEquiv N ht x)

/-- Finite support containing every possible jump location before `U`. -/
noncomputable def horizonArrivalSupport (N : ℕ → Ω → ℕ)
    (U : ℝ) (x : PathSpace Ω) : Finset ℝ :=
  (Finset.univ : Finset (HorizonArrival N U x)).image
    (horizonArrivalTime N U x)

/-- If an interval contains no labelled arrival, the count cannot change. -/
theorem poisPath_eq_of_Ioc_disjoint_horizonSupport
    (N : ℕ → Ω → ℕ) {U s t : ℝ} (hst : s ≤ t) (htU : t ≤ U)
    (x : PathSpace Ω)
    (hdisj : Disjoint (Ioc s t : Set ℝ)
      (horizonArrivalSupport N U x : Set ℝ)) :
    poisPath N s x = poisPath N t x := by
  rw [poisPath_eq_horizonArrivalCount N (hst.trans htU) x,
    poisPath_eq_horizonArrivalCount N htU x]
  unfold finiteArrivalCount
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.trans hst
  · intro hqt
    by_contra hqs
    have hsq : s < horizonArrivalTime N U x q := lt_of_not_ge hqs
    have hmemSupport : horizonArrivalTime N U x q ∈
        horizonArrivalSupport N U x := by
      simp [horizonArrivalSupport]
    exact Set.disjoint_left.mp hdisj ⟨hsq, hqt⟩ hmemSupport

/-- A path has locally finite jumps on `[0,U]` when a finite set contains all
locations at which an interval count can change. -/
def LocallyFiniteJumpsOn (Y : ℝ → ℕ) (U : ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ U →
    Disjoint (Ioc s t : Set ℝ) (S : Set ℝ) → Y s = Y t

/-- Pointwise local finiteness of `poisPath`; no probabilistic qualification is
needed and finite jump multiplicities are allowed. -/
theorem poisPath_locallyFiniteJumps (N : ℕ → Ω → ℕ)
    (U : ℝ) (x : PathSpace Ω) :
    LocallyFiniteJumpsOn (fun t => poisPath N t x) U := by
  refine ⟨horizonArrivalSupport N U x, ?_⟩
  intro s t _ hst htU hdisj
  exact poisPath_eq_of_Ioc_disjoint_horizonSupport N hst htU x hdisj

/-- Explicit pointwise counterexample to the requested unit-jump assertion:
two labelled points at the same position produce one jump of size two. -/
theorem duplicate_points_make_batch_jump (N : ℕ → Ω → ℕ)
    (x : PathSpace Ω)
    (hcount : N 0 x.1 = 2)
    (hfirst : clip (x.2 0 0) = (1 : ℝ) / 2)
    (hsecond : clip (x.2 0 1) = (1 : ℝ) / 2) :
    poisPath N ((49 : ℝ) / 100) x = 0 ∧
      poisPath N ((1 : ℝ) / 2) x = 2 := by
  have hsum : ∀ A : Set ℝ, cellHit A (cellData N 0 x) =
      A.indicator (fun _ => (1 : ℕ)) ((1 : ℝ) / 2) +
        A.indicator (fun _ => (1 : ℕ)) ((1 : ℝ) / 2) := by
    intro A
    unfold cellHit hitCount cellData
    show ∑ m ∈ Finset.range (N 0 x.1), A.indicator (fun _ => (1 : ℕ)) (clip (x.2 0 m)) = _
    rw [hcount]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hfirst, hsecond]
  constructor
  · rw [poisPath_eq_sum N (K := 1) (by norm_num) x]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hsum]
    have hn : ((1 : ℝ) / 2) ∉ Ioc 0 ((49 : ℝ) / 100 - ((0 : ℕ) : ℝ)) := by
      simp only [Set.mem_Ioc, Nat.cast_zero, sub_zero]
      norm_num
    simp only [Set.indicator_of_notMem hn, add_zero]
  · rw [poisPath_eq_sum N (K := 1) (by norm_num) x]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hsum]
    have hm : ((1 : ℝ) / 2) ∈ Ioc 0 ((1 : ℝ) / 2 - ((0 : ℕ) : ℝ)) := by
      simp only [Set.mem_Ioc, Nat.cast_zero, sub_zero]
      norm_num
    simp [Set.indicator_of_mem hm]

/-- Family specialization of pointwise local finiteness. -/
theorem poisFamily_locallyFiniteJumps {ι : Type*} [Fintype ι]
    (N : ℕ → Ω → ℕ) (l : ι) (U : ℝ)
    (ω : ι → PathSpace Ω) :
    LocallyFiniteJumpsOn (fun t => poisFamily ι N l t ω) U := by
  simpa [poisFamily] using poisPath_locallyFiniteJumps N U (ω l)

end Ripple.Kurtz.StrongApprox

end
