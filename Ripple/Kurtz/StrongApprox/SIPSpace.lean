/-
  Ripple.Kurtz.StrongApprox.SIPSpace — the probability space of the discrete strong invariance
  principle: one coupled block per index `(r, s)`, iid Poisson(1) unit counts `sipN`, iid
  standard normal steps `sipZ`, the block discrepancies `sipR`, and the identities tying the
  partial sums `sipD k = Σ_{i<k} (N_i − 1 − Z_i)` at block endpoints to the block discrepancies.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonSplitting
import Ripple.Kurtz.StrongApprox.SIPCells

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

/-! ### The space -/

/-- One block space per block index `(r, s)`. -/
abbrev SIPSpace : Type := ℕ × ℕ → BlockSpace

/-- The product of the block laws, block `(r, s)` having length `2^r`. -/
noncomputable def sipMeasure : Measure SIPSpace :=
  Measure.infinitePi (fun rs : ℕ × ℕ => blockMeasure (2 ^ rs.1))

instance : IsProbabilityMeasure sipMeasure := by
  unfold sipMeasure; infer_instance

/-- The block of a cell. -/
def cellBlock (i : ℕ) : ℕ × ℕ := (cellAnn i, cellBlk i)

/-- The Gaussian step of cell `i`. -/
noncomputable def sipZ (i : ℕ) (ω : SIPSpace) : ℝ := (ω (cellBlock i)).1 (cellPos i)

/-- The Poisson unit count of cell `i`. -/
noncomputable def sipN (i : ℕ) (ω : SIPSpace) : ℕ :=
  cellCount (2 ^ cellAnn i) (cellPos i) (ω (cellBlock i))

/-- The Poisson count of block `(r, s)`. -/
noncomputable def sipQ (r s : ℕ) (ω : SIPSpace) : ℕ := blockCount (2 ^ r) (ω (r, s))

/-- The discrepancy `Q − 2^r − Σ Z` of block `(r, s)`. -/
noncomputable def sipR (r s : ℕ) (ω : SIPSpace) : ℝ := blockErr (2 ^ r) (ω (r, s))

/-- The partial discrepancy `Σ_{i<k} (N_i − 1 − Z_i)`. -/
noncomputable def sipD (k : ℕ) (ω : SIPSpace) : ℝ :=
  ∑ i ∈ range k, ((sipN i ω : ℝ) - 1 - sipZ i ω)

theorem measurable_sipZ (i : ℕ) : Measurable (sipZ i) :=
  (measurable_pi_apply (cellPos i)).comp (measurable_fst.comp (measurable_pi_apply (cellBlock i)))

theorem measurable_sipN (i : ℕ) : Measurable (sipN i) :=
  (measurable_cellCount (by positivity) (cellPos i)).comp (measurable_pi_apply (cellBlock i))

theorem measurable_sipR (r s : ℕ) : Measurable (sipR r s) :=
  (measurable_blockErr (by positivity)).comp (measurable_pi_apply (r, s))

theorem measurable_sipD (k : ℕ) : Measurable (sipD k) :=
  Finset.measurable_sum _ fun i _ =>
    (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_sipN i)).sub
      measurable_const).sub (measurable_sipZ i)

/-! ### Laws and independence of the cell families -/

theorem sipMeasure_map_eval (rs : ℕ × ℕ) :
    sipMeasure.map (fun ω : SIPSpace => ω rs) = blockMeasure (2 ^ rs.1) :=
  Measure.infinitePi_map_eval _ rs

theorem sipMeasure_map_sipZ (i : ℕ) : sipMeasure.map (sipZ i) = gaussianReal 0 1 := by
  unfold sipMeasure sipZ
  rw [infinitePi_map_cell _ (cellBlock i) (W := fun x : BlockSpace => x.1 (cellPos i))
    ((measurable_pi_apply (cellPos i)).comp measurable_fst)]
  exact blockMeasure_map_fst_eval _ _

/-- `P{N_i = k} = e^{−1}/k!`. -/
theorem sipMeasure_sipN_eq (i k : ℕ) :
    sipMeasure {ω | sipN i ω = k} = ENNReal.ofReal (poisTerm k 1) := by
  unfold sipMeasure sipN
  rw [show {ω : SIPSpace | cellCount (2 ^ cellAnn i) (cellPos i) (ω (cellBlock i)) = k} =
      (fun ω : SIPSpace => ω (cellBlock i)) ⁻¹'
        {x | cellCount (2 ^ cellAnn i) (cellPos i) x = k} from rfl]
  rw [infinitePi_eval_preimage _ (cellBlock i)
    (s := {x | cellCount (2 ^ cellAnn i) (cellPos i) x = k})
    (measurable_cellCount (by positivity) _ (measurableSet_singleton k))]
  exact blockMeasure_cellCount_eq (2 ^ cellAnn i) ⟨cellPos i, cellPos_lt i⟩ k

theorem cellBlock_eq {i r s : ℕ} (h : cellBlock i = (r, s)) : cellAnn i = r ∧ cellBlk i = s := by
  simpa [cellBlock, Prod.mk.injEq] using h

/-- Two cells of one block with the same position coincide. -/
theorem cell_eq_of_pos {i i' : ℕ} (hb : cellBlock i = cellBlock i') (hp : cellPos i = cellPos i') :
    i = i' := by
  rw [← blockStart_cell i, ← blockStart_cell i']
  obtain ⟨h1, h2⟩ := cellBlock_eq (hb.trans rfl)
  rw [h1, h2, hp]

/-- **The Gaussian steps are iid standard normal.** -/
theorem iIndepFun_sipZ : iIndepFun sipZ sipMeasure := by
  have h := iIndepFun_cells (fun rs : ℕ × ℕ => blockMeasure (2 ^ rs.1)) cellBlock
    (fun i (x : BlockSpace) => x.1 (cellPos i))
    (fun i => (measurable_pi_apply _).comp measurable_fst) ?_
  · exact h
  · rintro ⟨r, s⟩
    have hinj : Function.Injective (fun c : {c // cellBlock c = (r, s)} => cellPos c.1) := by
      intro c c' h
      exact Subtype.ext (cell_eq_of_pos (c.2.trans c'.2.symm) h)
    exact (iIndepFun_blockMeasure_fst (2 ^ r)).precomp hinj

/-- **The unit counts are iid Poisson(1).** -/
theorem iIndepFun_sipN : iIndepFun sipN sipMeasure := by
  have h := iIndepFun_cells (fun rs : ℕ × ℕ => blockMeasure (2 ^ rs.1)) cellBlock
    (fun i (x : BlockSpace) => cellCount (2 ^ cellAnn i) (cellPos i) x)
    (fun i => measurable_cellCount (by positivity) _) ?_
  · exact h
  · rintro ⟨r, s⟩
    let pos : {c // cellBlock c = (r, s)} → Fin (2 ^ r) := fun c =>
      ⟨cellPos c.1, by have h := cellPos_lt c.1; rwa [(cellBlock_eq c.2).1] at h⟩
    have hinj : Function.Injective pos := by
      intro c c' h
      exact Subtype.ext (cell_eq_of_pos (c.2.trans c'.2.symm) (Fin.mk.inj_iff.mp h))
    have h2 := (iIndepFun_cellCount (2 ^ r)).precomp hinj
    have e : (fun c : {c // cellBlock c = (r, s)} => cellCount (2 ^ cellAnn c.1) (cellPos c.1)) =
        fun c => cellCount (2 ^ r) (pos c) := by
      funext c
      rw [(cellBlock_eq c.2).1]
    rw [e]
    exact h2

/-! ### The block discrepancies -/

theorem iIndepFun_sipR (r : ℕ) : iIndepFun (fun s => sipR r s) sipMeasure := by
  have h := iIndepFun_infinitePi (P := fun rs : ℕ × ℕ => blockMeasure (2 ^ rs.1))
    (X := fun rs => blockErr (2 ^ rs.1)) (fun rs => measurable_blockErr (by positivity))
  exact h.precomp (g := fun s => (r, s)) (fun s s' h => (Prod.mk.inj h).2)

theorem integral_sipR (r s : ℕ) : ∫ ω, sipR r s ω ∂sipMeasure = 0 := by
  unfold sipR sipMeasure
  rw [← integral_map (measurable_pi_apply (r, s)).aemeasurable
    (measurable_blockErr (by positivity)).aestronglyMeasurable, Measure.infinitePi_map_eval]
  exact integral_blockErr _

theorem integral_sipR_sq_le (r s : ℕ) : ∫ ω, sipR r s ω ^ 2 ∂sipMeasure ≤ 17 := by
  have h := integral_map (μ := sipMeasure) (φ := fun ω : SIPSpace => ω (r, s))
    (measurable_pi_apply (r, s)).aemeasurable
    (f := fun y : BlockSpace => blockErr (2 ^ r) y ^ 2)
    ((measurable_blockErr (by positivity)).pow_const 2).aestronglyMeasurable
  rw [sipMeasure_map_eval] at h
  unfold sipR
  rw [← h]
  exact integral_blockErr_sq_le _

theorem memLp_sipR (r s : ℕ) : MemLp (sipR r s) 2 sipMeasure := by
  unfold sipR sipMeasure
  have h := memLp_blockErr (2 ^ r)
  rw [← Measure.infinitePi_map_eval (fun rs : ℕ × ℕ => blockMeasure (2 ^ rs.1)) (r, s)] at h
  exact (memLp_map_measure_iff (measurable_blockErr (by positivity)).aestronglyMeasurable
    (measurable_pi_apply _).aemeasurable).mp h

/-! ### Cells of a block -/

theorem sipN_blockStart {r s p : ℕ} (hs : s < 3 * 2 ^ r) (hp : p < 2 ^ r) (ω : SIPSpace) :
    sipN (blockStart r s + p) ω = cellCount (2 ^ r) p (ω (r, s)) := by
  unfold sipN cellBlock
  rw [cellAnn_blockStart hs hp, cellBlk_blockStart hs hp, cellPos_blockStart hs hp]

theorem sipZ_blockStart {r s p : ℕ} (hs : s < 3 * 2 ^ r) (hp : p < 2 ^ r) (ω : SIPSpace) :
    sipZ (blockStart r s + p) ω = (ω (r, s)).1 p := by
  unfold sipZ cellBlock
  rw [cellAnn_blockStart hs hp, cellBlk_blockStart hs hp, cellPos_blockStart hs hp]

/-- The unit counts of a block add up to the block count. -/
theorem sum_sipN_block {r s : ℕ} (hs : s < 3 * 2 ^ r) (ω : SIPSpace) :
    ∑ p ∈ range (2 ^ r), sipN (blockStart r s + p) ω = sipQ r s ω := by
  rw [Finset.sum_congr rfl (fun p hp => sipN_blockStart hs (Finset.mem_range.mp hp) ω)]
  exact sum_cellCount (by positivity) _

/-- The block sum of the cell discrepancies is the block discrepancy. -/
theorem sum_block_eq_sipR {r s : ℕ} (hs : s < 3 * 2 ^ r) (ω : SIPSpace) :
    ∑ p ∈ range (2 ^ r), ((sipN (blockStart r s + p) ω : ℝ) - 1 - sipZ (blockStart r s + p) ω) =
      sipR r s ω := by
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [sipN_blockStart hs (Finset.mem_range.mp hp), sipZ_blockStart hs (Finset.mem_range.mp hp)])]
  unfold sipR blockErr gaussSum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Nat.cast_sum,
    sum_cellCount (by positivity)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-! ### Partial discrepancies at block endpoints -/

theorem sipD_add (a p : ℕ) (ω : SIPSpace) :
    sipD (a + p) ω = sipD a ω + ∑ x ∈ range p, ((sipN (a + x) ω : ℝ) - 1 - sipZ (a + x) ω) :=
  Finset.sum_range_add _ a p

theorem sipD_blockStart_succ {r s : ℕ} (hs : s < 3 * 2 ^ r) (ω : SIPSpace) :
    sipD (blockStart r (s + 1)) ω = sipD (blockStart r s) ω + sipR r s ω := by
  rw [blockStart_succ, sipD_add, sum_block_eq_sipR hs]

theorem sipD_blockStart {r s : ℕ} (hs : s ≤ 3 * 2 ^ r) (ω : SIPSpace) :
    sipD (blockStart r s) ω = sipD (annStart r) ω + ∑ s' ∈ range s, sipR r s' ω := by
  induction s with
  | zero => simp [blockStart_zero]
  | succ s ih =>
    rw [sipD_blockStart_succ (by omega), ih (by omega), Finset.sum_range_succ, add_assoc]

theorem sipD_annStart_succ (r : ℕ) (ω : SIPSpace) :
    sipD (annStart (r + 1)) ω = sipD (annStart r) ω + ∑ s ∈ range (3 * 2 ^ r), sipR r s ω := by
  rw [annStart_succ, sipD_blockStart le_rfl]

theorem sipD_annStart_zero (ω : SIPSpace) : sipD (annStart 0) ω = 0 := by
  simp [sipD, annStart_zero]

/-- A cell inside a block: `D_k = D_{annStart r} + Σ_{s'<s} R_{r,s'} + Σ_{x<p} (N − 1) − Σ_{x<p} Z`. -/
theorem sipD_cell {r s p : ℕ} (hs : s < 3 * 2 ^ r) (ω : SIPSpace) :
    sipD (blockStart r s + p) ω =
      sipD (annStart r) ω + ∑ s' ∈ range s, sipR r s' ω +
        ∑ x ∈ range p, ((sipN (blockStart r s + x) ω : ℝ) - 1) -
          ∑ x ∈ range p, sipZ (blockStart r s + x) ω := by
  rw [sipD_add, sipD_blockStart hs.le, Finset.sum_sub_distrib]
  ring

end Ripple.Kurtz.StrongApprox
