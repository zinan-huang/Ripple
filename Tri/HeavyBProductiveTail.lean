/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBBandReturn
import Tri.HeavyBProductiveFloor
import Tri.DoubleBAssembly

/-!
# Heavy-B productive tail on a stopped band

This file ports the Double-B productive-count supermartingale to the existing
`HeavyTrace`.  The counter is `fuel + up + down`, and the stopped band kernel is
the already-defined `heavyBandStop`.
-/

namespace Tri

open scoped ENNReal

/-- The Heavy-B productive counter carried by `HeavyTrace`. -/
def heavyTraceProductiveCount {n : ℕ} (q : HeavyTrace n) : ℕ :=
  q.fuel + q.up + q.down

/-- The counter is unchanged by inert labels. -/
theorem nextHeavyTrace_inert {n : ℕ} (q : HeavyTrace n) (k : PairComp)
    (hk : k = .xx ∨ k = .yy ∨ k = .bb) :
    PairComp.nextHeavyTrace q k = q := by
  unfold PairComp.nextHeavyTrace
  by_cases hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0
  · rw [dif_pos hw]
  · rw [dif_neg hw]
    have hnext : PairComp.heavyNext q.cfg.1 k = q.cfg.1 := by
      rcases hk with h | h | h <;> subst h <;> rfl
    have hf : k.heavyFuelInc = 0 := by
      rcases hk with h | h | h <;> subst h <;> rfl
    have hu : k.heavyUpInc = 0 := by
      rcases hk with h | h | h <;> subst h <;> rfl
    have hd : k.heavyDownInc = 0 := by
      rcases hk with h | h | h <;> subst h <;> rfl
    rw [hf, hu, hd, Nat.add_zero, Nat.add_zero, Nat.add_zero]
    congr 1
    exact Subtype.ext hnext

/-- On a supported Heavy-B label, the productive counter advances by the
corresponding trace increments. -/
theorem nextHeavyTrace_productiveCount {n : ℕ} (q : HeavyTrace n)
    (k : PairComp)
    (hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    heavyTraceProductiveCount (PairComp.nextHeavyTrace q k)
      = heavyTraceProductiveCount q
        + (k.heavyFuelInc + k.heavyUpInc + k.heavyDownInc) := by
  simp [PairComp.nextHeavyTrace, heavyTraceProductiveCount, hw]
  omega

/-- One-step expansion of the Heavy-B productive counter.  Each productive
label (`xy`, `xb`, `yb`) increases `fuel + up + down` by exactly one. -/
theorem heavyTraceStep_prod_expect
    (n : ℕ) (hn : 3 ≤ n) (q : HeavyTrace n) (w : ℝ≥0∞) :
    expect (heavyTraceStep n q) (fun q' => w ^ heavyTraceProductiveCount q')
      = (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (heavy_two_entities hn q.cfg) .xx
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
              (heavy_two_entities hn q.cfg) .yy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
              (heavy_two_entities hn q.cfg) .bb)
          * w ^ heavyTraceProductiveCount q
        + (dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
              (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
              (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
              (heavy_two_entities hn q.cfg) .yb)
          * w ^ (heavyTraceProductiveCount q + 1) := by
  have hh : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b :=
    heavy_two_entities hn q.cfg
  have key : ∀ k : PairComp,
      dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh k
        * w ^ heavyTraceProductiveCount (PairComp.nextHeavyTrace q k)
      = dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh k
        * w ^ (heavyTraceProductiveCount q
          + (k.heavyFuelInc + k.heavyUpInc + k.heavyDownInc)) := by
    intro k
    by_cases hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k = 0
    · rw [dbPairPMF_zero_of_weight_zero hw]
      simp
    · rw [nextHeavyTrace_productiveCount q k hw]
  unfold heavyTraceStep
  rw [dif_pos hh, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb,
          PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [key .xx, key .xy, key .yy, key .xb, key .yb, key .bb]
  simp only [PairComp.heavyFuelInc, PairComp.heavyUpInc,
    PairComp.heavyDownInc]
  ring

/-- Heavy-B productivity supermartingale for `fuel + up + down`. -/
theorem heavyTrace_prod_super
    (n : ℕ) (hn : 3 ≤ n) (q : HeavyTrace n)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hpp : p + p' = 1)
    (hwt : w ≠ ⊤) (hpT : p ≠ ⊤) (hp't : p' ≠ ⊤)
    (hprod : p ≤
      dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
          (heavy_two_entities hn q.cfg) .xy
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
          (heavy_two_entities hn q.cfg) .xb
        + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
          (heavy_two_entities hn q.cfg) .yb) :
    expect (heavyTraceStep n q) (fun q' => w ^ heavyTraceProductiveCount q')
      ≤ (p' + p * w) * w ^ heavyTraceProductiveCount q := by
  have hh : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b :=
    heavy_two_entities hn q.cfg
  set c := heavyTraceProductiveCount q
  set xx := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .xx
  set yy := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .yy
  set bb := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .bb
  set xy := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .xy
  set xb := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .xb
  set yb := dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh .yb
  have hfin : ∀ k, dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hh k ≠ ⊤ :=
    fun k => PMF.apply_ne_top _ _
  have hit : xx + yy + bb ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩, hfin _⟩
  have hpt : xy + xb + yb ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩, hfin _⟩
  rw [heavyTraceStep_prod_expect n hn q w]
  have hmass : (xx + yy + bb) + (xy + xb + yb) = 1 := by
    have := dbPairPMF_sum_six q.cfg.1.x q.cfg.1.y q.cfg.1.b hh
    rw [← this]
    ring
  calc
    (xx + yy + bb) * w ^ c + (xy + xb + yb) * w ^ (c + 1)
        = ((xx + yy + bb) + (xy + xb + yb) * w) * w ^ c := by
          rw [pow_succ]
          ring
    _ ≤ (p' + p * w) * w ^ c :=
        mul_le_mul_left
          (prod_scalar (xx + yy + bb) (xy + xb + yb) w p p'
            hmass hpp hprod hw1 hit hpt hwt hpT hp't) (w ^ c)

/-- Productive-count `V`-supermartingale for a frozen Heavy-B trace set. -/
theorem heavyProd_V_super
    (n : ℕ) (hn : 3 ≤ n)
    (B : HeavyTrace n → Prop) [DecidablePred B]
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hpp : p + p' = 1)
    (hwt : w ≠ ⊤) (hpT : p ≠ ⊤) (hp't : p' ≠ ⊤)
    (hBprod : ∀ q : HeavyTrace n, ¬ B q →
      p ≤ dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .yb) :
    ∀ q : HeavyTrace n,
      expect (freeze B (heavyTraceStep n) q)
          (fun z => if B z then 0 else w ^ heavyTraceProductiveCount z)
        ≤ (p' + p * w) *
          (if B q then 0 else w ^ heavyTraceProductiveCount q) := by
  intro q
  by_cases hB : B q
  · rw [freeze_of_mem q hB, expect_pure]
    simp [hB]
  · rw [freeze_of_not_mem q hB, if_neg hB]
    calc
      expect (heavyTraceStep n q)
          (fun z => if B z then 0 else w ^ heavyTraceProductiveCount z)
        ≤ expect (heavyTraceStep n q)
            (fun z => w ^ heavyTraceProductiveCount z) := by
          unfold expect
          refine ENNReal.tsum_le_tsum fun z => ?_
          exact mul_le_mul_right (by by_cases hBz : B z <;> simp [hBz]) _
      _ ≤ (p' + p * w) * w ^ heavyTraceProductiveCount q :=
          heavyTrace_prod_super n hn q w p p' hw1 hpp hwt hpT hp't
            (hBprod q hB)

/-- Heavy-B productive lower tail for an arbitrary frozen trace set. -/
theorem heavyProductivity_tail
    (n : ℕ) (hn : 3 ≤ n)
    (B : HeavyTrace n → Prop) [DecidablePred B]
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hpp : p + p' = 1)
    (hwt : w ≠ ⊤) (hpT : p ≠ ⊤) (hp't : p' ≠ ⊤)
    (hBprod : ∀ q : HeavyTrace n, ¬ B q →
      p ≤ dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .yb)
    (T m : ℕ) (q₀ : HeavyTrace n) :
    ∑' q, (if heavyTraceProductiveCount q ≤ m ∧ ¬ B q then
        iter (freeze B (heavyTraceStep n)) T q₀ q else 0)
      ≤ (p' + p * w) ^ T
          * (if B q₀ then 0 else w ^ heavyTraceProductiveCount q₀)
          / w ^ m :=
  count_tail_frozen (heavyTraceStep n) B heavyTraceProductiveCount w (p' + p * w)
    hw1 hw0 (heavyProd_V_super n hn B w p p' hw1 hpp hwt hpT hp't hBprod)
    T m q₀

/-- Productive-clock tail on the stopped Heavy-B band. -/
theorem heavyBand_productive_tail
    (n aLo hi T K : ℕ) (hn : 3 ≤ n) (pp : ℝ≥0∞) (hpp1 : pp ≤ 1)
    (hfloor : ∀ q : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 →
      BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi →
      pp ≤ dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .yb)
    (q₀ : HeavyTrace n) (hc0 : q₀.fuel + q₀.up + q₀.down = 0) :
    ∑' q, (if (aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 ∧
            BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi)
            ∧ q.fuel + q.up + q.down < K then
        iter (heavyBandStop n aLo hi) T q₀ q else 0)
      ≤ ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T
          / ((1 : ℝ≥0∞) / 2) ^ K := by
  classical
  let B : HeavyTrace n → Prop := fun q =>
    BiCfg.heavyLevel q.cfg.1 ≤ aLo ∨ hi ≤ BiCfg.heavyLevel q.cfg.1
  let w : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  let pp' : ℝ≥0∞ := 1 - pp
  have hw1 : w ≤ 1 := by norm_num [w]
  have hw0 : w ≠ 0 := by norm_num [w]
  have hwt : w ≠ ⊤ := by norm_num [w]
  have hpp : pp + pp' = 1 := by
    dsimp [pp']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpp1
  have hpT : pp ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hpp1
  have hp'1 : pp' ≤ 1 := by
    dsimp [pp']
    exact tsub_le_self
  have hp't : pp' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp'1
  have hBprod : ∀ q : HeavyTrace n, ¬ B q →
      pp ≤ dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xy
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .xb
          + dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b
            (heavy_two_entities hn q.cfg) .yb := by
    intro q hq
    exact hfloor q (by dsimp [B] at hq; omega) (by dsimp [B] at hq; omega)
  have hsub : ∀ q,
      (if (aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 ∧
              BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi)
              ∧ q.fuel + q.up + q.down < K then
          iter (heavyBandStop n aLo hi) T q₀ q else 0)
        ≤ (if heavyTraceProductiveCount q ≤ K ∧ ¬ B q then
          iter (heavyBandStop n aLo hi) T q₀ q else 0) := by
    intro q
    by_cases hq : (aLo + 1 ≤ BiCfg.heavyLevel q.cfg.1 ∧
              BiCfg.heavyLevel q.cfg.1 + 1 ≤ hi)
              ∧ q.fuel + q.up + q.down < K
    · rw [if_pos hq]
      have hnB : ¬ B q := by
        dsimp [B]
        omega
      have hcount : heavyTraceProductiveCount q ≤ K := by
        unfold heavyTraceProductiveCount
        omega
      rw [if_pos ⟨hcount, hnB⟩]
    · rw [if_neg hq]
      positivity
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  rw [heavyBandStop_eq_freeze aLo hi]
  have htail := heavyProductivity_tail n hn B w pp pp' hw1 hw0 hpp hwt
    hpT hp't hBprod T K q₀
  refine le_trans htail ?_
  dsimp [w, pp']
  gcongr
  · by_cases hB0 : B q₀
    · simp [hB0]
    · simp [hB0, heavyTraceProductiveCount, hc0]

end Tri

#print axioms Tri.nextHeavyTrace_inert
#print axioms Tri.nextHeavyTrace_productiveCount
#print axioms Tri.heavyTraceStep_prod_expect
#print axioms Tri.heavyTrace_prod_super
#print axioms Tri.heavyProd_V_super
#print axioms Tri.heavyProductivity_tail
#print axioms Tri.heavyBand_productive_tail
