/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBDirection
import Tri.SingleBCreationStep

/-!
# The Heavy-B six-composition expectation expansion

The last piece the two-parameter potential needs before it can be applied to
`heavyTraceStep`: one step's expectation, resolved into the three groups the
direction argument distinguishes.

## The creation is invisible here, and that shortens the proof

`doubleTraceStep_expect` has to work case-by-case through all six compositions.
Heavy-B's version does not, because the observable `G` reads only the level and
the two resolution counters — and Heavy-B's creation touches ONLY `fuel`. So all
four neutral compositions (`xy`, `xx`, `yy`, `bb`) contribute the SAME value,
and — the useful part — they do so **whether or not their weight is zero**, since
a zero-weight event freezes the whole trace and a firing creation moves nothing
`G` can see.

That is `nextHeavyTrace_neutral_proj`, and it needs no weight hypothesis. Only
the two resolutions require a case split, and there the zero-weight branch is
killed by its own vanishing mass rather than by an argument.
-/

namespace Tri
open scoped ENNReal


theorem pairComp_sum_expand (F : PairComp → ℝ≥0∞) :
    ∑ k : PairComp, F k
      = (F .xy + F .xx + F .yy + F .bb) + (F .yb + F .xb) := by
  rw [show (Finset.univ : Finset PairComp) =
    {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb,
     PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The neutral group leaves level, up and down alone -- including the
creation, which touches only `fuel`.  No weight hypothesis is needed. -/
theorem nextHeavyTrace_neutral_proj {n : ℕ} (q : HeavyTrace n) (k : PairComp)
    (hk : k = .xy ∨ k = .xx ∨ k = .yy ∨ k = .bb) :
    BiCfg.heavyLevel (PairComp.nextHeavyTrace q k).cfg.1
        = BiCfg.heavyLevel q.cfg.1
      ∧ (PairComp.nextHeavyTrace q k).up = q.up
      ∧ (PairComp.nextHeavyTrace q k).down = q.down := by
  unfold PairComp.nextHeavyTrace
  split_ifs with hw
  · exact ⟨rfl, rfl, rfl⟩
  · rcases hk with rfl | rfl | rfl | rfl
    · obtain ⟨hx, hy⟩ :=
        Nat.mul_ne_zero_iff.mp (by simpa [PairComp.weight] using hw)
      refine ⟨?_, rfl, rfl⟩
      simp only [PairComp.heavyNext, BiCfg.heavyLevel]
      omega
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩

/-- A firing `Y`-resolution: level down one, `down` up one, `up` fixed. -/
theorem nextHeavyTrace_yb_proj {n : ℕ} (q : HeavyTrace n) (a : ℕ)
    (ha : BiCfg.heavyLevel q.cfg.1 = a + 1)
    (hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b PairComp.yb ≠ 0) :
    BiCfg.heavyLevel (PairComp.nextHeavyTrace q PairComp.yb).cfg.1 = a
      ∧ (PairComp.nextHeavyTrace q PairComp.yb).up = q.up
      ∧ (PairComp.nextHeavyTrace q PairComp.yb).down = q.down + 1 := by
  unfold PairComp.nextHeavyTrace
  rw [dif_neg hw]
  refine ⟨?_, rfl, rfl⟩
  have h := heavyLevel_heavyNext_yb q.cfg.1 hw
  simp only at h ⊢
  omega

/-- A firing `X`-resolution: level up one, `up` up one, `down` fixed. -/
theorem nextHeavyTrace_xb_proj {n : ℕ} (q : HeavyTrace n) (a : ℕ)
    (ha : BiCfg.heavyLevel q.cfg.1 = a + 1)
    (hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b PairComp.xb ≠ 0) :
    BiCfg.heavyLevel (PairComp.nextHeavyTrace q PairComp.xb).cfg.1 = a + 2
      ∧ (PairComp.nextHeavyTrace q PairComp.xb).up = q.up + 1
      ∧ (PairComp.nextHeavyTrace q PairComp.xb).down = q.down := by
  unfold PairComp.nextHeavyTrace
  rw [dif_neg hw]
  refine ⟨?_, rfl, rfl⟩
  have h := heavyLevel_heavyNext_xb q.cfg.1 hw
  simp only at h ⊢
  omega

/-- **The expansion.**  One Heavy-B step, resolved into down / neutral / up. -/
theorem heavyTraceStep_expect (n : ℕ) (q : HeavyTrace n)
    (h : 2 ≤ heavyEntities q.cfg) (a : ℕ)
    (ha : BiCfg.heavyLevel q.cfg.1 = a + 1) (G : ℕ → ℕ → ℕ → ℝ≥0∞) :
    expect (heavyTraceStep n q)
        (fun z => G (BiCfg.heavyLevel z.cfg.1) z.up z.down)
      = heavyResolveDown q.cfg * G a q.up (q.down + 1)
        + heavyNeutralMass h * G (a + 1) q.up q.down
        + heavyResolveUp q.cfg * G (a + 2) (q.up + 1) q.down := by
  have hcond : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := h
  unfold heavyTraceStep
  rw [dif_pos hcond, expect_map, expect_fintype, pairComp_sum_expand]
  -- the four neutral compositions all read the same
  have hneu : ∀ k : PairComp, (k = .xy ∨ k = .xx ∨ k = .yy ∨ k = .bb) →
      G (BiCfg.heavyLevel (PairComp.nextHeavyTrace q k).cfg.1)
          (PairComp.nextHeavyTrace q k).up (PairComp.nextHeavyTrace q k).down
        = G (a + 1) q.up q.down := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := nextHeavyTrace_neutral_proj q k hk
    rw [h1, h2, h3, ha]
  rw [hneu .xy (Or.inl rfl), hneu .xx (Or.inr (Or.inl rfl)),
    hneu .yy (Or.inr (Or.inr (Or.inl rfl))),
    hneu .bb (Or.inr (Or.inr (Or.inr rfl)))]
  -- the two resolutions, each with its zero-weight branch killed by its mass
  have hyb : dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hcond .yb
      * G (BiCfg.heavyLevel (PairComp.nextHeavyTrace q .yb).cfg.1)
          (PairComp.nextHeavyTrace q .yb).up
          (PairComp.nextHeavyTrace q .yb).down
      = heavyResolveDown q.cfg * G a q.up (q.down + 1) := by
    by_cases hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b PairComp.yb = 0
    · have hm : dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hcond .yb = 0 := by
        rw [dbPairPMF_apply, hw]; simp
      rw [hm, ← heavyResolveDown_eq q.cfg h, hm]
      simp
    · obtain ⟨h1, h2, h3⟩ := nextHeavyTrace_yb_proj q a ha hw
      rw [h1, h2, h3, heavyResolveDown_eq q.cfg h]
  have hxb : dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hcond .xb
      * G (BiCfg.heavyLevel (PairComp.nextHeavyTrace q .xb).cfg.1)
          (PairComp.nextHeavyTrace q .xb).up
          (PairComp.nextHeavyTrace q .xb).down
      = heavyResolveUp q.cfg * G (a + 2) (q.up + 1) q.down := by
    by_cases hw : PairComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b PairComp.xb = 0
    · have hm : dbPairPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hcond .xb = 0 := by
        rw [dbPairPMF_apply, hw]; simp
      rw [hm, ← heavyResolveUp_eq q.cfg h, hm]
      simp
    · obtain ⟨h1, h2, h3⟩ := nextHeavyTrace_xb_proj q a ha hw
      rw [h1, h2, h3, heavyResolveUp_eq q.cfg h]
  rw [hyb, hxb]
  unfold heavyNeutralMass
  ring

end Tri

#print axioms Tri.pairComp_sum_expand
#print axioms Tri.nextHeavyTrace_neutral_proj
#print axioms Tri.nextHeavyTrace_yb_proj
#print axioms Tri.nextHeavyTrace_xb_proj
#print axioms Tri.heavyTraceStep_expect
