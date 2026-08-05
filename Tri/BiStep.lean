/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BiKernel
import Tri.BiMolecular

/-!
# The Double-B step kernel (Theorem 2)

The Double-B bi-molecular CRN acts on configurations `BiCfg (x,y,b)` with
`x + y + b = n`.  A step draws an unordered pair of the `n` molecules uniformly;
its composition is one of six kinds (`PairComp`).  The productive pairs fire the
reactions

* `xy` : `X + Y → 2B`   (`doubleLevel` unchanged),
* `xb` : `X + B → 2X`   (`doubleLevel` `+1`),
* `yb` : `Y + B → 2Y`   (`doubleLevel` `-1`),

while `xx`, `yy`, `bb` are inert.  `doubleBStep` is the induced kernel on
`BiCfg`, mirroring `triStep` one degree lower with `three_pair_split` as its
normalisation.
-/

namespace Tri

open scoped ENNReal

/-- The six compositions of an unordered pair drawn from species `X`, `Y`, `B`. -/
inductive PairComp
  | xx | xy | yy | xb | yb | bb
  deriving DecidableEq, Fintype, Repr

/-- The number of unordered pairs of each composition. -/
def PairComp.weight (x y b : ℕ) : PairComp → ℕ
  | .xx => Nat.choose x 2 | .xy => x * y | .yy => Nat.choose y 2
  | .xb => x * b | .yb => y * b | .bb => Nat.choose b 2

/-- The six pair-composition counts sum to `C(x+y+b,2)`. -/
theorem pairComp_sum_weight (x y b : ℕ) :
    (∑ k : PairComp, PairComp.weight x y b k) = Nat.choose (x + y + b) 2 := by
  rw [show (Finset.univ : Finset PairComp) =
    {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  simp [PairComp.weight, three_pair_split]
  ring

/-- The distribution of the composition of a uniformly drawn unordered pair in a
mixture of `x` `X`, `y` `Y`, `b` `B`, with `2 ≤ x + y + b`. -/
noncomputable def dbPairPMF (x y b : ℕ) (h : 2 ≤ x + y + b) : PMF PairComp :=
  PMF.ofFintype
    (fun k => (PairComp.weight x y b k : ℝ≥0∞) / (Nat.choose (x + y + b) 2 : ℝ≥0∞))
    (by
      have hpos : 0 < Nat.choose (x + y + b) 2 := Nat.choose_pos h
      have hne : ((Nat.choose (x + y + b) 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
      have htop : ((Nat.choose (x + y + b) 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [show ∑ k : PairComp, ((PairComp.weight x y b k : ℕ) : ℝ≥0∞)
            = ((∑ k : PairComp, PairComp.weight x y b k : ℕ) : ℝ≥0∞) by push_cast; rfl]
      rw [pairComp_sum_weight, ← div_eq_mul_inv]
      exact ENNReal.div_self hne htop)

@[simp] theorem dbPairPMF_apply (x y b : ℕ) (h : 2 ≤ x + y + b) (k : PairComp) :
    dbPairPMF x y b h k = (PairComp.weight x y b k : ℝ≥0∞) / (Nat.choose (x + y + b) 2 : ℝ≥0∞) :=
  rfl

/-- The next configuration under each pair composition.  `xx`, `yy`, `bb` are
inert; `xy`/`xb`/`yb` fire the three Double-B reactions.  (The truncated
subtractions only occur on zero-weight compositions.) -/
def PairComp.next (s : BiCfg) : PairComp → BiCfg
  | .xx => s | .yy => s | .bb => s
  | .xy => ⟨s.x - 1, s.y - 1, s.b + 2⟩
  | .xb => ⟨s.x + 1, s.y, s.b - 1⟩
  | .yb => ⟨s.x, s.y + 1, s.b - 1⟩

/-- **The Double-B step kernel.**  Draw a uniform pair, then apply its reaction. -/
noncomputable def doubleBStep (s : BiCfg) (h : 2 ≤ s.x + s.y + s.b) : PMF BiCfg :=
  (dbPairPMF s.x s.y s.b h).map (PairComp.next s)

/-! ## Resolution-event classification

Every productive reaction moves `doubleLevel` by a fixed amount: `xb` up by one
(a *resolution-up* event), `yb` down by one (*resolution-down*), and `xy` not at
all (*neutral*).  The inert compositions leave the state fixed.  These are the
events over which the domination argument of Theorem 2 is run. -/

/-- `xb` (`X + B → 2X`) is a resolution-up event: `doubleLevel` increases by one. -/
theorem next_xb_level (s : BiCfg) (hb : 1 ≤ s.b) :
    BiCfg.doubleLevel (PairComp.next s .xb) = BiCfg.doubleLevel s + 1 := by
  unfold BiCfg.doubleLevel PairComp.next; simp only; omega

/-- `yb` (`Y + B → 2Y`) is a resolution-down event: `doubleLevel` decreases by one. -/
theorem next_yb_level (s : BiCfg) (hb : 1 ≤ s.b) :
    BiCfg.doubleLevel (PairComp.next s .yb) + 1 = BiCfg.doubleLevel s := by
  unfold BiCfg.doubleLevel PairComp.next; simp only; omega

/-- `xy` (`X + Y → 2B`) is neutral for `doubleLevel`. -/
theorem next_xy_level (s : BiCfg) (hx : 1 ≤ s.x) :
    BiCfg.doubleLevel (PairComp.next s .xy) = BiCfg.doubleLevel s := by
  unfold BiCfg.doubleLevel PairComp.next; simp only; omega

/-- The inert compositions leave `doubleLevel` unchanged. -/
theorem next_inert_level (s : BiCfg) :
    BiCfg.doubleLevel (PairComp.next s .xx) = BiCfg.doubleLevel s
      ∧ BiCfg.doubleLevel (PairComp.next s .yy) = BiCfg.doubleLevel s
      ∧ BiCfg.doubleLevel (PairComp.next s .bb) = BiCfg.doubleLevel s :=
  ⟨rfl, rfl, rfl⟩

/-! ## Invariant preservation

Each reaction keeps the total molecule count `x + y + b = n` fixed (given that
the reacting molecules are present). -/

theorem next_xy_inv {n : ℕ} {s : BiCfg} (h : BiCfg.DoubleInv n s) (hx : 1 ≤ s.x) (hy : 1 ≤ s.y) :
    BiCfg.DoubleInv n (PairComp.next s .xy) := by
  unfold BiCfg.DoubleInv PairComp.next at *; simp only; omega

theorem next_xb_inv {n : ℕ} {s : BiCfg} (h : BiCfg.DoubleInv n s) (hb : 1 ≤ s.b) :
    BiCfg.DoubleInv n (PairComp.next s .xb) := by
  unfold BiCfg.DoubleInv PairComp.next at *; simp only; omega

theorem next_yb_inv {n : ℕ} {s : BiCfg} (h : BiCfg.DoubleInv n s) (hb : 1 ≤ s.b) :
    BiCfg.DoubleInv n (PairComp.next s .yb) := by
  unfold BiCfg.DoubleInv PairComp.next at *; simp only; omega

/-! ## Resolution masses

At an interior state with all three species present, the probabilities of the
two level-changing (resolution) reactions are `x·b / C(n,2)` for the up-step and
`y·b / C(n,2)` for the down-step.  The blank factor `b` is common, so the
**up:down odds are `x : y`** — exactly the productive bias of the tri-molecular
walk.  This is the quantitative input to the Theorem-2 domination argument. -/

/-- **Resolution-up mass.**  `X + B → 2X` fires with probability `x·b / C(n,2)`. -/
theorem doubleBStep_up (x y b : ℕ) (h : 2 ≤ (x + 1) + (y + 1) + (b + 1)) :
    doubleBStep ⟨x + 1, y + 1, b + 1⟩ (by simpa using h) ⟨x + 2, y + 1, b⟩
      = ((x + 1) * (b + 1) : ℝ≥0∞) / (Nat.choose ((x + 1) + (y + 1) + (b + 1)) 2 : ℝ≥0∞) := by
  unfold doubleBStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
    {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  simp [PairComp.next, PairComp.weight, dbPairPMF, BiCfg.mk.injEq]

/-- **Resolution-down mass.**  `Y + B → 2Y` fires with probability `y·b / C(n,2)`. -/
theorem doubleBStep_down (x y b : ℕ) (h : 2 ≤ (x + 1) + (y + 1) + (b + 1)) :
    doubleBStep ⟨x + 1, y + 1, b + 1⟩ (by simpa using h) ⟨x + 1, y + 2, b⟩
      = ((y + 1) * (b + 1) : ℝ≥0∞) / (Nat.choose ((x + 1) + (y + 1) + (b + 1)) 2 : ℝ≥0∞) := by
  unfold doubleBStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset PairComp) =
    {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  simp [PairComp.next, PairComp.weight, dbPairPMF, BiCfg.mk.injEq]

/-- **Odds domination (core of STEP 3).**  In the `X`-majority regime the
Double-B resolution up-fraction `x/(x+y)` is at least the tri-molecular
productive up-fraction at effective population `2n`, level `2x+b`.  Writing
`b = c+1`, the comparison is `(2x+c)(x+y) ≤ x(2x+2y+2c)`, i.e. `(x-y)·c ≥ 0`. -/
theorem doubleB_odds_dominate (x y c : ℕ) (hxy : y ≤ x) :
    (2 * x + c) * (x + y) ≤ x * (2 * x + 2 * y + 2 * c) := by
  nlinarith [Nat.mul_le_mul_left c hxy, Nat.zero_le c]

end Tri
