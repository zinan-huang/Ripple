import Ripple.Kurtz.StrongApprox.PaperSectionFourHypotheses
import Ripple.Kurtz.StrongApprox.TransferredKurtzPaths

/-!
# Borel rates without an extra off-lattice hypothesis

A bounded jump process started at a deterministic point visits a countable
set. Preserve the specified rates there and use the continuous limiting rate
elsewhere. The construction does not require the original rate to be Borel
on the entire Euclidean space.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Ripple.Kurtz.StrongApprox
open PaperSectionFourHypotheses

variable {m d : ℕ}

/-- The countable set containing every state of a finite-channel jump path. -/
def jumpReachableSet (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ) (N : ℕ) :
    Set (Fin d → ℝ) :=
  Set.range (fun n : Fin m → ℕ => x0 + ∑ l, ((n l : ℝ) / (N : ℝ)) • v l)

theorem jumpReachableSet_countable (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ) (N : ℕ) :
    (jumpReachableSet v x0 N).Countable := Set.countable_range _

/-- Extend arbitrary rates off the countable reachable set by the limiting rate. -/
def countableRateExtension (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ) (N : ℕ)
    (f g : Fin m → (Fin d → ℝ) → ℝ) (l : Fin m) (x : Fin d → ℝ) : ℝ := by
  classical
  exact if x ∈ jumpReachableSet v x0 N then g l x else f l x

theorem measurable_countableRateExtension (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ)
    (N : ℕ) (f g : Fin m → (Fin d → ℝ) → ℝ) (hf : ∀ l, Measurable (f l)) (l : Fin m) :
    Measurable (countableRateExtension v x0 N f g l) := by
  classical
  intro s hs
  have heq : (countableRateExtension v x0 N f g l) ⁻¹' s =
      (jumpReachableSet v x0 N ∩ (g l) ⁻¹' s) ∪
      ((jumpReachableSet v x0 N)ᶜ ∩ (f l) ⁻¹' s) := by
    ext x
    by_cases hx : x ∈ jumpReachableSet v x0 N <;>
      simp [countableRateExtension, hx]
  rw [heq]
  exact ((jumpReachableSet_countable v x0 N).mono Set.inter_subset_left).measurableSet.union
    ((jumpReachableSet_countable v x0 N).measurableSet.compl.inter (hf l hs))

theorem countableRateExtension_bounds (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ) (N : ℕ)
    {f g : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
    (hfzero : ∀ l x, 0 ≤ f l x) (hgb : ∀ l x, g l x ≤ eps l)
    (hgzero : ∀ l x, 0 ≤ g l x) (hfb : ∀ l x, f l x ≤ eps l) :
    (∀ l x, 0 ≤ countableRateExtension v x0 N f g l x) ∧
    (∀ l x, countableRateExtension v x0 N f g l x ≤ eps l) := by
  constructor <;> intro l x <;> unfold countableRateExtension <;>
    split_ifs <;> first | exact hfzero l x | exact hgzero l x | exact hgb l x | exact hfb l x

theorem countableRateExtension_error (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ) (N : ℕ)
    {f g : Fin m → (Fin d → ℝ) → ℝ} {C : Fin m → ℝ}
    (hC : ∀ l, 0 ≤ C l) (hfg : ∀ l x, |f l x - g l x| ≤ C l) :
    ∀ l x, |f l x - countableRateExtension v x0 N f g l x| ≤ C l := by
  intro l x
  unfold countableRateExtension
  split_ifs
  · exact hfg l x
  · simpa using hC l

theorem countableRateExtension_eq (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ) (N : ℕ)
    (f g : Fin m → (Fin d → ℝ) → ℝ) {x : Fin d → ℝ}
    (hx : x ∈ jumpReachableSet v x0 N) (l : Fin m) :
    countableRateExtension v x0 N f g l x = g l x := by
  simp [countableRateExtension, hx]

namespace KMTTransfer

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The time-change equation itself puts the constructed chain in the
countable reachable set; no regularity of the original rates is used. -/
theorem transferredChain_mem_jumpReachableSet {N : ℕ} (hN : 0 < N)
    (v : Fin m → Fin d → ℝ) {rate : Fin m → (Fin d → ℝ) → ℝ} {b : Fin m → ℝ}
    (hzero : ∀ l x, 0 ≤ rate l x) (hb : ∀ l x, rate l x ≤ b l)
    (hm : ∀ l, Measurable (rate l)) (x0 : Fin d → ℝ)
    (z : Ω × (ℕ × Fin m → KMTPoissonCode)) {t : ℝ} (ht : 0 ≤ t) :
    transferredChain hN v hzero hb hm x0 z t ∈ jumpReachableSet v x0 N := by
  let X := transferredChain hN v hzero hb hm x0 z
  refine ⟨fun l => cellPath (scaledTcClock (N : ℝ) rate X l t) (z.2 (N, l)), ?_⟩
  exact (transferredChain_equation hN v hzero hb hm x0 z t ⟨ht, le_rfl⟩).symm

/-- The chain made with the Borel extension solves (1.4) with the original
rates. Masking zero directions disappears from the vector equation. -/
theorem transferredChain_countableRateExtension_equation {N : ℕ} (hN : 0 < N)
    (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ)
    (f g : Fin m → (Fin d → ℝ) → ℝ) {eps : Fin m → ℝ}
    (hzero : ∀ l x, 0 ≤ countableRateExtension v x0 N f (maskZeroRate v g) l x)
    (hb : ∀ l x, countableRateExtension v x0 N f (maskZeroRate v g) l x ≤ eps l)
    (hm : ∀ l, Measurable (countableRateExtension v x0 N f (maskZeroRate v g) l))
    (z : Ω × (ℕ × Fin m → KMTPoissonCode)) {t : ℝ} (ht : 0 ≤ t) :
    let X := transferredChain hN v hzero hb hm x0 z
    X t = x0 + ∑ l, (transferredCellPath N l
      (scaledTcClock (N : ℝ) g X l t) z / (N : ℝ)) • v l := by
  dsimp only
  rw [transferredChain_equation hN v hzero hb hm x0 z t ⟨ht, le_rfl⟩]
  congr 1
  apply sum_smul_congr_of_nonzero
  intro l hl
  have hclock :
      scaledTcClock (N : ℝ) (countableRateExtension v x0 N f (maskZeroRate v g))
        (transferredChain hN v hzero hb hm x0 z) l t =
      scaledTcClock (N : ℝ) g (transferredChain hN v hzero hb hm x0 z) l t := by
    unfold scaledTcClock clock
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    beta_reduce
    rw [countableRateExtension_eq v x0 N f (maskZeroRate v g)
      (transferredChain_mem_jumpReachableSet hN v hzero hb hm x0 z hs.1) l]
    simp [maskZeroRate, hl]
  rw [hclock]

end KMTTransfer
end Ripple.Kurtz.StrongApprox
