/-
Ripple.BoundedUniversality.GPAC.Impossibility
-------------------------
The robustness dichotomy, impossibility side (oracle T1/T2, 2026-06-11).

* `hasDecider_of_factors_through_finite` + `verdict_factors_cells` +
  `no_uniform_robust_encoding` — **T1, the finite-advice theorem**:
  ANY verdict map `V : ℝ^d → Bool` that is constant on the ε-ball of
  each encoded input — with a bounded computable rational encoder —
  factors through finitely many floor-cells, hence the decided
  predicate has a computable Bool decider.  NO hypothesis on the
  dynamics is used: this kills every fixed-dimensional bounded
  uniformly-robust simulation of an undecidable predicate (polynomial
  ODE or otherwise) at the metric + computability level, before the
  vector field is even chosen.  It is the fully general form of
  `no_robust_increment_freeze`.

* `packing_finite` — **T2, the packing theorem**: a uniformly
  `2ε`-separated bounded family in `(ℝ^d, ℓ∞)` is finite.  Faithful
  robust tracking forces uniform separation of the encoded
  configurations, so unbounded-space computation cannot be faithfully
  robustly encoded in a fixed compact box.

Together with the positive main theorem (non-robust configuration-local
encoder), these make the encoder-robustness dichotomy a theorem in both
directions: the main construction's non-robustness is NECESSARY.
-/

import Ripple.BoundedUniversality.Core.DiscreteSource

namespace Ripple.BoundedUniversality.GPAC.Impossibility

open Ripple.BoundedUniversality.Core

/-! ## Floor-cell arithmetic -/

/-- Two points in the same `ε`-floor-cell are within `ε`.  Stated over any
linear ordered field with a floor (used at `ℚ` for T1 and `ℝ` for T2). -/
theorem abs_sub_lt_of_floor_div_eq {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K]
    {ε a b : K} (hε : 0 < ε) (h : ⌊a / ε⌋ = ⌊b / ε⌋) : |a - b| < ε := by
  have h1 : (⌊a / ε⌋ : K) ≤ a / ε := Int.floor_le _
  have h2 : a / ε < ⌊a / ε⌋ + 1 := Int.lt_floor_add_one _
  have h3 : (⌊b / ε⌋ : K) ≤ b / ε := Int.floor_le _
  have h4 : b / ε < ⌊b / ε⌋ + 1 := Int.lt_floor_add_one _
  rw [h] at h1 h2
  have hdiff : |a / ε - b / ε| < 1 := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hrw : a / ε - b / ε = (a - b) / ε := by ring
  rw [hrw, abs_div, abs_of_pos hε, div_lt_one hε] at hdiff
  exact hdiff

/-! ## T1: the finite-advice mechanism -/

/-- **Finite-advice mechanism.**  A predicate that factors through a
finite primcodable type via a computable map has a computable Bool
decider: the factor table is a finite object, hence computable
(`Primrec.dom_finite`), and the composite decides the predicate. -/
theorem hasDecider_of_factors_through_finite
    {F : Type*} [Primcodable F] [Finite F]
    (P : ℕ → Prop) (p : ℕ → F) (hp : Computable p)
    (hfac : ∀ a b, p a = p b → (P a ↔ P b)) :
    HasComputableBoolDecider P := by
  classical
  refine ⟨fun a => decide (∃ b, p b = p a ∧ P b), ?_, ?_⟩
  · exact ((Primrec.dom_finite
      (fun v : F => decide (∃ b, p b = v ∧ P b))).to_comp).comp hp
  · intro n
    constructor
    · intro h
      obtain ⟨b, hb, hPb⟩ := of_decide_eq_true h
      exact (hfac b n hb).mp hPb
    · intro h
      exact decide_eq_true ⟨n, rfl, h⟩

/-- **Robust-verdict factoring (pure mathematics, no computability).**
If a verdict map `V : ℝ^d → Bool` is constant (= `P w`) on the closed
`ε`-ball of every encoded input `x₀ w`, then `P` factors through the
`ε`-floor-cells of the encoder: two inputs in the same cell have
encodings within `ε`, so the midpoint lies in both balls and `V` at the
midpoint decides both. -/
theorem verdict_factors_cells (d : ℕ) (ε : ℚ) (hε : 0 < ε)
    (x₀ : ℕ → Fin d → ℚ) (P : ℕ → Prop) (V : (Fin d → ℝ) → Bool)
    (hrob : ∀ w (z : Fin d → ℝ),
        (∀ i, |z i - (x₀ w i : ℝ)| ≤ (ε : ℝ)) → (V z = true ↔ P w)) :
    ∀ a b, (∀ i, ⌊x₀ a i / ε⌋ = ⌊x₀ b i / ε⌋) → (P a ↔ P b) := by
  intro a b hcell
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  set z : Fin d → ℝ := fun i => ((x₀ a i : ℝ) + (x₀ b i : ℝ)) / 2 with hz
  have key : ∀ i, |(x₀ a i : ℝ) - (x₀ b i : ℝ)| < (ε : ℝ) := by
    intro i
    have hq : |x₀ a i - x₀ b i| < ε := abs_sub_lt_of_floor_div_eq hε (hcell i)
    exact_mod_cast hq
  have hza : ∀ i, |z i - (x₀ a i : ℝ)| ≤ (ε : ℝ) := by
    intro i
    have h1 : z i - (x₀ a i : ℝ) = ((x₀ b i : ℝ) - (x₀ a i : ℝ)) / 2 := by
      rw [hz]; ring
    rw [h1, abs_div, abs_two, abs_sub_comm]
    linarith [key i]
  have hzb : ∀ i, |z i - (x₀ b i : ℝ)| ≤ (ε : ℝ) := by
    intro i
    have h1 : z i - (x₀ b i : ℝ) = ((x₀ a i : ℝ) - (x₀ b i : ℝ)) / 2 := by
      rw [hz]; ring
    rw [h1, abs_div, abs_two]
    linarith [key i]
  rw [← hrob a z hza, hrob b z hzb]

/-- **T1 (impossibility of uniformly robust bounded encoding).**
There is no computable-cell rational encoder `x₀ : ℕ → ℚ^d`, uniform
radius `ε > 0`, and verdict map `V : ℝ^d → Bool` — V arbitrary, no
dynamics assumed — such that `V` decides `sourceHalts w` on the entire
closed `ε`-ball of every encoded input.

`cell` is any computable map into a finite type refining the
`ε`-floor-cells of the encoder; for a concrete encoder bounded by `B`
one takes `F = Fin d → Icc ⌊-B/ε⌋ ⌊B/ε⌋` and `cell = the floor map`,
which is computable for every explicitly-given rational encoder.  The
conclusion `False` is the strong form: uniform robustness + bounded
encoding + computability of the cell map are jointly inconsistent with
undecidability — independent of dimension, degree, coefficient field,
readout shape, or simulation time. -/
theorem no_uniform_robust_encoding
    {F : Type*} [Primcodable F] [Finite F]
    (d : ℕ) (ε : ℚ) (hε : 0 < ε)
    (x₀ : ℕ → Fin d → ℚ)
    (cell : ℕ → F) (hcell : Computable cell)
    (href : ∀ a b, cell a = cell b → ∀ i, ⌊x₀ a i / ε⌋ = ⌊x₀ b i / ε⌋)
    (V : (Fin d → ℝ) → Bool)
    (hrob : ∀ w (z : Fin d → ℝ),
        (∀ i, |z i - (x₀ w i : ℝ)| ≤ (ε : ℝ)) → (V z = true ↔ sourceHalts w)) :
    False :=
  sourceHalts_noBoolDecider <|
    hasDecider_of_factors_through_finite sourceHalts cell hcell
      (fun a b h =>
        verdict_factors_cells d ε hε x₀ sourceHalts V hrob a b (href a b h))

/-! ## T2: the packing theorem -/

/-- **T2 (packing).**  A family of points in `ℝ^d`, bounded by `B` in
every coordinate and pairwise `2ε`-separated in sup norm, is finite.
Hence a faithful robust simulation — which must keep the encodings of
distinct reachable configurations `2ε`-separated for decoding to be
well-defined — can host only finitely many configurations in a fixed
compact box: space-bounded computation only. -/
theorem packing_finite {ι : Type*} {d : ℕ} (B ε : ℝ) (hε : 0 < ε)
    (E : ι → Fin d → ℝ) (hbd : ∀ c i, |E c i| ≤ B)
    (hsep : Pairwise fun c c' => ∃ i, 2 * ε ≤ |E c i - E c' i|) :
    Finite ι := by
  classical
  have h2ε : (0 : ℝ) < 2 * ε := by linarith
  set m : ℤ := ⌈B / (2 * ε)⌉ + 1 with hm
  have hmem : ∀ c i, ⌊E c i / (2 * ε)⌋ ∈ Finset.Icc (-m) m := by
    intro c i
    have habs := abs_le.mp (hbd c i)
    have hub : E c i / (2 * ε) ≤ B / (2 * ε) := by
      gcongr
      exact habs.2
    have hlb : -(B / (2 * ε)) ≤ E c i / (2 * ε) := by
      rw [← neg_div]
      gcongr
      exact habs.1
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      push_cast [hm]
      have hceil : B / (2 * ε) ≤ (⌈B / (2 * ε)⌉ : ℝ) := Int.le_ceil _
      linarith
    · have h1 : (⌊E c i / (2 * ε)⌋ : ℝ) ≤ B / (2 * ε) :=
        le_trans (Int.floor_le _) hub
      have h2 : (B / (2 * ε)) ≤ (⌈B / (2 * ε)⌉ : ℝ) := Int.le_ceil _
      have : (⌊E c i / (2 * ε)⌋ : ℝ) ≤ ((m : ℤ) : ℝ) := by
        push_cast [hm]; linarith
      exact_mod_cast this
  set g : ι → (Fin d → ↥(Finset.Icc (-m) m)) :=
    fun c i => ⟨⌊E c i / (2 * ε)⌋, hmem c i⟩ with hg
  have hinj : Function.Injective g := by
    intro c c' hgcc
    by_contra hne
    obtain ⟨i, hi⟩ := hsep hne
    have hfl : ⌊E c i / (2 * ε)⌋ = ⌊E c' i / (2 * ε)⌋ := by
      have := congrFun hgcc i
      exact Subtype.ext_iff.mp this
    have := abs_sub_lt_of_floor_div_eq h2ε hfl
    linarith
  exact Finite.of_injective g hinj

end Ripple.BoundedUniversality.GPAC.Impossibility
