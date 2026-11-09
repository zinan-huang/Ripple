/-
  Ripple.LPP.CF24Example — Worked Example: PP → NAP via λ-Trick and Cubing

  Reference: `ref/pp_to_nap_v5 (1).pdf` (Population Protocols to
  Non-Autocatalytic Protocols via the Cubing Construction, Huang 2026).

  Goal: Formalize the full PP → NAP pipeline on the concrete CF'24 example.
  The original PP computes (3 - √5)/6 ≈ 0.1273 (via z_11 + z_01/2 readout).

  Pipeline stages:
    Step 0: Original 3-variable PP on simplex z_00 + z_01 + z_11 = 1
    Step 1: λ-trick (λ = 1/2): introduce r = 1 - u - z_01 - z_11 on 4-simplex
    Step 2: r²-trick: multiply every RHS by r², yielding a 4-PP
    Step 3: Cubing: 20 lifted variables v_α = C(3,α) · r^α_r · u^α_u · z_01^α_01 · z_11^α_11
    Step 4: NAP rewriting via explicit flow network
    Step 5: Readout z_11 + z_01/2 = (1/3) Σ c_i v_i → (3 - √5)/6

  This serves as the concrete instance validating the general PP → NAP
  theory before the abstract generalization. -/

import Ripple.LPP.Defs
import Ripple.Core.GronwallCofinal
import Ripple.Core.ODEGlobal
import Ripple.Core.ZeroInitPositivity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Ripple
namespace CF24

open scoped Topology

/-! ## Step 0: Original 3-variable PP

The CF'24 population protocol on the simplex z_00 + z_01 + z_11 = 1 is the
×16 integer form (see paper §4):

  ż_00 = -2z_00² + 7z_00z_01 - 2z_00z_11                       (eq. 1)
  ż_01 =  2z_00² - 8z_00z_01 + 16z_00z_11 - z_01z_11           (eq. 2)
  ż_11 =  z_00z_01 - 14z_00z_11 + z_01z_11                     (eq. 3)

With readout z_11 + z_01/2 → (3 - √5)/6 ≈ 0.1273 as t → ∞. -/

/-- CF'24 field on 3 variables (z_00, z_01, z_11). Indexed as:
  0 ↦ z_00,  1 ↦ z_01,  2 ↦ z_11. -/
noncomputable def field : (Fin 3 → ℝ) → Fin 3 → ℝ :=
  fun x i => match i with
  | ⟨0, _⟩ => -2 * x 0 * x 0 + 7 * x 0 * x 1 - 2 * x 0 * x 2
  | ⟨1, _⟩ => 2 * x 0 * x 0 - 8 * x 0 * x 1 + 16 * x 0 * x 2 - x 1 * x 2
  | ⟨2, _⟩ => x 0 * x 1 - 14 * x 0 * x 2 + x 1 * x 2

/-- CF'24 is conservative: ż_00 + ż_01 + ż_11 = 0 as a formal polynomial identity. -/
theorem field_conservative : IsConservative field := by
  intro x
  simp only [field, Fin.sum_univ_three]
  ring

/-! ## Step 1: λ-trick (λ = 1/2)

Introduce u := λ · z_00 = z_00/2 and r := 1 - u - z_01 - z_11 = z_00/2.
After reparametrization, the 4-variable system on r + u + z_01 + z_11 = 1 is
(paper v5 §5):

  u̇    = -4u² + 7u z_01 - 2u z_11                              (eq. 4)
  ż_01 =  8u² - 16u z_01 + 32u z_11 - z_01 z_11                (eq. 5)
  ż_11 =  2u z_01 - 28u z_11 + z_01 z_11                       (eq. 6)
  ṙ    = -4u² + 7u z_01 - 2u z_11                              (eq. 7)

Note: for λ = 1/2, ṙ = u̇ (see Remark 2.1 in v5). -/

/-- Indexed variables for the λ-trick system:
  0 ↦ r (slack),  1 ↦ u,  2 ↦ z_01,  3 ↦ z_11. -/
noncomputable def lambdaField : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  fun x i => match i with
  | ⟨0, _⟩ => -4 * x 1 * x 1 + 7 * x 1 * x 2 - 2 * x 1 * x 3              -- ṙ
  | ⟨1, _⟩ => -4 * x 1 * x 1 + 7 * x 1 * x 2 - 2 * x 1 * x 3              -- u̇
  | ⟨2, _⟩ =>  8 * x 1 * x 1 - 16 * x 1 * x 2 + 32 * x 1 * x 3 - x 2 * x 3  -- ż_01
  | ⟨3, _⟩ =>  2 * x 1 * x 2 - 28 * x 1 * x 3 + x 2 * x 3                  -- ż_11

/-- λ-trick system is conservative on the 4-simplex. -/
theorem lambdaField_conservative : IsConservative lambdaField := by
  intro x
  simp only [lambdaField, Fin.sum_univ_four]
  ring

/-! ### λ-trick embedding from the CF'24 3-PP

For `λ = 1/2`, the λ-trick adds a slack `r` with `r = u = (z_00)/2`.
On the embedded subset `r = u`, the four-variable RHS reduces to the
original three-variable CF'24 RHS componentwise:

  ṙ = u̇ = (ż_00)/2,   ż_01 = (z_01)·(unchanged eq.),  ż_11 = unchanged.

The embedding therefore lifts every CF'24 trajectory to a λ-trick
trajectory with the *same* readout `z_11 + z_01/2`. -/

/-- Lift `(z_00, z_01, z_11)` ↦ `(z_00/2, z_00/2, z_01, z_11)` on the
λ-trick variables `(r, u, z_01, z_11)`. -/
noncomputable def cf24LambdaEmbed (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  fun i => match i with
  | ⟨0, _⟩ => x 0 / 2
  | ⟨1, _⟩ => x 0 / 2
  | ⟨2, _⟩ => x 1
  | ⟨3, _⟩ => x 2

/-- The Jacobian of `cf24LambdaEmbed` applied to a velocity vector,
producing the velocity in the λ-trick coordinates. -/
noncomputable def cf24LambdaEmbedVel (v : Fin 3 → ℝ) : Fin 4 → ℝ :=
  fun i => match i with
  | ⟨0, _⟩ => v 0 / 2
  | ⟨1, _⟩ => v 0 / 2
  | ⟨2, _⟩ => v 1
  | ⟨3, _⟩ => v 2

/-- **λ-trick faithfulness on the embedded subset.**  Evaluating the
λ-trick field at the lifted state gives the lifted CF'24 velocity:
componentwise, `ṙ = u̇ = ż_00/2`, `ż_01 = ż_01`, `ż_11 = ż_11`. -/
theorem lambdaField_eq_cf24Embed (x : Fin 3 → ℝ) :
    lambdaField (cf24LambdaEmbed x) = cf24LambdaEmbedVel (field x) := by
  funext i
  fin_cases i <;>
    simp only [lambdaField, cf24LambdaEmbed, cf24LambdaEmbedVel, field] <;> ring

/-- The λ-trick simplex sum `r + u + z_01 + z_11` after embedding equals
the original CF'24 simplex sum `z_00 + z_01 + z_11`. -/
theorem cf24LambdaEmbed_sum (x : Fin 3 → ℝ) :
    ∑ i, cf24LambdaEmbed x i = x 0 + x 1 + x 2 := by
  simp only [cf24LambdaEmbed, Fin.sum_univ_four]; ring

/-- The λ-trick readout `z_11 + z_01/2` equals the original CF'24 readout
under the embedding. -/
theorem cf24LambdaEmbed_readout (x : Fin 3 → ℝ) :
    cf24LambdaEmbed x 3 + cf24LambdaEmbed x 2 / 2
      = x 2 + x 1 / 2 := by
  simp only [cf24LambdaEmbed]

/-- **HasDerivAt transport.**  If `y` is a CF'24 trajectory at time `t`,
then the lifted trajectory `cf24LambdaEmbed ∘ y` is a λ-trick trajectory
at the same time. -/
theorem cf24LambdaEmbed_hasDerivAt
    {y : ℝ → Fin 3 → ℝ} {t : ℝ}
    (hy : HasDerivAt y (field (y t)) t) :
    HasDerivAt (fun s => cf24LambdaEmbed (y s))
      (lambdaField (cf24LambdaEmbed (y t))) t := by
  have h0 : HasDerivAt (fun s => y s 0) (field (y t) 0) t := hasDerivAt_pi.mp hy 0
  have h1 : HasDerivAt (fun s => y s 1) (field (y t) 1) t := hasDerivAt_pi.mp hy 1
  have h2 : HasDerivAt (fun s => y s 2) (field (y t) 2) t := hasDerivAt_pi.mp hy 2
  rw [lambdaField_eq_cf24Embed]
  refine hasDerivAt_pi.mpr ?_
  intro i
  fin_cases i
  · -- coord 0: (y 0)/2
    have : HasDerivAt (fun s => y s 0 / 2) (field (y t) 0 / 2) t := h0.div_const 2
    simpa [cf24LambdaEmbed, cf24LambdaEmbedVel] using this
  · -- coord 1: (y 0)/2
    have : HasDerivAt (fun s => y s 0 / 2) (field (y t) 0 / 2) t := h0.div_const 2
    simpa [cf24LambdaEmbed, cf24LambdaEmbedVel] using this
  · -- coord 2: y 1
    simpa [cf24LambdaEmbed, cf24LambdaEmbedVel] using h1
  · -- coord 3: y 2
    simpa [cf24LambdaEmbed, cf24LambdaEmbedVel] using h2

/-- **λ-trick readout-limit preservation.**  If a CF'24 trajectory has
readout `z_11 + z_01/2 → L`, the lifted λ-trick trajectory has readout
`z_11 + z_01/2 → L` as well — they are the *same* function of time. -/
theorem cf24Lambda_readout_tendsto
    {y : ℝ → Fin 3 → ℝ} {L : ℝ}
    (h : Filter.Tendsto (fun t => y t 2 + y t 1 / 2) Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun t => cf24LambdaEmbed (y t) 3 + cf24LambdaEmbed (y t) 2 / 2)
      Filter.atTop (nhds L) := by
  have heq : (fun t => cf24LambdaEmbed (y t) 3 + cf24LambdaEmbed (y t) 2 / 2)
           = (fun t => y t 2 + y t 1 / 2) := by
    funext t; exact cf24LambdaEmbed_readout (y t)
  rw [heq]; exact h

/-! ## Step 2: r²-Trick

Multiply every RHS of the λ-trick system by r² = (x 0)². This produces a
degree-4 system (4-PP), still on the simplex r + u + z_01 + z_11 = 1.

The 4-PP condition (no positive x_j^4 term in ẋ_j⁺) holds by inspection
— see paper §6 verification table. -/

/-- r²-trick applied to the λ-trick system. -/
noncomputable def r2Field : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  fun x i => (x 0) * (x 0) * lambdaField x i

/-- r²-trick system is conservative. -/
theorem r2Field_conservative : IsConservative r2Field := by
  intro x
  simp only [r2Field]
  rw [← Finset.mul_sum]
  rw [lambdaField_conservative x]
  ring

/-! ## Step 3: The 20 Cubed Variables

For multi-index α = (α_r, α_u, α_01, α_11) ∈ ℕ⁴ with |α| = 3, define
  v_α := C(3, α) · r^α_r · u^α_u · z_01^α_01 · z_11^α_11

There are C(6, 3) = 20 such multi-indices. The paper §7 (v5) and §5.3 (v3)
indexes them as v_1, ..., v_20 in a specific order. We follow that order:

  v_1 = r³,  v_2 = 3r²u,  v_3 = 3r²z_01,  v_4 = 3r²z_11,  v_5 = 3ru²,
  v_6 = 6ruz_01,  v_7 = 6ruz_11,  v_8 = 3rz_01²,  v_9 = 6rz_01z_11,  v_10 = 3rz_11²,
  v_11 = u³,  v_12 = 3u²z_01,  v_13 = 3u²z_11,  v_14 = 3uz_01²,  v_15 = 6uz_01z_11,
  v_16 = 3uz_11²,  v_17 = z_01³,  v_18 = 3z_01²z_11,  v_19 = 3z_01z_11²,  v_20 = z_11³.

The multinomial theorem gives ∑ v_i = (r + u + z_01 + z_11)³ = 1. -/

/-- Multi-index for cubed variable v_i. Returns (α_r, α_u, α_01, α_11).
  Order: v_1 = r³, v_2 = 3r²u, v_3 = 3r²z_01, v_4 = 3r²z_11, v_5 = 3ru²,
  v_6 = 6ruz_01, v_7 = 6ruz_11, v_8 = 3rz_01², v_9 = 6rz_01z_11, v_10 = 3rz_11²,
  v_11 = u³, v_12 = 3u²z_01, v_13 = 3u²z_11, v_14 = 3uz_01², v_15 = 6uz_01z_11,
  v_16 = 3uz_11², v_17 = z_01³, v_18 = 3z_01²z_11, v_19 = 3z_01z_11², v_20 = z_11³. -/
def cubedIndex : Fin 20 → (Fin 4 → ℕ) :=
  ![![3,0,0,0], ![2,1,0,0], ![2,0,1,0], ![2,0,0,1], ![1,2,0,0],
    ![1,1,1,0], ![1,1,0,1], ![1,0,2,0], ![1,0,1,1], ![1,0,0,2],
    ![0,3,0,0], ![0,2,1,0], ![0,2,0,1], ![0,1,2,0], ![0,1,1,1],
    ![0,1,0,2], ![0,0,3,0], ![0,0,2,1], ![0,0,1,2], ![0,0,0,3]]

/-- Multinomial coefficient for cubed variable v_i.
  The factor `3! / (α_r! α_u! α_01! α_11!)` ensures ∑ v_i = 1. -/
def cubedMultinomial : Fin 20 → ℕ :=
  ![1, 3, 3, 3, 3, 6, 6, 3, 6, 3, 1, 3, 3, 3, 6, 3, 1, 3, 3, 1]

/-- Lift: v_i as a function of the 4-variable state.

  Concrete expansion for tractable chain-rule proofs. The abstract form
  `(cubedMultinomial i : ℝ) * ∏ k, (x k) ^ (cubedIndex i k)` is equivalent,
  established by `cubedLift_eq_abs` below. -/
noncomputable def cubedLift (i : Fin 20) (x : Fin 4 → ℝ) : ℝ :=
  (![x 0 ^ 3,                      -- v_1  = r³
     3 * x 0 ^ 2 * x 1,             -- v_2  = 3r²u
     3 * x 0 ^ 2 * x 2,             -- v_3  = 3r²z_01
     3 * x 0 ^ 2 * x 3,             -- v_4  = 3r²z_11
     3 * x 0 * x 1 ^ 2,             -- v_5  = 3ru²
     6 * x 0 * x 1 * x 2,           -- v_6  = 6ruz_01
     6 * x 0 * x 1 * x 3,           -- v_7  = 6ruz_11
     3 * x 0 * x 2 ^ 2,             -- v_8  = 3rz_01²
     6 * x 0 * x 2 * x 3,           -- v_9  = 6rz_01z_11
     3 * x 0 * x 3 ^ 2,             -- v_10 = 3rz_11²
     x 1 ^ 3,                       -- v_11 = u³
     3 * x 1 ^ 2 * x 2,             -- v_12 = 3u²z_01
     3 * x 1 ^ 2 * x 3,             -- v_13 = 3u²z_11
     3 * x 1 * x 2 ^ 2,             -- v_14 = 3uz_01²
     6 * x 1 * x 2 * x 3,           -- v_15 = 6uz_01z_11
     3 * x 1 * x 3 ^ 2,             -- v_16 = 3uz_11²
     x 2 ^ 3,                       -- v_17 = z_01³
     3 * x 2 ^ 2 * x 3,             -- v_18 = 3z_01²z_11
     3 * x 2 * x 3 ^ 2,             -- v_19 = 3z_01z_11²
     x 3 ^ 3] : Fin 20 → ℝ) i

/-! ## Step 4: NAP System on 20 Variables

Each v̇_i is the chain-rule derivative along the r²-trick field, rewritten
into NAP form — every positive monomial factors as v_β · v_γ with β ≠ α ∧
γ ≠ α. The explicit 20 equations are in paper §9.

We use 0-based indexing: paper v_k ↔ Lean `x (k-1)`. So `x 0` is v_1 = r³,
`x 1` is v_2 = 3r²u, ..., `x 19` is v_20 = z_11³. -/

/-- The 20-equation NAP system from paper §9 (transcribed).

Each row satisfies:
  * every positive term is a product `c · x i · x j` with `i ≠ α ∧ j ≠ α`
    (NAP condition — verified structurally via `napPositiveSplit` below);
  * every negative term has `x α` as a factor (automatic CRN-form loss).
-/
noncomputable def napField (x : Fin 20 → ℝ) : Fin 20 → ℝ := ![
  -- v_1 = r³  [paper §9 prints 7/2 — SymPy notebook ground-truth gives 7/3]
  (7/3) * x 2 * x 1 - 4 * x 0 * x 4 - x 0 * x 6,
  -- v_2 = 3r²u
  (7/2) * x 5 * x 0 + 14 * x 11 * x 0
    - (4/3) * x 1 * x 1 - (2/3) * x 1 * x 3 - (8/3) * x 1 * x 4 - (2/3) * x 1 * x 6,
  -- v_3 = 3r²z_01
  8 * x 4 * x 0 + 16 * x 6 * x 0 + 14 * x 13 * x 0
    - (16/3) * x 2 * x 1 - (1/3) * x 2 * x 3 - (8/3) * x 2 * x 4 - (2/3) * x 2 * x 6,
  -- v_4 = 3r²z_11
  x 5 * x 0 + (1/2) * x 8 * x 0 + 7 * x 14 * x 0
    - (28/3) * x 3 * x 1 - (8/3) * x 3 * x 4 - (2/3) * x 3 * x 6,
  -- v_5 = 3ru²  [paper §9 prints coeff 1/3 on x_4² — SymPy says 4/3]
  14 * x 11 * x 0 + (7/3) * x 11 * x 1
    - (8/3) * x 4 * x 1 - (4/3) * x 4 * x 3 - (4/3) * x 4 * x 4 - (1/3) * x 4 * x 6,
  -- v_6 = 6ruz_01
  48 * x 10 * x 0 + 64 * x 12 * x 0 + 14 * x 13 * x 0 + (14/3) * x 13 * x 1
    - (20/3) * x 5 * x 1 - x 5 * x 3 - (4/3) * x 5 * x 4 - (1/3) * x 5 * x 6,
  -- v_7 = 6ruz_11  [paper §9 prints coeff 1 on x_6·x_3 — SymPy says 2/3]
  4 * x 11 * x 0 + 8 * x 14 * x 0 + (7/3) * x 14 * x 1
    - (32/3) * x 6 * x 1 - (2/3) * x 6 * x 3 - (4/3) * x 6 * x 4 - (1/3) * x 6 * x 6,
  -- v_8 = 3rz_01²  [paper §9 prints 7·v_17·v_1 for third term — SymPy says v_17·v_2, i.e. x_16·x_1]
  16 * x 11 * x 0 + 32 * x 14 * x 0 + 7 * x 16 * x 1
    - (32/3) * x 7 * x 1 - (2/3) * x 7 * x 3 - (4/3) * x 7 * x 4 - (1/3) * x 7 * x 6,
  -- v_9 = 6rz_01z_11
  16 * x 12 * x 0 + 4 * x 13 * x 0 + 64 * x 15 * x 0 + 2 * x 17 * x 0 + (14/3) * x 17 * x 1
    - (44/3) * x 8 * x 1 - (1/3) * x 8 * x 3 - (4/3) * x 8 * x 4 - (1/3) * x 8 * x 6,
  -- v_10 = 3rz_11²
  2 * x 14 * x 0 + 2 * x 18 * x 0 + (7/3) * x 18 * x 1
    - (56/3) * x 9 * x 1 - (4/3) * x 9 * x 4 - (1/3) * x 9 * x 6,
  -- v_11 = u³
  (7/3) * x 11 * x 1 - 4 * x 10 * x 1 - 2 * x 10 * x 3,
  -- v_12 = 3u²z_01
  8 * x 10 * x 1 + (32/3) * x 12 * x 1 + (14/3) * x 13 * x 1
    - 8 * x 11 * x 1 - (5/3) * x 11 * x 3,
  -- v_13 = 3u²z_11
  (2/3) * x 11 * x 1 + (5/2) * x 14 * x 1
    - 12 * x 12 * x 1 - (4/3) * x 12 * x 3,
  -- v_14 = 3uz_01²
  (16/3) * x 11 * x 1 + (32/3) * x 14 * x 1 + 7 * x 16 * x 1
    - 12 * x 13 * x 1 - (4/3) * x 13 * x 3,
  -- v_15 = 6uz_01z_11
  (16/3) * x 12 * x 1 + (4/3) * x 13 * x 1 + (64/3) * x 15 * x 1 + (16/3) * x 17 * x 1
    - 16 * x 14 * x 1 - x 14 * x 3,
  -- v_16 = 3uz_11²
  (2/3) * x 14 * x 1 + 3 * x 18 * x 1
    - 20 * x 15 * x 1 - (2/3) * x 15 * x 3,
  -- v_17 = z_01³
  (8/3) * x 13 * x 1 + (32/3) * x 17 * x 1
    - 16 * x 16 * x 1 - x 16 * x 3,
  -- v_18 = 3z_01²z_11
  (8/3) * x 14 * x 1 + 2 * x 16 * x 1 + (64/3) * x 18 * x 1 + x 16 * x 3
    - 20 * x 17 * x 1 - (2/3) * x 17 * x 3,
  -- v_19 = 3z_01z_11²
  (8/3) * x 15 * x 1 + (4/3) * x 17 * x 1 + 32 * x 19 * x 1 + (2/3) * x 17 * x 3
    - 24 * x 18 * x 1 - (1/3) * x 18 * x 3,
  -- v_20 = z_11³
  (2/3) * x 18 * x 1 + (1/3) * x 18 * x 3
    - 28 * x 19 * x 1]

/-! ### Chain-rule faithfulness

The NAP system is faithful: when v_i is substituted by its cubedLift in
r²-trick variables (r, u, z_01, z_11), each napField coordinate equals the
chain-rule derivative of cubedLift along r2Field.

This is the key correctness theorem for Step 4. -/

/-- Chain-rule faithfulness for v_1..v_20. Each proof follows the same
  `change <explicit substitution> = <expanded polynomial>; ring` pattern.
  RHS is the chain-rule derivative expanded as a polynomial in (r,u,z_01,z_11).
  Generated from SymPy ground-truth computation in `ref/pp_to_nap_v5 (1).ipynb`. -/
theorem napField_chain_v1 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 0 = -12*(x 0)^4*(x 1)^2 + 21*(x 0)^4*(x 1)*(x 2) - 6*(x 0)^4*(x 1)*(x 3) := by
  change (7/3) * (3 * x 0 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 1) - 4 * (x 0 ^ 3) * (3 * x 0 * x 1 ^ 2) - (x 0 ^ 3) * (6 * x 0 * x 1 * x 3)
       = -12*(x 0)^4*(x 1)^2 + 21*(x 0)^4*(x 1)*(x 2) - 6*(x 0)^4*(x 1)*(x 3)
  ring

theorem napField_chain_v2 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 1 = -12*(x 0)^4*(x 1)^2 + 21*(x 0)^4*(x 1)*(x 2) - 6*(x 0)^4*(x 1)*(x 3) - 24*(x 0)^3*(x 1)^3 + 42*(x 0)^3*(x 1)^2*(x 2) - 12*(x 0)^3*(x 1)^2*(x 3) := by
  change (7/2) * (6 * x 0 * x 1 * x 2) * (x 0 ^ 3) + 14 * (3 * x 1 ^ 2 * x 2) * (x 0 ^ 3) - (4/3) * (3 * x 0 ^ 2 * x 1) * (3 * x 0 ^ 2 * x 1) - (2/3) * (3 * x 0 ^ 2 * x 1) * (3 * x 0 ^ 2 * x 3) - (8/3) * (3 * x 0 ^ 2 * x 1) * (3 * x 0 * x 1 ^ 2) - (2/3) * (3 * x 0 ^ 2 * x 1) * (6 * x 0 * x 1 * x 3)
       = -12*(x 0)^4*(x 1)^2 + 21*(x 0)^4*(x 1)*(x 2) - 6*(x 0)^4*(x 1)*(x 3) - 24*(x 0)^3*(x 1)^3 + 42*(x 0)^3*(x 1)^2*(x 2) - 12*(x 0)^3*(x 1)^2*(x 3)
  ring

theorem napField_chain_v3 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 2 = 24*(x 0)^4*(x 1)^2 - 48*(x 0)^4*(x 1)*(x 2) + 96*(x 0)^4*(x 1)*(x 3) - 3*(x 0)^4*(x 2)*(x 3) - 24*(x 0)^3*(x 1)^2*(x 2) + 42*(x 0)^3*(x 1)*(x 2)^2 - 12*(x 0)^3*(x 1)*(x 2)*(x 3) := by
  change 8 * (3 * x 0 * x 1 ^ 2) * (x 0 ^ 3) + 16 * (6 * x 0 * x 1 * x 3) * (x 0 ^ 3) + 14 * (3 * x 1 * x 2 ^ 2) * (x 0 ^ 3) - (16/3) * (3 * x 0 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 1) - (1/3) * (3 * x 0 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 3) - (8/3) * (3 * x 0 ^ 2 * x 2) * (3 * x 0 * x 1 ^ 2) - (2/3) * (3 * x 0 ^ 2 * x 2) * (6 * x 0 * x 1 * x 3)
       = 24*(x 0)^4*(x 1)^2 - 48*(x 0)^4*(x 1)*(x 2) + 96*(x 0)^4*(x 1)*(x 3) - 3*(x 0)^4*(x 2)*(x 3) - 24*(x 0)^3*(x 1)^2*(x 2) + 42*(x 0)^3*(x 1)*(x 2)^2 - 12*(x 0)^3*(x 1)*(x 2)*(x 3)
  ring

theorem napField_chain_v4 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 3 = 6*(x 0)^4*(x 1)*(x 2) - 84*(x 0)^4*(x 1)*(x 3) + 3*(x 0)^4*(x 2)*(x 3) - 24*(x 0)^3*(x 1)^2*(x 3) + 42*(x 0)^3*(x 1)*(x 2)*(x 3) - 12*(x 0)^3*(x 1)*(x 3)^2 := by
  change (6 * x 0 * x 1 * x 2) * (x 0 ^ 3) + (1/2) * (6 * x 0 * x 2 * x 3) * (x 0 ^ 3) + 7 * (6 * x 1 * x 2 * x 3) * (x 0 ^ 3) - (28/3) * (3 * x 0 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) - (8/3) * (3 * x 0 ^ 2 * x 3) * (3 * x 0 * x 1 ^ 2) - (2/3) * (3 * x 0 ^ 2 * x 3) * (6 * x 0 * x 1 * x 3)
       = 6*(x 0)^4*(x 1)*(x 2) - 84*(x 0)^4*(x 1)*(x 3) + 3*(x 0)^4*(x 2)*(x 3) - 24*(x 0)^3*(x 1)^2*(x 3) + 42*(x 0)^3*(x 1)*(x 2)*(x 3) - 12*(x 0)^3*(x 1)*(x 3)^2
  ring

theorem napField_chain_v5 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 4 = -24*(x 0)^3*(x 1)^3 + 42*(x 0)^3*(x 1)^2*(x 2) - 12*(x 0)^3*(x 1)^2*(x 3) - 12*(x 0)^2*(x 1)^4 + 21*(x 0)^2*(x 1)^3*(x 2) - 6*(x 0)^2*(x 1)^3*(x 3) := by
  change 14 * (3 * x 1 ^ 2 * x 2) * (x 0 ^ 3) + (7/3) * (3 * x 1 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 1) - (8/3) * (3 * x 0 * x 1 ^ 2) * (3 * x 0 ^ 2 * x 1) - (4/3) * (3 * x 0 * x 1 ^ 2) * (3 * x 0 ^ 2 * x 3) - (4/3) * (3 * x 0 * x 1 ^ 2) * (3 * x 0 * x 1 ^ 2) - (1/3) * (3 * x 0 * x 1 ^ 2) * (6 * x 0 * x 1 * x 3)
       = -24*(x 0)^3*(x 1)^3 + 42*(x 0)^3*(x 1)^2*(x 2) - 12*(x 0)^3*(x 1)^2*(x 3) - 12*(x 0)^2*(x 1)^4 + 21*(x 0)^2*(x 1)^3*(x 2) - 6*(x 0)^2*(x 1)^3*(x 3)
  ring

theorem napField_chain_v6 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 5 = 48*(x 0)^3*(x 1)^3 - 120*(x 0)^3*(x 1)^2*(x 2) + 192*(x 0)^3*(x 1)^2*(x 3) + 42*(x 0)^3*(x 1)*(x 2)^2 - 18*(x 0)^3*(x 1)*(x 2)*(x 3) - 24*(x 0)^2*(x 1)^3*(x 2) + 42*(x 0)^2*(x 1)^2*(x 2)^2 - 12*(x 0)^2*(x 1)^2*(x 2)*(x 3) := by
  change 48 * (x 1 ^ 3) * (x 0 ^ 3) + 64 * (3 * x 1 ^ 2 * x 3) * (x 0 ^ 3) + 14 * (3 * x 1 * x 2 ^ 2) * (x 0 ^ 3) + (14/3) * (3 * x 1 * x 2 ^ 2) * (3 * x 0 ^ 2 * x 1) - (20/3) * (6 * x 0 * x 1 * x 2) * (3 * x 0 ^ 2 * x 1) - (6 * x 0 * x 1 * x 2) * (3 * x 0 ^ 2 * x 3) - (4/3) * (6 * x 0 * x 1 * x 2) * (3 * x 0 * x 1 ^ 2) - (1/3) * (6 * x 0 * x 1 * x 2) * (6 * x 0 * x 1 * x 3)
       = 48*(x 0)^3*(x 1)^3 - 120*(x 0)^3*(x 1)^2*(x 2) + 192*(x 0)^3*(x 1)^2*(x 3) + 42*(x 0)^3*(x 1)*(x 2)^2 - 18*(x 0)^3*(x 1)*(x 2)*(x 3) - 24*(x 0)^2*(x 1)^3*(x 2) + 42*(x 0)^2*(x 1)^2*(x 2)^2 - 12*(x 0)^2*(x 1)^2*(x 2)*(x 3)
  ring

theorem napField_chain_v7 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 6 = 12*(x 0)^3*(x 1)^2*(x 2) - 192*(x 0)^3*(x 1)^2*(x 3) + 48*(x 0)^3*(x 1)*(x 2)*(x 3) - 12*(x 0)^3*(x 1)*(x 3)^2 - 24*(x 0)^2*(x 1)^3*(x 3) + 42*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 12*(x 0)^2*(x 1)^2*(x 3)^2 := by
  change 4 * (3 * x 1 ^ 2 * x 2) * (x 0 ^ 3) + 8 * (6 * x 1 * x 2 * x 3) * (x 0 ^ 3) + (7/3) * (6 * x 1 * x 2 * x 3) * (3 * x 0 ^ 2 * x 1) - (32/3) * (6 * x 0 * x 1 * x 3) * (3 * x 0 ^ 2 * x 1) - (2/3) * (6 * x 0 * x 1 * x 3) * (3 * x 0 ^ 2 * x 3) - (4/3) * (6 * x 0 * x 1 * x 3) * (3 * x 0 * x 1 ^ 2) - (1/3) * (6 * x 0 * x 1 * x 3) * (6 * x 0 * x 1 * x 3)
       = 12*(x 0)^3*(x 1)^2*(x 2) - 192*(x 0)^3*(x 1)^2*(x 3) + 48*(x 0)^3*(x 1)*(x 2)*(x 3) - 12*(x 0)^3*(x 1)*(x 3)^2 - 24*(x 0)^2*(x 1)^3*(x 3) + 42*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 12*(x 0)^2*(x 1)^2*(x 3)^2
  ring

theorem napField_chain_v8 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 7 = 48*(x 0)^3*(x 1)^2*(x 2) - 96*(x 0)^3*(x 1)*(x 2)^2 + 192*(x 0)^3*(x 1)*(x 2)*(x 3) - 6*(x 0)^3*(x 2)^2*(x 3) - 12*(x 0)^2*(x 1)^2*(x 2)^2 + 21*(x 0)^2*(x 1)*(x 2)^3 - 6*(x 0)^2*(x 1)*(x 2)^2*(x 3) := by
  change 16 * (3 * x 1 ^ 2 * x 2) * (x 0 ^ 3) + 32 * (6 * x 1 * x 2 * x 3) * (x 0 ^ 3) + 7 * (x 2 ^ 3) * (3 * x 0 ^ 2 * x 1) - (32/3) * (3 * x 0 * x 2 ^ 2) * (3 * x 0 ^ 2 * x 1) - (2/3) * (3 * x 0 * x 2 ^ 2) * (3 * x 0 ^ 2 * x 3) - (4/3) * (3 * x 0 * x 2 ^ 2) * (3 * x 0 * x 1 ^ 2) - (1/3) * (3 * x 0 * x 2 ^ 2) * (6 * x 0 * x 1 * x 3)
       = 48*(x 0)^3*(x 1)^2*(x 2) - 96*(x 0)^3*(x 1)*(x 2)^2 + 192*(x 0)^3*(x 1)*(x 2)*(x 3) - 6*(x 0)^3*(x 2)^2*(x 3) - 12*(x 0)^2*(x 1)^2*(x 2)^2 + 21*(x 0)^2*(x 1)*(x 2)^3 - 6*(x 0)^2*(x 1)*(x 2)^2*(x 3)
  ring

theorem napField_chain_v9 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 8 = 48*(x 0)^3*(x 1)^2*(x 3) + 12*(x 0)^3*(x 1)*(x 2)^2 - 264*(x 0)^3*(x 1)*(x 2)*(x 3) + 192*(x 0)^3*(x 1)*(x 3)^2 + 6*(x 0)^3*(x 2)^2*(x 3) - 6*(x 0)^3*(x 2)*(x 3)^2 - 24*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 42*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 12*(x 0)^2*(x 1)*(x 2)*(x 3)^2 := by
  change 16 * (3 * x 1 ^ 2 * x 3) * (x 0 ^ 3) + 4 * (3 * x 1 * x 2 ^ 2) * (x 0 ^ 3) + 64 * (3 * x 1 * x 3 ^ 2) * (x 0 ^ 3) + 2 * (3 * x 2 ^ 2 * x 3) * (x 0 ^ 3) + (14/3) * (3 * x 2 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) - (44/3) * (6 * x 0 * x 2 * x 3) * (3 * x 0 ^ 2 * x 1) - (1/3) * (6 * x 0 * x 2 * x 3) * (3 * x 0 ^ 2 * x 3) - (4/3) * (6 * x 0 * x 2 * x 3) * (3 * x 0 * x 1 ^ 2) - (1/3) * (6 * x 0 * x 2 * x 3) * (6 * x 0 * x 1 * x 3)
       = 48*(x 0)^3*(x 1)^2*(x 3) + 12*(x 0)^3*(x 1)*(x 2)^2 - 264*(x 0)^3*(x 1)*(x 2)*(x 3) + 192*(x 0)^3*(x 1)*(x 3)^2 + 6*(x 0)^3*(x 2)^2*(x 3) - 6*(x 0)^3*(x 2)*(x 3)^2 - 24*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 42*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 12*(x 0)^2*(x 1)*(x 2)*(x 3)^2
  ring

theorem napField_chain_v10 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 9 = 12*(x 0)^3*(x 1)*(x 2)*(x 3) - 168*(x 0)^3*(x 1)*(x 3)^2 + 6*(x 0)^3*(x 2)*(x 3)^2 - 12*(x 0)^2*(x 1)^2*(x 3)^2 + 21*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 6*(x 0)^2*(x 1)*(x 3)^3 := by
  change 2 * (6 * x 1 * x 2 * x 3) * (x 0 ^ 3) + 2 * (3 * x 2 * x 3 ^ 2) * (x 0 ^ 3) + (7/3) * (3 * x 2 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) - (56/3) * (3 * x 0 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) - (4/3) * (3 * x 0 * x 3 ^ 2) * (3 * x 0 * x 1 ^ 2) - (1/3) * (3 * x 0 * x 3 ^ 2) * (6 * x 0 * x 1 * x 3)
       = 12*(x 0)^3*(x 1)*(x 2)*(x 3) - 168*(x 0)^3*(x 1)*(x 3)^2 + 6*(x 0)^3*(x 2)*(x 3)^2 - 12*(x 0)^2*(x 1)^2*(x 3)^2 + 21*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 6*(x 0)^2*(x 1)*(x 3)^3
  ring

theorem napField_chain_v11 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 10 = -12*(x 0)^2*(x 1)^4 + 21*(x 0)^2*(x 1)^3*(x 2) - 6*(x 0)^2*(x 1)^3*(x 3) := by
  change (7/3) * (3 * x 1 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 1) - 4 * (x 1 ^ 3) * (3 * x 0 ^ 2 * x 1) - 2 * (x 1 ^ 3) * (3 * x 0 ^ 2 * x 3)
       = -12*(x 0)^2*(x 1)^4 + 21*(x 0)^2*(x 1)^3*(x 2) - 6*(x 0)^2*(x 1)^3*(x 3)
  ring

theorem napField_chain_v12 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 11 = 24*(x 0)^2*(x 1)^4 - 72*(x 0)^2*(x 1)^3*(x 2) + 96*(x 0)^2*(x 1)^3*(x 3) + 42*(x 0)^2*(x 1)^2*(x 2)^2 - 15*(x 0)^2*(x 1)^2*(x 2)*(x 3) := by
  change 8 * (x 1 ^ 3) * (3 * x 0 ^ 2 * x 1) + (32/3) * (3 * x 1 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) + (14/3) * (3 * x 1 * x 2 ^ 2) * (3 * x 0 ^ 2 * x 1) - 8 * (3 * x 1 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 1) - (5/3) * (3 * x 1 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 3)
       = 24*(x 0)^2*(x 1)^4 - 72*(x 0)^2*(x 1)^3*(x 2) + 96*(x 0)^2*(x 1)^3*(x 3) + 42*(x 0)^2*(x 1)^2*(x 2)^2 - 15*(x 0)^2*(x 1)^2*(x 2)*(x 3)
  ring

theorem napField_chain_v13 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 12 = 6*(x 0)^2*(x 1)^3*(x 2) - 108*(x 0)^2*(x 1)^3*(x 3) + 45*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 12*(x 0)^2*(x 1)^2*(x 3)^2 := by
  change (2/3) * (3 * x 1 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 1) + (5/2) * (6 * x 1 * x 2 * x 3) * (3 * x 0 ^ 2 * x 1) - 12 * (3 * x 1 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) - (4/3) * (3 * x 1 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 3)
       = 6*(x 0)^2*(x 1)^3*(x 2) - 108*(x 0)^2*(x 1)^3*(x 3) + 45*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 12*(x 0)^2*(x 1)^2*(x 3)^2
  ring

theorem napField_chain_v14 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 13 = 48*(x 0)^2*(x 1)^3*(x 2) - 108*(x 0)^2*(x 1)^2*(x 2)^2 + 192*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 21*(x 0)^2*(x 1)*(x 2)^3 - 12*(x 0)^2*(x 1)*(x 2)^2*(x 3) := by
  change (16/3) * (3 * x 1 ^ 2 * x 2) * (3 * x 0 ^ 2 * x 1) + (32/3) * (6 * x 1 * x 2 * x 3) * (3 * x 0 ^ 2 * x 1) + 7 * (x 2 ^ 3) * (3 * x 0 ^ 2 * x 1) - 12 * (3 * x 1 * x 2 ^ 2) * (3 * x 0 ^ 2 * x 1) - (4/3) * (3 * x 1 * x 2 ^ 2) * (3 * x 0 ^ 2 * x 3)
       = 48*(x 0)^2*(x 1)^3*(x 2) - 108*(x 0)^2*(x 1)^2*(x 2)^2 + 192*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 21*(x 0)^2*(x 1)*(x 2)^3 - 12*(x 0)^2*(x 1)*(x 2)^2*(x 3)
  ring

theorem napField_chain_v15 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 14 = 48*(x 0)^2*(x 1)^3*(x 3) + 12*(x 0)^2*(x 1)^2*(x 2)^2 - 288*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 192*(x 0)^2*(x 1)^2*(x 3)^2 + 48*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 18*(x 0)^2*(x 1)*(x 2)*(x 3)^2 := by
  change (16/3) * (3 * x 1 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) + (4/3) * (3 * x 1 * x 2 ^ 2) * (3 * x 0 ^ 2 * x 1) + (64/3) * (3 * x 1 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) + (16/3) * (3 * x 2 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) - 16 * (6 * x 1 * x 2 * x 3) * (3 * x 0 ^ 2 * x 1) - (6 * x 1 * x 2 * x 3) * (3 * x 0 ^ 2 * x 3)
       = 48*(x 0)^2*(x 1)^3*(x 3) + 12*(x 0)^2*(x 1)^2*(x 2)^2 - 288*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 192*(x 0)^2*(x 1)^2*(x 3)^2 + 48*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 18*(x 0)^2*(x 1)*(x 2)*(x 3)^2
  ring

theorem napField_chain_v16 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 15 = 12*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 180*(x 0)^2*(x 1)^2*(x 3)^2 + 27*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 6*(x 0)^2*(x 1)*(x 3)^3 := by
  change (2/3) * (6 * x 1 * x 2 * x 3) * (3 * x 0 ^ 2 * x 1) + 3 * (3 * x 2 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) - 20 * (3 * x 1 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) - (2/3) * (3 * x 1 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 3)
       = 12*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 180*(x 0)^2*(x 1)^2*(x 3)^2 + 27*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 6*(x 0)^2*(x 1)*(x 3)^3
  ring

theorem napField_chain_v17 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 16 = 24*(x 0)^2*(x 1)^2*(x 2)^2 - 48*(x 0)^2*(x 1)*(x 2)^3 + 96*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 3*(x 0)^2*(x 2)^3*(x 3) := by
  change (8/3) * (3 * x 1 * x 2 ^ 2) * (3 * x 0 ^ 2 * x 1) + (32/3) * (3 * x 2 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) - 16 * (x 2 ^ 3) * (3 * x 0 ^ 2 * x 1) - (x 2 ^ 3) * (3 * x 0 ^ 2 * x 3)
       = 24*(x 0)^2*(x 1)^2*(x 2)^2 - 48*(x 0)^2*(x 1)*(x 2)^3 + 96*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 3*(x 0)^2*(x 2)^3*(x 3)
  ring

theorem napField_chain_v18 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 17 = 48*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 6*(x 0)^2*(x 1)*(x 2)^3 - 180*(x 0)^2*(x 1)*(x 2)^2*(x 3) + 192*(x 0)^2*(x 1)*(x 2)*(x 3)^2 + 3*(x 0)^2*(x 2)^3*(x 3) - 6*(x 0)^2*(x 2)^2*(x 3)^2 := by
  change (8/3) * (6 * x 1 * x 2 * x 3) * (3 * x 0 ^ 2 * x 1) + 2 * (x 2 ^ 3) * (3 * x 0 ^ 2 * x 1) + (64/3) * (3 * x 2 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) + (x 2 ^ 3) * (3 * x 0 ^ 2 * x 3) - 20 * (3 * x 2 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) - (2/3) * (3 * x 2 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 3)
       = 48*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 6*(x 0)^2*(x 1)*(x 2)^3 - 180*(x 0)^2*(x 1)*(x 2)^2*(x 3) + 192*(x 0)^2*(x 1)*(x 2)*(x 3)^2 + 3*(x 0)^2*(x 2)^3*(x 3) - 6*(x 0)^2*(x 2)^2*(x 3)^2
  ring

theorem napField_chain_v19 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 18 = 24*(x 0)^2*(x 1)^2*(x 3)^2 + 12*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 216*(x 0)^2*(x 1)*(x 2)*(x 3)^2 + 96*(x 0)^2*(x 1)*(x 3)^3 + 6*(x 0)^2*(x 2)^2*(x 3)^2 - 3*(x 0)^2*(x 2)*(x 3)^3 := by
  change (8/3) * (3 * x 1 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) + (4/3) * (3 * x 2 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 1) + 32 * (x 3 ^ 3) * (3 * x 0 ^ 2 * x 1) + (2/3) * (3 * x 2 ^ 2 * x 3) * (3 * x 0 ^ 2 * x 3) - 24 * (3 * x 2 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) - (1/3) * (3 * x 2 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 3)
       = 24*(x 0)^2*(x 1)^2*(x 3)^2 + 12*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 216*(x 0)^2*(x 1)*(x 2)*(x 3)^2 + 96*(x 0)^2*(x 1)*(x 3)^3 + 6*(x 0)^2*(x 2)^2*(x 3)^2 - 3*(x 0)^2*(x 2)*(x 3)^3
  ring

theorem napField_chain_v20 (x : Fin 4 → ℝ) :
    napField (fun j => cubedLift j x) 19 = 6*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 84*(x 0)^2*(x 1)*(x 3)^3 + 3*(x 0)^2*(x 2)*(x 3)^3 := by
  change (2/3) * (3 * x 2 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 1) + (1/3) * (3 * x 2 * x 3 ^ 2) * (3 * x 0 ^ 2 * x 3) - 28 * (x 3 ^ 3) * (3 * x 0 ^ 2 * x 1)
       = 6*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 84*(x 0)^2*(x 1)*(x 3)^3 + 3*(x 0)^2*(x 2)*(x 3)^3
  ring

/-- Generic expansion of a sum over Fin 20 into 20 explicit terms. -/
private lemma sum_fin_20 (f : Fin 20 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 +
               f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 := by
  simp [Fin.sum_univ_succ]
  ring

/-- Conservation on the cubed manifold: ∑ i, v̇_i = 0.
  Follows from summing the 20 chain-rule theorems — the sum of the RHS polynomials
  cancels identically. (Algebraically this is 3·(Σx_j)²·(Σẋ_j) = 0 via r2Field_conservative,
  but we prove it directly from the chain_v1..v20 identities.) -/
theorem napField_conservative_on_cubed (x : Fin 4 → ℝ) :
    ∑ i, napField (fun j => cubedLift j x) i = 0 := by
  rw [sum_fin_20, napField_chain_v1 x, napField_chain_v2 x, napField_chain_v3 x,
      napField_chain_v4 x, napField_chain_v5 x, napField_chain_v6 x, napField_chain_v7 x,
      napField_chain_v8 x, napField_chain_v9 x, napField_chain_v10 x, napField_chain_v11 x,
      napField_chain_v12 x, napField_chain_v13 x, napField_chain_v14 x, napField_chain_v15 x,
      napField_chain_v16 x, napField_chain_v17 x, napField_chain_v18 x, napField_chain_v19 x,
      napField_chain_v20 x]
  ring

/-! ### Cubed-system HasDerivAt template (v_1 row)

Concrete proof that the chain-rule polynomial in `napField_chain_v1` is
exactly the time derivative of `cubedLift 0 ∘ z` along an r²-trick
trajectory.  The same template applies to all 20 rows; v_1 is the
simplest (a single power, `(x 0)^3`).

Pattern: `HasDerivAt.pow` on `(z s 0)^3` produces
`3 · (z t 0)^2 · r2Field(z t) 0`, which `ring`-rewrites to the v_1
chain-rule polynomial via `napField_chain_v1`. -/

theorem cubedLift_0_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 0 (z s))
      (napField (fun j => cubedLift j (z t)) 0) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have hp : HasDerivAt (fun s => (z s 0) ^ 3)
      (((3 : ℕ) : ℝ) * (z t 0) ^ (3 - 1) * r2Field (z t) 0) t := h0.pow 3
  have hexpand :
      ((3 : ℕ) : ℝ) * (z t 0) ^ (3 - 1) * r2Field (z t) 0
        = napField (fun j => cubedLift j (z t)) 0 := by
    rw [napField_chain_v1]
    simp only [r2Field, lambdaField]
    ring
  have hcl : (fun s => cubedLift 0 (z s)) = (fun s => (z s 0) ^ 3) := by
    funext s; simp [cubedLift]
  rw [hcl, ← hexpand]
  exact hp

/-- HasDerivAt for v_2 = 3·r²·u along an r²-trick trajectory. -/
theorem cubedLift_1_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 1 (z s))
      (napField (fun j => cubedLift j (z t)) 1) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have hbase :
      HasDerivAt (fun s => 3 * ((z s 0) ^ 2 * z s 1))
        (3 * ((((2 : ℕ) : ℝ) * (z t 0) ^ (2 - 1) * r2Field (z t) 0) * z t 1
              + (z t 0) ^ 2 * r2Field (z t) 1)) t :=
    (((h0.pow 2).mul h1).const_mul 3)
  have hcl : (fun s => cubedLift 1 (z s)) = (fun s => 3 * ((z s 0) ^ 2 * z s 1)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * ((((2 : ℕ) : ℝ) * (z t 0) ^ (2 - 1) * r2Field (z t) 0) * z t 1
            + (z t 0) ^ 2 * r2Field (z t) 1)
        = napField (fun j => cubedLift j (z t)) 1 := by
    rw [napField_chain_v2]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_3 = 3·r²·z_01 along an r²-trick trajectory. -/
theorem cubedLift_2_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 2 (z s))
      (napField (fun j => cubedLift j (z t)) 2) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have hbase :
      HasDerivAt (fun s => 3 * ((z s 0) ^ 2 * z s 2))
        (3 * ((((2 : ℕ) : ℝ) * (z t 0) ^ (2 - 1) * r2Field (z t) 0) * z t 2
              + (z t 0) ^ 2 * r2Field (z t) 2)) t :=
    (((h0.pow 2).mul h2).const_mul 3)
  have hcl : (fun s => cubedLift 2 (z s)) = (fun s => 3 * ((z s 0) ^ 2 * z s 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * ((((2 : ℕ) : ℝ) * (z t 0) ^ (2 - 1) * r2Field (z t) 0) * z t 2
            + (z t 0) ^ 2 * r2Field (z t) 2)
        = napField (fun j => cubedLift j (z t)) 2 := by
    rw [napField_chain_v3]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_4 = 3·r²·z_11 along an r²-trick trajectory. -/
theorem cubedLift_3_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 3 (z s))
      (napField (fun j => cubedLift j (z t)) 3) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 3 * ((z s 0) ^ 2 * z s 3))
        (3 * ((((2 : ℕ) : ℝ) * (z t 0) ^ (2 - 1) * r2Field (z t) 0) * z t 3
              + (z t 0) ^ 2 * r2Field (z t) 3)) t :=
    (((h0.pow 2).mul h3).const_mul 3)
  have hcl : (fun s => cubedLift 3 (z s)) = (fun s => 3 * ((z s 0) ^ 2 * z s 3)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * ((((2 : ℕ) : ℝ) * (z t 0) ^ (2 - 1) * r2Field (z t) 0) * z t 3
            + (z t 0) ^ 2 * r2Field (z t) 3)
        = napField (fun j => cubedLift j (z t)) 3 := by
    rw [napField_chain_v4]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_5 = 3·r·u² along an r²-trick trajectory. -/
theorem cubedLift_4_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 4 (z s))
      (napField (fun j => cubedLift j (z t)) 4) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have hbase :
      HasDerivAt (fun s => 3 * (z s 0 * (z s 1) ^ 2))
        (3 * (r2Field (z t) 0 * (z t 1) ^ 2
              + z t 0 * (((2 : ℕ) : ℝ) * (z t 1) ^ (2 - 1) * r2Field (z t) 1))) t :=
    ((h0.mul (h1.pow 2)).const_mul 3)
  have hcl : (fun s => cubedLift 4 (z s)) = (fun s => 3 * (z s 0 * (z s 1) ^ 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * (r2Field (z t) 0 * (z t 1) ^ 2
            + z t 0 * (((2 : ℕ) : ℝ) * (z t 1) ^ (2 - 1) * r2Field (z t) 1))
        = napField (fun j => cubedLift j (z t)) 4 := by
    rw [napField_chain_v5]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_6 = 6·r·u·z_01 along an r²-trick trajectory. -/
theorem cubedLift_5_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 5 (z s))
      (napField (fun j => cubedLift j (z t)) 5) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have hbase :
      HasDerivAt (fun s => 6 * (z s 0 * z s 1 * z s 2))
        (6 * ((r2Field (z t) 0 * z t 1 + z t 0 * r2Field (z t) 1) * z t 2
              + (z t 0 * z t 1) * r2Field (z t) 2)) t :=
    (((h0.mul h1).mul h2).const_mul 6)
  have hcl : (fun s => cubedLift 5 (z s)) = (fun s => 6 * (z s 0 * z s 1 * z s 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      6 * ((r2Field (z t) 0 * z t 1 + z t 0 * r2Field (z t) 1) * z t 2
            + (z t 0 * z t 1) * r2Field (z t) 2)
        = napField (fun j => cubedLift j (z t)) 5 := by
    rw [napField_chain_v6]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_7 = 6·r·u·z_11 along an r²-trick trajectory. -/
theorem cubedLift_6_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 6 (z s))
      (napField (fun j => cubedLift j (z t)) 6) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 6 * (z s 0 * z s 1 * z s 3))
        (6 * ((r2Field (z t) 0 * z t 1 + z t 0 * r2Field (z t) 1) * z t 3
              + (z t 0 * z t 1) * r2Field (z t) 3)) t :=
    (((h0.mul h1).mul h3).const_mul 6)
  have hcl : (fun s => cubedLift 6 (z s)) = (fun s => 6 * (z s 0 * z s 1 * z s 3)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      6 * ((r2Field (z t) 0 * z t 1 + z t 0 * r2Field (z t) 1) * z t 3
            + (z t 0 * z t 1) * r2Field (z t) 3)
        = napField (fun j => cubedLift j (z t)) 6 := by
    rw [napField_chain_v7]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_8 = 3·r·z_01² along an r²-trick trajectory. -/
theorem cubedLift_7_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 7 (z s))
      (napField (fun j => cubedLift j (z t)) 7) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have hbase :
      HasDerivAt (fun s => 3 * (z s 0 * (z s 2) ^ 2))
        (3 * (r2Field (z t) 0 * (z t 2) ^ 2
              + z t 0 * (((2 : ℕ) : ℝ) * (z t 2) ^ (2 - 1) * r2Field (z t) 2))) t :=
    ((h0.mul (h2.pow 2)).const_mul 3)
  have hcl : (fun s => cubedLift 7 (z s)) = (fun s => 3 * (z s 0 * (z s 2) ^ 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * (r2Field (z t) 0 * (z t 2) ^ 2
            + z t 0 * (((2 : ℕ) : ℝ) * (z t 2) ^ (2 - 1) * r2Field (z t) 2))
        = napField (fun j => cubedLift j (z t)) 7 := by
    rw [napField_chain_v8]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_9 = 6·r·z_01·z_11 along an r²-trick trajectory. -/
theorem cubedLift_8_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 8 (z s))
      (napField (fun j => cubedLift j (z t)) 8) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 6 * (z s 0 * z s 2 * z s 3))
        (6 * ((r2Field (z t) 0 * z t 2 + z t 0 * r2Field (z t) 2) * z t 3
              + (z t 0 * z t 2) * r2Field (z t) 3)) t :=
    (((h0.mul h2).mul h3).const_mul 6)
  have hcl : (fun s => cubedLift 8 (z s)) = (fun s => 6 * (z s 0 * z s 2 * z s 3)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      6 * ((r2Field (z t) 0 * z t 2 + z t 0 * r2Field (z t) 2) * z t 3
            + (z t 0 * z t 2) * r2Field (z t) 3)
        = napField (fun j => cubedLift j (z t)) 8 := by
    rw [napField_chain_v9]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_10 = 3·r·z_11² along an r²-trick trajectory. -/
theorem cubedLift_9_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 9 (z s))
      (napField (fun j => cubedLift j (z t)) 9) t := by
  have h0 : HasDerivAt (fun s => z s 0) (r2Field (z t) 0) t :=
    hasDerivAt_pi.mp hz 0
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 3 * (z s 0 * (z s 3) ^ 2))
        (3 * (r2Field (z t) 0 * (z t 3) ^ 2
              + z t 0 * (((2 : ℕ) : ℝ) * (z t 3) ^ (2 - 1) * r2Field (z t) 3))) t :=
    ((h0.mul (h3.pow 2)).const_mul 3)
  have hcl : (fun s => cubedLift 9 (z s)) = (fun s => 3 * (z s 0 * (z s 3) ^ 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * (r2Field (z t) 0 * (z t 3) ^ 2
            + z t 0 * (((2 : ℕ) : ℝ) * (z t 3) ^ (2 - 1) * r2Field (z t) 3))
        = napField (fun j => cubedLift j (z t)) 9 := by
    rw [napField_chain_v10]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_11 = u³ along an r²-trick trajectory. -/
theorem cubedLift_10_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 10 (z s))
      (napField (fun j => cubedLift j (z t)) 10) t := by
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have hp : HasDerivAt (fun s => (z s 1) ^ 3)
      (((3 : ℕ) : ℝ) * (z t 1) ^ (3 - 1) * r2Field (z t) 1) t := h1.pow 3
  have hexpand :
      ((3 : ℕ) : ℝ) * (z t 1) ^ (3 - 1) * r2Field (z t) 1
        = napField (fun j => cubedLift j (z t)) 10 := by
    rw [napField_chain_v11]
    simp only [r2Field, lambdaField]
    ring
  have hcl : (fun s => cubedLift 10 (z s)) = (fun s => (z s 1) ^ 3) := by
    funext s; simp [cubedLift]
  rw [hcl, ← hexpand]
  exact hp

/-- HasDerivAt for v_12 = 3·u²·z_01 along an r²-trick trajectory. -/
theorem cubedLift_11_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 11 (z s))
      (napField (fun j => cubedLift j (z t)) 11) t := by
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have hbase :
      HasDerivAt (fun s => 3 * ((z s 1) ^ 2 * z s 2))
        (3 * ((((2 : ℕ) : ℝ) * (z t 1) ^ (2 - 1) * r2Field (z t) 1) * z t 2
              + (z t 1) ^ 2 * r2Field (z t) 2)) t :=
    (((h1.pow 2).mul h2).const_mul 3)
  have hcl : (fun s => cubedLift 11 (z s)) = (fun s => 3 * ((z s 1) ^ 2 * z s 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * ((((2 : ℕ) : ℝ) * (z t 1) ^ (2 - 1) * r2Field (z t) 1) * z t 2
            + (z t 1) ^ 2 * r2Field (z t) 2)
        = napField (fun j => cubedLift j (z t)) 11 := by
    rw [napField_chain_v12]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_13 = 3·u²·z_11 along an r²-trick trajectory. -/
theorem cubedLift_12_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 12 (z s))
      (napField (fun j => cubedLift j (z t)) 12) t := by
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 3 * ((z s 1) ^ 2 * z s 3))
        (3 * ((((2 : ℕ) : ℝ) * (z t 1) ^ (2 - 1) * r2Field (z t) 1) * z t 3
              + (z t 1) ^ 2 * r2Field (z t) 3)) t :=
    (((h1.pow 2).mul h3).const_mul 3)
  have hcl : (fun s => cubedLift 12 (z s)) = (fun s => 3 * ((z s 1) ^ 2 * z s 3)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * ((((2 : ℕ) : ℝ) * (z t 1) ^ (2 - 1) * r2Field (z t) 1) * z t 3
            + (z t 1) ^ 2 * r2Field (z t) 3)
        = napField (fun j => cubedLift j (z t)) 12 := by
    rw [napField_chain_v13]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_14 = 3·u·z_01² along an r²-trick trajectory. -/
theorem cubedLift_13_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 13 (z s))
      (napField (fun j => cubedLift j (z t)) 13) t := by
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have hbase :
      HasDerivAt (fun s => 3 * (z s 1 * (z s 2) ^ 2))
        (3 * (r2Field (z t) 1 * (z t 2) ^ 2
              + z t 1 * (((2 : ℕ) : ℝ) * (z t 2) ^ (2 - 1) * r2Field (z t) 2))) t :=
    ((h1.mul (h2.pow 2)).const_mul 3)
  have hcl : (fun s => cubedLift 13 (z s)) = (fun s => 3 * (z s 1 * (z s 2) ^ 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * (r2Field (z t) 1 * (z t 2) ^ 2
            + z t 1 * (((2 : ℕ) : ℝ) * (z t 2) ^ (2 - 1) * r2Field (z t) 2))
        = napField (fun j => cubedLift j (z t)) 13 := by
    rw [napField_chain_v14]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_15 = 6·u·z_01·z_11 along an r²-trick trajectory. -/
theorem cubedLift_14_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 14 (z s))
      (napField (fun j => cubedLift j (z t)) 14) t := by
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 6 * (z s 1 * z s 2 * z s 3))
        (6 * ((r2Field (z t) 1 * z t 2 + z t 1 * r2Field (z t) 2) * z t 3
              + (z t 1 * z t 2) * r2Field (z t) 3)) t :=
    (((h1.mul h2).mul h3).const_mul 6)
  have hcl : (fun s => cubedLift 14 (z s)) = (fun s => 6 * (z s 1 * z s 2 * z s 3)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      6 * ((r2Field (z t) 1 * z t 2 + z t 1 * r2Field (z t) 2) * z t 3
            + (z t 1 * z t 2) * r2Field (z t) 3)
        = napField (fun j => cubedLift j (z t)) 14 := by
    rw [napField_chain_v15]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_16 = 3·u·z_11² along an r²-trick trajectory. -/
theorem cubedLift_15_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 15 (z s))
      (napField (fun j => cubedLift j (z t)) 15) t := by
  have h1 : HasDerivAt (fun s => z s 1) (r2Field (z t) 1) t :=
    hasDerivAt_pi.mp hz 1
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 3 * (z s 1 * (z s 3) ^ 2))
        (3 * (r2Field (z t) 1 * (z t 3) ^ 2
              + z t 1 * (((2 : ℕ) : ℝ) * (z t 3) ^ (2 - 1) * r2Field (z t) 3))) t :=
    ((h1.mul (h3.pow 2)).const_mul 3)
  have hcl : (fun s => cubedLift 15 (z s)) = (fun s => 3 * (z s 1 * (z s 3) ^ 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * (r2Field (z t) 1 * (z t 3) ^ 2
            + z t 1 * (((2 : ℕ) : ℝ) * (z t 3) ^ (2 - 1) * r2Field (z t) 3))
        = napField (fun j => cubedLift j (z t)) 15 := by
    rw [napField_chain_v16]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_17 = z_01³ along an r²-trick trajectory. -/
theorem cubedLift_16_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 16 (z s))
      (napField (fun j => cubedLift j (z t)) 16) t := by
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have hp : HasDerivAt (fun s => (z s 2) ^ 3)
      (((3 : ℕ) : ℝ) * (z t 2) ^ (3 - 1) * r2Field (z t) 2) t := h2.pow 3
  have hexpand :
      ((3 : ℕ) : ℝ) * (z t 2) ^ (3 - 1) * r2Field (z t) 2
        = napField (fun j => cubedLift j (z t)) 16 := by
    rw [napField_chain_v17]
    simp only [r2Field, lambdaField]
    ring
  have hcl : (fun s => cubedLift 16 (z s)) = (fun s => (z s 2) ^ 3) := by
    funext s; simp [cubedLift]
  rw [hcl, ← hexpand]
  exact hp

/-- HasDerivAt for v_18 = 3·z_01²·z_11 along an r²-trick trajectory. -/
theorem cubedLift_17_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 17 (z s))
      (napField (fun j => cubedLift j (z t)) 17) t := by
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 3 * ((z s 2) ^ 2 * z s 3))
        (3 * ((((2 : ℕ) : ℝ) * (z t 2) ^ (2 - 1) * r2Field (z t) 2) * z t 3
              + (z t 2) ^ 2 * r2Field (z t) 3)) t :=
    (((h2.pow 2).mul h3).const_mul 3)
  have hcl : (fun s => cubedLift 17 (z s)) = (fun s => 3 * ((z s 2) ^ 2 * z s 3)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * ((((2 : ℕ) : ℝ) * (z t 2) ^ (2 - 1) * r2Field (z t) 2) * z t 3
            + (z t 2) ^ 2 * r2Field (z t) 3)
        = napField (fun j => cubedLift j (z t)) 17 := by
    rw [napField_chain_v18]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_19 = 3·z_01·z_11² along an r²-trick trajectory. -/
theorem cubedLift_18_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 18 (z s))
      (napField (fun j => cubedLift j (z t)) 18) t := by
  have h2 : HasDerivAt (fun s => z s 2) (r2Field (z t) 2) t :=
    hasDerivAt_pi.mp hz 2
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hbase :
      HasDerivAt (fun s => 3 * (z s 2 * (z s 3) ^ 2))
        (3 * (r2Field (z t) 2 * (z t 3) ^ 2
              + z t 2 * (((2 : ℕ) : ℝ) * (z t 3) ^ (2 - 1) * r2Field (z t) 3))) t :=
    ((h2.mul (h3.pow 2)).const_mul 3)
  have hcl : (fun s => cubedLift 18 (z s)) = (fun s => 3 * (z s 2 * (z s 3) ^ 2)) := by
    funext s; simp [cubedLift]; ring
  have hexpand :
      3 * (r2Field (z t) 2 * (z t 3) ^ 2
            + z t 2 * (((2 : ℕ) : ℝ) * (z t 3) ^ (2 - 1) * r2Field (z t) 3))
        = napField (fun j => cubedLift j (z t)) 18 := by
    rw [napField_chain_v19]
    simp only [r2Field, lambdaField]
    ring
  rw [hcl, ← hexpand]
  exact hbase

/-- HasDerivAt for v_20 = z_11³ along an r²-trick trajectory. -/
theorem cubedLift_19_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) :
    HasDerivAt (fun s => cubedLift 19 (z s))
      (napField (fun j => cubedLift j (z t)) 19) t := by
  have h3 : HasDerivAt (fun s => z s 3) (r2Field (z t) 3) t :=
    hasDerivAt_pi.mp hz 3
  have hp : HasDerivAt (fun s => (z s 3) ^ 3)
      (((3 : ℕ) : ℝ) * (z t 3) ^ (3 - 1) * r2Field (z t) 3) t := h3.pow 3
  have hexpand :
      ((3 : ℕ) : ℝ) * (z t 3) ^ (3 - 1) * r2Field (z t) 3
        = napField (fun j => cubedLift j (z t)) 19 := by
    rw [napField_chain_v20]
    simp only [r2Field, lambdaField]
    ring
  have hcl : (fun s => cubedLift 19 (z s)) = (fun s => (z s 3) ^ 3) := by
    funext s; simp [cubedLift]
  rw [hcl, ← hexpand]
  exact hp

/-- **Packaged NAP-20 chain rule.**  Combines `cubedLift_0..19_hasDerivAt`
into a uniform statement quantified over the row index `i : Fin 20`. -/
theorem cubedLift_hasDerivAt {z : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hz : HasDerivAt z (r2Field (z t)) t) (i : Fin 20) :
    HasDerivAt (fun s => cubedLift i (z s))
      (napField (fun j => cubedLift j (z t)) i) t := by
  fin_cases i
  · exact cubedLift_0_hasDerivAt hz
  · exact cubedLift_1_hasDerivAt hz
  · exact cubedLift_2_hasDerivAt hz
  · exact cubedLift_3_hasDerivAt hz
  · exact cubedLift_4_hasDerivAt hz
  · exact cubedLift_5_hasDerivAt hz
  · exact cubedLift_6_hasDerivAt hz
  · exact cubedLift_7_hasDerivAt hz
  · exact cubedLift_8_hasDerivAt hz
  · exact cubedLift_9_hasDerivAt hz
  · exact cubedLift_10_hasDerivAt hz
  · exact cubedLift_11_hasDerivAt hz
  · exact cubedLift_12_hasDerivAt hz
  · exact cubedLift_13_hasDerivAt hz
  · exact cubedLift_14_hasDerivAt hz
  · exact cubedLift_15_hasDerivAt hz
  · exact cubedLift_16_hasDerivAt hz
  · exact cubedLift_17_hasDerivAt hz
  · exact cubedLift_18_hasDerivAt hz
  · exact cubedLift_19_hasDerivAt hz

/-! ### Step 4: Structural NAP Verification

We certify the NAP property of `napField` (paper §9) by exhibiting a decomposition
  `napField x i = napPosPart x i - x i * napLossFactor x i`
with the following two properties:

* `napPosPart x i` is a sum of monomials `c · x β · x γ` with `β ≠ i ∧ γ ≠ i`.
  This is manifest by reading off the `![...]` literal definition below —
  every row lists exactly the positive monomials of the corresponding `napField`
  row, and none of them reference `x i`.
* The only negative contribution to `napField x i` factors through `x i`,
  with cofactor `napLossFactor x i` linear in the other species.

Together these are exactly the two NAP clauses.
-/

/-- Positive (NAP-compliant) part of `napField _ i`: each summand is a
  product `c · x β · x γ` with `β ≠ i ∧ γ ≠ i` (verifiable by inspection).
  Transcribed from the `+` terms of `napField`. -/
noncomputable def napPosPart (x : Fin 20 → ℝ) : Fin 20 → ℝ := ![
  -- v_1, i=0 : (2,1)
  (7/3) * x 2 * x 1,
  -- v_2, i=1 : (5,0), (11,0)
  (7/2) * x 5 * x 0 + 14 * x 11 * x 0,
  -- v_3, i=2 : (4,0), (6,0), (13,0)
  8 * x 4 * x 0 + 16 * x 6 * x 0 + 14 * x 13 * x 0,
  -- v_4, i=3 : (5,0), (8,0), (14,0)
  x 5 * x 0 + (1/2) * x 8 * x 0 + 7 * x 14 * x 0,
  -- v_5, i=4 : (11,0), (11,1)
  14 * x 11 * x 0 + (7/3) * x 11 * x 1,
  -- v_6, i=5 : (10,0), (12,0), (13,0), (13,1)
  48 * x 10 * x 0 + 64 * x 12 * x 0 + 14 * x 13 * x 0 + (14/3) * x 13 * x 1,
  -- v_7, i=6 : (11,0), (14,0), (14,1)
  4 * x 11 * x 0 + 8 * x 14 * x 0 + (7/3) * x 14 * x 1,
  -- v_8, i=7 : (11,0), (14,0), (16,1)
  16 * x 11 * x 0 + 32 * x 14 * x 0 + 7 * x 16 * x 1,
  -- v_9, i=8 : (12,0), (13,0), (15,0), (17,0), (17,1)
  16 * x 12 * x 0 + 4 * x 13 * x 0 + 64 * x 15 * x 0
    + 2 * x 17 * x 0 + (14/3) * x 17 * x 1,
  -- v_10, i=9 : (14,0), (18,0), (18,1)
  2 * x 14 * x 0 + 2 * x 18 * x 0 + (7/3) * x 18 * x 1,
  -- v_11, i=10 : (11,1)
  (7/3) * x 11 * x 1,
  -- v_12, i=11 : (10,1), (12,1), (13,1)
  8 * x 10 * x 1 + (32/3) * x 12 * x 1 + (14/3) * x 13 * x 1,
  -- v_13, i=12 : (11,1), (14,1)
  (2/3) * x 11 * x 1 + (5/2) * x 14 * x 1,
  -- v_14, i=13 : (11,1), (14,1), (16,1)
  (16/3) * x 11 * x 1 + (32/3) * x 14 * x 1 + 7 * x 16 * x 1,
  -- v_15, i=14 : (12,1), (13,1), (15,1), (17,1)
  (16/3) * x 12 * x 1 + (4/3) * x 13 * x 1
    + (64/3) * x 15 * x 1 + (16/3) * x 17 * x 1,
  -- v_16, i=15 : (14,1), (18,1)
  (2/3) * x 14 * x 1 + 3 * x 18 * x 1,
  -- v_17, i=16 : (13,1), (17,1)
  (8/3) * x 13 * x 1 + (32/3) * x 17 * x 1,
  -- v_18, i=17 : (14,1), (16,1), (18,1), (16,3)
  (8/3) * x 14 * x 1 + 2 * x 16 * x 1 + (64/3) * x 18 * x 1 + x 16 * x 3,
  -- v_19, i=18 : (15,1), (17,1), (19,1), (17,3)
  (8/3) * x 15 * x 1 + (4/3) * x 17 * x 1
    + 32 * x 19 * x 1 + (2/3) * x 17 * x 3,
  -- v_20, i=19 : (18,1), (18,3)
  (2/3) * x 18 * x 1 + (1/3) * x 18 * x 3]

/-- Loss cofactor for row `i`: the negative part of `napField x i` factors
  as `x i * napLossFactor x i`. Each entry is a nonnegative linear form in
  other species. -/
noncomputable def napLossFactor (x : Fin 20 → ℝ) : Fin 20 → ℝ := ![
  -- v_1, i=0
  4 * x 4 + x 6,
  -- v_2, i=1
  (4/3) * x 1 + (2/3) * x 3 + (8/3) * x 4 + (2/3) * x 6,
  -- v_3, i=2
  (16/3) * x 1 + (1/3) * x 3 + (8/3) * x 4 + (2/3) * x 6,
  -- v_4, i=3
  (28/3) * x 1 + (8/3) * x 4 + (2/3) * x 6,
  -- v_5, i=4
  (8/3) * x 1 + (4/3) * x 3 + (4/3) * x 4 + (1/3) * x 6,
  -- v_6, i=5
  (20/3) * x 1 + x 3 + (4/3) * x 4 + (1/3) * x 6,
  -- v_7, i=6
  (32/3) * x 1 + (2/3) * x 3 + (4/3) * x 4 + (1/3) * x 6,
  -- v_8, i=7
  (32/3) * x 1 + (2/3) * x 3 + (4/3) * x 4 + (1/3) * x 6,
  -- v_9, i=8
  (44/3) * x 1 + (1/3) * x 3 + (4/3) * x 4 + (1/3) * x 6,
  -- v_10, i=9
  (56/3) * x 1 + (4/3) * x 4 + (1/3) * x 6,
  -- v_11, i=10
  4 * x 1 + 2 * x 3,
  -- v_12, i=11
  8 * x 1 + (5/3) * x 3,
  -- v_13, i=12
  12 * x 1 + (4/3) * x 3,
  -- v_14, i=13
  12 * x 1 + (4/3) * x 3,
  -- v_15, i=14
  16 * x 1 + x 3,
  -- v_16, i=15
  20 * x 1 + (2/3) * x 3,
  -- v_17, i=16
  16 * x 1 + x 3,
  -- v_18, i=17
  20 * x 1 + (2/3) * x 3,
  -- v_19, i=18
  24 * x 1 + (1/3) * x 3,
  -- v_20, i=19
  28 * x 1]

/-- NAP structural decomposition — each `napField` row splits as
  `(positive NAP part) − x_i · (loss cofactor)`. Combined with the manifest
  index avoidance in `napPosPart`'s definition, this certifies the NAP
  clauses of paper §9. -/
theorem napField_decomposes (x : Fin 20 → ℝ) (i : Fin 20) :
    napField x i = napPosPart x i - x i * napLossFactor x i := by
  fin_cases i <;> simp [napField, napPosPart, napLossFactor] <;> ring

/-! ## Step 5: Readout Convergence (PLACEHOLDER)

The readout z_11 + z_01/2 extracts to a linear combination of the 20
v_i via Lemma 10.1: x_j = (1/3) Σ α_j v_α.

Concrete coefficients are in paper §10.3. The limit (3 - √5)/6 is
preserved across the pipeline: Proposition 11.4 (λ-trick) and
Proposition 11.5 (r²-trick) show neither step changes lim_{t→∞} readout. -/

/-- Readout coefficients per Lemma 10.1: `c_α = (2α_3 + α_2) / 6` so that
  `Σ c_α v_α = z_11 + z_01/2 = x 3 + x 2 / 2` on the cubed manifold.
  Derivation: `x_j = (1/3) Σ α_j v_α`, so `z_11 + z_01/2 = x 3 + x 2 / 2
  = (1/6) Σ (2α_3 + α_2) v_α`. -/
noncomputable def readoutCoeff : Fin 20 → ℝ :=
  ![0,       -- v_1  α=(3,0,0,0)
    0,       -- v_2  α=(2,1,0,0)
    1/6,     -- v_3  α=(2,0,1,0)
    1/3,     -- v_4  α=(2,0,0,1)
    0,       -- v_5  α=(1,2,0,0)
    1/6,     -- v_6  α=(1,1,1,0)
    1/3,     -- v_7  α=(1,1,0,1)
    1/3,     -- v_8  α=(1,0,2,0)
    1/2,     -- v_9  α=(1,0,1,1)
    2/3,     -- v_10 α=(1,0,0,2)
    0,       -- v_11 α=(0,3,0,0)
    1/6,     -- v_12 α=(0,2,1,0)
    1/3,     -- v_13 α=(0,2,0,1)
    1/3,     -- v_14 α=(0,1,2,0)
    1/2,     -- v_15 α=(0,1,1,1)
    2/3,     -- v_16 α=(0,1,0,2)
    1/2,     -- v_17 α=(0,0,3,0)
    2/3,     -- v_18 α=(0,0,2,1)
    5/6,     -- v_19 α=(0,0,1,2)
    1]       -- v_20 α=(0,0,0,3)

/-- Readout on the cubed manifold recovers `z_11 + z_01/2`, *given* the
  r²-trick invariant `r + u + z_01 + z_11 = 1`. This invariant is preserved
  by r2Field (r2Field_conservative) so it holds for all t ≥ 0 once initial
  state is on the simplex.

  Algebraic derivation: ∂_j (Σ_α v_α) = ∂_j (Σx)^3 = 3(Σx)² so
  Σ_α α_j v_α = 3 x_j (Σx)², giving x_j = (1/3)·Σ_α α_j v_α when Σx = 1. -/
theorem readout_eq_z11_plus_half_z01 (x : Fin 4 → ℝ)
    (hsum : x 0 + x 1 + x 2 + x 3 = 1) :
    ∑ i, readoutCoeff i * cubedLift i x = x 3 + (x 2) / 2 := by
  have key : ∑ i, readoutCoeff i * cubedLift i x
           = (x 0 + x 1 + x 2 + x 3)^2 * (x 3 + (x 2) / 2) := by
    rw [sum_fin_20]
    simp [readoutCoeff, cubedLift]
    ring
  rw [key, hsum]
  ring

/-! ## Step 5 backbone: fixed-point identification

The readout limit `(3 - √5)/6` is the readout `z_11 + z_01/2` evaluated
at the attracting interior fixed point of the CF'24 field.  Solving
the fixed-point system
  a(−2a + 7b − 2c) = 0,
  2a² − 8ab + 16ac − bc = 0,
  ab − 14ac + bc = 0,   a + b + c = 1
for the interior branch (`a ≠ 0`) gives `b = 2/9` and `a, c` as the
two roots of `a² − (7/9)a + 1/81 = 0`, namely `a = (7 ± 3√5)/18`.
The corresponding readouts are `(3 ∓ √5)/6`; the paper identifies
`(3 − √5)/6` as the attracting branch. -/

open Real

/-- The CF'24 target constant `(3 − √5)/6 ≈ 0.1273`. -/
noncomputable def readoutLimit : ℝ := (3 - Real.sqrt 5) / 6

/-- The interior attracting fixed point of `field` in the 3-simplex.
Indexed as `0 ↦ z_00`, `1 ↦ z_01`, `2 ↦ z_11`. -/
noncomputable def fixedPoint : Fin 3 → ℝ
  | ⟨0, _⟩ => (7 + 3 * Real.sqrt 5) / 18
  | ⟨1, _⟩ => 2 / 9
  | ⟨2, _⟩ => (7 - 3 * Real.sqrt 5) / 18

/-- `(√5)² = 5`. -/
private lemma sq_sqrt_five : Real.sqrt 5 * Real.sqrt 5 = 5 := by
  have h5 : (0 : ℝ) ≤ 5 := by norm_num
  calc Real.sqrt 5 * Real.sqrt 5 = (Real.sqrt 5) ^ 2 := by ring
    _ = 5 := Real.sq_sqrt h5

/-- The fixed point lies on the simplex: `z_00 + z_01 + z_11 = 1`. -/
theorem fixedPoint_on_simplex :
    fixedPoint 0 + fixedPoint 1 + fixedPoint 2 = 1 := by
  simp only [fixedPoint]; ring

/-- `field` vanishes at the interior fixed point. -/
theorem field_fixedPoint : field fixedPoint = 0 := by
  funext i
  fin_cases i <;> simp only [field, fixedPoint, Pi.zero_apply]
  · -- z_00 component: a(-2a + 7b - 2c) with b = 2/9, a + c = 7/9, so -2a + 7·(2/9) - 2c = 14/9 - 2(a+c) = 14/9 - 14/9 = 0
    ring
  · -- z_01 component: 2a² - 8ab + 16ac - bc reduces to (7/18)·(5 - √5²) = 0
    have h := sq_sqrt_five
    linear_combination (-7/18 : ℝ) * h
  · -- z_11 component: ab - 14ac + bc reduces to (7/18)·(√5² - 5) = 0
    have h := sq_sqrt_five
    linear_combination (7/18 : ℝ) * h

/-- Readout `z_11 + z_01/2` at the interior fixed point is the target
constant `(3 − √5)/6`. -/
theorem readout_fixedPoint :
    fixedPoint 2 + fixedPoint 1 / 2 = readoutLimit := by
  simp only [fixedPoint, readoutLimit]
  ring

/-! ### The saddle fixed point

The fixed-point system `field x = 0` on the open simplex has **two**
interior solutions, corresponding to the two roots of `a² − (7/9)a + 1/81 = 0`
(see the comment at the top of Section *Lyapunov / fixed-point analysis*).
We name the second one `saddlePoint`.  Linearization shows it has
saddle structure (mixed-sign eigenvalues), so its stable manifold is
1-dimensional in the 2-D simplex phase space — a measure-zero set —
and generic trajectories converge to `fixedPoint`.  The saddle is what
the paper rules out as the *non-attracting* branch (readout `(3 + √5)/6`).

Formalizing the saddle explicitly is useful for:
  * Cf24BasinEntry correctness: the hypothesis presumes `x*` is the unique
    attractor; this is true *generically* (modulo `saddlePoint`'s 1-D
    stable manifold).
  * Future Poincaré–Bendixson-style global-convergence proofs: any such
    proof must rule out trajectories ω-limiting to `saddlePoint`. -/

/-- The interior **saddle** fixed point of `field`: same `b = 2/9`, but
`a` and `c` swapped relative to `fixedPoint`. -/
noncomputable def saddlePoint : Fin 3 → ℝ
  | ⟨0, _⟩ => (7 - 3 * Real.sqrt 5) / 18
  | ⟨1, _⟩ => 2 / 9
  | ⟨2, _⟩ => (7 + 3 * Real.sqrt 5) / 18

theorem saddlePoint_on_simplex :
    saddlePoint 0 + saddlePoint 1 + saddlePoint 2 = 1 := by
  simp only [saddlePoint]; ring

/-- `field` vanishes at the saddle. -/
theorem field_saddlePoint : field saddlePoint = 0 := by
  funext i
  fin_cases i <;> simp only [field, saddlePoint, Pi.zero_apply]
  · ring
  · have h := sq_sqrt_five
    linear_combination (-7/18 : ℝ) * h
  · have h := sq_sqrt_five
    linear_combination (7/18 : ℝ) * h

/-- The saddle's coordinates are strictly positive (interior of simplex). -/
theorem saddlePoint_pos : ∀ i, 0 < saddlePoint i := by
  intro i
  have h5_lt : Real.sqrt 5 < 3 := by
    have : Real.sqrt 5 < Real.sqrt 9 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this.trans_le (le_of_eq (by
      rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.sqrt_sq]; norm_num))
  fin_cases i <;> simp only [saddlePoint]
  · -- (7 - 3√5)/18 > 0 since 3√5 < 9 < 7? No, 3√5 ≈ 6.7 < 7.
    have : 3 * Real.sqrt 5 < 7 := by
      have h5_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
      nlinarith [Real.sqrt_nonneg (5 : ℝ), h5_sq]
    linarith
  · norm_num
  · have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
    have : 0 < 3 * Real.sqrt 5 := by linarith
    linarith

/-- Readout `z_11 + z_01/2` at the saddle is `(3 + √5)/6` — the
**non-target** value that the paper excludes by basin-of-attraction
arguments. -/
theorem readout_saddlePoint :
    saddlePoint 2 + saddlePoint 1 / 2 = (3 + Real.sqrt 5) / 6 := by
  simp only [saddlePoint]
  ring

/-- The two interior fixed points are distinct: their `z_11` components
differ by `√5/3 ≠ 0`. -/
theorem fixedPoint_ne_saddlePoint : fixedPoint ≠ saddlePoint := by
  intro h
  have h2 := congrArg (fun x => x 2) h
  simp only [fixedPoint, saddlePoint] at h2
  have h5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  linarith

/-! ### Readout derivative along trajectories

The scalar quantity `R(t) := z_11(t) + z_01(t)/2` satisfies a
derivative equation expressible purely in the original state.  Using
the field components directly:

  Ṙ  = ż_11 + ż_01/2
     = (z_00·z_01 − 14·z_00·z_11 + z_01·z_11)
       + (z_00² − 4·z_00·z_01 + 8·z_00·z_11 − z_01·z_11/2)
     = z_00² − 3·z_00·z_01 − 6·z_00·z_11 + z_01·z_11/2.

This identity is the bridge from the vector field to a 1-dimensional
attractor analysis on the readout itself. -/

/-- Purely algebraic identity for the readout derivative along `field`
trajectories. -/
theorem readout_deriv_identity (x : Fin 3 → ℝ) :
    field x 2 + field x 1 / 2
      = x 0 * x 0 - 3 * x 0 * x 1 - 6 * x 0 * x 2 + x 1 * x 2 / 2 := by
  simp only [field]; ring

/-- Readout derivative vanishes at the attracting fixed point. -/
theorem readout_deriv_at_fixedPoint :
    field fixedPoint 2 + field fixedPoint 1 / 2 = 0 := by
  rw [readout_deriv_identity]
  have h := sq_sqrt_five
  simp only [fixedPoint]
  linear_combination (7/36 : ℝ) * h

/-! ### Linearization indicators at the fixed point

Reducing the simplex to 2D via `z_00 = 1 − z_01 − z_11`, the
CF'24 field becomes a 2D system in `(u, v) := (z_01, z_11)`.  Direct
computation of the Jacobian at `(b*, c*) = (2/9, (7 − 3√5)/18)` gives

  J = [[(−57 + 5√5)/6, 14√5/3], [(18 − 7√5)/3, −14√5/3]].

Its trace and determinant are
  tr(J) = −(57 + 23√5)/6,
  det(J) = 35 + 49√5/3.

Since `√5 > 0`, `tr(J) < 0` and `det(J) > 0`, so the characteristic
polynomial `λ² − tr(J)·λ + det(J)` has two roots with strictly
negative real part.  This is the algebraic fingerprint of local
asymptotic stability. -/

/-- Trace of the Jacobian at the fixed point. -/
noncomputable def jacobianTrace : ℝ := -(57 + 23 * Real.sqrt 5) / 6

/-- Determinant of the Jacobian at the fixed point. -/
noncomputable def jacobianDet : ℝ := 35 + 49 * Real.sqrt 5 / 3

/-- The trace of the linearization is negative. -/
theorem jacobianTrace_neg : jacobianTrace < 0 := by
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  unfold jacobianTrace
  have hnum : (0 : ℝ) < 57 + 23 * Real.sqrt 5 := by positivity
  linarith

/-- The determinant of the linearization is positive. -/
theorem jacobianDet_pos : 0 < jacobianDet := by
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  unfold jacobianDet
  positivity

/-- Both eigenvalues of the linearization have strictly negative real
part (Routh–Hurwitz for a real 2×2 matrix).

Proof via real/imaginary split of the characteristic equation.  Writing
`z = a + b·i` with `a, b ∈ ℝ`:
  Re: `a² − b² − tr·a + det = 0`,
  Im: `b·(2a − tr) = 0`.
Case `b = 0` (real root): `a² − tr·a + det = 0` gives `tr·a = a² + det > 0`.
Since `tr < 0`, we get `a < 0`.
Case `2a = tr`: `a = tr/2 < 0` directly. -/
theorem eigenvalues_have_negative_real_part :
    ∀ z : ℂ, z * z - (jacobianTrace : ℂ) * z + (jacobianDet : ℂ) = 0 →
      z.re < 0 := by
  intro z hz
  have htr_neg : jacobianTrace < 0 := jacobianTrace_neg
  have hdet_pos : 0 < jacobianDet := jacobianDet_pos
  have h_re := congrArg Complex.re hz
  have h_im := congrArg Complex.im hz
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
             Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.zero_re, Complex.zero_im,
             zero_mul, sub_zero, add_zero] at h_re h_im
  -- h_re: z.re * z.re - z.im * z.im - (jacobianTrace * z.re - 0) + jacobianDet = 0
  -- h_im: (z.re * z.im + z.im * z.re) - (jacobianTrace * z.im + 0 * z.re) = 0
  set a := z.re with ha_def
  set b := z.im with hb_def
  -- From h_im: b * (2a - tr) = 0
  have h_im' : b * (2 * a - jacobianTrace) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp h_im' with hb | ha2
  · -- Case b = 0: z is real, so z.re satisfies the quadratic
    have h_re' : a * a - jacobianTrace * a + jacobianDet = 0 := by
      rw [hb] at h_re; linarith
    -- tr * a = a² + det > 0; since tr < 0, a must be negative
    have h_ta_pos : 0 < jacobianTrace * a := by
      have heq : jacobianTrace * a = a * a + jacobianDet := by linarith
      have : 0 ≤ a * a := mul_self_nonneg a
      linarith
    -- From tr * a > 0 and tr < 0, conclude a < 0
    by_contra hna
    push_neg at hna
    have : jacobianTrace * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt htr_neg) hna
    linarith
  · -- Case 2a = tr: a = tr/2 < 0
    have : a = jacobianTrace / 2 := by linarith
    rw [this]; linarith

/-! ### Quadratic Lyapunov candidate

Rather than solving the Lyapunov equation `J^T P + P J = -I` with
fractional coefficients involving `√5`, we exploit the observation
that for the specific CF'24 system the *symmetrized* Jacobian
`(J + J^T)/2` is already negative definite.  This lets us use the
naive quadratic

  V(b, c) := (b − b*)² + (c − c*)²

directly as a Lyapunov candidate: `V̇|_{linearization} = Δx^T (J + J^T) Δx`
and the matrix `J + J^T` has both eigenvalues negative iff its trace
and determinant are negative and positive respectively.

Computing `J + J^T` at the fixed point:
  (J+J^T)/2 = [[(-57 + 5√5)/6, (18 + 7√5)/6],
               [(18 + 7√5)/6, -14√5/3        ]]

Its trace equals `tr(J) = -(57 + 23√5)/6 < 0` (already proved).
Its determinant is `det(J_sym) = (1344·√5 − 1269)/36`, which is
positive since `√5 > 423/448 ≈ 0.944`. -/

/-- Determinant of the symmetrized Jacobian `(J + J^T)/2` at the
fixed point.  Positive-definiteness of this matrix gives a direct
Lyapunov function without solving a Sylvester equation. -/
noncomputable def jacobianSymDet : ℝ := (1344 * Real.sqrt 5 - 1269) / 36

theorem jacobianSymDet_pos : 0 < jacobianSymDet := by
  unfold jacobianSymDet
  have h5 : (5 : ℝ) = Real.sqrt 5 * Real.sqrt 5 := by
    have : Real.sqrt 5 * Real.sqrt 5 = 5 := sq_sqrt_five
    linarith
  -- 1344·√5 > 1269 iff √5 > 1269/1344 ≈ 0.944.  Use √5 > 2.
  have hsqrt : (2 : ℝ) < Real.sqrt 5 := by
    have h : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    nlinarith [Real.sqrt_nonneg (5 : ℝ), h]
  have : 1344 * Real.sqrt 5 > 1269 := by linarith
  linarith

/-- Quadratic Lyapunov candidate, expressed on the reduced 2D state
`(b, c) = (z_01, z_11)`.  We use the "distance-squared" form, which
works precisely because the symmetrized Jacobian is negative
definite at the fixed point. -/
noncomputable def lyapunov (x : Fin 3 → ℝ) : ℝ :=
  (x 1 - fixedPoint 1)^2 + (x 2 - fixedPoint 2)^2

theorem lyapunov_nonneg (x : Fin 3 → ℝ) : 0 ≤ lyapunov x := by
  unfold lyapunov; positivity

theorem lyapunov_fixedPoint : lyapunov fixedPoint = 0 := by
  unfold lyapunov; simp

/-- The Lyapunov function `V := (b - b*)² + (c - c*)²` is **strictly
positive** at the saddle, with value `5/9`.  Concretely: trajectories
that ω-limit to `saddlePoint` rather than `fixedPoint` would have
`V(traj t) → 5/9`, which is *much larger* than the basin-entry
threshold `1/512 ≈ 0.00195`.  This is precisely the obstruction
that `Cf24BasinEntry` papers over. -/
theorem lyapunov_saddlePoint : lyapunov saddlePoint = 5 / 9 := by
  unfold lyapunov
  simp only [saddlePoint, fixedPoint]
  have h := sq_sqrt_five
  linear_combination (1 / 9 : ℝ) * h

/-! ### Saddle linearization invariants

The (b, c)-projected Jacobian of `field` at `saddlePoint` has the closed form

```
J = ⎡ -(57 + 5√5)/6     -14√5/3       ⎤
    ⎣ (18 + 7√5)/3      14√5/3        ⎦
```

with trace `(−57 + 23√5)/6` and determinant `(105 − 49√5)/3`.  Since
`√5 > 15/7`, we have `49√5 > 105`, so `det J < 0`.  This is the
analytic certificate that `saddlePoint` is a saddle (one positive
eigenvalue, one negative) — its stable manifold is 1-dimensional.

We expose these closed forms as standalone real numbers (free of any
matrix-calculus formalism), as the analytic infrastructure for any
future formal stable-manifold argument.  See `saddleJacobianDet_neg`
below for the key sign-of-determinant inequality. -/

/-- Trace of the (b, c)-projected Jacobian of `field` at `saddlePoint`. -/
noncomputable def saddleJacobianTrace : ℝ := (-57 + 23 * Real.sqrt 5) / 6

/-- Determinant of the (b, c)-projected Jacobian of `field` at `saddlePoint`. -/
noncomputable def saddleJacobianDet : ℝ := (105 - 49 * Real.sqrt 5) / 3

/-- The saddle's Jacobian determinant is negative — analytic confirmation
that `saddlePoint` is a saddle (one stable, one unstable direction).

Key inequality `√5 > 15/7`, i.e., `5 > 225/49`, is `direct`:
`49 * 5 = 245 > 225 = 49 * (15/7)²`. -/
theorem saddleJacobianDet_neg : saddleJacobianDet < 0 := by
  unfold saddleJacobianDet
  -- √5 > 15/7  ⟺  5 > (15/7)² = 225/49.
  have h_sq : (15 / 7 : ℝ)^2 < 5 := by norm_num
  have h_sqrt5_gt : (15 / 7 : ℝ) < Real.sqrt 5 := by
    have h1 : Real.sqrt ((15 / 7)^2) < Real.sqrt 5 :=
      Real.sqrt_lt_sqrt (by positivity) h_sq
    have h2 : Real.sqrt ((15 / 7 : ℝ)^2) = 15 / 7 :=
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 15 / 7)
    linarith [h1, h2.le, h2.ge]
  -- 49 √5 > 49 · 15/7 = 7 · 15 = 105.
  have h_49 : 49 * Real.sqrt 5 > 105 := by linarith
  linarith

/-- Discriminant of the saddle Jacobian's characteristic polynomial:
`Δ = (trace)² − 4·det`.  This is positive (real distinct eigenvalues)
because `det < 0` already forces `Δ ≥ −4·det > 0`. -/
noncomputable def saddleJacobianDiscriminant : ℝ :=
  saddleJacobianTrace^2 - 4 * saddleJacobianDet

theorem saddleJacobianDiscriminant_pos : 0 < saddleJacobianDiscriminant := by
  unfold saddleJacobianDiscriminant
  have hdet := saddleJacobianDet_neg
  have htr_sq : 0 ≤ saddleJacobianTrace^2 := sq_nonneg _
  linarith

/-- Closed form for the discriminant: `Δ = (427 − 135√5)/18 ≈ 6.95`. -/
theorem saddleJacobianDiscriminant_eq :
    saddleJacobianDiscriminant = (427 - 135 * Real.sqrt 5) / 18 := by
  unfold saddleJacobianDiscriminant saddleJacobianTrace saddleJacobianDet
  have h := sq_sqrt_five
  linear_combination (529/36 : ℝ) * h

/-! ### Saddle Jacobian entries — formal partial derivatives

The closed-form values `saddleJacobianTrace` and `saddleJacobianDet` are
defined as standalone reals.  This subsection bridges them to actual
partial derivatives of `field` at `saddlePoint`, via Mathlib's
`HasDerivAt`.  We work on the simplex by substituting `z_00 = 1 − b − c`
into `field`, leaving the Jacobian as a 2×2 matrix in (b, c) coordinates.

The four entries are (closed forms):

```
J = ⎡ −(57 + 5√5)/6     −14√5/3       ⎤
    ⎣ (18 + 7√5)/3      14√5/3        ⎦
```

with `J[0][0] + J[1][1] = (−57 + 23√5)/6 = saddleJacobianTrace` and
`J[0][0]·J[1][1] − J[0][1]·J[1][0] = (105 − 49√5)/3 = saddleJacobianDet`. -/

/-- (b, c)-projected Jacobian entry `(0, 0)`: ∂(field _ 1)/∂b at saddle. -/
noncomputable def saddleJacobian00 : ℝ := -(57 + 5 * Real.sqrt 5) / 6

/-- (b, c)-projected Jacobian entry `(0, 1)`: ∂(field _ 1)/∂c at saddle. -/
noncomputable def saddleJacobian01 : ℝ := -14 * Real.sqrt 5 / 3

/-- (b, c)-projected Jacobian entry `(1, 0)`: ∂(field _ 2)/∂b at saddle. -/
noncomputable def saddleJacobian10 : ℝ := (18 + 7 * Real.sqrt 5) / 3

/-- (b, c)-projected Jacobian entry `(1, 1)`: ∂(field _ 2)/∂c at saddle. -/
noncomputable def saddleJacobian11 : ℝ := 14 * Real.sqrt 5 / 3

/-- Closed-form trace decomposes as the sum of diagonal Jacobian entries. -/
theorem saddleJacobianTrace_eq_sum_diag :
    saddleJacobianTrace = saddleJacobian00 + saddleJacobian11 := by
  unfold saddleJacobianTrace saddleJacobian00 saddleJacobian11
  ring

/-- Closed-form determinant decomposes as `J00·J11 − J01·J10`. -/
theorem saddleJacobianDet_eq_2x2 :
    saddleJacobianDet
      = saddleJacobian00 * saddleJacobian11 - saddleJacobian01 * saddleJacobian10 := by
  unfold saddleJacobianDet saddleJacobian00 saddleJacobian01
        saddleJacobian10 saddleJacobian11
  have h := sq_sqrt_five
  linear_combination (-7 : ℝ) * h

/-- The 0-th coordinate of the simplex parametrization `(b, c) ↦ (1−b−c, b, c)`
has derivative −1 in `b` (with `c` fixed). -/
private theorem hasDerivAt_simplex_z00_in_b (c b : ℝ) :
    HasDerivAt (fun b' : ℝ => 1 - b' - c) (-1) b := by
  have h_eq : (fun b' : ℝ => 1 - b' - c) = (fun b' => (1 - c) - b') := by
    funext; ring
  rw [h_eq]
  simpa using (hasDerivAt_const b (1 - c)).sub (hasDerivAt_id b)

/-- The 0-th coordinate of the simplex parametrization has derivative −1
in `c` (with `b` fixed). -/
private theorem hasDerivAt_simplex_z00_in_c (b c : ℝ) :
    HasDerivAt (fun c' : ℝ => 1 - b - c') (-1) c := by
  have h_eq : (fun c' : ℝ => 1 - b - c') = (fun c' => (1 - b) - c') := by
    funext; ring
  rw [h_eq]
  simpa using (hasDerivAt_const c (1 - b)).sub (hasDerivAt_id c)

/-- **(0,0) entry of the saddle Jacobian.** ∂(field _ 1)/∂b, with
`z_00 = 1 − b − c` and `z_11 = saddlePoint 2`, evaluated at `b = 2/9`.
Closed-form value `−(57 + 5√5)/6`. -/
theorem hasDerivAt_field1_in_b_at_saddle :
    HasDerivAt
      (fun b => field (fun i => match i with
        | ⟨0, _⟩ => 1 - b - saddlePoint 2
        | ⟨1, _⟩ => b
        | ⟨2, _⟩ => saddlePoint 2) 1)
      saddleJacobian00
      (saddlePoint 1) := by
  -- Expand `field _ 1` as a polynomial in `b` (with `c := saddlePoint 2` constant):
  --   f(b) = 10·b² + (-12 - 5·c)·b + (2 + 12·c - 14·c²).
  have h_eq : (fun b => field (fun i => match i with
        | ⟨0, _⟩ => 1 - b - saddlePoint 2
        | ⟨1, _⟩ => b
        | ⟨2, _⟩ => saddlePoint 2) 1)
      = (fun b => 10 * b^2 + (-12 - 5 * saddlePoint 2) * b
                  + (2 + 12 * saddlePoint 2 - 14 * saddlePoint 2^2)) := by
    funext b; simp [field]; ring
  rw [h_eq]
  -- Differentiate term-by-term.
  have h_pow := (hasDerivAt_pow 2 (saddlePoint 1)).const_mul (10 : ℝ)
  have h_lin := (hasDerivAt_id (saddlePoint 1)).const_mul (-12 - 5 * saddlePoint 2)
  have h_const :
      HasDerivAt (fun _ : ℝ => 2 + 12 * saddlePoint 2 - 14 * saddlePoint 2^2) 0
        (saddlePoint 1) := hasDerivAt_const _ _
  have h_sum := (h_pow.add h_lin).add h_const
  convert h_sum using 1
  -- Goal: saddleJacobian00 = (10 · 2 · b * b^(2-1)) + (-12 - 5c) + 0 at saddle.
  unfold saddleJacobian00
  have hb : saddlePoint 1 = 2/9 := by simp [saddlePoint]
  have hc : saddlePoint 2 = (7 + 3 * Real.sqrt 5) / 18 := by simp [saddlePoint]
  rw [hb, hc]; push_cast; ring

/-- **(0,1) entry of the saddle Jacobian.** ∂(field _ 1)/∂c, with
`z_00 = 1 − saddlePoint 1 − c` and `z_01 = saddlePoint 1`, evaluated at
`c = saddlePoint 2`.  Closed-form value `−14√5/3`. -/
theorem hasDerivAt_field1_in_c_at_saddle :
    HasDerivAt
      (fun c => field (fun i => match i with
        | ⟨0, _⟩ => 1 - saddlePoint 1 - c
        | ⟨1, _⟩ => saddlePoint 1
        | ⟨2, _⟩ => c) 1)
      saddleJacobian01
      (saddlePoint 2) := by
  -- Expand `field _ 1` as a polynomial in `c` (with `b := saddlePoint 1` constant):
  --   f(c) = -14·c² + (12 - 5·b)·c + const(b).
  have h_eq : (fun c => field (fun i => match i with
        | ⟨0, _⟩ => 1 - saddlePoint 1 - c
        | ⟨1, _⟩ => saddlePoint 1
        | ⟨2, _⟩ => c) 1)
      = (fun c => -14 * c^2 + (12 - 5 * saddlePoint 1) * c
                  + (2 * (1 - saddlePoint 1)^2 - 8 * saddlePoint 1 * (1 - saddlePoint 1))) := by
    funext c; simp [field]; ring
  rw [h_eq]
  have h_pow := (hasDerivAt_pow 2 (saddlePoint 2)).const_mul (-14 : ℝ)
  have h_lin := (hasDerivAt_id (saddlePoint 2)).const_mul (12 - 5 * saddlePoint 1)
  have h_const :
      HasDerivAt (fun _ : ℝ =>
        2 * (1 - saddlePoint 1)^2 - 8 * saddlePoint 1 * (1 - saddlePoint 1)) 0
        (saddlePoint 2) := hasDerivAt_const _ _
  have h_sum := (h_pow.add h_lin).add h_const
  convert h_sum using 1
  unfold saddleJacobian01
  have hb : saddlePoint 1 = 2/9 := by simp [saddlePoint]
  have hc : saddlePoint 2 = (7 + 3 * Real.sqrt 5) / 18 := by simp [saddlePoint]
  rw [hb, hc]; push_cast; ring

/-- **(1,0) entry of the saddle Jacobian.** ∂(field _ 2)/∂b, with
`z_00 = 1 − b − saddlePoint 2` and `z_11 = saddlePoint 2`, evaluated at
`b = saddlePoint 1`.  Closed-form value `(18 + 7√5)/3`. -/
theorem hasDerivAt_field2_in_b_at_saddle :
    HasDerivAt
      (fun b => field (fun i => match i with
        | ⟨0, _⟩ => 1 - b - saddlePoint 2
        | ⟨1, _⟩ => b
        | ⟨2, _⟩ => saddlePoint 2) 2)
      saddleJacobian10
      (saddlePoint 1) := by
  -- Expand `field _ 2` as a polynomial in `b` (with `c := saddlePoint 2` constant):
  --   f(b) = -b² + (1 + 14·c)·b + const(c).
  have h_eq : (fun b => field (fun i => match i with
        | ⟨0, _⟩ => 1 - b - saddlePoint 2
        | ⟨1, _⟩ => b
        | ⟨2, _⟩ => saddlePoint 2) 2)
      = (fun b => -1 * b^2 + (1 + 14 * saddlePoint 2) * b
                  + (14 * saddlePoint 2^2 - 14 * saddlePoint 2)) := by
    funext b; simp [field]; ring
  rw [h_eq]
  have h_pow := (hasDerivAt_pow 2 (saddlePoint 1)).const_mul (-1 : ℝ)
  have h_lin := (hasDerivAt_id (saddlePoint 1)).const_mul (1 + 14 * saddlePoint 2)
  have h_const :
      HasDerivAt (fun _ : ℝ => 14 * saddlePoint 2^2 - 14 * saddlePoint 2) 0
        (saddlePoint 1) := hasDerivAt_const _ _
  have h_sum := (h_pow.add h_lin).add h_const
  convert h_sum using 1
  unfold saddleJacobian10
  have hb : saddlePoint 1 = 2/9 := by simp [saddlePoint]
  have hc : saddlePoint 2 = (7 + 3 * Real.sqrt 5) / 18 := by simp [saddlePoint]
  rw [hb, hc]; push_cast; ring

/-- **(1,1) entry of the saddle Jacobian.** ∂(field _ 2)/∂c, with
`z_00 = 1 − saddlePoint 1 − c` and `z_01 = saddlePoint 1`, evaluated at
`c = saddlePoint 2`.  Closed-form value `14√5/3`. -/
theorem hasDerivAt_field2_in_c_at_saddle :
    HasDerivAt
      (fun c => field (fun i => match i with
        | ⟨0, _⟩ => 1 - saddlePoint 1 - c
        | ⟨1, _⟩ => saddlePoint 1
        | ⟨2, _⟩ => c) 2)
      saddleJacobian11
      (saddlePoint 2) := by
  -- Expand `field _ 2` as a polynomial in `c` (with `b := saddlePoint 1` constant):
  --   f(c) = 14·c² - 14·(1-b)·c + b·(1-b).
  have h_eq : (fun c => field (fun i => match i with
        | ⟨0, _⟩ => 1 - saddlePoint 1 - c
        | ⟨1, _⟩ => saddlePoint 1
        | ⟨2, _⟩ => c) 2)
      = (fun c => 14 * c^2 + (-14 * (1 - saddlePoint 1)) * c
                  + saddlePoint 1 * (1 - saddlePoint 1)) := by
    funext c; simp [field]; ring
  rw [h_eq]
  have h_pow := (hasDerivAt_pow 2 (saddlePoint 2)).const_mul (14 : ℝ)
  have h_lin := (hasDerivAt_id (saddlePoint 2)).const_mul (-14 * (1 - saddlePoint 1))
  have h_const :
      HasDerivAt (fun _ : ℝ => saddlePoint 1 * (1 - saddlePoint 1)) 0
        (saddlePoint 2) := hasDerivAt_const _ _
  have h_sum := (h_pow.add h_lin).add h_const
  convert h_sum using 1
  unfold saddleJacobian11
  have hb : saddlePoint 1 = 2/9 := by simp [saddlePoint]
  have hc : saddlePoint 2 = (7 + 3 * Real.sqrt 5) / 18 := by simp [saddlePoint]
  rw [hb, hc]; push_cast; ring

/-! ### Saddle Jacobian eigenvalues

With trace `T = (−57 + 23√5)/6 < 0` and determinant `D = (105 − 49√5)/3 < 0`,
the eigenvalues `λ± = (T ± √Δ)/2` (where `Δ = T² − 4D > 0`) have product `D < 0`,
hence opposite signs.  Below we expose `λ+ > 0` and `λ- < 0` — the analytic
certificate that `saddlePoint` is a saddle with a 1-D unstable direction
(eigenvector for `λ+`) and a 1-D stable direction (eigenvector for `λ-`). -/

/-- Positive eigenvalue of the saddle Jacobian. -/
noncomputable def saddleEigenvaluePositive : ℝ :=
  (saddleJacobianTrace + Real.sqrt saddleJacobianDiscriminant) / 2

/-- Negative eigenvalue of the saddle Jacobian. -/
noncomputable def saddleEigenvalueNegative : ℝ :=
  (saddleJacobianTrace - Real.sqrt saddleJacobianDiscriminant) / 2

/-- The discriminant strictly exceeds the squared trace (because `det < 0`). -/
theorem saddleJacobianDiscriminant_gt_traceSq :
    saddleJacobianTrace^2 < saddleJacobianDiscriminant := by
  unfold saddleJacobianDiscriminant
  have hdet := saddleJacobianDet_neg
  linarith

/-- `√Δ > |saddleJacobianTrace|`. -/
theorem sqrt_saddleJacobianDiscriminant_gt_abs_trace :
    |saddleJacobianTrace| < Real.sqrt saddleJacobianDiscriminant := by
  have h_sq : saddleJacobianTrace^2 < saddleJacobianDiscriminant :=
    saddleJacobianDiscriminant_gt_traceSq
  have h_sqrt_lt : Real.sqrt (saddleJacobianTrace^2) < Real.sqrt saddleJacobianDiscriminant :=
    Real.sqrt_lt_sqrt (sq_nonneg _) h_sq
  have h_sqrt_eq : Real.sqrt (saddleJacobianTrace^2) = |saddleJacobianTrace| :=
    Real.sqrt_sq_eq_abs _
  linarith

/-- The positive saddle eigenvalue is strictly positive. -/
theorem saddleEigenvaluePositive_pos : 0 < saddleEigenvaluePositive := by
  unfold saddleEigenvaluePositive
  have h := sqrt_saddleJacobianDiscriminant_gt_abs_trace
  have h_abs_le : -Real.sqrt saddleJacobianDiscriminant < saddleJacobianTrace := by
    have := abs_lt.mp h
    linarith [this.1]
  linarith

/-- The negative saddle eigenvalue is strictly negative. -/
theorem saddleEigenvalueNegative_neg : saddleEigenvalueNegative < 0 := by
  unfold saddleEigenvalueNegative
  have h := sqrt_saddleJacobianDiscriminant_gt_abs_trace
  have h_abs_lt : saddleJacobianTrace < Real.sqrt saddleJacobianDiscriminant := by
    have := abs_lt.mp h
    linarith [this.2]
  linarith

/-- Sum of saddle eigenvalues equals the trace. -/
theorem saddleEigenvalues_sum :
    saddleEigenvaluePositive + saddleEigenvalueNegative = saddleJacobianTrace := by
  unfold saddleEigenvaluePositive saddleEigenvalueNegative; ring

/-- Product of saddle eigenvalues equals the determinant. -/
theorem saddleEigenvalues_prod :
    saddleEigenvaluePositive * saddleEigenvalueNegative = saddleJacobianDet := by
  unfold saddleEigenvaluePositive saddleEigenvalueNegative
  set s := Real.sqrt saddleJacobianDiscriminant with hs
  have hΔ_pos : 0 ≤ saddleJacobianDiscriminant := saddleJacobianDiscriminant_pos.le
  have hs_sq : s^2 = saddleJacobianDiscriminant := Real.sq_sqrt hΔ_pos
  have h_alg :
      (saddleJacobianTrace + s) / 2 * ((saddleJacobianTrace - s) / 2)
        = (saddleJacobianTrace^2 - s^2) / 4 := by ring
  rw [h_alg, hs_sq]
  unfold saddleJacobianDiscriminant
  ring

/-- The positive eigenvalue annihilates the characteristic polynomial `x² − T·x + D`. -/
theorem saddleEigenvaluePositive_charPoly :
    saddleEigenvaluePositive^2 - saddleJacobianTrace * saddleEigenvaluePositive
      + saddleJacobianDet = 0 := by
  have h_sum := saddleEigenvalues_sum
  have h_prod := saddleEigenvalues_prod
  linear_combination saddleEigenvaluePositive * h_sum - h_prod

/-- The negative eigenvalue annihilates the characteristic polynomial `x² − T·x + D`. -/
theorem saddleEigenvalueNegative_charPoly :
    saddleEigenvalueNegative^2 - saddleJacobianTrace * saddleEigenvalueNegative
      + saddleJacobianDet = 0 := by
  have h_sum := saddleEigenvalues_sum
  have h_prod := saddleEigenvalues_prod
  linear_combination saddleEigenvalueNegative * h_sum - h_prod

/-- Spectral gap: `λ_+ − λ_- = √Δ > 0`.  This is the contraction-rate
margin used by graph-transform / Hartman-Grobman arguments. -/
theorem saddleEigenvalues_gap :
    saddleEigenvaluePositive - saddleEigenvalueNegative
      = Real.sqrt saddleJacobianDiscriminant := by
  unfold saddleEigenvaluePositive saddleEigenvalueNegative
  ring

/-- Spectral gap is strictly positive. -/
theorem saddleEigenvalues_gap_pos :
    0 < saddleEigenvaluePositive - saddleEigenvalueNegative := by
  rw [saddleEigenvalues_gap]
  exact Real.sqrt_pos.mpr saddleJacobianDiscriminant_pos

/-! ### Saddle Jacobian eigenvectors

Working in the (b, c) chart projected from the simplex, we use the standard
column-eigenvector form `(J01, λ − J00)` (which is well-defined since
`J01 = −14√5/3 ≠ 0`).  The eigenvalue equation `J · v = λ · v` reduces, after
expanding and applying the trace/determinant Vieta relations, to
`λ² − T·λ + D = 0`, which is precisely `saddleEigenvalue{Positive,Negative}_charPoly`. -/

/-- Eigenvector for the negative (stable) eigenvalue, in the `(b, c)` chart. -/
noncomputable def saddleStableVec : ℝ × ℝ :=
  (saddleJacobian01, saddleEigenvalueNegative - saddleJacobian00)

/-- Eigenvector for the positive (unstable) eigenvalue, in the `(b, c)` chart. -/
noncomputable def saddleUnstableVec : ℝ × ℝ :=
  (saddleJacobian01, saddleEigenvaluePositive - saddleJacobian00)

/-- `J01 ≠ 0`, hence both eigenvectors are nonzero in their first component. -/
theorem saddleJacobian01_ne_zero : saddleJacobian01 ≠ 0 := by
  unfold saddleJacobian01
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  have : Real.sqrt 5 = 0 := by linarith
  linarith

/-- Top row of the eigenvalue equation for the stable eigenvector. -/
theorem saddleStableVec_row0 :
    saddleJacobian00 * saddleStableVec.1 + saddleJacobian01 * saddleStableVec.2
      = saddleEigenvalueNegative * saddleStableVec.1 := by
  unfold saddleStableVec; ring

/-- Bottom row of the eigenvalue equation for the stable eigenvector. -/
theorem saddleStableVec_row1 :
    saddleJacobian10 * saddleStableVec.1 + saddleJacobian11 * saddleStableVec.2
      = saddleEigenvalueNegative * saddleStableVec.2 := by
  unfold saddleStableVec
  have h_charPoly := saddleEigenvalueNegative_charPoly
  have h_trace := saddleJacobianTrace_eq_sum_diag
  have h_det := saddleJacobianDet_eq_2x2
  -- After substituting v = (J01, λ - J00), the row reads
  --   J10 · J01 + J11 · (λ - J00) = λ · (λ - J00)
  -- which rearranges via det = J00·J11 - J01·J10 and T = J00 + J11 to charPoly.
  linear_combination (-1) * h_charPoly - saddleEigenvalueNegative * h_trace + h_det

/-- Top row of the eigenvalue equation for the unstable eigenvector. -/
theorem saddleUnstableVec_row0 :
    saddleJacobian00 * saddleUnstableVec.1 + saddleJacobian01 * saddleUnstableVec.2
      = saddleEigenvaluePositive * saddleUnstableVec.1 := by
  unfold saddleUnstableVec; ring

/-- Bottom row of the eigenvalue equation for the unstable eigenvector. -/
theorem saddleUnstableVec_row1 :
    saddleJacobian10 * saddleUnstableVec.1 + saddleJacobian11 * saddleUnstableVec.2
      = saddleEigenvaluePositive * saddleUnstableVec.2 := by
  unfold saddleUnstableVec
  have h_charPoly := saddleEigenvaluePositive_charPoly
  have h_trace := saddleJacobianTrace_eq_sum_diag
  have h_det := saddleJacobianDet_eq_2x2
  linear_combination (-1) * h_charPoly - saddleEigenvaluePositive * h_trace + h_det

/-- The stable eigenvector is nonzero (since `J01 ≠ 0`). -/
theorem saddleStableVec_ne_zero : saddleStableVec ≠ (0, 0) := by
  intro h
  have h1 : saddleStableVec.1 = 0 := by rw [h]
  exact saddleJacobian01_ne_zero h1

/-- The unstable eigenvector is nonzero. -/
theorem saddleUnstableVec_ne_zero : saddleUnstableVec ≠ (0, 0) := by
  intro h
  have h1 : saddleUnstableVec.1 = 0 := by rw [h]
  exact saddleJacobian01_ne_zero h1

/-- The two eigenvectors are linearly independent (their `2×2` determinant is nonzero):
    `det [v_s | v_u] = J01 · √Δ ≠ 0`. -/
theorem saddleEigenvecs_linearIndep :
    saddleStableVec.1 * saddleUnstableVec.2 - saddleUnstableVec.1 * saddleStableVec.2
      = saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant := by
  unfold saddleStableVec saddleUnstableVec saddleEigenvalueNegative saddleEigenvaluePositive
  ring

/-! ### Taylor expansion of `field` at the saddle

Since `field` is a homogeneous quadratic vector field, the Taylor expansion at
any point is exact through the second-order term.  Below we record the explicit
identities for the `(b, c)`-projected components at `saddlePoint`:

  field_1(saddle + (−u−v, u, v)) = J00·u + J01·v + 10·u² − 5·u·v − 14·v²
  field_2(saddle + (−u−v, u, v)) = J10·u + J11·v −  u² + 14·v² + 14·u·v

where `(u, v)` is the perturbation in the `(b, c)` chart and the `x₀`-component
moves by `−u − v` to preserve `∑ xᵢ = 1`.  These are the analytic certificates
that `J` is the **actual** linearization of `field` at `saddlePoint`. -/

/-- Exact second-order Taylor identity for `field 1` at the saddle. -/
theorem field1_taylor_at_saddle (u v : ℝ) :
    field (fun i : Fin 3 => match i with
      | ⟨0, _⟩ => saddlePoint 0 - u - v
      | ⟨1, _⟩ => saddlePoint 1 + u
      | ⟨2, _⟩ => saddlePoint 2 + v) 1
      = saddleJacobian00 * u + saddleJacobian01 * v
        + 10 * u^2 - 5 * u * v - 14 * v^2 := by
  simp only [field, saddlePoint, saddleJacobian00, saddleJacobian01]
  have h := sq_sqrt_five
  linear_combination (-7/18 : ℝ) * h

/-- Exact second-order Taylor identity for `field 2` at the saddle. -/
theorem field2_taylor_at_saddle (u v : ℝ) :
    field (fun i : Fin 3 => match i with
      | ⟨0, _⟩ => saddlePoint 0 - u - v
      | ⟨1, _⟩ => saddlePoint 1 + u
      | ⟨2, _⟩ => saddlePoint 2 + v) 2
      = saddleJacobian10 * u + saddleJacobian11 * v
        - u^2 + 14 * v^2 + 14 * u * v := by
  simp only [field, saddlePoint, saddleJacobian10, saddleJacobian11]
  have h := sq_sqrt_five
  linear_combination (7/18 : ℝ) * h

/-! ### Quadratic Lipschitz remainder bounds

The Taylor identities give an explicit constant Hessian.  Below we record the
operator norm bounds `|H_i(u, v)| ≤ C_i · (u² + v²)` that any Hartman-Grobman /
graph-transform argument requires for the nonlinear remainder.

For the field_1 quadratic `Q_1 = 10u² − 5uv − 14v²`, the bound `|Q_1| ≤ (33/2)·(u²+v²)`
follows from sum-of-squares decompositions:
  (33/2)·(u²+v²) − Q_1 = 4u² + (5/2)·(u+v)² + 28v²  ≥ 0
  (33/2)·(u²+v²) + Q_1 = 24u² + (5/2)·(u−v)²        ≥ 0

For the field_2 quadratic `Q_2 = -u² + 14v² + 14uv`, the bound `|Q_2| ≤ 21·(u²+v²)`
follows from:
  21·(u²+v²) − Q_2 = 22u² + 7v² − 14uv = 7(u−v)² + 15u²  ≥ 0
  21·(u²+v²) + Q_2 = 20u² + 35v² + 14uv = 7(u+v)² + 13u² + 28v²  ≥ 0 -/

/-- Upper bound on the field_1 quadratic remainder. -/
theorem field1_taylor_remainder_bound (u v : ℝ) :
    10 * u^2 - 5 * u * v - 14 * v^2 ≤ (33/2) * (u^2 + v^2) := by
  linarith [sq_nonneg (u + v), sq_nonneg u, sq_nonneg v, sq_nonneg (u - v)]

/-- Lower bound on the field_1 quadratic remainder. -/
theorem field1_taylor_remainder_bound_neg (u v : ℝ) :
    -((33/2) * (u^2 + v^2)) ≤ 10 * u^2 - 5 * u * v - 14 * v^2 := by
  linarith [sq_nonneg (u + v), sq_nonneg u, sq_nonneg v, sq_nonneg (u - v)]

/-- Two-sided bound on the field_1 quadratic remainder: `|Q_1| ≤ (33/2)·(u²+v²)`. -/
theorem field1_taylor_remainder_abs (u v : ℝ) :
    |10 * u^2 - 5 * u * v - 14 * v^2| ≤ (33/2) * (u^2 + v^2) := by
  rw [abs_le]
  exact ⟨field1_taylor_remainder_bound_neg u v, field1_taylor_remainder_bound u v⟩

/-- Upper bound on the field_2 quadratic remainder. -/
theorem field2_taylor_remainder_bound (u v : ℝ) :
    -u^2 + 14 * v^2 + 14 * u * v ≤ 21 * (u^2 + v^2) := by
  linarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]

/-- Lower bound on the field_2 quadratic remainder. -/
theorem field2_taylor_remainder_bound_neg (u v : ℝ) :
    -(21 * (u^2 + v^2)) ≤ -u^2 + 14 * v^2 + 14 * u * v := by
  linarith [sq_nonneg (u + v), sq_nonneg u, sq_nonneg v]

/-- Two-sided bound on the field_2 quadratic remainder: `|Q_2| ≤ 21·(u²+v²)`. -/
theorem field2_taylor_remainder_abs (u v : ℝ) :
    |-u^2 + 14 * v^2 + 14 * u * v| ≤ 21 * (u^2 + v^2) := by
  rw [abs_le]
  exact ⟨field2_taylor_remainder_bound_neg u v, field2_taylor_remainder_bound u v⟩

/-! ### Saddle Jacobian as a linear endomorphism of `ℝ × ℝ` -/

/-- The saddle Jacobian as a linear function on `ℝ × ℝ`, in `(b, c)` coordinates. -/
noncomputable def saddleJacobianApply (p : ℝ × ℝ) : ℝ × ℝ :=
  (saddleJacobian00 * p.1 + saddleJacobian01 * p.2,
   saddleJacobian10 * p.1 + saddleJacobian11 * p.2)

/-- Eigen-equation in vector form: `J · v_s = λ_- · v_s`. -/
theorem saddleJacobianApply_stableVec :
    saddleJacobianApply saddleStableVec
      = (saddleEigenvalueNegative * saddleStableVec.1,
         saddleEigenvalueNegative * saddleStableVec.2) := by
  ext
  · exact saddleStableVec_row0
  · exact saddleStableVec_row1

/-- Eigen-equation in vector form: `J · v_u = λ_+ · v_u`. -/
theorem saddleJacobianApply_unstableVec :
    saddleJacobianApply saddleUnstableVec
      = (saddleEigenvaluePositive * saddleUnstableVec.1,
         saddleEigenvaluePositive * saddleUnstableVec.2) := by
  ext
  · exact saddleUnstableVec_row0
  · exact saddleUnstableVec_row1

/-- Linearity: scalar multiplication factors through `saddleJacobianApply`. -/
theorem saddleJacobianApply_smul (c : ℝ) (p : ℝ × ℝ) :
    saddleJacobianApply (c * p.1, c * p.2)
      = (c * (saddleJacobianApply p).1, c * (saddleJacobianApply p).2) := by
  unfold saddleJacobianApply
  ext <;> ring

/-- Linearity: addition factors through `saddleJacobianApply`. -/
theorem saddleJacobianApply_add (p q : ℝ × ℝ) :
    saddleJacobianApply (p.1 + q.1, p.2 + q.2)
      = ((saddleJacobianApply p).1 + (saddleJacobianApply q).1,
         (saddleJacobianApply p).2 + (saddleJacobianApply q).2) := by
  unfold saddleJacobianApply
  ext <;> ring

/-- `saddleJacobianApply 0 = 0`. -/
@[simp] theorem saddleJacobianApply_zero :
    saddleJacobianApply (0, 0) = (0, 0) := by
  unfold saddleJacobianApply
  ext <;> ring

/-- The saddle Jacobian as an `ℝ`-linear map `ℝ × ℝ →ₗ[ℝ] ℝ × ℝ`.  This
form unlocks Mathlib's linear-algebra machinery (operator norms, range,
kernel, eigenspaces) for downstream graph-transform / spectral-theory
arguments. -/
noncomputable def saddleJacobianLinearMap : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := saddleJacobianApply
  map_add' p q := by
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    show saddleJacobianApply (p1 + q1, p2 + q2)
        = saddleJacobianApply (p1, p2) + saddleJacobianApply (q1, q2)
    rw [saddleJacobianApply_add (p1, p2) (q1, q2)]
    rfl
  map_smul' c p := by
    obtain ⟨p1, p2⟩ := p
    show saddleJacobianApply (c * p1, c * p2)
        = c • saddleJacobianApply (p1, p2)
    rw [saddleJacobianApply_smul c (p1, p2)]
    rfl

@[simp] theorem saddleJacobianLinearMap_apply (p : ℝ × ℝ) :
    saddleJacobianLinearMap p = saddleJacobianApply p := rfl

/-- The saddle Jacobian as a continuous `ℝ`-linear map.  Continuity is
automatic from finite dimensionality of `ℝ × ℝ`.  This unlocks
`‖saddleJacobianCLM‖` (operator norm), used as the linear-contraction
constant in graph-transform constructions. -/
noncomputable def saddleJacobianCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  saddleJacobianLinearMap.toContinuousLinearMap

@[simp] theorem saddleJacobianCLM_apply (p : ℝ × ℝ) :
    saddleJacobianCLM p = saddleJacobianApply p := rfl

/-! ### Stable / unstable subspaces (1-D) and J-invariance

For graph-transform stable-manifold work the next layer of structure is the
splitting `ℝ² = E_s ⊕ E_u` into 1-D `J`-invariant subspaces.  We package the
eigenlines `span ℝ {v_s}` and `span ℝ {v_u}` as Mathlib `Submodule`s. -/

/-- The stable subspace `E_s = span_ℝ {v_s}` (1-dimensional). -/
noncomputable def saddleStableSubspace : Submodule ℝ (ℝ × ℝ) :=
  Submodule.span ℝ {saddleStableVec}

/-- The unstable subspace `E_u = span_ℝ {v_u}` (1-dimensional). -/
noncomputable def saddleUnstableSubspace : Submodule ℝ (ℝ × ℝ) :=
  Submodule.span ℝ {saddleUnstableVec}

theorem saddleStableVec_mem_stableSubspace :
    saddleStableVec ∈ saddleStableSubspace :=
  Submodule.mem_span_singleton_self _

theorem saddleUnstableVec_mem_unstableSubspace :
    saddleUnstableVec ∈ saddleUnstableSubspace :=
  Submodule.mem_span_singleton_self _

/-- `saddleJacobianLinearMap v_s = λ_- • v_s`. -/
theorem saddleJacobianLinearMap_smul_stableVec :
    saddleJacobianLinearMap saddleStableVec
      = saddleEigenvalueNegative • saddleStableVec := by
  show saddleJacobianApply saddleStableVec = _
  rw [saddleJacobianApply_stableVec]
  ext <;> simp [Prod.smul_def, smul_eq_mul]

/-- `saddleJacobianLinearMap v_u = λ_+ • v_u`. -/
theorem saddleJacobianLinearMap_smul_unstableVec :
    saddleJacobianLinearMap saddleUnstableVec
      = saddleEigenvaluePositive • saddleUnstableVec := by
  show saddleJacobianApply saddleUnstableVec = _
  rw [saddleJacobianApply_unstableVec]
  ext <;> simp [Prod.smul_def, smul_eq_mul]

/-- `J`-invariance of the stable subspace: `J(E_s) ⊆ E_s`. -/
theorem saddleStableSubspace_invariant (p : ℝ × ℝ)
    (hp : p ∈ saddleStableSubspace) :
    saddleJacobianLinearMap p ∈ saddleStableSubspace := by
  rw [saddleStableSubspace, Submodule.mem_span_singleton] at hp
  obtain ⟨c, rfl⟩ := hp
  rw [LinearMap.map_smul, saddleJacobianLinearMap_smul_stableVec, smul_smul]
  exact Submodule.smul_mem _ _ saddleStableVec_mem_stableSubspace

/-- `J`-invariance of the unstable subspace: `J(E_u) ⊆ E_u`. -/
theorem saddleUnstableSubspace_invariant (p : ℝ × ℝ)
    (hp : p ∈ saddleUnstableSubspace) :
    saddleJacobianLinearMap p ∈ saddleUnstableSubspace := by
  rw [saddleUnstableSubspace, Submodule.mem_span_singleton] at hp
  obtain ⟨c, rfl⟩ := hp
  rw [LinearMap.map_smul, saddleJacobianLinearMap_smul_unstableVec, smul_smul]
  exact Submodule.smul_mem _ _ saddleUnstableVec_mem_unstableSubspace

/-- Eigenline invariance under linearization: `J · (c · v_s) = (c · λ_-) · v_s`. -/
theorem saddleJacobianApply_smul_stableVec (c : ℝ) :
    saddleJacobianApply (c * saddleStableVec.1, c * saddleStableVec.2)
      = (c * saddleEigenvalueNegative * saddleStableVec.1,
         c * saddleEigenvalueNegative * saddleStableVec.2) := by
  rw [saddleJacobianApply_smul]
  rw [saddleJacobianApply_stableVec]
  ext <;> ring

/-- Eigenline invariance under linearization: `J · (c · v_u) = (c · λ_+) · v_u`. -/
theorem saddleJacobianApply_smul_unstableVec (c : ℝ) :
    saddleJacobianApply (c * saddleUnstableVec.1, c * saddleUnstableVec.2)
      = (c * saddleEigenvaluePositive * saddleUnstableVec.1,
         c * saddleEigenvaluePositive * saddleUnstableVec.2) := by
  rw [saddleJacobianApply_smul]
  rw [saddleJacobianApply_unstableVec]
  ext <;> ring

/-! ### Change of basis to eigencoordinates

The 2×2 matrix `[v_s | v_u]` has determinant `J01 · √Δ ≠ 0`, so eigenvectors
form a basis.  This subsection records the explicit change-of-basis maps:
- forward: `(c, d) ↦ c·v_s + d·v_u`,
- backward: `p ↦ (saddleEigenCoord p)`,
both inverse to each other.  In eigencoordinates the linearization
diagonalizes to `(c, d) ↦ (λ_-·c, λ_+·d)`. -/

/-- Determinant of the eigenbasis matrix `[v_s | v_u]`. -/
noncomputable def saddleEigenDet : ℝ :=
  saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant

theorem saddleEigenDet_eq :
    saddleEigenDet
      = saddleStableVec.1 * saddleUnstableVec.2
          - saddleUnstableVec.1 * saddleStableVec.2 :=
  (saddleEigenvecs_linearIndep).symm

theorem saddleEigenDet_ne_zero : saddleEigenDet ≠ 0 := by
  unfold saddleEigenDet
  refine mul_ne_zero saddleJacobian01_ne_zero ?_
  exact (Real.sqrt_pos.mpr saddleJacobianDiscriminant_pos).ne'

/-- Eigencoordinates: write `p` as `c·v_s + d·v_u` and return `(c, d)`. -/
noncomputable def saddleEigenCoord (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 * saddleUnstableVec.2 - p.2 * saddleUnstableVec.1) / saddleEigenDet,
   (p.2 * saddleStableVec.1 - p.1 * saddleStableVec.2) / saddleEigenDet)

/-- Inverse direction: given eigencoordinates `(c, d)`, the corresponding
point is `c·v_s + d·v_u`. -/
noncomputable def saddleFromEigenCoord (cd : ℝ × ℝ) : ℝ × ℝ :=
  (cd.1 * saddleStableVec.1 + cd.2 * saddleUnstableVec.1,
   cd.1 * saddleStableVec.2 + cd.2 * saddleUnstableVec.2)

/-- Forward × backward: `saddleEigenCoord ∘ saddleFromEigenCoord = id`. -/
theorem saddleEigenCoord_saddleFromEigenCoord (cd : ℝ × ℝ) :
    saddleEigenCoord (saddleFromEigenCoord cd) = cd := by
  obtain ⟨c, d⟩ := cd
  unfold saddleEigenCoord saddleFromEigenCoord
  have hdet : saddleEigenDet ≠ 0 := saddleEigenDet_ne_zero
  have hdet_eq := saddleEigenDet_eq
  ext
  · -- first coordinate: ((c·v_s.1+d·v_u.1)·v_u.2 - (c·v_s.2+d·v_u.2)·v_u.1) / det = c
    show ((c * saddleStableVec.1 + d * saddleUnstableVec.1) * saddleUnstableVec.2
        - (c * saddleStableVec.2 + d * saddleUnstableVec.2) * saddleUnstableVec.1)
          / saddleEigenDet = c
    field_simp
    linear_combination -c * hdet_eq
  · show ((c * saddleStableVec.2 + d * saddleUnstableVec.2) * saddleStableVec.1
        - (c * saddleStableVec.1 + d * saddleUnstableVec.1) * saddleStableVec.2)
          / saddleEigenDet = d
    field_simp
    linear_combination -d * hdet_eq

/-- Backward × forward: `saddleFromEigenCoord ∘ saddleEigenCoord = id`. -/
theorem saddleFromEigenCoord_saddleEigenCoord (p : ℝ × ℝ) :
    saddleFromEigenCoord (saddleEigenCoord p) = p := by
  obtain ⟨p1, p2⟩ := p
  unfold saddleEigenCoord saddleFromEigenCoord
  have hdet : saddleEigenDet ≠ 0 := saddleEigenDet_ne_zero
  have hdet_eq := saddleEigenDet_eq
  ext
  · show (p1 * saddleUnstableVec.2 - p2 * saddleUnstableVec.1) / saddleEigenDet
            * saddleStableVec.1
        + (p2 * saddleStableVec.1 - p1 * saddleStableVec.2) / saddleEigenDet
            * saddleUnstableVec.1 = p1
    field_simp
    linear_combination -p1 * hdet_eq
  · show (p1 * saddleUnstableVec.2 - p2 * saddleUnstableVec.1) / saddleEigenDet
            * saddleStableVec.2
        + (p2 * saddleStableVec.1 - p1 * saddleStableVec.2) / saddleEigenDet
            * saddleUnstableVec.2 = p2
    field_simp
    linear_combination -p2 * hdet_eq

/-- **Diagonalization.** In eigencoordinates the linearization is diagonal:
    `saddleEigenCoord (J p) = (λ_- · cd.1, λ_+ · cd.2)` where `cd = saddleEigenCoord p`.

This is *the* statement that justifies the change of basis: in the new
coordinates, the linearized flow at the saddle decouples into two scalar
ODEs `ċ_s = λ_- c_s`, `ċ_u = λ_+ c_u`. -/
theorem saddleEigenCoord_saddleJacobianApply (p : ℝ × ℝ) :
    saddleEigenCoord (saddleJacobianApply p)
      = (saddleEigenvalueNegative * (saddleEigenCoord p).1,
         saddleEigenvaluePositive * (saddleEigenCoord p).2) := by
  obtain ⟨p1, p2⟩ := p
  have hdet : saddleEigenDet ≠ 0 := saddleEigenDet_ne_zero
  have h_sum := saddleEigenvalues_sum
  have h_prod := saddleEigenvalues_prod
  have h_T := saddleJacobianTrace_eq_sum_diag
  have h_D := saddleJacobianDet_eq_2x2
  unfold saddleEigenCoord saddleJacobianApply saddleStableVec saddleUnstableVec
  ext
  · show ((saddleJacobian00 * p1 + saddleJacobian01 * p2)
              * (saddleEigenvaluePositive - saddleJacobian00)
            - (saddleJacobian10 * p1 + saddleJacobian11 * p2) * saddleJacobian01)
            / saddleEigenDet
        = saddleEigenvalueNegative
          * ((p1 * (saddleEigenvaluePositive - saddleJacobian00)
                - p2 * saddleJacobian01) / saddleEigenDet)
    field_simp
    linear_combination
      (saddleJacobian00 * p1 + saddleJacobian01 * p2) * h_sum
      + (saddleJacobian00 * p1 + saddleJacobian01 * p2) * h_T
      - p1 * h_prod
      - p1 * h_D
  · show ((saddleJacobian10 * p1 + saddleJacobian11 * p2) * saddleJacobian01
            - (saddleJacobian00 * p1 + saddleJacobian01 * p2)
                * (saddleEigenvalueNegative - saddleJacobian00))
            / saddleEigenDet
        = saddleEigenvaluePositive
          * ((p2 * saddleJacobian01
                - p1 * (saddleEigenvalueNegative - saddleJacobian00)) / saddleEigenDet)
    field_simp
    linear_combination
      -(saddleJacobian00 * p1 + saddleJacobian01 * p2) * h_sum
      - (saddleJacobian00 * p1 + saddleJacobian01 * p2) * h_T
      + p1 * h_prod
      + p1 * h_D

/-! ### Linearity of `saddleEigenCoord` and eigenvec → standard basis

Both `saddleEigenCoord` and `saddleFromEigenCoord` are ℝ-linear (each component
is a linear functional of the input pair).  Together with the diagonalization
above, they exhibit `saddleJacobianApply` as similar to the diagonal map
`(c, d) ↦ (λ_-·c, λ_+·d)`. -/

@[simp] theorem saddleEigenCoord_zero : saddleEigenCoord (0, 0) = (0, 0) := by
  unfold saddleEigenCoord
  ext <;> simp

theorem saddleEigenCoord_add (p q : ℝ × ℝ) :
    saddleEigenCoord (p.1 + q.1, p.2 + q.2)
      = (saddleEigenCoord p + saddleEigenCoord q : ℝ × ℝ) := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  unfold saddleEigenCoord
  ext <;> simp <;> ring

theorem saddleEigenCoord_smul (c : ℝ) (p : ℝ × ℝ) :
    saddleEigenCoord (c * p.1, c * p.2)
      = (c * (saddleEigenCoord p).1, c * (saddleEigenCoord p).2) := by
  obtain ⟨p1, p2⟩ := p
  unfold saddleEigenCoord
  ext <;> simp <;> ring

@[simp] theorem saddleFromEigenCoord_zero :
    saddleFromEigenCoord (0, 0) = (0, 0) := by
  unfold saddleFromEigenCoord
  ext <;> simp

theorem saddleFromEigenCoord_add (cd ef : ℝ × ℝ) :
    saddleFromEigenCoord (cd.1 + ef.1, cd.2 + ef.2)
      = (saddleFromEigenCoord cd + saddleFromEigenCoord ef : ℝ × ℝ) := by
  obtain ⟨c, d⟩ := cd; obtain ⟨e, f⟩ := ef
  unfold saddleFromEigenCoord
  ext <;> simp <;> ring

theorem saddleFromEigenCoord_smul (k : ℝ) (cd : ℝ × ℝ) :
    saddleFromEigenCoord (k * cd.1, k * cd.2)
      = (k * (saddleFromEigenCoord cd).1, k * (saddleFromEigenCoord cd).2) := by
  obtain ⟨c, d⟩ := cd
  unfold saddleFromEigenCoord
  ext <;> simp <;> ring

/-- The stable eigenvector maps to `(1, 0)` in eigencoordinates. -/
theorem saddleEigenCoord_saddleStableVec :
    saddleEigenCoord saddleStableVec = (1, 0) := by
  have hdet : saddleEigenDet ≠ 0 := saddleEigenDet_ne_zero
  have hgap : saddleEigenvaluePositive - saddleEigenvalueNegative
                = Real.sqrt saddleJacobianDiscriminant := saddleEigenvalues_gap
  unfold saddleEigenCoord saddleStableVec saddleEigenDet
  ext
  · -- (J01·(λ_+ - J00) - (λ_- - J00)·J01) / (J01·√Δ) = 1
    show (saddleJacobian01 * (saddleEigenvaluePositive - saddleJacobian00)
            - (saddleEigenvalueNegative - saddleJacobian00) * saddleJacobian01)
          / (saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant) = 1
    have hdet' : saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant ≠ 0 := hdet
    have key : saddleJacobian01 * (saddleEigenvaluePositive - saddleJacobian00)
                - (saddleEigenvalueNegative - saddleJacobian00) * saddleJacobian01
             = saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant := by
      linear_combination saddleJacobian01 * hgap
    rw [key, div_self hdet']
  · show ((saddleEigenvalueNegative - saddleJacobian00) * saddleJacobian01
            - saddleJacobian01 * (saddleEigenvalueNegative - saddleJacobian00))
          / (saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant) = 0
    have h0 : (saddleEigenvalueNegative - saddleJacobian00) * saddleJacobian01
              - saddleJacobian01 * (saddleEigenvalueNegative - saddleJacobian00) = 0 := by ring
    rw [h0, zero_div]

/-- The unstable eigenvector maps to `(0, 1)` in eigencoordinates. -/
theorem saddleEigenCoord_saddleUnstableVec :
    saddleEigenCoord saddleUnstableVec = (0, 1) := by
  have hdet : saddleEigenDet ≠ 0 := saddleEigenDet_ne_zero
  have hgap : saddleEigenvaluePositive - saddleEigenvalueNegative
                = Real.sqrt saddleJacobianDiscriminant := saddleEigenvalues_gap
  unfold saddleEigenCoord saddleUnstableVec saddleEigenDet
  ext
  · show (saddleJacobian01 * (saddleEigenvaluePositive - saddleJacobian00)
            - (saddleEigenvaluePositive - saddleJacobian00) * saddleJacobian01)
          / (saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant) = 0
    have h0 : saddleJacobian01 * (saddleEigenvaluePositive - saddleJacobian00)
              - (saddleEigenvaluePositive - saddleJacobian00) * saddleJacobian01 = 0 := by ring
    rw [h0, zero_div]
  · show ((saddleEigenvaluePositive - saddleJacobian00) * saddleJacobian01
            - saddleJacobian01 * (saddleEigenvalueNegative - saddleJacobian00))
          / (saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant) = 1
    have hdet' : saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant ≠ 0 := hdet
    have key : (saddleEigenvaluePositive - saddleJacobian00) * saddleJacobian01
                - saddleJacobian01 * (saddleEigenvalueNegative - saddleJacobian00)
             = saddleJacobian01 * Real.sqrt saddleJacobianDiscriminant := by
      linear_combination saddleJacobian01 * hgap
    rw [key, div_self hdet']

/-! ### Spectral projections and direct sum decomposition

The eigenbasis decomposes any `p : ℝ × ℝ` uniquely as `c·v_s + d·v_u`.
The two **spectral projections** read off `c·v_s` and `d·v_u` separately.
Together with the J-eigen-equivariance of each projection, this is the
classical "stable/unstable splitting" used by the graph-transform argument. -/

/-- Stable spectral projection: extract the `v_s`-component. -/
noncomputable def saddleProjStable (p : ℝ × ℝ) : ℝ × ℝ :=
  ((saddleEigenCoord p).1 * saddleStableVec.1,
   (saddleEigenCoord p).1 * saddleStableVec.2)

/-- Unstable spectral projection: extract the `v_u`-component. -/
noncomputable def saddleProjUnstable (p : ℝ × ℝ) : ℝ × ℝ :=
  ((saddleEigenCoord p).2 * saddleUnstableVec.1,
   (saddleEigenCoord p).2 * saddleUnstableVec.2)

/-- The two projections sum to the identity: `p = P_s p + P_u p`. -/
theorem saddleProj_decomposition (p : ℝ × ℝ) :
    p = ((saddleProjStable p).1 + (saddleProjUnstable p).1,
         (saddleProjStable p).2 + (saddleProjUnstable p).2) := by
  obtain ⟨p1, p2⟩ := p
  have h := saddleFromEigenCoord_saddleEigenCoord (p1, p2)
  unfold saddleFromEigenCoord at h
  unfold saddleProjStable saddleProjUnstable
  -- h says (cd.1·v_s.1 + cd.2·v_u.1, cd.1·v_s.2 + cd.2·v_u.2) = (p1, p2)
  rw [Prod.mk.injEq] at h
  ext
  · exact h.1.symm
  · exact h.2.symm

/-- `P_s p` lies in the stable subspace. -/
theorem saddleProjStable_mem (p : ℝ × ℝ) :
    saddleProjStable p ∈ saddleStableSubspace := by
  rw [saddleStableSubspace, Submodule.mem_span_singleton]
  refine ⟨(saddleEigenCoord p).1, ?_⟩
  unfold saddleProjStable
  ext <;> simp [Prod.smul_def, smul_eq_mul]

/-- `P_u p` lies in the unstable subspace. -/
theorem saddleProjUnstable_mem (p : ℝ × ℝ) :
    saddleProjUnstable p ∈ saddleUnstableSubspace := by
  rw [saddleUnstableSubspace, Submodule.mem_span_singleton]
  refine ⟨(saddleEigenCoord p).2, ?_⟩
  unfold saddleProjUnstable
  ext <;> simp [Prod.smul_def, smul_eq_mul]

/-- J restricted to `P_s p` is `λ_-` times `P_s p`. -/
theorem saddleJacobianApply_saddleProjStable (p : ℝ × ℝ) :
    saddleJacobianApply (saddleProjStable p)
      = (saddleEigenvalueNegative * (saddleProjStable p).1,
         saddleEigenvalueNegative * (saddleProjStable p).2) := by
  unfold saddleProjStable
  have hP := saddleJacobianApply_smul (saddleEigenCoord p).1 saddleStableVec
  rw [saddleJacobianApply_stableVec] at hP
  rw [hP]
  ext <;> ring

/-- J restricted to `P_u p` is `λ_+` times `P_u p`. -/
theorem saddleJacobianApply_saddleProjUnstable (p : ℝ × ℝ) :
    saddleJacobianApply (saddleProjUnstable p)
      = (saddleEigenvaluePositive * (saddleProjUnstable p).1,
         saddleEigenvaluePositive * (saddleProjUnstable p).2) := by
  unfold saddleProjUnstable
  have hP := saddleJacobianApply_smul (saddleEigenCoord p).2 saddleUnstableVec
  rw [saddleJacobianApply_unstableVec] at hP
  rw [hP]
  ext <;> ring

/-! ### Quadratic-remainder difference identities (Lipschitz-prep)

For graph-transform contraction we need `|Q(p₁) − Q(p₂)| ≤ K·r·‖p₁−p₂‖`
on small disks.  The first algebraic brick: an exact polynomial identity
expressing `Q(p₁) − Q(p₂)` via the differences `(u₁−u₂)`, `(v₁−v₂)`. -/

/-- Polynomial identity for the field_1 quadratic-remainder difference. -/
theorem field1_remainder_diff (u₁ v₁ u₂ v₂ : ℝ) :
    (10 * u₁^2 - 5 * u₁ * v₁ - 14 * v₁^2)
      - (10 * u₂^2 - 5 * u₂ * v₂ - 14 * v₂^2)
      = 10 * (u₁ + u₂) * (u₁ - u₂)
        - 5 * (u₁ * (v₁ - v₂) + v₂ * (u₁ - u₂))
        - 14 * (v₁ + v₂) * (v₁ - v₂) := by ring

/-- Polynomial identity for the field_2 quadratic-remainder difference. -/
theorem field2_remainder_diff (u₁ v₁ u₂ v₂ : ℝ) :
    (-u₁^2 + 14 * v₁^2 + 14 * u₁ * v₁)
      - (-u₂^2 + 14 * v₂^2 + 14 * u₂ * v₂)
      = -(u₁ + u₂) * (u₁ - u₂)
        + 14 * (v₁ + v₂) * (v₁ - v₂)
        + 14 * (u₁ * (v₁ - v₂) + v₂ * (u₁ - u₂)) := by ring

/-- **Squared Lipschitz bound for `Q_1`.**  Using the polynomial identity
`Q_1(p₁) − Q_1(p₂) = X·A + Y·B` with `A = u₁ − u₂`, `B = v₁ − v₂`,
`X = 10(u₁+u₂) − 5v₂`, `Y = −5u₁ − 14(v₁+v₂)`, plus Cauchy-Schwarz
`(X·A + Y·B)² ≤ (X² + Y²)(A² + B²)` and an `AM-GM` bound on `X² + Y²`.

This is the analytic input to graph-transform contraction: on a disk
of radius `r`, `‖Q_1(p₁) − Q_1(p₂)‖ ≤ √(607·2r²) · ‖p₁−p₂‖ = O(r) · ‖p₁−p₂‖`,
so the Lipschitz constant of `Q_1` shrinks to `0` as `r → 0`. -/
theorem field1_remainder_lipschitz_sq (u₁ v₁ u₂ v₂ : ℝ) :
    ((10 * u₁^2 - 5 * u₁ * v₁ - 14 * v₁^2)
        - (10 * u₂^2 - 5 * u₂ * v₂ - 14 * v₂^2))^2
      ≤ 607 * (u₁^2 + v₁^2 + u₂^2 + v₂^2)
              * ((u₁ - u₂)^2 + (v₁ - v₂)^2) := by
  set X := 10*(u₁+u₂) - 5*v₂ with hXdef
  set Y := -5*u₁ - 14*(v₁+v₂) with hYdef
  set A := u₁ - u₂ with hAdef
  set B := v₁ - v₂ with hBdef
  have h_diff : (10*u₁^2 - 5*u₁*v₁ - 14*v₁^2) - (10*u₂^2 - 5*u₂*v₂ - 14*v₂^2)
              = X*A + Y*B := by
    simp only [hXdef, hYdef, hAdef, hBdef]; ring
  rw [h_diff]
  -- Cauchy-Schwarz: (XA + YB)² ≤ (X² + Y²)(A² + B²)
  have h_CS : (X*A + Y*B)^2 ≤ (X^2 + Y^2) * (A^2 + B^2) := by
    linarith [sq_nonneg (X*B - Y*A)]
  -- AM-GM: X² + Y² ≤ 607·(u₁²+v₁²+u₂²+v₂²)
  have h_xy : X^2 + Y^2 ≤ 607 * (u₁^2 + v₁^2 + u₂^2 + v₂^2) := by
    simp only [hXdef, hYdef]
    nlinarith [sq_nonneg (u₁+u₂), sq_nonneg (v₁+v₂),
               sq_nonneg (u₁+u₂-v₂), sq_nonneg (u₁+u₂+v₂),
               sq_nonneg (u₁-(v₁+v₂)), sq_nonneg (u₁+(v₁+v₂)),
               sq_nonneg u₁, sq_nonneg v₁, sq_nonneg u₂, sq_nonneg v₂]
  have h_AB_nn : (0 : ℝ) ≤ A^2 + B^2 := by positivity
  calc (X*A + Y*B)^2
      ≤ (X^2 + Y^2) * (A^2 + B^2) := h_CS
    _ ≤ 607*(u₁^2 + v₁^2 + u₂^2 + v₂^2) * (A^2 + B^2) :=
        mul_le_mul_of_nonneg_right h_xy h_AB_nn
    _ = 607*(u₁^2 + v₁^2 + u₂^2 + v₂^2) * ((u₁-u₂)^2 + (v₁-v₂)^2) := by
        simp only [hAdef, hBdef]

/-- **Squared Lipschitz bound for `Q_2`.**  Same Cauchy-Schwarz + AM-GM
strategy as `field1_remainder_lipschitz_sq`, with coefficients adapted
from the identity `Q_2(p₁) − Q_2(p₂) = X·A + Y·B` where now
`X = -(u₁+u₂) + 14·v₂`, `Y = 14·u₁ + 14·(v₁+v₂)`. -/
theorem field2_remainder_lipschitz_sq (u₁ v₁ u₂ v₂ : ℝ) :
    ((-u₁^2 + 14 * v₁^2 + 14 * u₁ * v₁)
        - (-u₂^2 + 14 * v₂^2 + 14 * u₂ * v₂))^2
      ≤ 1200 * (u₁^2 + v₁^2 + u₂^2 + v₂^2)
              * ((u₁ - u₂)^2 + (v₁ - v₂)^2) := by
  set X := -(u₁+u₂) + 14*v₂ with hXdef
  set Y := 14*u₁ + 14*(v₁+v₂) with hYdef
  set A := u₁ - u₂ with hAdef
  set B := v₁ - v₂ with hBdef
  have h_diff : (-u₁^2 + 14*v₁^2 + 14*u₁*v₁) - (-u₂^2 + 14*v₂^2 + 14*u₂*v₂)
              = X*A + Y*B := by
    simp only [hXdef, hYdef, hAdef, hBdef]; ring
  rw [h_diff]
  have h_CS : (X*A + Y*B)^2 ≤ (X^2 + Y^2) * (A^2 + B^2) := by
    linarith [sq_nonneg (X*B - Y*A)]
  have h_xy : X^2 + Y^2 ≤ 1200 * (u₁^2 + v₁^2 + u₂^2 + v₂^2) := by
    simp only [hXdef, hYdef]
    nlinarith [sq_nonneg (u₁+u₂), sq_nonneg (v₁+v₂),
               sq_nonneg (u₁+u₂-v₂), sq_nonneg (u₁+u₂+v₂),
               sq_nonneg (u₁-(v₁+v₂)), sq_nonneg (u₁+(v₁+v₂)),
               sq_nonneg u₁, sq_nonneg v₁, sq_nonneg u₂, sq_nonneg v₂]
  have h_AB_nn : (0 : ℝ) ≤ A^2 + B^2 := by positivity
  calc (X*A + Y*B)^2
      ≤ (X^2 + Y^2) * (A^2 + B^2) := h_CS
    _ ≤ 1200*(u₁^2 + v₁^2 + u₂^2 + v₂^2) * (A^2 + B^2) :=
        mul_le_mul_of_nonneg_right h_xy h_AB_nn
    _ = 1200*(u₁^2 + v₁^2 + u₂^2 + v₂^2) * ((u₁-u₂)^2 + (v₁-v₂)^2) := by
        simp only [hAdef, hBdef]

/-- **Combined squared Lipschitz bound for `Q` (vector form).**  Adds the
component-wise bounds `K_1 = 607` and `K_2 = 1200` to give a single
`K = 1807` constant for the full vector remainder
`Q(p) = (Q_1(p), Q_2(p))`.  This is the form consumed by the graph-transform
contraction argument. -/
theorem field_remainder_lipschitz_sq (u₁ v₁ u₂ v₂ : ℝ) :
    ((10 * u₁^2 - 5 * u₁ * v₁ - 14 * v₁^2)
        - (10 * u₂^2 - 5 * u₂ * v₂ - 14 * v₂^2))^2
    + ((-u₁^2 + 14 * v₁^2 + 14 * u₁ * v₁)
        - (-u₂^2 + 14 * v₂^2 + 14 * u₂ * v₂))^2
      ≤ 1807 * (u₁^2 + v₁^2 + u₂^2 + v₂^2)
              * ((u₁ - u₂)^2 + (v₁ - v₂)^2) := by
  have h1 := field1_remainder_lipschitz_sq u₁ v₁ u₂ v₂
  have h2 := field2_remainder_lipschitz_sq u₁ v₁ u₂ v₂
  linarith

/-- The vector-valued saddle remainder map `Q : ℝ² → ℝ²` packaging the two
component remainders `Q_1, Q_2` from `field_decomposition_near_saddle`.

`Q(p) = (10·p₁² − 5·p₁·p₂ − 14·p₂², −p₁² + 14·p₂² + 14·p₁·p₂)`. -/
noncomputable def saddleQ (p : ℝ × ℝ) : ℝ × ℝ :=
  (10 * p.1^2 - 5 * p.1 * p.2 - 14 * p.2^2,
   -p.1^2 + 14 * p.2^2 + 14 * p.1 * p.2)

/-- `Q(0) = 0`: the remainder vanishes at the saddle. -/
@[simp] theorem saddleQ_zero : saddleQ (0, 0) = (0, 0) := by
  unfold saddleQ; simp

/-- `saddleQ` is continuous (polynomial in two variables). -/
theorem continuous_saddleQ : Continuous saddleQ := by
  unfold saddleQ
  refine Continuous.prodMk ?_ ?_
  · -- 10·u² − 5·u·v − 14·v²
    fun_prop
  · -- −u² + 14·v² + 14·u·v
    fun_prop

/-- **Pointwise (`L¹`) Lipschitz bound for `Q_1` on the closed ball
`max(|u_i|, |v_i|) ≤ a`.**  Direct polynomial reasoning gives
`|Q_1(p₁) − Q_1(p₂)| ≤ 25a · |Δu| + 33a · |Δv|`. -/
theorem saddleQ_fst_lipschitz_l1 (a : ℝ) (p₁ p₂ : ℝ × ℝ)
    (hu₁ : |p₁.1| ≤ a) (hv₁ : |p₁.2| ≤ a)
    (hu₂ : |p₂.1| ≤ a) (hv₂ : |p₂.2| ≤ a) :
    |(saddleQ p₁).1 - (saddleQ p₂).1|
      ≤ 25 * a * |p₁.1 - p₂.1| + 33 * a * |p₁.2 - p₂.2| := by
  have h_ident : (saddleQ p₁).1 - (saddleQ p₂).1
      = 10 * (p₁.1 + p₂.1) * (p₁.1 - p₂.1)
        - 5 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))
        - 14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2) := by
    unfold saddleQ; exact field1_remainder_diff p₁.1 p₁.2 p₂.1 p₂.2
  have ha_nn : 0 ≤ a := (abs_nonneg p₁.1).trans hu₁
  -- |u₁+u₂| ≤ 2a, |v₁+v₂| ≤ 2a, |u₁| ≤ a, |v₂| ≤ a
  have h_su : |p₁.1 + p₂.1| ≤ 2 * a := by
    calc |p₁.1 + p₂.1| ≤ |p₁.1| + |p₂.1| := abs_add_le _ _
      _ ≤ a + a := by linarith
      _ = 2 * a := by ring
  have h_sv : |p₁.2 + p₂.2| ≤ 2 * a := by
    calc |p₁.2 + p₂.2| ≤ |p₁.2| + |p₂.2| := abs_add_le _ _
      _ ≤ a + a := by linarith
      _ = 2 * a := by ring
  rw [h_ident]
  -- Triangle/abs bounds on each piece
  have h_t1 : |10 * (p₁.1 + p₂.1) * (p₁.1 - p₂.1)| ≤ 20 * a * |p₁.1 - p₂.1| := by
    rw [show (10 : ℝ) * (p₁.1 + p₂.1) * (p₁.1 - p₂.1)
        = 10 * ((p₁.1 + p₂.1) * (p₁.1 - p₂.1)) by ring]
    rw [abs_mul, abs_mul]
    have : |p₁.1 + p₂.1| * |p₁.1 - p₂.1| ≤ (2 * a) * |p₁.1 - p₂.1| :=
      mul_le_mul_of_nonneg_right h_su (abs_nonneg _)
    have h10 : |(10 : ℝ)| = 10 := by norm_num
    rw [h10]; linarith
  have h_t2 : |5 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))|
      ≤ 5 * a * |p₁.2 - p₂.2| + 5 * a * |p₁.1 - p₂.1| := by
    have h_inner : |p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)|
        ≤ a * |p₁.2 - p₂.2| + a * |p₁.1 - p₂.1| := by
      calc |p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)|
          ≤ |p₁.1 * (p₁.2 - p₂.2)| + |p₂.2 * (p₁.1 - p₂.1)| := abs_add_le _ _
        _ = |p₁.1| * |p₁.2 - p₂.2| + |p₂.2| * |p₁.1 - p₂.1| := by rw [abs_mul, abs_mul]
        _ ≤ a * |p₁.2 - p₂.2| + a * |p₁.1 - p₂.1| := by
            have d1 : |p₁.1| * |p₁.2 - p₂.2| ≤ a * |p₁.2 - p₂.2| :=
              mul_le_mul_of_nonneg_right hu₁ (abs_nonneg _)
            have d2 : |p₂.2| * |p₁.1 - p₂.1| ≤ a * |p₁.1 - p₂.1| :=
              mul_le_mul_of_nonneg_right hv₂ (abs_nonneg _)
            linarith
    calc |5 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))|
        = |(5 : ℝ)| * |p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)| := abs_mul _ _
      _ = 5 * |p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)| := by norm_num
      _ ≤ 5 * (a * |p₁.2 - p₂.2| + a * |p₁.1 - p₂.1|) :=
          mul_le_mul_of_nonneg_left h_inner (by norm_num)
      _ = 5 * a * |p₁.2 - p₂.2| + 5 * a * |p₁.1 - p₂.1| := by ring
  have h_t3 : |14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)| ≤ 28 * a * |p₁.2 - p₂.2| := by
    rw [show (14 : ℝ) * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)
        = 14 * ((p₁.2 + p₂.2) * (p₁.2 - p₂.2)) by ring]
    rw [abs_mul, abs_mul]
    have : |p₁.2 + p₂.2| * |p₁.2 - p₂.2| ≤ (2 * a) * |p₁.2 - p₂.2| :=
      mul_le_mul_of_nonneg_right h_sv (abs_nonneg _)
    have h14 : |(14 : ℝ)| = 14 := by norm_num
    rw [h14]; linarith
  calc |10 * (p₁.1 + p₂.1) * (p₁.1 - p₂.1)
          - 5 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))
          - 14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)|
      ≤ |10 * (p₁.1 + p₂.1) * (p₁.1 - p₂.1)|
          + |5 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))|
          + |14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)| := by
        have h1 := abs_sub (10 * (p₁.1 + p₂.1) * (p₁.1 - p₂.1)
            - 5 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)))
            (14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2))
        have h2 := abs_sub (10 * (p₁.1 + p₂.1) * (p₁.1 - p₂.1))
            (5 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)))
        linarith
    _ ≤ 20 * a * |p₁.1 - p₂.1|
          + (5 * a * |p₁.2 - p₂.2| + 5 * a * |p₁.1 - p₂.1|)
          + 28 * a * |p₁.2 - p₂.2| := by linarith
    _ = 25 * a * |p₁.1 - p₂.1| + 33 * a * |p₁.2 - p₂.2| := by ring

/-- **Pointwise (`L¹`) Lipschitz bound for `Q_2` on the closed ball
`max(|u_i|, |v_i|) ≤ a`.**  Direct polynomial reasoning gives
`|Q_2(p₁) − Q_2(p₂)| ≤ 16a · |Δu| + 42a · |Δv|`. -/
theorem saddleQ_snd_lipschitz_l1 (a : ℝ) (p₁ p₂ : ℝ × ℝ)
    (hu₁ : |p₁.1| ≤ a) (hv₁ : |p₁.2| ≤ a)
    (hu₂ : |p₂.1| ≤ a) (hv₂ : |p₂.2| ≤ a) :
    |(saddleQ p₁).2 - (saddleQ p₂).2|
      ≤ 16 * a * |p₁.1 - p₂.1| + 42 * a * |p₁.2 - p₂.2| := by
  have h_ident : (saddleQ p₁).2 - (saddleQ p₂).2
      = -(p₁.1 + p₂.1) * (p₁.1 - p₂.1)
        + 14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)
        + 14 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)) := by
    unfold saddleQ; exact field2_remainder_diff p₁.1 p₁.2 p₂.1 p₂.2
  have ha_nn : 0 ≤ a := (abs_nonneg p₁.1).trans hu₁
  have h_su : |p₁.1 + p₂.1| ≤ 2 * a := by
    calc |p₁.1 + p₂.1| ≤ |p₁.1| + |p₂.1| := abs_add_le _ _
      _ ≤ a + a := by linarith
      _ = 2 * a := by ring
  have h_sv : |p₁.2 + p₂.2| ≤ 2 * a := by
    calc |p₁.2 + p₂.2| ≤ |p₁.2| + |p₂.2| := abs_add_le _ _
      _ ≤ a + a := by linarith
      _ = 2 * a := by ring
  rw [h_ident]
  have h_t1 : |(-(p₁.1 + p₂.1)) * (p₁.1 - p₂.1)| ≤ 2 * a * |p₁.1 - p₂.1| := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right h_su (abs_nonneg _)
  have h_t2 : |14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)| ≤ 28 * a * |p₁.2 - p₂.2| := by
    rw [show (14 : ℝ) * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)
        = 14 * ((p₁.2 + p₂.2) * (p₁.2 - p₂.2)) by ring]
    rw [abs_mul, abs_mul]
    have : |p₁.2 + p₂.2| * |p₁.2 - p₂.2| ≤ (2 * a) * |p₁.2 - p₂.2| :=
      mul_le_mul_of_nonneg_right h_sv (abs_nonneg _)
    have h14 : |(14 : ℝ)| = 14 := by norm_num
    rw [h14]; linarith
  have h_t3 : |14 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))|
      ≤ 14 * a * |p₁.2 - p₂.2| + 14 * a * |p₁.1 - p₂.1| := by
    have h_inner : |p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)|
        ≤ a * |p₁.2 - p₂.2| + a * |p₁.1 - p₂.1| := by
      calc |p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)|
          ≤ |p₁.1 * (p₁.2 - p₂.2)| + |p₂.2 * (p₁.1 - p₂.1)| := abs_add_le _ _
        _ = |p₁.1| * |p₁.2 - p₂.2| + |p₂.2| * |p₁.1 - p₂.1| := by rw [abs_mul, abs_mul]
        _ ≤ a * |p₁.2 - p₂.2| + a * |p₁.1 - p₂.1| := by
            have d1 : |p₁.1| * |p₁.2 - p₂.2| ≤ a * |p₁.2 - p₂.2| :=
              mul_le_mul_of_nonneg_right hu₁ (abs_nonneg _)
            have d2 : |p₂.2| * |p₁.1 - p₂.1| ≤ a * |p₁.1 - p₂.1| :=
              mul_le_mul_of_nonneg_right hv₂ (abs_nonneg _)
            linarith
    calc |14 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))|
        = |(14 : ℝ)| * |p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)| := abs_mul _ _
      _ = 14 * |p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1)| := by norm_num
      _ ≤ 14 * (a * |p₁.2 - p₂.2| + a * |p₁.1 - p₂.1|) :=
          mul_le_mul_of_nonneg_left h_inner (by norm_num)
      _ = 14 * a * |p₁.2 - p₂.2| + 14 * a * |p₁.1 - p₂.1| := by ring
  have h_split1 : -(p₁.1 + p₂.1) * (p₁.1 - p₂.1)
      = (-(p₁.1 + p₂.1)) * (p₁.1 - p₂.1) := by ring
  rw [h_split1]
  calc |(-(p₁.1 + p₂.1)) * (p₁.1 - p₂.1)
          + 14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)
          + 14 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))|
      ≤ |(-(p₁.1 + p₂.1)) * (p₁.1 - p₂.1)
          + 14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)|
          + |14 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))| := abs_add_le _ _
    _ ≤ (|(-(p₁.1 + p₂.1)) * (p₁.1 - p₂.1)|
          + |14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2)|)
          + |14 * (p₁.1 * (p₁.2 - p₂.2) + p₂.2 * (p₁.1 - p₂.1))| := by
        have := abs_add_le ((-(p₁.1 + p₂.1)) * (p₁.1 - p₂.1))
          (14 * (p₁.2 + p₂.2) * (p₁.2 - p₂.2))
        linarith
    _ ≤ (2 * a * |p₁.1 - p₂.1| + 28 * a * |p₁.2 - p₂.2|)
          + (14 * a * |p₁.2 - p₂.2| + 14 * a * |p₁.1 - p₂.1|) := by linarith
    _ = 16 * a * |p₁.1 - p₂.1| + 42 * a * |p₁.2 - p₂.2| := by ring

/-- **Vector max-norm Lipschitz bound for `saddleQ` on closed max-norm ball.**
Combining Q_1 and Q_2 L¹ pointwise bounds (each ≤ 25a/33a and 16a/42a) gives
`max(|ΔQ_1|, |ΔQ_2|) ≤ 58·a · max(|Δu|, |Δv|)` on the ball
`max(|u_i|, |v_i|) ≤ a`.

This is the Mathlib-shaped Lipschitz bound (since `Prod.dist_eq = max`) that
feeds directly into `LipschitzOnWith` and Picard-Lindelöf. -/
theorem saddleQ_lipschitz_max (a : ℝ) (p₁ p₂ : ℝ × ℝ)
    (hu₁ : |p₁.1| ≤ a) (hv₁ : |p₁.2| ≤ a)
    (hu₂ : |p₂.1| ≤ a) (hv₂ : |p₂.2| ≤ a) :
    max |(saddleQ p₁).1 - (saddleQ p₂).1| |(saddleQ p₁).2 - (saddleQ p₂).2|
      ≤ 58 * a * max |p₁.1 - p₂.1| |p₁.2 - p₂.2| := by
  have ha_nn : 0 ≤ a := (abs_nonneg p₁.1).trans hu₁
  have h1 := saddleQ_fst_lipschitz_l1 a p₁ p₂ hu₁ hv₁ hu₂ hv₂
  have h2 := saddleQ_snd_lipschitz_l1 a p₁ p₂ hu₁ hv₁ hu₂ hv₂
  set M := max |p₁.1 - p₂.1| |p₁.2 - p₂.2| with hM
  have hM_nn : 0 ≤ M := le_max_of_le_left (abs_nonneg _)
  have h_du : |p₁.1 - p₂.1| ≤ M := le_max_left _ _
  have h_dv : |p₁.2 - p₂.2| ≤ M := le_max_right _ _
  have ha_nn' : 0 ≤ 25 * a := by linarith
  have hb_nn' : 0 ≤ 33 * a := by linarith
  have hc_nn' : 0 ≤ 16 * a := by linarith
  have hd_nn' : 0 ≤ 42 * a := by linarith
  have h1' : |(saddleQ p₁).1 - (saddleQ p₂).1| ≤ 58 * a * M := by
    calc |(saddleQ p₁).1 - (saddleQ p₂).1|
        ≤ 25 * a * |p₁.1 - p₂.1| + 33 * a * |p₁.2 - p₂.2| := h1
      _ ≤ 25 * a * M + 33 * a * M :=
          add_le_add (mul_le_mul_of_nonneg_left h_du ha_nn')
                     (mul_le_mul_of_nonneg_left h_dv hb_nn')
      _ = 58 * a * M := by ring
  have h2' : |(saddleQ p₁).2 - (saddleQ p₂).2| ≤ 58 * a * M := by
    calc |(saddleQ p₁).2 - (saddleQ p₂).2|
        ≤ 16 * a * |p₁.1 - p₂.1| + 42 * a * |p₁.2 - p₂.2| := h2
      _ ≤ 16 * a * M + 42 * a * M :=
          add_le_add (mul_le_mul_of_nonneg_left h_du hc_nn')
                     (mul_le_mul_of_nonneg_left h_dv hd_nn')
      _ = 58 * a * M := by ring
  exact max_le h1' h2'

/-- **`LipschitzOnWith` for `saddleQ` on a closed ball.**  Mathlib-shaped
form: on `closedBall (0,0) a`, the map `saddleQ` is `(58a)`-Lipschitz with
respect to the standard product metric `dist p₁ p₂ = max |Δu| |Δv|`.

This is the form ingested by `IsPicardLindelof`. -/
theorem saddleQ_lipschitzOnWith (a : ℝ) (ha : 0 ≤ a) :
    LipschitzOnWith ⟨58 * a, by positivity⟩ saddleQ
      (Metric.closedBall ((0, 0) : ℝ × ℝ) a) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p₁ hp₁ p₂ hp₂
  have hp₁' : dist p₁ ((0,0) : ℝ × ℝ) ≤ a := hp₁
  have hp₂' : dist p₂ ((0,0) : ℝ × ℝ) ≤ a := hp₂
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero] at hp₁'
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero] at hp₂'
  have h_max := saddleQ_lipschitz_max a p₁ p₂ hp₁'.1 hp₁'.2 hp₂'.1 hp₂'.2
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [Real.dist_eq, NNReal.coe_mk]
  exact h_max

/-- **Vector Lipschitz bound for `saddleQ`.**  Repackaging
`field_remainder_lipschitz_sq` against the named `saddleQ`:
`‖Q(p₁) − Q(p₂)‖² ≤ 1807 · (‖p₁‖² + ‖p₂‖²) · ‖p₁ − p₂‖²`. -/
theorem saddleQ_lipschitz_sq (p₁ p₂ : ℝ × ℝ) :
    ((saddleQ p₁).1 - (saddleQ p₂).1)^2 + ((saddleQ p₁).2 - (saddleQ p₂).2)^2
      ≤ 1807 * (p₁.1^2 + p₁.2^2 + p₂.1^2 + p₂.2^2)
              * ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) := by
  unfold saddleQ
  exact field_remainder_lipschitz_sq p₁.1 p₁.2 p₂.1 p₂.2

/-- The **local field near `saddlePoint`** in the `(u, v) = (b−b*, c−c*)`
chart, packaged as a single `ℝ² → ℝ²` map: linear (Jacobian) plus quadratic
(remainder).  This is the form of the vector field that the graph-transform
construction iterates against. -/
noncomputable def saddleField (p : ℝ × ℝ) : ℝ × ℝ :=
  ((saddleJacobianApply p).1 + (saddleQ p).1,
   (saddleJacobianApply p).2 + (saddleQ p).2)

/-- The local field vanishes at the saddle. -/
@[simp] theorem saddleField_zero : saddleField (0, 0) = (0, 0) := by
  unfold saddleField
  simp [saddleJacobianApply, saddleQ]

/-- `saddleField` is continuous (sum of a continuous linear map and a
polynomial map). -/
theorem continuous_saddleField : Continuous saddleField := by
  unfold saddleField
  refine Continuous.prodMk ?_ ?_
  · refine Continuous.add ?_ ?_
    · exact (continuous_fst.comp saddleJacobianCLM.continuous)
    · exact continuous_fst.comp continuous_saddleQ
  · refine Continuous.add ?_ ?_
    · exact (continuous_snd.comp saddleJacobianCLM.continuous)
    · exact continuous_snd.comp continuous_saddleQ

/-- `saddleField p = saddleJacobianApply p + saddleQ p` (pointwise pair sum).
This is the trivial unfolding fact, used to redirect `saddleField` Lipschitz
bounds through the additive decomposition. -/
theorem saddleField_eq_add (p : ℝ × ℝ) :
    saddleField p = saddleJacobianApply p + saddleQ p := by
  unfold saddleField; rfl

/-- **`LipschitzOnWith` for `saddleField` on a closed ball.**  The local field
near the saddle is `(‖J‖ + 58a)`-Lipschitz on the max-norm ball of radius `a`,
where `‖J‖ = ‖saddleJacobianCLM‖₊` is the operator norm of the linearised part
and `58a` is the constant from `saddleQ_lipschitzOnWith`.

This is the **PicardLindelöf prerequisite**: combined with continuity of
`saddleField` and the saddle vanishing at `0`, it gives existence and
uniqueness of the local flow on a small enough ball. -/
theorem saddleField_lipschitzOnWith (a : ℝ) (ha : 0 ≤ a) :
    LipschitzOnWith
      (‖saddleJacobianCLM‖₊ + ⟨58 * a, by positivity⟩)
      saddleField
      (Metric.closedBall ((0, 0) : ℝ × ℝ) a) := by
  have hKa_nn : (0 : ℝ) ≤ 58 * a := by positivity
  let Ka : NNReal := ⟨58 * a, hKa_nn⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro p₁ hp₁ p₂ hp₂
  have h_J_lip : LipschitzWith ‖saddleJacobianCLM‖₊ saddleJacobianApply := by
    convert saddleJacobianCLM.lipschitz using 1
  have h_J : dist (saddleJacobianApply p₁) (saddleJacobianApply p₂)
        ≤ (‖saddleJacobianCLM‖₊ : ℝ) * dist p₁ p₂ :=
    h_J_lip.dist_le_mul p₁ p₂
  have h_Q : dist (saddleQ p₁) (saddleQ p₂) ≤ (Ka : ℝ) * dist p₁ p₂ :=
    (saddleQ_lipschitzOnWith a ha).dist_le_mul p₁ hp₁ p₂ hp₂
  rw [saddleField_eq_add, saddleField_eq_add]
  have h_tri := dist_add_add_le
    (saddleJacobianApply p₁) (saddleQ p₁)
    (saddleJacobianApply p₂) (saddleQ p₂)
  have h_combined : dist (saddleJacobianApply p₁ + saddleQ p₁)
                        (saddleJacobianApply p₂ + saddleQ p₂)
        ≤ (‖saddleJacobianCLM‖₊ : ℝ) * dist p₁ p₂
          + (Ka : ℝ) * dist p₁ p₂ :=
    le_trans h_tri (add_le_add h_J h_Q)
  show dist (saddleJacobianApply p₁ + saddleQ p₁)
            (saddleJacobianApply p₂ + saddleQ p₂)
    ≤ ((‖saddleJacobianCLM‖₊ + Ka : NNReal) : ℝ) * dist p₁ p₂
  rw [NNReal.coe_add]
  linarith [h_combined]

/-- **Localized Lipschitz bound for `saddleQ`.**  When both points lie in the
disk `‖p_i‖² ≤ r²`, the squared Lipschitz constant becomes `3614·r²`:
`‖Q(p₁) − Q(p₂)‖² ≤ 3614 · r² · ‖p₁ − p₂‖²`.  This is the form that makes
the graph-transform a contraction for small enough `r`. -/
theorem saddleQ_lipschitz_sq_localized (r : ℝ) (p₁ p₂ : ℝ × ℝ)
    (h₁ : p₁.1^2 + p₁.2^2 ≤ r^2) (h₂ : p₂.1^2 + p₂.2^2 ≤ r^2) :
    ((saddleQ p₁).1 - (saddleQ p₂).1)^2 + ((saddleQ p₁).2 - (saddleQ p₂).2)^2
      ≤ 3614 * r^2 * ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) := by
  have hQ := saddleQ_lipschitz_sq p₁ p₂
  have hsum : p₁.1^2 + p₁.2^2 + p₂.1^2 + p₂.2^2 ≤ 2 * r^2 := by linarith
  have hdiff_nn : (0 : ℝ) ≤ (p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2 := by positivity
  calc ((saddleQ p₁).1 - (saddleQ p₂).1)^2 + ((saddleQ p₁).2 - (saddleQ p₂).2)^2
      ≤ 1807 * (p₁.1^2 + p₁.2^2 + p₂.1^2 + p₂.2^2)
              * ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) := hQ
    _ ≤ 1807 * (2 * r^2) * ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) := by
        apply mul_le_mul_of_nonneg_right _ hdiff_nn
        exact mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 1807)
    _ = 3614 * r^2 * ((p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2) := by ring

/-- **Norm bound for `saddleField` on a closed ball.**  Since `saddleField`
vanishes at the saddle and is `(‖J‖ + 58a)`-Lipschitz on `closedBall 0 a`,
we get `‖saddleField p‖ ≤ (‖J‖ + 58a) · a` for `p ∈ closedBall 0 a`.

This is the **`norm_le L`** ingredient of `IsPicardLindelof`. -/
theorem saddleField_norm_le_on_ball (a : ℝ) (ha : 0 ≤ a)
    (p : ℝ × ℝ) (hp : p ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) a) :
    ‖saddleField p‖
      ≤ ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a := by
  have hKa_nn : (0 : ℝ) ≤ 58 * a := by positivity
  let Ka : NNReal := ⟨58 * a, hKa_nn⟩
  have h_zero : ((0, 0) : ℝ × ℝ) ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) a := by
    simp [Metric.mem_closedBall, ha]
  have h_lip := (saddleField_lipschitzOnWith a ha).dist_le_mul p hp ((0, 0) : ℝ × ℝ) h_zero
  have h_dist_p : dist p ((0, 0) : ℝ × ℝ) ≤ a := hp
  have h_K_coe : ((‖saddleJacobianCLM‖₊ + Ka : NNReal) : ℝ)
      = (‖saddleJacobianCLM‖₊ : ℝ) + 58 * a := by
    rw [NNReal.coe_add]; rfl
  rw [h_K_coe, saddleField_zero] at h_lip
  -- h_lip : dist (saddleField p) (0, 0) ≤ (‖J‖ + 58a) * dist p (0, 0)
  have h_norm_eq : ‖saddleField p‖ = dist (saddleField p) ((0, 0) : ℝ × ℝ) := by
    rw [show ((0, 0) : ℝ × ℝ) = (0 : ℝ × ℝ) from rfl, dist_zero_right]
  rw [h_norm_eq]
  have h_K_nn : 0 ≤ (‖saddleJacobianCLM‖₊ : ℝ) + 58 * a := by positivity
  calc dist (saddleField p) ((0, 0) : ℝ × ℝ)
      ≤ ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * dist p ((0, 0) : ℝ × ℝ) := h_lip
    _ ≤ ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a :=
        mul_le_mul_of_nonneg_left h_dist_p h_K_nn

/-! ### Time-dependent wrapping (autonomous case)

The saddle field is autonomous, but `Mathlib.Analysis.ODE.PicardLindelof`
requires a time-dependent vector field `f : ℝ → E → E`.  We package
`saddleField` as the trivial wrapping `t ↦ saddleField`.  The three
time-uniform `IsPicardLindelof` ingredients (Lipschitz on ball at every
time, continuity in time, norm bound at every time) all reduce to their
autonomous counterparts. -/

/-- Time-dependent wrapper around `saddleField` (autonomous). -/
noncomputable def saddleFieldTime : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
  fun _ p => saddleField p

@[simp] theorem saddleFieldTime_apply (t : ℝ) (p : ℝ × ℝ) :
    saddleFieldTime t p = saddleField p := rfl

/-- **Time-uniform Lipschitz bound** for `saddleFieldTime`: at every time `t`,
the spatial slice `saddleFieldTime t = saddleField` is `(‖J‖₊ + ⟨58a, _⟩)`-
Lipschitz on `closedBall 0 a`.  This is the `IsPicardLindelof.lipschitzOnWith`
ingredient. -/
theorem saddleFieldTime_lipschitzOnWith (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    LipschitzOnWith
      (‖saddleJacobianCLM‖₊ + ⟨58 * a, by positivity⟩)
      (saddleFieldTime t)
      (Metric.closedBall ((0, 0) : ℝ × ℝ) a) := by
  unfold saddleFieldTime
  exact saddleField_lipschitzOnWith a ha

/-- **Time-continuity at fixed `x`** for `saddleFieldTime`: since the field
is autonomous, `t ↦ saddleFieldTime t x` is constant in `t` on any interval.
This is the `IsPicardLindelof.continuousOn` ingredient. -/
theorem saddleFieldTime_continuousOn_time (x : ℝ × ℝ)
    (s : Set ℝ) :
    ContinuousOn (fun t => saddleFieldTime t x) s := by
  unfold saddleFieldTime
  exact continuousOn_const

/-- **Time-uniform norm bound** for `saddleFieldTime`: at every time `t` and
every `x ∈ closedBall 0 a`, `‖saddleFieldTime t x‖ ≤ (‖J‖ + 58a) · a`.
This is the `IsPicardLindelof.norm_le` ingredient. -/
theorem saddleFieldTime_norm_le (a : ℝ) (ha : 0 ≤ a)
    (t : ℝ) (x : ℝ × ℝ) (hx : x ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) a) :
    ‖saddleFieldTime t x‖ ≤ ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a := by
  unfold saddleFieldTime
  exact saddleField_norm_le_on_ball a ha x hx

/-! ### `IsPicardLindelof` instance for the saddle field

Pulling all the prerequisites together: given concrete `a, r, T : ℝ≥0`
satisfying the contraction constraint, we produce the Mathlib
`IsPicardLindelof` structure for `saddleFieldTime` on the symmetric
interval `Icc (-T) T` with `t₀ = 0` and `x₀ = (0, 0)`.

This is the gateway to Mathlib's existence and uniqueness theorems
for the local flow near the saddle. -/

/-- The IsPicardLindelof Lipschitz constant for the saddle field on a closed
ball of radius `a`: K(a) = ‖J‖₊ + ⟨58a, _⟩.  Packaged as `ℝ≥0`. -/
noncomputable def saddleField_K (a : ℝ) (ha : 0 ≤ a) : NNReal :=
  ‖saddleJacobianCLM‖₊ + ⟨58 * a, by positivity⟩

/-- The IsPicardLindelof norm bound for the saddle field on a closed ball of
radius `a`: L(a) = (‖J‖ + 58a) · a.  Packaged as `ℝ≥0`. -/
noncomputable def saddleField_L (a : ℝ) (ha : 0 ≤ a) : NNReal :=
  ⟨((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a, by positivity⟩

theorem saddleField_K_coe (a : ℝ) (ha : 0 ≤ a) :
    (saddleField_K a ha : ℝ) = (‖saddleJacobianCLM‖₊ : ℝ) + 58 * a := by
  unfold saddleField_K
  rw [NNReal.coe_add]; rfl

theorem saddleField_L_coe (a : ℝ) (ha : 0 ≤ a) :
    (saddleField_L a ha : ℝ) = ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a := rfl

/-- **`IsPicardLindelof` for `saddleFieldTime`** on a symmetric interval.

Given `a r T : ℝ` with `0 ≤ r ≤ a` and `0 ≤ T`, and the parameter constraint
`L(a) · T ≤ a - r` (Mathlib's `mul_max_le`), we obtain `IsPicardLindelof`
on `Icc (-T) T` anchored at `t₀ = 0` and `x₀ = (0, 0)`.

The constraint amounts to: the time-`T` flow stays inside the ball of radius
`a` when starting from a smaller ball of radius `r`. -/
theorem saddleFieldTime_isPicardLindelof
    (a r T : ℝ) (ha : 0 ≤ a) (hr_nn : 0 ≤ r) (hT_nn : 0 ≤ T)
    (hr_a : r ≤ a)
    (h_constraint : ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a * T ≤ a - r) :
    IsPicardLindelof
      saddleFieldTime
      (⟨0, by simp [neg_le_self_iff, hT_nn]⟩
        : Set.Icc (-T) T)
      ((0, 0) : ℝ × ℝ)
      ⟨a, ha⟩
      ⟨r, hr_nn⟩
      (saddleField_L a ha)
      (saddleField_K a ha) := by
  refine
    { lipschitzOnWith := ?_
      continuousOn := ?_
      norm_le := ?_
      mul_max_le := ?_ }
  · intro t _
    have h := saddleFieldTime_lipschitzOnWith a ha t
    convert h
  · intro x _
    exact saddleFieldTime_continuousOn_time x _
  · intro t _ x hx
    have h := saddleFieldTime_norm_le a ha t x hx
    rw [saddleField_L_coe a ha]
    exact h
  · -- mul_max_le: L · max(T - 0, 0 - (-T)) ≤ a - r
    show (saddleField_L a ha : ℝ) * max (T - 0) (0 - (-T))
          ≤ ((⟨a, ha⟩ : NNReal) : ℝ) - ((⟨r, hr_nn⟩ : NNReal) : ℝ)
    rw [saddleField_L_coe a ha]
    have h_max : max (T - 0) (0 - (-T)) = T := by
      simp [sub_zero, zero_sub, neg_neg, max_self]
    rw [h_max]
    show ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a * T
        ≤ ((⟨a, ha⟩ : NNReal) : ℝ) - ((⟨r, hr_nn⟩ : NNReal) : ℝ)
    have h_a_coe : ((⟨a, ha⟩ : NNReal) : ℝ) = a := rfl
    have h_r_coe : ((⟨r, hr_nn⟩ : NNReal) : ℝ) = r := rfl
    rw [h_a_coe, h_r_coe]
    exact h_constraint

/-- **Existence of a local saddle flow.**  Plugging
`saddleFieldTime_isPicardLindelof` into Mathlib's
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`
yields a flow `α : (ℝ × ℝ) → ℝ → (ℝ × ℝ)` defined for initial points
in the closed ball of radius `r` around the saddle, satisfying:

* `α x 0 = x` (initial condition);
* `(α x)` is differentiable on `[-T, T]` with derivative `saddleField (α x t)`
  (autonomous flow of the saddle field);
* the time-`t` slice `α · t` is Lipschitz in the initial point with some
  constant `L'`.

This is the unconditional existence step.  The remaining work for the stable
manifold is purely *graph-transform* on top of this flow. -/
theorem exists_saddleLocalFlow
    (a r T : ℝ) (ha : 0 ≤ a) (hr_nn : 0 ≤ r) (hT_nn : 0 ≤ T)
    (hr_a : r ≤ a)
    (h_constraint : ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a * T ≤ a - r) :
    ∃ α : (ℝ × ℝ) → ℝ → (ℝ × ℝ),
      (∀ x ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r,
        α x 0 = x ∧
        ∀ t ∈ Set.Icc (-T) T,
          HasDerivWithinAt (α x) (saddleField (α x t)) (Set.Icc (-T) T) t) ∧
      ∃ L' : NNReal, ∀ t ∈ Set.Icc (-T) T,
        LipschitzOnWith L' (α · t) (Metric.closedBall ((0, 0) : ℝ × ℝ) r) :=
  (saddleFieldTime_isPicardLindelof a r T ha hr_nn hT_nn hr_a h_constraint
    ).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith

/-- **Concrete witness** for the local flow constraint.  For *any* positive
ball radius `a`, choosing `r = a/2` and `T = 1 / (2 (‖J‖ + 58 a + 1))` yields
a valid `(r, T)` pair satisfying the Picard-Lindelöf constraint
`(‖J‖ + 58 a) · a · T ≤ a - r`.  This shows that the flow exists for all
sufficiently small initial-point perturbations of the saddle. -/
theorem exists_saddleLocalFlow_witness (a : ℝ) (ha_pos : 0 < a) :
    ∃ r T : ℝ, 0 < r ∧ 0 < T ∧ r ≤ a ∧
      ((‖saddleJacobianCLM‖₊ : ℝ) + 58 * a) * a * T ≤ a - r := by
  set N : ℝ := (‖saddleJacobianCLM‖₊ : ℝ) with hN_def
  have hN_nn : 0 ≤ N := NNReal.coe_nonneg _
  have h58a_nn : 0 ≤ 58 * a := by positivity
  have hZ_nn : 0 ≤ N + 58 * a := by linarith
  have hD_pos : 0 < N + 58 * a + 1 := by linarith
  refine ⟨a / 2, 1 / (2 * (N + 58 * a + 1)), ?_, ?_, ?_, ?_⟩
  · linarith
  · positivity
  · linarith
  · -- (N + 58a) · a · (1 / (2(N + 58a + 1))) ≤ a - a/2 = a/2
    have h_a_pos : 0 < a := ha_pos
    rw [show a - a/2 = a/2 from by ring]
    rw [show (N + 58 * a) * a * (1 / (2 * (N + 58 * a + 1)))
          = (N + 58 * a) * a / (2 * (N + 58 * a + 1)) from by ring]
    rw [div_le_iff₀ (by linarith)]
    have h_step : (N + 58 * a) * a ≤ (N + 58 * a + 1) * a := by
      have : (N + 58 * a) ≤ (N + 58 * a + 1) := by linarith
      exact mul_le_mul_of_nonneg_right this (le_of_lt ha_pos)
    linarith [h_step, ha_pos, hZ_nn]

/-- **Unconditional local existence of the saddle flow.**  For *every* positive
ball radius `a`, there exist concrete positive `r ≤ a` and time horizon `T`
such that the saddle field admits a Lipschitz local flow on `closedBall 0 r`
over `[-T, T]`.

This is a consequence of `exists_saddleLocalFlow_witness` (existence of valid
Picard-Lindelöf parameters) and `exists_saddleLocalFlow` (the flow given those
parameters).  Combining them gives the user-facing form: no smallness on `a`
needs to be assumed — the local flow always exists. -/
theorem exists_saddleLocalFlow_of_pos (a : ℝ) (ha_pos : 0 < a) :
    ∃ r T : ℝ, 0 < r ∧ 0 < T ∧ r ≤ a ∧
      ∃ α : (ℝ × ℝ) → ℝ → (ℝ × ℝ),
        (∀ x ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r,
          α x 0 = x ∧
          ∀ t ∈ Set.Icc (-T) T,
            HasDerivWithinAt (α x) (saddleField (α x t)) (Set.Icc (-T) T) t) ∧
        ∃ L' : NNReal, ∀ t ∈ Set.Icc (-T) T,
          LipschitzOnWith L' (α · t) (Metric.closedBall ((0, 0) : ℝ × ℝ) r) := by
  obtain ⟨r, T, hr_pos, hT_pos, hr_a, h_constraint⟩ :=
    exists_saddleLocalFlow_witness a ha_pos
  refine ⟨r, T, hr_pos, hT_pos, hr_a, ?_⟩
  exact exists_saddleLocalFlow a r T (le_of_lt ha_pos) (le_of_lt hr_pos)
    (le_of_lt hT_pos) hr_a h_constraint

/-! ### Structure-form local flow

Bundles the existential output of `exists_saddleLocalFlow_of_pos` into a
single record so that downstream constructions (graph-transform map, etc.)
can quote a concrete `α` rather than carrying a 7-tuple of existentials. -/

/-- A bundled local flow on a closed ball of radius `r ≤ a` over the time
interval `[-T, T]`, satisfying initial condition, derivative property
along the saddle field, and Lipschitz dependence on the initial point. -/
structure SaddleLocalFlow (a : ℝ) where
  /-- Spatial ball radius. -/
  r : ℝ
  /-- Time horizon. -/
  T : ℝ
  /-- Flow function `α x t`. -/
  α : (ℝ × ℝ) → ℝ → (ℝ × ℝ)
  r_pos : 0 < r
  T_pos : 0 < T
  r_le_a : r ≤ a
  /-- α x 0 = x for all x in the ball. -/
  init : ∀ x ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r, α x 0 = x
  /-- α x is a solution to the saddle ODE on [-T, T]. -/
  deriv : ∀ x ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r,
            ∀ t ∈ Set.Icc (-T) T,
              HasDerivWithinAt (α x) (saddleField (α x t)) (Set.Icc (-T) T) t
  /-- Lipschitz constant for the time-`t` flow map. -/
  L' : NNReal
  /-- α(·, t) is Lipschitz on the ball, uniformly in t. -/
  lip : ∀ t ∈ Set.Icc (-T) T,
          LipschitzOnWith L' (α · t) (Metric.closedBall ((0, 0) : ℝ × ℝ) r)

/-- Existence of a `SaddleLocalFlow a` for any `a > 0`.  Repackages
`exists_saddleLocalFlow_of_pos` in structure form. -/
theorem nonempty_saddleLocalFlow {a : ℝ} (ha_pos : 0 < a) :
    Nonempty (SaddleLocalFlow a) := by
  obtain ⟨r, T, hr_pos, hT_pos, hr_a, α, h_flow, L', h_lip⟩ :=
    exists_saddleLocalFlow_of_pos a ha_pos
  exact ⟨{
    r := r
    T := T
    α := α
    r_pos := hr_pos
    T_pos := hT_pos
    r_le_a := hr_a
    init := fun x hx => (h_flow x hx).1
    deriv := fun x hx t ht => (h_flow x hx).2 t ht
    L' := L'
    lip := h_lip
  }⟩

/-- A concrete witness `SaddleLocalFlow a` extracted via `Classical.choice`,
for any positive ball radius `a`.  Downstream constructions can refer to
`saddleLocalFlow a ha_pos` and access fields `.α`, `.r`, `.T`, `.init`, etc.
without re-deriving the existential each time. -/
noncomputable def saddleLocalFlow {a : ℝ} (ha_pos : 0 < a) :
    SaddleLocalFlow a :=
  (nonempty_saddleLocalFlow ha_pos).some

/-- The radius `r` of the extracted flow is positive. -/
theorem saddleLocalFlow_r_pos {a : ℝ} (ha_pos : 0 < a) :
    0 < (saddleLocalFlow ha_pos).r := (saddleLocalFlow ha_pos).r_pos

/-- The time horizon `T` of the extracted flow is positive. -/
theorem saddleLocalFlow_T_pos {a : ℝ} (ha_pos : 0 < a) :
    0 < (saddleLocalFlow ha_pos).T := (saddleLocalFlow ha_pos).T_pos

/-- A `SaddleLocalFlow` that is **guaranteed to have ball radius ≥ ρ** for any
prescribed `ρ > 0`.  Picks the underlying Picard-Lindelöf parameters
`a := 2·ρ`, `r := ρ`, `T := 1 / (2·(‖J‖ + 116·ρ + 1))`, which satisfy the
constraint `(‖J‖ + 58·a)·a·T ≤ a − r = ρ`.

This gives downstream graph-transform code direct control over the spatial
radius without depending on the arbitrary `r` produced by the unconstrained
witness `saddleLocalFlow`. -/
theorem nonempty_saddleLocalFlowAt (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ F : SaddleLocalFlow (2 * ρ), F.r = ρ := by
  set N : ℝ := (‖saddleJacobianCLM‖₊ : ℝ) with hN_def
  have hN_nn : 0 ≤ N := NNReal.coe_nonneg _
  set a : ℝ := 2 * ρ with ha_def
  have ha_pos : 0 < a := by positivity
  have ha_nn : 0 ≤ a := le_of_lt ha_pos
  set T : ℝ := 1 / (2 * (N + 58 * a + 1)) with hT_def
  have hD_pos : 0 < N + 58 * a + 1 := by positivity
  have hT_pos : 0 < T := by positivity
  have hr_le_a : ρ ≤ a := by rw [ha_def]; linarith
  have h_constraint : (N + 58 * a) * a * T ≤ a - ρ := by
    have ha_eq : a - ρ = ρ := by rw [ha_def]; ring
    rw [ha_eq, hT_def]
    rw [show (N + 58 * a) * a * (1 / (2 * (N + 58 * a + 1)))
          = (N + 58 * a) * a / (2 * (N + 58 * a + 1)) from by ring]
    rw [div_le_iff₀ (by linarith)]
    have hZ_nn : 0 ≤ N + 58 * a := by positivity
    have h_step : (N + 58 * a) * a ≤ (N + 58 * a + 1) * a :=
      mul_le_mul_of_nonneg_right (by linarith) ha_nn
    linarith [h_step, hρ, hZ_nn]
  obtain ⟨α, h_flow, L', h_lip⟩ :=
    exists_saddleLocalFlow a ρ T ha_nn (le_of_lt hρ) (le_of_lt hT_pos)
      hr_le_a h_constraint
  refine ⟨{
    r := ρ
    T := T
    α := α
    r_pos := hρ
    T_pos := hT_pos
    r_le_a := hr_le_a
    init := fun x hx => (h_flow x hx).1
    deriv := fun x hx t ht => (h_flow x hx).2 t ht
    L' := L'
    lip := h_lip
  }, rfl⟩

/-- A concrete `SaddleLocalFlow (2·ρ)` with prescribed spatial radius
`F.r = ρ`, extracted via `Classical.choose`. -/
noncomputable def saddleLocalFlowAt (ρ : ℝ) (hρ : 0 < ρ) :
    SaddleLocalFlow (2 * ρ) :=
  (nonempty_saddleLocalFlowAt ρ hρ).choose

/-- The radius of `saddleLocalFlowAt ρ hρ` is exactly `ρ`. -/
theorem saddleLocalFlowAt_r (ρ : ℝ) (hρ : 0 < ρ) :
    (saddleLocalFlowAt ρ hρ).r = ρ :=
  (nonempty_saddleLocalFlowAt ρ hρ).choose_spec

/-- Flow expressed in eigencoordinates: convert input to original coords,
flow, convert output back.  This is the natural object for the graph
transform — its second component is a candidate `ψ'(c)` value. -/
noncomputable def SaddleLocalFlow.eigenFlow {a : ℝ} (F : SaddleLocalFlow a)
    (cd : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  saddleEigenCoord (F.α (saddleFromEigenCoord cd) t)

/-- At time `t = 0`, the eigen-flow is the identity on inputs whose original
coordinates lie in the flow's ball. -/
theorem SaddleLocalFlow.eigenFlow_zero {a : ℝ} (F : SaddleLocalFlow a)
    (cd : ℝ × ℝ)
    (h_in : saddleFromEigenCoord cd ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    F.eigenFlow cd 0 = cd := by
  unfold eigenFlow
  rw [F.init _ h_in]
  exact saddleEigenCoord_saddleFromEigenCoord cd


/-- Restrict a `SaddleLocalFlow a` to a smaller spatial radius `r' ≤ a` with
`0 < r' ≤ flow.r`.  The same flow function `α` solves the ODE on the smaller
ball (closedBall is monotone in radius), with the same time horizon and
Lipschitz constant. -/
noncomputable def SaddleLocalFlow.restrict {a : ℝ} (F : SaddleLocalFlow a)
    (r' : ℝ) (hr'_pos : 0 < r') (hr'_le : r' ≤ F.r) : SaddleLocalFlow a where
  r := r'
  T := F.T
  α := F.α
  r_pos := hr'_pos
  T_pos := F.T_pos
  r_le_a := hr'_le.trans F.r_le_a
  init := fun x hx => F.init x (Metric.closedBall_subset_closedBall hr'_le hx)
  deriv := fun x hx t ht =>
    F.deriv x (Metric.closedBall_subset_closedBall hr'_le hx) t ht
  L' := F.L'
  lip := fun t ht =>
    (F.lip t ht).mono (Metric.closedBall_subset_closedBall hr'_le)

/-! ### Eigencoordinate form of the saddle field

In eigencoordinates `cd = saddleEigenCoord p`, the field decomposes as
`(λ_- · cd.1 + R_-, λ_+ · cd.2 + R_+)` where `R = saddleQEigen cd` is
the eigencoord remainder.  This is the form needed for the graph-transform
contraction: stable variable `c` decays exponentially as `e^{λ_- t}`,
unstable variable `d` grows exponentially as `e^{λ_+ t}`. -/

/-- The saddle field expressed in eigencoordinates. -/
noncomputable def saddleFieldEigen (cd : ℝ × ℝ) : ℝ × ℝ :=
  saddleEigenCoord (saddleField (saddleFromEigenCoord cd))

/-- The quadratic remainder of `saddleField` in eigencoordinates. -/
noncomputable def saddleQEigen (cd : ℝ × ℝ) : ℝ × ℝ :=
  saddleEigenCoord (saddleQ (saddleFromEigenCoord cd))

/-- **Diagonal + remainder decomposition of the eigencoord field.**
`saddleFieldEigen cd = (λ_- · cd.1 + R_- cd, λ_+ · cd.2 + R_+ cd)`. -/
theorem saddleFieldEigen_eq (cd : ℝ × ℝ) :
    saddleFieldEigen cd =
      (saddleEigenvalueNegative * cd.1 + (saddleQEigen cd).1,
       saddleEigenvaluePositive * cd.2 + (saddleQEigen cd).2) := by
  unfold saddleFieldEigen saddleQEigen
  rw [saddleField_eq_add]
  set p := saddleFromEigenCoord cd with hp
  -- Reshape `saddleJacobianApply p + saddleQ p` (Prod.add) into pair form
  -- so that `saddleEigenCoord_add` (which expects explicit pairs) applies.
  have h_reshape :
      (saddleJacobianApply p + saddleQ p)
        = ((saddleJacobianApply p).1 + (saddleQ p).1,
           (saddleJacobianApply p).2 + (saddleQ p).2) := by
    ext <;> rfl
  rw [h_reshape, saddleEigenCoord_add, saddleEigenCoord_saddleJacobianApply]
  have h_cd : saddleEigenCoord p = cd := by
    rw [hp]; exact saddleEigenCoord_saddleFromEigenCoord cd
  rw [h_cd]
  ext <;> simp

/-- The eigencoord remainder vanishes at the origin. -/
@[simp] theorem saddleQEigen_zero : saddleQEigen (0, 0) = (0, 0) := by
  unfold saddleQEigen
  rw [saddleFromEigenCoord_zero, saddleQ_zero, saddleEigenCoord_zero]

/-- The eigencoord field vanishes at the origin (the saddle). -/
@[simp] theorem saddleFieldEigen_zero : saddleFieldEigen (0, 0) = (0, 0) := by
  rw [saddleFieldEigen_eq, saddleQEigen_zero]
  simp

/-- Explicit Lipschitz constant for `saddleEigenCoord` (a linear map, hence
Lipschitz on all of `ℝ × ℝ`).  In max-norm this is the row-sum of the
inverse-eigenvector-matrix bound. -/
noncomputable def saddleEigenCoordLipConst : ℝ :=
  (|saddleStableVec.1| + |saddleStableVec.2| +
   |saddleUnstableVec.1| + |saddleUnstableVec.2|) / |saddleEigenDet|

theorem saddleEigenCoordLipConst_nonneg : 0 ≤ saddleEigenCoordLipConst := by
  unfold saddleEigenCoordLipConst
  exact div_nonneg (by positivity) (abs_nonneg _)

/-- `saddleEigenCoord` is globally Lipschitz with constant
`saddleEigenCoordLipConst` in the max-norm on `ℝ × ℝ`. -/
theorem saddleEigenCoord_dist_le (p q : ℝ × ℝ) :
    dist (saddleEigenCoord p) (saddleEigenCoord q)
      ≤ saddleEigenCoordLipConst * dist p q := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
      Real.dist_eq, Real.dist_eq]
  set M := max |p.1 - q.1| |p.2 - q.2| with hM_def
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hp1 : |p.1 - q.1| ≤ M := le_max_left _ _
  have hp2 : |p.2 - q.2| ≤ M := le_max_right _ _
  have h_det_pos : 0 < |saddleEigenDet| :=
    abs_pos.mpr saddleEigenDet_ne_zero
  -- Pre-numerator bounds: `(|u.1| + |u.2|) * M` and `(|s.1| + |s.2|) * M`.
  have h_num1 :
      |(p.1 - q.1) * saddleUnstableVec.2 - (p.2 - q.2) * saddleUnstableVec.1|
        ≤ (|saddleUnstableVec.1| + |saddleUnstableVec.2|) * M := by
    have h_tri := abs_sub ((p.1 - q.1) * saddleUnstableVec.2)
                         ((p.2 - q.2) * saddleUnstableVec.1)
    rw [abs_mul, abs_mul] at h_tri
    have h_bd1 : |p.1 - q.1| * |saddleUnstableVec.2|
                  ≤ M * |saddleUnstableVec.2| :=
      mul_le_mul_of_nonneg_right hp1 (abs_nonneg _)
    have h_bd2 : |p.2 - q.2| * |saddleUnstableVec.1|
                  ≤ M * |saddleUnstableVec.1| :=
      mul_le_mul_of_nonneg_right hp2 (abs_nonneg _)
    linarith [h_tri, h_bd1, h_bd2]
  have h_num2 :
      |(p.2 - q.2) * saddleStableVec.1 - (p.1 - q.1) * saddleStableVec.2|
        ≤ (|saddleStableVec.1| + |saddleStableVec.2|) * M := by
    have h_tri := abs_sub ((p.2 - q.2) * saddleStableVec.1)
                         ((p.1 - q.1) * saddleStableVec.2)
    rw [abs_mul, abs_mul] at h_tri
    have h_bd1 : |p.2 - q.2| * |saddleStableVec.1|
                  ≤ M * |saddleStableVec.1| :=
      mul_le_mul_of_nonneg_right hp2 (abs_nonneg _)
    have h_bd2 : |p.1 - q.1| * |saddleStableVec.2|
                  ≤ M * |saddleStableVec.2| :=
      mul_le_mul_of_nonneg_right hp1 (abs_nonneg _)
    linarith [h_tri, h_bd1, h_bd2]
  -- Algebraic identities for (saddleEigenCoord p).i - (saddleEigenCoord q).i
  have h_eq1 :
      (saddleEigenCoord p).1 - (saddleEigenCoord q).1
        = ((p.1 - q.1) * saddleUnstableVec.2
            - (p.2 - q.2) * saddleUnstableVec.1) / saddleEigenDet := by
    show (p.1 * saddleUnstableVec.2 - p.2 * saddleUnstableVec.1) / saddleEigenDet
          - (q.1 * saddleUnstableVec.2 - q.2 * saddleUnstableVec.1) / saddleEigenDet
        = _
    ring
  have h_eq2 :
      (saddleEigenCoord p).2 - (saddleEigenCoord q).2
        = ((p.2 - q.2) * saddleStableVec.1
            - (p.1 - q.1) * saddleStableVec.2) / saddleEigenDet := by
    show (p.2 * saddleStableVec.1 - p.1 * saddleStableVec.2) / saddleEigenDet
          - (q.2 * saddleStableVec.1 - q.1 * saddleStableVec.2) / saddleEigenDet
        = _
    ring
  -- Final componentwise bounds, each ≤ K_E * M
  unfold saddleEigenCoordLipConst
  set K := |saddleStableVec.1| + |saddleStableVec.2| +
            |saddleUnstableVec.1| + |saddleUnstableVec.2| with hK_def
  have hK_nn : 0 ≤ K := by positivity
  have h_lhs1 :
      |(saddleEigenCoord p).1 - (saddleEigenCoord q).1|
        ≤ K / |saddleEigenDet| * M := by
    rw [h_eq1, abs_div]
    have h_main :
        |(p.1 - q.1) * saddleUnstableVec.2 - (p.2 - q.2) * saddleUnstableVec.1|
          ≤ K * M := by
      have h_step :
          (|saddleUnstableVec.1| + |saddleUnstableVec.2|) * M ≤ K * M := by
        apply mul_le_mul_of_nonneg_right _ hM_nn
        rw [hK_def]
        have := abs_nonneg saddleStableVec.1
        have := abs_nonneg saddleStableVec.2
        linarith
      linarith [h_num1, h_step]
    calc |(p.1 - q.1) * saddleUnstableVec.2 - (p.2 - q.2) * saddleUnstableVec.1|
            / |saddleEigenDet|
        ≤ K * M / |saddleEigenDet| :=
          div_le_div_of_nonneg_right h_main (abs_nonneg _)
      _ = K / |saddleEigenDet| * M := by ring
  have h_lhs2 :
      |(saddleEigenCoord p).2 - (saddleEigenCoord q).2|
        ≤ K / |saddleEigenDet| * M := by
    rw [h_eq2, abs_div]
    have h_main :
        |(p.2 - q.2) * saddleStableVec.1 - (p.1 - q.1) * saddleStableVec.2|
          ≤ K * M := by
      have h_step :
          (|saddleStableVec.1| + |saddleStableVec.2|) * M ≤ K * M := by
        apply mul_le_mul_of_nonneg_right _ hM_nn
        rw [hK_def]
        have := abs_nonneg saddleUnstableVec.1
        have := abs_nonneg saddleUnstableVec.2
        linarith
      linarith [h_num2, h_step]
    calc |(p.2 - q.2) * saddleStableVec.1 - (p.1 - q.1) * saddleStableVec.2|
            / |saddleEigenDet|
        ≤ K * M / |saddleEigenDet| :=
          div_le_div_of_nonneg_right h_main (abs_nonneg _)
      _ = K / |saddleEigenDet| * M := by ring
  exact max_le h_lhs1 h_lhs2

/-- Explicit Lipschitz constant for `saddleFromEigenCoord` in the max-norm
on `ℝ × ℝ` (a linear map). -/
noncomputable def saddleFromEigenCoordLipConst : ℝ :=
  |saddleStableVec.1| + |saddleStableVec.2| +
   |saddleUnstableVec.1| + |saddleUnstableVec.2|

theorem saddleFromEigenCoordLipConst_nonneg :
    0 ≤ saddleFromEigenCoordLipConst := by
  unfold saddleFromEigenCoordLipConst
  positivity

/-- `saddleFromEigenCoord` is globally Lipschitz with constant
`saddleFromEigenCoordLipConst` in the max-norm on `ℝ × ℝ`. -/
theorem saddleFromEigenCoord_dist_le (cd₁ cd₂ : ℝ × ℝ) :
    dist (saddleFromEigenCoord cd₁) (saddleFromEigenCoord cd₂)
      ≤ saddleFromEigenCoordLipConst * dist cd₁ cd₂ := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
      Real.dist_eq, Real.dist_eq]
  set M := max |cd₁.1 - cd₂.1| |cd₁.2 - cd₂.2| with hM_def
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hp1 : |cd₁.1 - cd₂.1| ≤ M := le_max_left _ _
  have hp2 : |cd₁.2 - cd₂.2| ≤ M := le_max_right _ _
  have h_eq1 :
      (saddleFromEigenCoord cd₁).1 - (saddleFromEigenCoord cd₂).1
        = (cd₁.1 - cd₂.1) * saddleStableVec.1
            + (cd₁.2 - cd₂.2) * saddleUnstableVec.1 := by
    show (cd₁.1 * saddleStableVec.1 + cd₁.2 * saddleUnstableVec.1)
          - (cd₂.1 * saddleStableVec.1 + cd₂.2 * saddleUnstableVec.1) = _
    ring
  have h_eq2 :
      (saddleFromEigenCoord cd₁).2 - (saddleFromEigenCoord cd₂).2
        = (cd₁.1 - cd₂.1) * saddleStableVec.2
            + (cd₁.2 - cd₂.2) * saddleUnstableVec.2 := by
    show (cd₁.1 * saddleStableVec.2 + cd₁.2 * saddleUnstableVec.2)
          - (cd₂.1 * saddleStableVec.2 + cd₂.2 * saddleUnstableVec.2) = _
    ring
  unfold saddleFromEigenCoordLipConst
  set K := |saddleStableVec.1| + |saddleStableVec.2| +
            |saddleUnstableVec.1| + |saddleUnstableVec.2| with hK_def
  have hK_nn : 0 ≤ K := by positivity
  have h_lhs1 :
      |(saddleFromEigenCoord cd₁).1 - (saddleFromEigenCoord cd₂).1| ≤ K * M := by
    rw [h_eq1]
    have h_tri := abs_add_le ((cd₁.1 - cd₂.1) * saddleStableVec.1)
                          ((cd₁.2 - cd₂.2) * saddleUnstableVec.1)
    rw [abs_mul, abs_mul] at h_tri
    have h_bd1 : |cd₁.1 - cd₂.1| * |saddleStableVec.1| ≤ M * |saddleStableVec.1| :=
      mul_le_mul_of_nonneg_right hp1 (abs_nonneg _)
    have h_bd2 : |cd₁.2 - cd₂.2| * |saddleUnstableVec.1|
                  ≤ M * |saddleUnstableVec.1| :=
      mul_le_mul_of_nonneg_right hp2 (abs_nonneg _)
    have h_step :
        M * |saddleStableVec.1| + M * |saddleUnstableVec.1| ≤ K * M := by
      rw [hK_def]
      have := abs_nonneg saddleStableVec.2
      have := abs_nonneg saddleUnstableVec.2
      nlinarith [hM_nn, abs_nonneg saddleStableVec.1, abs_nonneg saddleUnstableVec.1]
    linarith [h_tri, h_bd1, h_bd2, h_step]
  have h_lhs2 :
      |(saddleFromEigenCoord cd₁).2 - (saddleFromEigenCoord cd₂).2| ≤ K * M := by
    rw [h_eq2]
    have h_tri := abs_add_le ((cd₁.1 - cd₂.1) * saddleStableVec.2)
                          ((cd₁.2 - cd₂.2) * saddleUnstableVec.2)
    rw [abs_mul, abs_mul] at h_tri
    have h_bd1 : |cd₁.1 - cd₂.1| * |saddleStableVec.2| ≤ M * |saddleStableVec.2| :=
      mul_le_mul_of_nonneg_right hp1 (abs_nonneg _)
    have h_bd2 : |cd₁.2 - cd₂.2| * |saddleUnstableVec.2|
                  ≤ M * |saddleUnstableVec.2| :=
      mul_le_mul_of_nonneg_right hp2 (abs_nonneg _)
    have h_step :
        M * |saddleStableVec.2| + M * |saddleUnstableVec.2| ≤ K * M := by
      rw [hK_def]
      nlinarith [hM_nn, abs_nonneg saddleStableVec.1, abs_nonneg saddleStableVec.2,
                 abs_nonneg saddleUnstableVec.1, abs_nonneg saddleUnstableVec.2]
    linarith [h_tri, h_bd1, h_bd2, h_step]
  exact max_le h_lhs1 h_lhs2

/-- The eigen-flow is Lipschitz in the initial eigencoord point, with
constant `K_E · L' · K_F`, on inputs whose lifted versions lie in the
flow's ball.  Composes the three Lipschitz steps:
`saddleFromEigenCoord` (K_F), `F.α(·,t)` (L'), `saddleEigenCoord` (K_E). -/
theorem SaddleLocalFlow.eigenFlow_dist_le {a : ℝ} (F : SaddleLocalFlow a)
    (t : ℝ) (ht : t ∈ Set.Icc (-F.T) F.T) (cd₁ cd₂ : ℝ × ℝ)
    (h₁ : saddleFromEigenCoord cd₁ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r)
    (h₂ : saddleFromEigenCoord cd₂ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    dist (F.eigenFlow cd₁ t) (F.eigenFlow cd₂ t)
      ≤ saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
          * dist cd₁ cd₂ := by
  unfold eigenFlow
  have hKE : dist (saddleEigenCoord (F.α (saddleFromEigenCoord cd₁) t))
                  (saddleEigenCoord (F.α (saddleFromEigenCoord cd₂) t))
              ≤ saddleEigenCoordLipConst
                  * dist (F.α (saddleFromEigenCoord cd₁) t)
                         (F.α (saddleFromEigenCoord cd₂) t) :=
    saddleEigenCoord_dist_le _ _
  have hα : dist (F.α (saddleFromEigenCoord cd₁) t)
                 (F.α (saddleFromEigenCoord cd₂) t)
              ≤ (F.L' : ℝ) * dist (saddleFromEigenCoord cd₁)
                                  (saddleFromEigenCoord cd₂) := by
    have := (F.lip t ht).dist_le_mul _ h₁ _ h₂
    simpa using this
  have hKF : dist (saddleFromEigenCoord cd₁) (saddleFromEigenCoord cd₂)
              ≤ saddleFromEigenCoordLipConst * dist cd₁ cd₂ :=
    saddleFromEigenCoord_dist_le _ _
  have hKE_nn := saddleEigenCoordLipConst_nonneg
  have hL'_nn : (0 : ℝ) ≤ (F.L' : ℝ) := NNReal.coe_nonneg _
  calc dist (saddleEigenCoord (F.α (saddleFromEigenCoord cd₁) t))
            (saddleEigenCoord (F.α (saddleFromEigenCoord cd₂) t))
      ≤ saddleEigenCoordLipConst
          * dist (F.α (saddleFromEigenCoord cd₁) t)
                 (F.α (saddleFromEigenCoord cd₂) t) := hKE
    _ ≤ saddleEigenCoordLipConst
          * ((F.L' : ℝ) * dist (saddleFromEigenCoord cd₁)
                                (saddleFromEigenCoord cd₂)) :=
        mul_le_mul_of_nonneg_left hα hKE_nn
    _ ≤ saddleEigenCoordLipConst
          * ((F.L' : ℝ) * (saddleFromEigenCoordLipConst * dist cd₁ cd₂)) := by
        apply mul_le_mul_of_nonneg_left _ hKE_nn
        exact mul_le_mul_of_nonneg_left hKF hL'_nn
    _ = saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
          * dist cd₁ cd₂ := by ring

/-- **`saddleQEigen` is Lipschitz on small eigencoord disks**, with Lipschitz
constant proportional to the radius `ρ`.  Specifically:
`dist (saddleQEigen cd₁) (saddleQEigen cd₂) ≤ 58 K_E K_F² ρ · dist cd₁ cd₂`
on `closedBall (0,0) ρ`.

The fact that the constant *scales linearly with `ρ`* — i.e., the remainder
is "second-order small" — is exactly what makes the graph-transform a
contraction at sufficiently small `ρ`. -/
theorem saddleQEigen_dist_le_on_ball (ρ : ℝ) (hρ : 0 ≤ ρ)
    (cd₁ cd₂ : ℝ × ℝ)
    (hcd₁ : cd₁ ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) ρ)
    (hcd₂ : cd₂ ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) ρ) :
    dist (saddleQEigen cd₁) (saddleQEigen cd₂)
      ≤ 58 * saddleEigenCoordLipConst
          * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst)
          * ρ * dist cd₁ cd₂ := by
  set K_E := saddleEigenCoordLipConst with hKE_def
  set K_F := saddleFromEigenCoordLipConst with hKF_def
  have hKE_nn : 0 ≤ K_E := saddleEigenCoordLipConst_nonneg
  have hKF_nn : 0 ≤ K_F := saddleFromEigenCoordLipConst_nonneg
  set a : ℝ := K_F * ρ with ha_def
  have ha_nn : 0 ≤ a := mul_nonneg hKF_nn hρ
  set p₁ := saddleFromEigenCoord cd₁ with hp₁_def
  set p₂ := saddleFromEigenCoord cd₂ with hp₂_def
  -- Step 1: p_i ∈ closedBall 0 a
  have h_dist_cd₁ : dist cd₁ ((0, 0) : ℝ × ℝ) ≤ ρ := hcd₁
  have h_dist_cd₂ : dist cd₂ ((0, 0) : ℝ × ℝ) ≤ ρ := hcd₂
  have hp_in_ball₁ : p₁ ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) a := by
    show dist p₁ ((0, 0) : ℝ × ℝ) ≤ a
    have h_F0 : saddleFromEigenCoord ((0, 0) : ℝ × ℝ) = (0, 0) :=
      saddleFromEigenCoord_zero
    rw [hp₁_def, show ((0, 0) : ℝ × ℝ) = saddleFromEigenCoord (0, 0) from h_F0.symm]
    rw [ha_def]
    have := saddleFromEigenCoord_dist_le cd₁ ((0, 0) : ℝ × ℝ)
    have h_step : K_F * dist cd₁ ((0, 0) : ℝ × ℝ) ≤ K_F * ρ :=
      mul_le_mul_of_nonneg_left h_dist_cd₁ hKF_nn
    linarith [this, h_step]
  have hp_in_ball₂ : p₂ ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) a := by
    show dist p₂ ((0, 0) : ℝ × ℝ) ≤ a
    have h_F0 : saddleFromEigenCoord ((0, 0) : ℝ × ℝ) = (0, 0) :=
      saddleFromEigenCoord_zero
    rw [hp₂_def, show ((0, 0) : ℝ × ℝ) = saddleFromEigenCoord (0, 0) from h_F0.symm]
    rw [ha_def]
    have := saddleFromEigenCoord_dist_le cd₂ ((0, 0) : ℝ × ℝ)
    have h_step : K_F * dist cd₂ ((0, 0) : ℝ × ℝ) ≤ K_F * ρ :=
      mul_le_mul_of_nonneg_left h_dist_cd₂ hKF_nn
    linarith [this, h_step]
  -- Step 2: bound dist (saddleQ p₁) (saddleQ p₂) ≤ 58a · dist p₁ p₂
  have h_Q : dist (saddleQ p₁) (saddleQ p₂) ≤ 58 * a * dist p₁ p₂ := by
    have h_lip := (saddleQ_lipschitzOnWith a ha_nn).dist_le_mul p₁ hp_in_ball₁ p₂
                    hp_in_ball₂
    simpa [NNReal.coe_mk] using h_lip
  -- Step 3: bound dist p₁ p₂ ≤ K_F · dist cd₁ cd₂
  have h_F : dist p₁ p₂ ≤ K_F * dist cd₁ cd₂ :=
    saddleFromEigenCoord_dist_le cd₁ cd₂
  -- Step 4: bound dist (saddleQEigen cd₁) (saddleQEigen cd₂)
  --   = dist (saddleEigenCoord (Q p₁)) (saddleEigenCoord (Q p₂))
  --   ≤ K_E · dist (Q p₁) (Q p₂)
  have h_E : dist (saddleQEigen cd₁) (saddleQEigen cd₂)
              ≤ K_E * dist (saddleQ p₁) (saddleQ p₂) := by
    show dist (saddleEigenCoord (saddleQ p₁)) (saddleEigenCoord (saddleQ p₂))
          ≤ K_E * dist (saddleQ p₁) (saddleQ p₂)
    exact saddleEigenCoord_dist_le _ _
  -- Combine all four steps
  have h_dist_pp_nn : 0 ≤ dist p₁ p₂ := dist_nonneg
  have h_dist_cd_nn : 0 ≤ dist cd₁ cd₂ := dist_nonneg
  have h_Q_K : K_E * dist (saddleQ p₁) (saddleQ p₂)
                ≤ K_E * (58 * a * dist p₁ p₂) :=
    mul_le_mul_of_nonneg_left h_Q hKE_nn
  have h_F_lift : 58 * a * dist p₁ p₂ ≤ 58 * a * (K_F * dist cd₁ cd₂) := by
    apply mul_le_mul_of_nonneg_left h_F
    have : 0 ≤ 58 * a := by positivity
    exact this
  calc dist (saddleQEigen cd₁) (saddleQEigen cd₂)
      ≤ K_E * dist (saddleQ p₁) (saddleQ p₂) := h_E
    _ ≤ K_E * (58 * a * dist p₁ p₂) := h_Q_K
    _ ≤ K_E * (58 * a * (K_F * dist cd₁ cd₂)) :=
        mul_le_mul_of_nonneg_left h_F_lift hKE_nn
    _ = 58 * K_E * (K_F * K_F) * ρ * dist cd₁ cd₂ := by rw [ha_def]; ring

/-- **Quadratic bound on `saddleQEigen`.**  Combining
`saddleQEigen_dist_le_on_ball` with `saddleQEigen_zero` gives a uniform
bound `‖Q_e cd‖ ≤ 58 K_E K_F² · ρ²` on `closedBall (0,0) ρ`.  The `ρ²` is
what one expects of a quadratic (Taylor) remainder. -/
theorem saddleQEigen_norm_le_on_ball (ρ : ℝ) (hρ : 0 ≤ ρ)
    (cd : ℝ × ℝ) (hcd : cd ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) ρ) :
    dist (saddleQEigen cd) ((0, 0) : ℝ × ℝ)
      ≤ 58 * saddleEigenCoordLipConst
          * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst)
          * (ρ * ρ) := by
  have hKE_nn : 0 ≤ saddleEigenCoordLipConst := saddleEigenCoordLipConst_nonneg
  have hKF_nn : 0 ≤ saddleFromEigenCoordLipConst := saddleFromEigenCoordLipConst_nonneg
  have h0_in : ((0, 0) : ℝ × ℝ) ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) ρ := by
    show dist ((0, 0) : ℝ × ℝ) ((0, 0) : ℝ × ℝ) ≤ ρ
    rw [dist_self]; exact hρ
  have h_lip := saddleQEigen_dist_le_on_ball ρ hρ cd ((0, 0) : ℝ × ℝ) hcd h0_in
  -- Replace `saddleQEigen (0, 0)` by `(0, 0)` in `h_lip`.
  rw [saddleQEigen_zero] at h_lip
  have h_dist_cd : dist cd ((0, 0) : ℝ × ℝ) ≤ ρ := hcd
  have h_const_nn :
      0 ≤ 58 * saddleEigenCoordLipConst
            * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst) * ρ := by
    positivity
  calc dist (saddleQEigen cd) ((0, 0) : ℝ × ℝ)
      ≤ 58 * saddleEigenCoordLipConst
          * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst)
          * ρ * dist cd ((0, 0) : ℝ × ℝ) := h_lip
    _ ≤ 58 * saddleEigenCoordLipConst
          * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst)
          * ρ * ρ := mul_le_mul_of_nonneg_left h_dist_cd h_const_nn
    _ = 58 * saddleEigenCoordLipConst
          * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst)
          * (ρ * ρ) := by ring

/-- **Spectral gap** of the saddle: the smaller of `|λ_-|` and `λ_+`.
This is the rate at which the linearized flow contracts onto the stable
manifold (and expands away from it).  The graph-transform contraction
threshold is `ρ < saddleSpectralGap / (58 K_E K_F²)`. -/
noncomputable def saddleSpectralGap : ℝ :=
  min (-saddleEigenvalueNegative) saddleEigenvaluePositive

theorem saddleSpectralGap_pos : 0 < saddleSpectralGap := by
  unfold saddleSpectralGap
  have h_neg := saddleEigenvalueNegative_neg
  have h_pos := saddleEigenvaluePositive_pos
  exact lt_min (by linarith) h_pos

theorem saddleSpectralGap_le_neg_lambda_neg :
    saddleSpectralGap ≤ -saddleEigenvalueNegative :=
  min_le_left _ _

theorem saddleSpectralGap_le_lambda_pos :
    saddleSpectralGap ≤ saddleEigenvaluePositive :=
  min_le_right _ _

/-- **Graph-transform contraction threshold.**  At any positive radius `ρ`
strictly below this threshold, the Q-remainder Lipschitz constant
`58 K_E K_F² ρ` is strictly less than the spectral gap, so the linear
part dominates the nonlinearity. -/
noncomputable def saddleGraphTransformThreshold : ℝ :=
  saddleSpectralGap
    / (58 * saddleEigenCoordLipConst
        * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst) + 1)

theorem saddleGraphTransformThreshold_pos : 0 < saddleGraphTransformThreshold := by
  unfold saddleGraphTransformThreshold
  apply div_pos saddleSpectralGap_pos
  have hKE_nn := saddleEigenCoordLipConst_nonneg
  have hKF_nn := saddleFromEigenCoordLipConst_nonneg
  positivity

/-- At any radius below the threshold, the `Q_e` Lipschitz constant
`58 K_E K_F² ρ` is strictly less than the spectral gap. -/
theorem saddleQEigen_lipschitz_lt_gap (ρ : ℝ) (hρ_thresh : ρ < saddleGraphTransformThreshold) :
    58 * saddleEigenCoordLipConst
        * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst) * ρ
      < saddleSpectralGap := by
  set β := 58 * saddleEigenCoordLipConst
              * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst) with hβ_def
  have hβ_nn : 0 ≤ β := by
    rw [hβ_def]
    have hKE_nn := saddleEigenCoordLipConst_nonneg
    have hKF_nn := saddleFromEigenCoordLipConst_nonneg
    positivity
  have hβplus1_pos : 0 < β + 1 := by linarith
  unfold saddleGraphTransformThreshold at hρ_thresh
  rw [show (58 * saddleEigenCoordLipConst
              * (saddleFromEigenCoordLipConst * saddleFromEigenCoordLipConst) + 1)
            = β + 1 from rfl] at hρ_thresh
  by_cases hβ_zero : β = 0
  · rw [hβ_zero, zero_mul]; exact saddleSpectralGap_pos
  · have hβ_pos : 0 < β := lt_of_le_of_ne hβ_nn (Ne.symm hβ_zero)
    have h1 : β * ρ < β * (saddleSpectralGap / (β + 1)) :=
      mul_lt_mul_of_pos_left hρ_thresh hβ_pos
    have h2 : β * (saddleSpectralGap / (β + 1)) ≤ saddleSpectralGap := by
      rw [mul_div_assoc', div_le_iff₀ hβplus1_pos]
      have hgap_pos := saddleSpectralGap_pos
      linarith [hβ_nn, hgap_pos]
    linarith

/-! ### Direct sum decomposition: ℝ² = stable ⊕ unstable

The two subspaces span ℝ² and intersect trivially.  This is the
final algebraic ingredient before the *analytic* graph-transform
construction of the stable manifold. -/

/-- The stable and unstable subspaces meet only at zero. -/
theorem saddleSubspaces_inf_bot :
    saddleStableSubspace ⊓ saddleUnstableSubspace = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvs, hvu⟩ := hv
  rw [saddleStableSubspace, Submodule.mem_span_singleton] at hvs
  rw [saddleUnstableSubspace, Submodule.mem_span_singleton] at hvu
  obtain ⟨c, hc⟩ := hvs
  obtain ⟨d, hd⟩ := hvu
  -- v = c • v_s and v = d • v_u.  Apply saddleEigenCoord to both.
  have h_smul_s : saddleEigenCoord (c • saddleStableVec) = (c, 0) := by
    show saddleEigenCoord (c * saddleStableVec.1, c * saddleStableVec.2) = (c, 0)
    rw [saddleEigenCoord_smul, saddleEigenCoord_saddleStableVec]
    simp
  have h_smul_u : saddleEigenCoord (d • saddleUnstableVec) = (0, d) := by
    show saddleEigenCoord (d * saddleUnstableVec.1, d * saddleUnstableVec.2) = (0, d)
    rw [saddleEigenCoord_smul, saddleEigenCoord_saddleUnstableVec]
    simp
  have hcd : ((c : ℝ), (0 : ℝ)) = ((0 : ℝ), d) := by
    rw [← h_smul_s, ← h_smul_u, hc, hd]
  have hc0 : c = 0 := (Prod.mk.injEq _ _ _ _).mp hcd |>.1
  rw [Submodule.mem_bot]
  rw [hc0, zero_smul] at hc
  exact hc.symm

/-- The stable and unstable subspaces span all of ℝ². -/
theorem saddleSubspaces_sup_top :
    saddleStableSubspace ⊔ saddleUnstableSubspace = ⊤ := by
  rw [eq_top_iff]
  intro p _
  -- p = (eC p).1 • v_s + (eC p).2 • v_u
  have hp : p = (saddleEigenCoord p).1 • saddleStableVec
                  + (saddleEigenCoord p).2 • saddleUnstableVec := by
    have h := saddleFromEigenCoord_saddleEigenCoord p
    obtain ⟨p1, p2⟩ := p
    set c := (saddleEigenCoord (p1, p2)).1
    set d := (saddleEigenCoord (p1, p2)).2
    show (p1, p2) = (c * saddleStableVec.1 + d * saddleUnstableVec.1,
                     c * saddleStableVec.2 + d * saddleUnstableVec.2)
    rw [← h]
    rfl
  rw [hp]
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left
      (Submodule.smul_mem _ _ saddleStableVec_mem_stableSubspace)
  · exact Submodule.mem_sup_right
      (Submodule.smul_mem _ _ saddleUnstableVec_mem_unstableSubspace)

/-- ℝ² is the internal direct sum of `saddleStableSubspace` and
`saddleUnstableSubspace`. -/
theorem saddleSubspaces_isCompl :
    IsCompl saddleStableSubspace saddleUnstableSubspace := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]; exact saddleSubspaces_inf_bot
  · rw [codisjoint_iff]; exact saddleSubspaces_sup_top

/-! ### Stable manifold scaffolding: small disk + Lipschitz curve space

Per the strategy outlined in `notes/stable-manifold-plan.md`, we construct
the local stable manifold at `saddlePoint` as the graph of a Lipschitz
function `ψ : ℝ → ℝ` from the stable eigencoordinate to the unstable one,
defined on a small disk `[-r, r]`.

This block introduces only the supporting definitions:
- `saddleEigenDisk r`: closed disk of radius `r` in eigencoordinates `(c, d)`.
- `SaddleLipCurve r L`: Lipschitz curves `ψ : ℝ → ℝ` with `ψ 0 = 0`,
  `|ψ s| ≤ L · |s|` and `|ψ s − ψ s'| ≤ L · |s − s'|` on `[-r, r]`.

The graph-transform map and contraction proof come in subsequent bricks. -/

/-- Closed disk of radius `r` in eigencoordinates, centered at the origin
(which corresponds to `saddlePoint` in the original `(b, c)` chart). -/
def saddleEigenDisk (r : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1^2 + p.2^2 ≤ r^2}

@[simp] theorem zero_mem_saddleEigenDisk (r : ℝ) (hr : 0 ≤ r) :
    ((0 : ℝ), (0 : ℝ)) ∈ saddleEigenDisk r := by
  unfold saddleEigenDisk
  simp [sq_nonneg]

/-- A `Lipschitz curve` through the origin in eigencoordinates: a function
`ψ : ℝ → ℝ` with `ψ 0 = 0` and Lipschitz constant `L` on the symmetric
interval `[-r, r]`.  Curves of this kind serve as candidate graphs for
the stable manifold parameterized by the stable eigencoordinate.

Note that `domain_bound` is *implied* by `lipschitz` and `zero_at_zero`
(taking `s' = 0`), but we include it for ergonomic access. -/
structure SaddleLipCurve (r L : ℝ) where
  /-- The underlying function. -/
  toFun : ℝ → ℝ
  /-- Vanishing at the origin (so the curve passes through the saddle). -/
  zero_at_zero : toFun 0 = 0
  /-- Linear bound: `|ψ s| ≤ L · |s|` for `|s| ≤ r`. -/
  domain_bound : ∀ s, |s| ≤ r → |toFun s| ≤ L * |s|
  /-- Lipschitz on `[-r, r]`: `|ψ s − ψ s'| ≤ L · |s − s'|`. -/
  lipschitz : ∀ s s', |s| ≤ r → |s'| ≤ r → |toFun s - toFun s'| ≤ L * |s - s'|

namespace SaddleLipCurve

/-- The constant zero function is a valid `SaddleLipCurve` at every Lipschitz
constant `L ≥ 0`.  This is the canonical starting point for the
graph-transform iteration. -/
def zero (r L : ℝ) (hL : 0 ≤ L) : SaddleLipCurve r L where
  toFun := fun _ => 0
  zero_at_zero := rfl
  domain_bound := by
    intro s _
    simp
    exact mul_nonneg hL (abs_nonneg s)
  lipschitz := by
    intro s s' _ _
    simp
    exact mul_nonneg hL (abs_nonneg _)

/-- Uniform bound on a `SaddleLipCurve` over the disk: `|ψ s| ≤ L · r` for all
`|s| ≤ r`.  Used to show that iterates of the graph-transform stay inside the
function space. -/
theorem uniform_bound {r L : ℝ} (hL : 0 ≤ L) (ψ : SaddleLipCurve r L)
    (s : ℝ) (hs : |s| ≤ r) : |ψ.toFun s| ≤ L * r := by
  have h1 := ψ.domain_bound s hs
  have h2 : L * |s| ≤ L * r := mul_le_mul_of_nonneg_left hs hL
  exact h1.trans h2

/-- Pointwise difference of two `SaddleLipCurve`s is bounded by `2 · L · r` on
the disk.  This is the bound that lets us define a sup-norm distance on the
function space. -/
theorem diff_uniform_bound {r L : ℝ} (hL : 0 ≤ L)
    (ψ ψ' : SaddleLipCurve r L) (s : ℝ) (hs : |s| ≤ r) :
    |ψ.toFun s - ψ'.toFun s| ≤ 2 * L * r := by
  have h1 : |ψ.toFun s| ≤ L * r := uniform_bound hL ψ s hs
  have h2 : |ψ'.toFun s| ≤ L * r := uniform_bound hL ψ' s hs
  have h3 : |ψ.toFun s - ψ'.toFun s| ≤ |ψ.toFun s| + |ψ'.toFun s| := abs_sub _ _
  linarith

/-- Smart constructor: a Lipschitz function vanishing at the origin yields a
`SaddleLipCurve` (the `domain_bound` field is derivable from `lipschitz` and
`zero_at_zero` when `0 ≤ r`). -/
def ofLipschitz {r L : ℝ} (hr : 0 ≤ r) (toFun : ℝ → ℝ)
    (zero_at_zero : toFun 0 = 0)
    (lipschitz : ∀ s s', |s| ≤ r → |s'| ≤ r → |toFun s - toFun s'| ≤ L * |s - s'|) :
    SaddleLipCurve r L where
  toFun := toFun
  zero_at_zero := zero_at_zero
  domain_bound := by
    intro s hs
    have h := lipschitz s 0 hs (by rw [abs_zero]; exact hr)
    rw [zero_at_zero, sub_zero, sub_zero] at h
    exact h
  lipschitz := lipschitz

/-- Sup-distance on the `SaddleLipCurve r L` function space:
`d(ψ, ψ') := sup_{|s| ≤ r} |ψ(s) − ψ'(s)|`.  This is the distance under which
graph-transform will be a contraction (so we can apply Banach fixed point). -/
noncomputable def dist {r L : ℝ} (ψ ψ' : SaddleLipCurve r L) : ℝ :=
  sSup ((fun s => |ψ.toFun s - ψ'.toFun s|) '' {s : ℝ | |s| ≤ r})

/-- The distance is bounded above by `2 · L · r`. -/
theorem dist_le_two_L_r {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    (ψ ψ' : SaddleLipCurve r L) :
    dist ψ ψ' ≤ 2 * L * r := by
  unfold dist
  apply csSup_le
  · refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simp [hr]
    · show |ψ.toFun 0 - ψ'.toFun 0| = 0
      rw [ψ.zero_at_zero, ψ'.zero_at_zero]; simp
  · rintro x ⟨s, hs, rfl⟩
    exact diff_uniform_bound hL ψ ψ' s hs

/-- The distance is nonnegative. -/
theorem dist_nonneg {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    (ψ ψ' : SaddleLipCurve r L) :
    0 ≤ dist ψ ψ' := by
  unfold dist
  apply le_csSup
  · refine ⟨2 * L * r, ?_⟩
    rintro x ⟨s, hs, rfl⟩
    exact diff_uniform_bound hL ψ ψ' s hs
  · refine ⟨0, ?_, ?_⟩
    · simp [hr]
    · show |ψ.toFun 0 - ψ'.toFun 0| = 0
      rw [ψ.zero_at_zero, ψ'.zero_at_zero]; simp

/-- The distance from a curve to itself is zero. -/
theorem dist_self {r L : ℝ} (hr : 0 ≤ r) (ψ : SaddleLipCurve r L) :
    dist ψ ψ = 0 := by
  unfold dist
  have hset : (fun s => |ψ.toFun s - ψ.toFun s|) '' {s : ℝ | |s| ≤ r} = {0} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, _, rfl⟩; simp
    · rintro rfl; exact ⟨0, by simp [hr], by simp⟩
  rw [hset, csSup_singleton]

/-- The distance is symmetric. -/
theorem dist_comm {r L : ℝ} (ψ ψ' : SaddleLipCurve r L) :
    dist ψ ψ' = dist ψ' ψ := by
  unfold dist
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [abs_sub_comm]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [abs_sub_comm]

/-- The pointwise difference is bounded above by the sup-distance:
`|ψ₁ s - ψ₂ s| ≤ dist ψ₁ ψ₂` for all `|s| ≤ r`.  This is the form most
useful for upper-bounding pointwise behavior using the metric. -/
theorem abs_sub_le_dist {r L : ℝ} (hL : 0 ≤ L)
    (ψ₁ ψ₂ : SaddleLipCurve r L) (s : ℝ) (hs : |s| ≤ r) :
    |ψ₁.toFun s - ψ₂.toFun s| ≤ dist ψ₁ ψ₂ := by
  unfold dist
  apply le_csSup
  · refine ⟨2 * L * r, ?_⟩
    rintro x ⟨s', hs', rfl⟩
    exact diff_uniform_bound hL ψ₁ ψ₂ s' hs'
  · exact ⟨s, hs, rfl⟩

/-- Triangle inequality for the sup-distance. -/
theorem dist_triangle {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    (ψ₁ ψ₂ ψ₃ : SaddleLipCurve r L) :
    dist ψ₁ ψ₃ ≤ dist ψ₁ ψ₂ + dist ψ₂ ψ₃ := by
  unfold dist
  apply csSup_le
  · refine ⟨0, 0, ?_, ?_⟩
    · simp [hr]
    · show |ψ₁.toFun 0 - ψ₃.toFun 0| = 0
      rw [ψ₁.zero_at_zero, ψ₃.zero_at_zero]; simp
  · rintro x ⟨s, hs, rfl⟩
    -- |ψ₁ s − ψ₃ s| ≤ |ψ₁ s − ψ₂ s| + |ψ₂ s − ψ₃ s|, then bound each by sup
    have h_tri : |ψ₁.toFun s - ψ₃.toFun s|
        ≤ |ψ₁.toFun s - ψ₂.toFun s| + |ψ₂.toFun s - ψ₃.toFun s| := by
      have := abs_sub_le (ψ₁.toFun s) (ψ₂.toFun s) (ψ₃.toFun s)
      linarith
    have hbdd12 : BddAbove ((fun s => |ψ₁.toFun s - ψ₂.toFun s|) '' {s : ℝ | |s| ≤ r}) := by
      refine ⟨2 * L * r, ?_⟩
      rintro x ⟨s', hs', rfl⟩
      exact diff_uniform_bound hL ψ₁ ψ₂ s' hs'
    have hbdd23 : BddAbove ((fun s => |ψ₂.toFun s - ψ₃.toFun s|) '' {s : ℝ | |s| ≤ r}) := by
      refine ⟨2 * L * r, ?_⟩
      rintro x ⟨s', hs', rfl⟩
      exact diff_uniform_bound hL ψ₂ ψ₃ s' hs'
    have h12 : |ψ₁.toFun s - ψ₂.toFun s|
        ≤ sSup ((fun s => |ψ₁.toFun s - ψ₂.toFun s|) '' {s : ℝ | |s| ≤ r}) := by
      apply le_csSup hbdd12
      exact ⟨s, hs, rfl⟩
    have h23 : |ψ₂.toFun s - ψ₃.toFun s|
        ≤ sSup ((fun s => |ψ₂.toFun s - ψ₃.toFun s|) '' {s : ℝ | |s| ≤ r}) := by
      apply le_csSup hbdd23
      exact ⟨s, hs, rfl⟩
    linarith

/-- Two `SaddleLipCurve`s have zero sup-distance iff they agree pointwise on
the disk.  This is the standard "metric ⟹ equality on test points"
characterization for the function space. -/
theorem dist_eq_zero_iff_eq_on_disk {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    (ψ₁ ψ₂ : SaddleLipCurve r L) :
    dist ψ₁ ψ₂ = 0 ↔ ∀ s, |s| ≤ r → ψ₁.toFun s = ψ₂.toFun s := by
  refine ⟨?_, ?_⟩
  · intro hd s hs
    have h1 := abs_sub_le_dist hL ψ₁ ψ₂ s hs
    rw [hd] at h1
    have h3 : |ψ₁.toFun s - ψ₂.toFun s| = 0 :=
      le_antisymm h1 (abs_nonneg _)
    have h4 : ψ₁.toFun s - ψ₂.toFun s = 0 := abs_eq_zero.mp h3
    linarith
  · intro hpt
    have h_le : dist ψ₁ ψ₂ ≤ 0 := by
      unfold dist
      apply csSup_le
      · refine ⟨0, 0, ?_, ?_⟩
        · simp [hr]
        · show |ψ₁.toFun 0 - ψ₂.toFun 0| = 0
          rw [hpt 0 (by rw [abs_zero]; exact hr)]; simp
      · rintro x ⟨s, hs, rfl⟩
        show |ψ₁.toFun s - ψ₂.toFun s| ≤ 0
        rw [hpt s hs]; simp
    have h_ge : 0 ≤ dist ψ₁ ψ₂ := dist_nonneg hr hL ψ₁ ψ₂
    linarith

/-! #### Curve-to-graph lifting

A `SaddleLipCurve` ψ represents a graph in eigencoordinates `(c, ψ c)`.
To plug it into the original-coordinate ODE / flow, we lift through
`saddleFromEigenCoord`.  These small lemmas make subsequent flow-based
arguments cleaner. -/

/-- Original-coordinate point on the graph of `ψ` over stable-axis value `c`. -/
noncomputable def graphPoint {r L : ℝ} (ψ : SaddleLipCurve r L) (c : ℝ) :
    ℝ × ℝ :=
  saddleFromEigenCoord (c, ψ.toFun c)

/-- The graph passes through the saddle (the origin) at `c = 0`. -/
theorem graphPoint_zero {r L : ℝ} (ψ : SaddleLipCurve r L) :
    graphPoint ψ 0 = (0, 0) := by
  unfold graphPoint
  rw [ψ.zero_at_zero]
  exact saddleFromEigenCoord_zero

/-- The eigencoord of the graph lift returns the original `(c, ψ c)` pair.
Direct consequence of `saddleEigenCoord ∘ saddleFromEigenCoord = id`.
This is the unifying identity tying `graphPoint` (in original coords) to
the eigencoord parameterization used by `flowedPoint`. -/
theorem saddleEigenCoord_graphPoint {r L : ℝ} (ψ : SaddleLipCurve r L) (c : ℝ) :
    saddleEigenCoord (graphPoint ψ c) = (c, ψ.toFun c) := by
  unfold graphPoint
  exact saddleEigenCoord_saddleFromEigenCoord _

end SaddleLipCurve

/-- `graphPoint ψ` is Lipschitz in the stable axis parameter `c` on the disk
`[-r, r]`, with constant `K_F · max(1, L)`.  This is the regularity we need
to control how the graph deforms under flow. -/
theorem SaddleLipCurve_graphPoint_lipschitz {r L : ℝ} (hL : 0 ≤ L)
    (ψ : SaddleLipCurve r L) (c₁ c₂ : ℝ) (hc₁ : |c₁| ≤ r) (hc₂ : |c₂| ≤ r) :
    dist (SaddleLipCurve.graphPoint ψ c₁) (SaddleLipCurve.graphPoint ψ c₂)
      ≤ saddleFromEigenCoordLipConst * max 1 L * |c₁ - c₂| := by
  unfold SaddleLipCurve.graphPoint
  have h1 : dist (saddleFromEigenCoord (c₁, ψ.toFun c₁))
                 (saddleFromEigenCoord (c₂, ψ.toFun c₂))
              ≤ saddleFromEigenCoordLipConst
                  * dist ((c₁, ψ.toFun c₁) : ℝ × ℝ) (c₂, ψ.toFun c₂) :=
    saddleFromEigenCoord_dist_le _ _
  have h2 : dist ((c₁, ψ.toFun c₁) : ℝ × ℝ) (c₂, ψ.toFun c₂)
              = max |c₁ - c₂| |ψ.toFun c₁ - ψ.toFun c₂| := by
    simp [Prod.dist_eq, Real.dist_eq]
  rw [h2] at h1
  have hψ : |ψ.toFun c₁ - ψ.toFun c₂| ≤ L * |c₁ - c₂| :=
    ψ.lipschitz c₁ c₂ hc₁ hc₂
  have habs_nn : 0 ≤ |c₁ - c₂| := abs_nonneg _
  have hone_le : |c₁ - c₂| ≤ max 1 L * |c₁ - c₂| := by
    have h1' : |c₁ - c₂| ≤ 1 * |c₁ - c₂| := by linarith
    exact h1'.trans (mul_le_mul_of_nonneg_right (le_max_left 1 L) habs_nn)
  have hL_le : L * |c₁ - c₂| ≤ max 1 L * |c₁ - c₂| :=
    mul_le_mul_of_nonneg_right (le_max_right 1 L) habs_nn
  have hmax : max |c₁ - c₂| |ψ.toFun c₁ - ψ.toFun c₂| ≤ max 1 L * |c₁ - c₂| := by
    apply max_le
    · exact hone_le
    · exact hψ.trans hL_le
  have hKF_nn := saddleFromEigenCoordLipConst_nonneg
  calc dist (saddleFromEigenCoord (c₁, ψ.toFun c₁))
            (saddleFromEigenCoord (c₂, ψ.toFun c₂))
      ≤ saddleFromEigenCoordLipConst
          * max |c₁ - c₂| |ψ.toFun c₁ - ψ.toFun c₂| := h1
    _ ≤ saddleFromEigenCoordLipConst * (max 1 L * |c₁ - c₂|) :=
        mul_le_mul_of_nonneg_left hmax hKF_nn
    _ = saddleFromEigenCoordLipConst * max 1 L * |c₁ - c₂| := by ring

/-- The graph point `SaddleLipCurve.graphPoint ψ c` lies in the closed ball of
radius `saddleFromEigenCoordLipConst · max(r, L · r)` around the origin in
original coordinates, for any `|c| ≤ r`.  This is the inclusion needed to plug
a curve into the local flow which is defined on a disk in original
coordinates. -/
theorem SaddleLipCurve_graphPoint_dist_le {r L : ℝ} (hL : 0 ≤ L)
    (ψ : SaddleLipCurve r L) (c : ℝ) (hc : |c| ≤ r) :
    dist (SaddleLipCurve.graphPoint ψ c) ((0, 0) : ℝ × ℝ)
      ≤ saddleFromEigenCoordLipConst * max r (L * r) := by
  unfold SaddleLipCurve.graphPoint
  have h1 : dist (saddleFromEigenCoord (c, ψ.toFun c))
                 (saddleFromEigenCoord (0, 0))
              ≤ saddleFromEigenCoordLipConst
                  * dist ((c, ψ.toFun c) : ℝ × ℝ) (0, 0) :=
    saddleFromEigenCoord_dist_le _ _
  rw [saddleFromEigenCoord_zero] at h1
  have h2 : dist ((c, ψ.toFun c) : ℝ × ℝ) (0, 0)
              = max |c| |ψ.toFun c| := by
    simp [Prod.dist_eq, Real.dist_eq, abs_zero]
  rw [h2] at h1
  have hψ : |ψ.toFun c| ≤ L * r := by
    have := ψ.domain_bound c hc
    have hLc : L * |c| ≤ L * r := mul_le_mul_of_nonneg_left hc hL
    linarith
  have hmax : max |c| |ψ.toFun c| ≤ max r (L * r) := by
    apply max_le
    · exact le_max_of_le_left hc
    · exact le_max_of_le_right hψ
  have hKF_nn := saddleFromEigenCoordLipConst_nonneg
  calc dist (saddleFromEigenCoord (c, ψ.toFun c)) ((0, 0) : ℝ × ℝ)
      ≤ saddleFromEigenCoordLipConst * max |c| |ψ.toFun c| := h1
    _ ≤ saddleFromEigenCoordLipConst * max r (L * r) :=
        mul_le_mul_of_nonneg_left hmax hKF_nn

/-- Membership form of `SaddleLipCurve_graphPoint_dist_le`: the graph point lies
in the closed ball of radius `saddleFromEigenCoordLipConst · max(r, L · r)`
around the origin.  This is the form directly accepted by the local flow's
domain hypothesis. -/
theorem SaddleLipCurve_graphPoint_mem_ball {r L : ℝ} (hL : 0 ≤ L)
    (ψ : SaddleLipCurve r L) (c : ℝ) (hc : |c| ≤ r) :
    SaddleLipCurve.graphPoint ψ c ∈
      Metric.closedBall ((0, 0) : ℝ × ℝ)
        (saddleFromEigenCoordLipConst * max r (L * r)) := by
  rw [Metric.mem_closedBall]
  exact SaddleLipCurve_graphPoint_dist_le hL ψ c hc

/-- Bridge between curve-side disk inclusion and flow-side domain:
the graph point `graphPoint ψ c` lies in the local-flow ball
`closedBall (0,0) (saddleLocalFlowAt ρ hρ).r` whenever
`K_F · max(r, L·r) ≤ ρ` and `|c| ≤ r`. -/
theorem SaddleLipCurve_graphPoint_mem_saddleLocalFlowAt {r L : ℝ} (hL : 0 ≤ L)
    (ψ : SaddleLipCurve r L) (c : ℝ) (hc : |c| ≤ r)
    (ρ : ℝ) (hρ : 0 < ρ)
    (h_inc : saddleFromEigenCoordLipConst * max r (L * r) ≤ ρ) :
    SaddleLipCurve.graphPoint ψ c ∈
      Metric.closedBall ((0, 0) : ℝ × ℝ) (saddleLocalFlowAt ρ hρ).r := by
  rw [saddleLocalFlowAt_r]
  rw [Metric.mem_closedBall]
  exact (SaddleLipCurve_graphPoint_dist_le hL ψ c hc).trans h_inc

/-- Specialization of the bridge lemma when `L ≤ 1`: the constraint
`K_F · max(r, L · r) ≤ ρ` collapses to `K_F · r ≤ ρ` since `L · r ≤ r`.
This is the form used by graph-transform contraction arguments where
the candidate Lipschitz constants are kept ≤ 1 throughout iteration. -/
theorem SaddleLipCurve_graphPoint_mem_saddleLocalFlowAt_of_L_le_one
    {r L : ℝ} (hL : 0 ≤ L) (hL1 : L ≤ 1) (hr : 0 ≤ r)
    (ψ : SaddleLipCurve r L) (c : ℝ) (hc : |c| ≤ r)
    (ρ : ℝ) (hρ : 0 < ρ)
    (h_inc : saddleFromEigenCoordLipConst * r ≤ ρ) :
    SaddleLipCurve.graphPoint ψ c ∈
      Metric.closedBall ((0, 0) : ℝ × ℝ) (saddleLocalFlowAt ρ hρ).r := by
  refine SaddleLipCurve_graphPoint_mem_saddleLocalFlowAt hL ψ c hc ρ hρ ?_
  have h_eq : max r (L * r) = r :=
    max_eq_left (mul_le_of_le_one_left hr hL1)
  rw [h_eq]
  exact h_inc

/-- The eigen-flow image of the curve graph at stable-axis point `c`,
parameterized by time `t`.  This is the candidate raw output of the
graph transform: at `t = 0` it is the trivial graph `(c, ψ c)`; for
small `t > 0` it is the forward-image graph that the transform aims
to re-parameterize back over the stable axis. -/
noncomputable def SaddleLipCurve.flowedPoint {r L : ℝ} (ψ : SaddleLipCurve r L)
    {a : ℝ} (F : SaddleLocalFlow a) (t c : ℝ) : ℝ × ℝ :=
  F.eigenFlow (c, ψ.toFun c) t

/-- At `t = 0`, the flowed point is the original `(c, ψ c)`. -/
theorem SaddleLipCurve.flowedPoint_zero {r L : ℝ} (ψ : SaddleLipCurve r L)
    {a : ℝ} (F : SaddleLocalFlow a) (c : ℝ) (hc : |c| ≤ r)
    (h_in : SaddleLipCurve.graphPoint ψ c ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    SaddleLipCurve.flowedPoint ψ F 0 c = (c, ψ.toFun c) := by
  unfold flowedPoint graphPoint at *
  exact F.eigenFlow_zero (c, ψ.toFun c) h_in

/-- Reformulation of `flowedPoint` in original (non-eigen) coords: the
flowed point equals the eigencoord of the original-coord trajectory
`F.α (graphPoint ψ c) t`.  This is the form that connects directly to
the underlying ODE system on `ℝ × ℝ` rather than the eigencoord
parameterization. -/
theorem SaddleLipCurve.flowedPoint_eq_eigen_of_alpha {r L : ℝ}
    (ψ : SaddleLipCurve r L) {a : ℝ} (F : SaddleLocalFlow a) (t c : ℝ) :
    SaddleLipCurve.flowedPoint ψ F t c
      = saddleEigenCoord (F.α (SaddleLipCurve.graphPoint ψ c) t) := by
  unfold SaddleLipCurve.flowedPoint SaddleLocalFlow.eigenFlow
         SaddleLipCurve.graphPoint
  rfl

/-- Stable-axis component of the flowed point: `flowedC ψ F t c` is the
first coordinate (in eigencoord) of `flowedPoint ψ F t c`.  This is the
"new c" produced by flowing the graph forward; the reparameterization
question is whether `c ↦ flowedC ψ F t c` is a bijection on the stable
disk for small `t`. -/
noncomputable def SaddleLipCurve.flowedC {r L : ℝ} (ψ : SaddleLipCurve r L)
    {a : ℝ} (F : SaddleLocalFlow a) (t c : ℝ) : ℝ :=
  (SaddleLipCurve.flowedPoint ψ F t c).1

/-- Unstable-axis component of the flowed point: `flowedD ψ F t c` is the
second coordinate.  Together with `flowedC`, this gives the candidate new
graph value `(flowedC, flowedD)` at the original `c`. -/
noncomputable def SaddleLipCurve.flowedD {r L : ℝ} (ψ : SaddleLipCurve r L)
    {a : ℝ} (F : SaddleLocalFlow a) (t c : ℝ) : ℝ :=
  (SaddleLipCurve.flowedPoint ψ F t c).2

/-- At `t = 0`, the stable-axis component of the flowed point is `c` itself. -/
theorem SaddleLipCurve.flowedC_zero {r L : ℝ} (ψ : SaddleLipCurve r L)
    {a : ℝ} (F : SaddleLocalFlow a) (c : ℝ) (hc : |c| ≤ r)
    (h_in : SaddleLipCurve.graphPoint ψ c ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    SaddleLipCurve.flowedC ψ F 0 c = c := by
  unfold flowedC
  rw [ψ.flowedPoint_zero F c hc h_in]

/-- At `t = 0`, the unstable-axis component of the flowed point is `ψ c`. -/
theorem SaddleLipCurve.flowedD_zero {r L : ℝ} (ψ : SaddleLipCurve r L)
    {a : ℝ} (F : SaddleLocalFlow a) (c : ℝ) (hc : |c| ≤ r)
    (h_in : SaddleLipCurve.graphPoint ψ c ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    SaddleLipCurve.flowedD ψ F 0 c = ψ.toFun c := by
  unfold flowedD
  rw [ψ.flowedPoint_zero F c hc h_in]

/-- The flowed point is Lipschitz in the stable-axis parameter `c`, with
constant `K_E · L' · K_F · max(1, L)`.  Hypothesis: both `c₁`, `c₂` are
in the disk `[-r, r]` and their graph lifts are in the flow's ball. -/
theorem SaddleLipCurve_flowedPoint_dist_le {r L : ℝ} (hL : 0 ≤ L)
    (ψ : SaddleLipCurve r L) {a : ℝ} (F : SaddleLocalFlow a)
    (t : ℝ) (ht : t ∈ Set.Icc (-F.T) F.T) (c₁ c₂ : ℝ)
    (hc₁ : |c₁| ≤ r) (hc₂ : |c₂| ≤ r)
    (h₁ : SaddleLipCurve.graphPoint ψ c₁ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r)
    (h₂ : SaddleLipCurve.graphPoint ψ c₂ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    dist (SaddleLipCurve.flowedPoint ψ F t c₁)
         (SaddleLipCurve.flowedPoint ψ F t c₂)
      ≤ saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
          * max 1 L * |c₁ - c₂| := by
  unfold SaddleLipCurve.flowedPoint
  -- eigenFlow Lipschitz step
  have h_eigen :
      dist (F.eigenFlow (c₁, ψ.toFun c₁) t) (F.eigenFlow (c₂, ψ.toFun c₂) t)
        ≤ saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
            * dist ((c₁, ψ.toFun c₁) : ℝ × ℝ) (c₂, ψ.toFun c₂) := by
    have := F.eigenFlow_dist_le t ht (c₁, ψ.toFun c₁) (c₂, ψ.toFun c₂)
              (by unfold SaddleLipCurve.graphPoint at h₁; exact h₁)
              (by unfold SaddleLipCurve.graphPoint at h₂; exact h₂)
    exact this
  -- product distance bound
  have h_pair : dist ((c₁, ψ.toFun c₁) : ℝ × ℝ) (c₂, ψ.toFun c₂)
                  = max |c₁ - c₂| |ψ.toFun c₁ - ψ.toFun c₂| := by
    simp [Prod.dist_eq, Real.dist_eq]
  rw [h_pair] at h_eigen
  -- |ψ c₁ - ψ c₂| ≤ L · |c₁ - c₂|
  have hψ : |ψ.toFun c₁ - ψ.toFun c₂| ≤ L * |c₁ - c₂| :=
    ψ.lipschitz c₁ c₂ hc₁ hc₂
  have habs_nn : 0 ≤ |c₁ - c₂| := abs_nonneg _
  have hone_le : |c₁ - c₂| ≤ max 1 L * |c₁ - c₂| := by
    have : |c₁ - c₂| ≤ 1 * |c₁ - c₂| := by linarith
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left 1 L) habs_nn)
  have hL_le : L * |c₁ - c₂| ≤ max 1 L * |c₁ - c₂| :=
    mul_le_mul_of_nonneg_right (le_max_right 1 L) habs_nn
  have hmax : max |c₁ - c₂| |ψ.toFun c₁ - ψ.toFun c₂| ≤ max 1 L * |c₁ - c₂| := by
    apply max_le hone_le (hψ.trans hL_le)
  -- compose
  have hKE_nn := saddleEigenCoordLipConst_nonneg
  have hL'_nn : (0 : ℝ) ≤ (F.L' : ℝ) := NNReal.coe_nonneg _
  have hKF_nn := saddleFromEigenCoordLipConst_nonneg
  have hC_nn : 0 ≤ saddleEigenCoordLipConst * (F.L' : ℝ)
                    * saddleFromEigenCoordLipConst := by positivity
  calc dist (F.eigenFlow (c₁, ψ.toFun c₁) t) (F.eigenFlow (c₂, ψ.toFun c₂) t)
      ≤ saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
          * max |c₁ - c₂| |ψ.toFun c₁ - ψ.toFun c₂| := h_eigen
    _ ≤ saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
          * (max 1 L * |c₁ - c₂|) :=
        mul_le_mul_of_nonneg_left hmax hC_nn
    _ = saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
          * max 1 L * |c₁ - c₂| := by ring

/-- The first (stable-axis) component of `flowedPoint` is Lipschitz in `c`
with the same constant as the full flowed point.  This is the bound on the
candidate reparameterization map `c ↦ c'`. -/
theorem SaddleLipCurve_flowedC_dist_le {r L : ℝ} (hL : 0 ≤ L)
    (ψ : SaddleLipCurve r L) {a : ℝ} (F : SaddleLocalFlow a)
    (t : ℝ) (ht : t ∈ Set.Icc (-F.T) F.T) (c₁ c₂ : ℝ)
    (hc₁ : |c₁| ≤ r) (hc₂ : |c₂| ≤ r)
    (h₁ : SaddleLipCurve.graphPoint ψ c₁ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r)
    (h₂ : SaddleLipCurve.graphPoint ψ c₂ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    |SaddleLipCurve.flowedC ψ F t c₁ - SaddleLipCurve.flowedC ψ F t c₂|
      ≤ saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
          * max 1 L * |c₁ - c₂| := by
  have hpt := SaddleLipCurve_flowedPoint_dist_le hL ψ F t ht c₁ c₂ hc₁ hc₂ h₁ h₂
  have hproj :
      |SaddleLipCurve.flowedC ψ F t c₁ - SaddleLipCurve.flowedC ψ F t c₂|
        ≤ dist (SaddleLipCurve.flowedPoint ψ F t c₁)
               (SaddleLipCurve.flowedPoint ψ F t c₂) := by
    unfold SaddleLipCurve.flowedC
    rw [show |(SaddleLipCurve.flowedPoint ψ F t c₁).1
              - (SaddleLipCurve.flowedPoint ψ F t c₂).1|
            = dist (SaddleLipCurve.flowedPoint ψ F t c₁).1
                   (SaddleLipCurve.flowedPoint ψ F t c₂).1
            from (Real.dist_eq _ _).symm,
        Prod.dist_eq]
    exact le_max_left _ _
  exact hproj.trans hpt

/-- The second (unstable-axis) component of `flowedPoint` is Lipschitz in `c`
with the same constant. -/
theorem SaddleLipCurve_flowedD_dist_le {r L : ℝ} (hL : 0 ≤ L)
    (ψ : SaddleLipCurve r L) {a : ℝ} (F : SaddleLocalFlow a)
    (t : ℝ) (ht : t ∈ Set.Icc (-F.T) F.T) (c₁ c₂ : ℝ)
    (hc₁ : |c₁| ≤ r) (hc₂ : |c₂| ≤ r)
    (h₁ : SaddleLipCurve.graphPoint ψ c₁ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r)
    (h₂ : SaddleLipCurve.graphPoint ψ c₂ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    |SaddleLipCurve.flowedD ψ F t c₁ - SaddleLipCurve.flowedD ψ F t c₂|
      ≤ saddleEigenCoordLipConst * (F.L' : ℝ) * saddleFromEigenCoordLipConst
          * max 1 L * |c₁ - c₂| := by
  have hpt := SaddleLipCurve_flowedPoint_dist_le hL ψ F t ht c₁ c₂ hc₁ hc₂ h₁ h₂
  have hproj :
      |SaddleLipCurve.flowedD ψ F t c₁ - SaddleLipCurve.flowedD ψ F t c₂|
        ≤ dist (SaddleLipCurve.flowedPoint ψ F t c₁)
               (SaddleLipCurve.flowedPoint ψ F t c₂) := by
    unfold SaddleLipCurve.flowedD
    rw [show |(SaddleLipCurve.flowedPoint ψ F t c₁).2
              - (SaddleLipCurve.flowedPoint ψ F t c₂).2|
            = dist (SaddleLipCurve.flowedPoint ψ F t c₁).2
                   (SaddleLipCurve.flowedPoint ψ F t c₂).2
            from (Real.dist_eq _ _).symm,
        Prod.dist_eq]
    exact le_max_right _ _
  exact hproj.trans hpt

/-- At `t = 0`, the c-axis flow is exactly the identity, so the
`flowedC` difference equals the input difference.  This is the
"1-bilipschitz at t = 0" base case for the reparameterization
invertibility argument. -/
theorem SaddleLipCurve_flowedC_zero_diff {r L : ℝ}
    (ψ : SaddleLipCurve r L) {a : ℝ} (F : SaddleLocalFlow a)
    (c₁ c₂ : ℝ) (hc₁ : |c₁| ≤ r) (hc₂ : |c₂| ≤ r)
    (h₁ : SaddleLipCurve.graphPoint ψ c₁ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r)
    (h₂ : SaddleLipCurve.graphPoint ψ c₂ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    SaddleLipCurve.flowedC ψ F 0 c₁ - SaddleLipCurve.flowedC ψ F 0 c₂
      = c₁ - c₂ := by
  rw [ψ.flowedC_zero F c₁ hc₁ h₁, ψ.flowedC_zero F c₂ hc₂ h₂]

/-- Symmetric statement on the unstable axis: at `t = 0`, the d-axis
flow returns `ψ c` exactly, so the `flowedD` difference equals
`ψ c₁ - ψ c₂`. -/
theorem SaddleLipCurve_flowedD_zero_diff {r L : ℝ}
    (ψ : SaddleLipCurve r L) {a : ℝ} (F : SaddleLocalFlow a)
    (c₁ c₂ : ℝ) (hc₁ : |c₁| ≤ r) (hc₂ : |c₂| ≤ r)
    (h₁ : SaddleLipCurve.graphPoint ψ c₁ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r)
    (h₂ : SaddleLipCurve.graphPoint ψ c₂ ∈
              Metric.closedBall ((0, 0) : ℝ × ℝ) F.r) :
    SaddleLipCurve.flowedD ψ F 0 c₁ - SaddleLipCurve.flowedD ψ F 0 c₂
      = ψ.toFun c₁ - ψ.toFun c₂ := by
  rw [ψ.flowedD_zero F c₁ hc₁ h₁, ψ.flowedD_zero F c₂ hc₂ h₂]

/-! ### Field-near-saddle decomposition (final wrapper)

The single statement that packages the four analytic layers — Taylor identity
+ remainder bound + vector form — into a `field = linearization + bounded
quadratic` decomposition near `saddlePoint`.  This is the form used by any
graph-transform stable-manifold argument as the contraction-mapping
hypothesis. -/

/-- The field at a perturbed saddle decomposes as `J·p + Q(p)` with `‖Q(p)‖∞`
componentwise bounded by `21·(u² + v²)` (component-wise sup of `33/2` and `21`).

This is the analytic content needed for any Hartman-Grobman / graph-transform
argument: the nonlinear remainder is bounded by `C·‖p‖²` with explicit
constant `C = 21`. -/
theorem field_decomposition_near_saddle (u v : ℝ) :
    let perturbed : Fin 3 → ℝ := fun i => match i with
      | ⟨0, _⟩ => saddlePoint 0 - u - v
      | ⟨1, _⟩ => saddlePoint 1 + u
      | ⟨2, _⟩ => saddlePoint 2 + v
    -- Linear-plus-quadratic decomposition: each (b,c) component is
    -- `(linear part) + (quadratic remainder)`, with the remainder
    -- componentwise bounded by 21·(u² + v²).
    (field perturbed 1 = (saddleJacobianApply (u, v)).1
        + (10 * u^2 - 5 * u * v - 14 * v^2)) ∧
    (field perturbed 2 = (saddleJacobianApply (u, v)).2
        + (-u^2 + 14 * v^2 + 14 * u * v)) ∧
    (|field perturbed 1 - (saddleJacobianApply (u, v)).1| ≤ 21 * (u^2 + v^2)) ∧
    (|field perturbed 2 - (saddleJacobianApply (u, v)).2| ≤ 21 * (u^2 + v^2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- field_1 = J·p + Q_1
    rw [field1_taylor_at_saddle]; unfold saddleJacobianApply; ring
  · -- field_2 = J·p + Q_2
    rw [field2_taylor_at_saddle]; unfold saddleJacobianApply; ring
  · -- |field_1 - linear| ≤ 21·(u²+v²) — using the (33/2)-bound and 33/2 ≤ 21
    have h1 := field1_taylor_remainder_abs u v
    have h_calc :
        field
          (fun i : Fin 3 => match i with
            | ⟨0, _⟩ => saddlePoint 0 - u - v
            | ⟨1, _⟩ => saddlePoint 1 + u
            | ⟨2, _⟩ => saddlePoint 2 + v) 1
          - (saddleJacobianApply (u, v)).1
          = 10 * u^2 - 5 * u * v - 14 * v^2 := by
      rw [field1_taylor_at_saddle]; unfold saddleJacobianApply; ring
    rw [h_calc]
    calc |10 * u^2 - 5 * u * v - 14 * v^2|
        ≤ (33/2) * (u^2 + v^2) := h1
      _ ≤ 21 * (u^2 + v^2) := by
          have hs : 0 ≤ u^2 + v^2 := by positivity
          linarith
  · -- |field_2 - linear| ≤ 21·(u²+v²)
    have h2 := field2_taylor_remainder_abs u v
    have h_calc :
        field
          (fun i : Fin 3 => match i with
            | ⟨0, _⟩ => saddlePoint 0 - u - v
            | ⟨1, _⟩ => saddlePoint 1 + u
            | ⟨2, _⟩ => saddlePoint 2 + v) 2
          - (saddleJacobianApply (u, v)).2
          = -u^2 + 14 * v^2 + 14 * u * v := by
      rw [field2_taylor_at_saddle]; unfold saddleJacobianApply; ring
    rw [h_calc]
    exact h2

/-- **Local field — original-chart agreement.**  At the perturbed point
`saddlePoint + (−(u+v), u, v) ∈ ℝ³`, the (b, c) components of `field` equal
`saddleField (u, v)`.  This is a vector reformulation of
`field_decomposition_near_saddle`. -/
theorem saddleField_eq_field (u v : ℝ) :
    let perturbed : Fin 3 → ℝ := fun i => match i with
      | ⟨0, _⟩ => saddlePoint 0 - u - v
      | ⟨1, _⟩ => saddlePoint 1 + u
      | ⟨2, _⟩ => saddlePoint 2 + v
    field perturbed 1 = (saddleField (u, v)).1
      ∧ field perturbed 2 = (saddleField (u, v)).2 := by
  intro perturbed
  obtain ⟨h1, h2, _, _⟩ := field_decomposition_near_saddle u v
  refine ⟨?_, ?_⟩
  · rw [h1]
    show (saddleJacobianApply (u, v)).1 + (10 * u^2 - 5 * u * v - 14 * v^2)
       = (saddleField (u, v)).1
    unfold saddleField saddleQ
    simp
  · rw [h2]
    show (saddleJacobianApply (u, v)).2 + (-u^2 + 14 * v^2 + 14 * u * v)
       = (saddleField (u, v)).2
    unfold saddleField saddleQ
    simp

/-- `lyapunov x = 0 ⇒ x agrees with the fixed point on components 1, 2`. -/
theorem lyapunov_eq_zero_iff (x : Fin 3 → ℝ) :
    lyapunov x = 0 ↔ x 1 = fixedPoint 1 ∧ x 2 = fixedPoint 2 := by
  unfold lyapunov
  constructor
  · intro h
    have h1 : (x 1 - fixedPoint 1)^2 = 0 ∧ (x 2 - fixedPoint 2)^2 = 0 := by
      constructor
      all_goals linarith [sq_nonneg (x 1 - fixedPoint 1), sq_nonneg (x 2 - fixedPoint 2)]
    refine ⟨?_, ?_⟩
    · have := pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0) |>.mp h1.1
      linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0) |>.mp h1.2
      linarith
  · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

/-! ### Lie derivative of the Lyapunov candidate -/

/-- Formal Lie derivative `V̇(x) = ∇V(x) · field(x)`, expressed on the
3D ambient state.  Along any trajectory `x(t)` that solves
`x'(t) = field x(t)`, we have `d/dt (lyapunov (x t)) = lyapunovDeriv (x t)`. -/
noncomputable def lyapunovDeriv (x : Fin 3 → ℝ) : ℝ :=
  2 * (x 1 - fixedPoint 1) * field x 1 + 2 * (x 2 - fixedPoint 2) * field x 2

/-- The Lie derivative vanishes at the fixed point (since `field` itself vanishes there). -/
theorem lyapunovDeriv_fixedPoint : lyapunovDeriv fixedPoint = 0 := by
  have h := field_fixedPoint
  have h1 : field fixedPoint 1 = 0 := by rw [h]; rfl
  have h2 : field fixedPoint 2 = 0 := by rw [h]; rfl
  unfold lyapunovDeriv
  rw [h1, h2]; ring

/-! ### Negative-definite quadratic form from the symmetrized Jacobian

The linearization contribution to `V̇` at the fixed point is the
quadratic form `(Δb, Δc) ↦ Δx^T (J + J^T) Δx` where `J` is the
Jacobian.  Spelled out:

  Q(u, v) = A·u² + 2B·u·v + C·v²

with `A = (−57 + 5√5)/3`, `B = (18 + 7√5)/3`, `C = −28√5/3`.

Key algebraic identity used in the non-positivity proof:
  A · Q(u, v) = (A·u + B·v)² + (AC − B²)·v²

Since `A < 0` and `AC − B² = (1344√5 − 1269)/9 > 0`, the right-hand
side is a sum of non-negative squares, so `A · Q ≥ 0` and hence
`Q ≤ 0` (dividing by the negative `A`). -/

/-- The symmetrized-Jacobian quadratic form. -/
noncomputable def lyapunovQuad (u v : ℝ) : ℝ :=
  ((-57 + 5 * Real.sqrt 5) / 3) * u^2
    + (2 * (18 + 7 * Real.sqrt 5) / 3) * u * v
    + (-28 * Real.sqrt 5 / 3) * v^2

/-- Coefficient `A = (−57 + 5√5)/3` of the quadratic form is negative. -/
private lemma lyapunovQuad_A_neg : (-57 + 5 * Real.sqrt 5) / 3 < 0 := by
  have h : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h3 : Real.sqrt 5 < 3 := by nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  linarith

/-- `AC − B² = (1344√5 − 1269)/9 > 0`. -/
private lemma lyapunovQuad_discr_pos :
    ((-57 + 5 * Real.sqrt 5) / 3) * (-28 * Real.sqrt 5 / 3)
      - ((18 + 7 * Real.sqrt 5) / 3)^2 > 0 := by
  have h : Real.sqrt 5 * Real.sqrt 5 = 5 := sq_sqrt_five
  have h2 : (2 : ℝ) < Real.sqrt 5 := by
    have hsq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    nlinarith [Real.sqrt_nonneg (5 : ℝ), hsq]
  -- The difference equals (1344·√5 − 1269)/9, positive since √5 > 2 > 1269/1344.
  linarith [h, h2, Real.sqrt_nonneg (5 : ℝ)]

/-- The quadratic form is non-positive everywhere. -/
theorem lyapunovQuad_nonpos (u v : ℝ) : lyapunovQuad u v ≤ 0 := by
  let A : ℝ := (-57 + 5 * Real.sqrt 5) / 3
  let B : ℝ := (18 + 7 * Real.sqrt 5) / 3
  let C : ℝ := -28 * Real.sqrt 5 / 3
  have hA_neg : A < 0 := lyapunovQuad_A_neg
  have hdiscr : A * C - B^2 > 0 := lyapunovQuad_discr_pos
  -- key: A * Q = (A·u + B·v)² + (A·C − B²)·v²
  have key : A * lyapunovQuad u v = (A*u + B*v)^2 + (A*C - B^2) * v^2 := by
    unfold lyapunovQuad
    show A * _ = _
    ring
  have num_nonneg : 0 ≤ (A*u + B*v)^2 + (A*C - B^2) * v^2 := by
    have h1 : 0 ≤ (A*u + B*v)^2 := sq_nonneg _
    have h2 : 0 ≤ (A*C - B^2) * v^2 := mul_nonneg (le_of_lt hdiscr) (sq_nonneg v)
    linarith
  have hAQ : 0 ≤ A * lyapunovQuad u v := by rw [key]; exact num_nonneg
  by_contra hQ_pos
  push_neg at hQ_pos
  have hneg : A * lyapunovQuad u v < 0 :=
    mul_neg_of_neg_of_pos hA_neg hQ_pos
  linarith

/-! ### Decomposition of `field` and `V̇` in shifted coordinates -/

/-- On the simplex `x 0 + x 1 + x 2 = 1`, the second component of the
field factors through the Jacobian column `(J_{11}, J_{12})` plus a
homogeneous quadratic remainder.  The identity holds modulo
`(√5)² = 5`. -/
private lemma field_1_factored (x : Fin 3 → ℝ)
    (hsimplex : x 0 + x 1 + x 2 = 1) :
    field x 1
      = ((-57 + 5 * Real.sqrt 5) / 6) * (x 1 - fixedPoint 1)
        + (14 * Real.sqrt 5 / 3) * (x 2 - fixedPoint 2)
        + 10 * (x 1 - fixedPoint 1)^2
        - 5 * (x 1 - fixedPoint 1) * (x 2 - fixedPoint 2)
        - 14 * (x 2 - fixedPoint 2)^2 := by
  have h5 := sq_sqrt_five
  have hx0 : x 0 = 1 - x 1 - x 2 := by linarith
  simp only [field, fixedPoint]
  rw [hx0]
  linear_combination (-7/18 : ℝ) * h5

/-- Analogous factorization for the third component. -/
private lemma field_2_factored (x : Fin 3 → ℝ)
    (hsimplex : x 0 + x 1 + x 2 = 1) :
    field x 2
      = ((18 - 7 * Real.sqrt 5) / 3) * (x 1 - fixedPoint 1)
        + (-14 * Real.sqrt 5 / 3) * (x 2 - fixedPoint 2)
        - (x 1 - fixedPoint 1)^2
        + 14 * (x 1 - fixedPoint 1) * (x 2 - fixedPoint 2)
        + 14 * (x 2 - fixedPoint 2)^2 := by
  have h5 := sq_sqrt_five
  have hx0 : x 0 = 1 - x 1 - x 2 := by linarith
  simp only [field, fixedPoint]
  rw [hx0]
  linear_combination (7/18 : ℝ) * h5

/-- **Key decomposition**: on the simplex, the Lie derivative `V̇(x)`
splits cleanly into the negative-definite symmetrized-Jacobian
quadratic form plus a cubic remainder with *rational* coefficients
(no `√5`).  This is the algebraic heart of the stability argument. -/
theorem lyapunovDeriv_on_simplex (x : Fin 3 → ℝ)
    (hsimplex : x 0 + x 1 + x 2 = 1) :
    lyapunovDeriv x
      = lyapunovQuad (x 1 - fixedPoint 1) (x 2 - fixedPoint 2)
        + 20 * (x 1 - fixedPoint 1)^3
        - 12 * (x 1 - fixedPoint 1)^2 * (x 2 - fixedPoint 2)
        + 28 * (x 2 - fixedPoint 2)^3 := by
  unfold lyapunovDeriv lyapunovQuad
  rw [field_1_factored x hsimplex, field_2_factored x hsimplex]
  ring

/-! ### Explicit spectral gap for the symmetrized-Jacobian quadratic form -/

/-- `√5 < 3`. -/
private lemma sqrt_five_lt_three : Real.sqrt 5 < 3 := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := sq_sqrt_five
  have hpos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  nlinarith

/-- `11·√5 > 19`, equivalent to `√5 > 19/11 ≈ 1.73` (we have `√5 ≈ 2.24`). -/
private lemma eleven_sqrt_five_gt_nineteen : 11 * Real.sqrt 5 > 19 := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := sq_sqrt_five
  have hpos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  nlinarith

/-- **Spectral gap**: the quadratic form `lyapunovQuad` is bounded above by
`-(13 − 4√5)·(u² + v²)`.  The constant `13 − 4√5 ≈ 4.06` is a concrete
lower bound on the spectral gap; it is attained up to `|A| − |B|` in
the simple off-diagonal AM-GM bound.

Proof: complete the square.  Let `B = (18 + 7√5)/3 > 0`.  A direct
ring identity gives

  Q(u,v) + (13 − 4√5)(u² + v²) = −B·(u − v)² + (19 − 11√5)·v²

and both summands are non-positive: `−B < 0` times a square, and
`19 − 11√5 < 0` (since `11√5 > 19`) times `v² ≥ 0`. -/
theorem lyapunovQuad_le_neg_sq (u v : ℝ) :
    lyapunovQuad u v ≤ -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := sq_sqrt_five
  have hpos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  -- Algebraic identity for the gap-adjusted form.
  have key : lyapunovQuad u v + (13 - 4 * Real.sqrt 5) * (u^2 + v^2)
           = -((18 + 7 * Real.sqrt 5) / 3) * (u - v)^2
             + (19 - 11 * Real.sqrt 5) * v^2 := by
    unfold lyapunovQuad; ring
  have hB_pos : 0 < (18 + 7 * Real.sqrt 5) / 3 := by linarith
  have h19 : 19 - 11 * Real.sqrt 5 < 0 := by
    have := eleven_sqrt_five_gt_nineteen; linarith
  have h1 : -((18 + 7 * Real.sqrt 5) / 3) * (u - v)^2 ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact sq_nonneg _
  have h2 : (19 - 11 * Real.sqrt 5) * v^2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt h19) (sq_nonneg _)
  have sum : lyapunovQuad u v + (13 - 4 * Real.sqrt 5) * (u^2 + v^2) ≤ 0 := by
    rw [key]; linarith
  linarith

/-- The spectral gap `13 − 4√5` is strictly positive. -/
theorem lyapunov_gap_pos : 0 < 13 - 4 * Real.sqrt 5 := by
  have h5 := sqrt_five_lt_three; linarith

/-! ### Cubic-remainder bound on `V̇` -/

/-- Bound on the cubic remainder that appears in `lyapunovDeriv_on_simplex`:

    `|20·u³ − 12·u²·v + 28·v³| ≤ 32·(|u| + |v|)·(u² + v²)`.

This uses the triangle inequality plus the monomial bounds
`|u|·u² ≤ s·(u²+v²)`, `|v|·u² ≤ s·(u²+v²)`, `|v|·v² ≤ s·(u²+v²)` where
`s := |u|+|v|`.  The resulting coefficient `32 = 20 + 12` (on `u²`) /
`28` (on `v²`) is the max, giving `32·s·(u²+v²)`. -/
theorem cubic_remainder_bound (u v : ℝ) :
    |20 * u^3 - 12 * u^2 * v + 28 * v^3|
      ≤ 32 * (|u| + |v|) * (u^2 + v^2) := by
  set s := |u| + |v| with hs_def
  have hu_abs : 0 ≤ |u| := abs_nonneg _
  have hv_abs : 0 ≤ |v| := abs_nonneg _
  have hs_nn : 0 ≤ s := add_nonneg hu_abs hv_abs
  have hu_le : |u| ≤ s := by change |u| ≤ |u| + |v|; linarith
  have hv_le : |v| ≤ s := by change |v| ≤ |u| + |v|; linarith
  have hu2_nn : 0 ≤ u^2 := sq_nonneg _
  have hv2_nn : 0 ≤ v^2 := sq_nonneg _
  have hu2_eq : |u|^2 = u^2 := sq_abs u
  have hv2_eq : |v|^2 = v^2 := sq_abs v
  -- Triangle inequality
  have htri : |20 * u^3 - 12 * u^2 * v + 28 * v^3|
              ≤ |20 * u^3| + |12 * u^2 * v| + |28 * v^3| := by
    have hrewrite : (20 * u^3 - 12 * u^2 * v + 28 * v^3)
                  = 20 * u^3 + (-(12 * u^2 * v)) + 28 * v^3 := by ring
    rw [hrewrite]
    have hthree := abs_add_three (20 * u^3) (-(12 * u^2 * v)) (28 * v^3)
    rw [abs_neg] at hthree
    exact hthree
  -- Absolute values of the monomials
  have habs1 : |20 * u^3| = 20 * |u| * u^2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 20)]
    have : |u^3| = |u| * u^2 := by
      rw [show u^3 = u * u^2 from by ring, abs_mul, abs_of_nonneg hu2_nn]
    rw [this]; ring
  have habs2 : |12 * u^2 * v| = 12 * u^2 * |v| := by
    rw [show (12 : ℝ) * u^2 * v = 12 * u^2 * v from rfl]
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 12),
        abs_of_nonneg hu2_nn]
  have habs3 : |28 * v^3| = 28 * |v| * v^2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 28)]
    have : |v^3| = |v| * v^2 := by
      rw [show v^3 = v * v^2 from by ring, abs_mul, abs_of_nonneg hv2_nn]
    rw [this]; ring
  -- Monomial bounds
  have h1 : 20 * |u| * u^2 ≤ 20 * s * u^2 := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu_le (by norm_num : (0:ℝ) ≤ 20)) hu2_nn
    linarith
  have h2 : 12 * u^2 * |v| ≤ 12 * s * u^2 := by
    have h_v_u2 : u^2 * |v| ≤ u^2 * s :=
      mul_le_mul_of_nonneg_left hv_le hu2_nn
    linarith
  have h3 : 28 * |v| * v^2 ≤ 28 * s * v^2 := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv_le (by norm_num : (0:ℝ) ≤ 28)) hv2_nn
    linarith
  -- Total bound: 20·s·u² + 12·s·u² + 28·s·v² = 32·s·u² + 28·s·v² ≤ 32·s·(u²+v²).
  have htotal : |20 * u^3| + |12 * u^2 * v| + |28 * v^3|
                  ≤ 32 * s * (u^2 + v^2) := by
    rw [habs1, habs2, habs3]
    have hsu2 : 0 ≤ s * u^2 := mul_nonneg hs_nn hu2_nn
    have hsv2 : 0 ≤ s * v^2 := mul_nonneg hs_nn hv2_nn
    linarith
  linarith

/-- **Sharp squared bound on the cubic remainder**:

    `(20·u³ − 12·u²·v + 28·v³)² ≤ 784 · (u² + v²)³`.

This is sharper than the L¹ bound `cubic_remainder_bound`: extracting the
square root gives `|cubic| ≤ 28·(u²+v²)^{3/2} = 28·V·√V`, so on the
V-sublevel `V ≤ δ²` the cubic contributes at most `28·δ·V` to `V̇`,
versus `32·δ·V` from the L¹ route.  This widens the basin from
`(13−4√5)²/2048 ≈ 1/124.6` to `(13−4√5)²/784 ≈ 1/47.7`.

The constant `784 = 28²` is sharp; `linarith` discharges this directly
with a generous list of square-nonnegativity hints. -/
theorem cubic_remainder_bound_sq (u v : ℝ) :
    (20 * u^3 - 12 * u^2 * v + 28 * v^3)^2
      ≤ 784 * (u^2 + v^2)^3 := by
  nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u - v), sq_nonneg (u + v),
             sq_nonneg (u^2 - v^2), sq_nonneg (u^2 + v^2),
             sq_nonneg (u^3 - v^3), sq_nonneg (u^3 + v^3),
             sq_nonneg (u^2 * v - u * v^2), sq_nonneg (u^2 * v + u * v^2),
             sq_nonneg (2 * u - v), sq_nonneg (2 * u + v),
             sq_nonneg (u - 2 * v), sq_nonneg (u + 2 * v),
             sq_nonneg (u^2 - 2 * v^2), sq_nonneg (2 * u^2 - v^2),
             sq_nonneg (u * (u - v)), sq_nonneg (v * (u + v)),
             sq_nonneg (20 * u^3 - 12 * u^2 * v + 28 * v^3),
             sq_nonneg (5 * u^3 - 3 * u^2 * v + 7 * v^3),
             sq_nonneg (u^2 * v + u * v^2 - v^3),
             mul_self_nonneg (u * v)]

/-! ### Combined small-ball negativity of `V̇` -/

/-- On the simplex, within the ball `|Δb| + |Δc| ≤ 1/16`, the Lie derivative
of the Lyapunov function along the CF'24 field satisfies

    `V̇(x) ≤ −(11 − 4√5) · ((x₁ − b*)² + (x₂ − c*)²)`.

The constant `11 − 4√5 ≈ 2.06 > 0` is the residual gap after absorbing the
cubic remainder into the quadratic form:
`V̇ ≤ −(13 − 4√5)·R² + 32·(1/16)·R² = −(11 − 4√5)·R²`, where `R² := Δb²+Δc²`.

This is the local asymptotic-stability certificate for the fixed point. -/
theorem lyapunovDeriv_le_small_ball (x : Fin 3 → ℝ)
    (hsimplex : x 0 + x 1 + x 2 = 1)
    (hball : |x 1 - fixedPoint 1| + |x 2 - fixedPoint 2| ≤ 1 / 16) :
    lyapunovDeriv x
      ≤ -(11 - 4 * Real.sqrt 5)
          * ((x 1 - fixedPoint 1)^2 + (x 2 - fixedPoint 2)^2) := by
  set u := x 1 - fixedPoint 1 with hu_def
  set v := x 2 - fixedPoint 2 with hv_def
  -- Exact decomposition from the polynomial factorization on the simplex.
  have hdecomp : lyapunovDeriv x
      = lyapunovQuad u v + 20 * u^3 - 12 * u^2 * v + 28 * v^3 := by
    have := lyapunovDeriv_on_simplex x hsimplex
    simpa [hu_def, hv_def] using this
  -- Spectral gap bound on the quadratic part.
  have hQ : lyapunovQuad u v ≤ -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) :=
    lyapunovQuad_le_neg_sq u v
  -- Cubic bound.
  have hR_abs : |20 * u^3 - 12 * u^2 * v + 28 * v^3|
                  ≤ 32 * (|u| + |v|) * (u^2 + v^2) := cubic_remainder_bound u v
  -- The remainder itself is bounded above by its absolute value.
  have hR : 20 * u^3 - 12 * u^2 * v + 28 * v^3
              ≤ 32 * (|u| + |v|) * (u^2 + v^2) :=
    le_of_abs_le hR_abs
  -- Shrink the radius factor using the small-ball hypothesis.
  have hsum_nn : 0 ≤ u^2 + v^2 := by positivity
  have hshrink : 32 * (|u| + |v|) * (u^2 + v^2) ≤ 2 * (u^2 + v^2) := by
    have h32 : 32 * (|u| + |v|) ≤ 2 := by
      have : (|u| + |v|) ≤ 1/16 := hball
      linarith
    nlinarith
  -- Combine: V̇ ≤ [-(13-4√5) + 2] · (u²+v²) = -(11 - 4√5) · (u²+v²).
  have hfinal : lyapunovDeriv x
      ≤ -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) + 2 * (u^2 + v^2) := by
    linarith
  have : -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) + 2 * (u^2 + v^2)
        = -(11 - 4 * Real.sqrt 5) * (u^2 + v^2) := by ring
  linarith

/-- The residual spectral gap `11 − 4√5 > 0`: strict negativity of `V̇`
on the small ball, away from the fixed point. -/
theorem lyapunov_residual_gap_pos : 0 < 11 - 4 * Real.sqrt 5 := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := sq_sqrt_five
  have hpos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  nlinarith

/-! ### Chain rule + composite local-exponential-decay theorem

With `lyapunovDeriv_le_small_ball` giving `V̇ ≤ -α·V` on the simplex inside
the ball `|Δb|+|Δc| ≤ 1/16`, we compose with the scalar decay lemma
`Ripple.scalar_exponential_decay` to get the local convergence rate for any
trajectory that *stays inside the ball* — the invariance itself is left as
a hypothesis here (a separate ODE argument). -/

/-- Restating the small-ball estimate in terms of `lyapunov x`: this is
just `V̇ ≤ -α · V` where `V := lyapunov` (the sum of squares). -/
theorem lyapunovDeriv_le_neg_alpha_lyapunov (x : Fin 3 → ℝ)
    (hsimplex : x 0 + x 1 + x 2 = 1)
    (hball : |x 1 - fixedPoint 1| + |x 2 - fixedPoint 2| ≤ 1 / 16) :
    lyapunovDeriv x ≤ -(11 - 4 * Real.sqrt 5) * lyapunov x := by
  have := lyapunovDeriv_le_small_ball x hsimplex hball
  simpa [lyapunov] using this

/-- **Chain rule for the Lyapunov function along a trajectory** (right derivative).

If the coordinates `x · 1` and `x · 2` have right-derivatives `field (x t) 1`
and `field (x t) 2` at `t`, then `s ↦ lyapunov (x s)` has right-derivative
`lyapunovDeriv (x t)` at `t`. -/
theorem lyapunov_hasDerivWithinAt {x : ℝ → Fin 3 → ℝ} {t : ℝ} {S : Set ℝ}
    (h1 : HasDerivWithinAt (fun s => x s 1) (field (x t) 1) S t)
    (h2 : HasDerivWithinAt (fun s => x s 2) (field (x t) 2) S t) :
    HasDerivWithinAt (fun s => lyapunov (x s)) (lyapunovDeriv (x t)) S t := by
  have g1 := (h1.sub_const (fixedPoint 1)).pow 2
  have g2 := (h2.sub_const (fixedPoint 2)).pow 2
  have gsum := g1.add g2
  have hfun : (fun s => (x s 1 - fixedPoint 1) ^ 2 + (x s 2 - fixedPoint 2) ^ 2)
            = (fun s => lyapunov (x s)) := by
    funext s; simp [lyapunov]
  have hderiv :
      ((2 : ℕ) : ℝ) * (x t 1 - fixedPoint 1) ^ (2 - 1) * field (x t) 1
        + ((2 : ℕ) : ℝ) * (x t 2 - fixedPoint 2) ^ (2 - 1) * field (x t) 2
      = lyapunovDeriv (x t) := by
    simp only [lyapunovDeriv]; push_cast; ring
  rw [← hfun, ← hderiv]
  exact gsum

/-- **CF'24 local exponential decay.**

If a trajectory `x : ℝ → Fin 3 → ℝ` of the CF'24 field stays on the simplex
and inside the ball `|Δb| + |Δc| ≤ 1/16` throughout `[0, T]`, then
`lyapunov (x t) ≤ lyapunov (x 0) · exp(-(11 − 4√5) · t)` for `t ∈ [0, T]`.

This is the quantitative local asymptotic-stability statement: under
forward invariance of the small ball (which itself follows from the
decay, by a standard continuity argument not formalized here), the
Lyapunov function decays exponentially with rate `11 − 4√5`. -/
theorem cf24_local_exponential_decay_of_ball
    {x : ℝ → Fin 3 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Icc 0 T))
    (hx_deriv_b : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ico (0 : ℝ) T, x t 0 + x t 1 + x t 2 = 1)
    (hx_ball : ∀ t ∈ Set.Ico (0 : ℝ) T,
       |x t 1 - fixedPoint 1| + |x t 2 - fixedPoint 2| ≤ 1 / 16) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      lyapunov (x t) ≤ lyapunov (x 0) * Real.exp (-(11 - 4 * Real.sqrt 5) * t) :=
  Ripple.scalar_exponential_decay
    (V := fun t => lyapunov (x t))
    (V' := fun t => lyapunovDeriv (x t))
    (α := 11 - 4 * Real.sqrt 5) (T := T)
    lyapunov_residual_gap_pos hT hV_cont
    (fun t ht => lyapunov_hasDerivWithinAt (hx_deriv_b t ht) (hx_deriv_c t ht))
    (fun t ht => lyapunovDeriv_le_neg_alpha_lyapunov (x t)
                   (hx_simplex t ht) (hx_ball t ht))

/-! ### Forward-invariance of the small ball

The previous decay theorem `cf24_local_exponential_decay_of_ball` required a
hypothesis that the trajectory stays in the `ℓ¹`-ball of radius `1/16`
for all `t ∈ [0, T]`. We now close this hypothesis by proving forward
invariance of the *sublevel set* `{V ≤ V(x 0)}` whenever `V(x 0) < 1/512`:
the ℓ²→ℓ¹ Cauchy-Schwarz estimate `|Δb|+|Δc| ≤ √2·√V` then shows that
`V ≤ V(x 0) < 1/512` forces `|Δb|+|Δc| ≤ 1/16`, so the small-ball bound
applies and in fact `V̇ < 0`, which by the strict-boundary fencing lemma
locks `V ≤ V(x 0)` along the trajectory. -/

/-- **ℓ¹ bounded by ℓ² in 2D (Cauchy–Schwarz).**
`(|a|+|b|)² ≤ 2·(a²+b²)`, hence `|a|+|b| ≤ √2 · √(a²+b²)`. -/
lemma ell1_le_sqrt_two_mul_sqrt_sq_add_sq (a b : ℝ) :
    |a| + |b| ≤ Real.sqrt 2 * Real.sqrt (a^2 + b^2) := by
  have habsq : |a|^2 = a^2 := sq_abs a
  have hbsq  : |b|^2 = b^2 := sq_abs b
  have hcs : (|a| + |b|)^2 ≤ 2 * (a^2 + b^2) := by
    have h := sq_nonneg (|a| - |b|)
    linarith [habsq, hbsq, h]
  have hnn : 0 ≤ |a| + |b| := by positivity
  have hsum_nn : 0 ≤ a^2 + b^2 := by positivity
  have hmul : Real.sqrt 2 * Real.sqrt (a^2 + b^2) = Real.sqrt (2 * (a^2 + b^2)) :=
    (Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) _).symm
  rw [hmul, ← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hcs

/-- If `V(x) ≤ V₀ < 1/512`, then `|Δb|+|Δc| ≤ 1/16`. -/
lemma ball_of_lyapunov_le (x : Fin 3 → ℝ) {V₀ : ℝ}
    (hV_le : lyapunov x ≤ V₀) (hV₀ : V₀ ≤ 1 / 512) :
    |x 1 - fixedPoint 1| + |x 2 - fixedPoint 2| ≤ 1/16 := by
  set u := x 1 - fixedPoint 1
  set v := x 2 - fixedPoint 2
  have hell2 : |u| + |v| ≤ Real.sqrt 2 * Real.sqrt (u^2 + v^2) :=
    ell1_le_sqrt_two_mul_sqrt_sq_add_sq u v
  have hV : u^2 + v^2 ≤ 1/512 := by
    have : lyapunov x = u^2 + v^2 := rfl
    linarith [this.symm.le, hV_le, hV₀]
  have h2nn : (0:ℝ) ≤ 2 := by norm_num
  have h512 : (0:ℝ) ≤ 1/512 := by norm_num
  have h_sum_nn : (0:ℝ) ≤ u^2 + v^2 := by positivity
  have hsqrt_bound : Real.sqrt (u^2 + v^2) ≤ Real.sqrt (1/512) :=
    Real.sqrt_le_sqrt hV
  have hmul_mono :
      Real.sqrt 2 * Real.sqrt (u^2 + v^2) ≤ Real.sqrt 2 * Real.sqrt (1/512) :=
    mul_le_mul_of_nonneg_left hsqrt_bound (Real.sqrt_nonneg _)
  have hcollapse : Real.sqrt 2 * Real.sqrt (1/512) = (1:ℝ)/16 := by
    rw [← Real.sqrt_mul h2nn]
    have h1_256 : (2 : ℝ) * (1/512) = 1/256 := by norm_num
    rw [h1_256]
    have h256_eq : (1/256 : ℝ) = (1/16)^2 := by norm_num
    rw [h256_eq, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/16)]
  linarith [hell2, hmul_mono, hcollapse.le]

/-- **Forward invariance of the Lyapunov sublevel set.**

If `0 < V(x 0) < 1/512` and the trajectory has the usual continuity and
right-derivative properties on `[0, T]`, then `V(x t) ≤ V(x 0)` for all
`t ∈ [0, T]`. Proof: strict-boundary fencing with constant boundary
`B(t) := V(x 0)`; the boundary-touch condition `V(x t) = V(x 0)` forces
`|Δb|+|Δc| ≤ 1/16` via ℓ²→ℓ¹, hence `V̇ ≤ -α·V(x 0) < 0 = B'`. -/
theorem cf24_lyapunov_forward_invariant
    {x : ℝ → Fin 3 → ℝ} {T : ℝ} (_hT : 0 ≤ T)
    (hV0_pos : 0 < lyapunov (x 0))
    (hV0_small : lyapunov (x 0) < 1 / 512)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Icc 0 T))
    (hx_deriv_b : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ico (0 : ℝ) T, x t 0 + x t 1 + x t 2 = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, lyapunov (x t) ≤ lyapunov (x 0) := by
  refine image_le_of_deriv_right_lt_deriv_boundary
    (f := fun t => lyapunov (x t))
    (f' := fun t => lyapunovDeriv (x t))
    (B := fun _ => lyapunov (x 0))
    (B' := fun _ => 0)
    hV_cont
    (fun t ht => lyapunov_hasDerivWithinAt (hx_deriv_b t ht) (hx_deriv_c t ht))
    (le_refl _) (fun _ => hasDerivAt_const _ _) ?_
  intro t ht hV_eq
  -- Beta-reduce the hypothesis.
  simp only at hV_eq
  -- At the boundary-touch point, V(x t) = V(x 0) < 1/512.
  have hV_bound : lyapunov (x t) ≤ 1 / 512 := hV_eq.trans_lt hV0_small |>.le
  have h_in_ball : |x t 1 - fixedPoint 1| + |x t 2 - fixedPoint 2| ≤ 1 / 16 :=
    ball_of_lyapunov_le (x t) (le_refl _) hV_bound
  have hbound := lyapunovDeriv_le_neg_alpha_lyapunov (x t) (hx_simplex t ht) h_in_ball
  have hV_pos_t : 0 < lyapunov (x t) := hV_eq ▸ hV0_pos
  have hα : 0 < 11 - 4 * Real.sqrt 5 := lyapunov_residual_gap_pos
  have : -(11 - 4 * Real.sqrt 5) * lyapunov (x t) < 0 := by
    have := mul_pos hα hV_pos_t
    linarith
  linarith [hbound, this]

/-- **CF'24 local exponential decay — unconditional form.**

Combining forward invariance with `cf24_local_exponential_decay_of_ball`: on any
trajectory of the CF'24 field that starts with `0 < V(x 0) < 1/512`, the
Lyapunov function decays exponentially with rate `11 − 4√5`, with no ball
hypothesis needed. -/
theorem cf24_local_exponential_decay
    {x : ℝ → Fin 3 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hV0_pos : 0 < lyapunov (x 0))
    (hV0_small : lyapunov (x 0) < 1 / 512)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Icc 0 T))
    (hx_deriv_b : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ico (0 : ℝ) T, x t 0 + x t 1 + x t 2 = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      lyapunov (x t) ≤ lyapunov (x 0) * Real.exp (-(11 - 4 * Real.sqrt 5) * t) := by
  have hinv := cf24_lyapunov_forward_invariant hT hV0_pos hV0_small hV_cont
    hx_deriv_b hx_deriv_c hx_simplex
  have hball : ∀ t ∈ Set.Ico (0 : ℝ) T,
      |x t 1 - fixedPoint 1| + |x t 2 - fixedPoint 2| ≤ 1/16 := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1, ht.2.le⟩
    exact ball_of_lyapunov_le (x t) (hinv t ht_icc) hV0_small.le
  exact cf24_local_exponential_decay_of_ball hT hV_cont hx_deriv_b hx_deriv_c hx_simplex hball

/-! ### Parametric extension of the local-decay chain (overnight 2026-04-25)

The concrete chain above is hardcoded at the threshold `V(x 0) < 1/512`,
which is the largest sublevel set whose ℓ² → ℓ¹ Cauchy–Schwarz inflation
fits inside the small ball `|Δb|+|Δc| ≤ 1/16` where the cubic-remainder
shrinks to `2 ≤ 13 − 4√5 − 2 = 11 − 4√5`.

The same argument works at *any* L¹ ball radius `δ` with
`32·δ < 13 − 4√5`.  The corresponding sublevel threshold is
`ρ(δ) = δ²/2`, and the residual decay rate is
`α(δ) = (13 − 4√5) − 32·δ`.  We expose a parametric chain so a future
"corrected basin-entry" argument can use *any* `(δ, ρ, α)` triple
satisfying the constraint.  The hardcoded version above is recovered at
`δ = 1/16`, `ρ = 1/512`, `α = 11 − 4√5`.

A concrete corollary at `δ = 1/8`, `ρ = 1/128`, `α = 9 − 4√5`
is materialized as `cf24_basinEntry_from_medium_init` further down (this
is the largest clean rational sublevel — the analytic ceiling is
`(13−4√5)²/2048 ≈ 1/124.6`). -/

/-- **Parametric small-ball estimate.** -/
theorem lyapunovDeriv_le_small_ball_param (δ : ℝ)
    (hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5)
    (x : Fin 3 → ℝ)
    (hsimplex : x 0 + x 1 + x 2 = 1)
    (hball : |x 1 - fixedPoint 1| + |x 2 - fixedPoint 2| ≤ δ) :
    lyapunovDeriv x
      ≤ -((13 - 4 * Real.sqrt 5) - 32 * δ)
          * ((x 1 - fixedPoint 1)^2 + (x 2 - fixedPoint 2)^2) := by
  set u := x 1 - fixedPoint 1 with hu_def
  set v := x 2 - fixedPoint 2 with hv_def
  have hdecomp : lyapunovDeriv x
      = lyapunovQuad u v + 20 * u^3 - 12 * u^2 * v + 28 * v^3 := by
    have := lyapunovDeriv_on_simplex x hsimplex
    simpa [hu_def, hv_def] using this
  have hQ : lyapunovQuad u v ≤ -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) :=
    lyapunovQuad_le_neg_sq u v
  have hR_abs : |20 * u^3 - 12 * u^2 * v + 28 * v^3|
                  ≤ 32 * (|u| + |v|) * (u^2 + v^2) := cubic_remainder_bound u v
  have hR : 20 * u^3 - 12 * u^2 * v + 28 * v^3
              ≤ 32 * (|u| + |v|) * (u^2 + v^2) :=
    le_of_abs_le hR_abs
  have hsum_nn : 0 ≤ u^2 + v^2 := by positivity
  have hsum_le_δ : (|u| + |v|) ≤ δ := hball
  have hshrink : 32 * (|u| + |v|) * (u^2 + v^2) ≤ 32 * δ * (u^2 + v^2) := by
    have h32 : 32 * (|u| + |v|) ≤ 32 * δ := by linarith
    nlinarith
  -- V̇ ≤ -(13-4√5)·R² + 32δ·R² = -[(13-4√5) - 32δ]·R².
  have hfinal : lyapunovDeriv x
      ≤ -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) + 32 * δ * (u^2 + v^2) := by
    linarith
  have heq : -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) + 32 * δ * (u^2 + v^2)
        = -((13 - 4 * Real.sqrt 5) - 32 * δ) * (u^2 + v^2) := by ring
  linarith

/-- **Parametric residual decay rate** restated using `lyapunov`. -/
theorem lyapunovDeriv_le_neg_alpha_lyapunov_param (δ : ℝ)
    (hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5)
    (x : Fin 3 → ℝ)
    (hsimplex : x 0 + x 1 + x 2 = 1)
    (hball : |x 1 - fixedPoint 1| + |x 2 - fixedPoint 2| ≤ δ) :
    lyapunovDeriv x
      ≤ -((13 - 4 * Real.sqrt 5) - 32 * δ) * lyapunov x := by
  have := lyapunovDeriv_le_small_ball_param δ hδ_lt x hsimplex hball
  simpa [lyapunov] using this

/-- **Parametric ball-from-sublevel.** If `V(x) ≤ V₀` and `2·V₀ ≤ δ²`,
then `|Δb|+|Δc| ≤ δ`. -/
lemma ball_of_lyapunov_le_param (x : Fin 3 → ℝ) {V₀ δ : ℝ}
    (hV_le : lyapunov x ≤ V₀) (hδ_nn : 0 ≤ δ) (hbound : 2 * V₀ ≤ δ^2) :
    |x 1 - fixedPoint 1| + |x 2 - fixedPoint 2| ≤ δ := by
  set u := x 1 - fixedPoint 1
  set v := x 2 - fixedPoint 2
  have hell2 : |u| + |v| ≤ Real.sqrt 2 * Real.sqrt (u^2 + v^2) :=
    ell1_le_sqrt_two_mul_sqrt_sq_add_sq u v
  have hV : u^2 + v^2 ≤ V₀ := by
    have : lyapunov x = u^2 + v^2 := rfl
    linarith
  have h2nn : (0:ℝ) ≤ 2 := by norm_num
  have h_sum_nn : (0:ℝ) ≤ u^2 + v^2 := by positivity
  have h2V_le_δ2 : 2 * (u^2 + v^2) ≤ δ^2 := by linarith
  have hsqrt : Real.sqrt (2 * (u^2 + v^2)) ≤ Real.sqrt (δ^2) :=
    Real.sqrt_le_sqrt h2V_le_δ2
  have hsqrt_eq : Real.sqrt (δ^2) = δ := Real.sqrt_sq hδ_nn
  have hmul : Real.sqrt 2 * Real.sqrt (u^2 + v^2) = Real.sqrt (2 * (u^2 + v^2)) :=
    (Real.sqrt_mul h2nn _).symm
  linarith [hsqrt, hsqrt_eq.le, hmul.le]

/-- **Parametric forward invariance.**  If `0 < V(x 0)` and `2·V(x 0) ≤ δ²`
with `32·δ < 13 − 4√5`, then `V(x t) ≤ V(x 0)` for all `t ∈ [0, T]`. -/
theorem cf24_lyapunov_forward_invariant_param
    {x : ℝ → Fin 3 → ℝ} {T : ℝ} (_hT : 0 ≤ T)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5)
    (hV0_pos : 0 < lyapunov (x 0))
    (hV0_small : 2 * lyapunov (x 0) ≤ δ^2)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Icc 0 T))
    (hx_deriv_b : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ico (0 : ℝ) T, x t 0 + x t 1 + x t 2 = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, lyapunov (x t) ≤ lyapunov (x 0) := by
  refine image_le_of_deriv_right_lt_deriv_boundary
    (f := fun t => lyapunov (x t))
    (f' := fun t => lyapunovDeriv (x t))
    (B := fun _ => lyapunov (x 0))
    (B' := fun _ => 0)
    hV_cont
    (fun t ht => lyapunov_hasDerivWithinAt (hx_deriv_b t ht) (hx_deriv_c t ht))
    (le_refl _) (fun _ => hasDerivAt_const _ _) ?_
  intro t ht hV_eq
  simp only at hV_eq
  -- V(x t) = V(x 0): use param ball-from-sublevel.
  have hV_le_self : lyapunov (x t) ≤ lyapunov (x 0) := hV_eq.le
  have h2V_le : 2 * lyapunov (x t) ≤ δ^2 := by linarith
  have h_in_ball : |x t 1 - fixedPoint 1| + |x t 2 - fixedPoint 2| ≤ δ :=
    ball_of_lyapunov_le_param (x t) (le_refl _) hδ_nn h2V_le
  have hbound :=
    lyapunovDeriv_le_neg_alpha_lyapunov_param δ hδ_lt (x t)
      (hx_simplex t ht) h_in_ball
  have hV_pos_t : 0 < lyapunov (x t) := hV_eq ▸ hV0_pos
  have hα_pos : 0 < (13 - 4 * Real.sqrt 5) - 32 * δ := by linarith
  have : -((13 - 4 * Real.sqrt 5) - 32 * δ) * lyapunov (x t) < 0 := by
    have := mul_pos hα_pos hV_pos_t; linarith
  linarith

/-- **Parametric local exponential decay** (composition with
`Ripple.scalar_exponential_decay`). -/
theorem cf24_local_exponential_decay_param_of_ball
    {x : ℝ → Fin 3 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (δ : ℝ) (hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Icc 0 T))
    (hx_deriv_b : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ico (0 : ℝ) T, x t 0 + x t 1 + x t 2 = 1)
    (hx_ball : ∀ t ∈ Set.Ico (0 : ℝ) T,
       |x t 1 - fixedPoint 1| + |x t 2 - fixedPoint 2| ≤ δ) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      lyapunov (x t) ≤ lyapunov (x 0)
        * Real.exp (-((13 - 4 * Real.sqrt 5) - 32 * δ) * t) := by
  have hα_pos : 0 < (13 - 4 * Real.sqrt 5) - 32 * δ := by linarith
  exact Ripple.scalar_exponential_decay
    (V := fun t => lyapunov (x t))
    (V' := fun t => lyapunovDeriv (x t))
    (α := (13 - 4 * Real.sqrt 5) - 32 * δ) (T := T)
    hα_pos hT hV_cont
    (fun t ht => lyapunov_hasDerivWithinAt (hx_deriv_b t ht) (hx_deriv_c t ht))
    (fun t ht => lyapunovDeriv_le_neg_alpha_lyapunov_param δ hδ_lt (x t)
                   (hx_simplex t ht) (hx_ball t ht))

/-- **Parametric unconditional decay** — combines forward invariance and
exponential decay, parameterized by an L¹ radius `δ`.  Specializing at
`δ = 1/16` recovers `cf24_local_exponential_decay`. -/
theorem cf24_local_exponential_decay_param
    {x : ℝ → Fin 3 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5)
    (hV0_pos : 0 < lyapunov (x 0))
    (hV0_small : 2 * lyapunov (x 0) ≤ δ^2)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Icc 0 T))
    (hx_deriv_b : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ico (0 : ℝ) T, x t 0 + x t 1 + x t 2 = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      lyapunov (x t) ≤ lyapunov (x 0)
        * Real.exp (-((13 - 4 * Real.sqrt 5) - 32 * δ) * t) := by
  have hinv := cf24_lyapunov_forward_invariant_param hT δ hδ_nn hδ_lt
    hV0_pos hV0_small hV_cont hx_deriv_b hx_deriv_c hx_simplex
  have hball : ∀ t ∈ Set.Ico (0 : ℝ) T,
      |x t 1 - fixedPoint 1| + |x t 2 - fixedPoint 2| ≤ δ := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1, ht.2.le⟩
    have h2V_le : 2 * lyapunov (x t) ≤ δ^2 := by
      have := hinv t ht_icc; linarith
    exact ball_of_lyapunov_le_param (x t) (le_refl _) hδ_nn h2V_le
  exact cf24_local_exponential_decay_param_of_ball hT δ hδ_lt hV_cont
    hx_deriv_b hx_deriv_c hx_simplex hball

/-! ### Sharp parametric chain — V-sublevel forward invariance (28·δ rate)

The L¹-ball chain above absorbs the cubic remainder via
`|cubic| ≤ 32·(|u|+|v|)·V`, giving a decay rate `(13−4√5) − 32·δ` and a
basin ceiling `V₀ < (13−4√5)²/2048 ≈ 1/124.6`.

The sharper estimate
  `(20·u³ − 12·u²·v + 28·v³)² ≤ 784 · (u²+v²)³`     -- `cubic_remainder_bound_sq`
yields `|cubic| ≤ 28·V·√V`, so on the V-sublevel `V(x) ≤ δ²` we get
`|cubic| ≤ 28·δ·V` directly — without any L¹-ball detour.  The decay
rate becomes `(13−4√5) − 28·δ`, the analytic-ceiling constraint becomes
`28·δ < 13−4√5`, and the basin extends to
`V₀ < (13−4√5)²/784 ≈ 1/47.7`, a 2.6× improvement.

Forward invariance is also simpler in this formulation: since `V` is a
Lyapunov function (`V̇ ≤ -α·V` whenever `V ≤ δ²`), the sublevel set
`{V ≤ δ²}` is forward-invariant by Grönwall. -/

/-- **Sharp parametric small-ball estimate** (V-sublevel form).

If `V(x) ≤ δ²` (and `δ ≥ 0`), then
  `V̇ ≤ -((13 − 4√5) − 28·δ) · V`.

This is the V-sublevel analogue of `lyapunovDeriv_le_neg_alpha_lyapunov_param`
with the *sharp* constant `28` replacing `32`, valid because we control
`u²+v² ≤ δ²` instead of the strictly stronger `|u|+|v| ≤ δ`. -/
theorem lyapunovDeriv_le_sublevel_sharp (δ : ℝ) (hδ_nn : 0 ≤ δ)
    (x : Fin 3 → ℝ)
    (hsimplex : x 0 + x 1 + x 2 = 1)
    (hV_le : lyapunov x ≤ δ^2) :
    lyapunovDeriv x ≤ -((13 - 4 * Real.sqrt 5) - 28 * δ) * lyapunov x := by
  set u := x 1 - fixedPoint 1 with hu_def
  set v := x 2 - fixedPoint 2 with hv_def
  have hV_eq : lyapunov x = u^2 + v^2 := rfl
  have hV_nn : 0 ≤ u^2 + v^2 := by positivity
  have hdecomp : lyapunovDeriv x
      = lyapunovQuad u v + 20 * u^3 - 12 * u^2 * v + 28 * v^3 := by
    have := lyapunovDeriv_on_simplex x hsimplex
    simpa [hu_def, hv_def] using this
  have hQ : lyapunovQuad u v ≤ -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) :=
    lyapunovQuad_le_neg_sq u v
  -- Sharp polynomial bound: (cubic)² ≤ 784·V³.
  have h_cubic_sq : (20 * u^3 - 12 * u^2 * v + 28 * v^3)^2
                      ≤ 784 * (u^2 + v^2)^3 := cubic_remainder_bound_sq u v
  -- Take sqrt: |cubic| ≤ 28·(u²+v²)·√(u²+v²).
  have h_abs_cubic : |20 * u^3 - 12 * u^2 * v + 28 * v^3|
                      ≤ 28 * (u^2 + v^2) * Real.sqrt (u^2 + v^2) := by
    have h_sqrt_le :
        Real.sqrt ((20 * u^3 - 12 * u^2 * v + 28 * v^3)^2)
          ≤ Real.sqrt (784 * (u^2 + v^2)^3) :=
      Real.sqrt_le_sqrt h_cubic_sq
    rw [Real.sqrt_sq_eq_abs] at h_sqrt_le
    -- Rewrite RHS as (28·(u²+v²))² · (u²+v²) to extract sqrt cleanly.
    have hrew : (784 : ℝ) * (u^2 + v^2)^3
              = (28 * (u^2 + v^2))^2 * (u^2 + v^2) := by ring
    rw [hrew, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (by positivity : (0:ℝ) ≤ 28 * (u^2 + v^2))] at h_sqrt_le
    exact h_sqrt_le
  -- √(u²+v²) ≤ δ from V(x) ≤ δ².
  have h_sqrt_V_le : Real.sqrt (u^2 + v^2) ≤ δ := by
    have hV_uv : u^2 + v^2 ≤ δ^2 := by rw [← hV_eq]; exact hV_le
    have h_sqrt_le : Real.sqrt (u^2 + v^2) ≤ Real.sqrt (δ^2) :=
      Real.sqrt_le_sqrt hV_uv
    rwa [Real.sqrt_sq hδ_nn] at h_sqrt_le
  -- Combine: |cubic| ≤ 28·δ·V.
  have h_cubic_le : (20 * u^3 - 12 * u^2 * v + 28 * v^3)
                      ≤ 28 * δ * (u^2 + v^2) := by
    have h28V_nn : 0 ≤ 28 * (u^2 + v^2) := by positivity
    have h_step : 28 * (u^2 + v^2) * Real.sqrt (u^2 + v^2)
                    ≤ 28 * (u^2 + v^2) * δ :=
      mul_le_mul_of_nonneg_left h_sqrt_V_le h28V_nn
    have h_self : (20 * u^3 - 12 * u^2 * v + 28 * v^3)
                    ≤ |20 * u^3 - 12 * u^2 * v + 28 * v^3| := le_abs_self _
    linarith
  -- Combine with quadratic bound.
  have hsum : lyapunovDeriv x
      ≤ -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) + 28 * δ * (u^2 + v^2) := by
    linarith
  have heq : -(13 - 4 * Real.sqrt 5) * (u^2 + v^2) + 28 * δ * (u^2 + v^2)
        = -((13 - 4 * Real.sqrt 5) - 28 * δ) * (u^2 + v^2) := by ring
  have : lyapunovDeriv x
      ≤ -((13 - 4 * Real.sqrt 5) - 28 * δ) * (u^2 + v^2) := by linarith
  rw [hV_eq]; exact this

/-- **Sharp parametric forward invariance.** If `V(x 0) ≤ δ²` with
`28·δ < 13 − 4√5`, then `V(x t) ≤ V(x 0) ≤ δ²` for all `t ∈ [0, T]`.

This is the sharp analogue of `cf24_lyapunov_forward_invariant_param` —
no L¹-ball detour: V-sublevel is automatically forward-invariant
because `V̇ ≤ -α·V ≤ 0` whenever `V ≤ δ²`. -/
theorem cf24_lyapunov_forward_invariant_sharp
    {x : ℝ → Fin 3 → ℝ} {T : ℝ} (_hT : 0 ≤ T)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_lt : 28 * δ < 13 - 4 * Real.sqrt 5)
    (hV0_pos : 0 < lyapunov (x 0))
    (hV0_small : lyapunov (x 0) ≤ δ^2)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Icc 0 T))
    (hx_deriv_b : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ico (0 : ℝ) T, x t 0 + x t 1 + x t 2 = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, lyapunov (x t) ≤ lyapunov (x 0) := by
  refine image_le_of_deriv_right_lt_deriv_boundary
    (f := fun t => lyapunov (x t))
    (f' := fun t => lyapunovDeriv (x t))
    (B := fun _ => lyapunov (x 0))
    (B' := fun _ => 0)
    hV_cont
    (fun t ht => lyapunov_hasDerivWithinAt (hx_deriv_b t ht) (hx_deriv_c t ht))
    (le_refl _) (fun _ => hasDerivAt_const _ _) ?_
  intro t ht hV_eq
  simp only at hV_eq
  -- V(x t) = V(x 0) ≤ δ², so we get the sharp bound on V̇(x t).
  have hV_le_t : lyapunov (x t) ≤ δ^2 := by rw [hV_eq]; exact hV0_small
  have hbound :=
    lyapunovDeriv_le_sublevel_sharp δ hδ_nn (x t)
      (hx_simplex t ht) hV_le_t
  have hV_pos_t : 0 < lyapunov (x t) := hV_eq ▸ hV0_pos
  have hα_pos : 0 < (13 - 4 * Real.sqrt 5) - 28 * δ := by linarith
  have : -((13 - 4 * Real.sqrt 5) - 28 * δ) * lyapunov (x t) < 0 := by
    have := mul_pos hα_pos hV_pos_t; linarith
  linarith

/-- **Sharp parametric local exponential decay.**

Under the same hypotheses as the sharp forward invariance, plus
`28·δ < 13 − 4√5`, the Lyapunov function decays exponentially at the
sharper rate `(13 − 4√5) − 28·δ`. -/
theorem cf24_local_exponential_decay_sharp
    {x : ℝ → Fin 3 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_lt : 28 * δ < 13 - 4 * Real.sqrt 5)
    (hV0_pos : 0 < lyapunov (x 0))
    (hV0_small : lyapunov (x 0) ≤ δ^2)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Icc 0 T))
    (hx_deriv_b : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ico (0 : ℝ) T, x t 0 + x t 1 + x t 2 = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      lyapunov (x t) ≤ lyapunov (x 0)
        * Real.exp (-((13 - 4 * Real.sqrt 5) - 28 * δ) * t) := by
  have hα_pos : 0 < (13 - 4 * Real.sqrt 5) - 28 * δ := by linarith
  have hinv := cf24_lyapunov_forward_invariant_sharp hT δ hδ_nn hδ_lt
    hV0_pos hV0_small hV_cont hx_deriv_b hx_deriv_c hx_simplex
  have hsublevel : ∀ t ∈ Set.Ico (0 : ℝ) T, lyapunov (x t) ≤ δ^2 := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1, ht.2.le⟩
    exact (hinv t ht_icc).trans hV0_small
  exact Ripple.scalar_exponential_decay
    (V := fun t => lyapunov (x t))
    (V' := fun t => lyapunovDeriv (x t))
    (α := (13 - 4 * Real.sqrt 5) - 28 * δ) (T := T)
    hα_pos hT hV_cont
    (fun t ht => lyapunov_hasDerivWithinAt (hx_deriv_b t ht) (hx_deriv_c t ht))
    (fun t ht => lyapunovDeriv_le_sublevel_sharp δ hδ_nn (x t)
                   (hx_simplex t ht) (hsublevel t ht))

/-! ### Step 5 (final): readout convergence from exponential decay

Given `V(x t) → 0`, the coordinates `x t 1, x t 2` converge to the
fixed-point coordinates, hence the readout `z_11 + z_01/2` converges to
`z_11* + z_01*/2 = (3 - √5)/6`.

We package this as two statements:
1. `cf24_readout_tendsto_of_lyapunov_zero`: atomic bridge — from
   `V(x t) → 0` to the readout limit.
2. `lyapunov_tendsto_zero_of_exp_bound`: if there is a pointwise
   exponential-decay envelope `V(x t) ≤ C · exp(-α·t)` for all `t ≥ 0`
   with `α > 0`, then `V(x t) → 0` as `t → ∞`.

Chaining the two closes Step 5 modulo the global-existence hypothesis
(Layer 2), which feeds the decay envelope into statement 2. -/

/-- `|a| ≤ √(a² + b²)`: ℓ∞ ≤ ℓ² in 2D. -/
lemma abs_le_sqrt_sq_add_sq_left (a b : ℝ) : |a| ≤ Real.sqrt (a^2 + b^2) :=
  Real.abs_le_sqrt (by linarith [sq_nonneg b])

/-- `|b| ≤ √(a² + b²)`: ℓ∞ ≤ ℓ² in 2D. -/
lemma abs_le_sqrt_sq_add_sq_right (a b : ℝ) : |b| ≤ Real.sqrt (a^2 + b^2) :=
  Real.abs_le_sqrt (by linarith [sq_nonneg a])

/-- Pointwise bound `|Δb| ≤ √V(x)`. -/
lemma abs_sub_b_le_sqrt_lyapunov (x : Fin 3 → ℝ) :
    |x 1 - fixedPoint 1| ≤ Real.sqrt (lyapunov x) :=
  abs_le_sqrt_sq_add_sq_left (x 1 - fixedPoint 1) (x 2 - fixedPoint 2)

/-- Pointwise bound `|Δc| ≤ √V(x)`. -/
lemma abs_sub_c_le_sqrt_lyapunov (x : Fin 3 → ℝ) :
    |x 2 - fixedPoint 2| ≤ Real.sqrt (lyapunov x) :=
  abs_le_sqrt_sq_add_sq_right (x 1 - fixedPoint 1) (x 2 - fixedPoint 2)

/-- **Readout convergence from Lyapunov decay.**

If `V(x t) → 0` as `t → ∞`, then the readout `z_11(t) + z_01(t)/2`
converges to `(3 - √5)/6`. Proof: `√V` is continuous at `0`, so
`√V(x t) → 0`; each coordinate error is squeezed between `0` and `√V`,
so `x t 1 → b*, x t 2 → c*`; the readout is a linear combination. -/
theorem cf24_readout_tendsto_of_lyapunov_zero
    {x : ℝ → Fin 3 → ℝ}
    (hV : Filter.Tendsto (fun t => lyapunov (x t)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => x t 2 + x t 1 / 2) Filter.atTop (nhds readoutLimit) := by
  -- Step 1: √V(x t) → 0.
  have hsqrt : Filter.Tendsto (fun t => Real.sqrt (lyapunov (x t)))
      Filter.atTop (nhds 0) := by
    have hcont : Filter.Tendsto Real.sqrt (nhds 0) (nhds 0) := by
      simpa using (Real.continuous_sqrt.tendsto (0 : ℝ))
    simpa using hcont.comp hV
  -- Step 2: |x t 1 - b*| → 0 and |x t 2 - c*| → 0.
  have h_abs_b : Filter.Tendsto (fun t => |x t 1 - fixedPoint 1|)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun t => abs_sub_b_le_sqrt_lyapunov (x t)) hsqrt
  have h_abs_c : Filter.Tendsto (fun t => |x t 2 - fixedPoint 2|)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun t => abs_sub_c_le_sqrt_lyapunov (x t)) hsqrt
  -- Step 3: x t 1 → b*, x t 2 → c* via sandwich `-|f| ≤ f ≤ |f|`.
  have h_sub_b : Filter.Tendsto (fun t => x t 1 - fixedPoint 1) Filter.atTop (nhds 0) := by
    have hneg : Filter.Tendsto (fun t => -|x t 1 - fixedPoint 1|) Filter.atTop (nhds 0) := by
      simpa using h_abs_b.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg h_abs_b
      (fun _ => neg_abs_le _) (fun _ => le_abs_self _)
  have h_sub_c : Filter.Tendsto (fun t => x t 2 - fixedPoint 2) Filter.atTop (nhds 0) := by
    have hneg : Filter.Tendsto (fun t => -|x t 2 - fixedPoint 2|) Filter.atTop (nhds 0) := by
      simpa using h_abs_c.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg h_abs_c
      (fun _ => neg_abs_le _) (fun _ => le_abs_self _)
  have h_b : Filter.Tendsto (fun t => x t 1) Filter.atTop (nhds (fixedPoint 1)) := by
    have := h_sub_b.add_const (fixedPoint 1)
    simpa using this
  have h_c : Filter.Tendsto (fun t => x t 2) Filter.atTop (nhds (fixedPoint 2)) := by
    have := h_sub_c.add_const (fixedPoint 2)
    simpa using this
  -- Step 4: readout → fp 2 + fp 1 / 2 = readoutLimit.
  have h_sum : Filter.Tendsto (fun t => x t 2 + x t 1 / 2)
      Filter.atTop (nhds (fixedPoint 2 + fixedPoint 1 / 2)) := by
    exact h_c.add (h_b.div_const 2)
  rw [show readoutLimit = fixedPoint 2 + fixedPoint 1 / 2 from readout_fixedPoint.symm]
  exact h_sum

/-- **Lyapunov decay envelope implies `V(x t) → 0`.**

If `0 ≤ V(x t) ≤ C · exp(-α·t)` for all `t ≥ 0` with `0 < α`, then
`V(x t) → 0` as `t → ∞`. -/
theorem lyapunov_tendsto_zero_of_exp_bound
    {x : ℝ → Fin 3 → ℝ} {α C : ℝ} (hα : 0 < α)
    (h_bound : ∀ t : ℝ, 0 ≤ t →
      lyapunov (x t) ≤ C * Real.exp (-α * t)) :
    Filter.Tendsto (fun t => lyapunov (x t)) Filter.atTop (nhds 0) := by
  -- RHS tends to 0: C · exp(-α·t) → C · 0 = 0.
  have h_exp_tendsto : Filter.Tendsto (fun t => Real.exp (-α * t))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -α * t) Filter.atTop Filter.atBot :=
      (Filter.tendsto_const_mul_atBot_of_neg (by linarith : -α < 0)).mpr Filter.tendsto_id
    exact Real.tendsto_exp_atBot.comp h1
  have h_rhs : Filter.Tendsto (fun t => C * Real.exp (-α * t))
      Filter.atTop (nhds 0) := by
    have := h_exp_tendsto.const_mul C
    simpa using this
  -- Squeeze: 0 ≤ V(x t) ≤ C · exp(-α·t) eventually.
  refine squeeze_zero' ?_ ?_ h_rhs
  · exact Filter.Eventually.of_forall (fun t => lyapunov_nonneg (x t))
  · refine Filter.eventually_atTop.mpr ⟨0, ?_⟩
    intro t ht
    exact h_bound t ht

/-! ### Layer 2 building blocks: boundary behavior on the positive simplex

Standard invariance arguments for the positive simplex
`Σ := {x : Fin 3 → ℝ | x 0, x 1, x 2 ≥ 0 ∧ x 0 + x 1 + x 2 = 1}` rest on
two algebraic facts:

1. `field_conservative` (already proved): `Σᵢ fᵢ(x) = 0`, so the tangent
   hyperplane `Σᵢ xᵢ = 1` is forward-invariant.
2. **Sub-tangent (Nagumo) condition on the coordinate hyperplanes**: at
   any point of the closed simplex where some `xᵢ = 0`, the component
   `fᵢ(x) ≥ 0` — so the field points into the positive orthant.

We record the three sub-tangent inequalities explicitly. Combined with
`field_conservative`, these imply that trajectories starting in `Σ`
stay in `Σ` (Nagumo's invariance theorem, standard in ODE theory — the
formal ODE-theoretic consequence is deferred to a separate file that
wires Picard–Lindelöf). -/

/-- Sub-tangent at `z_00 = 0`: the `z_00` component of `field` vanishes. -/
theorem field_nonneg_at_z00_zero (x : Fin 3 → ℝ) (hx0 : x 0 = 0) :
    0 ≤ field x 0 := by
  simp [field, hx0]

/-- Sub-tangent at `z_01 = 0`: under non-negativity of the other two
coordinates, `ż_01 ≥ 0`. -/
theorem field_nonneg_at_z01_zero (x : Fin 3 → ℝ)
    (hx0 : 0 ≤ x 0) (hx2 : 0 ≤ x 2) (hx1 : x 1 = 0) :
    0 ≤ field x 1 := by
  simp only [field, hx1, mul_zero, sub_zero, zero_mul]
  -- field x 1 = 2 · x 0 · x 0 + 16 · x 0 · x 2
  have h1 : (0:ℝ) ≤ 2 * x 0 * x 0 := by positivity
  have h2 : (0:ℝ) ≤ 16 * x 0 * x 2 := by positivity
  linarith [h1, h2]

/-- Sub-tangent at `z_11 = 0`: under non-negativity of the other two
coordinates, `ż_11 ≥ 0`. -/
theorem field_nonneg_at_z11_zero (x : Fin 3 → ℝ)
    (hx0 : 0 ≤ x 0) (hx1 : 0 ≤ x 1) (hx2 : x 2 = 0) :
    0 ≤ field x 2 := by
  simp only [field, hx2, mul_zero]
  -- field x 2 = x 0 · x 1
  linarith [mul_nonneg hx0 hx1]

/-- Compact bundle of the sub-tangent conditions on the simplex. -/
theorem field_subtangent (x : Fin 3 → ℝ)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : 0 ≤ x 2) :
    (x 0 = 0 → 0 ≤ field x 0) ∧
    (x 1 = 0 → 0 ≤ field x 1) ∧
    (x 2 = 0 → 0 ≤ field x 2) :=
  ⟨fun hx => field_nonneg_at_z00_zero x hx,
   fun hx => field_nonneg_at_z01_zero x h0 h2 hx,
   fun hx => field_nonneg_at_z11_zero x h0 h1 hx⟩

/-! ### End-to-end Step 5 bridge

This is the composition of the local-stability chain with the Step-5
readout-convergence chain.  It takes the *global* ODE hypotheses on
`[0, ∞)` together with a small-energy initial condition
(`0 < V(x 0) < 1/512`) and concludes readout convergence.  No ball
hypothesis, no finite-time restriction — the only missing input for a
"pure simplex-interior initial condition" result is the Layer-2 basin
argument that drives an arbitrary simplex-interior start into the
`1/512` sublevel set in finite time (then a time shift reduces to this
theorem). -/
theorem cf24_readout_tendsto_from_small_lyapunov_init
    {x : ℝ → Fin 3 → ℝ}
    (hV0_pos : 0 < lyapunov (x 0))
    (hV0_small : lyapunov (x 0) < 1 / 512)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Ici 0))
    (hx_deriv_b : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ici (0 : ℝ), x t 0 + x t 1 + x t 2 = 1) :
    Filter.Tendsto (fun t => x t 2 + x t 1 / 2) Filter.atTop (nhds readoutLimit) := by
  -- Pointwise exponential envelope V(x t) ≤ V(x 0) · exp(-α·t).
  have h_envelope : ∀ t : ℝ, 0 ≤ t →
      lyapunov (x t)
        ≤ lyapunov (x 0) * Real.exp (-(11 - 4 * Real.sqrt 5) * t) := by
    intro t ht
    set T : ℝ := t + 1 with hT_def
    have hT_nn : (0 : ℝ) ≤ T := by rw [hT_def]; linarith
    have hIcc_sub : Set.Icc (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := fun s hs => hs.1
    have hIco_sub : Set.Ico (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := fun s hs => hs.1
    have hVcontT : ContinuousOn (fun s => lyapunov (x s)) (Set.Icc 0 T) :=
      hV_cont.mono hIcc_sub
    have hdb : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun r => x r 1) (field (x s) 1) (Set.Ici s) s :=
      fun s hs => hx_deriv_b s (hIco_sub hs)
    have hdc : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun r => x r 2) (field (x s) 2) (Set.Ici s) s :=
      fun s hs => hx_deriv_c s (hIco_sub hs)
    have hsim : ∀ s ∈ Set.Ico (0 : ℝ) T, x s 0 + x s 1 + x s 2 = 1 :=
      fun s hs => hx_simplex s (hIco_sub hs)
    have hres := cf24_local_exponential_decay hT_nn hV0_pos
      hV0_small hVcontT hdb hdc hsim
    exact hres t ⟨ht, by rw [hT_def]; linarith⟩
  -- V(x t) → 0.
  have hV_zero : Filter.Tendsto (fun t => lyapunov (x t)) Filter.atTop (nhds 0) :=
    lyapunov_tendsto_zero_of_exp_bound lyapunov_residual_gap_pos h_envelope
  -- Readout → readoutLimit.
  exact cf24_readout_tendsto_of_lyapunov_zero hV_zero

/-- **Sharp end-to-end Step 5 bridge.**

The sharp counterpart of `cf24_readout_tendsto_from_small_lyapunov_init`:
takes the SHARP threshold `V(x 0) < (13 − 4√5)² / 784 ≈ 1/47.7` (a 10.7×
extension over `1/512`) and concludes readout convergence.  Setting
`δ = √V(x 0)`, the sharp parametric chain
`cf24_local_exponential_decay_sharp` gives an exponential
envelope at the rate `(13 − 4√5) − 28·δ > 0`. -/
theorem cf24_readout_tendsto_from_sharp_lyapunov_init
    {x : ℝ → Fin 3 → ℝ}
    (hV0_pos : 0 < lyapunov (x 0))
    (hV0_sharp : lyapunov (x 0) < (13 - 4 * Real.sqrt 5)^2 / 784)
    (hV_cont : ContinuousOn (fun t => lyapunov (x t)) (Set.Ici 0))
    (hx_deriv_b : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => x s 1) (field (x t) 1) (Set.Ici t) t)
    (hx_deriv_c : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => x s 2) (field (x t) 2) (Set.Ici t) t)
    (hx_simplex : ∀ t ∈ Set.Ici (0 : ℝ), x t 0 + x t 1 + x t 2 = 1) :
    Filter.Tendsto (fun t => x t 2 + x t 1 / 2) Filter.atTop (nhds readoutLimit) := by
  -- Set δ = √V(x 0); then δ² = V(x 0) and 28δ < 13 − 4√5.
  set δ := Real.sqrt (lyapunov (x 0)) with hδ_def
  have hV0_nn : 0 ≤ lyapunov (x 0) := hV0_pos.le
  have hδ_nn : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ^2 = lyapunov (x 0) := by
    rw [hδ_def, sq, ← Real.sqrt_mul hV0_nn, Real.sqrt_mul_self hV0_nn]
  have hV_le : lyapunov (x 0) ≤ δ^2 := by rw [hδsq]
  have h_sqrt5_lt : Real.sqrt 5 < 13 / 4 := by
    have h1 : Real.sqrt 5 < Real.sqrt ((13 / 4)^2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    have h2 : Real.sqrt ((13 / 4)^2) = 13 / 4 :=
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 13/4)
    linarith [h1, h2.le, h2.ge]
  have h_pos : 0 < 13 - 4 * Real.sqrt 5 := by linarith
  have hδ_lt : 28 * δ < 13 - 4 * Real.sqrt 5 := by
    have h28δ_nn : 0 ≤ 28 * δ := by positivity
    have h_sq_lt : (28 * δ)^2 < (13 - 4 * Real.sqrt 5)^2 := by
      have h1 : (28 * δ)^2 = 784 * δ^2 := by ring
      rw [h1, hδsq]
      linarith [hV0_sharp]
    have h_sqrt_lt : Real.sqrt ((28 * δ)^2) < Real.sqrt ((13 - 4 * Real.sqrt 5)^2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_lt
    have hL : Real.sqrt ((28 * δ)^2) = 28 * δ := Real.sqrt_sq h28δ_nn
    have hR : Real.sqrt ((13 - 4 * Real.sqrt 5)^2) = 13 - 4 * Real.sqrt 5 :=
      Real.sqrt_sq h_pos.le
    linarith [h_sqrt_lt, hL.le, hL.ge, hR.le, hR.ge]
  set α : ℝ := (13 - 4 * Real.sqrt 5) - 28 * δ with hα_def
  have hα_pos : 0 < α := by show 0 < (13 - 4 * Real.sqrt 5) - 28 * δ; linarith
  have h_envelope : ∀ t : ℝ, 0 ≤ t →
      lyapunov (x t)
        ≤ lyapunov (x 0) * Real.exp (-α * t) := by
    intro t ht
    set T : ℝ := t + 1 with hT_def
    have hT_nn : (0 : ℝ) ≤ T := by rw [hT_def]; linarith
    have hIcc_sub : Set.Icc (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := fun s hs => hs.1
    have hIco_sub : Set.Ico (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := fun s hs => hs.1
    have hVcontT : ContinuousOn (fun s => lyapunov (x s)) (Set.Icc 0 T) :=
      hV_cont.mono hIcc_sub
    have hdb : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun r => x r 1) (field (x s) 1) (Set.Ici s) s :=
      fun s hs => hx_deriv_b s (hIco_sub hs)
    have hdc : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun r => x r 2) (field (x s) 2) (Set.Ici s) s :=
      fun s hs => hx_deriv_c s (hIco_sub hs)
    have hsim : ∀ s ∈ Set.Ico (0 : ℝ) T, x s 0 + x s 1 + x s 2 = 1 :=
      fun s hs => hx_simplex s (hIco_sub hs)
    have hres := cf24_local_exponential_decay_sharp hT_nn δ hδ_nn hδ_lt
      hV0_pos hV_le hVcontT hdb hdc hsim
    exact hres t ⟨ht, by rw [hT_def]; linarith⟩
  have hV_zero : Filter.Tendsto (fun t => lyapunov (x t)) Filter.atTop (nhds 0) :=
    lyapunov_tendsto_zero_of_exp_bound hα_pos h_envelope
  exact cf24_readout_tendsto_of_lyapunov_zero hV_zero

/-! ### Layer 2 wiring: CRN-implementability of the CF'24 field

We decompose each component of `field` as `prod − degr · xᵢ` with
`prod, degr` positive polynomials.  Writing out the decomposition:

- `f_0 = 7 x₀ x₁ − (2 x₀ + 2 x₂) · x₀`
- `f_1 = (2 x₀² + 16 x₀ x₂) − (8 x₀ + x₂) · x₁`
- `f_2 = (x₀ x₁ + x₁ x₂) − 14 x₀ · x₂`

This gives `IsCRNImplementable 3 field`, which — combined with
`field_conservative` and the local-Lipschitz bound for polynomial fields
— lets us invoke `crn_simplex_global_ode_solution'` to get a global
solution of the CF'24 field from any non-negative simplex initial
condition.  The basin argument on the resulting solution is the
remaining Layer-2 step. -/

/-- Production term for component 0: `7 x₀ x₁`. -/
noncomputable def cf24Prod : Fin 3 → ((Fin 3 → ℝ) → ℝ)
  | ⟨0, _⟩ => fun x => 7 * x 0 * x 1
  | ⟨1, _⟩ => fun x => 2 * x 0 * x 0 + 16 * x 0 * x 2
  | ⟨2, _⟩ => fun x => x 0 * x 1 + x 1 * x 2

/-- Degradation rate for component 0: `2 x₀ + 2 x₂`, etc. -/
noncomputable def cf24Degr : Fin 3 → ((Fin 3 → ℝ) → ℝ)
  | ⟨0, _⟩ => fun x => 2 * x 0 + 2 * x 2
  | ⟨1, _⟩ => fun x => 8 * x 0 + x 2
  | ⟨2, _⟩ => fun x => 14 * x 0

/-- The production terms are positive polynomials on the non-negative orthant. -/
theorem cf24Prod_pos : ∀ i, IsPositivePoly (cf24Prod i) := by
  intro i x hx
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2
  fin_cases i <;>
    simp only [cf24Prod, show (⟨0, _⟩ : Fin 3) = 0 from rfl,
               show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl,
               show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl] <;>
    positivity

/-- The degradation rates are positive polynomials on the non-negative orthant. -/
theorem cf24Degr_pos : ∀ i, IsPositivePoly (cf24Degr i) := by
  intro i x hx
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2
  fin_cases i <;> simp only [cf24Degr] <;> positivity

/-- Pointwise CRN decomposition: `field x i = cf24Prod i x − cf24Degr i x · x i`. -/
theorem cf24_field_eq (x : Fin 3 → ℝ) (i : Fin 3) :
    field x i = cf24Prod i x - cf24Degr i x * x i := by
  fin_cases i <;>
    simp only [field, cf24Prod, cf24Degr, Fin.isValue, show (⟨0, by norm_num⟩ : Fin 3) = 0 from rfl,
               show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl,
               show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl] <;>
    ring

/-- **CRN-implementability of the CF'24 field.**

Combined with `field_conservative` and the polynomial-local-Lipschitz
lemma, this unlocks `crn_simplex_global_ode_solution'` for `field`. -/
noncomputable def cf24_isCRNImplementable : IsCRNImplementable 3 field where
  prod := cf24Prod
  degr := cf24Degr
  prod_pos := cf24Prod_pos
  degr_pos := cf24Degr_pos
  field_eq := cf24_field_eq

/-! ## PolyPIVP wrapper + local Lipschitz for `field`

We package the CF'24 field as a syntactic `PolyPIVP 3` so that the narrow
technical lemma `polyPIVP_field_locally_lipschitz` applies.  The init in
the wrapper is a placeholder (not used for the Lipschitz conclusion). -/

open MvPolynomial in
/-- Syntactic `PolyPIVP 3` whose evaluated field is `field`.  Init is a
placeholder; only the polynomial field is used to extract local Lipschitz
data. -/
noncomputable def cf24PolyPIVP : PolyPIVP 3 where
  field := fun i =>
    match i with
    | ⟨0, _⟩ =>
        -(C 2) * X 0 * X 0 + C 7 * X 0 * X 1 - C 2 * X 0 * X 2
    | ⟨1, _⟩ =>
        C 2 * X 0 * X 0 - C 8 * X 0 * X 1 + C 16 * X 0 * X 2 - X 1 * X 2
    | ⟨2, _⟩ =>
        X 0 * X 1 - C 14 * X 0 * X 2 + X 1 * X 2
    | ⟨n+3, hn⟩ => absurd hn (by omega)
  init := fun _ => 0
  output := 2

/-- The semantic field of `cf24PolyPIVP` equals `field` pointwise. -/
theorem cf24PolyPIVP_evalField_eq (x : Fin 3 → ℝ) (i : Fin 3) :
    cf24PolyPIVP.toPIVP.field x i = field x i := by
  change cf24PolyPIVP.evalField x i = field x i
  unfold PolyPIVP.evalField
  fin_cases i <;>
    simp [cf24PolyPIVP, field, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_C]

/-- CF'24 field is locally Lipschitz (polynomial ⇒ smooth ⇒ locally Lipschitz
on balls). -/
theorem field_locally_lipschitz :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 3 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖field x - field y‖ ≤ L * ‖x - y‖ := by
  intro R hR
  obtain ⟨L, hL⟩ := polyPIVP_field_locally_lipschitz cf24PolyPIVP R hR
  refine ⟨L, ?_⟩
  intro x y hx hy
  have hx_eq : cf24PolyPIVP.toPIVP.field x = field x := by
    funext i; exact cf24PolyPIVP_evalField_eq x i
  have hy_eq : cf24PolyPIVP.toPIVP.field y = field y := by
    funext i; exact cf24PolyPIVP_evalField_eq y i
  have := hL x y hx hy
  rw [hx_eq, hy_eq] at this
  exact this

/-! ## Global ODE solution from any simplex initial condition

Given a non-negative vector in the simplex, `crn_simplex_global_ode_solution'`
produces a global PIVP solution.  We expose this as the Solution for a
semantic `PIVP 3` built from `field`. -/

/-- The semantic `PIVP 3` for the CF'24 field at an arbitrary initial point. -/
noncomputable def cf24PIVP (x0 : Fin 3 → ℝ) : PIVP 3 where
  field := field
  init := x0
  output := 2

/-- Global ODE solution on `[0, ∞)` for any non-negative simplex initial
condition. -/
noncomputable def cf24_global_solution (x0 : Fin 3 → ℝ)
    (h_init_nn : ∀ i, 0 ≤ x0 i) (h_init_simplex : ∑ i, x0 i = 1) :
    PIVP.Solution (cf24PIVP x0) :=
  crn_simplex_global_ode_solution' (cf24PIVP x0)
    cf24_isCRNImplementable field_conservative
    field_locally_lipschitz h_init_nn h_init_simplex

/-! ## Step 5 top-level statement

The concrete end-to-end claim: for every non-negative simplex initial
condition `x0`, the readout `z_11 + z_01/2` along the global CRN trajectory
converges to `(3 − √5)/6`. -/

/-- **Basin-of-attraction entry hypothesis.**  Along the global trajectory
starting from any simplex-interior initial condition, the Lyapunov function
`V = (b − b*)² + (c − c*)²` drops strictly below `1/512` at some finite
time `t₀ ≥ 0`.

Exposed as an explicit `Prop` rather than a `sorry` (cf. the analogous
`AperyConifoldThreeHalvesBound` pattern in `Ripple.Number.AperyBounded`).

Status.  The paper of Chen–Huang (v5, Prop 11.4–11.5) establishes global
convergence by combining local asymptotic stability at the fixed point
with a numerical verification of the basin.  A fully formal proof is not
given in the paper either; the v5 PDF §12 (Figure 2) explicitly marks this
step as "numerically verified".

What would be required to discharge it formally:
* The symmetric-quadratic decomposition
    `V̇(x) = Q(Δb, Δc) + 20·Δb³ − 12·Δb²·Δc + 28·Δc³`
  (already proved: `lyapunovDeriv_on_simplex`), with `Q` negative-definite
  (already proved: `lyapunovQuad_le_neg_sq`), gives `V̇ ≤ 0` only in the
  small ball where the cubic remainder is dominated.  **Globally on the
  open simplex, `V` is not monotone** (numeric: V̇ can be briefly positive
  far from the fixed point).
* A full proof therefore needs either (a) a different Lyapunov function
  globally valid on the open simplex (a plausible candidate is KL-divergence
  `H(x‖x*) = Σᵢ xᵢ log(xᵢ/xᵢ*)` for mass-action systems), or (b) a 2-D
  Bendixson–Poincaré/LaSalle argument ruling out non-fixed-point ω-limits.

This is the one genuine dynamical-systems mountain remaining; everything
downstream of `cf24_step5_readout_conditional` is fully proved. -/
def Cf24BasinEntry : Prop :=
  ∀ (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1),
    0 < x0 0 → 0 < x0 1 → 0 < x0 2 →
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      0 < lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀) ∧
      lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀) < 1 / 512

/-- **`Cf24BasinEntry` is false.**

The claimed property `Cf24BasinEntry` (Lyapunov drops below `1/512` in finite
time from every interior simplex point) is *not true* in the form stated in
the paper sketch.  The interior **saddle point** `saddlePoint` is itself a
counterexample: ODE uniqueness forces the trajectory starting at `saddlePoint`
to stay at `saddlePoint` for all `t ≥ 0`, so the Lyapunov value is constantly
`5/9`, which is greater than `1/512`.

This formalizes the warning in the docstring above: a fully formal proof of
basin entry needs a different Lyapunov function or a Bendixson–Poincaré
argument that **explicitly rules out the saddle's stable manifold** as an
initial condition.  The paper's "interior" hypothesis is too weak. -/
theorem cf24_basinEntry_false : ¬ Cf24BasinEntry := by
  intro h
  -- The saddle is a non-negative simplex-interior point.
  have h_nn : ∀ i, 0 ≤ saddlePoint i := fun i => (saddlePoint_pos i).le
  have h_simplex : ∑ i, saddlePoint i = 1 := by
    rw [Fin.sum_univ_three]; exact saddlePoint_on_simplex
  -- Apply the hypothesis at `saddlePoint` to obtain `t₀` with `V(traj t₀) < 1/512`.
  obtain ⟨t₀, ht₀_nn, _, hV_lt⟩ :=
    h saddlePoint h_nn h_simplex
      (saddlePoint_pos 0) (saddlePoint_pos 1) (saddlePoint_pos 2)
  set sol := cf24_global_solution saddlePoint h_nn h_simplex with hsol_def
  -- Step 1: HasDerivAt for the trajectory at every t ≥ 0.
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP saddlePoint).field x = field x :=
    fun _ => rfl
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht
    have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hy_cont : ContinuousOn (fun s => sol.trajectory s) (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact (hy_deriv t ht).continuousAt.continuousWithinAt
  -- Step 2: Show `sol.trajectory t = saddlePoint` for every `t ∈ [0, t₀+1]`.
  -- Use ODE uniqueness (`ODE_solution_unique_of_mem_Icc_right`) on the closed
  -- interval `[0, T]` with `T := t₀ + 1`, comparing `sol.trajectory` against
  -- the constant function `saddlePoint`.
  set T : ℝ := t₀ + 1 with hT_def
  have hT_pos : 0 < T := by linarith
  have h0T : (0 : ℝ) ≤ T := hT_pos.le
  -- Bound `‖sol.trajectory t‖` on the compact `[0, T]` via continuity.
  have hy_contIcc : ContinuousOn (fun s => sol.trajectory s) (Set.Icc 0 T) :=
    hy_cont.mono (fun s hs => hs.1)
  have h_compact : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
  obtain ⟨M, hM_bound⟩ : ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖sol.trajectory t‖ ≤ M := by
    have h_cont_norm : ContinuousOn (fun t => ‖sol.trajectory t‖) (Set.Icc 0 T) :=
      hy_contIcc.norm
    obtain ⟨M, hM⟩ := h_compact.bddAbove_image h_cont_norm
    exact ⟨M, fun t ht => hM ⟨t, ht, rfl⟩⟩
  have hM_nn : 0 ≤ M := by
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl _, h0T⟩
    exact le_trans (norm_nonneg _) (hM_bound 0 h0mem)
  -- Pick `R` larger than both `M` and `‖saddlePoint‖`.
  set R : ℝ := M + ‖saddlePoint‖ + 1 with hR_def
  have hR_pos : 0 < R := by
    have h1 : 0 ≤ ‖saddlePoint‖ := norm_nonneg _
    linarith
  -- Both `sol.trajectory t` (for t ∈ [0,T]) and `saddlePoint` lie in closed ball R.
  have h_traj_in_ball : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖sol.trajectory t‖ ≤ R := by
    intro t ht
    have h1 : 0 ≤ ‖saddlePoint‖ := norm_nonneg _
    have := hM_bound t ht
    linarith
  have h_saddle_in_ball : ‖saddlePoint‖ ≤ R := by
    have hM' : 0 ≤ M := hM_nn
    linarith
  -- Lipschitz constant for `field` on the ball.
  obtain ⟨L, hL⟩ := field_locally_lipschitz R hR_pos
  -- Take K := max L 0 as NNReal.
  have hL_or : 0 ≤ max L 0 := le_max_right _ _
  set K : NNReal := ⟨max L 0, hL_or⟩ with hK_def
  -- `field` is Lipschitz with constant K on the closed ball of radius R.
  have h_field_lip : LipschitzOnWith K field {x : Fin 3 → ℝ | ‖x‖ ≤ R} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : ‖x‖ ≤ R := hx
    have hy' : ‖y‖ ≤ R := hy
    have h_main : ‖field x - field y‖ ≤ L * ‖x - y‖ := hL x y hx' hy'
    have h_max : L ≤ max L 0 := le_max_left _ _
    have hxy_nn : 0 ≤ ‖x - y‖ := norm_nonneg _
    have : L * ‖x - y‖ ≤ max L 0 * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right h_max hxy_nn
    have hbridge : ‖field x - field y‖ ≤ max L 0 * ‖x - y‖ :=
      le_trans h_main this
    have hKR : (K : ℝ) = max L 0 := by rw [hK_def]; rfl
    rw [dist_eq_norm, dist_eq_norm, hKR]
    exact hbridge
  -- Now invoke ODE_solution_unique_of_mem_Icc_right.
  set v : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun _ y => field y with hv_def
  set s : ℝ → Set (Fin 3 → ℝ) := fun _ => {x : Fin 3 → ℝ | ‖x‖ ≤ R} with hs_def
  -- Lipschitz on every `s t` with constant K (independent of t).
  have hv_lip : ∀ t ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith K (v t) (s t) :=
    fun _ _ => h_field_lip
  -- Continuity of `sol.trajectory` and the constant `saddlePoint` on `[0,T]`.
  have h_const_cont : ContinuousOn (fun _ : ℝ => saddlePoint) (Set.Icc 0 T) :=
    continuousOn_const
  -- HasDerivWithinAt (Ici t) for `sol.trajectory` on `Ico 0 T`.
  have h_sol_hd : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => sol.trajectory s) (v t (sol.trajectory t)) (Set.Ici t) t := by
    intro t ht
    have := hy_deriv t ht.1
    exact this.hasDerivWithinAt
  -- HasDerivWithinAt for the constant `saddlePoint`.  Since `field saddlePoint = 0`,
  -- the derivative `0` matches `v t (saddlePoint) = field saddlePoint = 0`.
  have h_const_hd : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun _ : ℝ => saddlePoint) (v t saddlePoint) (Set.Ici t) t := by
    intro t _
    have h_field_zero : v t saddlePoint = 0 := by
      simp [hv_def, field_saddlePoint]
    rw [h_field_zero]
    exact (hasDerivWithinAt_const t _ _)
  -- Membership of trajectory in `s t`.
  have h_sol_in_s : ∀ t ∈ Set.Ico (0 : ℝ) T, sol.trajectory t ∈ s t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    exact h_traj_in_ball t ht'
  -- Membership of constant saddlePoint in `s t`.
  have h_const_in_s : ∀ t ∈ Set.Ico (0 : ℝ) T, saddlePoint ∈ s t :=
    fun _ _ => h_saddle_in_ball
  -- Initial value match: `sol.trajectory 0 = saddlePoint`.
  have h_init : sol.trajectory 0 = saddlePoint := by
    have := sol.init_cond
    simpa [cf24PIVP] using this
  -- Apply ODE uniqueness to get equality on `[0, T]`.
  have h_eqOn :=
    ODE_solution_unique_of_mem_Icc_right (v := v) (s := s) (K := K)
      hv_lip hy_contIcc h_sol_hd h_sol_in_s h_const_cont h_const_hd h_const_in_s h_init
  -- In particular at `t₀ ∈ [0, T]`.
  have ht₀_in : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨ht₀_nn, by linarith⟩
  have h_traj_at_t₀ : sol.trajectory t₀ = saddlePoint := h_eqOn ht₀_in
  -- Step 3: Conclude `lyapunov (sol.trajectory t₀) = 5/9`, contradicting `< 1/512`.
  rw [h_traj_at_t₀, lyapunov_saddlePoint] at hV_lt
  linarith

/-! ### Two concrete obstructions to `Cf24BasinEntry` as stated

Beyond the `saddlePoint` counterexample (`cf24_basinEntry_false`), there is a
second, even simpler obstruction at the **attractor itself**: starting at
`fixedPoint`, ODE uniqueness forces `traj t ≡ fixedPoint`, hence
`V(traj t) ≡ V(fixedPoint) = 0`, which fails the strict inequality
`0 < V(traj t₀)` required by `Cf24BasinEntry`.

Together, these two findings show `Cf24BasinEntry` is *unsalvageable* in
its stated form.  The natural correction is to assume the initial Lyapunov
value already satisfies `0 < V(x0) < 1/512`, in which case basin entry holds
trivially at `t₀ = 0`.  We formalize this as `Cf24BasinEntryFromSmallInit`
and prove it directly. -/

/-- The interior attractor's coordinates are strictly positive. -/
theorem fixedPoint_pos : ∀ i, 0 < fixedPoint i := by
  intro i
  have h5_lt : Real.sqrt 5 < 3 := by
    have hlt : Real.sqrt 5 < Real.sqrt 9 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have h9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.sqrt_sq] ; norm_num
    linarith
  have h5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  fin_cases i <;> simp only [fixedPoint]
  · -- (7 + 3√5)/18 > 0
    have h3sqrt5_pos : 0 < 3 * Real.sqrt 5 := by linarith
    linarith
  · norm_num
  · -- (7 - 3√5)/18 > 0 since 3√5 < 9 ≤ 7? Actually 3√5 ≈ 6.708 < 7.
    have h3sqrt5_lt : 3 * Real.sqrt 5 < 7 := by
      have h5_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
      nlinarith [Real.sqrt_nonneg (5 : ℝ), h5_sq]
    linarith

/-- **Second counterexample — at the attractor `fixedPoint`.**

Starting at `fixedPoint`, ODE uniqueness pins `traj t = fixedPoint` for all
`t ≥ 0`, so `lyapunov (traj t) = 0`.  In particular the strict positivity
clause `0 < V(traj t₀)` of `Cf24BasinEntry` can never hold from this initial
condition.  This is a second, fundamentally different obstruction from the
saddle counterexample: not "trapped above threshold" but "exactly *at*
threshold-0". -/
theorem cf24_basinEntry_fails_at_fixedPoint :
    ¬ ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      0 < lyapunov ((cf24_global_solution fixedPoint
        (fun i => (fixedPoint_pos i).le)
        (by rw [Fin.sum_univ_three]; exact fixedPoint_on_simplex)).trajectory t₀) ∧
      lyapunov ((cf24_global_solution fixedPoint
        (fun i => (fixedPoint_pos i).le)
        (by rw [Fin.sum_univ_three]; exact fixedPoint_on_simplex)).trajectory t₀)
        < 1 / 512 := by
  rintro ⟨t₀, ht₀_nn, hV_pos, _⟩
  -- Abbreviate the simplex hypotheses.
  set h_nn : ∀ i, 0 ≤ fixedPoint i := fun i => (fixedPoint_pos i).le with hnn_def
  set h_simplex : ∑ i, fixedPoint i = 1 := by
    rw [Fin.sum_univ_three]; exact fixedPoint_on_simplex
  set sol := cf24_global_solution fixedPoint h_nn h_simplex with hsol_def
  -- HasDerivAt for the trajectory.
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP fixedPoint).field x = field x :=
    fun _ => rfl
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht
    have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hy_cont : ContinuousOn (fun s => sol.trajectory s) (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact (hy_deriv t ht).continuousAt.continuousWithinAt
  -- Use ODE uniqueness on `[0, T]` with `T := t₀ + 1`.
  set T : ℝ := t₀ + 1 with hT_def
  have hT_pos : 0 < T := by linarith
  have h0T : (0 : ℝ) ≤ T := hT_pos.le
  have hy_contIcc : ContinuousOn (fun s => sol.trajectory s) (Set.Icc 0 T) :=
    hy_cont.mono (fun s hs => hs.1)
  have h_compact : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
  obtain ⟨M, hM_bound⟩ : ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖sol.trajectory t‖ ≤ M := by
    have h_cont_norm : ContinuousOn (fun t => ‖sol.trajectory t‖) (Set.Icc 0 T) :=
      hy_contIcc.norm
    obtain ⟨M, hM⟩ := h_compact.bddAbove_image h_cont_norm
    exact ⟨M, fun t ht => hM ⟨t, ht, rfl⟩⟩
  have hM_nn : 0 ≤ M := by
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl _, h0T⟩
    exact le_trans (norm_nonneg _) (hM_bound 0 h0mem)
  set R : ℝ := M + ‖fixedPoint‖ + 1 with hR_def
  have hR_pos : 0 < R := by
    have h1 : 0 ≤ ‖fixedPoint‖ := norm_nonneg _
    linarith
  have h_traj_in_ball : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖sol.trajectory t‖ ≤ R := by
    intro t ht
    have h1 : 0 ≤ ‖fixedPoint‖ := norm_nonneg _
    have := hM_bound t ht
    linarith
  have h_fp_in_ball : ‖fixedPoint‖ ≤ R := by
    have hM' : 0 ≤ M := hM_nn
    linarith
  obtain ⟨L, hL⟩ := field_locally_lipschitz R hR_pos
  have hL_or : 0 ≤ max L 0 := le_max_right _ _
  set K : NNReal := ⟨max L 0, hL_or⟩ with hK_def
  have h_field_lip : LipschitzOnWith K field {x : Fin 3 → ℝ | ‖x‖ ≤ R} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : ‖x‖ ≤ R := hx
    have hy' : ‖y‖ ≤ R := hy
    have h_main : ‖field x - field y‖ ≤ L * ‖x - y‖ := hL x y hx' hy'
    have h_max : L ≤ max L 0 := le_max_left _ _
    have hxy_nn : 0 ≤ ‖x - y‖ := norm_nonneg _
    have : L * ‖x - y‖ ≤ max L 0 * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right h_max hxy_nn
    have hbridge : ‖field x - field y‖ ≤ max L 0 * ‖x - y‖ :=
      le_trans h_main this
    have hKR : (K : ℝ) = max L 0 := by rw [hK_def]; rfl
    rw [dist_eq_norm, dist_eq_norm, hKR]
    exact hbridge
  set v : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun _ y => field y with hv_def
  set s : ℝ → Set (Fin 3 → ℝ) := fun _ => {x : Fin 3 → ℝ | ‖x‖ ≤ R} with hs_def
  have hv_lip : ∀ t ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith K (v t) (s t) :=
    fun _ _ => h_field_lip
  have h_const_cont : ContinuousOn (fun _ : ℝ => fixedPoint) (Set.Icc 0 T) :=
    continuousOn_const
  have h_sol_hd : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => sol.trajectory s) (v t (sol.trajectory t)) (Set.Ici t) t := by
    intro t ht
    have := hy_deriv t ht.1
    exact this.hasDerivWithinAt
  have h_const_hd : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun _ : ℝ => fixedPoint) (v t fixedPoint) (Set.Ici t) t := by
    intro t _
    have h_field_zero : v t fixedPoint = 0 := by
      simp [hv_def, field_fixedPoint]
    rw [h_field_zero]
    exact (hasDerivWithinAt_const t _ _)
  have h_sol_in_s : ∀ t ∈ Set.Ico (0 : ℝ) T, sol.trajectory t ∈ s t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    exact h_traj_in_ball t ht'
  have h_const_in_s : ∀ t ∈ Set.Ico (0 : ℝ) T, fixedPoint ∈ s t :=
    fun _ _ => h_fp_in_ball
  have h_init : sol.trajectory 0 = fixedPoint := by
    have := sol.init_cond
    simpa [cf24PIVP] using this
  have h_eqOn :=
    ODE_solution_unique_of_mem_Icc_right (v := v) (s := s) (K := K)
      hv_lip hy_contIcc h_sol_hd h_sol_in_s h_const_cont h_const_hd h_const_in_s h_init
  have ht₀_in : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨ht₀_nn, by linarith⟩
  have h_traj_at_t₀ : sol.trajectory t₀ = fixedPoint := h_eqOn ht₀_in
  -- Conclude: V(traj t₀) = V(fixedPoint) = 0, contradicting `0 < V(traj t₀)`.
  rw [h_traj_at_t₀, lyapunov_fixedPoint] at hV_pos
  exact lt_irrefl 0 hV_pos

/-- Corrected basin-entry property: if the initial Lyapunov value is already
in the open sublevel band `(0, 1/512)`, then basin entry holds — trivially,
at `t₀ = 0`. -/
def Cf24BasinEntryFromSmallInit : Prop :=
  ∀ (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1),
    0 < x0 0 → 0 < x0 1 → 0 < x0 2 →
    0 < lyapunov x0 → lyapunov x0 < 1 / 512 →
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      0 < lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀) ∧
      lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀) < 1 / 512

/-- **Corrected basin-entry holds.**

When the assumption `Cf24BasinEntry` is patched to require the initial
Lyapunov value to already lie in `(0, 1/512)`, the conclusion is trivial:
take `t₀ = 0` and use `traj 0 = x0`. -/
theorem cf24_basinEntry_fromSmallInit : Cf24BasinEntryFromSmallInit := by
  intro x0 h_nn h_simplex _ _ _ hV_pos hV_small
  refine ⟨0, le_refl 0, ?_, ?_⟩
  · have h_init : (cf24_global_solution x0 h_nn h_simplex).trajectory 0 = x0 :=
      (cf24_global_solution x0 h_nn h_simplex).init_cond
    rw [h_init]; exact hV_pos
  · have h_init : (cf24_global_solution x0 h_nn h_simplex).trajectory 0 = x0 :=
      (cf24_global_solution x0 h_nn h_simplex).init_cond
    rw [h_init]; exact hV_small

/-- **Medium-init basin entry — constructive, unconditional.**

Stronger than `Cf24BasinEntryFromSmallInit`: from any interior simplex
point with `0 < V(x0) < 1/128`, the trajectory eventually enters the
small-init sublevel set `V < 1/512`.  The proof composes the parametric
decay envelope at `δ = 1/8` (so `ρ = 1/128`) with
`lyapunov_tendsto_zero_of_exp_bound` and Filter.eventually-atTop
extraction.

Note: we do *not* claim `0 < V(traj t₀)` (that would need a
backward-Grönwall lower envelope, not directly in the chain).  This is
unnecessary for the readout chain, which now bypasses time-shift via
`cf24_step5_readout_from_medium_init` and
`cf24_step5_readout_from_analytic_basin`. -/
theorem cf24_basinEntry_from_medium_init
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0) (hV0_med : lyapunov x0 < 1 / 128) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀)
        < 1 / 512 := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  -- Parametric δ-radius and rate.
  set δ : ℝ := 1 / 8 with hδ_def
  have hδ_nn : 0 ≤ δ := by show (0 : ℝ) ≤ 1/8; norm_num
  have hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5 := by
    -- Need: 4 < 13 − 4√5, i.e. √5 < 9/4. Square: 5 < 81/16 ✓.
    have h_sqrt_bd : Real.sqrt 5 < 9 / 4 := by
      have h1 : Real.sqrt 5 < Real.sqrt ((9 / 4) ^ 2) := by
        apply Real.sqrt_lt_sqrt (by norm_num)
        norm_num
      have h2 : Real.sqrt ((9 / 4) ^ 2) = 9 / 4 :=
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9/4)
      linarith [h1, h2.le, h2.ge]
    have h32δ : (32 : ℝ) * (1 / 8) = 4 := by norm_num
    show (32 : ℝ) * (1/8) < 13 - 4 * Real.sqrt 5
    rw [h32δ]; linarith
  set α : ℝ := (13 - 4 * Real.sqrt 5) - 32 * δ with hα_def
  have hα_pos : 0 < α := by
    show 0 < (13 - 4 * Real.sqrt 5) - 32 * δ; linarith
  -- Standard ODE-side hypotheses on `sol`.
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x :=
    fun _ => rfl
  have hx_init : sol.trajectory 0 = x0 := sol.init_cond
  have hV0_pos' : 0 < lyapunov (sol.trajectory 0) := by rw [hx_init]; exact hV0_pos
  have h2V_le : 2 * lyapunov (sol.trajectory 0) ≤ δ^2 := by
    rw [hx_init]
    have hδsq : δ^2 = 1 / 64 := by show ((1 : ℝ)/8)^2 = 1/64; norm_num
    rw [hδsq]; linarith
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht; have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hly_cont : Continuous lyapunov := by
    unfold lyapunov
    exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
      |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
  -- Pointwise envelope: V(traj t) ≤ V(traj 0) · exp(-α·t) for all t ≥ 0.
  have h_envelope : ∀ t : ℝ, 0 ≤ t →
      lyapunov (sol.trajectory t)
        ≤ lyapunov (sol.trajectory 0) * Real.exp (-α * t) := by
    intro t ht
    set T : ℝ := t + 1 with hT_def
    have hT_pos : 0 < T := by linarith
    have hT_nn : 0 ≤ T := hT_pos.le
    have hV_cont : ContinuousOn (fun s => lyapunov (sol.trajectory s))
        (Set.Icc 0 T) := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      have hsol_cont : ContinuousAt (fun u => sol.trajectory u) s :=
        (hy_deriv s hs_nn).continuousAt
      exact (hly_cont.continuousAt.comp hsol_cont).continuousWithinAt
    have hx_deriv_b : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun u => sol.trajectory u 1)
          (field (sol.trajectory s) 1) (Set.Ici s) s := fun s hs =>
      (hasDerivAt_pi.mp (hy_deriv s hs.1) 1).hasDerivWithinAt
    have hx_deriv_c : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun u => sol.trajectory u 2)
          (field (sol.trajectory s) 2) (Set.Ici s) s := fun s hs =>
      (hasDerivAt_pi.mp (hy_deriv s hs.1) 2).hasDerivWithinAt
    have hx_simplex_T : ∀ s ∈ Set.Ico (0 : ℝ) T,
        sol.trajectory s 0 + sol.trajectory s 1 + sol.trajectory s 2 = 1 := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      have h_ode : ∀ u ∈ Set.Ico (0 : ℝ) T,
          HasDerivAt sol.trajectory (field (sol.trajectory u)) u :=
        fun u hu => sol.is_solution u hu.1
      have h_eq :=
        conservative_local_sum_const field_conservative T hT_pos
          sol.trajectory h_ode s ⟨hs_nn, hs.2⟩
      have h_init_sum : ∑ i, sol.trajectory 0 i = 1 := by
        rw [hx_init]; exact h_simplex
      have := h_eq.trans h_init_sum
      simpa [Fin.sum_univ_three] using this
    have h_decay := cf24_local_exponential_decay_param
      hT_nn δ hδ_nn hδ_lt hV0_pos' h2V_le hV_cont
      hx_deriv_b hx_deriv_c hx_simplex_T
    exact h_decay t ⟨ht, by linarith⟩
  -- V(traj t) → 0 by exp envelope.
  have hV_to_zero : Filter.Tendsto (fun t => lyapunov (sol.trajectory t))
      Filter.atTop (nhds 0) :=
    lyapunov_tendsto_zero_of_exp_bound (α := α)
      (C := lyapunov (sol.trajectory 0)) hα_pos h_envelope
  -- Extract a t₀ ≥ 0 with V(traj t₀) < 1/512.
  have h_lt : (0 : ℝ) < 1 / 512 := by norm_num
  have h_eventually_lt : ∀ᶠ t in Filter.atTop,
      lyapunov (sol.trajectory t) < 1 / 512 :=
    hV_to_zero.eventually (eventually_lt_nhds h_lt)
  have h_eventually_nn : ∀ᶠ t in Filter.atTop, (0 : ℝ) ≤ t :=
    Filter.eventually_atTop.mpr ⟨0, fun t ht => ht⟩
  rcases (h_eventually_nn.and h_eventually_lt).exists with ⟨t₀, ht₀_nn, h_V_lt⟩
  exact ⟨t₀, ht₀_nn, h_V_lt⟩

/-- **Lyapunov decays to zero from medium initial value.**

Same parametric chain as `cf24_basinEntry_from_medium_init`, exposing the
strong conclusion: `V(traj t) → 0` along the global solution.  Subsumes
the eventual-entry conclusion. -/
theorem cf24_lyapunov_tendsto_zero_from_medium_init
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0) (hV0_med : lyapunov x0 < 1 / 128) :
    Filter.Tendsto
      (fun t => lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t))
      Filter.atTop (nhds 0) := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  set δ : ℝ := 1 / 8 with hδ_def
  have hδ_nn : 0 ≤ δ := by show (0 : ℝ) ≤ 1/8; norm_num
  have hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5 := by
    have h_sqrt_bd : Real.sqrt 5 < 9 / 4 := by
      have h1 : Real.sqrt 5 < Real.sqrt ((9 / 4) ^ 2) := by
        apply Real.sqrt_lt_sqrt (by norm_num); norm_num
      have h2 : Real.sqrt ((9 / 4) ^ 2) = 9 / 4 :=
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9/4)
      linarith [h1, h2.le, h2.ge]
    have h32δ : (32 : ℝ) * (1 / 8) = 4 := by norm_num
    show (32 : ℝ) * (1/8) < 13 - 4 * Real.sqrt 5
    rw [h32δ]; linarith
  set α : ℝ := (13 - 4 * Real.sqrt 5) - 32 * δ with hα_def
  have hα_pos : 0 < α := by show 0 < (13 - 4 * Real.sqrt 5) - 32 * δ; linarith
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x :=
    fun _ => rfl
  have hx_init : sol.trajectory 0 = x0 := sol.init_cond
  have hV0_pos' : 0 < lyapunov (sol.trajectory 0) := by rw [hx_init]; exact hV0_pos
  have h2V_le : 2 * lyapunov (sol.trajectory 0) ≤ δ^2 := by
    rw [hx_init]
    have hδsq : δ^2 = 1 / 64 := by show ((1 : ℝ)/8)^2 = 1/64; norm_num
    rw [hδsq]; linarith
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht; have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hly_cont : Continuous lyapunov := by
    unfold lyapunov
    exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
      |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
  have h_envelope : ∀ t : ℝ, 0 ≤ t →
      lyapunov (sol.trajectory t)
        ≤ lyapunov (sol.trajectory 0) * Real.exp (-α * t) := by
    intro t ht
    set T : ℝ := t + 1 with hT_def
    have hT_pos : 0 < T := by linarith
    have hT_nn : 0 ≤ T := hT_pos.le
    have hV_cont : ContinuousOn (fun s => lyapunov (sol.trajectory s))
        (Set.Icc 0 T) := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      have hsol_cont : ContinuousAt (fun u => sol.trajectory u) s :=
        (hy_deriv s hs_nn).continuousAt
      exact (hly_cont.continuousAt.comp hsol_cont).continuousWithinAt
    have hx_deriv_b : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun u => sol.trajectory u 1)
          (field (sol.trajectory s) 1) (Set.Ici s) s := fun s hs =>
      (hasDerivAt_pi.mp (hy_deriv s hs.1) 1).hasDerivWithinAt
    have hx_deriv_c : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun u => sol.trajectory u 2)
          (field (sol.trajectory s) 2) (Set.Ici s) s := fun s hs =>
      (hasDerivAt_pi.mp (hy_deriv s hs.1) 2).hasDerivWithinAt
    have hx_simplex_T : ∀ s ∈ Set.Ico (0 : ℝ) T,
        sol.trajectory s 0 + sol.trajectory s 1 + sol.trajectory s 2 = 1 := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      have h_ode : ∀ u ∈ Set.Ico (0 : ℝ) T,
          HasDerivAt sol.trajectory (field (sol.trajectory u)) u :=
        fun u hu => sol.is_solution u hu.1
      have h_eq :=
        conservative_local_sum_const field_conservative T hT_pos
          sol.trajectory h_ode s ⟨hs_nn, hs.2⟩
      have h_init_sum : ∑ i, sol.trajectory 0 i = 1 := by
        rw [hx_init]; exact h_simplex
      have := h_eq.trans h_init_sum
      simpa [Fin.sum_univ_three] using this
    have h_decay := cf24_local_exponential_decay_param
      hT_nn δ hδ_nn hδ_lt hV0_pos' h2V_le hV_cont
      hx_deriv_b hx_deriv_c hx_simplex_T
    exact h_decay t ⟨ht, by linarith⟩
  exact lyapunov_tendsto_zero_of_exp_bound (α := α)
    (C := lyapunov (sol.trajectory 0)) hα_pos h_envelope

/-- **Step 5 readout convergence from medium initial value — unconditional.**

From any interior simplex point with `0 < V(x0) < 1/128`, the readout
`z_11(t) + z_01(t)/2` converges to `(3 − √5)/6` as `t → ∞`.

Critically, this is *unconditional* (no `Cf24BasinEntry` hypothesis):
the basin radius `1/128` is constructively reached via the parametric
decay chain at `δ = 1/8` (close to the analytic ceiling `(13−4√5)²/2048
≈ 1/124.6`). -/
theorem cf24_step5_readout_from_medium_init
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0) (hV0_med : lyapunov x0 < 1 / 128) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) :=
  cf24_readout_tendsto_of_lyapunov_zero
    (cf24_lyapunov_tendsto_zero_from_medium_init x0 h_nn h_simplex hV0_pos hV0_med)

/-- **Parametric Lyapunov tendsto zero — workhorse.**

Generalizes the medium-init chain: for any `δ ≥ 0` with `32 δ < 13 − 4√5`
and `2 V(x0) ≤ δ²`, the trajectory's Lyapunov value tends to zero.  Used
to prove the analytic-ceiling readout convergence below. -/
theorem cf24_lyapunov_tendsto_zero_param
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5)
    (h2V_le : 2 * lyapunov x0 ≤ δ^2) :
    Filter.Tendsto
      (fun t => lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t))
      Filter.atTop (nhds 0) := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  set α : ℝ := (13 - 4 * Real.sqrt 5) - 32 * δ with hα_def
  have hα_pos : 0 < α := by show 0 < (13 - 4 * Real.sqrt 5) - 32 * δ; linarith
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x :=
    fun _ => rfl
  have hx_init : sol.trajectory 0 = x0 := sol.init_cond
  have hV0_pos' : 0 < lyapunov (sol.trajectory 0) := by rw [hx_init]; exact hV0_pos
  have h2V_le' : 2 * lyapunov (sol.trajectory 0) ≤ δ^2 := by
    rw [hx_init]; exact h2V_le
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht; have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hly_cont : Continuous lyapunov := by
    unfold lyapunov
    exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
      |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
  have h_envelope : ∀ t : ℝ, 0 ≤ t →
      lyapunov (sol.trajectory t)
        ≤ lyapunov (sol.trajectory 0) * Real.exp (-α * t) := by
    intro t ht
    set T : ℝ := t + 1 with hT_def
    have hT_pos : 0 < T := by linarith
    have hT_nn : 0 ≤ T := hT_pos.le
    have hV_cont : ContinuousOn (fun s => lyapunov (sol.trajectory s))
        (Set.Icc 0 T) := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      have hsol_cont : ContinuousAt (fun u => sol.trajectory u) s :=
        (hy_deriv s hs_nn).continuousAt
      exact (hly_cont.continuousAt.comp hsol_cont).continuousWithinAt
    have hx_deriv_b : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun u => sol.trajectory u 1)
          (field (sol.trajectory s) 1) (Set.Ici s) s := fun s hs =>
      (hasDerivAt_pi.mp (hy_deriv s hs.1) 1).hasDerivWithinAt
    have hx_deriv_c : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun u => sol.trajectory u 2)
          (field (sol.trajectory s) 2) (Set.Ici s) s := fun s hs =>
      (hasDerivAt_pi.mp (hy_deriv s hs.1) 2).hasDerivWithinAt
    have hx_simplex_T : ∀ s ∈ Set.Ico (0 : ℝ) T,
        sol.trajectory s 0 + sol.trajectory s 1 + sol.trajectory s 2 = 1 := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      have h_ode : ∀ u ∈ Set.Ico (0 : ℝ) T,
          HasDerivAt sol.trajectory (field (sol.trajectory u)) u :=
        fun u hu => sol.is_solution u hu.1
      have h_eq :=
        conservative_local_sum_const field_conservative T hT_pos
          sol.trajectory h_ode s ⟨hs_nn, hs.2⟩
      have h_init_sum : ∑ i, sol.trajectory 0 i = 1 := by
        rw [hx_init]; exact h_simplex
      have := h_eq.trans h_init_sum
      simpa [Fin.sum_univ_three] using this
    have h_decay := cf24_local_exponential_decay_param
      hT_nn δ hδ_nn hδ_lt hV0_pos' h2V_le' hV_cont
      hx_deriv_b hx_deriv_c hx_simplex_T
    exact h_decay t ⟨ht, by linarith⟩
  exact lyapunov_tendsto_zero_of_exp_bound (α := α)
    (C := lyapunov (sol.trajectory 0)) hα_pos h_envelope

/-- **Step 5 readout convergence at the analytic basin ceiling — unconditional.**

Maximal constructive basin: for any interior simplex point with
`0 < V(x0) < (13 − 4√5)² / 2048 ≈ 1/124.6`, the readout converges to
`(3 − √5)/6`.  This is the largest sublevel set reachable by the
parametric chain: setting `δ = √(2 V(x0))` makes `δ² = 2 V(x0)` exactly,
and `32 δ < 13 − 4√5` is equivalent to `V(x0) < (13 − 4√5)² / 2048`.

Subsumes `cf24_step5_readout_from_medium_init`: `1/128 < 1/124.6`-ish
is replaced by the sharp irrational ceiling. -/
theorem cf24_step5_readout_from_analytic_basin
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (hV0_lt_max : lyapunov x0 < (13 - 4 * Real.sqrt 5)^2 / 2048) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  -- Pick δ = √(2 V(x0)).  Then δ² = 2 V(x0) and 32 δ < 13 − 4√5.
  set δ := Real.sqrt (2 * lyapunov x0) with hδ_def
  have h2V_pos : 0 < 2 * lyapunov x0 := by linarith
  have h2V_nn : 0 ≤ 2 * lyapunov x0 := h2V_pos.le
  have hδ_nn : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ^2 = 2 * lyapunov x0 := by
    rw [hδ_def, sq, ← Real.sqrt_mul h2V_nn, Real.sqrt_mul_self h2V_nn]
  have h2V_le : 2 * lyapunov x0 ≤ δ^2 := by rw [hδsq]
  -- 13 − 4√5 > 0 (since √5 < 13/4 ⟺ 5 < 169/16 ⟺ 80 < 169).
  have h_sqrt5_lt : Real.sqrt 5 < 13 / 4 := by
    have h1 : Real.sqrt 5 < Real.sqrt ((13 / 4)^2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    have h2 : Real.sqrt ((13 / 4)^2) = 13 / 4 :=
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 13/4)
    linarith [h1, h2.le, h2.ge]
  have h_pos : 0 < 13 - 4 * Real.sqrt 5 := by linarith
  -- 32 δ < 13 − 4√5 by squaring (both sides ≥ 0).
  have hδ_lt : 32 * δ < 13 - 4 * Real.sqrt 5 := by
    have h32δ_nn : 0 ≤ 32 * δ := by positivity
    have h_sq_lt : (32 * δ)^2 < (13 - 4 * Real.sqrt 5)^2 := by
      have h1 : (32 * δ)^2 = 1024 * δ^2 := by ring
      rw [h1, hδsq]
      -- Need 1024 · 2 V₀ < (13 − 4√5)², i.e. 2048 V₀ < (13 − 4√5)².
      linarith [hV0_lt_max]
    have h_sqrt_lt : Real.sqrt ((32 * δ)^2) < Real.sqrt ((13 - 4 * Real.sqrt 5)^2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_lt
    have hL : Real.sqrt ((32 * δ)^2) = 32 * δ := Real.sqrt_sq h32δ_nn
    have hR : Real.sqrt ((13 - 4 * Real.sqrt 5)^2) = 13 - 4 * Real.sqrt 5 :=
      Real.sqrt_sq h_pos.le
    linarith [h_sqrt_lt, hL.le, hL.ge, hR.le, hR.ge]
  -- Apply parametric tendsto-zero, then compose with readout convergence.
  exact cf24_readout_tendsto_of_lyapunov_zero
    (cf24_lyapunov_tendsto_zero_param x0 h_nn h_simplex hV0_pos
      δ hδ_nn hδ_lt h2V_le)

/-- **Readout convergence from L¹ ball around the fixed point.**

User-friendly form of `cf24_step5_readout_from_analytic_basin`: if the
initial state lies in the open L¹ ball of radius `1/12` around
`(b*, c*) = (z_01*, z_11*)`, the readout converges to `(3 − √5)/6`.

Containment chain:
  `|Δb| + |Δc| < 1/12  ⟹  V = Δb² + Δc² ≤ (|Δb|+|Δc|)² < 1/144`
  `1/144  <  (13 − 4√5)² / 2048`  (since `√5 < 9/4`).

The L¹ ball radius `1/12` is the largest clean rational bound that
fits inside the analytic basin. -/
theorem cf24_step5_readout_from_l1_ball
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (hball : |x0 1 - fixedPoint 1| + |x0 2 - fixedPoint 2| < 1 / 12) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  -- Step 1: V(x0) ≤ (|Δb|+|Δc|)² < 1/144.
  set u := x0 1 - fixedPoint 1 with hu_def
  set v := x0 2 - fixedPoint 2 with hv_def
  have habs_nn : 0 ≤ |u| + |v| := by positivity
  have h_uv_sq : u^2 + v^2 ≤ (|u| + |v|)^2 := by
    have hcross : 0 ≤ 2 * |u| * |v| := by positivity
    have hexp : (|u| + |v|)^2 = u^2 + 2 * |u| * |v| + v^2 := by
      have h1 : (|u| + |v|)^2 = |u|^2 + 2 * |u| * |v| + |v|^2 := by ring
      have h2 : |u|^2 = u^2 := sq_abs u
      have h3 : |v|^2 = v^2 := sq_abs v
      rw [h1, h2, h3]
    linarith
  have hV_eq : lyapunov x0 = u^2 + v^2 := by
    show (x0 1 - fixedPoint 1)^2 + (x0 2 - fixedPoint 2)^2 = _
    rw [hu_def, hv_def]
  have hsq_lt : (|u| + |v|)^2 < (1/12)^2 := by
    have h_pos := lt_of_le_of_lt habs_nn hball
    have := mul_self_lt_mul_self habs_nn hball
    linarith [this, h_pos.le]
  have hV_lt : lyapunov x0 < 1 / 144 := by
    rw [hV_eq]
    calc u^2 + v^2 ≤ (|u| + |v|)^2 := h_uv_sq
      _ < (1/12)^2 := hsq_lt
      _ = 1 / 144 := by norm_num
  -- Step 2: 1/144 < (13 − 4√5)² / 2048.
  have h_sqrt5_lt : Real.sqrt 5 < 9 / 4 := by
    have h1 : Real.sqrt 5 < Real.sqrt ((9 / 4)^2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    have h2 : Real.sqrt ((9 / 4)^2) = 9 / 4 :=
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9/4)
    linarith [h1, h2.le, h2.ge]
  have h_sqrt5_sq : (Real.sqrt 5)^2 = 5 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h_basin_gt : (1 : ℝ) / 144 < (13 - 4 * Real.sqrt 5)^2 / 2048 := by
    -- (13 − 4√5)² = 249 − 104√5; need 144·(249−104√5) > 2048,
    -- i.e. 14976·√5 < 33808.  Since √5 < 9/4, 14976·(9/4) = 33696 < 33808.
    have h_expand : (13 - 4 * Real.sqrt 5)^2 = 249 - 104 * Real.sqrt 5 := by
      have : (13 - 4 * Real.sqrt 5)^2
          = 169 - 104 * Real.sqrt 5 + 16 * (Real.sqrt 5)^2 := by ring
      rw [this, h_sqrt5_sq]; ring
    rw [h_expand]
    linarith [h_sqrt5_lt]
  have hV_lt_max : lyapunov x0 < (13 - 4 * Real.sqrt 5)^2 / 2048 :=
    lt_trans hV_lt h_basin_gt
  exact cf24_step5_readout_from_analytic_basin x0 h_nn h_simplex hV0_pos hV_lt_max

/-- **Sharp parametric Lyapunov tendsto zero — V-sublevel form.**

Sharp analogue of `cf24_lyapunov_tendsto_zero_param`: for any `δ ≥ 0`
with `28·δ < 13 − 4√5` and `V(x0) ≤ δ²`, the trajectory's Lyapunov value
tends to zero.  Drives the sharp-basin readout theorem below. -/
theorem cf24_lyapunov_tendsto_zero_sharp
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_lt : 28 * δ < 13 - 4 * Real.sqrt 5)
    (hV_le : lyapunov x0 ≤ δ^2) :
    Filter.Tendsto
      (fun t => lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t))
      Filter.atTop (nhds 0) := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  set α : ℝ := (13 - 4 * Real.sqrt 5) - 28 * δ with hα_def
  have hα_pos : 0 < α := by show 0 < (13 - 4 * Real.sqrt 5) - 28 * δ; linarith
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x :=
    fun _ => rfl
  have hx_init : sol.trajectory 0 = x0 := sol.init_cond
  have hV0_pos' : 0 < lyapunov (sol.trajectory 0) := by rw [hx_init]; exact hV0_pos
  have hV_le' : lyapunov (sol.trajectory 0) ≤ δ^2 := by
    rw [hx_init]; exact hV_le
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht; have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hly_cont : Continuous lyapunov := by
    unfold lyapunov
    exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
      |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
  have h_envelope : ∀ t : ℝ, 0 ≤ t →
      lyapunov (sol.trajectory t)
        ≤ lyapunov (sol.trajectory 0) * Real.exp (-α * t) := by
    intro t ht
    set T : ℝ := t + 1 with hT_def
    have hT_pos : 0 < T := by linarith
    have hT_nn : 0 ≤ T := hT_pos.le
    have hV_cont : ContinuousOn (fun s => lyapunov (sol.trajectory s))
        (Set.Icc 0 T) := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      have hsol_cont : ContinuousAt (fun u => sol.trajectory u) s :=
        (hy_deriv s hs_nn).continuousAt
      exact (hly_cont.continuousAt.comp hsol_cont).continuousWithinAt
    have hx_deriv_b : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun u => sol.trajectory u 1)
          (field (sol.trajectory s) 1) (Set.Ici s) s := fun s hs =>
      (hasDerivAt_pi.mp (hy_deriv s hs.1) 1).hasDerivWithinAt
    have hx_deriv_c : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun u => sol.trajectory u 2)
          (field (sol.trajectory s) 2) (Set.Ici s) s := fun s hs =>
      (hasDerivAt_pi.mp (hy_deriv s hs.1) 2).hasDerivWithinAt
    have hx_simplex_T : ∀ s ∈ Set.Ico (0 : ℝ) T,
        sol.trajectory s 0 + sol.trajectory s 1 + sol.trajectory s 2 = 1 := by
      intro s hs
      have hs_nn : 0 ≤ s := hs.1
      have h_ode : ∀ u ∈ Set.Ico (0 : ℝ) T,
          HasDerivAt sol.trajectory (field (sol.trajectory u)) u :=
        fun u hu => sol.is_solution u hu.1
      have h_eq :=
        conservative_local_sum_const field_conservative T hT_pos
          sol.trajectory h_ode s ⟨hs_nn, hs.2⟩
      have h_init_sum : ∑ i, sol.trajectory 0 i = 1 := by
        rw [hx_init]; exact h_simplex
      have := h_eq.trans h_init_sum
      simpa [Fin.sum_univ_three] using this
    have h_decay := cf24_local_exponential_decay_sharp
      hT_nn δ hδ_nn hδ_lt hV0_pos' hV_le' hV_cont
      hx_deriv_b hx_deriv_c hx_simplex_T
    exact h_decay t ⟨ht, by linarith⟩
  exact lyapunov_tendsto_zero_of_exp_bound (α := α)
    (C := lyapunov (sol.trajectory 0)) hα_pos h_envelope

/-- **Step 5 readout convergence — SHARP analytic basin** (2.6× extension).

For any interior simplex point with `0 < V(x0) < (13 − 4√5)² / 784 ≈ 1/47.7`,
the readout converges to `(3 − √5)/6`.

This is the largest sublevel set reachable by the V-sublevel parametric
chain (sharp constant `28` from the squared cubic-remainder inequality):
setting `δ = √V(x0)` gives `δ² = V(x0)`, and `28·δ < 13 − 4√5` is
equivalent to `V(x0) < (13 − 4√5)² / 784`.

This subsumes `cf24_step5_readout_from_analytic_basin` (the `2048`
denominator → `784` is the 2.6× improvement). -/
theorem cf24_step5_readout_from_sharp_basin
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (hV0_lt_max : lyapunov x0 < (13 - 4 * Real.sqrt 5)^2 / 784) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  -- Pick δ = √V(x0).  Then δ² = V(x0) and 28 δ < 13 − 4√5.
  set δ := Real.sqrt (lyapunov x0) with hδ_def
  have hV0_nn : 0 ≤ lyapunov x0 := hV0_pos.le
  have hδ_nn : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ^2 = lyapunov x0 := by
    rw [hδ_def, sq, ← Real.sqrt_mul hV0_nn, Real.sqrt_mul_self hV0_nn]
  have hV_le : lyapunov x0 ≤ δ^2 := by rw [hδsq]
  have h_sqrt5_lt : Real.sqrt 5 < 13 / 4 := by
    have h1 : Real.sqrt 5 < Real.sqrt ((13 / 4)^2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    have h2 : Real.sqrt ((13 / 4)^2) = 13 / 4 :=
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 13/4)
    linarith [h1, h2.le, h2.ge]
  have h_pos : 0 < 13 - 4 * Real.sqrt 5 := by linarith
  -- 28 δ < 13 − 4√5 by squaring (both sides ≥ 0).
  have hδ_lt : 28 * δ < 13 - 4 * Real.sqrt 5 := by
    have h28δ_nn : 0 ≤ 28 * δ := by positivity
    have h_sq_lt : (28 * δ)^2 < (13 - 4 * Real.sqrt 5)^2 := by
      have h1 : (28 * δ)^2 = 784 * δ^2 := by ring
      rw [h1, hδsq]
      -- Need 784 V₀ < (13 − 4√5)².
      linarith [hV0_lt_max]
    have h_sqrt_lt : Real.sqrt ((28 * δ)^2) < Real.sqrt ((13 - 4 * Real.sqrt 5)^2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_lt
    have hL : Real.sqrt ((28 * δ)^2) = 28 * δ := Real.sqrt_sq h28δ_nn
    have hR : Real.sqrt ((13 - 4 * Real.sqrt 5)^2) = 13 - 4 * Real.sqrt 5 :=
      Real.sqrt_sq h_pos.le
    linarith [h_sqrt_lt, hL.le, hL.ge, hR.le, hR.ge]
  exact cf24_readout_tendsto_of_lyapunov_zero
    (cf24_lyapunov_tendsto_zero_sharp x0 h_nn h_simplex hV0_pos
      δ hδ_nn hδ_lt hV_le)

/-- **Sharp medium-init readout convergence (clean rational).**

Convenient rational specialization of `cf24_step5_readout_from_sharp_basin`:
for `V(x0) < 1/49` the readout converges.  The constant `1/49` is the
largest clean unit-fraction strictly below `(13 − 4√5)²/784`, certified
via the simple bound `(13 − 4√5)² > 16` (from `√5 < 9/4`).

Compared to `cf24_step5_readout_from_medium_init` (V₀ < 1/128), this is
a `2.6×` extension of the medium-init basin. -/
theorem cf24_step5_readout_from_sharp_medium_init
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0) (hV0_med : lyapunov x0 < 1 / 49) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  -- 1/49 < (13 − 4√5)² / 784 via (13 − 4√5)² > 16 from √5 < 9/4.
  have h_sqrt5_lt : Real.sqrt 5 < 9 / 4 := by
    have h1 : Real.sqrt 5 < Real.sqrt ((9 / 4)^2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    have h2 : Real.sqrt ((9 / 4)^2) = 9 / 4 :=
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9/4)
    linarith [h1, h2.le, h2.ge]
  have h_sqrt5_sq : (Real.sqrt 5)^2 = 5 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h_basin_gt : (1 : ℝ) / 49 < (13 - 4 * Real.sqrt 5)^2 / 784 := by
    have h_expand : (13 - 4 * Real.sqrt 5)^2 = 249 - 104 * Real.sqrt 5 := by
      have : (13 - 4 * Real.sqrt 5)^2
          = 169 - 104 * Real.sqrt 5 + 16 * (Real.sqrt 5)^2 := by ring
      rw [this, h_sqrt5_sq]; ring
    rw [h_expand]
    nlinarith [h_sqrt5_lt]
  have hV_lt_max : lyapunov x0 < (13 - 4 * Real.sqrt 5)^2 / 784 :=
    lt_trans hV0_med h_basin_gt
  exact cf24_step5_readout_from_sharp_basin x0 h_nn h_simplex hV0_pos hV_lt_max

/-- **Sharp L¹-ball readout convergence.**

User-friendly form of `cf24_step5_readout_from_sharp_basin`: if the initial
state lies in the open L¹ ball of radius `1/8` around `(b*, c*)`, the
readout converges to `(3 − √5)/6`.

Containment: `|Δb|+|Δc| < 1/8 ⟹ V ≤ (|Δb|+|Δc|)² < 1/64 < (13−4√5)²/784`.

The radius `1/8 ≈ 0.125` is a clean rational inside the sharp ball
`r < (13−4√5)/28 ≈ 0.1448`.  This is `1.5×` larger than the L¹ radius
`1/12` admitted by the (non-sharp) `cf24_step5_readout_from_l1_ball`. -/
theorem cf24_step5_readout_from_sharp_l1_ball
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (hball : |x0 1 - fixedPoint 1| + |x0 2 - fixedPoint 2| < 1 / 8) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  set u := x0 1 - fixedPoint 1 with hu_def
  set v := x0 2 - fixedPoint 2 with hv_def
  have habs_nn : 0 ≤ |u| + |v| := by positivity
  have h_uv_sq : u^2 + v^2 ≤ (|u| + |v|)^2 := by
    have hcross : 0 ≤ 2 * |u| * |v| := by positivity
    have hexp : (|u| + |v|)^2 = u^2 + 2 * |u| * |v| + v^2 := by
      have h1 : (|u| + |v|)^2 = |u|^2 + 2 * |u| * |v| + |v|^2 := by ring
      have h2 : |u|^2 = u^2 := sq_abs u
      have h3 : |v|^2 = v^2 := sq_abs v
      rw [h1, h2, h3]
    linarith
  have hV_eq : lyapunov x0 = u^2 + v^2 := by
    show (x0 1 - fixedPoint 1)^2 + (x0 2 - fixedPoint 2)^2 = _
    rw [hu_def, hv_def]
  have hsq_lt : (|u| + |v|)^2 < (1/8)^2 := by
    have h_pos := lt_of_le_of_lt habs_nn hball
    have := mul_self_lt_mul_self habs_nn hball
    linarith [this, h_pos.le]
  have hV_lt : lyapunov x0 < 1 / 64 := by
    rw [hV_eq]
    calc u^2 + v^2 ≤ (|u| + |v|)^2 := h_uv_sq
      _ < (1/8)^2 := hsq_lt
      _ = 1 / 64 := by norm_num
  -- 1/64 < (13 − 4√5)² / 784.  Use √5 < 9/4 ⟹ (13 − 4√5)² > 15.
  have h_sqrt5_lt : Real.sqrt 5 < 9 / 4 := by
    have h1 : Real.sqrt 5 < Real.sqrt ((9 / 4)^2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    have h2 : Real.sqrt ((9 / 4)^2) = 9 / 4 :=
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9/4)
    linarith [h1, h2.le, h2.ge]
  have h_sqrt5_sq : (Real.sqrt 5)^2 = 5 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h_basin_gt : (1 : ℝ) / 64 < (13 - 4 * Real.sqrt 5)^2 / 784 := by
    -- (13 − 4√5)² = 249 − 104√5; need 784 < 64·(249−104√5) = 15936 − 6656√5,
    -- i.e. 6656√5 < 15152, √5 < 15152/6656 = 2.2766…, satisfied by √5 < 9/4 = 2.25.
    have h_expand : (13 - 4 * Real.sqrt 5)^2 = 249 - 104 * Real.sqrt 5 := by
      have : (13 - 4 * Real.sqrt 5)^2
          = 169 - 104 * Real.sqrt 5 + 16 * (Real.sqrt 5)^2 := by ring
      rw [this, h_sqrt5_sq]; ring
    rw [h_expand]
    linarith [h_sqrt5_lt]
  have hV_lt_max : lyapunov x0 < (13 - 4 * Real.sqrt 5)^2 / 784 :=
    lt_trans hV_lt h_basin_gt
  exact cf24_step5_readout_from_sharp_basin x0 h_nn h_simplex hV0_pos hV_lt_max

/-- **Sharper L¹-ball readout convergence (radius `1/7`, closer to the
analytic ceiling).**

The L¹ analytic ceiling is `r* = (13 − 4√5) / 28 ≈ 0.1448`.  The cleanest
rational with `1/n < r*` is `1/7 ≈ 0.1428`.  In V-terms, `(1/7)² = 1/49`,
which is the same sublevel threshold used in
`cf24_step5_readout_from_sharp_medium_init`.

Compared to `cf24_step5_readout_from_sharp_l1_ball` (radius `1/8`), this is
a `14%` radius extension (and a `30%` V-sublevel extension `1/64 → 1/49`),
hugging the analytic ceiling. -/
theorem cf24_step5_readout_from_sharper_l1_ball
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (hball : |x0 1 - fixedPoint 1| + |x0 2 - fixedPoint 2| < 1 / 7) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  set u := x0 1 - fixedPoint 1 with hu_def
  set v := x0 2 - fixedPoint 2 with hv_def
  have habs_nn : 0 ≤ |u| + |v| := by positivity
  have h_uv_sq : u^2 + v^2 ≤ (|u| + |v|)^2 := by
    have hcross : 0 ≤ 2 * |u| * |v| := by positivity
    have hexp : (|u| + |v|)^2 = u^2 + 2 * |u| * |v| + v^2 := by
      have h1 : (|u| + |v|)^2 = |u|^2 + 2 * |u| * |v| + |v|^2 := by ring
      have h2 : |u|^2 = u^2 := sq_abs u
      have h3 : |v|^2 = v^2 := sq_abs v
      rw [h1, h2, h3]
    linarith
  have hV_eq : lyapunov x0 = u^2 + v^2 := by
    show (x0 1 - fixedPoint 1)^2 + (x0 2 - fixedPoint 2)^2 = _
    rw [hu_def, hv_def]
  have hsq_lt : (|u| + |v|)^2 < (1/7)^2 := by
    have h_pos := lt_of_le_of_lt habs_nn hball
    have := mul_self_lt_mul_self habs_nn hball
    linarith [this, h_pos.le]
  have hV_lt : lyapunov x0 < 1 / 49 := by
    rw [hV_eq]
    calc u^2 + v^2 ≤ (|u| + |v|)^2 := h_uv_sq
      _ < (1/7)^2 := hsq_lt
      _ = 1 / 49 := by norm_num
  exact cf24_step5_readout_from_sharp_medium_init x0 h_nn h_simplex hV0_pos hV_lt

/-- **Analytic-ceiling L¹-ball readout convergence.**

The exact maximum L¹ radius achievable by the V-sublevel parametric chain is
`r* := (13 − 4√5) / 28`, an irrational number ≈ `0.1448`.  Any L¹-ball strictly
smaller than this gives readout convergence.  This is the SHARPEST L¹ form
the chain produces; rational specializations (`1/8`, `1/7`) round it down. -/
theorem cf24_step5_readout_from_sharp_l1_ball_analytic
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (hball : |x0 1 - fixedPoint 1| + |x0 2 - fixedPoint 2|
              < (13 - 4 * Real.sqrt 5) / 28) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  set u := x0 1 - fixedPoint 1 with hu_def
  set v := x0 2 - fixedPoint 2 with hv_def
  set r : ℝ := (13 - 4 * Real.sqrt 5) / 28 with hr_def
  have habs_nn : 0 ≤ |u| + |v| := by positivity
  have h_sqrt5_lt : Real.sqrt 5 < 13 / 4 := by
    have h1 : Real.sqrt 5 < Real.sqrt ((13 / 4)^2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    have h2 : Real.sqrt ((13 / 4)^2) = 13 / 4 :=
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 13/4)
    linarith [h1, h2.le, h2.ge]
  have hr_pos : 0 < r := by show 0 < (13 - 4 * Real.sqrt 5) / 28; linarith
  have h_uv_sq : u^2 + v^2 ≤ (|u| + |v|)^2 := by
    have hcross : 0 ≤ 2 * |u| * |v| := by positivity
    have hexp : (|u| + |v|)^2 = u^2 + 2 * |u| * |v| + v^2 := by
      have h1 : (|u| + |v|)^2 = |u|^2 + 2 * |u| * |v| + |v|^2 := by ring
      have h2 : |u|^2 = u^2 := sq_abs u
      have h3 : |v|^2 = v^2 := sq_abs v
      rw [h1, h2, h3]
    linarith
  have hV_eq : lyapunov x0 = u^2 + v^2 := by
    show (x0 1 - fixedPoint 1)^2 + (x0 2 - fixedPoint 2)^2 = _
    rw [hu_def, hv_def]
  have hsq_lt : (|u| + |v|)^2 < r^2 := by
    have := mul_self_lt_mul_self habs_nn hball
    linarith [this, hr_pos.le]
  have hr_sq_eq : r^2 = (13 - 4 * Real.sqrt 5)^2 / 784 := by
    show ((13 - 4 * Real.sqrt 5) / 28)^2 = (13 - 4 * Real.sqrt 5)^2 / 784
    field_simp
    ring
  have hV_lt_max : lyapunov x0 < (13 - 4 * Real.sqrt 5)^2 / 784 := by
    rw [hV_eq, ← hr_sq_eq]
    exact lt_of_le_of_lt h_uv_sq hsq_lt
  exact cf24_step5_readout_from_sharp_basin x0 h_nn h_simplex hV0_pos hV_lt_max

/-- **Step 5 unconditional sublemma — readout convergence from `V(x0) < 1/512`.**

Subsumes the basin-entry sorry in the case where the initial Lyapunov value
is already below the sublevel-set threshold.  Fully proved. -/
theorem cf24_step5_readout_from_small_init
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0) (hV0_small : lyapunov x0 < 1 / 512) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  -- Every hypothesis of `cf24_readout_tendsto_from_small_lyapunov_init`
  -- follows directly from properties of `sol`; no time-shift needed.
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x := fun _ => rfl
  have hx_init : sol.trajectory 0 = x0 := sol.init_cond
  have hV0_pos' : 0 < lyapunov (sol.trajectory 0) := by rw [hx_init]; exact hV0_pos
  have hV0_small' : lyapunov (sol.trajectory 0) < 1 / 512 := by
    rw [hx_init]; exact hV0_small
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht
    have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hx_deriv_b : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => sol.trajectory s 1)
        (field (sol.trajectory t) 1) (Set.Ici t) t := fun t ht =>
    (hasDerivAt_pi.mp (hy_deriv t ht) 1).hasDerivWithinAt
  have hx_deriv_c : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => sol.trajectory s 2)
        (field (sol.trajectory t) 2) (Set.Ici t) t := fun t ht =>
    (hasDerivAt_pi.mp (hy_deriv t ht) 2).hasDerivWithinAt
  have hx_simplex : ∀ t ∈ Set.Ici (0 : ℝ),
      sol.trajectory t 0 + sol.trajectory t 1 + sol.trajectory t 2 = 1 := by
    intro t ht
    have ht_nn : (0 : ℝ) ≤ t := ht
    have h_ode : ∀ u ∈ Set.Ico (0 : ℝ) (t + 1),
        HasDerivAt sol.trajectory (field (sol.trajectory u)) u :=
      fun u hu => sol.is_solution u hu.1
    have h_eq :=
      conservative_local_sum_const field_conservative (t + 1) (by linarith)
        sol.trajectory h_ode t ⟨ht_nn, by linarith⟩
    have h_init : ∑ i, sol.trajectory 0 i = 1 := by
      rw [hx_init]; exact h_simplex
    have := h_eq.trans h_init
    simpa [Fin.sum_univ_three] using this
  have hV_cont : ContinuousOn (fun t => lyapunov (sol.trajectory t))
      (Set.Ici 0) := by
    intro t ht
    have hy_cont : ContinuousAt (fun s => sol.trajectory s) t :=
      (hy_deriv t ht).continuousAt
    have hly_cont : Continuous lyapunov := by
      unfold lyapunov
      exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
        |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
    exact (hly_cont.continuousAt.comp hy_cont).continuousWithinAt
  exact cf24_readout_tendsto_from_small_lyapunov_init
    (x := sol.trajectory) hV0_pos' hV0_small' hV_cont
    hx_deriv_b hx_deriv_c hx_simplex

/-! ### Saddle-stable exclusion is automatic in the sharp basin

For any `x0` already in the sharp basin (`V(x0) < (13 − 4√5)²/784`), the
trajectory cannot ω-limit to `saddlePoint`: by the sharp envelope, `V → 0`,
while continuity of `lyapunov` would force `V(traj t) → V(saddle) = 5/9` if
the trajectory tended to saddle.  Limit uniqueness gives a contradiction.

This documents the fact that the saddle-exclusion hypothesis of
`Cf24SaddleExcludedBasinEntry` is *redundant* for any starting condition already in the
sharp basin — equivalently, the "hard case" for the corrected conditional
theorem is exactly the case where `V(x0) ≥ (13 − 4√5)²/784`. -/

/-- Helper: V(traj) → 0 from sharp-basin initial condition.  Wraps
`cf24_lyapunov_tendsto_zero_sharp` with the canonical `δ = √V(x0)`
construction. -/
theorem cf24_lyapunov_tendsto_zero_from_sharp_basin
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (hV0_lt_max : lyapunov x0 < (13 - 4 * Real.sqrt 5)^2 / 784) :
    Filter.Tendsto
      (fun t => lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t))
      Filter.atTop (nhds 0) := by
  set δ := Real.sqrt (lyapunov x0) with hδ_def
  have hV0_nn : 0 ≤ lyapunov x0 := hV0_pos.le
  have hδ_nn : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ^2 = lyapunov x0 := by
    rw [hδ_def, sq, ← Real.sqrt_mul hV0_nn, Real.sqrt_mul_self hV0_nn]
  have hV_le : lyapunov x0 ≤ δ^2 := by rw [hδsq]
  have h_sqrt5_lt : Real.sqrt 5 < 13 / 4 := by
    have h1 : Real.sqrt 5 < Real.sqrt ((13 / 4)^2) := by
      apply Real.sqrt_lt_sqrt (by norm_num); norm_num
    have h2 : Real.sqrt ((13 / 4)^2) = 13 / 4 :=
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 13/4)
    linarith [h1, h2.le, h2.ge]
  have h_pos : 0 < 13 - 4 * Real.sqrt 5 := by linarith
  have hδ_lt : 28 * δ < 13 - 4 * Real.sqrt 5 := by
    have h28δ_nn : 0 ≤ 28 * δ := by positivity
    have h_sq_lt : (28 * δ)^2 < (13 - 4 * Real.sqrt 5)^2 := by
      have h1 : (28 * δ)^2 = 784 * δ^2 := by ring
      rw [h1, hδsq]
      linarith [hV0_lt_max]
    have h_sqrt_lt : Real.sqrt ((28 * δ)^2) < Real.sqrt ((13 - 4 * Real.sqrt 5)^2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_lt
    have hL : Real.sqrt ((28 * δ)^2) = 28 * δ := Real.sqrt_sq h28δ_nn
    have hR : Real.sqrt ((13 - 4 * Real.sqrt 5)^2) = 13 - 4 * Real.sqrt 5 :=
      Real.sqrt_sq h_pos.le
    linarith [h_sqrt_lt, hL.le, hL.ge, hR.le, hR.ge]
  exact cf24_lyapunov_tendsto_zero_sharp x0 h_nn h_simplex hV0_pos
    δ hδ_nn hδ_lt hV_le

/-- **Saddle-stable exclusion is automatic in the sharp basin.**

For `V(x0) < (13 − 4√5)²/784`, the trajectory cannot ω-limit to
`saddlePoint`.  Therefore the saddle-stable hypothesis of
`Cf24SaddleExcludedBasinEntry` is automatically discharged for any sharp-basin start,
and the "real" obstruction to closing the unconditional case lives entirely
in the regime `V(x0) ≥ (13 − 4√5)²/784`. -/
theorem cf24_not_saddle_stable_of_sharp_init
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (hV0_pos : 0 < lyapunov x0)
    (hV0_sharp : lyapunov x0 < (13 - 4 * Real.sqrt 5)^2 / 784) :
    ¬ Filter.Tendsto
        (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t)
        Filter.atTop (nhds saddlePoint) := by
  intro h_tendsto
  have hly_cont : Continuous lyapunov := by
    unfold lyapunov
    exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
      |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
  have h_V_tendsto_saddle : Filter.Tendsto
      (fun t => lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t))
      Filter.atTop (nhds (lyapunov saddlePoint)) :=
    (hly_cont.tendsto _).comp h_tendsto
  have h_V_tendsto_zero := cf24_lyapunov_tendsto_zero_from_sharp_basin
    x0 h_nn h_simplex hV0_pos hV0_sharp
  have h_uniq := tendsto_nhds_unique h_V_tendsto_saddle h_V_tendsto_zero
  rw [lyapunov_saddlePoint] at h_uniq
  norm_num at h_uniq

/-! ### Corrected basin-entry hypothesis with saddle-stable exclusion

`Cf24BasinEntry` (above) is FALSE as stated: the saddle interior fixed point
is itself a counterexample (`cf24_basinEntry_false`).  Two changes salvage
the conditional Step 5 chain:

1. **Saddle-stable exclusion.**  Trajectories on the saddle's 1-D stable
   manifold (a measure-zero set in the 2-D simplex interior) are explicitly
   removed by the hypothesis that the trajectory does *not* tend to
   `saddlePoint` at infinity.

2. **Sharp threshold `(13 − 4√5)² / 784 ≈ 1/47.7`** in place of `1/512` —
   the largest sublevel set reachable by the V-sublevel parametric chain
   (sharp constant `28` from the squared cubic-remainder inequality
   `cubic_remainder_bound_sq`).  This is a `10.7×` larger basin to land in,
   correspondingly easier to discharge.

Formal closure of `Cf24SaddleExcludedBasinEntry` requires a stable-manifold theorem
(Mathlib gap, ~800–1500 lines) plus a Bendixson–Poincaré–style argument
ruling out non-fixed-point ω-limits (Mathlib gap, ~600–1200 lines).  The
conditional theorem `cf24_step5_readout_of_saddleExcludedBasinEntry` discharges *everything
downstream* of `Cf24SaddleExcludedBasinEntry`. -/
def Cf24SaddleExcludedBasinEntry : Prop :=
  ∀ (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1),
    0 < x0 0 → 0 < x0 1 → 0 < x0 2 →
    ¬ Filter.Tendsto
        (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t)
        Filter.atTop (nhds saddlePoint) →
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧
      0 < lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀) ∧
      lyapunov ((cf24_global_solution x0 h_nn h_simplex).trajectory t₀)
          < (13 - 4 * Real.sqrt 5)^2 / 784

/-- **Step 5 final (corrected) — readout convergence from interior init,
conditional on the corrected basin-entry hypothesis `Cf24SaddleExcludedBasinEntry`.**

Statement: assuming `Cf24SaddleExcludedBasinEntry`, for every non-negative simplex-interior
initial condition whose trajectory does not ω-limit to the saddle, the readout
`z_11 + z_01/2` along the global CRN trajectory converges to `(3 − √5)/6`.

Proof: plugs the entry time into the SHARP bridge
`cf24_readout_tendsto_from_sharp_lyapunov_init` rather than the `1/512`
bridge.  The saddle-exclusion hypothesis is forwarded verbatim from the
hypothesis to `Cf24SaddleExcludedBasinEntry`. -/
theorem cf24_step5_readout_of_saddleExcludedBasinEntry (h_basin' : Cf24SaddleExcludedBasinEntry)
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) (h_interior_1 : 0 < x0 1)
    (h_interior_2 : 0 < x0 2)
    (h_not_saddle_stable :
      ¬ Filter.Tendsto
          (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t)
          Filter.atTop (nhds saddlePoint)) :
    Filter.Tendsto
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 2
              + (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 / 2)
      Filter.atTop (nhds readoutLimit) := by
  obtain ⟨t₀, ht₀_nn, hV_pos, hV_sharp⟩ :=
    h_basin' x0 h_nn h_simplex h_interior_0 h_interior_1 h_interior_2
      h_not_saddle_stable
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  set y : ℝ → Fin 3 → ℝ := fun t => sol.trajectory (t + t₀) with hy_def
  -- HasDerivAt for the shifted trajectory.
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x := fun _ => rfl
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => y s) (field (y t)) t := by
    intro t ht
    have hsol_is := sol.is_solution (t + t₀) (by linarith)
    have hcomp : HasDerivAt (fun s => sol.trajectory (s + t₀))
        ((cf24PIVP x0).field (sol.trajectory (t + t₀))) t :=
      hsol_is.comp_add_const t t₀
    simpa [hy_def, hsol_field_eq] using hcomp
  have hx_deriv_b : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => y s 1) (field (y t) 1) (Set.Ici t) t := by
    intro t ht
    exact (hasDerivAt_pi.mp (hy_deriv t ht) 1).hasDerivWithinAt
  have hx_deriv_c : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s => y s 2) (field (y t) 2) (Set.Ici t) t := by
    intro t ht
    exact (hasDerivAt_pi.mp (hy_deriv t ht) 2).hasDerivWithinAt
  -- Lyapunov initial data after shift.
  have hV0_pos : 0 < lyapunov (y 0) := by
    change 0 < lyapunov (sol.trajectory (0 + t₀))
    rw [zero_add]; exact hV_pos
  have hV0_sharp : lyapunov (y 0) < (13 - 4 * Real.sqrt 5)^2 / 784 := by
    change lyapunov (sol.trajectory (0 + t₀)) < (13 - 4 * Real.sqrt 5)^2 / 784
    rw [zero_add]; exact hV_sharp
  -- Simplex preservation on [t₀, ∞) via conservation, transferred to `y`.
  have hx_simplex : ∀ t ∈ Set.Ici (0 : ℝ), y t 0 + y t 1 + y t 2 = 1 := by
    intro t ht
    have ht_nn : 0 ≤ t := ht
    have hsum_T : ∀ T : ℝ, 0 < T → ∀ s ∈ Set.Ico (0 : ℝ) T,
        ∑ i, sol.trajectory s i = ∑ i, sol.trajectory 0 i := by
      intro T hT
      have h_ode : ∀ u ∈ Set.Ico (0 : ℝ) T,
          HasDerivAt sol.trajectory (field (sol.trajectory u)) u := by
        intro u hu
        have := sol.is_solution u hu.1
        exact this
      exact conservative_local_sum_const field_conservative T hT sol.trajectory h_ode
    have h_sum_init : ∑ i, sol.trajectory 0 i = 1 := by
      rw [sol.init_cond]; exact h_simplex
    have h_sum_at : ∑ i, sol.trajectory (t + t₀) i = 1 := by
      have h_eq := hsum_T (t + t₀ + 1) (by linarith)
        (t + t₀) ⟨by linarith, by linarith⟩
      rw [h_eq]; exact h_sum_init
    simpa [Fin.sum_univ_three, hy_def] using h_sum_at
  -- Continuity of V ∘ y on [0, ∞).
  have hV_cont : ContinuousOn (fun t => lyapunov (y t)) (Set.Ici 0) := by
    intro t ht
    have hy_cont : ContinuousAt (fun s => y s) t := (hy_deriv t ht).continuousAt
    have hly_cont : Continuous lyapunov := by
      unfold lyapunov
      exact ((continuous_apply (1 : Fin 3)).sub continuous_const).pow 2
        |>.add (((continuous_apply (2 : Fin 3)).sub continuous_const).pow 2)
    exact (hly_cont.continuousAt.comp hy_cont).continuousWithinAt
  -- Apply the SHARP readout bridge to the shifted trajectory.
  have h_shifted :
      Filter.Tendsto (fun t => y t 2 + y t 1 / 2) Filter.atTop (nhds readoutLimit) :=
    cf24_readout_tendsto_from_sharp_lyapunov_init (x := y)
      hV0_pos hV0_sharp hV_cont hx_deriv_b hx_deriv_c hx_simplex
  -- Shift back: original trajectory equals shifted ∘ (· − t₀).
  have h_shift_back : Filter.Tendsto (fun t : ℝ => t - t₀) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ (-t₀) Filter.tendsto_id
  have h_eq :
      (fun t => sol.trajectory t 2 + sol.trajectory t 1 / 2) =
        (fun t => y t 2 + y t 1 / 2) ∘ (fun t => t - t₀) := by
    funext t
    simp [hy_def, sub_add_cancel]
  rw [h_eq]
  exact h_shifted.comp h_shift_back

/-- **λ-trick lift of corrected Step 5**, under the hypothesis `Cf24SaddleExcludedBasinEntry` and the saddle-stable
exclusion. -/
theorem cf24_lambda_lifted_readout_of_saddleExcludedBasinEntry (h_basin' : Cf24SaddleExcludedBasinEntry)
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) (h_interior_1 : 0 < x0 1)
    (h_interior_2 : 0 < x0 2)
    (h_not_saddle_stable :
      ¬ Filter.Tendsto
          (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t)
          Filter.atTop (nhds saddlePoint)) :
    Filter.Tendsto
      (fun t =>
        cf24LambdaEmbed ((cf24_global_solution x0 h_nn h_simplex).trajectory t) 3
        + cf24LambdaEmbed
            ((cf24_global_solution x0 h_nn h_simplex).trajectory t) 2 / 2)
      Filter.atTop (nhds readoutLimit) :=
  cf24Lambda_readout_tendsto
    (cf24_step5_readout_of_saddleExcludedBasinEntry h_basin' x0 h_nn h_simplex
      h_interior_0 h_interior_1 h_interior_2 h_not_saddle_stable)

/-- **Strict positivity of the z_00 coordinate along the CF'24 trajectory.**

Along any trajectory starting from a simplex-interior initial condition
(with `z_00(0) = x0 0 > 0`), we have `z_00(t) > 0` for all `t ≥ 0`.

Proof sketch.  The 0-th ODE component factors as
  `ż_00(t) = z_00(t) · g(t)`,  where  `g(t) := -2·z_00(t) + 7·z_01(t) - 2·z_11(t)`.
Suppose for contradiction there exists `t₁ ≥ 0` with `z_00(t₁) ≤ 0`.  Since
`z_00` is continuous and `z_00(0) > 0`, by IVT there is a first zero
`t* ∈ (0, t₁]`.  On `[0, t*]` the zero function `0 : ℝ → ℝ` and `z_00`
both satisfy the linear ODE `ẏ(s) = y(s) · g(s)` (for the first: `0 = 0·g(s)`;
for the second: `ż_00(s) = z_00(s) · g(s)` from the field formula).  Backward
ODE uniqueness (`ODE_solution_unique_of_mem_Icc_left`) from the matched terminal
value at `t*` then forces `z_00(0) = 0`, contradicting `z_00(0) = x0 0 > 0`.
-/
theorem cf24_traj_zero_strict_pos
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ∀ t, 0 ≤ t → 0 < (cf24_global_solution x0 h_nn h_simplex).trajectory t 0 := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  -- Name the 0-th coordinate and the continuous coefficient g(t).
  set z₀ : ℝ → ℝ := fun t => sol.trajectory t 0 with hz₀_def
  set g : ℝ → ℝ := fun t =>
    -2 * sol.trajectory t 0 + 7 * sol.trajectory t 1 - 2 * sol.trajectory t 2 with hg_def
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x := fun _ => rfl
  -- HasDerivAt for the full trajectory at each t ≥ 0.
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht
    have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  -- Continuity of each coordinate on Set.Ici 0.
  have hz_cont : ∀ i, ContinuousOn (fun t => sol.trajectory t i) (Set.Ici (0 : ℝ)) := by
    intro i t ht
    have h_pi := (hasDerivAt_pi.mp (hy_deriv t ht) i).continuousAt
    exact h_pi.continuousWithinAt
  have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    have h0 : ContinuousOn (fun t => -2 * sol.trajectory t 0) (Set.Ici (0 : ℝ)) :=
      (continuousOn_const (c := (-2 : ℝ))).mul (hz_cont 0)
    have h1 : ContinuousOn (fun t => 7 * sol.trajectory t 1) (Set.Ici (0 : ℝ)) :=
      (continuousOn_const (c := (7 : ℝ))).mul (hz_cont 1)
    have h2 : ContinuousOn (fun t => 2 * sol.trajectory t 2) (Set.Ici (0 : ℝ)) :=
      (continuousOn_const (c := (2 : ℝ))).mul (hz_cont 2)
    exact (h0.add h1).sub h2
  -- HasDerivAt for z₀ at each t ≥ 0, with derivative z₀(t) · g(t).
  have hz₀_deriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt z₀ (z₀ t * g t) t := by
    intro t ht
    have hpi := hasDerivAt_pi.mp (hy_deriv t ht) 0
    -- field (sol.trajectory t) 0 = z₀(t) * g(t).
    have hfield_eq : field (sol.trajectory t) 0 = z₀ t * g t := by
      simp [field, hz₀_def, hg_def]; ring
    rw [← hfield_eq]
    exact hpi
  -- Continuity of z₀ on Ici 0.
  have hz₀_cont : ContinuousOn z₀ (Set.Ici (0 : ℝ)) := hz_cont 0
  -- The initial value is strictly positive.
  have hz₀_init : z₀ 0 = x0 0 := by
    change sol.trajectory 0 0 = x0 0
    have : sol.trajectory 0 = (cf24PIVP x0).init := sol.init_cond
    rw [this]
    rfl
  -- Main claim by contradiction: assume some t with 0 ≤ t and z₀ t ≤ 0.
  -- Show z₀(t) > 0 for all t ≥ 0.
  intro t ht
  by_contra hle
  push_neg at hle
  -- hle : z₀ t ≤ 0.  Combined with z₀(0) = x0 0 > 0 and continuity on [0,t],
  -- IVT gives a zero in (0, t].
  have hz₀0_pos : 0 < z₀ 0 := by rw [hz₀_init]; exact h_interior_0
  have ht_pos : 0 < t := by
    rcases eq_or_lt_of_le ht with rfl | ht_pos
    · linarith [hle, hz₀0_pos]
    · exact ht_pos
  -- Apply IVT on [0, t] to get t* ∈ [0, t] with z₀ t* = 0.
  have hz₀_contOn_Icc : ContinuousOn z₀ (Set.Icc 0 t) :=
    hz₀_cont.mono (fun s hs => hs.1)
  obtain ⟨t_star, ht_star_mem, hz₀_t_star⟩ :=
    intermediate_value_Icc' ht hz₀_contOn_Icc
      (show (0 : ℝ) ∈ Set.Icc (z₀ t) (z₀ 0) from ⟨hle, hz₀0_pos.le⟩)
  -- `t_star` cannot be 0 (since z₀ 0 > 0 ≠ 0).
  have ht_star_pos : 0 < t_star := by
    rcases eq_or_lt_of_le ht_star_mem.1 with h0 | hpos
    · exfalso
      rw [← h0] at hz₀_t_star
      linarith [hz₀_t_star, hz₀0_pos]
    · exact hpos
  have ht_star_nn : 0 ≤ t_star := ht_star_mem.1
  -- Now apply backward ODE uniqueness on Icc 0 t_star.
  -- Work with the family v t y := y * g t (independent of parameter t for z).
  set v : ℝ → ℝ → ℝ := fun τ y => y * g τ with hv_def
  -- Both z₀ and the zero function solve ẏ = v(τ, y) on Icc 0 t_star.
  -- Bound |g| uniformly on Icc 0 t_star: ContinuousOn + compact ⇒ bounded.
  have hg_contOn_Icc : ContinuousOn g (Set.Icc 0 t_star) :=
    hg_cont.mono (fun s hs => hs.1)
  have h_compact : IsCompact (Set.Icc (0 : ℝ) t_star) := isCompact_Icc
  obtain ⟨M, hM_bound⟩ : ∃ M, ∀ τ ∈ Set.Icc (0 : ℝ) t_star, |g τ| ≤ M := by
    have h_cont_abs : ContinuousOn (fun τ => |g τ|) (Set.Icc 0 t_star) :=
      hg_contOn_Icc.abs
    obtain ⟨M, hM⟩ :=
      h_compact.bddAbove_image h_cont_abs
    refine ⟨M, fun τ hτ => ?_⟩
    exact hM ⟨τ, hτ, rfl⟩
  -- Lipschitz constant for v τ: K := max M 0, treated as NNReal.
  have hM_nn : 0 ≤ M := by
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t_star := ⟨le_refl _, ht_star_nn⟩
    exact le_trans (abs_nonneg _) (hM_bound 0 h0mem)
  set K : NNReal := ⟨M, hM_nn⟩ with hK_def
  -- v τ is Lipschitz in y with constant K on τ ∈ Icc 0 t_star.
  have hv_lip : ∀ τ ∈ Set.Ioc (0 : ℝ) t_star,
      LipschitzOnWith K (v τ) Set.univ := by
    intro τ hτ
    have hτ_mem : τ ∈ Set.Icc (0 : ℝ) t_star := ⟨hτ.1.le, hτ.2⟩
    have hMτ : |g τ| ≤ M := hM_bound τ hτ_mem
    -- Reduce to LipschitzWith via `.lipschitzOnWith`.
    apply LipschitzWith.lipschitzOnWith
    -- Use `of_dist_le_mul`: dist (v τ y₁) (v τ y₂) ≤ K * dist y₁ y₂.
    apply LipschitzWith.of_dist_le_mul
    intro y₁ y₂
    change dist (y₁ * g τ) (y₂ * g τ) ≤ (K : ℝ) * dist y₁ y₂
    have hKM : (K : ℝ) = M := by rw [hK_def]; rfl
    rw [hKM, Real.dist_eq, Real.dist_eq, ← sub_mul, abs_mul, mul_comm M _]
    exact mul_le_mul_of_nonneg_left hMτ (abs_nonneg _)
  -- Continuity of z₀ and const 0 on Icc 0 t_star.
  have hz₀_contOn : ContinuousOn z₀ (Set.Icc 0 t_star) :=
    hz₀_cont.mono (fun s hs => hs.1)
  have h0_contOn : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 t_star) :=
    continuousOn_const
  -- HasDerivWithinAt (Iic τ) τ for z₀ and 0 on Ioc 0 t_star.
  have hz₀_hd : ∀ τ ∈ Set.Ioc (0 : ℝ) t_star,
      HasDerivWithinAt z₀ (v τ (z₀ τ)) (Set.Iic τ) τ := by
    intro τ hτ
    have h := hz₀_deriv τ hτ.1.le
    have : HasDerivWithinAt z₀ (z₀ τ * g τ) (Set.Iic τ) τ := h.hasDerivWithinAt
    exact this
  have h0_hd : ∀ τ ∈ Set.Ioc (0 : ℝ) t_star,
      HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (v τ ((fun _ : ℝ => (0 : ℝ)) τ))
        (Set.Iic τ) τ := by
    intro τ _
    simp only [v, zero_mul]
    exact (hasDerivWithinAt_const τ _ 0)
  -- Apply ODE_solution_unique_of_mem_Icc_left with s = univ (trivial).
  have h_univ : ∀ τ ∈ Set.Ioc (0 : ℝ) t_star, (z₀ τ : ℝ) ∈ (Set.univ : Set ℝ) := fun _ _ => trivial
  have h_univ0 : ∀ τ ∈ Set.Ioc (0 : ℝ) t_star, ((0 : ℝ) : ℝ) ∈ (Set.univ : Set ℝ) :=
    fun _ _ => trivial
  have h_eq_at_tstar : z₀ t_star = (fun _ : ℝ => (0 : ℝ)) t_star := by
    simp [hz₀_t_star]
  have h_eqOn :=
    ODE_solution_unique_of_mem_Icc_left (v := v) (s := fun _ => Set.univ)
      (K := K) hv_lip hz₀_contOn hz₀_hd h_univ h0_contOn h0_hd h_univ0 h_eq_at_tstar
  -- Evaluate at 0: z₀ 0 = 0.
  have h_zero_at0 : z₀ 0 = 0 :=
    h_eqOn ⟨le_refl _, ht_star_nn⟩
  -- Contradict positivity at 0.
  rw [hz₀_init] at h_zero_at0
  linarith [h_interior_0]

/-- **Strict positivity of the z_01 coordinate along the CF'24 trajectory.**

Along any trajectory starting from a simplex-interior initial condition
(with `z_01(0) = x0 1 > 0`), we have `z_01(t) > 0` for all `t ≥ 0`.

Proof sketch.  The 1-st ODE component decomposes as
  `ż_01(t) = σ_1(t) - z_01(t) · μ_1(t)`,
where `σ_1(t) := 2 z_00(t)² + 16 z_00(t) z_11(t) ≥ 2 z_00(t)² > 0` and
`μ_1(t) := 8 z_00(t) + z_11(t) ≥ 0`.

If `z_01(t₁) ≤ 0` for some `t₁ ≥ 0`, take
`t* := sInf {s ∈ Icc 0 t₁ | z_01(s) ≤ 0}`.  By continuity and closedness,
`z_01(t*) ≤ 0`; on `[0, t*)` we have `z_01 > 0`.  At `t*`, the field
gives `ż_01(t*) ≥ σ_1(t*) > 0`.  But the slope
`(z_01(t* + h) − z_01(t*)) / h` for `h ∈ 𝓝[<] 0` is non-positive
(non-negative numerator over negative denominator).  By
`HasDerivAt.tendsto_slope_zero_left` the limit equals `ż_01(t*)`,
forcing it ≤ 0.  Contradiction. -/
theorem cf24_traj_one_strict_pos
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0)
    (h_interior_1 : 0 < x0 1) :
    ∀ t, 0 ≤ t → 0 < (cf24_global_solution x0 h_nn h_simplex).trajectory t 1 := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  set z₁ : ℝ → ℝ := fun t => sol.trajectory t 1 with hz₁_def
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x := fun _ => rfl
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht
    have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hz_cont : ∀ i, ContinuousOn (fun t => sol.trajectory t i) (Set.Ici (0 : ℝ)) := by
    intro i t ht
    have h_pi := (hasDerivAt_pi.mp (hy_deriv t ht) i).continuousAt
    exact h_pi.continuousWithinAt
  have hz₁_deriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt z₁ (field (sol.trajectory t) 1) t := by
    intro t ht
    exact hasDerivAt_pi.mp (hy_deriv t ht) 1
  have hz₁_cont : ContinuousOn z₁ (Set.Ici (0 : ℝ)) := hz_cont 1
  have hz₁_init : z₁ 0 = x0 1 := by
    change sol.trajectory 0 1 = x0 1
    have : sol.trajectory 0 = (cf24PIVP x0).init := sol.init_cond
    rw [this]; rfl
  have h_nn_traj : ∀ s, 0 ≤ s → ∀ i, 0 ≤ sol.trajectory s i := by
    intro s hs i
    exact pivp_solution_nonneg (P := cf24PIVP x0)
      cf24_isCRNImplementable field_locally_lipschitz
      (by intro j; simpa [cf24PIVP] using h_nn j)
      sol s hs i
  have hz0_pos : ∀ s, 0 ≤ s → 0 < sol.trajectory s 0 :=
    cf24_traj_zero_strict_pos h_nn h_simplex h_interior_0
  intro t ht
  by_contra hle
  push_neg at hle
  have hz₁0_pos : 0 < z₁ 0 := by rw [hz₁_init]; exact h_interior_1
  have ht_pos : 0 < t := by
    rcases eq_or_lt_of_le ht with rfl | ht_pos
    · linarith [hle, hz₁0_pos]
    · exact ht_pos
  set S : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) t ∧ z₁ s ≤ 0} with hS_def
  have hS_nonempty : S.Nonempty := ⟨t, ⟨ht, le_refl _⟩, hle⟩
  have hS_bddBelow : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  set t_star : ℝ := sInf S with ht_star_def
  have ht_star_nn : 0 ≤ t_star :=
    le_csInf hS_nonempty (fun s hs => hs.1.1)
  have ht_star_le_t : t_star ≤ t := by
    rcases hS_nonempty with ⟨s, hs⟩
    exact le_trans (csInf_le hS_bddBelow hs) hs.1.2
  have hz₁_pos_below : ∀ s, 0 ≤ s → s < t_star → 0 < z₁ s := by
    intro s hs_nn hs_lt
    by_contra hle_s
    push_neg at hle_s
    have hsS : s ∈ S := ⟨⟨hs_nn, le_trans hs_lt.le ht_star_le_t⟩, hle_s⟩
    have : t_star ≤ s := csInf_le hS_bddBelow hsS
    linarith
  have hz₁_t_star_le : z₁ t_star ≤ 0 := by
    have hclosed_le : IsClosed {y : ℝ | z₁ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t} := by
      have hS_eq : {y : ℝ | z₁ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t}
          = (z₁ ⁻¹' Set.Iic 0) ∩ Set.Icc (0:ℝ) t := by
        ext y; simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, and_comm]
      have hcontIcc : ContinuousOn z₁ (Set.Icc (0:ℝ) t) :=
        hz₁_cont.mono (fun s hs => hs.1)
      rw [hS_eq]
      have hclosed_Icc : IsClosed (Set.Icc (0:ℝ) t) := isClosed_Icc
      have hpreim : IsClosed ((z₁ ⁻¹' Set.Iic 0) ∩ Set.Icc (0:ℝ) t) := by
        have h1 : IsClosed (Set.Icc (0:ℝ) t ∩ z₁ ⁻¹' Set.Iic 0) :=
          hcontIcc.preimage_isClosed_of_isClosed hclosed_Icc isClosed_Iic
        rw [Set.inter_comm] at h1
        exact h1
      exact hpreim
    have ht_star_mem_closure : t_star ∈ closure S :=
      csInf_mem_closure hS_nonempty hS_bddBelow
    have hS_subset : S ⊆ {y : ℝ | z₁ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t} := by
      intro y hy; exact ⟨hy.2, hy.1⟩
    have ht_star_in_closure :
        t_star ∈ closure {y : ℝ | z₁ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t} :=
      closure_mono hS_subset ht_star_mem_closure
    have ht_star_mem_closed : t_star ∈ {y : ℝ | z₁ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t} :=
      hclosed_le.closure_eq.symm ▸ ht_star_in_closure
    exact ht_star_mem_closed.1
  have ht_star_pos : 0 < t_star := by
    rcases eq_or_lt_of_le ht_star_nn with h0 | hpos
    · exfalso
      rw [← h0] at hz₁_t_star_le
      linarith [hz₁0_pos]
    · exact hpos
  have h_field_one : field (sol.trajectory t_star) 1
      = 2 * (sol.trajectory t_star 0)^2
        + 16 * sol.trajectory t_star 0 * sol.trajectory t_star 2
        - z₁ t_star * (8 * sol.trajectory t_star 0 + sol.trajectory t_star 2) := by
    simp only [field, hz₁_def, sq]
    ring
  have hz0_t_star_pos : 0 < sol.trajectory t_star 0 := hz0_pos t_star ht_star_nn
  have hz2_t_star_nn : 0 ≤ sol.trajectory t_star 2 := h_nn_traj t_star ht_star_nn 2
  have hsigma_pos : 0 < 2 * (sol.trajectory t_star 0)^2
      + 16 * sol.trajectory t_star 0 * sol.trajectory t_star 2 := by
    have h1 : 0 < 2 * (sol.trajectory t_star 0)^2 := by positivity
    have h2 : 0 ≤ 16 * sol.trajectory t_star 0 * sol.trajectory t_star 2 := by positivity
    linarith
  have hmu_nn : 0 ≤ 8 * sol.trajectory t_star 0 + sol.trajectory t_star 2 := by
    have := hz0_t_star_pos.le
    linarith
  have h_neg_term :
      0 ≤ -(z₁ t_star * (8 * sol.trajectory t_star 0 + sol.trajectory t_star 2)) := by
    have hprod_le : z₁ t_star * (8 * sol.trajectory t_star 0 + sol.trajectory t_star 2)
        ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hz₁_t_star_le hmu_nn
    linarith
  have h_deriv_pos : 0 < field (sol.trajectory t_star) 1 := by
    rw [h_field_one]; linarith
  have hz₁_hd_at_tstar : HasDerivAt z₁ (field (sol.trajectory t_star) 1) t_star :=
    hz₁_deriv t_star ht_star_nn
  have h_slope_lim : Filter.Tendsto (fun h : ℝ => h⁻¹ * (z₁ (t_star + h) - z₁ t_star))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (field (sol.trajectory t_star) 1)) := by
    have hraw := hz₁_hd_at_tstar.tendsto_slope_zero_left
    simpa [smul_eq_mul] using hraw
  have h_eventually : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Iio 0),
      h⁻¹ * (z₁ (t_star + h) - z₁ t_star) ≤ 0 := by
    -- Eventually h ∈ Ioo (-t_star) 0 along 𝓝[<] 0.
    have h_open_nbhd : Set.Ioi (-t_star) ∈ nhds (0 : ℝ) :=
      Ioi_mem_nhds (by linarith : -t_star < 0)
    have hmem : Set.Ioi (-t_star) ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) :=
      mem_nhdsWithin_of_mem_nhds h_open_nbhd
    filter_upwards [hmem, self_mem_nhdsWithin] with h hh_lower hh_neg_set
    have hh_neg : h < 0 := hh_neg_set
    have hh_lower' : -t_star < h := hh_lower
    have hts_h_nn : 0 ≤ t_star + h := by linarith
    have hts_h_lt : t_star + h < t_star := by linarith
    have hz₁_pos_at : 0 < z₁ (t_star + h) := hz₁_pos_below _ hts_h_nn hts_h_lt
    have hnum_nn : 0 ≤ z₁ (t_star + h) - z₁ t_star := by linarith
    have hh_inv_nonpos : h⁻¹ ≤ 0 := inv_nonpos.mpr hh_neg.le
    nlinarith [hh_inv_nonpos, hnum_nn]
  -- Pass to the limit (NeBot is auto-instance for NoMinOrder ℝ).
  have hderiv_le : field (sol.trajectory t_star) 1 ≤ 0 :=
    le_of_tendsto h_slope_lim h_eventually
  linarith

/-- **Strict positivity of the z_11 coordinate along the CF'24 trajectory.**

Same slope-bound contradiction as `cf24_traj_one_strict_pos`, with the
following twist: the field at the first zero `t*` factors as
`ż_11 = z_00 z_01 + z_11 · (z_01 - 14 z_00)`.  The second term has
indeterminate sign, so we improve `z_11(t*) ≤ 0` to `z_11(t*) = 0` using
continuity from below (since `z_11 > 0` on `[0, t*)`).  Then
`ż_11(t*) = z_00(t*) · z_01(t*) > 0` by `cf24_traj_zero_strict_pos` and
`cf24_traj_one_strict_pos`. -/
theorem cf24_traj_two_strict_pos
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) (h_interior_1 : 0 < x0 1)
    (h_interior_2 : 0 < x0 2) :
    ∀ t, 0 ≤ t → 0 < (cf24_global_solution x0 h_nn h_simplex).trajectory t 2 := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  set z₂ : ℝ → ℝ := fun t => sol.trajectory t 2 with hz₂_def
  have hsol_field_eq : ∀ x : Fin 3 → ℝ, (cf24PIVP x0).field x = field x := fun _ => rfl
  have hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => sol.trajectory s) (field (sol.trajectory t)) t := by
    intro t ht
    have := sol.is_solution t ht
    simpa [hsol_field_eq] using this
  have hz_cont : ∀ i, ContinuousOn (fun t => sol.trajectory t i) (Set.Ici (0 : ℝ)) := by
    intro i t ht
    have h_pi := (hasDerivAt_pi.mp (hy_deriv t ht) i).continuousAt
    exact h_pi.continuousWithinAt
  have hz₂_deriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt z₂ (field (sol.trajectory t) 2) t := by
    intro t ht
    exact hasDerivAt_pi.mp (hy_deriv t ht) 2
  have hz₂_cont : ContinuousOn z₂ (Set.Ici (0 : ℝ)) := hz_cont 2
  have hz₂_init : z₂ 0 = x0 2 := by
    change sol.trajectory 0 2 = x0 2
    have : sol.trajectory 0 = (cf24PIVP x0).init := sol.init_cond
    rw [this]; rfl
  have hz0_pos : ∀ s, 0 ≤ s → 0 < sol.trajectory s 0 :=
    cf24_traj_zero_strict_pos h_nn h_simplex h_interior_0
  have hz1_pos : ∀ s, 0 ≤ s → 0 < sol.trajectory s 1 :=
    cf24_traj_one_strict_pos h_nn h_simplex h_interior_0 h_interior_1
  intro t ht
  by_contra hle
  push_neg at hle
  have hz₂0_pos : 0 < z₂ 0 := by rw [hz₂_init]; exact h_interior_2
  have ht_pos : 0 < t := by
    rcases eq_or_lt_of_le ht with rfl | ht_pos
    · linarith [hle, hz₂0_pos]
    · exact ht_pos
  set S : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) t ∧ z₂ s ≤ 0} with hS_def
  have hS_nonempty : S.Nonempty := ⟨t, ⟨ht, le_refl _⟩, hle⟩
  have hS_bddBelow : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  set t_star : ℝ := sInf S with ht_star_def
  have ht_star_nn : 0 ≤ t_star :=
    le_csInf hS_nonempty (fun s hs => hs.1.1)
  have ht_star_le_t : t_star ≤ t := by
    rcases hS_nonempty with ⟨s, hs⟩
    exact le_trans (csInf_le hS_bddBelow hs) hs.1.2
  have hz₂_pos_below : ∀ s, 0 ≤ s → s < t_star → 0 < z₂ s := by
    intro s hs_nn hs_lt
    by_contra hle_s
    push_neg at hle_s
    have hsS : s ∈ S := ⟨⟨hs_nn, le_trans hs_lt.le ht_star_le_t⟩, hle_s⟩
    have : t_star ≤ s := csInf_le hS_bddBelow hsS
    linarith
  have hz₂_t_star_le : z₂ t_star ≤ 0 := by
    have hclosed_le : IsClosed {y : ℝ | z₂ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t} := by
      have hS_eq : {y : ℝ | z₂ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t}
          = (z₂ ⁻¹' Set.Iic 0) ∩ Set.Icc (0:ℝ) t := by
        ext y; simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, and_comm]
      have hcontIcc : ContinuousOn z₂ (Set.Icc (0:ℝ) t) :=
        hz₂_cont.mono (fun s hs => hs.1)
      rw [hS_eq]
      have hclosed_Icc : IsClosed (Set.Icc (0:ℝ) t) := isClosed_Icc
      have hpreim : IsClosed ((z₂ ⁻¹' Set.Iic 0) ∩ Set.Icc (0:ℝ) t) := by
        have h1 : IsClosed (Set.Icc (0:ℝ) t ∩ z₂ ⁻¹' Set.Iic 0) :=
          hcontIcc.preimage_isClosed_of_isClosed hclosed_Icc isClosed_Iic
        rw [Set.inter_comm] at h1
        exact h1
      exact hpreim
    have ht_star_mem_closure : t_star ∈ closure S :=
      csInf_mem_closure hS_nonempty hS_bddBelow
    have hS_subset : S ⊆ {y : ℝ | z₂ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t} := by
      intro y hy; exact ⟨hy.2, hy.1⟩
    have ht_star_in_closure :
        t_star ∈ closure {y : ℝ | z₂ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t} :=
      closure_mono hS_subset ht_star_mem_closure
    have ht_star_mem_closed : t_star ∈ {y : ℝ | z₂ y ≤ 0 ∧ y ∈ Set.Icc (0:ℝ) t} :=
      hclosed_le.closure_eq.symm ▸ ht_star_in_closure
    exact ht_star_mem_closed.1
  have ht_star_pos : 0 < t_star := by
    rcases eq_or_lt_of_le ht_star_nn with h0 | hpos
    · exfalso
      rw [← h0] at hz₂_t_star_le
      linarith [hz₂0_pos]
    · exact hpos
  -- Strengthen z₂(t_star) ≤ 0 to z₂(t_star) = 0 via continuity from below.
  have hz₂_t_star_ge : 0 ≤ z₂ t_star := by
    have hcont_at : ContinuousWithinAt z₂ (Set.Ici (0:ℝ)) t_star := hz₂_cont _ ht_star_nn
    -- Sequence t_star - 1/(n+1) → t_star with values in [0, t_star).
    have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop
        (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have htends : Filter.Tendsto (fun n : ℕ => t_star - 1 / ((n : ℝ) + 1)) Filter.atTop
        (nhds t_star) := by
      have h2 : Filter.Tendsto (fun n : ℕ => t_star - 1 / ((n : ℝ) + 1)) Filter.atTop
          (nhds (t_star - 0)) :=
        (tendsto_const_nhds (x := t_star)).sub h_inv_tendsto
      simpa using h2
    have heventually : ∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ t_star - 1 / ((n : ℝ) + 1) ∧ t_star - 1 / ((n : ℝ) + 1) < t_star := by
      have h_lt : ∀ᶠ n : ℕ in Filter.atTop, (1 / ((n : ℝ) + 1)) < t_star :=
        h_inv_tendsto.eventually (eventually_lt_nhds ht_star_pos)
      filter_upwards [h_lt] with n hn
      have hpos_inv : 0 < (1 / ((n : ℝ) + 1)) := by positivity
      refine ⟨?_, ?_⟩ <;> linarith
    have hpos_seq : ∀ᶠ n : ℕ in Filter.atTop, 0 < z₂ (t_star - 1 / ((n : ℝ) + 1)) := by
      filter_upwards [heventually] with n hn
      exact hz₂_pos_below _ hn.1 hn.2
    have htends_in : Filter.Tendsto (fun n : ℕ => t_star - 1 / ((n : ℝ) + 1)) Filter.atTop
        (nhdsWithin t_star (Set.Ici (0:ℝ))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨htends, ?_⟩
      filter_upwards [heventually] with n hn using hn.1
    have hz₂_seq : Filter.Tendsto (fun n : ℕ => z₂ (t_star - 1 / ((n : ℝ) + 1))) Filter.atTop
        (nhds (z₂ t_star)) := hcont_at.tendsto.comp htends_in
    exact ge_of_tendsto hz₂_seq (by filter_upwards [hpos_seq] with n hn using hn.le)
  have hz₂_t_star_eq : z₂ t_star = 0 := le_antisymm hz₂_t_star_le hz₂_t_star_ge
  have h_field_two : field (sol.trajectory t_star) 2
      = sol.trajectory t_star 0 * sol.trajectory t_star 1
        + z₂ t_star * (sol.trajectory t_star 1 - 14 * sol.trajectory t_star 0) := by
    simp only [field, hz₂_def]
    ring
  have hz0_t_star_pos : 0 < sol.trajectory t_star 0 := hz0_pos t_star ht_star_nn
  have hz1_t_star_pos : 0 < sol.trajectory t_star 1 := hz1_pos t_star ht_star_nn
  have h_source_pos : 0 < sol.trajectory t_star 0 * sol.trajectory t_star 1 :=
    mul_pos hz0_t_star_pos hz1_t_star_pos
  have h_deriv_pos : 0 < field (sol.trajectory t_star) 2 := by
    rw [h_field_two, hz₂_t_star_eq]
    simpa using h_source_pos
  have hz₂_hd_at_tstar : HasDerivAt z₂ (field (sol.trajectory t_star) 2) t_star :=
    hz₂_deriv t_star ht_star_nn
  have h_slope_lim : Filter.Tendsto (fun h : ℝ => h⁻¹ * (z₂ (t_star + h) - z₂ t_star))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (field (sol.trajectory t_star) 2)) := by
    have hraw := hz₂_hd_at_tstar.tendsto_slope_zero_left
    simpa [smul_eq_mul] using hraw
  have h_eventually : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Iio 0),
      h⁻¹ * (z₂ (t_star + h) - z₂ t_star) ≤ 0 := by
    have h_open_nbhd : Set.Ioi (-t_star) ∈ nhds (0 : ℝ) :=
      Ioi_mem_nhds (by linarith : -t_star < 0)
    have hmem : Set.Ioi (-t_star) ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) :=
      mem_nhdsWithin_of_mem_nhds h_open_nbhd
    filter_upwards [hmem, self_mem_nhdsWithin] with h hh_lower hh_neg_set
    have hh_neg : h < 0 := hh_neg_set
    have hh_lower' : -t_star < h := hh_lower
    have hts_h_nn : 0 ≤ t_star + h := by linarith
    have hts_h_lt : t_star + h < t_star := by linarith
    have hz₂_pos_at : 0 < z₂ (t_star + h) := hz₂_pos_below _ hts_h_nn hts_h_lt
    have hnum_nn : 0 ≤ z₂ (t_star + h) - z₂ t_star := by linarith
    have hh_inv_nonpos : h⁻¹ ≤ 0 := inv_nonpos.mpr hh_neg.le
    nlinarith [hh_inv_nonpos, hnum_nn]
  have hderiv_le : field (sol.trajectory t_star) 2 ≤ 0 :=
    le_of_tendsto h_slope_lim h_eventually
  linarith

/-- **Simplex-interior invariance of the CF'24 trajectory.** -/
theorem cf24_traj_simplex_interior
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) (h_interior_1 : 0 < x0 1)
    (h_interior_2 : 0 < x0 2) :
    ∀ t, 0 ≤ t → ∀ i,
      0 < (cf24_global_solution x0 h_nn h_simplex).trajectory t i := by
  intro t ht i
  fin_cases i
  · exact cf24_traj_zero_strict_pos h_nn h_simplex h_interior_0 t ht
  · exact cf24_traj_one_strict_pos h_nn h_simplex h_interior_0 h_interior_1 t ht
  · exact cf24_traj_two_strict_pos h_nn h_simplex h_interior_0 h_interior_1
      h_interior_2 t ht

/-! ### σ integral scaffolding for `Cf24R2Reparam` discharge

We now construct the r²-trick time reparametrization `σ(t) = ∫₀ᵗ 4/(z(u) 0)² du`
(with `z = cf24_global_solution.trajectory`) and prove the properties needed
for `Cf24R2Reparam`: `σ` is continuous and strictly increasing on `[0,∞)`,
`σ(0) = 0`, `σ(t) ≥ 4·t`, and therefore `σ → ∞`.

The factor `4` comes from the λ-trick map `u = z_00 / 2` so that
`1/(z_00/2)² = 4/z_00²`. -/

/-- **Simplex upper bound on the z_00 coordinate.**  Along the CF'24
trajectory, `z_00(t) ≤ 1` for all `t ≥ 0`, since the three components sum
to 1 and the other two are non-negative. -/
theorem cf24_traj_zero_le_one
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1) :
    ∀ t, 0 ≤ t → (cf24_global_solution x0 h_nn h_simplex).trajectory t 0 ≤ 1 := by
  intro t ht
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  -- Simplex conservation on the full trajectory.
  have hSum : ∑ i, sol.trajectory t i = 1 := by
    have h_cons' : ∀ x, ∑ i, (cf24PIVP x0).field x i = 0 := by
      intro x; exact field_conservative x
    have h_init' : ∑ i, (cf24PIVP x0).init i = 1 := by
      simpa [cf24PIVP] using h_simplex
    exact conservative_trajectory_simplex sol h_cons' h_init' ht
  -- Non-negativity of each coordinate.
  have h_nn_traj : ∀ i, 0 ≤ sol.trajectory t i := by
    intro i
    exact pivp_solution_nonneg (P := cf24PIVP x0)
      cf24_isCRNImplementable field_locally_lipschitz
      (by intro j; simpa [cf24PIVP] using h_nn j)
      sol t ht i
  have h3 :
      sol.trajectory t 0 + sol.trajectory t 1 + sol.trajectory t 2 = 1 := by
    simpa [Fin.sum_univ_three] using hSum
  have h1_nn : 0 ≤ sol.trajectory t 1 := h_nn_traj 1
  have h2_nn : 0 ≤ sol.trajectory t 2 := h_nn_traj 2
  linarith

/-- **σ** — the r²-trick time reparametrization, defined as the
integral of `4/(z(u) 0)²` from 0 to t along the CF'24 orbit. -/
noncomputable def cf24_sigma
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1) :
    ℝ → ℝ :=
  fun t => ∫ u in (0 : ℝ)..t,
    4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2

/-- `σ(0) = 0`. -/
theorem cf24_sigma_zero
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1) :
    cf24_sigma x0 h_nn h_simplex 0 = 0 := by
  unfold cf24_sigma
  exact intervalIntegral.integral_same

/-- Continuity of the `z_00` coordinate on `[0, ∞)`. -/
private theorem cf24_traj_zero_contOn
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1) :
    ContinuousOn
      (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t 0)
      (Set.Ici (0 : ℝ)) := by
  set sol := cf24_global_solution x0 h_nn h_simplex
  intro t ht
  have h_sol := sol.is_solution t ht
  have h_pi := (hasDerivAt_pi.mp h_sol 0).continuousAt
  exact h_pi.continuousWithinAt

/-- Continuity of the integrand `4/(z(u) 0)²` on `[0, ∞)`, given strict
positivity of `z(u) 0`. -/
private theorem cf24_integrand_contOn
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ContinuousOn
      (fun u => 4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2)
      (Set.Ici (0 : ℝ)) := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  have h_traj_cont := cf24_traj_zero_contOn h_nn h_simplex
  have h_pos : ∀ u ∈ Set.Ici (0 : ℝ), sol.trajectory u 0 ≠ 0 := by
    intro u hu
    have : 0 < sol.trajectory u 0 :=
      cf24_traj_zero_strict_pos h_nn h_simplex h_interior_0 u hu
    exact ne_of_gt this
  have h_sq_ne : ∀ u ∈ Set.Ici (0 : ℝ), (sol.trajectory u 0)^2 ≠ 0 := by
    intro u hu
    exact pow_ne_zero 2 (h_pos u hu)
  have h_sq_cont : ContinuousOn
      (fun u => (sol.trajectory u 0)^2) (Set.Ici (0 : ℝ)) :=
    h_traj_cont.pow 2
  exact (continuousOn_const).div h_sq_cont h_sq_ne

/-- On any subinterval `[a,b] ⊆ [0,∞)`, the integrand is bounded away from
the singularity and hence interval-integrable. -/
private theorem cf24_integrand_intervalIntegrable
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun u => 4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2)
      MeasureTheory.volume a b := by
  have h_cont := cf24_integrand_contOn h_nn h_simplex h_interior_0
  have h_sub : Set.Icc a b ⊆ Set.Ici (0 : ℝ) := fun x hx => le_trans ha hx.1
  have h_on_Icc : ContinuousOn
      (fun u => 4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2)
      (Set.Icc a b) :=
    h_cont.mono h_sub
  exact h_on_Icc.intervalIntegrable_of_Icc hab

/-- Positivity of the integrand on `[0, ∞)`. -/
private theorem cf24_integrand_pos
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ∀ u, 0 ≤ u →
      0 < 4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2 := by
  intro u hu
  have h_pos : 0 < (cf24_global_solution x0 h_nn h_simplex).trajectory u 0 :=
    cf24_traj_zero_strict_pos h_nn h_simplex h_interior_0 u hu
  have h_sq_pos : 0 < ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2 :=
    pow_pos h_pos 2
  positivity

/-- **σ is strictly monotone on `[0, ∞)`.**  Along any strictly-positive
`z_00`-orbit, the integral `σ` grows strictly. -/
theorem cf24_sigma_strictMonoOn
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    StrictMonoOn (cf24_sigma x0 h_nn h_simplex) (Set.Ici 0) := by
  intro a ha b hb hab
  -- σ b - σ a = ∫_a^b integrand; integrand positive & continuous ⇒ integral > 0.
  have ha0 : (0 : ℝ) ≤ a := ha
  have hb0 : (0 : ℝ) ≤ b := hb
  have hab_le : a ≤ b := hab.le
  have h_int_ab := cf24_integrand_intervalIntegrable h_nn h_simplex h_interior_0 ha0 hab_le
  have h_int_0a := cf24_integrand_intervalIntegrable h_nn h_simplex h_interior_0
    (le_refl (0 : ℝ)) ha0
  have h_int_0b := cf24_integrand_intervalIntegrable h_nn h_simplex h_interior_0
    (le_refl (0 : ℝ)) hb0
  -- σ b = σ a + ∫_a^b integrand
  have h_split :
      cf24_sigma x0 h_nn h_simplex b
        = cf24_sigma x0 h_nn h_simplex a
          + ∫ u in a..b,
              4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2 := by
    unfold cf24_sigma
    rw [← intervalIntegral.integral_add_adjacent_intervals h_int_0a h_int_ab]
  -- ∫_a^b integrand > 0.
  have h_cont_Icc :
      ContinuousOn
        (fun u => 4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2)
        (Set.Icc a b) :=
    (cf24_integrand_contOn h_nn h_simplex h_interior_0).mono
      (fun x hx => le_trans ha0 hx.1)
  -- `integral_pos` wants positivity on Ioc, but we have it on Ici 0 ⊇ [a,b].
  have h_le_Ioc : ∀ u ∈ Set.Ioc a b,
      0 ≤ 4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2 := by
    intro u hu
    exact (cf24_integrand_pos h_nn h_simplex h_interior_0 u
      (le_trans ha0 hu.1.le)).le
  have h_lt_c : ∃ c ∈ Set.Icc a b,
      0 < 4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory c 0)^2 := by
    refine ⟨a, ⟨le_refl a, hab_le⟩, ?_⟩
    exact cf24_integrand_pos h_nn h_simplex h_interior_0 a ha0
  have h_pos_int :
      0 < ∫ u in a..b,
        4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2 :=
    intervalIntegral.integral_pos hab h_cont_Icc h_le_Ioc h_lt_c
  linarith

/-- **σ(t) ≥ 4·t for `t ≥ 0`.**  Since `z_00(u) ≤ 1` on the simplex, we
have `4/(z_00(u))² ≥ 4`, so the integral dominates the linear function. -/
theorem cf24_sigma_ge
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ∀ t, 0 ≤ t → 4 * t ≤ cf24_sigma x0 h_nn h_simplex t := by
  intro t ht
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  -- ∫_0^t 4 = 4·t.
  have h_int_const : ∫ _u in (0 : ℝ)..t, (4 : ℝ) = 4 * t := by
    rw [intervalIntegral.integral_const]
    simp [sub_zero]; ring
  -- Pointwise bound on Icc 0 t: 4 ≤ integrand.
  have h_pw : ∀ u ∈ Set.Icc (0 : ℝ) t,
      (4 : ℝ) ≤ 4 / (sol.trajectory u 0)^2 := by
    intro u hu
    have hu_nn : 0 ≤ u := hu.1
    have h_pos : 0 < sol.trajectory u 0 :=
      cf24_traj_zero_strict_pos h_nn h_simplex h_interior_0 u hu_nn
    have h_le1 : sol.trajectory u 0 ≤ 1 :=
      cf24_traj_zero_le_one h_nn h_simplex u hu_nn
    have h_sq_pos : 0 < (sol.trajectory u 0)^2 := pow_pos h_pos 2
    have h_sq_le1 : (sol.trajectory u 0)^2 ≤ 1 := by
      have h1 : (sol.trajectory u 0)^2 ≤ 1 * 1 := by
        rw [sq]
        exact mul_le_mul h_le1 h_le1 h_pos.le zero_le_one
      simpa using h1
    -- 4 = 4/1 ≤ 4/(z 0)² since (z 0)² ≤ 1 and (z 0)² > 0.
    have h_lhs : (4 : ℝ) = 4 / 1 := by norm_num
    conv_lhs => rw [h_lhs]
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) h_sq_pos h_sq_le1
  -- Interval-integrability of both sides.
  have h_int_L :
      IntervalIntegrable (fun _ => (4 : ℝ)) MeasureTheory.volume 0 t :=
    intervalIntegrable_const
  have h_int_R := cf24_integrand_intervalIntegrable h_nn h_simplex h_interior_0
    (le_refl (0 : ℝ)) ht
  -- Monotonicity of integral on [0,t].
  have h_mono :
      (∫ u in (0 : ℝ)..t, (4 : ℝ))
        ≤ ∫ u in (0 : ℝ)..t, 4 / (sol.trajectory u 0)^2 :=
    intervalIntegral.integral_mono_on ht h_int_L h_int_R h_pw
  calc 4 * t = ∫ _u in (0 : ℝ)..t, (4 : ℝ) := h_int_const.symm
    _ ≤ ∫ u in (0 : ℝ)..t, 4 / (sol.trajectory u 0)^2 := h_mono
    _ = cf24_sigma x0 h_nn h_simplex t := rfl

/-- **σ → ∞.**  Since `σ(t) ≥ 4·t` for `t ≥ 0` and `4·t → ∞`, we get
`σ t → ∞` as `t → ∞`. -/
theorem cf24_sigma_tendsto_atTop
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    Filter.Tendsto (cf24_sigma x0 h_nn h_simplex) Filter.atTop Filter.atTop := by
  -- 4·t → ∞.
  have h_lin : Filter.Tendsto (fun t : ℝ => 4 * t) Filter.atTop Filter.atTop := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    exact Filter.tendsto_atTop.mpr fun b => by
      have := (Filter.tendsto_atTop.mp (Filter.tendsto_id (α := ℝ))) (b / 4)
      filter_upwards [this, Filter.eventually_ge_atTop (0 : ℝ)] with t ht h0
      have : b / 4 ≤ t := ht
      have := (div_le_iff₀ h4).mp this
      linarith
  -- Eventually 4·t ≤ σ(t).
  have h_ev : (fun t : ℝ => 4 * t) ≤ᶠ[Filter.atTop] cf24_sigma x0 h_nn h_simplex := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact cf24_sigma_ge h_nn h_simplex h_interior_0 t ht
  exact Filter.tendsto_atTop_mono' _ h_ev h_lin

/-- **σ is continuous on `[0, ∞)`.**  Follows from continuity of the
integrand on `[0, ∞)` together with interval-integrability on every
`[0, T]`, via `intervalIntegral.continuousOn_primitive_interval'`. -/
theorem cf24_sigma_continuousOn
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ContinuousOn (cf24_sigma x0 h_nn h_simplex) (Set.Ici (0 : ℝ)) := by
  -- Local continuity at each t₀ ≥ 0: pick T > t₀, use continuity on [[0, T]].
  intro t₀ ht₀
  have ht₀0 : (0 : ℝ) ≤ t₀ := ht₀
  -- Choose T := t₀ + 1 so that t₀ ∈ [0, T].
  set T := t₀ + 1 with hT_def
  have hT_pos : (0 : ℝ) ≤ T := by have : (0 : ℝ) ≤ t₀ := ht₀0; linarith
  have h_int_0T := cf24_integrand_intervalIntegrable h_nn h_simplex h_interior_0
    (le_refl (0 : ℝ)) hT_pos
  -- `continuousOn_primitive_interval'` with a = 0, b₁ = 0, b₂ = T.
  have h_cont_uIcc :
      ContinuousOn (cf24_sigma x0 h_nn h_simplex) (Set.uIcc (0 : ℝ) T) := by
    have h_zero_mem : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) T := by
      simp [Set.uIcc, hT_pos]
    exact intervalIntegral.continuousOn_primitive_interval' h_int_0T h_zero_mem
  -- t₀ ∈ uIcc 0 T = [0, T] since 0 ≤ t₀ ≤ T.
  have ht₀_mem : t₀ ∈ Set.uIcc (0 : ℝ) T := by
    have : t₀ ≤ T := by simp [hT_def]
    simp [Set.uIcc, hT_pos, ht₀0, this]
  have h_at_t₀ : ContinuousWithinAt
      (cf24_sigma x0 h_nn h_simplex) (Set.uIcc (0 : ℝ) T) t₀ :=
    h_cont_uIcc t₀ ht₀_mem
  -- Convert to ContinuousWithinAt on Set.Ici 0.
  refine h_at_t₀.mono_of_mem_nhdsWithin ?_
  -- `Set.uIcc 0 T = [0, T]` (since 0 ≤ T), and this set is a neighbourhood of
  -- t₀ within `Set.Ici 0`, because `(t₀ - 1, T + 1) ∩ Ici 0` is open and
  -- contains t₀, and sits inside `Icc 0 T`.
  have h_uIcc_eq : Set.uIcc (0 : ℝ) T = Set.Icc (0 : ℝ) T := by
    simp [Set.uIcc, hT_pos]
  rw [h_uIcc_eq]
  -- Show `Icc 0 T ∈ 𝓝[Ici 0] t₀`.
  have hT_lt : t₀ < T + 1 := by
    simp only [hT_def]; linarith
  have h_Iio : Set.Iio (T + 1) ∈ nhds t₀ := IsOpen.mem_nhds isOpen_Iio hT_lt
  have h_Iio_within : Set.Iio (T + 1) ∈ nhdsWithin t₀ (Set.Ici (0 : ℝ)) :=
    mem_nhdsWithin_of_mem_nhds h_Iio
  -- Icc 0 T = Ici 0 ∩ Iic T; within Ici 0, this becomes `Iic T`, which is in
  -- the filter because Iic T ⊇ Iio (T+1) (nope — Iic T = {x ≤ T}, Iio (T+1) = {x < T+1};
  -- but x < T+1 doesn't imply x ≤ T).  So use a different bound: pick Iio (T)
  -- which DOES imply Iic T via <.  Better: use that t₀ < T so Iic T is a nhd.
  have h_Iic : Set.Iic T ∈ nhds t₀ := by
    have h_lt : t₀ < T := by
      simp only [hT_def]; linarith
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Iio h_lt) Set.Iio_subset_Iic_self
  have h_Iic_within : Set.Iic T ∈ nhdsWithin t₀ (Set.Ici (0 : ℝ)) :=
    mem_nhdsWithin_of_mem_nhds h_Iic
  -- Also self_mem: Set.Ici 0 ∈ nhdsWithin t₀ (Set.Ici 0).
  have h_self : Set.Ici (0 : ℝ) ∈ nhdsWithin t₀ (Set.Ici (0 : ℝ)) :=
    self_mem_nhdsWithin
  -- Intersect: Ici 0 ∩ Iic T = Icc 0 T.
  have h_inter :
      Set.Ici (0 : ℝ) ∩ Set.Iic T ∈ nhdsWithin t₀ (Set.Ici (0 : ℝ)) :=
    Filter.inter_mem h_self h_Iic_within
  have h_eq : Set.Ici (0 : ℝ) ∩ Set.Iic T = Set.Icc (0 : ℝ) T := by
    ext x; simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic, and_comm]
  rw [← h_eq]
  exact h_inter

/-- **σ is surjective from `[0, ∞)` onto `[0, ∞)`.**  Intermediate-value
theorem applied to σ continuous on some `[0, T]` with `σ 0 = 0` and
`y ≤ σ T` (achievable since `σ → ∞`). -/
theorem cf24_sigma_surjOn
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    Set.SurjOn (cf24_sigma x0 h_nn h_simplex) (Set.Ici (0 : ℝ))
      (Set.Ici (0 : ℝ)) := by
  intro y hy
  have hy0 : (0 : ℝ) ≤ y := hy
  -- Pick T with y ≤ σ T using `σ → ∞`.
  have h_tends := cf24_sigma_tendsto_atTop h_nn h_simplex h_interior_0
  have h_eventually : ∀ᶠ t in Filter.atTop, y ≤ cf24_sigma x0 h_nn h_simplex t :=
    Filter.tendsto_atTop.mp h_tends y
  have h_eventually_nn : ∀ᶠ t in Filter.atTop, (0 : ℝ) ≤ t :=
    Filter.eventually_ge_atTop 0
  have h_both := h_eventually.and h_eventually_nn
  obtain ⟨T, hT_y, hT_nn⟩ := h_both.exists
  -- σ is continuous on [0, T].
  have h_cont_Ici := cf24_sigma_continuousOn h_nn h_simplex h_interior_0
  have h_Icc_sub : Set.Icc (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) :=
    fun x hx => hx.1
  have h_cont_Icc :
      ContinuousOn (cf24_sigma x0 h_nn h_simplex) (Set.Icc (0 : ℝ) T) :=
    h_cont_Ici.mono h_Icc_sub
  -- Apply IVT: y ∈ [σ 0, σ T] = [0, σ T] since σ 0 = 0 and y ≤ σ T.
  have h_sigma_zero :
      cf24_sigma x0 h_nn h_simplex 0 = 0 :=
    cf24_sigma_zero h_nn h_simplex
  have h_y_mem : y ∈ Set.Icc
      (cf24_sigma x0 h_nn h_simplex 0) (cf24_sigma x0 h_nn h_simplex T) := by
    refine ⟨?_, hT_y⟩
    rw [h_sigma_zero]; exact hy0
  have h_img := intermediate_value_Icc hT_nn h_cont_Icc h_y_mem
  obtain ⟨t, ht_mem, ht_eq⟩ := h_img
  exact ⟨t, h_Icc_sub ht_mem, ht_eq⟩

/-- **τ = σ⁻¹** on `[0, ∞)`.  Defined piecewise: for `s ≥ 0`, `τ s` is a
chosen preimage of `s` under `σ` (exists by `cf24_sigma_surjOn`); for
`s < 0`, `τ s := 0` (default). -/
noncomputable def cf24_tau
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) : ℝ → ℝ := by
  classical
  exact fun s =>
    if hs : 0 ≤ s then
      Classical.choose (cf24_sigma_surjOn h_nn h_simplex h_interior_0 hs)
    else 0

/-- Characterization of `τ` via `Classical.choose`: for `s ≥ 0`, `τ s` is
the chosen preimage. -/
private theorem cf24_tau_spec
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) {s : ℝ} (hs : 0 ≤ s) :
    cf24_tau x0 h_nn h_simplex h_interior_0 s ∈ Set.Ici (0 : ℝ) ∧
    cf24_sigma x0 h_nn h_simplex
      (cf24_tau x0 h_nn h_simplex h_interior_0 s) = s := by
  classical
  unfold cf24_tau
  simp [hs]
  exact Classical.choose_spec
    (cf24_sigma_surjOn h_nn h_simplex h_interior_0 hs)

/-- `τ 0 = 0`. -/
theorem cf24_tau_zero
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    cf24_tau x0 h_nn h_simplex h_interior_0 0 = 0 := by
  have h_spec := cf24_tau_spec h_nn h_simplex h_interior_0 (le_refl (0 : ℝ))
  obtain ⟨h_nn_tau, h_sigma_tau⟩ := h_spec
  -- σ is strictly monotone on Ici 0 and σ 0 = 0, so σ x = 0 with x ≥ 0 forces x = 0.
  have h_sigma_zero : cf24_sigma x0 h_nn h_simplex 0 = 0 :=
    cf24_sigma_zero h_nn h_simplex
  set t := cf24_tau x0 h_nn h_simplex h_interior_0 0 with ht_def
  -- We have σ t = 0 and σ 0 = 0 and t ≥ 0 and 0 ∈ Ici 0. By strict monotonicity, t = 0.
  have h_smono := cf24_sigma_strictMonoOn h_nn h_simplex h_interior_0
  rcases lt_trichotomy t 0 with h_lt | h_eq | h_gt
  · exact absurd h_lt (not_lt.mpr h_nn_tau)
  · exact h_eq
  · -- 0 < t ⇒ σ 0 < σ t = 0, contradiction.
    have h_st_pos : cf24_sigma x0 h_nn h_simplex 0
        < cf24_sigma x0 h_nn h_simplex t :=
      h_smono (Set.left_mem_Ici) h_nn_tau h_gt
    rw [h_sigma_zero, h_sigma_tau] at h_st_pos
    exact absurd h_st_pos (lt_irrefl 0)

/-- `τ s ≥ 0` for `s ≥ 0`. -/
theorem cf24_tau_nonneg
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ∀ s, 0 ≤ s → 0 ≤ cf24_tau x0 h_nn h_simplex h_interior_0 s := by
  intro s hs
  exact (cf24_tau_spec h_nn h_simplex h_interior_0 hs).1

/-- `σ(τ s) = s` for `s ≥ 0`. -/
theorem cf24_sigma_tau
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ∀ s, 0 ≤ s →
      cf24_sigma x0 h_nn h_simplex
        (cf24_tau x0 h_nn h_simplex h_interior_0 s) = s := by
  intro s hs
  exact (cf24_tau_spec h_nn h_simplex h_interior_0 hs).2

/-- `τ(σ t) = t` for `t ≥ 0`.  Uses that σ is strictly monotone (hence
injective) on `Ici 0`. -/
theorem cf24_tau_sigma
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ∀ t, 0 ≤ t →
      cf24_tau x0 h_nn h_simplex h_interior_0
        (cf24_sigma x0 h_nn h_simplex t) = t := by
  intro t ht
  -- σ t ≥ σ 0 = 0 by strict monotonicity (or equality if t = 0).
  have h_sigma_zero : cf24_sigma x0 h_nn h_simplex 0 = 0 :=
    cf24_sigma_zero h_nn h_simplex
  have h_smono := cf24_sigma_strictMonoOn h_nn h_simplex h_interior_0
  have h_sigma_nn : 0 ≤ cf24_sigma x0 h_nn h_simplex t := by
    rcases eq_or_lt_of_le ht with h_eq | h_lt
    · rw [← h_eq, h_sigma_zero]
    · have := h_smono (le_refl (0 : ℝ)) ht h_lt
      rw [h_sigma_zero] at this; exact this.le
  -- Let t' := τ (σ t). Then σ t' = σ t.  By injectivity (strict mono), t' = t.
  have h_spec := cf24_tau_spec h_nn h_simplex h_interior_0 h_sigma_nn
  obtain ⟨h_t'_nn, h_sigma_t'⟩ := h_spec
  set t' := cf24_tau x0 h_nn h_simplex h_interior_0
    (cf24_sigma x0 h_nn h_simplex t) with ht'_def
  -- σ t' = σ t.
  -- Want t' = t.  Use strict mono injection on Ici 0.
  rcases lt_trichotomy t' t with h_lt | h_eq | h_gt
  · have := h_smono h_t'_nn ht h_lt
    rw [h_sigma_t'] at this; exact absurd this (lt_irrefl _)
  · exact h_eq
  · have := h_smono ht h_t'_nn h_gt
    rw [h_sigma_t'] at this; exact absurd this (lt_irrefl _)

/-- **τ is strictly monotone on `[0, ∞)`.**  If `a < b` both in `[0, ∞)`,
then `σ(τ a) = a < b = σ(τ b)` so `τ a ≠ τ b`; and since σ is strictly
monotone with `σ(τ a), σ(τ b) ≥ 0`, we cannot have `τ a ≥ τ b`. -/
theorem cf24_tau_strictMonoOn
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    StrictMonoOn (cf24_tau x0 h_nn h_simplex h_interior_0) (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) ≤ a := ha
  have hb0 : (0 : ℝ) ≤ b := hb
  have h_spec_a := cf24_tau_spec h_nn h_simplex h_interior_0 ha0
  have h_spec_b := cf24_tau_spec h_nn h_simplex h_interior_0 hb0
  obtain ⟨h_ta_nn, h_sa⟩ := h_spec_a
  obtain ⟨h_tb_nn, h_sb⟩ := h_spec_b
  set ta := cf24_tau x0 h_nn h_simplex h_interior_0 a
  set tb := cf24_tau x0 h_nn h_simplex h_interior_0 b
  have h_smono := cf24_sigma_strictMonoOn h_nn h_simplex h_interior_0
  -- Suppose ta ≥ tb.  Then σ ta ≥ σ tb (by strict mono contrapositive), i.e. a ≥ b.
  by_contra h_not
  push_neg at h_not
  rcases eq_or_lt_of_le h_not with h_eq | h_gt
  · -- ta = tb ⇒ a = σ ta = σ tb = b, contradicts a < b.
    have h_sa' : cf24_sigma x0 h_nn h_simplex ta = a := h_sa
    have h_sb' : cf24_sigma x0 h_nn h_simplex tb = b := h_sb
    have h_ta_eq : ta = tb := h_eq.symm
    rw [h_ta_eq] at h_sa'
    -- h_sa' : σ tb = a; h_sb' : σ tb = b; so a = b, contradiction with a < b.
    have : a = b := by rw [← h_sa', h_sb']
    exact absurd this (ne_of_lt hab)
  · -- tb < ta ⇒ σ tb < σ ta ⇒ b < a, contradicts a < b.
    have h_σlt := h_smono h_tb_nn h_ta_nn h_gt
    have h_sa' : cf24_sigma x0 h_nn h_simplex ta = a := h_sa
    have h_sb' : cf24_sigma x0 h_nn h_simplex tb = b := h_sb
    have : b < a := by rw [← h_sa', ← h_sb']; exact h_σlt
    exact absurd (lt_trans hab this) (lt_irrefl _)

/-- **τ → ∞.**  `τ` is strict mono on `Ici 0` and surjective onto `Ici 0`
(since `τ (σ t) = t` for every `t ≥ 0` and `σ t ∈ Ici 0`), hence unbounded
above.  A strict-mono unbounded function tends to `atTop`.

More concretely: for any `M ≥ 0`, taking `s := σ M ≥ 0` gives `τ s = M`.
For every `s' ≥ s`, strict monotonicity gives `τ s' ≥ τ s = M`. -/
theorem cf24_tau_tendsto_atTop
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    Filter.Tendsto (cf24_tau x0 h_nn h_simplex h_interior_0)
      Filter.atTop Filter.atTop := by
  set τ := cf24_tau x0 h_nn h_simplex h_interior_0 with hτ_def
  set σ := cf24_sigma x0 h_nn h_simplex with hσ_def
  have h_σ0 : σ 0 = 0 := cf24_sigma_zero h_nn h_simplex
  have h_σmono := cf24_sigma_strictMonoOn h_nn h_simplex h_interior_0
  have h_τmono := cf24_tau_strictMonoOn h_nn h_simplex h_interior_0
  refine Filter.tendsto_atTop.mpr ?_
  intro M
  -- Pick M' := max M 0 ≥ 0 so σ(M') ≥ 0 and τ(σ(M')) = M'.
  set M' : ℝ := max M 0 with hM'_def
  have hM'_nn : 0 ≤ M' := le_max_right _ _
  have hM_le : M ≤ M' := le_max_left _ _
  -- σ M' ≥ 0.
  have h_σM'_nn : 0 ≤ σ M' := by
    rcases eq_or_lt_of_le hM'_nn with h_eq | h_lt
    · rw [← h_eq, h_σ0]
    · have h := h_σmono (le_refl (0 : ℝ)) hM'_nn h_lt
      have : σ 0 < σ M' := h
      linarith
  -- τ (σ M') = M'.
  have h_τσ : cf24_tau x0 h_nn h_simplex h_interior_0 (σ M') = M' :=
    cf24_tau_sigma h_nn h_simplex h_interior_0 M' hM'_nn
  -- For any s' ≥ σ M', τ s' ≥ τ (σ M') = M' ≥ M.
  filter_upwards [Filter.eventually_ge_atTop (σ M')] with s' hs'
  -- s' ≥ 0 since σ M' ≥ 0.
  have hs'_nn : 0 ≤ s' := le_trans h_σM'_nn hs'
  rcases eq_or_lt_of_le hs' with h_eq | h_lt
  · -- s' = σ M'.
    have : τ s' = M' := by rw [← h_eq]; exact h_τσ
    linarith
  · -- s' > σ M'.
    have h := h_τmono h_σM'_nn hs'_nn h_lt
    have : τ (σ M') < τ s' := h
    have h_eqM' : τ (σ M') = M' := h_τσ
    linarith

/-! ### Differentiability of σ and τ — assembling the chain rule.

The remaining Part C lemmas: `σ` has derivative `4/(z 0)²` at interior
points via FTC, `τ` has the reciprocal derivative via the inverse
function theorem, and the composed map `cf24LambdaEmbed ∘ traj ∘ τ`
satisfies the r²-trick ODE at every `s > 0`. -/

/-- **FTC at interior points.**  σ is differentiable at every `t > 0`
with derivative `4/(z 0 t)²`. -/
theorem cf24_sigma_hasDerivAt
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cf24_sigma x0 h_nn h_simplex)
      (4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory t 0)^2) t := by
  set f : ℝ → ℝ := fun u =>
    4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory u 0)^2 with hf_def
  -- Integrand continuous on [0, ∞) ⊇ nhds t (since t > 0).
  have h_cont_Ici : ContinuousOn f (Set.Ici (0 : ℝ)) :=
    cf24_integrand_contOn h_nn h_simplex h_interior_0
  have h_Ici_nhds : Set.Ici (0 : ℝ) ∈ nhds t := by
    have h_Ioi : Set.Ioi (0 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds ht
    apply Filter.mem_of_superset h_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    exact le_of_lt hx
  have h_contAt : ContinuousAt f t := by
    have h_cwa : ContinuousWithinAt f (Set.Ici (0 : ℝ)) t :=
      h_cont_Ici t (le_of_lt ht)
    exact ContinuousWithinAt.continuousAt h_cwa h_Ici_nhds
  -- StronglyMeasurableAtFilter at nhds t: built from continuity on Ioi 0 (open nhd of t).
  have h_cont_Ioi : ContinuousOn f (Set.Ioi (0 : ℝ)) := by
    apply h_cont_Ici.mono
    intro u hu
    simp only [Set.mem_Ioi] at hu
    exact le_of_lt hu
  have h_meas : StronglyMeasurableAtFilter f (nhds t) := by
    refine ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds ht, ?_⟩
    exact (h_cont_Ioi.aestronglyMeasurable isOpen_Ioi.measurableSet)
  have h_ftc : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, f x) (f t) t := by
    have h_int_t : IntervalIntegrable f MeasureTheory.volume 0 t :=
      cf24_integrand_intervalIntegrable h_nn h_simplex h_interior_0
        (le_refl 0) (le_of_lt ht)
    exact intervalIntegral.integral_hasDerivAt_right h_int_t h_meas h_contAt
  simpa [cf24_sigma, hf_def] using h_ftc

/-- **τ is continuous at every `s > 0`.**  Using strict monotonicity of
σ and τ on `Ici 0`, with σ's values straddling any neighborhood of `s`. -/
theorem cf24_tau_continuousAt_pos
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (cf24_tau x0 h_nn h_simplex h_interior_0) s := by
  set τ := cf24_tau x0 h_nn h_simplex h_interior_0 with hτ_def
  set σ := cf24_sigma x0 h_nn h_simplex with hσ_def
  have hs_nn : (0 : ℝ) ≤ s := le_of_lt hs
  have h_τs_nn : 0 ≤ τ s := cf24_tau_nonneg h_nn h_simplex h_interior_0 s hs_nn
  have h_στs : σ (τ s) = s :=
    cf24_sigma_tau h_nn h_simplex h_interior_0 s hs_nn
  have h_σ0 : σ 0 = 0 := cf24_sigma_zero h_nn h_simplex
  have h_τs_pos : 0 < τ s := by
    rcases eq_or_lt_of_le h_τs_nn with h_eq | h_lt
    · exfalso
      have hh : σ (τ s) = σ 0 := by rw [← h_eq]
      rw [h_στs, h_σ0] at hh; linarith
    · exact h_lt
  rw [Metric.continuousAt_iff]
  intro ε hε
  set ε' : ℝ := min ε (τ s) with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε h_τs_pos
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have hε'_le_τs : ε' ≤ τ s := min_le_right _ _
  have h_lo_nn : 0 ≤ τ s - ε' := by linarith
  have h_hi_nn : 0 ≤ τ s + ε' := by linarith
  have h_σmono := cf24_sigma_strictMonoOn h_nn h_simplex h_interior_0
  have h_σ_lo_lt : σ (τ s - ε') < s := by
    have h := h_σmono h_lo_nn h_τs_nn (by linarith : τ s - ε' < τ s)
    have : σ (τ s - ε') < σ (τ s) := h
    linarith [h_στs]
  have h_s_lt_σ_hi : s < σ (τ s + ε') := by
    have h := h_σmono h_τs_nn h_hi_nn (by linarith : τ s < τ s + ε')
    have : σ (τ s) < σ (τ s + ε') := h
    linarith [h_στs]
  set δ : ℝ := min (s - σ (τ s - ε')) (σ (τ s + ε') - s) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  rw [Real.dist_eq] at hy ⊢
  have h_y_lo : σ (τ s - ε') < y := by
    have h_low : s - δ < y := by linarith [abs_lt.mp hy]
    have h_δ_le : δ ≤ s - σ (τ s - ε') := min_le_left _ _
    linarith
  have h_y_hi : y < σ (τ s + ε') := by
    have h_hi : y < s + δ := by linarith [abs_lt.mp hy]
    have h_δ_le : δ ≤ σ (τ s + ε') - s := min_le_right _ _
    linarith
  have h_σ_lo_nn : 0 ≤ σ (τ s - ε') := by
    rcases eq_or_lt_of_le h_lo_nn with h_eq | h_lt
    · rw [← h_eq, h_σ0]
    · have h := h_σmono (le_refl (0 : ℝ)) h_lo_nn h_lt
      have : σ 0 < σ (τ s - ε') := h
      linarith
  have h_σ_hi_nn : 0 ≤ σ (τ s + ε') := by
    have h := h_σmono (le_refl (0 : ℝ)) h_hi_nn (by linarith)
    have : σ 0 < σ (τ s + ε') := h
    linarith
  have h_y_nn : 0 ≤ y := le_trans h_σ_lo_nn (le_of_lt h_y_lo)
  have h_τ_strict := cf24_tau_strictMonoOn h_nn h_simplex h_interior_0
  have h_τ_inv_lo :
      cf24_tau x0 h_nn h_simplex h_interior_0 (σ (τ s - ε')) = τ s - ε' :=
    cf24_tau_sigma h_nn h_simplex h_interior_0 _ h_lo_nn
  have h_τ_inv_hi :
      cf24_tau x0 h_nn h_simplex h_interior_0 (σ (τ s + ε')) = τ s + ε' :=
    cf24_tau_sigma h_nn h_simplex h_interior_0 _ h_hi_nn
  have h_τ_y_lo : τ s - ε' < τ y := by
    have h := h_τ_strict h_σ_lo_nn h_y_nn h_y_lo
    rw [h_τ_inv_lo] at h; exact h
  have h_τ_y_hi : τ y < τ s + ε' := by
    have h := h_τ_strict h_y_nn h_σ_hi_nn h_y_hi
    rw [h_τ_inv_hi] at h; exact h
  have h_abs : |τ y - τ s| < ε' := by
    rw [abs_lt]; constructor <;> linarith
  linarith

/-- **τ has derivative `(z 0 (τ s))² / 4` at every `s > 0`.**  Via the
inverse function theorem applied to σ. -/
theorem cf24_tau_hasDerivAt
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (cf24_tau x0 h_nn h_simplex h_interior_0)
      (((cf24_global_solution x0 h_nn h_simplex).trajectory
          (cf24_tau x0 h_nn h_simplex h_interior_0 s) 0)^2 / 4) s := by
  set τ := cf24_tau x0 h_nn h_simplex h_interior_0 with hτ_def
  set σ := cf24_sigma x0 h_nn h_simplex with hσ_def
  have hs_nn : (0 : ℝ) ≤ s := le_of_lt hs
  have h_τs_nn : 0 ≤ τ s := cf24_tau_nonneg h_nn h_simplex h_interior_0 s hs_nn
  have h_στs : σ (τ s) = s :=
    cf24_sigma_tau h_nn h_simplex h_interior_0 s hs_nn
  have h_σ0 : σ 0 = 0 := cf24_sigma_zero h_nn h_simplex
  have h_τs_pos : 0 < τ s := by
    rcases eq_or_lt_of_le h_τs_nn with h_eq | h_lt
    · exfalso
      have hh : σ (τ s) = σ 0 := by rw [← h_eq]
      rw [h_στs, h_σ0] at hh; linarith
    · exact h_lt
  have h_σ_deriv : HasDerivAt σ
      (4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 0)^2)
      (τ s) :=
    cf24_sigma_hasDerivAt h_nn h_simplex h_interior_0 h_τs_pos
  have h_traj_pos : 0 < (cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 0 :=
    cf24_traj_zero_strict_pos h_nn h_simplex h_interior_0 (τ s) h_τs_nn
  have h_sq_pos :
      0 < ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 0)^2 :=
    pow_pos h_traj_pos 2
  have h_f'_pos :
      (0 : ℝ) < 4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 0)^2 := by
    positivity
  have h_f'_ne :
      (4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 0)^2 : ℝ) ≠ 0 :=
    ne_of_gt h_f'_pos
  have h_τ_cont : ContinuousAt τ s :=
    cf24_tau_continuousAt_pos h_nn h_simplex h_interior_0 hs
  have h_σ_τ : ∀ᶠ y in nhds s, σ (τ y) = y := by
    have h_Ioi : Set.Ioi (0 : ℝ) ∈ nhds s := isOpen_Ioi.mem_nhds hs
    refine Filter.mem_of_superset h_Ioi ?_
    intro y hy
    exact cf24_sigma_tau h_nn h_simplex h_interior_0 y (le_of_lt hy)
  have h_inv := h_σ_deriv.of_local_left_inverse h_τ_cont h_f'_ne h_σ_τ
  -- (4 / z²)⁻¹ = z² / 4.
  have h_eq :
      (4 / ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 0)^2 : ℝ)⁻¹
        = ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 0)^2 / 4 := by
    rw [inv_div]
  rw [h_eq] at h_inv
  exact h_inv

/-! ### `s = 0` endpoint: right-derivative of σ and τ

To restore the full `0 ≤ s` clause in `Cf24R2Reparam`, we need the
right-derivative of `τ = σ⁻¹` at `s = 0`.  The chain is:

* `cf24_sigma_hasDerivWithinAt_zero` — `σ` has right-derivative
  `4 / (x0 0)²` at `0`, by FTC for `Ici`-restricted integrals.
* `cf24_tau_continuousWithinAt_zero` — `τ` is right-continuous at `0`.
* `cf24_tau_hasDerivWithinAt_zero` — `τ` has right-derivative
  `(x0 0)² / 4` at `0`, via the within-version of the inverse function
  theorem `HasFDerivWithinAt.of_local_left_inverse`.
-/

/-- **Right-derivative of σ at 0.**  Applying the one-sided FTC at the
left endpoint with the integrand continuous on `[0,∞)` from the right. -/
theorem cf24_sigma_hasDerivWithinAt_zero
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    HasDerivWithinAt (cf24_sigma x0 h_nn h_simplex)
      (4 / (x0 0)^2) (Set.Ici (0 : ℝ)) 0 := by
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  set f : ℝ → ℝ := fun u => 4 / (sol.trajectory u 0)^2 with hf_def
  -- Integrand value at 0 is 4 / (x0 0)^2.
  have h_traj0 : sol.trajectory 0 = x0 := sol.init_cond
  have h_f0 : f 0 = 4 / (x0 0)^2 := by
    simp [hf_def, h_traj0]
  -- Integrability on [0, 0]: trivially, since cf24_integrand_intervalIntegrable
  -- works for any 0 ≤ a ≤ b.  We need the goal in the form
  -- HasDerivWithinAt (∫ x in 0..u, f x) (f 0) (Ici 0) 0.
  -- We use the FTC right-derivative variant, with a=0, b=0, s=Ici 0, t=Ioi 0.
  have h_int : IntervalIntegrable f MeasureTheory.volume 0 0 :=
    (IntervalIntegrable.refl)
  -- StronglyMeasurableAtFilter f (𝓝[Ioi 0] 0): integrand is continuous on Ioi 0.
  have h_cont_Ici : ContinuousOn f (Set.Ici (0 : ℝ)) :=
    cf24_integrand_contOn h_nn h_simplex h_interior_0
  have h_cont_Ioi : ContinuousOn f (Set.Ioi (0 : ℝ)) := by
    apply h_cont_Ici.mono
    intro u hu
    exact (Set.mem_Ioi.mp hu).le
  have h_meas : StronglyMeasurableAtFilter f (𝓝[Set.Ioi (0 : ℝ)] 0) := by
    refine ⟨Set.Ioi 0, self_mem_nhdsWithin, ?_⟩
    exact h_cont_Ioi.aestronglyMeasurable isOpen_Ioi.measurableSet
  -- ContinuousWithinAt f (Ioi 0) 0: from continuity on Ici 0, restricted.
  have h_cwa_Ici : ContinuousWithinAt f (Set.Ici (0 : ℝ)) 0 :=
    h_cont_Ici 0 Set.self_mem_Ici
  have h_cwa_Ioi : ContinuousWithinAt f (Set.Ioi (0 : ℝ)) 0 :=
    h_cwa_Ici.mono (fun u hu => (Set.mem_Ioi.mp hu).le)
  -- Apply intervalIntegral.integral_hasDerivWithinAt_right.
  have h_ftc :
      HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, f x) (f 0) (Set.Ici (0 : ℝ)) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right h_int h_meas h_cwa_Ioi
  rw [h_f0] at h_ftc
  simpa [cf24_sigma, hf_def] using h_ftc

/-- **τ is right-continuous at 0.**  Strict monotonicity of σ + σ(0) = 0
gives, for any neighborhood `[0, ε)` of `0`, the preimage under τ contains
`[0, σ(ε))`. -/
theorem cf24_tau_continuousWithinAt_zero
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    ContinuousWithinAt (cf24_tau x0 h_nn h_simplex h_interior_0)
      (Set.Ici (0 : ℝ)) 0 := by
  have h_τ0 : cf24_tau x0 h_nn h_simplex h_interior_0 0 = 0 :=
    cf24_tau_zero h_nn h_simplex h_interior_0
  have h_σ0 : cf24_sigma x0 h_nn h_simplex 0 = 0 :=
    cf24_sigma_zero h_nn h_simplex
  have h_σmono := cf24_sigma_strictMonoOn h_nn h_simplex h_interior_0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- Take δ := σ ε, which is positive since σ is strictly monotone and σ(0) = 0.
  have h_σε_pos : 0 < cf24_sigma x0 h_nn h_simplex ε := by
    have h := h_σmono (le_refl (0 : ℝ)) (le_of_lt hε) hε
    rwa [h_σ0] at h
  refine ⟨cf24_sigma x0 h_nn h_simplex ε, h_σε_pos, ?_⟩
  intro y hy_mem hy_dist
  simp only [Set.mem_Ici] at hy_mem
  rw [Real.dist_eq] at hy_dist ⊢
  rw [h_τ0]; rw [sub_zero]
  -- y < σ ε so τ y < ε (by strict mono of τ).
  have hy_lt_σε : y < cf24_sigma x0 h_nn h_simplex ε := by
    have habs : |y - 0| < cf24_sigma x0 h_nn h_simplex ε := by simpa using hy_dist
    rw [sub_zero] at habs
    exact (abs_lt.mp habs).2
  have h_τy_nn : 0 ≤ cf24_tau x0 h_nn h_simplex h_interior_0 y :=
    cf24_tau_nonneg h_nn h_simplex h_interior_0 y hy_mem
  -- τ y < ε: use that σ τ y = y < σ ε and σ strict mono on Ici 0.
  have h_τmono := cf24_tau_strictMonoOn h_nn h_simplex h_interior_0
  have h_τσε : cf24_tau x0 h_nn h_simplex h_interior_0
      (cf24_sigma x0 h_nn h_simplex ε) = ε :=
    cf24_tau_sigma h_nn h_simplex h_interior_0 ε (le_of_lt hε)
  have h_τy_lt : cf24_tau x0 h_nn h_simplex h_interior_0 y < ε := by
    rcases lt_or_eq_of_le hy_mem with hy_pos | hy_eq
    · have h := h_τmono hy_mem (le_of_lt h_σε_pos) hy_lt_σε
      rwa [h_τσε] at h
    · -- y = 0
      rw [← hy_eq, h_τ0]; exact hε
  -- So |τ y| = τ y < ε.
  have habs_eq : |cf24_tau x0 h_nn h_simplex h_interior_0 y| =
      cf24_tau x0 h_nn h_simplex h_interior_0 y := abs_of_nonneg h_τy_nn
  rw [habs_eq]; exact h_τy_lt

/-- **Right-derivative of τ at 0.**  Direct slope-limit proof via the
characterization `HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s\{x}] x) (𝓝 f')`.

The key idea: for `y > 0` close to `0`, write `t = τ y`.  Then `t > 0`,
`σ t = y`, and `slope τ 0 y = (τ y - τ 0)/(y - 0) = t / σ t`.  Since
`σ t / t → 4/(x0 0)²` as `t → 0+` (i.e. `slope σ 0 t → 4/(x0 0)²`), we get
`t / σ t → (x0 0)²/4`.  Compose with `τ` continuous at `0` from the right
(plus `τ y > 0` for `y > 0`) to conclude. -/
theorem cf24_tau_hasDerivWithinAt_zero
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    HasDerivWithinAt (cf24_tau x0 h_nn h_simplex h_interior_0)
      ((x0 0)^2 / 4) (Set.Ici (0 : ℝ)) 0 := by
  -- Local short names for readability.
  let τ : ℝ → ℝ := cf24_tau x0 h_nn h_simplex h_interior_0
  let σ : ℝ → ℝ := cf24_sigma x0 h_nn h_simplex
  -- Hypotheses stated in terms of τ, σ (definitionally fine via let-zeta).
  have h_τ0 : τ 0 = 0 := cf24_tau_zero h_nn h_simplex h_interior_0
  have h_σ0 : σ 0 = 0 := cf24_sigma_zero h_nn h_simplex
  change HasDerivWithinAt τ ((x0 0)^2 / 4) (Set.Ici (0 : ℝ)) 0
  -- σ has right-derivative 4/(x0 0)^2 at 0.
  have h_σ_deriv :
      HasDerivWithinAt σ (4 / (x0 0)^2) (Set.Ici (0 : ℝ)) 0 :=
    cf24_sigma_hasDerivWithinAt_zero h_nn h_simplex h_interior_0
  have h_x00_sq_pos : 0 < (x0 0)^2 := pow_pos h_interior_0 2
  have h_f'_pos : (0 : ℝ) < 4 / (x0 0)^2 := by positivity
  have h_f'_ne : (4 / (x0 0)^2 : ℝ) ≠ 0 := ne_of_gt h_f'_pos
  -- Convert σ-derivative to slope tendsto on Ioi 0.
  -- `Ici 0 \ {0} = Ioi 0`, so the slope filter is `𝓝[Ioi 0] 0`.
  have h_slope_σ :
      Filter.Tendsto (slope σ 0) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (4 / (x0 0)^2)) := by
    have hh := hasDerivWithinAt_iff_tendsto_slope.mp h_σ_deriv
    -- hh : Tendsto (slope σ 0) (𝓝[Ici 0 \ {0}] 0) (𝓝 _).
    rwa [show (Set.Ici (0 : ℝ)) \ {0} = Set.Ioi 0 from Set.Ici_diff_left] at hh
  -- For t > 0, slope σ 0 t = (σ t - σ 0)/(t - 0) = σ t / t.
  -- Hence (slope σ 0 t) → 4/(x0 0)² as t → 0+, i.e. σ t / t → 4/(x0 0)².
  -- Take inverse: t / σ t → (x0 0)²/4 as t → 0+.
  have h_inv :
      Filter.Tendsto (fun t => t / σ t) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 ((x0 0)^2 / 4)) := by
    have h_eq : ((4 / (x0 0)^2) : ℝ)⁻¹ = (x0 0)^2 / 4 := inv_div _ _
    have h_inv_tendsto :
        Filter.Tendsto (fun t => (slope σ 0 t)⁻¹) (𝓝[Set.Ioi (0 : ℝ)] 0)
          (𝓝 ((4 / (x0 0)^2)⁻¹)) :=
      h_slope_σ.inv₀ h_f'_ne
    rw [h_eq] at h_inv_tendsto
    -- Show the inverse-of-slope agrees with t / σ t on Ioi 0.
    apply h_inv_tendsto.congr'
    refine Filter.eventually_of_mem self_mem_nhdsWithin ?_
    intro t ht
    simp only [Set.mem_Ioi] at ht
    change (slope σ 0 t)⁻¹ = t / σ t
    -- slope σ 0 t = (σ t - σ 0)/(t - 0) = σ t / t.
    have h1 : slope σ 0 t = σ t / t := by
      rw [slope_def_field, h_σ0, sub_zero, sub_zero]
    rw [h1, inv_div]
  -- τ takes 𝓝[Ioi 0] 0 into 𝓝[Ioi 0] 0: τ is right-continuous at 0,
  -- with τ 0 = 0, and τ y > 0 for y > 0 (strict mono on Ici 0, plus τ 0 = 0).
  have h_τ_cwa : ContinuousWithinAt τ (Set.Ici (0 : ℝ)) 0 :=
    cf24_tau_continuousWithinAt_zero h_nn h_simplex h_interior_0
  have h_τmono := cf24_tau_strictMonoOn h_nn h_simplex h_interior_0
  -- τ tendsto on Ioi 0:
  have h_τ_tendsto_Ioi :
      Filter.Tendsto τ (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝[Set.Ioi (0 : ℝ)] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · -- Tendsto τ (𝓝[Ioi 0] 0) (𝓝 0): from continuity within Ici 0 + Ioi ⊆ Ici.
      have h_τ_tendsto :
          Filter.Tendsto τ (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (τ 0)) := h_τ_cwa
      have h_mono : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝[Set.Ici (0 : ℝ)] 0 :=
        nhdsWithin_mono _ Set.Ioi_subset_Ici_self
      have := h_τ_tendsto.mono_left h_mono
      rw [h_τ0] at this; exact this
    · -- Eventually τ y ∈ Ioi 0 for y ∈ Ioi 0: use strict mono of τ.
      refine Filter.eventually_of_mem self_mem_nhdsWithin ?_
      intro y hy
      simp only [Set.mem_Ioi] at hy ⊢
      change 0 < τ y
      have h0_le : (0 : ℝ) ≤ 0 := le_refl 0
      have hy_le : (0 : ℝ) ≤ y := le_of_lt hy
      have h : τ 0 < τ y := h_τmono h0_le hy_le hy
      rw [h_τ0] at h; exact h
  -- Compose: slope τ 0 y = τ y / y for y ≠ 0, and we'll show
  -- τ y / y = t / σ t where t = τ y on Ioi 0 (use σ τ y = y).
  have h_slope_τ :
      Filter.Tendsto (slope τ 0) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 ((x0 0)^2 / 4)) := by
    -- (fun t => t / σ t) ∘ τ → (x0 0)²/4 as y → 0 in Ioi.
    have h_comp := h_inv.comp h_τ_tendsto_Ioi
    -- h_comp : Tendsto ((fun t => t / σ t) ∘ τ) (𝓝[Ioi 0] 0) (𝓝 ((x0 0)²/4))
    apply h_comp.congr'
    refine Filter.eventually_of_mem self_mem_nhdsWithin ?_
    intro y hy
    simp only [Set.mem_Ioi] at hy
    -- Goal: (fun t => t / σ t) (τ y) = slope τ 0 y, i.e. τ y / σ (τ y) = (τ y - τ 0)/(y - 0).
    have h_στy : σ (τ y) = y :=
      cf24_sigma_tau h_nn h_simplex h_interior_0 y (le_of_lt hy)
    change τ y / σ (τ y) = slope τ 0 y
    rw [h_στy, slope_def_field, h_τ0, sub_zero, sub_zero]
  -- Conclude via the slope characterization.
  rw [hasDerivWithinAt_iff_tendsto_slope]
  rw [show (Set.Ici (0 : ℝ)) \ {0} = Set.Ioi 0 from Set.Ici_diff_left]
  exact h_slope_τ

/-- **Chain rule packaged.**  The composed map `cf24LambdaEmbed ∘ traj ∘ τ`
has derivative `r2Field (cf24LambdaEmbed (traj (τ s)))` at every `s > 0`. -/
theorem cf24_r2_reparam_hasDerivAt
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun s' => cf24LambdaEmbed
        ((cf24_global_solution x0 h_nn h_simplex).trajectory
          (cf24_tau x0 h_nn h_simplex h_interior_0 s')))
      (r2Field (cf24LambdaEmbed
        ((cf24_global_solution x0 h_nn h_simplex).trajectory
          (cf24_tau x0 h_nn h_simplex h_interior_0 s)))) s := by
  set τ := cf24_tau x0 h_nn h_simplex h_interior_0 with hτ_def
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  have hs_nn : (0 : ℝ) ≤ s := le_of_lt hs
  have h_τs_nn : 0 ≤ τ s := cf24_tau_nonneg h_nn h_simplex h_interior_0 s hs_nn
  have h_τ_deriv :
      HasDerivAt τ ((sol.trajectory (τ s) 0)^2 / 4) s :=
    cf24_tau_hasDerivAt h_nn h_simplex h_interior_0 hs
  have h_traj_deriv :
      HasDerivAt (fun u => sol.trajectory u) (field (sol.trajectory (τ s))) (τ s) :=
    sol.is_solution (τ s) h_τs_nn
  have h_embed_deriv :
      HasDerivAt (fun u => cf24LambdaEmbed (sol.trajectory u))
        (lambdaField (cf24LambdaEmbed (sol.trajectory (τ s)))) (τ s) :=
    cf24LambdaEmbed_hasDerivAt h_traj_deriv
  have h_comp :=
    HasDerivAt.scomp s h_embed_deriv h_τ_deriv
  -- h_comp : HasDerivAt (fun s' => cf24LambdaEmbed (sol.trajectory (τ s')))
  --           ((traj (τ s) 0)²/4 • lambdaField (cf24LambdaEmbed (traj (τ s)))) s
  have h_val_eq :
      (((sol.trajectory (τ s) 0)^2 / 4) •
          (lambdaField (cf24LambdaEmbed (sol.trajectory (τ s))) : Fin 4 → ℝ))
        = r2Field (cf24LambdaEmbed (sol.trajectory (τ s))) := by
    funext i
    simp only [r2Field, cf24LambdaEmbed, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h_val_eq] at h_comp
  exact h_comp

/-- **Chain rule packaged at `s = 0`.**  At the endpoint, τ has only a
right-derivative; we use `HasDerivAt.scomp_hasDerivWithinAt` to combine
the (full) HasDerivAt of the embedded trajectory with the (within)
right-derivative of τ. -/
theorem cf24_r2_reparam_hasDerivWithinAt_zero
    {x0 : Fin 3 → ℝ} (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) :
    HasDerivWithinAt
      (fun s' => cf24LambdaEmbed
        ((cf24_global_solution x0 h_nn h_simplex).trajectory
          (cf24_tau x0 h_nn h_simplex h_interior_0 s')))
      (r2Field (cf24LambdaEmbed
        ((cf24_global_solution x0 h_nn h_simplex).trajectory
          (cf24_tau x0 h_nn h_simplex h_interior_0 0)))) (Set.Ici 0) 0 := by
  set τ := cf24_tau x0 h_nn h_simplex h_interior_0 with hτ_def
  set sol := cf24_global_solution x0 h_nn h_simplex with hsol_def
  have h_τ0 : τ 0 = 0 := cf24_tau_zero h_nn h_simplex h_interior_0
  -- Right-derivative of τ at 0 with value (x0 0)^2 / 4 = (sol.trajectory 0 0)^2 / 4.
  have h_traj0 : sol.trajectory 0 = x0 := sol.init_cond
  have h_x00_eq : sol.trajectory 0 0 = x0 0 := by rw [h_traj0]
  have h_τ_deriv :
      HasDerivWithinAt τ ((x0 0)^2 / 4) (Set.Ici (0 : ℝ)) 0 :=
    cf24_tau_hasDerivWithinAt_zero h_nn h_simplex h_interior_0
  -- HasDerivAt of the trajectory at τ 0 = 0 (using sol.is_solution at t = 0).
  have h_traj_deriv :
      HasDerivAt (fun u => sol.trajectory u) (field (sol.trajectory 0)) 0 :=
    sol.is_solution 0 (le_refl 0)
  have h_embed_deriv :
      HasDerivAt (fun u => cf24LambdaEmbed (sol.trajectory u))
        (lambdaField (cf24LambdaEmbed (sol.trajectory 0))) 0 :=
    cf24LambdaEmbed_hasDerivAt h_traj_deriv
  -- Replace the base point τ 0 by 0 in the within-derivative.
  have h_τ_deriv' :
      HasDerivWithinAt τ ((sol.trajectory (τ 0) 0)^2 / 4) (Set.Ici (0 : ℝ)) 0 := by
    have h_eq : (sol.trajectory (τ 0) 0)^2 / 4 = (x0 0)^2 / 4 := by
      rw [h_τ0, h_x00_eq]
    rw [h_eq]; exact h_τ_deriv
  -- Apply chain rule: HasDerivAt at τ 0, HasDerivWithinAt at 0.
  have h_embed_deriv' :
      HasDerivAt (fun u => cf24LambdaEmbed (sol.trajectory u))
        (lambdaField (cf24LambdaEmbed (sol.trajectory (τ 0)))) (τ 0) := by
    rw [h_τ0]; exact h_embed_deriv
  have h_comp :
      HasDerivWithinAt
        ((fun u => cf24LambdaEmbed (sol.trajectory u)) ∘ τ)
        (((sol.trajectory (τ 0) 0)^2 / 4) •
          (lambdaField (cf24LambdaEmbed (sol.trajectory (τ 0))) : Fin 4 → ℝ))
        (Set.Ici (0 : ℝ)) 0 :=
    h_embed_deriv'.scomp_hasDerivWithinAt 0 h_τ_deriv'
  have h_val_eq :
      (((sol.trajectory (τ 0) 0)^2 / 4) •
          (lambdaField (cf24LambdaEmbed (sol.trajectory (τ 0))) : Fin 4 → ℝ))
        = r2Field (cf24LambdaEmbed (sol.trajectory (τ 0))) := by
    funext i
    simp only [r2Field, cf24LambdaEmbed, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h_val_eq] at h_comp
  exact h_comp

/-- **r²-trick time reparametrization hypothesis** (Layer 3 Prop 11.5).

The r²-trick multiplies every λ-trick velocity by `r² = (z 0)²`, slowing
down time by that factor.  Concretely, if `z(t)` is a λ-trick orbit with
`z(t) 0 → α > 0` (which is the case for CF'24 — we have `z(t) 0 = z_00/2`
and `z_00 → (7+3√5)/18 > 0`), the reparametrization solving
  `dτ/ds = (z(τ(s)) 0)²`,  τ(0) = 0
yields a strictly increasing `τ : [0, ∞) → [0, ∞)` with `τ → ∞` (since
`(z 0)²` is bounded below from some `T₀` onward).  The reparametrized
orbit `w(s) := z(τ(s))` then solves `w'(s) = r2Field(w(s))`.

The derivative clause is stated for all `s ≥ 0` (right-derivative at
the endpoint `s = 0`); see `cf24_r2_reparam_hasDerivWithinAt_zero` for
the endpoint case. -/
def Cf24R2Reparam : Prop :=
  ∀ (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1),
    0 < x0 0 → 0 < x0 1 → 0 < x0 2 →
    ∃ τ : ℝ → ℝ,
      τ 0 = 0 ∧
      (∀ s, 0 ≤ s → 0 ≤ τ s) ∧
      Filter.Tendsto τ Filter.atTop Filter.atTop ∧
      (∀ s, 0 ≤ s → HasDerivWithinAt
        (fun s' => cf24LambdaEmbed
          ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s')))
        (r2Field (cf24LambdaEmbed
          ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)))) (Set.Ici 0) s)

/-- **Discharge of `Cf24R2Reparam`.**  `τ := σ⁻¹` (the construction
`cf24_tau`) satisfies all four clauses: initial value 0, non-negativity,
divergence to infinity, and the chain-rule derivative clause for all
`s ≥ 0` (using the right-derivative of τ at `s = 0`). -/
theorem cf24_r2_reparam : Cf24R2Reparam := by
  intro x0 h_nn h_simplex h0 _ _
  refine ⟨cf24_tau x0 h_nn h_simplex h0,
    cf24_tau_zero h_nn h_simplex h0,
    cf24_tau_nonneg h_nn h_simplex h0,
    cf24_tau_tendsto_atTop h_nn h_simplex h0,
    ?_⟩
  intro s hs
  rcases lt_or_eq_of_le hs with hs_pos | hs_eq
  · exact (cf24_r2_reparam_hasDerivAt h_nn h_simplex h0 hs_pos).hasDerivWithinAt
  · -- s = 0
    rw [← hs_eq]
    exact cf24_r2_reparam_hasDerivWithinAt_zero h_nn h_simplex h0

/-- **r²-trick lift of corrected Step 5**, under the basin hypothesis `Cf24SaddleExcludedBasinEntry` plus the saddle-stable
exclusion `h_not_saddle_stable`. -/
theorem cf24_r2_lifted_readout_of_saddleExcludedBasinEntry
    (h_basin' : Cf24SaddleExcludedBasinEntry) (h_reparam : Cf24R2Reparam)
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) (h_interior_1 : 0 < x0 1)
    (h_interior_2 : 0 < x0 2)
    (h_not_saddle_stable :
      ¬ Filter.Tendsto
          (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t)
          Filter.atTop (nhds saddlePoint)) :
    ∃ τ : ℝ → ℝ,
      (∀ s, 0 ≤ s → 0 ≤ τ s) ∧
      Filter.Tendsto τ Filter.atTop Filter.atTop ∧
      (∀ s, 0 ≤ s → HasDerivWithinAt
        (fun s' => cf24LambdaEmbed
          ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s')))
        (r2Field (cf24LambdaEmbed
          ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)))) (Set.Ici 0) s) ∧
      Filter.Tendsto
        (fun s =>
          cf24LambdaEmbed
            ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 3
          + cf24LambdaEmbed
              ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 2 / 2)
        Filter.atTop (nhds readoutLimit) := by
  obtain ⟨τ, _, hτ_nn, hτ_atTop, hτ_deriv⟩ :=
    h_reparam x0 h_nn h_simplex h_interior_0 h_interior_1 h_interior_2
  refine ⟨τ, hτ_nn, hτ_atTop, hτ_deriv, ?_⟩
  exact (cf24_lambda_lifted_readout_of_saddleExcludedBasinEntry h_basin' x0 h_nn h_simplex
    h_interior_0 h_interior_1 h_interior_2 h_not_saddle_stable).comp hτ_atTop

/-- **NAP-20 lift of corrected Step 5**, using `Cf24SaddleExcludedBasinEntry` and the saddle-stable exclusion. -/
theorem cf24_nap20_lifted_readout_of_saddleExcludedBasinEntry
    (h_basin' : Cf24SaddleExcludedBasinEntry) (h_reparam : Cf24R2Reparam)
    (x0 : Fin 3 → ℝ) (h_nn : ∀ i, 0 ≤ x0 i) (h_simplex : ∑ i, x0 i = 1)
    (h_interior_0 : 0 < x0 0) (h_interior_1 : 0 < x0 1)
    (h_interior_2 : 0 < x0 2)
    (h_not_saddle_stable :
      ¬ Filter.Tendsto
          (fun t => (cf24_global_solution x0 h_nn h_simplex).trajectory t)
          Filter.atTop (nhds saddlePoint)) :
    ∃ τ : ℝ → ℝ,
      Filter.Tendsto τ Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun s => ∑ i, readoutCoeff i * cubedLift i
          (cf24LambdaEmbed
            ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s))))
        Filter.atTop (nhds readoutLimit) := by
  obtain ⟨τ, hτ_nn, hτ_atTop, _, h_readout⟩ :=
    cf24_r2_lifted_readout_of_saddleExcludedBasinEntry h_basin' h_reparam x0 h_nn h_simplex
      h_interior_0 h_interior_1 h_interior_2 h_not_saddle_stable
  refine ⟨τ, hτ_atTop, ?_⟩
  have h_eq : ∀ s, 0 ≤ s →
      (∑ i, readoutCoeff i * cubedLift i
          (cf24LambdaEmbed
            ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s))))
        = cf24LambdaEmbed
            ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 3
          + cf24LambdaEmbed
              ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 2 / 2 := by
    intro s hs
    have hτs : 0 ≤ τ s := hτ_nn s hs
    have hPi : ∑ i, (cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) i = 1 :=
      conservative_trajectory_simplex
        (cf24_global_solution x0 h_nn h_simplex)
        field_conservative
        (by simpa [cf24PIVP] using h_simplex)
        hτs
    have h3 : (cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 0
             + (cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 1
             + (cf24_global_solution x0 h_nn h_simplex).trajectory (τ s) 2 = 1 := by
      simpa [Fin.sum_univ_three] using hPi
    have hsum :
        cf24LambdaEmbed
            ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 0
          + cf24LambdaEmbed
              ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 1
          + cf24LambdaEmbed
              ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 2
          + cf24LambdaEmbed
              ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 3 = 1 := by
      have hA := cf24LambdaEmbed_sum
        ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s))
      simp [Fin.sum_univ_four] at hA
      linarith [h3]
    exact readout_eq_z11_plus_half_z01 _ hsum
  have hEv :
      (fun s => ∑ i, readoutCoeff i * cubedLift i
          (cf24LambdaEmbed
            ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s))))
        =ᶠ[Filter.atTop]
      (fun s =>
        cf24LambdaEmbed
          ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 3
        + cf24LambdaEmbed
            ((cf24_global_solution x0 h_nn h_simplex).trajectory (τ s)) 2 / 2) := by
    refine Filter.eventually_atTop.mpr ⟨0, ?_⟩
    intro s hs; exact h_eq s hs
  exact h_readout.congr' hEv.symm

/-! ### Layer 3 status

Closed:
  * λ-trick algebraic embedding (`cf24LambdaEmbed`,
    `lambdaField_eq_cf24Embed`, `cf24LambdaEmbed_sum`,
    `cf24LambdaEmbed_readout`).
  * λ-trick HasDerivAt transport (`cf24LambdaEmbed_hasDerivAt`).
  * λ-trick readout-limit preservation (`cf24Lambda_readout_tendsto`).
  * NAP-20 row-by-row chain rule (`cubedLift_0_hasDerivAt` …
    `cubedLift_19_hasDerivAt`, packaged as `cubedLift_hasDerivAt`).
  * r²-trick lift via reparametrization
    (`Cf24R2Reparam` — now fully discharged by `cf24_r2_reparam`).
  * Part C σ/τ chain rule (`cf24_sigma_hasDerivAt`,
    `cf24_tau_hasDerivAt`, `cf24_sigma_hasDerivWithinAt_zero`,
    `cf24_tau_hasDerivWithinAt_zero`, `cf24_r2_reparam_hasDerivAt`,
    `cf24_r2_reparam_hasDerivWithinAt_zero`, `cf24_r2_reparam`):
    `τ = σ⁻¹` with σ(t) = ∫₀ᵗ 4/(z 0)² du has derivative (z 0 (τ s))²/4
    at all s ≥ 0 (right-derivative at the endpoint), yielding the
    r²-trick ODE for cf24LambdaEmbed ∘ traj ∘ τ.
  * NAP-20 readout transport (`readout_eq_z11_plus_half_z01`): the
    cubed-manifold readout `Σ readoutCoeff · cubedLift` equals the λ-trick
    readout on the 4-simplex.

The paper's claim, from the canonical initial condition `(1, 0, 0)`, is proved
without hypotheses in `Ripple/LPP/CF24Canonical.lean` (`cf24_readout_canonical`,
`cf24_lambda_readout_canonical`, `cf24_r2_readout_canonical`,
`cf24_nap20_readout_canonical`).  The former `…_of_basinEntry` theorems were
deleted: their hypothesis `Cf24BasinEntry` is false (`cf24_basinEntry_false`).

Open (not claimed by the paper): `Cf24SaddleExcludedBasinEntry`, basin entry
from every interior initial condition off the saddle's stable manifold.

Discharged:
  * `Cf24R2Reparam` — fully discharged by `cf24_r2_reparam` using
    σ = ∫₀ᵗ 4/(z 0)² du and τ = σ⁻¹, with the derivative clause stated
    for all `s ≥ 0`, including the right-derivative at the endpoint
    `s = 0` (built from the one-sided FTC for σ at 0 and the
    `HasFDerivWithinAt.of_local_left_inverse` form of the inverse
    function theorem). -/

end CF24
end Ripple
