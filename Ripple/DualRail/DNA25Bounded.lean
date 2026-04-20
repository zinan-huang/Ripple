/-
  Ripple.DualRail.DNA25Bounded — DNA 25 / [RTCRN2] polynomial-scale dual-rail
  boundedness theorem.

  This file formalizes the core bounded-existence result for the DNA 25
  polynomial-scale dual-rail construction `polynomialScaleDualRail`, namely:

    Given a zero-init `BoundedTimeComputable d α` whose field is a
    polynomial `p : Fin d → MvPolynomial (Fin d) ℚ`, the 2·d-dimensional
    dual-rail PIVP

      u_j' = p̂⁺_j − u_j·v_j·(p̂⁺_j + p̂⁻_j)
      v_j' = p̂⁻_j − u_j·v_j·(p̂⁺_j + p̂⁻_j)

    with zero initial data admits a `PIVP.Solution` whose trajectories
    are non-negative, bounded, and satisfy the dual-rail identity
    `u_j(t) − v_j(t) = y_j(t)` where `y` is the original trajectory.

  ## Proof structure

  The paper's proof (p.11 of [RTCRN2]) is a hand-wavy contradiction:
  "if u_i or v_i were unbounded, then both would be unbounded (since
  u_i − v_i = y_i is bounded), but the annihilation term −u_i v_i (p̂⁺+p̂⁻)
  dominates". We promote this sketch to a rigorous **barrier argument**
  (per Xiang's description, non-barrier — the auxiliary variable
  `s_j := u_j + v_j` defines a forward-invariant region `{s_j ≤ √(2+β²)}`
  whose boundary is crossed only outward-to-inward, by direct sign analysis
  of `s_j'`).

  ### Barrier structure.

  Let `s_j := u_j + v_j` and `w_j := u_j − v_j`. From the ODE:

    s_j' = (p̂⁺_j + p̂⁻_j) · (1 − 2·u_j·v_j)
         = (p̂⁺_j + p̂⁻_j) · (1 − (s_j² − w_j²)/2)                     (*)
    w_j' = p̂⁺_j − p̂⁻_j = p_j(w)   (so w_j = y_j if w(0) = 0)

  When `s_j > √(2 + w_j²)`, the factor `(1 − (s_j² − w_j²)/2) < 0`, and
  since `(p̂⁺_j + p̂⁻_j) ≥ 0` pointwise (non-negative coefficients on a
  non-negative state), we get `s_j' ≤ 0`. Hence `s_j(t) ≤ √(2 + β²)`
  whenever `|w_j(t)| ≤ β` and `s_j(0) = 0`.

  Since `u_j, v_j ≥ 0` (CRN non-negativity, by `crn_trajectory_nonneg`
  applied to `polynomialScaleDualRail_pcd`) and `u_j + v_j ≤ √(2 + β²)`,
  each of `u_j, v_j` is individually bounded by `√(2 + β²)`.

  ### Structure of the Lean proof.

  This file provides:

  * `polynomialScaleDualRail_field_expansion` — algebraic identity
    expressing the field of `polynomialScaleDualRail` in terms of
    `dualRailPosPart`, `dualRailNegPart`, and the `u·v·…` annihilation.
  * `polynomialScaleDualRail_bounded` — the main theorem, as stated above.

  The analytic core — "s_j is a priori bounded by √(2+β²) along any local
  solution with matching dual-rail identity, given input bound β" — is
  the classical barrier scalar-barrier argument, identical in spirit to
  `scalar_cubic_sigma_bound_local` in `ScalarCubic.lean` but in a multi-
  dimensional setting where every coordinate s_j enjoys an independent
  barrier. That invariant is packaged here as `dna25_apriori_bound` and
  invoked via `locally_lipschitz_bounded_global_ode_proved_continuous`
  to produce the global solution.

  **Status (2026-04-20): fully proved, axiom trace
  `[propext, Classical.choice, Quot.sound]`.**

  Reference: [RTCRN2] Huang–Klinge–Lathrop, "Real-Time Equivalence of CRNs
  and Analog Computers", DNA 25 (2019), Theorem 2, p. 11.
-/

import Ripple.DualRail.ConstantAnnihilation
import Ripple.DualRail.BTCReduction
import Ripple.Core.ODEGlobal
import Ripple.Core.ZeroInitPositivity

namespace Ripple
namespace DualRail

open MvPolynomial Set Ripple

/-! ## The per-coordinate barrier structure

We expose two computed quantities:

  `dnaLyapSum` := `u_j + v_j`       -- the "s" variable
  `dnaLyapDiff` := `u_j − v_j`      -- the "w" variable (equals `y_j`)

Their differential behaviour along the ODE gives the barrier bound. -/

/-- **Algebraic identity for the `polynomialScaleDualRail` field, even row
(`k = 2j`, the `u_j` row).**

The field value at state `w : Fin (2·d) → ℝ` is

  `p̂⁺_j(w) − w_{2j} · w_{2j+1} · (p̂⁺_j(w) + p̂⁻_j(w))`

where the positive/negative parts are evaluated at `w`. -/
theorem polynomialScaleDualRail_field_u {d : ℕ} [NeZero d]
    (p : Fin d → MvPolynomial (Fin d) ℚ) (j : Fin d)
    (w : Fin (2 * d) → ℝ) :
    (polynomialScaleDualRail d p).toPIVP.field w ⟨2 * j.val, by omega⟩
      = (dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) w
        - w ⟨2 * j.val, by omega⟩ * w ⟨2 * j.val + 1, by omega⟩
          * ((dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) w
              + (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) w) := by
  -- Evaluate the polynomial at the state vector and simplify the `if`.
  show (polynomialScaleDualRail d p).evalField w ⟨2 * j.val, by omega⟩ = _
  unfold PolyPIVP.evalField polynomialScaleDualRail
  -- The field component for k = ⟨2j, _⟩: k.val = 2j so k.val % 2 = 0 and k.val / 2 = j.
  have hk_mod : (2 * j.val) % 2 = 0 := by omega
  have hk_div : (2 * j.val) / 2 = j.val := by omega
  simp only [show ((2 * j.val) % 2 = 0 : Bool) = true from by
    simp [hk_mod], if_true]
  -- The `i` inside the def is ⟨(2j)/2, _⟩ = ⟨j, _⟩.
  have hi_eq : (⟨(2 * j.val) / 2, by
      have : 2 * j.val < 2 * d := by have := j.isLt; omega
      omega⟩ : Fin d) = j := by
    apply Fin.ext; show (2 * j.val) / 2 = j.val; omega
  rw [hi_eq]
  -- Evaluate the resulting polynomial expression.
  simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_X]
  have hfix1 : (⟨2 * (2 * j.val / 2), by
      have : 2 * j.val < 2 * d := by have := j.isLt; omega
      omega⟩ : Fin (2 * d)) = ⟨2 * j.val, by omega⟩ := by
    apply Fin.ext; show 2 * (2 * j.val / 2) = 2 * j.val; omega
  have hfix2 : (⟨2 * (2 * j.val / 2) + 1, by
      have : 2 * j.val + 1 < 2 * d := by have := j.isLt; omega
      omega⟩ : Fin (2 * d)) = ⟨2 * j.val + 1, by omega⟩ := by
    apply Fin.ext; show 2 * (2 * j.val / 2) + 1 = 2 * j.val + 1; omega
  rw [hfix1, hfix2]

/-- **Algebraic identity for the `polynomialScaleDualRail` field, odd row
(`k = 2j+1`, the `v_j` row).** -/
theorem polynomialScaleDualRail_field_v {d : ℕ} [NeZero d]
    (p : Fin d → MvPolynomial (Fin d) ℚ) (j : Fin d)
    (w : Fin (2 * d) → ℝ) :
    (polynomialScaleDualRail d p).toPIVP.field w ⟨2 * j.val + 1, by omega⟩
      = (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) w
        - w ⟨2 * j.val, by omega⟩ * w ⟨2 * j.val + 1, by omega⟩
          * ((dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) w
              + (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) w) := by
  show (polynomialScaleDualRail d p).evalField w ⟨2 * j.val + 1, by omega⟩ = _
  unfold PolyPIVP.evalField polynomialScaleDualRail
  have hk_mod : (2 * j.val + 1) % 2 = 1 := by omega
  have hk_mod_ne : ¬ (2 * j.val + 1) % 2 = 0 := by omega
  have hk_div : (2 * j.val + 1) / 2 = j.val := by omega
  simp only [show ((2 * j.val + 1) % 2 = 0 : Bool) = false from by
    simp [hk_mod], if_false, Bool.false_eq_true]
  have hi_eq : (⟨(2 * j.val + 1) / 2, by
      have : 2 * j.val + 1 < 2 * d := by have := j.isLt; omega
      omega⟩ : Fin d) = j := by
    apply Fin.ext; show (2 * j.val + 1) / 2 = j.val; omega
  rw [hi_eq]
  simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_X]
  have hfix1 : (⟨2 * ((2 * j.val + 1) / 2), by
      have : 2 * j.val < 2 * d := by have := j.isLt; omega
      omega⟩ : Fin (2 * d)) = ⟨2 * j.val, by omega⟩ := by
    apply Fin.ext; show 2 * ((2 * j.val + 1) / 2) = 2 * j.val; omega
  have hfix2 : (⟨2 * ((2 * j.val + 1) / 2) + 1, by
      have : 2 * j.val + 1 < 2 * d := by have := j.isLt; omega
      omega⟩ : Fin (2 * d)) = ⟨2 * j.val + 1, by omega⟩ := by
    apply Fin.ext; show 2 * ((2 * j.val + 1) / 2) + 1 = 2 * j.val + 1; omega
  rw [hfix1, hfix2]

/-! ## The barrier a priori bound (analytic core).

The single analytic obstacle for the DNA 25 theorem: any local solution of
the `polynomialScaleDualRail` field, starting at zero, with pairwise
differences tracking `y_j(t) = btc.sol.trajectory t j`, is uniformly bounded
on its domain by `M := √(2 + β²) + 1`.

Informal proof: let `s_j(t) := sol t ⟨2j,_⟩ + sol t ⟨2j+1,_⟩` (the "sum" rail)
and `w_j(t) := sol t ⟨2j,_⟩ − sol t ⟨2j+1,_⟩` (the "difference" rail). Using
the per-row field identities (`polynomialScaleDualRail_field_u`,
`polynomialScaleDualRail_field_v`), the sum satisfies the scalar ODE

  s_j' = (p̂⁺_j(sol t) + p̂⁻_j(sol t)) · (1 − 2·u_j·v_j)
       = (p̂⁺_j + p̂⁻_j) · (1 − (s_j² − w_j²)/2)

Because `p̂⁺_j, p̂⁻_j ≥ 0` whenever `sol ≥ 0` (which CRN non-negativity
guarantees on the trajectory), and `|w_j(t)| = |y_j(t)| ≤ β` by the dual-rail
identity, the region `{s_j ≤ √(2 + β²)}` is forward-invariant (the drift
factor `(1 − (s² − w²)/2)` becomes non-positive once `s² ≥ 2 + w²`). So
`s_j(t) ≤ √(2 + β²)`. Combined with non-negativity (each of u_j, v_j ≥ 0),
this yields `u_j(t), v_j(t) ≤ s_j(t) ≤ √(2 + β²) < M`.

Formalization status. **PROVED**. The 2d-dimensional barrier argument
is implemented below using the dual-rail identity (to get `|w_j| ≤ β`
from `btc.bounded`) plus CRN non-negativity (`crn_local_nonneg` applied
to `polynomialScaleDualRail_pcd`). The per-coordinate forward-invariance
is discharged by a direct last-exit-time argument (`sSup`) combined
with `antitoneOn_of_hasDerivWithinAt_nonpos`. -/
/-- Auxiliary: the combined sum `s_j(t) := y t ⟨2j,_⟩ + y t ⟨2j+1,_⟩` has
derivative `(p̂⁺_j + p̂⁻_j)(y t) · (1 − 2·u_j·v_j)` along any local solution
of `polynomialScaleDualRail`. -/
private lemma dna25_sum_has_deriv {d : ℕ} [NeZero d]
    (p : Fin d → MvPolynomial (Fin d) ℚ) (j : Fin d)
    {T : ℝ} (y : ℝ → Fin (2 * d) → ℝ)
    (h_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((polynomialScaleDualRail d p).toPIVP.field (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt (fun s => y s ⟨2 * j.val, by omega⟩ + y s ⟨2 * j.val + 1, by omega⟩)
        (((dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) (y t)
          + (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) (y t))
         * (1 - 2 * y t ⟨2 * j.val, by omega⟩ * y t ⟨2 * j.val + 1, by omega⟩)) t := by
  intro t ht
  have hy_t := h_deriv t ht
  have hy_coord : ∀ k : Fin (2 * d),
      HasDerivAt (fun s => y s k)
        ((polynomialScaleDualRail d p).toPIVP.field (y t) k) t :=
    hasDerivAt_pi.mp hy_t
  have h_u := hy_coord ⟨2 * j.val, by omega⟩
  have h_v := hy_coord ⟨2 * j.val + 1, by omega⟩
  have h_sum := h_u.add h_v
  -- Rewrite the sum of field values using the u/v row identities.
  have h_u_id := polynomialScaleDualRail_field_u p j (y t)
  have h_v_id := polynomialScaleDualRail_field_v p j (y t)
  have h_target :
      (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val, by omega⟩
        + (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val + 1, by omega⟩
      = ((dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) (y t)
          + (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) (y t))
        * (1 - 2 * y t ⟨2 * j.val, by omega⟩ * y t ⟨2 * j.val + 1, by omega⟩) := by
    rw [h_u_id, h_v_id]; ring
  rw [h_target] at h_sum
  exact h_sum

/-- **DNA 25 a priori bound (barrier argument).**

For any zero-init local solution `y` of `polynomialScaleDualRail d p` on
`[0, T)`, where the underlying `btc.sol.trajectory` is uniformly bounded by
`β`, each coordinate of `y` is bounded by `√(2 + β²)`, hence `‖y t‖ ≤ M`
for `M := √(2 + β²) + 1`. -/
private theorem dna25_apriori_bound {d : ℕ} [NeZero d] {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (h_field : ∀ y : Fin d → ℝ, ∀ i : Fin d,
        btc.pivp.field y i = (p i).eval₂ (Rat.castHom ℝ) y)
    (h_zero : ∀ j, btc.pivp.init j = 0)
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_bd : ∀ t, 0 ≤ t → ‖btc.sol.trajectory t‖ ≤ β)
    (M : ℝ) (hM : 0 < M)
    (hM_def : Real.sqrt (2 + β ^ 2) + 1 ≤ M)
    (T : ℝ) (hT : 0 < T) (y : ℝ → Fin (2 * d) → ℝ)
    (hy0 : y 0 = fun _ => 0)
    (h_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((polynomialScaleDualRail d p).toPIVP.field (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ M := by
  -- Key abbreviations.
  set σMax : ℝ := Real.sqrt (2 + β ^ 2) with hσMax_def
  have hσMax_nn : 0 ≤ σMax := Real.sqrt_nonneg _
  have hσMax_sq : σMax ^ 2 = 2 + β ^ 2 := by
    have hβsq_nn : 0 ≤ (2 + β ^ 2 : ℝ) := by positivity
    rw [hσMax_def]
    exact Real.sq_sqrt hβsq_nn
  -- The PIVP and its CRN decomposition.
  have hpcd : PolyCRNDecomposition (2 * d) (polynomialScaleDualRail d p) :=
    polynomialScaleDualRail_pcd d p
  have h_crn : IsCRNImplementable (2 * d)
      (polynomialScaleDualRail d p).toPIVP.field := hpcd.toIsCRNImplementable
  have h_lip := polyPIVP_field_locally_lipschitz (polynomialScaleDualRail d p)
  -- Step 1: non-negativity on [0, T).
  have h_init_nn : ∀ i : Fin (2 * d), 0 ≤ y 0 i := by
    intro i; rw [hy0]
  have h_nn : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ k : Fin (2 * d), 0 ≤ y t k :=
    crn_local_nonneg h_crn h_lip T hT y h_init_nn h_deriv
  -- Step 2: on any Icc 0 T' ⊂ [0, T), w_j(t) := y t ⟨2j,_⟩ − y t ⟨2j+1,_⟩ equals
  -- btc.sol.trajectory t j. Proof: w satisfies the same ODE w' = p(w) as
  -- btc.sol, with the same initial condition; apply ODE uniqueness.
  set w : ℝ → Fin d → ℝ :=
    fun t j => y t ⟨2 * j.val, by omega⟩ - y t ⟨2 * j.val + 1, by omega⟩ with hw_def
  -- Define the 1-dim-level polynomial field as a PolyPIVP.
  let P : PolyPIVP d :=
    { field := p, init := fun _ => 0, output := ⟨0, (NeZero.pos d)⟩ }
  have hP_field : ∀ v : Fin d → ℝ,
      P.toPIVP.field v = fun j => (p j).eval₂ (Rat.castHom ℝ) v := by
    intro v; funext j; rfl
  -- w has the expected derivative on [0, T).
  have hw_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt w (P.toPIVP.field (w t)) t := by
    intro t ht
    have hy_t := h_deriv t ht
    have hy_coord : ∀ k : Fin (2 * d),
        HasDerivAt (fun s => y s k)
          ((polynomialScaleDualRail d p).toPIVP.field (y t) k) t :=
      hasDerivAt_pi.mp hy_t
    rw [hasDerivAt_pi]
    intro j
    have h_u := hy_coord ⟨2 * j.val, by omega⟩
    have h_v := hy_coord ⟨2 * j.val + 1, by omega⟩
    have h_diff :
        HasDerivAt (fun s => y s ⟨2 * j.val, by omega⟩ - y s ⟨2 * j.val + 1, by omega⟩)
          ((polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val, by omega⟩
            - (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val + 1, by omega⟩) t :=
      h_u.sub h_v
    have h_u_id := polynomialScaleDualRail_field_u p j (y t)
    have h_v_id := polynomialScaleDualRail_field_v p j (y t)
    have h_sub_id :
        (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val, by omega⟩
          - (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val + 1, by omega⟩
        = (dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) (y t)
          - (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) (y t) := by
      rw [h_u_id, h_v_id]; ring
    have h_alg := dualRailPos_sub_dualRailNeg_eval d p j (y t)
    have h_target :
        (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val, by omega⟩
          - (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val + 1, by omega⟩
        = (p j).eval₂ (Rat.castHom ℝ) (w t) := by
      rw [h_sub_id, h_alg]
    rw [h_target] at h_diff
    show HasDerivAt (fun s => w s j) (P.toPIVP.field (w t) j) t
    have hPf : P.toPIVP.field (w t) j = (p j).eval₂ (Rat.castHom ℝ) (w t) := rfl
    rw [hPf]
    convert h_diff using 1
  have hw_init : w 0 = fun _ => 0 := by
    funext j
    show y 0 ⟨2 * j.val, by omega⟩ - y 0 ⟨2 * j.val + 1, by omega⟩ = 0
    rw [hy0]; simp
  -- btc.sol.trajectory satisfies the same ODE.
  have hz_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt btc.sol.trajectory (P.toPIVP.field (btc.sol.trajectory t)) t := by
    intro t ht
    have h := btc.sol.is_solution t ht
    have h_eq : btc.pivp.field (btc.sol.trajectory t)
        = P.toPIVP.field (btc.sol.trajectory t) := by
      funext i
      rw [h_field (btc.sol.trajectory t) i]
      rfl
    rw [← h_eq]; exact h
  have hz_init : btc.sol.trajectory 0 = fun _ => 0 := by
    have h := btc.sol.init_cond
    funext j; rw [h]; exact h_zero j
  have h_lip_P := polyPIVP_field_locally_lipschitz P
  -- For every T' ∈ (0, T), w and btc.sol.trajectory agree on Icc 0 T'.
  have hw_eq_btc : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ j : Fin d,
      w t j = btc.sol.trajectory t j := by
    intro t ht j
    rcases eq_or_lt_of_le ht.1 with ht_zero | ht_pos
    · subst ht_zero
      rw [hw_init, hz_init]
    · -- Use uniqueness on Icc 0 t.
      set T' : ℝ := t with hT'_def
      have hT'_pos : 0 < T' := ht_pos
      -- Continuity of w and btc.sol.trajectory on Icc 0 T'.
      have hw_cont : ContinuousOn w (Set.Icc 0 T') := by
        intro s hs
        refine (hw_deriv s ?_).continuousAt.continuousWithinAt
        exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      have hz_cont : ContinuousOn btc.sol.trajectory (Set.Icc 0 T') := by
        intro s hs
        exact (hz_deriv s hs.1).continuousAt.continuousWithinAt
      have h_Icc_ne : (Set.Icc (0 : ℝ) T').Nonempty := ⟨0, ⟨le_refl _, hT'_pos.le⟩⟩
      obtain ⟨u_w, _, hu_w_max⟩ :=
        isCompact_Icc.exists_isMaxOn h_Icc_ne hw_cont.norm
      obtain ⟨u_z, _, hu_z_max⟩ :=
        isCompact_Icc.exists_isMaxOn h_Icc_ne hz_cont.norm
      set R : ℝ := max ‖w u_w‖ ‖btc.sol.trajectory u_z‖ with hR_def
      have hR_nn : 0 ≤ R := le_max_of_le_left (norm_nonneg _)
      have hw_bd_R : ∀ s ∈ Set.Icc (0 : ℝ) T', ‖w s‖ ≤ R := fun s hs =>
        le_trans (hu_w_max hs) (le_max_left _ _)
      have hz_bd_R : ∀ s ∈ Set.Icc (0 : ℝ) T', ‖btc.sol.trajectory s‖ ≤ R := fun s hs =>
        le_trans (hu_z_max hs) (le_max_right _ _)
      have hw_dw : ∀ s ∈ Set.Icc (0 : ℝ) T',
          HasDerivWithinAt w (P.toPIVP.field (w s)) (Set.Icc 0 T') s := by
        intro s hs
        have hs_in : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
        exact (hw_deriv s hs_in).hasDerivWithinAt
      have hz_dw : ∀ s ∈ Set.Icc (0 : ℝ) T',
          HasDerivWithinAt btc.sol.trajectory
            (P.toPIVP.field (btc.sol.trajectory s)) (Set.Icc 0 T') s := fun s hs =>
        (hz_deriv s hs.1).hasDerivWithinAt
      have h_eqOn : Set.EqOn w btc.sol.trajectory (Set.Icc 0 T') :=
        solutions_agree_on_Icc hT'_pos hR_nn h_lip_P hw_init hz_init hw_dw hz_dw
          hw_bd_R hz_bd_R
      have ht_in : t ∈ Set.Icc (0 : ℝ) T' := ⟨ht.1, le_refl _⟩
      have h_eq_t : w t = btc.sol.trajectory t := h_eqOn ht_in
      exact congrArg (fun v => v j) h_eq_t
  -- Step 3: the barrier argument for each j.
  -- Claim: for all t ∈ Ico 0 T, y t ⟨2j,_⟩ + y t ⟨2j+1,_⟩ ≤ σMax.
  have h_barrier : ∀ j : Fin d, ∀ t ∈ Set.Ico (0 : ℝ) T,
      y t ⟨2 * j.val, by omega⟩ + y t ⟨2 * j.val + 1, by omega⟩ ≤ σMax := by
    intro j t ht
    set s_fun : ℝ → ℝ :=
      fun τ => y τ ⟨2 * j.val, by omega⟩ + y τ ⟨2 * j.val + 1, by omega⟩ with hs_def
    -- s_fun 0 = 0.
    have hs_init : s_fun 0 = 0 := by
      show y 0 ⟨2 * j.val, by omega⟩ + y 0 ⟨2 * j.val + 1, by omega⟩ = 0
      rw [hy0]; simp
    -- Contradiction approach: assume s_fun t > σMax.
    by_contra h_gt
    push_neg at h_gt
    -- Define the set where s_fun is "bad" (> σMax) on [0, t].
    -- By IVT / continuity, there's a last τ < t with s_fun τ = σMax,
    -- and on (τ, t], s_fun > σMax ⇒ s_fun' ≤ 0 ⇒ s_fun antitone ⇒ s_fun t ≤ s_fun τ⁺ = σMax, contra.
    -- Continuity of s_fun on [0, T').
    have hs_cont_ev : ∀ τ ∈ Set.Ico (0 : ℝ) T, ContinuousAt s_fun τ := by
      intro τ hτ
      have h_deriv_τ := dna25_sum_has_deriv p j y h_deriv τ hτ
      exact h_deriv_τ.continuousAt
    -- Continuity on [0, t].
    have ht_le_T : t < T := ht.2
    have ht_nn : 0 ≤ t := ht.1
    have hs_cont_Icc : ContinuousOn s_fun (Set.Icc 0 t) := by
      intro τ hτ
      refine (hs_cont_ev τ ?_).continuousWithinAt
      exact ⟨hτ.1, lt_of_le_of_lt hτ.2 ht_le_T⟩
    -- The set S := {τ ∈ [0, t] | s_fun τ ≤ σMax}. S is nonempty (0 ∈ S), closed, bounded above.
    -- Let τ* := sSup S. By continuity, s_fun τ* ≤ σMax. If τ* = t we're done.
    -- Else τ* < t, s_fun τ* = σMax exactly (else can push up), and on (τ*, t], s_fun > σMax.
    -- Then s_fun is antitone on [τ*, t] (derivative ≤ 0), so s_fun t ≤ s_fun τ* = σMax. Contradiction.
    set S : Set ℝ := {τ | τ ∈ Set.Icc (0 : ℝ) t ∧ s_fun τ ≤ σMax} with hS_def
    have h0_mem : (0 : ℝ) ∈ S := ⟨⟨le_refl _, ht_nn⟩, by rw [hs_init]; exact hσMax_nn⟩
    have hS_ne : S.Nonempty := ⟨0, h0_mem⟩
    have hS_bdd : BddAbove S := ⟨t, fun τ hτ => hτ.1.2⟩
    set τ_star : ℝ := sSup S with hτ_def
    have hτ_le : τ_star ≤ t := csSup_le hS_ne (fun τ hτ => hτ.1.2)
    have hτ_nn : 0 ≤ τ_star := le_csSup hS_bdd h0_mem
    have hτ_in_Icc : τ_star ∈ Set.Icc (0 : ℝ) t := ⟨hτ_nn, hτ_le⟩
    -- s_fun τ_star ≤ σMax by sequential continuity (approach from S).
    have h_s_τ_le : s_fun τ_star ≤ σMax := by
      -- Sequential approach: S ∋ τ_n → τ_star; continuity gives s_fun τ_star = lim s_fun τ_n ≤ σMax.
      rcases eq_or_lt_of_le hτ_nn with hτ_zero | hτ_pos
      · rw [← hτ_zero, hs_init]; exact hσMax_nn
      · have hs_cont_τ : ContinuousWithinAt s_fun (Set.Icc 0 t) τ_star :=
          hs_cont_Icc τ_star hτ_in_Icc
        by_contra h_gt_τ
        push_neg at h_gt_τ
        -- Get a neighborhood where s_fun > σMax.
        rw [Metric.continuousWithinAt_iff] at hs_cont_τ
        obtain ⟨δ, hδ, hδ_prop⟩ := hs_cont_τ ((s_fun τ_star - σMax) / 2) (by linarith)
        -- Find u ∈ S with τ_star - δ < u ≤ τ_star.
        obtain ⟨u, hu_mem, hu_lt⟩ :=
          exists_lt_of_lt_csSup hS_ne (show τ_star - δ < τ_star by linarith)
        have hu_le := le_csSup hS_bdd hu_mem
        have hu_in_Icc : u ∈ Set.Icc (0 : ℝ) t := hu_mem.1
        have hu_dist : dist u τ_star < δ := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith : u - τ_star ≤ 0)]
          linarith
        have h_close := hδ_prop hu_in_Icc hu_dist
        rw [Real.dist_eq] at h_close
        have h_abs := abs_sub_lt_iff.mp h_close
        -- s_fun u ≤ σMax, so s_fun τ_star ≤ s_fun u + |s_fun u - s_fun τ_star| < σMax + (s_fun τ_star - σMax)/2.
        -- Therefore s_fun τ_star < σMax + (s_fun τ_star - σMax)/2, i.e., (s_fun τ_star - σMax)/2 < 0, contra.
        have h2 : s_fun τ_star - s_fun u < (s_fun τ_star - σMax) / 2 := by linarith [h_abs.2]
        linarith [hu_mem.2]
    -- Case split on τ_star = t vs τ_star < t.
    rcases eq_or_lt_of_le hτ_le with hτ_eq | hτ_lt
    · -- τ_star = t. Then s_fun t ≤ σMax, contradicting h_gt.
      rw [hτ_eq] at h_s_τ_le
      linarith
    · -- τ_star < t. On (τ_star, t], s_fun > σMax. (Else u > τ_star would be in S.)
      have h_above : ∀ u, τ_star < u → u ≤ t → σMax < s_fun u := by
        intro u hsu hut
        by_contra h_le
        push_neg at h_le
        have hu_in_Icc' : u ∈ Set.Icc (0 : ℝ) t :=
          ⟨le_trans hτ_nn (le_of_lt hsu), hut⟩
        have hu_in_S : u ∈ S := ⟨hu_in_Icc', h_le⟩
        have : u ≤ τ_star := le_csSup hS_bdd hu_in_S
        linarith
      -- We also need s_fun τ_star = σMax exactly.
      -- (By the argument: if s_fun τ_star < σMax, then by continuity s_fun stays < σMax in
      -- a right-neighborhood of τ_star, contradicting h_above.)
      have h_s_τ_eq : s_fun τ_star = σMax := by
        refine le_antisymm h_s_τ_le ?_
        by_contra h_lt'
        push_neg at h_lt'
        have hs_cont_τ : ContinuousWithinAt s_fun (Set.Icc 0 t) τ_star :=
          hs_cont_Icc τ_star hτ_in_Icc
        rw [Metric.continuousWithinAt_iff] at hs_cont_τ
        obtain ⟨δ, hδ, hδ_prop⟩ := hs_cont_τ ((σMax - s_fun τ_star) / 2) (by linarith)
        set u := min (τ_star + δ / 2) t with hu_def
        have hu_le_t : u ≤ t := min_le_right _ _
        have hu_lt_t' : τ_star < u := lt_min (by linarith) hτ_lt
        have hu_mem_Icc : u ∈ Set.Icc (0 : ℝ) t :=
          ⟨le_trans hτ_nn (le_of_lt hu_lt_t'), hu_le_t⟩
        have hu_dist : dist u τ_star < δ := by
          have h1 : u ≤ τ_star + δ / 2 := min_le_left _ _
          rw [Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < u - τ_star)]
          linarith
        have h_close := hδ_prop hu_mem_Icc hu_dist
        rw [Real.dist_eq] at h_close
        have h_abs := abs_sub_lt_iff.mp h_close
        have hu_gt := h_above u hu_lt_t' hu_le_t
        linarith
      -- Now prove s_fun antitone on [τ_star, t] (derivative ≤ 0 on interior).
      set D : Set ℝ := Set.Icc τ_star t with hD_def
      have hD_conv : Convex ℝ D := convex_Icc _ _
      have hs_cont_D : ContinuousOn s_fun D := by
        intro τ hτ
        refine (hs_cont_ev τ ?_).continuousWithinAt
        exact ⟨le_trans hτ_nn hτ.1, lt_of_le_of_lt hτ.2 ht_le_T⟩
      have h_deriv_D : ∀ τ ∈ interior D,
          HasDerivWithinAt s_fun
            (((dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) (y τ)
              + (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) (y τ))
              * (1 - 2 * y τ ⟨2 * j.val, by omega⟩ * y τ ⟨2 * j.val + 1, by omega⟩))
            (interior D) τ := by
        intro τ hτ
        have hτ_D := interior_subset hτ
        have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
          ⟨le_trans hτ_nn hτ_D.1, lt_of_le_of_lt hτ_D.2 ht_le_T⟩
        exact (dna25_sum_has_deriv p j y h_deriv τ hτ_Ico).hasDerivWithinAt
      -- The derivative on interior D is ≤ 0 since s_fun τ > σMax there.
      have h_deriv_nonpos : ∀ τ ∈ interior D,
          ((dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) (y τ)
            + (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) (y τ))
            * (1 - 2 * y τ ⟨2 * j.val, by omega⟩ * y τ ⟨2 * j.val + 1, by omega⟩)
          ≤ 0 := by
        intro τ hτ
        have hτ_D := interior_subset hτ
        have hτ_Ico : τ ∈ Set.Ico (0 : ℝ) T :=
          ⟨le_trans hτ_nn hτ_D.1, lt_of_le_of_lt hτ_D.2 ht_le_T⟩
        -- On (τ_star, t]: s_fun > σMax. Interior of [τ_star, t] is Ioo τ_star t ⊆ (τ_star, t].
        have hτ_in_Ioo : τ ∈ Set.Ioo τ_star t := by
          have h_int_eq : interior D = Set.Ioo τ_star t := by
            rw [hD_def, interior_Icc]
          rw [h_int_eq] at hτ
          exact hτ
        have hs_gt : σMax < s_fun τ := h_above τ hτ_in_Ioo.1 (le_of_lt hτ_in_Ioo.2)
        -- Non-negativity of y.
        have hy_nn : ∀ k, 0 ≤ y τ k := h_nn τ hτ_Ico
        -- The positive factor.
        have h_pos_part_nn :
            0 ≤ (dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) (y τ) :=
          dualRailPosPart_eval_nonneg d p j (y τ) hy_nn
        have h_neg_part_nn :
            0 ≤ (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) (y τ) :=
          dualRailNegPart_eval_nonneg d p j (y τ) hy_nn
        have h_sum_nn :
            0 ≤ (dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) (y τ)
              + (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) (y τ) :=
          add_nonneg h_pos_part_nn h_neg_part_nn
        -- The second factor: 1 - 2 u v ≤ 0.
        -- Key algebra: 4 u v = (u+v)² - (u-v)² = s_fun² - w², with |w| ≤ β.
        -- So 2 u v = (s_fun² - w²) / 2 ≥ (s_fun² - β²) / 2 > (σMax² - β²)/2 = 1.
        have hu_val := y τ ⟨2 * j.val, by omega⟩
        have hv_val := y τ ⟨2 * j.val + 1, by omega⟩
        have hw_val : w τ j = btc.sol.trajectory τ j :=
          hw_eq_btc τ hτ_Ico j
        -- |btc.sol.trajectory τ j| ≤ β.
        have hβ_τ : |btc.sol.trajectory τ j| ≤ β := by
          have h_norm := hβ_bd τ (le_trans hτ_nn (le_of_lt hτ_in_Ioo.1))
          calc |btc.sol.trajectory τ j|
              = ‖btc.sol.trajectory τ j‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖btc.sol.trajectory τ‖ := norm_le_pi_norm _ j
            _ ≤ β := h_norm
        -- w τ j² ≤ β².
        have hw_sq_le : (w τ j) ^ 2 ≤ β ^ 2 := by
          have h_abs_le : |w τ j| ≤ β := by rw [hw_val]; exact hβ_τ
          have h1 := sq_abs (w τ j)
          calc (w τ j) ^ 2 = |w τ j| ^ 2 := by rw [h1]
            _ ≤ β ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h_abs_le 2
        -- s_fun τ² > σMax² = 2 + β².
        have hs_sq_gt : 2 + β ^ 2 < (s_fun τ) ^ 2 := by
          rw [← hσMax_sq]
          apply sq_lt_sq'
          · -- -σMax < s_fun τ: follows from s_fun τ > σMax ≥ 0.
            linarith
          · linarith
        -- Algebra: 4·u·v = s_fun² - w².
        have h_alg : 4 * (y τ ⟨2 * j.val, by omega⟩) * (y τ ⟨2 * j.val + 1, by omega⟩)
            = (s_fun τ) ^ 2 - (w τ j) ^ 2 := by
          show 4 * (y τ ⟨2 * j.val, by omega⟩) * (y τ ⟨2 * j.val + 1, by omega⟩)
              = (y τ ⟨2 * j.val, by omega⟩ + y τ ⟨2 * j.val + 1, by omega⟩) ^ 2
              - (y τ ⟨2 * j.val, by omega⟩ - y τ ⟨2 * j.val + 1, by omega⟩) ^ 2
          ring
        -- 2 u v ≥ 1.
        have h_2uv_ge :
            2 * y τ ⟨2 * j.val, by omega⟩ * y τ ⟨2 * j.val + 1, by omega⟩ ≥ 1 := by
          have : 4 * y τ ⟨2 * j.val, by omega⟩ * y τ ⟨2 * j.val + 1, by omega⟩
              ≥ 2 := by
            rw [h_alg]; linarith
          linarith
        -- 1 - 2 u v ≤ 0.
        have h_factor_nonpos :
            1 - 2 * y τ ⟨2 * j.val, by omega⟩ * y τ ⟨2 * j.val + 1, by omega⟩ ≤ 0 := by
          linarith
        exact mul_nonpos_of_nonneg_of_nonpos h_sum_nn h_factor_nonpos
      have h_anti := antitoneOn_of_hasDerivWithinAt_nonpos hD_conv hs_cont_D
        h_deriv_D h_deriv_nonpos
      have hτ_in_D : τ_star ∈ D := ⟨le_refl _, le_of_lt hτ_lt⟩
      have ht_in_D : t ∈ D := ⟨le_of_lt hτ_lt, le_refl _⟩
      have h_mono : s_fun t ≤ s_fun τ_star :=
        h_anti hτ_in_D ht_in_D (le_of_lt hτ_lt)
      rw [h_s_τ_eq] at h_mono
      linarith
  -- Step 4: combine non-negativity + barrier bound to bound ‖y t‖ ≤ σMax ≤ M.
  intro t ht
  -- ‖y t‖ = max over k of |y t k| = max over k of y t k (by non-neg).
  have hy_nn_t : ∀ k, 0 ≤ y t k := h_nn t ht
  have h_coord_bd : ∀ k, y t k ≤ σMax := by
    intro k
    -- k = ⟨k.val, _⟩. If k.val is even, k = ⟨2j,_⟩ for j = k.val/2; else odd.
    rcases Nat.even_or_odd k.val with h_even | h_odd
    · obtain ⟨j_val, hj_val⟩ := h_even
      have hj_lt : j_val < d := by
        have := k.isLt
        omega
      let j : Fin d := ⟨j_val, hj_lt⟩
      have hk_eq : k = ⟨2 * j.val, by omega⟩ := by
        apply Fin.ext
        show k.val = 2 * j_val
        omega
      rw [hk_eq]
      have h_bar := h_barrier j t ht
      have h_other_nn : 0 ≤ y t ⟨2 * j.val + 1, by omega⟩ :=
        hy_nn_t _
      linarith
    · obtain ⟨j_val, hj_val⟩ := h_odd
      have hj_lt : j_val < d := by
        have := k.isLt
        omega
      let j : Fin d := ⟨j_val, hj_lt⟩
      have hk_eq : k = ⟨2 * j.val + 1, by omega⟩ := by
        apply Fin.ext
        show k.val = 2 * j_val + 1
        omega
      rw [hk_eq]
      have h_bar := h_barrier j t ht
      have h_other_nn : 0 ≤ y t ⟨2 * j.val, by omega⟩ :=
        hy_nn_t _
      linarith
  -- Pi norm ≤ σMax.
  have h_norm_le_σMax : ‖y t‖ ≤ σMax := by
    rw [pi_norm_le_iff_of_nonneg hσMax_nn]
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (hy_nn_t k)]
    exact h_coord_bd k
  -- σMax + 1 ≤ M, so σMax ≤ M (via hM_def).
  have : σMax ≤ M := by
    have h1 : σMax ≤ σMax + 1 := by linarith
    linarith
  linarith

/-! ## Dual-rail identity along any zero-init solution. -/

/-- **Dual-rail identity (structural lemma).**

Along any zero-init solution of `polynomialScaleDualRail`, the difference
`y t ⟨2j,_⟩ − y t ⟨2j+1,_⟩` satisfies the original GPAC ODE
`w' = p_j(w)`, and therefore (by ODE uniqueness with matching initial
condition) coincides with `btc.sol.trajectory t j`.

The key algebraic step is `dualRailPos_sub_dualRailNeg_eval`, which gives
the polynomial identity `p̂⁺_j(w) − p̂⁻_j(w) = p_j(w_{2·0} − w_{2·0+1}, …)`.
Combined with the individual field identities
`polynomialScaleDualRail_field_u`, `polynomialScaleDualRail_field_v`, the
`u·v·(p̂⁺+p̂⁻)` terms cancel upon subtraction.

The ODE uniqueness consumer wires this into `btc.sol.is_solution` via
`ODE_solution_unique_of_mem_Icc_right` on every compact interval. -/
private theorem dna25_dualRail_identity {d : ℕ} [NeZero d] {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (_h_field : ∀ y : Fin d → ℝ, ∀ i : Fin d,
        btc.pivp.field y i
          = (p i).eval₂ (Rat.castHom ℝ) y)
    (_h_zero : ∀ j, btc.pivp.init j = 0)
    (y : ℝ → Fin (2 * d) → ℝ)
    (_hy0 : y 0 = fun _ => 0)
    (_hy_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y ((polynomialScaleDualRail d p).toPIVP.field (y t)) t) :
    ∀ t, 0 ≤ t → ∀ j : Fin d,
      y t ⟨2 * j.val, by omega⟩ - y t ⟨2 * j.val + 1, by omega⟩
        = btc.sol.trajectory t j := by
  -- Define the difference function w t j = y t ⟨2j,_⟩ - y t ⟨2j+1,_⟩.
  set w : ℝ → Fin d → ℝ :=
    fun t j => y t ⟨2 * j.val, by omega⟩ - y t ⟨2 * j.val + 1, by omega⟩ with hw_def
  -- Define the 1-dim-level polynomial field as a PolyPIVP (init all 0, any output).
  let P : PolyPIVP d :=
    { field := p, init := fun _ => 0, output := ⟨0, (NeZero.pos d)⟩ }
  -- The field of P at x : Fin d → ℝ.
  have hP_field : ∀ v : Fin d → ℝ, P.toPIVP.field v
      = fun j => (p j).eval₂ (Rat.castHom ℝ) v := by
    intro v; funext j; rfl
  -- Claim A: HasDerivAt (fun t => w t) (P.toPIVP.field (w t)) t for all t ≥ 0.
  have hw_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt w (P.toPIVP.field (w t)) t := by
    intro t ht
    have hy_t := _hy_deriv t ht
    -- Extract per-coord derivatives from hy_t via hasDerivAt_pi.
    have hy_coord : ∀ k : Fin (2 * d),
        HasDerivAt (fun s => y s k)
          ((polynomialScaleDualRail d p).toPIVP.field (y t) k) t :=
      hasDerivAt_pi.mp hy_t
    -- Use hasDerivAt_pi to assemble w's derivative from per-j derivatives.
    rw [hasDerivAt_pi]
    intro j
    -- w · j = (fun s => y s ⟨2j,_⟩) - (fun s => y s ⟨2j+1,_⟩).
    have h_u := hy_coord ⟨2 * j.val, by omega⟩
    have h_v := hy_coord ⟨2 * j.val + 1, by omega⟩
    have h_diff :
        HasDerivAt (fun s => y s ⟨2 * j.val, by omega⟩ - y s ⟨2 * j.val + 1, by omega⟩)
          ((polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val, by omega⟩
            - (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val + 1, by omega⟩)
          t := h_u.sub h_v
    -- The target derivative value equals (p j).eval₂ _ (w t).
    -- Use polynomialScaleDualRail_field_u / _v and dualRailPos_sub_dualRailNeg_eval.
    have h_u_id := polynomialScaleDualRail_field_u p j (y t)
    have h_v_id := polynomialScaleDualRail_field_v p j (y t)
    have h_sub_id :
        (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val, by omega⟩
          - (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val + 1, by omega⟩
        = (dualRailPosPart d p j).eval₂ (Rat.castHom ℝ) (y t)
          - (dualRailNegPart d p j).eval₂ (Rat.castHom ℝ) (y t) := by
      rw [h_u_id, h_v_id]; ring
    have h_alg := dualRailPos_sub_dualRailNeg_eval d p j (y t)
    have h_target :
        (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val, by omega⟩
          - (polynomialScaleDualRail d p).toPIVP.field (y t) ⟨2 * j.val + 1, by omega⟩
        = (p j).eval₂ (Rat.castHom ℝ) (w t) := by
      rw [h_sub_id, h_alg]
    rw [h_target] at h_diff
    -- Rewrite P.toPIVP.field (w t) j = (p j).eval₂ _ (w t).
    show HasDerivAt (fun s => w s j) (P.toPIVP.field (w t) j) t
    have : P.toPIVP.field (w t) j = (p j).eval₂ (Rat.castHom ℝ) (w t) := rfl
    rw [this]
    convert h_diff using 1
  -- Claim B: w 0 = fun _ => 0.
  have hw_init : w 0 = fun _ => 0 := by
    funext j
    show y 0 ⟨2 * j.val, by omega⟩ - y 0 ⟨2 * j.val + 1, by omega⟩ = 0
    rw [_hy0]; simp
  -- Claim C: btc.sol.trajectory has the same derivative structure.
  have hz_deriv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt btc.sol.trajectory (P.toPIVP.field (btc.sol.trajectory t)) t := by
    intro t ht
    have h := btc.sol.is_solution t ht
    -- btc.pivp.field = P.toPIVP.field pointwise by _h_field.
    have h_eq : btc.pivp.field (btc.sol.trajectory t)
        = P.toPIVP.field (btc.sol.trajectory t) := by
      funext i
      rw [_h_field (btc.sol.trajectory t) i]
      rfl
    rw [← h_eq]
    exact h
  -- Claim D: btc.sol.trajectory 0 = fun _ => 0.
  have hz_init : btc.sol.trajectory 0 = fun _ => 0 := by
    have h := btc.sol.init_cond
    funext j
    rw [h]
    exact _h_zero j
  -- Local Lipschitz of P.toPIVP.field.
  have h_lip := polyPIVP_field_locally_lipschitz P
  -- Uniqueness on every compact [0, T] via solutions_agree_on_Icc.
  intro t ht j
  rcases eq_or_lt_of_le ht with ht_zero | ht_pos
  · -- t = 0 case.
    subst ht_zero
    show y 0 ⟨2 * j.val, by omega⟩ - y 0 ⟨2 * j.val + 1, by omega⟩
      = btc.sol.trajectory 0 j
    rw [_hy0]
    have : btc.sol.trajectory 0 j = 0 := by
      rw [hz_init]
    rw [this]
    ring
  · -- t > 0: apply uniqueness on Icc 0 T for T := t + 1.
    set T : ℝ := t + 1 with hT_def
    have hT_pos : 0 < T := by linarith
    -- Continuity of w and btc.sol.trajectory on Icc 0 T (from HasDerivAt).
    have hw_cont : ContinuousOn w (Set.Icc 0 T) := by
      intro s hs
      exact (hw_deriv s hs.1).continuousAt.continuousWithinAt
    have hz_cont : ContinuousOn btc.sol.trajectory (Set.Icc 0 T) := by
      intro s hs
      exact (hz_deriv s hs.1).continuousAt.continuousWithinAt
    -- Bounds on compact [0, T] via isCompact_Icc.exists_isMaxOn.
    have h_Icc_ne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, ⟨le_refl _, hT_pos.le⟩⟩
    obtain ⟨u_w, _, hu_w_max⟩ :=
      isCompact_Icc.exists_isMaxOn h_Icc_ne hw_cont.norm
    obtain ⟨u_z, _, hu_z_max⟩ :=
      isCompact_Icc.exists_isMaxOn h_Icc_ne hz_cont.norm
    set Mw : ℝ := ‖w u_w‖ with hMw_def
    set Mz : ℝ := ‖btc.sol.trajectory u_z‖ with hMz_def
    set R : ℝ := max Mw Mz with hR_def
    have hR_nn : 0 ≤ R := le_max_of_le_left (norm_nonneg _)
    have hw_bd_R : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖w s‖ ≤ R := fun s hs =>
      le_trans (hu_w_max hs) (le_max_left _ _)
    have hz_bd_R : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖btc.sol.trajectory s‖ ≤ R := fun s hs =>
      le_trans (hu_z_max hs) (le_max_right _ _)
    -- Package HasDerivWithinAt on Icc 0 T.
    have hw_dw : ∀ s ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt w (P.toPIVP.field (w s)) (Set.Icc 0 T) s := fun s hs =>
      (hw_deriv s hs.1).hasDerivWithinAt
    have hz_dw : ∀ s ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt btc.sol.trajectory (P.toPIVP.field (btc.sol.trajectory s))
          (Set.Icc 0 T) s := fun s hs =>
      (hz_deriv s hs.1).hasDerivWithinAt
    -- Both start at 0.
    have hw_init' : w 0 = (fun _ => 0 : Fin d → ℝ) := hw_init
    have hz_init' : btc.sol.trajectory 0 = (fun _ => 0 : Fin d → ℝ) := hz_init
    -- Apply solutions_agree_on_Icc.
    have h_eqOn : Set.EqOn w btc.sol.trajectory (Set.Icc 0 T) :=
      solutions_agree_on_Icc hT_pos hR_nn h_lip hw_init' hz_init' hw_dw hz_dw
        hw_bd_R hz_bd_R
    have ht_in : t ∈ Set.Icc (0 : ℝ) T := ⟨ht, by linarith⟩
    have h_eq_t : w t = btc.sol.trajectory t := h_eqOn ht_in
    show y t ⟨2 * j.val, by omega⟩ - y t ⟨2 * j.val + 1, by omega⟩
      = btc.sol.trajectory t j
    have := congrArg (fun v => v j) h_eq_t
    simp at this
    exact this

/-! ## The main theorem. -/

/-- **[RTCRN2]/DNA 25 polynomial-scale dual-rail boundedness.**

Given a zero-init `BoundedTimeComputable d α` whose field is a concrete
polynomial `p` and whose initial condition vanishes on every species,
the 2·d-dimensional polynomial-scale dual-rail PIVP `polynomialScaleDualRail d p`
admits a globally-continuous `PIVP.Solution` that is:

  * non-negative on `[0, ∞)` (CRN non-negativity invariant);
  * bounded uniformly by a constant `B > 0` depending on `btc`;
  * satisfies the dual-rail identity `u_j(t) − v_j(t) = y_j(t)` where
    `y = btc.sol.trajectory`.

The construction witnesses an explicit trajectory `traj(t, k) = ...` and
uses the barrier bound `s_j(t) := u_j(t) + v_j(t) ≤ √(2 + β²)` together
with non-negativity to bound every coordinate.

This is [RTCRN2] Theorem 2's boundedness assertion (p. 11), at the level
of a full `PIVP.Solution` rather than just a "there exists a
non-negative bounded trajectory" statement.

### Implementation note.

Rather than re-derive the existence of the solution from Picard iteration
on the `polynomialScaleDualRail` field (which requires an independent
proof of the barrier barrier `s_j ≤ √(2+β²)`), this proof *reuses* the
already-established `dualRail_semantic_solution`.  Caveat: that theorem
produces a solution to an **exponential-shift** PIVP whose field is the
exp-shift field, not the `polynomialScaleDualRail` field.  Therefore the
two PIVPs are **not the same**, and the witness from
`dualRail_semantic_solution` **does not** directly verify the field of
`polynomialScaleDualRail`.

What we prove here is the **existence form** of the DNA 25 theorem: we
use the `polynomialScaleDualRail` field's local Lipschitz continuity
(`polyPIVP_field_locally_lipschitz`) plus an a-priori bound to produce
the solution via `locally_lipschitz_bounded_global_ode_proved_continuous`.
The a-priori bound comes from the barrier argument described in the
file header. -/
theorem polynomialScaleDualRail_bounded {d : ℕ} [NeZero d] {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (h_field : ∀ y : Fin d → ℝ, ∀ i : Fin d,
        btc.pivp.field y i
          = (p i).eval₂ (Rat.castHom ℝ) y)
    (h_zero : ∀ j, btc.pivp.init j = 0) :
    ∃ (sol : PIVP.Solution (polynomialScaleDualRail d p).toPIVP) (B : ℝ), 0 < B ∧
      (∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k) ∧
      (∀ t, 0 ≤ t → ∀ k, sol.trajectory t k ≤ B) ∧
      (∀ t, 0 ≤ t → ∀ j : Fin d,
        sol.trajectory t ⟨2 * j.val, by omega⟩
          - sol.trajectory t ⟨2 * j.val + 1, by omega⟩
          = btc.sol.trajectory t j) ∧
      Continuous sol.trajectory := by
  -- Set up the barrier barrier M = √(2 + β²) + 1 where β bounds |y_j|.
  obtain ⟨βSup, _hβ_pos, hβ_bd⟩ := btc.bounded
  set β : ℝ := max βSup 1 with hβ_def
  have _hβ_pos' : 0 < β := lt_of_lt_of_le one_pos (le_max_right _ _)
  have _hβ_bd' : ∀ t, 0 ≤ t → ‖btc.sol.trajectory t‖ ≤ β := by
    intro t ht
    calc ‖btc.sol.trajectory t‖
        ≤ βSup := hβ_bd t ht
      _ ≤ β := le_max_left _ _
  set M : ℝ := Real.sqrt (2 + β ^ 2) + 1 with hM_def
  have hM_pos : 0 < M := by
    have h1 : 0 ≤ Real.sqrt (2 + β ^ 2) := Real.sqrt_nonneg _
    linarith
  -- Abbreviation for the PIVP field of the polynomial-scale dual rail.
  set F : (Fin (2 * d) → ℝ) → Fin (2 * d) → ℝ :=
    (polynomialScaleDualRail d p).toPIVP.field with hF_def
  set y₀ : Fin (2 * d) → ℝ := fun _ => 0 with hy₀_def
  -- Step (A): local Lipschitz of F.
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (2 * d) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F x - F y‖ ≤ L * ‖x - y‖ :=
    polyPIVP_field_locally_lipschitz (polynomialScaleDualRail d p)
  -- Step (B): a priori bound (barrier barrier), scoped via dna25_apriori_bound.
  have h_invariant : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin (2 * d) → ℝ),
      y 0 = y₀ →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (F (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ M := by
    intro T hT y hy0 h_deriv
    have hy0' : y 0 = fun _ => 0 := hy0
    exact dna25_apriori_bound btc p h_field h_zero β _hβ_pos' _hβ_bd'
      M hM_pos (le_refl _) T hT y hy0' h_deriv
  -- Step (C): invoke the global-existence theorem.
  obtain ⟨y, hy0, hy_deriv, hy_cont⟩ :=
    locally_lipschitz_bounded_global_ode_proved_continuous F y₀
      h_lip M hM_pos h_invariant
  -- We have a globally continuous trajectory y : ℝ → Fin (2 * d) → ℝ with
  -- y 0 = 0 and forward-time HasDerivAt at every t ≥ 0. Package it as a
  -- PIVP.Solution of (polynomialScaleDualRail d p).toPIVP.
  refine
    ⟨ { trajectory := y,
        init_cond := ?_,
        is_solution := hy_deriv },
      M, hM_pos, ?_, ?_, ?_, hy_cont ⟩
  · -- init_cond: y 0 = (polynomialScaleDualRail d p).toPIVP.init
    rw [hy0]
    funext k
    show (0 : ℝ) = ((polynomialScaleDualRail d p).init k : ℝ)
    show (0 : ℝ) = ((0 : ℚ) : ℝ)
    norm_cast
  · -- Non-negativity via CRN non-negativity invariant.
    intro t ht k
    -- `polynomialScaleDualRail` has a PolyCRNDecomposition
    -- (`polynomialScaleDualRail_pcd`), and its init is zero everywhere, so
    -- `crn_trajectory_nonneg` applies.
    have hpcd : PolyCRNDecomposition (2 * d) (polynomialScaleDualRail d p) :=
      polynomialScaleDualRail_pcd d p
    have hzi : (polynomialScaleDualRail d p).IsZeroInit := by
      intro j
      show (polynomialScaleDualRail d p).init j = 0
      rfl
    -- Bundle the constructed solution.
    let sol : PIVP.Solution (polynomialScaleDualRail d p).toPIVP :=
      { trajectory := y
        init_cond := by
          rw [hy0]
          funext k
          show (0 : ℝ) = ((polynomialScaleDualRail d p).init k : ℝ)
          show (0 : ℝ) = ((0 : ℚ) : ℝ)
          norm_cast
        is_solution := hy_deriv }
    have hbnd : (polynomialScaleDualRail d p).toPIVP.IsBounded sol.trajectory := by
      refine ⟨M, hM_pos, ?_⟩
      intro t ht'
      -- Derive the global sup-norm bound from the coordwise bound via
      -- the a priori invariant on [0, t+1].
      have hT_pos : (0 : ℝ) < t + 1 := by linarith
      have hy_deriv' : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
          HasDerivAt y (F (y s)) s := fun s hs => hy_deriv s hs.1
      have ht_in : t ∈ Set.Ico (0 : ℝ) (t + 1) := ⟨ht', by linarith⟩
      exact h_invariant (t + 1) hT_pos y hy0 hy_deriv' t ht_in
    exact crn_trajectory_nonneg hpcd hzi sol hbnd k t ht
  · -- Coord-wise bound from sup-norm bound.
    intro t ht k
    have hT_pos : (0 : ℝ) < t + 1 := by linarith
    have hy_deriv' : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
        HasDerivAt y (F (y s)) s := fun s hs => hy_deriv s hs.1
    have ht_in : t ∈ Set.Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have h_norm : ‖y t‖ ≤ M := h_invariant (t + 1) hT_pos y hy0 hy_deriv' t ht_in
    calc y t k ≤ |y t k| := le_abs_self _
      _ = ‖y t k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖y t‖ := norm_le_pi_norm _ k
      _ ≤ M := h_norm
  · -- Dual-rail identity: y t ⟨2j,_⟩ − y t ⟨2j+1,_⟩ = btc.sol.trajectory t j.
    exact dna25_dualRail_identity btc p h_field h_zero y hy0 hy_deriv
  -- The theorem is now fully proved with zero scoped sorries. The proof
  -- pipeline is:
  -- (A) `polyPIVP_field_locally_lipschitz` — local Lipschitz of F.
  -- (B) `dna25_apriori_bound` — a-priori invariant `‖y t‖ ≤ M` via the
  --     2d-dimensional barrier argument (sum-rail forward-invariance with
  --     CRN non-negativity + dual-rail identity bound on w_j).
  -- (C) `locally_lipschitz_bounded_global_ode_proved_continuous` — packages
  --     (A)+(B) into a globally continuous solution.
  -- (D) `crn_trajectory_nonneg` + `dna25_dualRail_identity` — non-negativity
  --     and the u - v = y identity.

/-! ## Convergence corollary: dual-rail difference tracks `btc.convergence`.

`polynomialScaleDualRail_bounded` establishes existence + non-negativity +
boundedness + continuity + the dual-rail identity `u_j − v_j = y_j`. The
identity allows any exponential convergence bound on `btc.sol.trajectory t
btc.pivp.output` (i.e. `|y_output(t) − α| < exp(-r)` for `t > btc.modulus r`)
to be transferred verbatim to the difference `u_output(t) − v_output(t)`.

This corollary packages the full dual-rail BTC-level witness — the natural
output of the DNA 25 polynomial-scale construction, ready to be fed as the
x, y-input pair into the Lemma 8 subtraction gadget (with `α = β = original`
and the trivial case `α − β = 0` replaced by the looser version discussed
in `SubtractionGadget.subtraction_lemma8_analytic` TODO). -/
theorem polynomialScaleDualRail_bounded_converges {d : ℕ} [NeZero d] {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (h_field : ∀ y : Fin d → ℝ, ∀ i : Fin d,
        btc.pivp.field y i
          = (p i).eval₂ (Rat.castHom ℝ) y)
    (h_zero : ∀ j, btc.pivp.init j = 0) :
    ∃ (sol : PIVP.Solution (polynomialScaleDualRail d p).toPIVP) (B : ℝ),
      0 < B ∧
      (∀ t, 0 ≤ t → ∀ k, 0 ≤ sol.trajectory t k) ∧
      (∀ t, 0 ≤ t → ∀ k, sol.trajectory t k ≤ B) ∧
      (∀ t, 0 ≤ t → ∀ j : Fin d,
        sol.trajectory t ⟨2 * j.val, by omega⟩
          - sol.trajectory t ⟨2 * j.val + 1, by omega⟩
          = btc.sol.trajectory t j) ∧
      Continuous sol.trajectory ∧
      -- Convergence: the output-coord difference tracks the BTC convergence,
      -- for all `t ≥ 0` past the modulus.
      (∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > btc.modulus r →
        |sol.trajectory t ⟨2 * btc.pivp.output.val, by omega⟩
          - sol.trajectory t ⟨2 * btc.pivp.output.val + 1, by omega⟩
          - α|
        < Real.exp (-(r : ℝ))) := by
  obtain ⟨sol, B, hB_pos, h_nonneg, h_bnd, h_id, h_cont⟩ :=
    polynomialScaleDualRail_bounded btc p h_field h_zero
  refine ⟨sol, B, hB_pos, h_nonneg, h_bnd, h_id, h_cont, ?_⟩
  intro r t ht_nn ht
  rw [h_id t ht_nn btc.pivp.output]
  exact btc.convergence r t ht

end DualRail
end Ripple
