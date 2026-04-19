/-
  Ripple.DualRail.BTCReduction — DNA 25 dual-rail at BoundedTimeComputable level.

  Given a zero-init BoundedTimeComputable for α, the [RTCRN2]/DNA 25
  polynomial-scale annihilation dual-rail construction produces a (higher-
  dimensional) BTC for α whose init is zero on every species and whose
  non-output species trajectories are non-negative throughout `[0, ∞)`.
  Time modulus is preserved.

  Architecture. The underlying construction combines:
    (a) the semantic field split `p_i = p_i⁺ − p_i⁻` into non-negative parts
        (syntactic analogue: `posPart/negPart` in `DualRail/ConstantAnnihilation.lean`),
    (b) the dual-rail PIVP `u_i' = p_i⁺(u−v) − u_i·v_i·(p_i⁺+p_i⁻)`,
        `v_i' = p_i⁻(u−v) − u_i·v_i·(p_i⁺+p_i⁻)`, plus a readout species
        `z' = p_o(u − v)` with `z(0) = 0`, giving `z(t) = y_o(t)`, and
    (c) the DNA 25 polynomial-scale boundedness argument (already axiomatized
        at a weaker "bare function" form in
        `Ripple/DualRail/ConstantAnnihilation.lean`).

  Structural decomposition. Converting `BoundedTimeComputable.toDualRail`
  to a theorem factors the argument into:

  * `dualRail_semantic_solution` (residual axiom): At the semantic
    `BoundedTimeComputable` level, the 2d-dimensional dual-rail PIVP has
    a full `PIVP.Solution` (with `HasDerivAt` on each coordinate) whose
    trajectories are non-negative on `[0, ∞)` and whose differences
    `u_i(t) − v_i(t)` reproduce the original trajectory `y_i(t)`. This is
    the content of [RTCRN2]/DNA 25 at the Solution level — a strengthening
    of `dualRail_polynomial_scale_bounded` from the raw-function form.

  * Readout glue (proven here): attach one more species `z` with trajectory
    equal to `btc.sol.trajectory · btc.pivp.output`. Because `z(0) = 0`
    (by zero-init) and `z'(t) = btc.pivp.field (y(t)) output` (by btc's
    `is_solution`) and by the dual-rail identity
    `u(t) − v(t) = y(t)`, the readout species's ODE `z' = p_o(u − v)`
    is satisfied without invoking ODE uniqueness — we use the known
    trajectory `y_o` directly.

  The result: `BoundedTimeComputable.toDualRail` is a theorem (no longer
  an axiom), reducing to the single structural residual
  `dualRail_semantic_solution`.

  Reference: [RTCRN2] (Huang-Klinge-Lathrop, DNA 25, 2019).
-/

import Ripple.Core.BoundedTime
import Ripple.Core.InitShift
import Ripple.DualRail.ExpMajorization

namespace Ripple

/-! ## Semantic dual-rail Solution — exponential-shift construction

`dualRail_semantic_solution` used to be declared as an `axiom`. It is now
a **theorem** proved by the exponential-shift construction:

  u_j(t) := y_j(t) + β_j · (1 − e^{−t})      (u-rail, even indices 2j)
  v_j(t) :=           β_j · (1 − e^{−t})      (v-rail, odd  indices 2j+1)

where `y_j(t) := btc.sol.trajectory t j` and `β_j` is the per-coordinate
exponential majorizer of `|y_j|` (see `BoundedTimeComputable.dualRailBeta`).
The PIVP vector field is

  u_j' = p_j(u − v) + β_j − v_j           (because (1−e^{−t})' = e^{−t}
                                           = 1 − (1−e^{−t}) = 1 − v_j/β_j,
                                           so β_j·e^{−t} = β_j − v_j)
  v_j' =             β_j − v_j

Nonnegativity: `v_j ≥ 0` (since β_j ≥ 0 and 0 ≤ 1 − e^{−t}); `u_j =
y_j + β_j(1−e^{−t}) ≥ −|y_j| + β_j(1−e^{−t}) ≥ 0` by the majorization.
Difference: `u_j − v_j = y_j`. Boundedness: `v_j ≤ β_j` and `u_j ≤ M + β_j`.

The only analytic residual axiom is
`bounded_zero_init_exp_majorization` (in `Ripple/DualRail/ExpMajorization.lean`).
-/

/-! ### Index helpers for the 2d-dimensional dual rail. -/

/-- Even-index ("u-rail") coordinate. -/
@[inline] def dualRailU {d : ℕ} (j : Fin d) : Fin (2 * d) :=
  ⟨2 * j.val, by omega⟩

/-- Odd-index ("v-rail") coordinate. -/
@[inline] def dualRailV {d : ℕ} (j : Fin d) : Fin (2 * d) :=
  ⟨2 * j.val + 1, by omega⟩

/-- The original coordinate of a dual-rail index: `(2j)/2 = j`, `(2j+1)/2 = j`.
This is always well-defined when `k < 2*d`. -/
@[inline] def dualRailJ {d : ℕ} (k : Fin (2 * d)) : Fin d :=
  ⟨k.val / 2, Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 2)
    |>.mpr (by have := k.isLt; omega)⟩

theorem dualRailU_val {d : ℕ} (j : Fin d) :
    (dualRailU j).val = 2 * j.val := rfl

theorem dualRailV_val {d : ℕ} (j : Fin d) :
    (dualRailV j).val = 2 * j.val + 1 := rfl

theorem dualRailJ_of_u {d : ℕ} (j : Fin d) :
    dualRailJ (dualRailU j) = j := by
  apply Fin.ext
  show 2 * j.val / 2 = j.val
  omega

theorem dualRailJ_of_v {d : ℕ} (j : Fin d) :
    dualRailJ (dualRailV j) = j := by
  apply Fin.ext
  show (2 * j.val + 1) / 2 = j.val
  omega

/-! ### The dual-rail Solution theorem. -/

/-- [RTCRN2]/DNA 25 dual-rail Solution, semantic layer. **Theorem** proved
by the exponential-shift construction. Every zero-init
`BoundedTimeComputable d α` admits a 2d-dimensional dual-rail
`PIVP.Solution` with non-negative, bounded trajectories whose pairwise
differences reproduce the original trajectory. -/
theorem dualRail_semantic_solution {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_zero : ∀ j, btc.pivp.init j = 0) :
    ∃ (P : PIVP (2 * d)) (sol : PIVP.Solution P) (B : ℝ), 0 < B ∧
      (∀ k : Fin (2 * d), P.init k = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ k : Fin (2 * d), 0 ≤ sol.trajectory t k) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ k : Fin (2 * d), sol.trajectory t k ≤ B) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j : Fin d,
        sol.trajectory t ⟨2 * j.val, by omega⟩
          - sol.trajectory t ⟨2 * j.val + 1, by omega⟩
          = btc.sol.trajectory t j) := by
  -- Extract per-coordinate β majorizers.
  set β : Fin d → ℝ := btc.dualRailBeta h_zero with hβ_def
  have hβ_nn : ∀ j, 0 ≤ β j := fun j => btc.dualRailBeta_nonneg h_zero j
  have hβ_maj : ∀ j t, 0 ≤ t →
      |btc.sol.trajectory t j| ≤ β j * (1 - Real.exp (-t)) :=
    fun j t ht => btc.dualRailBeta_majorizes h_zero j t ht
  -- Uniform upper bound on |y_j(t)|.
  obtain ⟨M, hM_nn, hM_bd⟩ := btc.coord_bound
  -- Uniform bound on β: B := 1 + M + (Σ β_j). Actually we just need B ≥ M + β_j
  -- for every j, which is guaranteed by B := 1 + M + max_j β_j. Since `Fin d` is
  -- finite, `Finset.univ.sup' ...` could be used, but a simpler sum works:
  set βsum : ℝ := (Finset.univ : Finset (Fin d)).sum β with hβsum_def
  have hβsum_nn : 0 ≤ βsum :=
    Finset.sum_nonneg (fun j _ => hβ_nn j)
  have hβj_le_sum : ∀ j, β j ≤ βsum :=
    fun j => by
      have := Finset.single_le_sum (f := β)
        (fun i _ => hβ_nn i) (Finset.mem_univ j)
      simpa [hβsum_def] using this
  set B : ℝ := 1 + M + βsum with hB_def
  have hB_pos : 0 < B := by
    have : 0 ≤ M + βsum := by linarith
    linarith
  -- 0 ≤ 1 − e^{−t} ≤ 1 on t ≥ 0.
  have h_exp_bd : ∀ t, 0 ≤ t → 0 ≤ 1 - Real.exp (-t) ∧ 1 - Real.exp (-t) ≤ 1 := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have : Real.exp (-t) ≤ 1 := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith
    · have : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
      linarith
  -- Trajectory: u_j, v_j.
  let uTraj : ℝ → Fin d → ℝ := fun t j =>
    btc.sol.trajectory t j + β j * (1 - Real.exp (-t))
  let vTraj : ℝ → Fin d → ℝ := fun t j =>
    β j * (1 - Real.exp (-t))
  -- Combined trajectory on Fin (2*d): parity split on k.val % 2.
  let traj : ℝ → Fin (2 * d) → ℝ := fun t k =>
    if k.val % 2 = 0 then uTraj t (dualRailJ k) else vTraj t (dualRailJ k)
  -- PIVP field.
  let field : (Fin (2 * d) → ℝ) → (Fin (2 * d) → ℝ) := fun y k =>
    if k.val % 2 = 0 then
      btc.pivp.field (fun j => y (dualRailU j) - y (dualRailV j)) (dualRailJ k)
        + β (dualRailJ k) - y (dualRailV (dualRailJ k))
    else
      β (dualRailJ k) - y k
  -- `Fin (2 * d)` is inhabited iff d ≥ 1; for d = 0 the hypothesis `btc`
  -- is itself uninhabited (`btc.pivp.output : Fin 0`).
  by_cases hd0 : d = 0
  · subst hd0
    -- Degenerate: `btc.pivp.output : Fin 0` is uninhabited.
    exact (btc.pivp.output).elim0
  · -- Main case: d ≥ 1.
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
    have h2d_pos : 0 < 2 * d := by omega
    let P : PIVP (2 * d) :=
      { field := field
        init := fun _ => 0
        output := ⟨0, h2d_pos⟩ }
    -- Build the Solution.
    refine ⟨P, ?_, B, hB_pos, ?_, ?_, ?_, ?_⟩
    · -- sol : PIVP.Solution P
      refine
        { trajectory := traj
          init_cond := ?_
          is_solution := ?_ }
      · -- traj 0 = fun _ => 0
        funext k
        show (if k.val % 2 = 0 then uTraj 0 (dualRailJ k)
                               else vTraj 0 (dualRailJ k)) = 0
        have h_one_minus_exp : 1 - Real.exp (-(0 : ℝ)) = 0 := by
          simp [Real.exp_zero]
        have h_y_zero : btc.sol.trajectory 0 (dualRailJ k) = 0 := by
          have := congrFun btc.sol.init_cond (dualRailJ k)
          rw [this]; exact h_zero _
        by_cases hpar : k.val % 2 = 0
        · rw [if_pos hpar]
          show btc.sol.trajectory 0 (dualRailJ k) + β (dualRailJ k) *
            (1 - Real.exp (-(0 : ℝ))) = 0
          rw [h_y_zero, h_one_minus_exp]; ring
        · rw [if_neg hpar]
          show β (dualRailJ k) * (1 - Real.exp (-(0 : ℝ))) = 0
          rw [h_one_minus_exp]; ring
      · -- is_solution
        intro t ht
        refine hasDerivAt_pi.mpr ?_
        intro k
        -- We split on parity.
        by_cases hpar : k.val % 2 = 0
        · -- u-rail: d/dt[y_j + β_j(1-e^{-t})] = y_j' + β_j e^{-t}
          -- Want this = btc.field(y) j + β_j - v_j(t)
          --   = btc.field(y) j + β_j·e^{-t}  ✓
          -- (using v_j = β_j(1-e^{-t}), so β_j - v_j = β_j·e^{-t}).
          -- First the derivative of the trajectory coordinate.
          have h_btc := (hasDerivAt_pi.mp (btc.sol.is_solution t ht))
                          (dualRailJ k)
          -- h_btc : HasDerivAt (fun s => btc.sol.trajectory s (dualRailJ k))
          --              (btc.pivp.field (btc.sol.trajectory t) (dualRailJ k)) t
          have h_one_minus_exp :
              HasDerivAt (fun s : ℝ => 1 - Real.exp (-s)) (Real.exp (-t)) t := by
            have h1 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
            have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s))
                (Real.exp (-t) * (-1)) t := h1.exp
            have h3 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s))
                (0 - Real.exp (-t) * (-1)) t :=
              (hasDerivAt_const t (1 : ℝ)).sub h2
            convert h3 using 1; ring
          have h_scaled :
              HasDerivAt (fun s : ℝ => β (dualRailJ k) * (1 - Real.exp (-s)))
                (β (dualRailJ k) * Real.exp (-t)) t :=
            h_one_minus_exp.const_mul _
          -- Combined: LHS = y + βv where v := (1-e^{-t}).
          have h_sum :
              HasDerivAt (fun s : ℝ => btc.sol.trajectory s (dualRailJ k)
                                       + β (dualRailJ k) * (1 - Real.exp (-s)))
                (btc.pivp.field (btc.sol.trajectory t) (dualRailJ k)
                  + β (dualRailJ k) * Real.exp (-t)) t :=
            h_btc.add h_scaled
          -- Now we need to rewrite the goal into exactly this form.
          -- Goal: HasDerivAt (fun s => traj s k) (field (traj t) k) t.
          show HasDerivAt (fun s => traj s k) (field (traj t) k) t
          -- LHS.
          have hLHS_eq :
              (fun s : ℝ => traj s k) =
              (fun s : ℝ => btc.sol.trajectory s (dualRailJ k)
                             + β (dualRailJ k) * (1 - Real.exp (-s))) := by
            funext s
            show (if k.val % 2 = 0 then uTraj s (dualRailJ k)
                                   else vTraj s (dualRailJ k))
              = btc.sol.trajectory s (dualRailJ k)
                + β (dualRailJ k) * (1 - Real.exp (-s))
            rw [if_pos hpar]
          -- RHS.
          -- The field on u-rail: btc.field(u−v) j + β_j − v_j.
          -- Here (u−v) j = y_j(t); and v_j(t) = β_j(1-e^{-t}).
          -- So field = btc.field(y) j + β_j − β_j(1-e^{-t})
          --          = btc.field(y) j + β_j·e^{-t}.
          have h_uv_eq :
              (fun j => traj t (dualRailU j) - traj t (dualRailV j)) =
              (fun j => btc.sol.trajectory t j) := by
            funext j
            show (if (dualRailU j).val % 2 = 0 then uTraj t (dualRailJ (dualRailU j))
                                                else vTraj t (dualRailJ (dualRailU j)))
              - (if (dualRailV j).val % 2 = 0 then uTraj t (dualRailJ (dualRailV j))
                                                else vTraj t (dualRailJ (dualRailV j)))
              = btc.sol.trajectory t j
            have huev : (dualRailU j).val % 2 = 0 := by
              show (2 * j.val) % 2 = 0; omega
            have hvod : ¬ (dualRailV j).val % 2 = 0 := by
              show ¬ (2 * j.val + 1) % 2 = 0; omega
            rw [if_pos huev, if_neg hvod, dualRailJ_of_u, dualRailJ_of_v]
            show (btc.sol.trajectory t j + β j * (1 - Real.exp (-t)))
                 - β j * (1 - Real.exp (-t))
              = btc.sol.trajectory t j
            ring
          have hv_eq : traj t (dualRailV (dualRailJ k)) =
              β (dualRailJ k) * (1 - Real.exp (-t)) := by
            show (if (dualRailV (dualRailJ k)).val % 2 = 0 then
                    uTraj t (dualRailJ (dualRailV (dualRailJ k)))
                  else vTraj t (dualRailJ (dualRailV (dualRailJ k))))
              = β (dualRailJ k) * (1 - Real.exp (-t))
            have hvod : ¬ (dualRailV (dualRailJ k)).val % 2 = 0 := by
              show ¬ (2 * (dualRailJ k).val + 1) % 2 = 0; omega
            rw [if_neg hvod, dualRailJ_of_v]
          have hRHS_eq :
              field (traj t) k =
              btc.pivp.field (btc.sol.trajectory t) (dualRailJ k)
                + β (dualRailJ k) * Real.exp (-t) := by
            show (if k.val % 2 = 0 then
                   btc.pivp.field (fun j => traj t (dualRailU j) - traj t (dualRailV j))
                                   (dualRailJ k)
                     + β (dualRailJ k) - traj t (dualRailV (dualRailJ k))
                 else
                   β (dualRailJ k) - traj t k)
              = btc.pivp.field (btc.sol.trajectory t) (dualRailJ k)
                  + β (dualRailJ k) * Real.exp (-t)
            rw [if_pos hpar, h_uv_eq, hv_eq]
            ring
          rw [hLHS_eq, hRHS_eq]
          exact h_sum
        · -- v-rail: d/dt[β_j(1-e^{-t})] = β_j·e^{-t} = β_j − v_j.
          have h_one_minus_exp :
              HasDerivAt (fun s : ℝ => 1 - Real.exp (-s)) (Real.exp (-t)) t := by
            have h1 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
            have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s))
                (Real.exp (-t) * (-1)) t := h1.exp
            have h3 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s))
                (0 - Real.exp (-t) * (-1)) t :=
              (hasDerivAt_const t (1 : ℝ)).sub h2
            convert h3 using 1; ring
          have h_scaled :
              HasDerivAt (fun s : ℝ => β (dualRailJ k) * (1 - Real.exp (-s)))
                (β (dualRailJ k) * Real.exp (-t)) t :=
            h_one_minus_exp.const_mul _
          show HasDerivAt (fun s => traj s k) (field (traj t) k) t
          have hLHS_eq :
              (fun s : ℝ => traj s k) =
              (fun s : ℝ => β (dualRailJ k) * (1 - Real.exp (-s))) := by
            funext s
            show (if k.val % 2 = 0 then uTraj s (dualRailJ k)
                                   else vTraj s (dualRailJ k))
              = β (dualRailJ k) * (1 - Real.exp (-s))
            rw [if_neg hpar]
          have hRHS_eq :
              field (traj t) k =
              β (dualRailJ k) * Real.exp (-t) := by
            show (if k.val % 2 = 0 then
                   btc.pivp.field (fun j => traj t (dualRailU j) - traj t (dualRailV j))
                                   (dualRailJ k)
                     + β (dualRailJ k) - traj t (dualRailV (dualRailJ k))
                 else
                   β (dualRailJ k) - traj t k)
              = β (dualRailJ k) * Real.exp (-t)
            rw [if_neg hpar]
            -- traj t k = vTraj t (dualRailJ k) = β (dualRailJ k) * (1 - exp(-t))
            have htrajk : traj t k = β (dualRailJ k) * (1 - Real.exp (-t)) := by
              show (if k.val % 2 = 0 then uTraj t (dualRailJ k)
                                     else vTraj t (dualRailJ k))
                = β (dualRailJ k) * (1 - Real.exp (-t))
              rw [if_neg hpar]
            rw [htrajk]; ring
          rw [hLHS_eq, hRHS_eq]
          exact h_scaled
    · -- init zero.
      intro k
      rfl
    · -- non-negativity: each u_j, v_j ≥ 0.
      intro t ht k
      show (if k.val % 2 = 0 then uTraj t (dualRailJ k)
                             else vTraj t (dualRailJ k)) ≥ 0
      have hexp := h_exp_bd t ht
      by_cases hpar : k.val % 2 = 0
      · rw [if_pos hpar]
        -- u_j = y_j + β_j(1-e^{-t}) ≥ -|y_j| + β_j(1-e^{-t}) ≥ 0 by majorization.
        show 0 ≤ btc.sol.trajectory t (dualRailJ k)
                 + β (dualRailJ k) * (1 - Real.exp (-t))
        have h_maj := hβ_maj (dualRailJ k) t ht
        have h_abs : -|btc.sol.trajectory t (dualRailJ k)| ≤
            btc.sol.trajectory t (dualRailJ k) := neg_abs_le _
        linarith
      · rw [if_neg hpar]
        show 0 ≤ β (dualRailJ k) * (1 - Real.exp (-t))
        exact mul_nonneg (hβ_nn _) hexp.1
    · -- bound: each traj ≤ B.
      intro t ht k
      show (if k.val % 2 = 0 then uTraj t (dualRailJ k)
                             else vTraj t (dualRailJ k)) ≤ B
      have hexp := h_exp_bd t ht
      have hM_j : |btc.sol.trajectory t (dualRailJ k)| ≤ M :=
        hM_bd t ht (dualRailJ k)
      have hβ_sum : β (dualRailJ k) ≤ βsum := hβj_le_sum (dualRailJ k)
      by_cases hpar : k.val % 2 = 0
      · rw [if_pos hpar]
        -- u_j ≤ |y_j| + β_j·(1-e^{-t}) ≤ M + β_j ≤ 1 + M + βsum = B.
        show btc.sol.trajectory t (dualRailJ k)
              + β (dualRailJ k) * (1 - Real.exp (-t)) ≤ B
        have hylt : btc.sol.trajectory t (dualRailJ k)
            ≤ |btc.sol.trajectory t (dualRailJ k)| := le_abs_self _
        have hy_le : btc.sol.trajectory t (dualRailJ k) ≤ M := by linarith
        have hβpart : β (dualRailJ k) * (1 - Real.exp (-t))
            ≤ β (dualRailJ k) := by
          have h1 : β (dualRailJ k) * (1 - Real.exp (-t))
              ≤ β (dualRailJ k) * 1 := by
            apply mul_le_mul_of_nonneg_left hexp.2 (hβ_nn _)
          linarith
        show (_ : ℝ) ≤ 1 + M + βsum
        linarith
      · rw [if_neg hpar]
        show β (dualRailJ k) * (1 - Real.exp (-t)) ≤ B
        have hβpart : β (dualRailJ k) * (1 - Real.exp (-t))
            ≤ β (dualRailJ k) := by
          have h1 : β (dualRailJ k) * (1 - Real.exp (-t))
              ≤ β (dualRailJ k) * 1 := by
            apply mul_le_mul_of_nonneg_left hexp.2 (hβ_nn _)
          linarith
        show (_ : ℝ) ≤ 1 + M + βsum
        linarith
    · -- dual-rail identity: u_j − v_j = y_j.
      intro t _ht j
      -- Goal: traj t ⟨2j, _⟩ − traj t ⟨2j+1, _⟩ = btc.sol.trajectory t j.
      have hu_eq : (⟨2 * j.val, by omega⟩ : Fin (2 * d)) = dualRailU j := rfl
      have hv_eq : (⟨2 * j.val + 1, by omega⟩ : Fin (2 * d)) = dualRailV j := rfl
      rw [hu_eq, hv_eq]
      show (if (dualRailU j).val % 2 = 0 then uTraj t (dualRailJ (dualRailU j))
                                          else vTraj t (dualRailJ (dualRailU j)))
         - (if (dualRailV j).val % 2 = 0 then uTraj t (dualRailJ (dualRailV j))
                                          else vTraj t (dualRailJ (dualRailV j)))
         = btc.sol.trajectory t j
      have huev : (dualRailU j).val % 2 = 0 := by
        show (2 * j.val) % 2 = 0; omega
      have hvod : ¬ (dualRailV j).val % 2 = 0 := by
        show ¬ (2 * j.val + 1) % 2 = 0; omega
      rw [if_pos huev, if_neg hvod, dualRailJ_of_u, dualRailJ_of_v]
      show (btc.sol.trajectory t j + β j * (1 - Real.exp (-t)))
           - β j * (1 - Real.exp (-t))
         = btc.sol.trajectory t j
      ring

/-! ## Main theorem: `BoundedTimeComputable.toDualRail` -/

/-- [RTCRN2]/DNA 25 dual-rail BTC reduction: a zero-init BTC for α produces
a (possibly higher-dimensional) BTC for α whose every species starts at 0,
whose non-output species stay non-negative on `[0, ∞)`, and whose output
(the readout z species) exactly tracks the original output trajectory.
Time modulus is preserved.

This is now a theorem, reducing to the single structural residual axiom
`dualRail_semantic_solution`. The readout glue is handled here without
ODE-uniqueness: we define `z(t) := btc.sol.trajectory t btc.pivp.output`
and observe that `z(0) = 0` (by zero-init) and `z'(t) = btc.pivp.field
(btc.sol.trajectory t) btc.pivp.output`, which coincides with
`btc.pivp.field (u(t) − v(t)) output` by the dual-rail identity. -/
theorem BoundedTimeComputable.toDualRail {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_zero : ∀ j, btc.pivp.init j = 0) :
    ∃ d' : ℕ, ∃ btc' : BoundedTimeComputable d' α,
      (∀ j, btc'.pivp.init j = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j, j ≠ btc'.pivp.output →
        0 ≤ btc'.sol.trajectory t j) ∧
      btc'.modulus = btc.modulus ∧
      (∀ t : ℝ, 0 ≤ t →
        btc'.sol.trajectory t btc'.pivp.output
          = btc.sol.trajectory t btc.pivp.output) := by
  -- Extract dual-rail solution from the residual structural axiom.
  obtain ⟨P, sol, B, hB_pos, hP_init, h_nonneg, h_bdd, h_diff⟩ :=
    dualRail_semantic_solution btc h_zero
  obtain ⟨M, hM_pos, hM_bd⟩ := btc.bounded
  -- Build the extended PIVP and Solution by direct record construction,
  -- avoiding `let` bindings that block `change`/`show`.
  refine ⟨2 * d + 1, ?_, ?_, ?_, ?_, ?_⟩
  · -- The `BoundedTimeComputable (2*d+1) α` record.
    refine {
      pivp := {
        field := fun y =>
          Fin.snoc
            (P.field (fun k : Fin (2 * d) => y k.castSucc))
            (btc.pivp.field
              (fun j : Fin d => y ⟨2 * j.val, by omega⟩
                - y ⟨2 * j.val + 1, by omega⟩)
              btc.pivp.output)
        init := Fin.snoc (fun k : Fin (2 * d) => P.init k) 0
        output := Fin.last (2 * d) }
      sol := {
        trajectory := fun t =>
          Fin.snoc
            (fun k : Fin (2 * d) => sol.trajectory t k)
            (btc.sol.trajectory t btc.pivp.output)
        init_cond := ?_
        is_solution := ?_ }
      modulus := btc.modulus
      bounded := ?_
      convergence := ?_ }
    · -- init_cond
      funext k
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · -- last coord: btc.sol.trajectory 0 btc.pivp.output = 0
        simp only [Fin.snoc_last]
        have h_btc_zero : btc.sol.trajectory 0 btc.pivp.output = 0 := by
          have := congrFun btc.sol.init_cond btc.pivp.output
          rw [this]; exact h_zero btc.pivp.output
        rw [h_btc_zero]
      · -- first 2d coords
        simp only [Fin.snoc_castSucc]
        have h_sol_zero : sol.trajectory 0 k' = 0 := by
          have := congrFun sol.init_cond k'
          rw [this]; exact hP_init k'
        rw [h_sol_zero]
        exact (hP_init k').symm
    · -- is_solution
      intro t ht
      refine hasDerivAt_pi.mpr ?_
      intro k
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · -- Last coord: readout tracks btc's output.
        have h_btc := hasDerivAt_pi.mp (btc.sol.is_solution t ht) btc.pivp.output
        -- Beta-reduce the goal.
        show HasDerivAt
            (fun s : ℝ =>
              Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
                (fun k : Fin (2 * d) => sol.trajectory s k)
                (btc.sol.trajectory s btc.pivp.output) (Fin.last (2 * d)))
            (Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
              (P.field (fun k : Fin (2 * d) =>
                Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
                  (fun k : Fin (2 * d) => sol.trajectory t k)
                  (btc.sol.trajectory t btc.pivp.output) k.castSucc))
              (btc.pivp.field
                (fun j : Fin d =>
                  Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
                    (fun k : Fin (2 * d) => sol.trajectory t k)
                    (btc.sol.trajectory t btc.pivp.output)
                    ⟨2 * j.val, by omega⟩
                  - Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
                    (fun k : Fin (2 * d) => sol.trajectory t k)
                    (btc.sol.trajectory t btc.pivp.output)
                    ⟨2 * j.val + 1, by omega⟩)
                btc.pivp.output)
              (Fin.last (2 * d))) t
        -- Simplify LHS projection.
        have h_proj : (fun s : ℝ =>
            Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
              (fun k : Fin (2 * d) => sol.trajectory s k)
              (btc.sol.trajectory s btc.pivp.output) (Fin.last (2 * d)))
            = fun s : ℝ => btc.sol.trajectory s btc.pivp.output := by
          funext s; rw [Fin.snoc_last]
        rw [h_proj]
        -- Simplify RHS using snoc_last and the dual-rail identity.
        rw [Fin.snoc_last]
        -- Now need: HasDerivAt (fun s => btc.sol.trajectory s btc.pivp.output)
        --   (btc.pivp.field (fun j => newTraj t ⟨2j⟩ - newTraj t ⟨2j+1⟩) btc.pivp.output) t
        -- Rewrite the diffs using dual-rail identity.
        have h_diffs : (fun j : Fin d =>
            Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
              (fun k : Fin (2 * d) => sol.trajectory t k)
              (btc.sol.trajectory t btc.pivp.output)
              ⟨2 * j.val, by omega⟩
            - Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
              (fun k : Fin (2 * d) => sol.trajectory t k)
              (btc.sol.trajectory t btc.pivp.output)
              ⟨2 * j.val + 1, by omega⟩)
            = fun j : Fin d => btc.sol.trajectory t j := by
          funext j
          have hidx1 : (⟨2 * j.val, by omega⟩ : Fin (2 * d + 1))
              = Fin.castSucc (⟨2 * j.val, by omega⟩ : Fin (2 * d)) := by
            apply Fin.ext; rfl
          have hidx2 : (⟨2 * j.val + 1, by omega⟩ : Fin (2 * d + 1))
              = Fin.castSucc (⟨2 * j.val + 1, by omega⟩ : Fin (2 * d)) := by
            apply Fin.ext; rfl
          rw [hidx1, hidx2, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact h_diff t ht j
        rw [h_diffs]
        exact h_btc
      · -- First 2d coords: inherit from sol.is_solution.
        have h_sol := hasDerivAt_pi.mp (sol.is_solution t ht) k'
        -- After beta-reduction the goal is:
        --   HasDerivAt (fun s => Fin.snoc _ _ k'.castSucc)
        --     (Fin.snoc (P.field ...) _ k'.castSucc) t
        -- Simplify LHS projection and RHS projection.
        show HasDerivAt
            (fun s : ℝ =>
              Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
                (fun k : Fin (2 * d) => sol.trajectory s k)
                (btc.sol.trajectory s btc.pivp.output) k'.castSucc)
            (Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
              (P.field (fun j : Fin (2 * d) =>
                Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
                  (fun k : Fin (2 * d) => sol.trajectory t k)
                  (btc.sol.trajectory t btc.pivp.output) j.castSucc))
              (btc.pivp.field
                (fun j : Fin d =>
                  Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
                    (fun k : Fin (2 * d) => sol.trajectory t k)
                    (btc.sol.trajectory t btc.pivp.output)
                    ⟨2 * j.val, by omega⟩
                  - Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
                    (fun k : Fin (2 * d) => sol.trajectory t k)
                    (btc.sol.trajectory t btc.pivp.output)
                    ⟨2 * j.val + 1, by omega⟩)
                btc.pivp.output)
              k'.castSucc) t
        have h_proj : (fun s : ℝ =>
            Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
              (fun k : Fin (2 * d) => sol.trajectory s k)
              (btc.sol.trajectory s btc.pivp.output) k'.castSucc)
            = fun s : ℝ => sol.trajectory s k' := by
          funext s; rw [Fin.snoc_castSucc]
        rw [h_proj]
        -- Simplify RHS.
        rw [Fin.snoc_castSucc]
        -- Now P.field has argument `fun j => Fin.snoc ... j.castSucc`
        have h_arg : (fun j : Fin (2 * d) =>
            Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
              (fun k : Fin (2 * d) => sol.trajectory t k)
              (btc.sol.trajectory t btc.pivp.output) j.castSucc)
            = fun j : Fin (2 * d) => sol.trajectory t j := by
          funext j; rw [Fin.snoc_castSucc]
        rw [h_arg]
        exact h_sol
    · -- bounded: |trajectory t| ≤ B + M
      refine ⟨B + M, by linarith, fun t ht => ?_⟩
      rw [pi_norm_le_iff_of_nonneg (by linarith)]
      intro k
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · -- Last coord
        show ‖Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
          (fun k : Fin (2 * d) => sol.trajectory t k)
          (btc.sol.trajectory t btc.pivp.output) (Fin.last (2 * d))‖ ≤ B + M
        rw [Fin.snoc_last]
        have hn : ‖btc.sol.trajectory t btc.pivp.output‖
            ≤ ‖btc.sol.trajectory t‖ := norm_le_pi_norm _ _
        calc ‖btc.sol.trajectory t btc.pivp.output‖
            ≤ ‖btc.sol.trajectory t‖ := hn
          _ ≤ M := hM_bd t ht
          _ ≤ B + M := by linarith
      · -- First 2d coords
        show ‖Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
          (fun k : Fin (2 * d) => sol.trajectory t k)
          (btc.sol.trajectory t btc.pivp.output) k'.castSucc‖ ≤ B + M
        rw [Fin.snoc_castSucc]
        rw [Real.norm_eq_abs]
        have hlo : 0 ≤ sol.trajectory t k' := h_nonneg t ht k'
        have hhi : sol.trajectory t k' ≤ B := h_bdd t ht k'
        rw [abs_of_nonneg hlo]
        linarith
    · -- convergence
      intro r t ht
      -- trajectory at output (last) equals btc output trajectory.
      show |Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ) _
          (btc.sol.trajectory t btc.pivp.output) (Fin.last (2 * d)) - α|
          < Real.exp (-(r : ℝ))
      rw [Fin.snoc_last]
      exact btc.convergence r t ht
  · -- All new inits are zero.
    intro j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · -- last coord
      show Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
        (fun k : Fin (2 * d) => P.init k) 0 (Fin.last (2 * d)) = 0
      exact Fin.snoc_last _ _
    · -- first 2d coords
      show Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
        (fun k : Fin (2 * d) => P.init k) 0 j'.castSucc = 0
      rw [Fin.snoc_castSucc]
      exact hP_init j'
  · -- Non-negativity on non-output species.
    intro t ht j hjne
    induction j using Fin.lastCases with
    | last =>
      -- j = Fin.last: contradicts hjne (which says j ≠ output = Fin.last).
      exact absurd rfl hjne
    | cast j' =>
      -- j = j'.castSucc
      show 0 ≤ Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
        (fun k : Fin (2 * d) => sol.trajectory t k)
        (btc.sol.trajectory t btc.pivp.output) j'.castSucc
      rw [Fin.snoc_castSucc]
      exact h_nonneg t ht j'
  · -- Modulus preserved: rfl.
    rfl
  · -- Readout identity: trajectory at output equals btc.sol output trajectory.
    intro t _ht
    show Fin.snoc (α := fun _ : Fin (2 * d + 1) => ℝ)
      (fun k : Fin (2 * d) => sol.trajectory t k)
      (btc.sol.trajectory t btc.pivp.output) (Fin.last (2 * d))
      = btc.sol.trajectory t btc.pivp.output
    exact Fin.snoc_last _ _

/-! ## Composed DNA 25 reduction: shift + dual-rail -/

/-- DNA 25 semantic reduction at BTC level: every BTC for α reduces, via
change of variables `ẑ = y − y₀`, to a zero-init + non-negative-interior
BTC for `α − y₀`, with the same time modulus. Composes
`BoundedTimeComputable.shiftToZero` with `BoundedTimeComputable.toDualRail`. -/
theorem BoundedTimeComputable.dna25_shift_dualRail {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    ∃ β : ℝ, ∃ d' : ℕ, ∃ btc' : BoundedTimeComputable d' (α - β),
      (∀ j, btc'.pivp.init j = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j, j ≠ btc'.pivp.output →
        0 ≤ btc'.sol.trajectory t j) ∧
      btc'.modulus = btc.modulus := by
  obtain ⟨d', btc', h_init', h_nonneg', h_mod_eq, _h_readout⟩ :=
    btc.shiftToZero.toDualRail (fun j => btc.shiftToZero_pivp_init j)
  exact ⟨btc.pivp.init btc.pivp.output, d', btc', h_init', h_nonneg', h_mod_eq⟩

/-! ## IsRealTimeComputable-level DNA 25 full reduction -/

/-- DNA 25 full reduction at `IsRealTimeComputable` level:
`α` real-time computable ⟹ there exist a shift constant `β` and a zero-init
+ non-negative-interior BTC for `(α − β)` with the same linear modulus.
The missing summand `β` is itself real-time computable by `realtime_const`,
so `realtime_field_add` closes the cycle back to `α`. -/
theorem IsRealTimeComputable.dna25_full_reduction {α : ℝ}
    (ha : IsRealTimeComputable α) :
    ∃ β : ℝ, ∃ d : ℕ, ∃ btc : BoundedTimeComputable d (α - β),
      (∀ j, btc.pivp.init j = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j, j ≠ btc.pivp.output →
        0 ≤ btc.sol.trajectory t j) ∧
      ∃ C > 0, ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1) := by
  obtain ⟨d, btc, C, hC, hmod⟩ := ha
  obtain ⟨β, d', btc', h_init', h_nonneg', h_mod_eq⟩ :=
    btc.dna25_shift_dualRail
  refine ⟨β, d', btc', h_init', h_nonneg', C, hC, fun r => ?_⟩
  rw [h_mod_eq]
  exact hmod r

end Ripple
