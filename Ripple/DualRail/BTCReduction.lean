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

namespace Ripple

/-! ## Semantic dual-rail Solution — structural residual axiom

`dualRail_semantic_solution` is the semantic-`BoundedTimeComputable`
analogue of `DualRail.dualRail_polynomial_scale_bounded`, strengthened
from a bare-function output to a full `PIVP.Solution` structure. It is
declared as an `axiom` because its proof requires interleaving Picard-
Lindelöf local existence with a Lyapunov-based a priori bound on
`Σ_i (u_i² + v_i²)`, which lives beyond the current project scope.

The statement is: given a zero-init BTC for α, there is a 2d-dimensional
PIVP `P` and a `PIVP.Solution P` whose trajectories are:
  (i)  zero at time 0,
  (ii) non-negative for all `t ≥ 0` on every coordinate,
  (iii) satisfying the dual-rail identity
        `sol[2j] − sol[2j+1] = btc.sol.trajectory · j`,
  (iv) uniformly bounded on `[0, ∞)`.
-/

/-- [RTCRN2]/DNA 25 dual-rail Solution, semantic layer. Residual structural
axiom: every zero-init `BoundedTimeComputable d α` admits a 2d-dimensional
dual-rail `PIVP.Solution` with non-negative, bounded trajectories whose
pairwise differences reproduce the original trajectory. This is the
published DNA 25 theorem at the Solution level. -/
axiom dualRail_semantic_solution {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (_h_zero : ∀ j, btc.pivp.init j = 0) :
    ∃ (P : PIVP (2 * d)) (sol : PIVP.Solution P) (B : ℝ), 0 < B ∧
      (∀ k : Fin (2 * d), P.init k = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ k : Fin (2 * d), 0 ≤ sol.trajectory t k) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ k : Fin (2 * d), sol.trajectory t k ≤ B) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j : Fin d,
        sol.trajectory t ⟨2 * j.val, by omega⟩
          - sol.trajectory t ⟨2 * j.val + 1, by omega⟩
          = btc.sol.trajectory t j)

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
