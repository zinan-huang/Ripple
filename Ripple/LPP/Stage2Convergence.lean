/-
  Ripple.LPP.Stage2Convergence — Remark 14 replacement for `stage2_convergence_axiom`.

  Purpose: discharge `stage2_convergence_axiom` (used in `Stages.lean`'s
  `stage2_ode_axiom`) by the argument of [LPP, Remark 14]:

    * x₀(0) = 1, and on the simplex (∑ᵢ zᵢ = 1),
      z₀(s) = 1 - y_o(τ(s)) - c·∑_{j≠o} y_j(τ(s)).
    * If the BTC trajectory satisfies the "room" condition
          y_o(s) + c·∑_{j≠o} y_j(s) ≤ 1 - c_room   for all s ≥ 0,
      then z₀(s) ≥ c_room along the Stage 2 orbit — WITHOUT monotonicity.
    * Combined with `stage2_convergence_from_z0_invariant`, this closes
      the axiom.

  Status
  ------
  The reparametrization identity `stage2_output_eq_btc_output_at_tau` lives in
  `Stages.lean` but is FINITE-T (requires explicit bounds `M, L` on the
  window `[0, T]`). Remark 14 needs the ∀ s ≥ 0 version. The extension is
  packaged here as `stage2_unscaledTail_eq_btcTraj_comp_tau_global`.

  Caller responsibility. The "room" condition must be supplied by an upstream
  refinement of the BTC (e.g. a CRN on the simplex with bounded tail mass).
  A matching strengthened BTC for the algebraic pipeline is expected to live
  in `Ripple.LPP.AlgebraicConstruction` once this chain is in place.

  NO custom axioms beyond those already declared in Stages.lean.
-/

import Ripple.LPP.Stages

namespace Ripple

open scoped Topology

/-! ## Remark 14 step 1 — algebraic expression for `z₀` in reparam coordinates

On the Stage 2 simplex (`∑ᵢ sol(s)ᵢ = 1`), the 0-th coordinate `z₀(s)`
is determined by the tail:

  z₀(s) = 1 - ∑_{j : Fin d} sol(s)_{j.succ}
        = 1 - c · (unscaledTail s)_o - c · ∑_{j≠o} (unscaledTail s)_j + (1-c)·(unscaledTail s)_o

The λ-trick leaves the output coordinate unscaled (`selectiveUnscale o c · o = ·o`),
so `sol(s)_{o.succ} = (unscaledTail s)_o`, and for `j ≠ o`,
`sol(s)_{j.succ} = c · (unscaledTail s)_j`. -/

/-- Simplex decomposition of `z₀` using the λ-trick structure.

On the Stage 2 simplex, `z₀(s) = 1 - w_o(s) - c·∑_{j≠o} w_j(s)` where
`w = selectiveUnscale o c (tail sol)` and `o = btc.pivp.output`.

Pure algebraic identity — no ODE content. -/
theorem stage2_z0_eq_unscaledTail_sum {d : ℕ} [NeZero d] {α ε c : ℝ} (hc : c ≠ 0)
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (s : ℝ) (_hs : 0 ≤ s)
    (h_sum : ∑ i, sol.trajectory s i = 1) :
    sol.trajectory s 0
      = 1 - selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))
              btc.pivp.output
        - c * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              selectiveUnscale btc.pivp.output c
                (Fin.tail (sol.trajectory s)) j := by
  -- Step 1: use conservation to move z₀ to the other side.
  have h_z0_eq : sol.trajectory s 0 = 1 - ∑ j : Fin d, sol.trajectory s j.succ := by
    have : sol.trajectory s 0 + ∑ j : Fin d, sol.trajectory s j.succ
        = ∑ i, sol.trajectory s i := by
      rw [Fin.sum_univ_succ]
    linarith [this, h_sum]
  rw [h_z0_eq]
  -- Step 2: split the tail sum by the λ-trick.
  -- At the output index o: sol(s)_{o.succ} = tail sol_o = unscale·o = w·o.
  -- At j ≠ o: sol(s)_{j.succ} = tail sol_j = c · w·j.
  set w := selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))
    with hw_def
  have h_tail_o : sol.trajectory s btc.pivp.output.succ = w btc.pivp.output := by
    simp [hw_def, Fin.tail, selectiveUnscale_output]
  have h_tail_ne : ∀ j ≠ btc.pivp.output,
      sol.trajectory s j.succ = c * w j := by
    intro j hj
    have : Fin.tail (sol.trajectory s) j = sol.trajectory s j.succ := rfl
    rw [hw_def, selectiveUnscale_ne hj]
    simp only [Fin.tail]
    field_simp
  -- Step 3: rearrange the finite sum.
  have h_sum_split : ∑ j : Fin d, sol.trajectory s j.succ
      = w btc.pivp.output + ∑ j ∈ Finset.univ.erase btc.pivp.output, c * w j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ btc.pivp.output)]
    rw [h_tail_o]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact h_tail_ne j (Finset.mem_erase.mp hj).1
  rw [h_sum_split]
  rw [Finset.mul_sum]
  ring

/-! ## Remark 14 step 2 — `z₀ ≥ c_room` from a BTC room condition

Given the reparametrization identity `w(s) = btc.sol(τ(s))`, if the BTC
trajectory satisfies `y_o(σ) + c·∑_{j≠o} y_j(σ) ≤ 1 - c_room` for all σ ≥ 0,
then `z₀(s) ≥ c_room` for all s in the window where the reparam identity
holds.

This lemma is *local* — it takes the reparam identity as a hypothesis on
`[0, T]`. The global version (using the extended reparam identity) is
`stage2_z0_lb_from_btc_room_global`. -/

/-- Local z₀ lower bound from the BTC room condition and reparametrization.

Hypotheses:
  * `h_room`: the input BTC satisfies `y_o(σ) + c·∑_{j≠o} y_j(σ) ≤ 1 - c_room`
    for every `σ ≥ 0`.
  * `h_reparam`: on `[0, T]`, the Stage 2 unscaled tail equals `btc.sol ∘ τ`.
  * `h_sum`: simplex conservation of `sol` on `[0, T]`.
  * `h_τ_nn`: `τ(s) ≥ 0` on `[0, T]`.

Conclusion: `z₀(s) ≥ c_room` on `[0, T]`. -/
theorem stage2_z0_lb_from_btc_room_local
    {d : ℕ} [NeZero d] {α : ℝ} {ε c c_room : ℝ} (hc : c ≠ 0)
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + c * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.sol.trajectory σ j ≤ 1 - c_room)
    (T : ℝ) (hT : 0 ≤ T)
    (h_reparam : Set.EqOn
      (fun s => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)))
      (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      (Set.Icc (0 : ℝ) T))
    (h_sum : ∀ s, 0 ≤ s → ∑ i, sol.trajectory s i = 1)
    (h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, c_room ≤ sol.trajectory s 0 := by
  intro s hs
  -- Decompose z₀ via the simplex identity.
  rw [stage2_z0_eq_unscaledTail_sum hc sol s hs.1 (h_sum s hs.1)]
  -- Substitute the reparametrization identity.
  have h_eq := h_reparam hs
  -- Apply componentwise: at output and at each j ≠ output.
  have h_eq_o : selectiveUnscale btc.pivp.output c
      (Fin.tail (sol.trajectory s)) btc.pivp.output
        = btc.sol.trajectory (stage2_effectiveTime sol s) btc.pivp.output := by
    exact congrFun h_eq btc.pivp.output
  have h_eq_j : ∀ j ∈ Finset.univ.erase btc.pivp.output,
      selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)) j
        = btc.sol.trajectory (stage2_effectiveTime sol s) j := by
    intro j _
    exact congrFun h_eq j
  rw [h_eq_o]
  rw [Finset.sum_congr rfl h_eq_j]
  -- Apply the room condition at σ = τ(s).
  have h_room_at := h_room _ (h_τ_nn s hs.1)
  linarith

/-! ## Remark 14 step 3 — global extension

`stage2_output_eq_btc_output_at_tau` (in Stages.lean) gives the reparam
identity on `[0, T]` conditioned on finite bounds `M, L`. The `M, L` bounds
are actually uniform in `T`:

  * `M := max(M_btc, 1/c)` where `M_btc` comes from `btc.bounded` (global)
    and `1/c` bounds the unscaled tail via the simplex + `selectiveUnscale_norm_le_div`.
  * `L` comes from `quadraticForm_locally_lipschitz` on `closedBall 0 M`.

We therefore apply the finite-T version pointwise at each `s` (taking `T := s`). -/

/-- Global reparametrization identity (Remark 14 step 3).

The unscaled tail of the Stage 2 solution equals `btc.sol ∘ τ` for all
`s ≥ 0`. Follows from the finite-T version `stage2_output_eq_btc_output_at_tau`
by taking `T := s + 1` and using `btc.bounded` + `quadraticForm_locally_lipschitz`
to supply uniform `M, L`. -/
theorem stage2_unscaledTail_eq_btcTraj_comp_tau_global
    {d : ℕ} [NeZero d] {α : ℝ} {ε c : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1)
    {btc : BoundedTimeComputable d α}
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_sol_nn : ∀ s, 0 ≤ s → ∀ i, 0 ≤ sol.trajectory s i)
    (h_sol_sum : ∀ s, 0 ≤ s → ∑ i, sol.trajectory s i = 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0) :
    ∀ s, 0 ≤ s →
      selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))
        = btc.sol.trajectory (stage2_effectiveTime sol s) := by
  -- Uniform simplex bound on sol: ‖sol(s)‖ ≤ 1.
  have h_sol_bdd : ∀ s, 0 ≤ s → ‖sol.trajectory s‖ ≤ 1 := by
    intro s hs
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (h_sol_nn s hs i)]
    calc sol.trajectory s i
        ≤ ∑ j, sol.trajectory s j :=
          Finset.single_le_sum (f := sol.trajectory s)
            (fun j _ => h_sol_nn s hs j) (Finset.mem_univ i)
      _ = 1 := h_sol_sum s hs
  -- z₀ bounds from simplex.
  have h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0 := fun s hs =>
    h_sol_nn s hs 0
  have h_z0_le : ∀ s, 0 ≤ s → sol.trajectory s 0 ≤ 1 := by
    intro s hs
    have h_coord := norm_le_pi_norm (sol.trajectory s) 0
    rw [Real.norm_eq_abs] at h_coord
    exact (abs_le.mp (h_coord.trans (h_sol_bdd s hs))).2
  -- btc trajectory bound (global).
  obtain ⟨M_btc, hM_btc_pos, hM_btc⟩ := btc.bounded
  set M : ℝ := max M_btc (1 / c) with hM_def
  have hM_pos : 0 < M := lt_of_lt_of_le hM_btc_pos (le_max_left _ _)
  have h_invc_le_M : 1 / c ≤ M := le_max_right _ _
  have h_Mbtc_le_M : M_btc ≤ M := le_max_left _ _
  -- Lipschitz of btc.pivp.field on closedBall 0 M.
  obtain ⟨L, hL_bound⟩ := quadraticForm_locally_lipschitz A B h_field M hM_pos
  set L' : ℝ := max L 0 with hL'_def
  have hL'_nn : 0 ≤ L' := le_max_right _ _
  have hL'_bound : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖btc.pivp.field x - btc.pivp.field y‖ ≤ L' * ‖x - y‖ := by
    intro x y hx hy
    exact (hL_bound x y hx hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- τ non-negativity (global).
  have h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s := fun s hs =>
    stage2_effectiveTime_nonneg hε.le sol h_z0_nn s hs
  -- Bound on w: ‖selectiveUnscale o c (Fin.tail sol(s))‖ ≤ 1/c ≤ M (global).
  have h_w_bdd_global : ∀ s, 0 ≤ s →
      ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖ ≤ M := by
    intro s hs
    have h_tail_bdd : ‖Fin.tail (sol.trajectory s)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      exact (norm_le_pi_norm (sol.trajectory s) i.succ).trans (h_sol_bdd s hs)
    calc ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖
        ≤ ‖Fin.tail (sol.trajectory s)‖ / c :=
          selectiveUnscale_norm_le_div _ hc hc1 _
      _ ≤ 1 / c := by
          rw [div_le_div_iff_of_pos_right hc]; exact h_tail_bdd
      _ ≤ M := h_invc_le_M
  -- Bound on btc.sol ∘ τ (global).
  have h_btc_bdd_global : ∀ s, 0 ≤ s →
      ‖btc.sol.trajectory (stage2_effectiveTime sol s)‖ ≤ M := fun s hs =>
    (hM_btc _ (h_τ_nn s hs)).trans h_Mbtc_le_M
  -- Pointwise extension: at each s ≥ 0, apply the finite-T version with T := s.
  intro s hs
  have h_w_bdd_local : ∀ u ∈ Set.Icc (0 : ℝ) s,
      ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory u))‖ ≤ M :=
    fun u hu => h_w_bdd_global u hu.1
  have h_btc_bdd_local : ∀ u ∈ Set.Icc (0 : ℝ) s,
      ‖btc.sol.trajectory (stage2_effectiveTime sol u)‖ ≤ M :=
    fun u hu => h_btc_bdd_global u hu.1
  have h_eqOn := stage2_unscaledTail_eq_btcTraj_comp_tau (ne_of_gt hc) sol
    h_zero_init h_z0_nn h_z0_le h_τ_nn s hs M L' hL'_nn
    h_w_bdd_local h_btc_bdd_local hL'_bound
  exact h_eqOn ⟨hs, le_refl s⟩

/-! ## Remark 14 step 4 — main theorem replacing `stage2_convergence_axiom` -/

/-- **Remark 14 replacement for `stage2_convergence_axiom`**.

Given the "room" condition on the input BTC's trajectory — which cannot be
derived from `btc.bounded` alone but IS a property of CRNs designed on the
simplex — this theorem discharges the Stage 2 convergence with NO new axiom
or monotonicity assumption.

Hypotheses beyond those of `stage2_convergence_axiom`:
  * `hc1 : c ≤ 1` (pins `c ∈ (0, 1]` given `0 < c`)
  * `A, B`: the BTC's explicit quadratic CRN decomposition
  * `h_sol_nn, h_sol_sum`: CRN invariance of the Stage 2 solution (nonneg + simplex)
  * `h_zero_init`: `btc.pivp.init o = 0` — the DNA 25 normalization
  * `h_room`: **the Remark 14 room condition on the BTC trajectory**. -/
theorem stage2_convergence_from_room
    {d : ℕ} [NeZero d] {α : ℝ} {ε c c_room : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1)
    (hc_room_pos : 0 < c_room) (hc_room_le_c : c_room ≤ c)
    (hε_c_room : 1 ≤ ε * c_room)
    {btc : BoundedTimeComputable d α}
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_sol_nn : ∀ s, 0 ≤ s → ∀ i, 0 ≤ sol.trajectory s i)
    (h_sol_sum : ∀ s, 0 ≤ s → ∑ i, sol.trajectory s i = 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + c * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.sol.trajectory σ j ≤ 1 - c_room) :
    ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > btc.modulus r →
      |sol.trajectory t (stage2_pivp ε c btc.pivp).output - α| <
        Real.exp (-(r : ℝ)) := by
  intro r t ht_nn ht_gt
  -- Step 1: get the global reparametrization identity.
  have h_reparam_global := stage2_unscaledTail_eq_btcTraj_comp_tau_global
    hε hc hc1 A B h_field sol h_sol_nn h_sol_sum h_zero_init
  -- Step 2: τ(s) ≥ 0 from z₀ ≥ 0 (simplex).
  have h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0 := fun s hs =>
    h_sol_nn s hs 0
  have h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s := fun s hs =>
    stage2_effectiveTime_nonneg hε.le sol h_z0_nn s hs
  -- Step 3: restate reparam identity as a local Set.EqOn and apply room lemma.
  have h_reparam_local : Set.EqOn
      (fun s => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)))
      (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      (Set.Icc (0 : ℝ) t) := fun s hs => h_reparam_global s hs.1
  have h_z0_lb_local := stage2_z0_lb_from_btc_room_local
    (ne_of_gt hc) sol h_room t ht_nn h_reparam_local h_sol_sum h_τ_nn
  -- Step 4: c_room ≤ z₀(s) for all s ∈ [0, t]. Extend via the same argument
  -- pointwise: for each s ≥ 0, apply the local lemma with T := s. Hence a
  -- GLOBAL h_z0_lb with `c_room` (not `c`).
  have h_z0_lb : ∀ s, 0 ≤ s → c_room ≤ sol.trajectory s 0 := by
    intro s hs
    have h_local : Set.EqOn
        (fun u => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory u)))
        (fun u => btc.sol.trajectory (stage2_effectiveTime sol u))
        (Set.Icc (0 : ℝ) s) := fun u hu => h_reparam_global u hu.1
    exact stage2_z0_lb_from_btc_room_local
      (ne_of_gt hc) sol h_room s hs h_local h_sol_sum h_τ_nn s ⟨hs, le_refl _⟩
  -- Step 5: τ(t) ≥ ε·c_room·t ≥ t, then compose with btc.convergence.
  -- Simplex bound on sol: ‖sol(s)‖ ≤ 1, mirroring `stage2_convergence_from_z0_invariant`.
  have h_sol_bdd : ∀ s, 0 ≤ s → ‖sol.trajectory s‖ ≤ 1 := by
    intro s hs
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (h_sol_nn s hs i)]
    calc sol.trajectory s i
        ≤ ∑ j, sol.trajectory s j :=
          Finset.single_le_sum (f := sol.trajectory s)
            (fun j _ => h_sol_nn s hs j) (Finset.mem_univ i)
      _ = 1 := h_sol_sum s hs
  have h_z0_le : ∀ s, 0 ≤ s → sol.trajectory s 0 ≤ 1 := by
    intro s hs
    have h_coord := norm_le_pi_norm (sol.trajectory s) 0
    rw [Real.norm_eq_abs] at h_coord
    exact (abs_le.mp (h_coord.trans (h_sol_bdd s hs))).2
  obtain ⟨M_btc, hM_btc_pos, hM_btc⟩ := btc.bounded
  set M : ℝ := max M_btc (1 / c) with hM_def
  have hM_pos : 0 < M := lt_of_lt_of_le hM_btc_pos (le_max_left _ _)
  have h_invc_le_M : 1 / c ≤ M := le_max_right _ _
  have h_Mbtc_le_M : M_btc ≤ M := le_max_left _ _
  obtain ⟨L, hL_bound⟩ := quadraticForm_locally_lipschitz A B h_field M hM_pos
  set L' : ℝ := max L 0 with hL'_def
  have hL'_nn : 0 ≤ L' := le_max_right _ _
  have hL'_bound : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M →
      ‖btc.pivp.field x - btc.pivp.field y‖ ≤ L' * ‖x - y‖ := by
    intro x y hx hy
    exact (hL_bound x y hx hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h_w_bdd : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖ ≤ M := by
    intro s hs
    have h_tail_bdd : ‖Fin.tail (sol.trajectory s)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      exact (norm_le_pi_norm (sol.trajectory s) i.succ).trans (h_sol_bdd s hs.1)
    calc ‖selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))‖
        ≤ ‖Fin.tail (sol.trajectory s)‖ / c :=
          selectiveUnscale_norm_le_div _ hc hc1 _
      _ ≤ 1 / c := by
          rw [div_le_div_iff_of_pos_right hc]; exact h_tail_bdd
      _ ≤ M := h_invc_le_M
  have h_btc_bdd : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖btc.sol.trajectory (stage2_effectiveTime sol s)‖ ≤ M := fun s hs =>
    (hM_btc _ (h_τ_nn s hs.1)).trans h_Mbtc_le_M
  -- Pointwise reparam at t.
  have h_eq :=
    stage2_output_eq_btc_output_at_tau (hc := ne_of_gt hc) sol h_zero_init
      (fun s hs => h_sol_nn s hs 0) h_z0_le h_τ_nn t ht_nn M L' hL'_nn
      h_w_bdd h_btc_bdd hL'_bound t ⟨ht_nn, le_refl _⟩
  -- τ lower bound via the c_room invariant.
  have h_τ_lb : ε * c_room * t ≤ stage2_effectiveTime sol t :=
    stage2_effectiveTime_lb hε.le sol ht_nn hc_room_pos.le
      (fun s hs => h_z0_lb s hs.1)
  have h_t_le_τ : t ≤ stage2_effectiveTime sol t := by
    calc t = 1 * t := (one_mul t).symm
      _ ≤ (ε * c_room) * t := mul_le_mul_of_nonneg_right hε_c_room ht_nn
      _ ≤ stage2_effectiveTime sol t := h_τ_lb
  have h_τ_gt : stage2_effectiveTime sol t > btc.modulus r :=
    lt_of_lt_of_le ht_gt h_t_le_τ
  rw [h_eq]
  exact btc.convergence r (stage2_effectiveTime sol t) h_τ_gt

/-! ## Summary

The Remark 14 chain is closed. `stage2_convergence_from_room` discharges the
content of `stage2_convergence_axiom` with NO new axioms, at the cost of:

  * The hypothesis `1 ≤ ε · c_room` (strengthening `1 ≤ ε · c` via `c_room ≤ c`);
  * The `h_room` hypothesis on the BTC trajectory — must be supplied by the
    upstream CRN construction (open obligation on the algebraic pipeline). -/

end Ripple
