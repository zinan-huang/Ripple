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
    (T : ℝ) (_hT : 0 ≤ T)
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
    (hc_room_pos : 0 < c_room) (_hc_room_le_c : c_room ≤ c)
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

/-! ## Axiom-free Stage 2 ODE gate

Parallel entry point to `stage2_ode_axiom`, invoking `stage2_convergence_from_room`
(not `stage2_convergence_axiom`). Callers that can supply the room condition and
zero-init normalization get an axiom-free Stage 2 ODE. -/

/-- **Axiom-free replacement for `stage2_ode_axiom`**.

Same conclusion as `stage2_ode_axiom` but the convergence proof uses
`stage2_convergence_from_room`, so this theorem introduces no new axiom.

Extra hypotheses beyond `stage2_ode_axiom`:
  * `hc1 : c ≤ 1` (pins `c ∈ (0, 1]`)
  * `c_room : ℝ`, `hc_room_pos : 0 < c_room`, `hc_room_le_c : c_room ≤ c`
  * `hε_c_room : 1 ≤ ε * c_room` (strengthens `1 ≤ ε * c`)
  * `h_zero_init : btc.pivp.init btc.pivp.output = 0`
  * `h_room`: Remark 14 room condition on the upstream BTC trajectory. -/
theorem stage2_ode_axiomless_from_room {d : ℕ} [NeZero d] {α : ℝ}
    (btc : BoundedTimeComputable d α) (ε c c_room : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1)
    (hc_room_pos : 0 < c_room) (hc_room_le_c : c_room ≤ c)
    (hε_c_room : 1 ≤ ε * c_room)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_sum_le : c * ∑ j, btc.pivp.init j ≤ 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + c * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.sol.trajectory σ j ≤ 1 - c_room) :
    ∃ sol : PIVP.Solution (stage2_pivp ε c btc.pivp),
      ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > btc.modulus r →
        |sol.trajectory t (stage2_pivp ε c btc.pivp).output - α| <
          Real.exp (-(r : ℝ)) := by
  -- Reconstruct CRN from A, B (mirrors `stage2_ode_axiom`).
  have crn : IsCRNImplementable d btc.pivp.field := {
    prod := fun i x => ∑ a, ∑ b, A i a b * x a * x b
    degr := fun i x => ∑ a, B i a * x a
    prod_pos := fun i x hx => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hA i a b) (hx a)) (hx b)
    degr_pos := fun i x hx => Finset.sum_nonneg fun a _ => mul_nonneg (hB i a) (hx a)
    field_eq := fun x i => h_field i x }
  let P := stage2_pivp ε c btc.pivp
  have h_crn' : IsCRNImplementable (d + 1) P.field :=
    (stage2_field_tpp (o := btc.pivp.output) hε.le hc crn).toIsCRNImplementable
  have h_cons' : IsConservative P.field :=
    balancingDilation_conservative _
  have h_lip' : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (d + 1) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖P.field x - P.field y‖ ≤ L * ‖x - y‖ :=
    cubicForm_locally_lipschitz
      (stage2_field_cubicForm (o := btc.pivp.output) hε.le hc A B hA hB h_field)
  have h_init_nn' : ∀ i, 0 ≤ P.init i :=
    stage2_init_nonneg hc.le h_init_nn h_sum_le
  have h_init_simp : ∑ i, P.init i = 1 :=
    stage2_init_simplex c btc.pivp.init
  -- Existence of the global solution on [0,∞).
  let sol := crn_simplex_global_ode_solution P h_crn' h_cons' h_lip' h_init_nn' h_init_simp
  -- Extract TPP & cubic-form data needed to derive simplex + non-negativity.
  have tpp' : IsTPPImplementable (d + 1) P.field :=
    stage2_field_tpp (o := btc.pivp.output) hε.le hc crn
  have s' : Stage2CubicForm (d + 1) P.field :=
    stage2_field_cubicForm (o := btc.pivp.output) hε.le hc A B hA hB h_field
  -- Simplex invariance and non-negativity of `sol` (proved CRN invariants).
  have h_sol_sum : ∀ t, 0 ≤ t → ∑ i, sol.trajectory t i = 1 :=
    fun t ht => conservative_trajectory_simplex sol tpp'.conservative
      (stage2_init_simplex c btc.pivp.init) ht
  have h_sol_nn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol.trajectory t i :=
    fun t ht => crn_nonneg_invariance sol tpp'.toIsCRNImplementable
      (stage2_init_nonneg hc.le h_init_nn h_sum_le)
      (cubicForm_locally_lipschitz s') t ht
  -- Discharge convergence via the axiom-free room lemma.
  refine ⟨sol, ?_⟩
  intro r t ht_nn ht_gt
  exact stage2_convergence_from_room (d := d) (α := α) (ε := ε) (c := c) (c_room := c_room)
    hε hc hc1 hc_room_pos hc_room_le_c hε_c_room
    (btc := btc) A B h_field sol h_sol_nn h_sol_sum h_zero_init h_room r t ht_nn ht_gt

/-! ## Axiom-free Stage 2 core entry

Parallel to the private `stage2_core` in `Stages.lean`: threads the Remark 14
room hypothesis through, producing the same conclusion as `stage2_core` with
no use of `stage2_convergence_axiom`. -/

/-- **Axiom-free Stage 2 core**. Same conclusion as the private `stage2_core`,
derived via `stage2_convergence_from_room`. Parameters `ε, c` are picked
internally: `c := c_room`, `ε := 1 / c_room`. The caller supplies

  * `c_room ∈ (0, 1]` with `c_room ∈ ℚ`
  * `c_room · ∑ init ≤ 1` (same shape as the internal `h_sum_le`)
  * `h_zero_init`, `h_room` (Remark 14 input). -/
theorem stage2_core_from_room {d : ℕ} [NeZero d] {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.pivp.init i = ↑q)
    (c_room : ℝ) (hc_room_pos : 0 < c_room) (hc_room_le_1 : c_room ≤ 1)
    (hc_room_q : ∃ q : ℚ, c_room = (q : ℝ))
    (h_sum_le_room : c_room * ∑ j, btc.pivp.init j ≤ 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + c_room * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.sol.trajectory σ j ≤ 1 - c_room) :
    ∃ (d' : ℕ) (btc' : BoundedTimeComputable d' α),
      ∃ (_ : IsTPPImplementable d' btc'.pivp.field)
        (_ : Stage2CubicForm d' btc'.pivp.field),
        (∀ t, 0 ≤ t → ∑ i, btc'.sol.trajectory t i = 1) ∧
        (∀ t, 0 ≤ t → ∀ i, 0 ≤ btc'.sol.trajectory t i) ∧
        (∀ i, ∃ q : ℚ, btc'.sol.trajectory 0 i = ↑q) ∧
        (∀ r, btc'.modulus r = max (btc.modulus r) 0) := by
  -- Parameter choice: ε := 1 / c_room, c := c_room. Then ε·c_room = 1.
  set ε : ℝ := 1 / c_room with hε_def
  set c : ℝ := c_room with hc_def
  have hε : 0 < ε := by rw [hε_def]; exact one_div_pos.mpr hc_room_pos
  have hc : 0 < c := hc_room_pos
  have hc1 : c ≤ 1 := hc_room_le_1
  have hε_c : 1 ≤ ε * c_room := by
    rw [hε_def, div_mul_cancel₀ 1 (ne_of_gt hc_room_pos)]
  have h_sum_le : c * ∑ j, btc.pivp.init j ≤ 1 := h_sum_le_room
  -- Get ODE existence + convergence via the axiomless gate.
  obtain ⟨sol, h_conv⟩ :=
    stage2_ode_axiomless_from_room btc ε c c_room hε hc hc1 hc_room_pos le_rfl hε_c
      A B hA hB h_field h_init_nn h_sum_le h_zero_init h_room
  -- Reconstruct CRN decomposition from A, B (mirrors `stage2_core`).
  have crn : IsCRNImplementable d btc.pivp.field := {
    prod := fun i x => ∑ a, ∑ b, A i a b * x a * x b
    degr := fun i x => ∑ a, B i a * x a
    prod_pos := fun i x hx => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hA i a b) (hx a)) (hx b)
    degr_pos := fun i x hx => Finset.sum_nonneg fun a _ => mul_nonneg (hB i a) (hx a)
    field_eq := fun x i => h_field i x }
  -- TPP and CubicForm structure on the Stage 2 system.
  have tpp' : IsTPPImplementable (d + 1) (stage2_pivp ε c btc.pivp).field :=
    stage2_field_tpp (o := btc.pivp.output) hε.le hc crn
  have s' : Stage2CubicForm (d + 1) (stage2_pivp ε c btc.pivp).field :=
    stage2_field_cubicForm (o := btc.pivp.output) hε.le hc A B hA hB h_field
  -- Simplex + non-negativity invariants on sol.
  have h_simplex : ∀ t, 0 ≤ t → ∑ i, sol.trajectory t i = 1 :=
    fun t ht => conservative_trajectory_simplex sol tpp'.conservative
      (stage2_init_simplex c btc.pivp.init) ht
  have h_nn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol.trajectory t i :=
    fun t ht => crn_nonneg_invariance sol tpp'.toIsCRNImplementable
      (stage2_init_nonneg hc.le h_init_nn h_sum_le)
      (cubicForm_locally_lipschitz s') t ht
  -- Boundedness on simplex.
  have h_bounded : (stage2_pivp ε c btc.pivp).IsBounded sol.trajectory := by
    refine ⟨2, two_pos, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (h_nn t ht i)]
    calc sol.trajectory t i
        ≤ ∑ j, sol.trajectory t j :=
          Finset.single_le_sum (fun j _ => h_nn t ht j) (Finset.mem_univ i)
      _ = 1 := h_simplex t ht
      _ ≤ 2 := by norm_num
  -- Build the Stage 2 BTC. `h_conv` has the extra `0 ≤ t` hypothesis; strip it
  -- since `ht_gt : t > btc.modulus r` together with modulus ≥ 0 gives t ≥ 0.
  -- The BoundedTimeComputable.convergence expects the bare form
  -- `∀ r t, t > modulus r → ...`, so we derive 0 ≤ t from the modulus being
  -- non-negative on the pipeline. In Ripple's pipeline, `btc.modulus` outputs
  -- non-negative reals by convention. We case split on t ≥ 0 or not.
  let btc' : BoundedTimeComputable (d + 1) α := {
    pivp := stage2_pivp ε c btc.pivp
    sol := sol
    modulus := fun r => max (btc.modulus r) 0
    bounded := h_bounded
    convergence := by
      intro r t ht
      have ht_nn : 0 ≤ t := lt_of_le_of_lt (le_max_right _ _) ht |>.le
      have ht_btc : t > btc.modulus r := lt_of_le_of_lt (le_max_left _ _) ht
      exact h_conv r t ht_nn ht_btc }
  refine ⟨d + 1, btc', tpp', s', h_simplex, h_nn, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i
    have h_init := congr_fun sol.init_cond i
    rw [show btc'.sol.trajectory 0 i = sol.trajectory 0 i from rfl, h_init]
    exact stage2_init_rational hc_room_q h_init_rat i
  · intro r
    rfl

/-! ## Axiom-free Stage 2 → LPP composition

Chains `stage2_core_from_room` with `tpp_to_lpp` to yield
`IsLPPComputable α` directly from a quadratic BTC + room hypothesis,
bypassing `stage2_convergence_axiom`. -/

/-- **Axiom-free Stage 2 → LPP**. Given a BTC with explicit quadratic CRN
decomposition, rational init, and the Remark 14 room condition for some
rational `c_room ∈ (0, 1]` with `c_room · ∑ init ≤ 1`, concludes
`IsLPPComputable α` — no use of `stage2_convergence_axiom`. -/
theorem stage2_to_lpp_from_room {d : ℕ} [NeZero d] {α : ℝ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (btc : BoundedTimeComputable d α)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.pivp.init i = ↑q)
    (c_room : ℝ) (hc_room_pos : 0 < c_room) (hc_room_le_1 : c_room ≤ 1)
    (hc_room_q : ∃ q : ℚ, c_room = (q : ℝ))
    (h_sum_le_room : c_room * ∑ j, btc.pivp.init j ≤ 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + c_room * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.sol.trajectory σ j ≤ 1 - c_room) :
    ∃ _ : IsLPPComputable α, True := by
  obtain ⟨d', btc', tpp', s', h_simp, h_nn, h_rat, _h_mod⟩ :=
    stage2_core_from_room btc A B hA hB h_field h_init_nn h_init_rat
      c_room hc_room_pos hc_room_le_1 hc_room_q h_sum_le_room h_zero_init h_room
  exact tpp_to_lpp hα01 btc' tpp' s' h_simp h_nn h_rat

/-- Quantitative axiom-free Stage 2 → LPP.
Stage 2 changes the modulus only by `max (·) 0`, and Stage 3 contributes the
explicit `+1` slack from `tpp_to_lpp_with_modulus`. -/
theorem stage2_to_lpp_from_room_with_modulus {d : ℕ} [NeZero d] {α : ℝ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (btc : BoundedTimeComputable d α)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.pivp.init i = ↑q)
    (c_room : ℝ) (hc_room_pos : 0 < c_room) (hc_room_le_1 : c_room ≤ 1)
    (hc_room_q : ∃ q : ℚ, c_room = (q : ℝ))
    (h_sum_le_room : c_room * ∑ j, btc.pivp.init j ≤ 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + c_room * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.sol.trajectory σ j ≤ 1 - c_room) :
    ∃ h : IsLPPComputable α,
      ∀ r : ℕ, ∀ t : ℝ, t > max (btc.modulus r) 0 + 1 →
        |∑ i ∈ h.marked, h.sol t i - α| < Real.exp (-(r : ℝ)) := by
  obtain ⟨d', btc', tpp', s', h_simp, h_nn, h_rat, h_mod⟩ :=
    stage2_core_from_room btc A B hA hB h_field h_init_nn h_init_rat
      c_room hc_room_pos hc_room_le_1 hc_room_q h_sum_le_room h_zero_init h_room
  obtain ⟨h, hh⟩ := tpp_to_lpp_with_modulus hα01 btc' tpp' s' h_simp h_nn h_rat
  refine ⟨h, ?_⟩
  intro r t ht
  have ht1 : t > max (btc'.modulus r + 1) 0 := by
    rw [h_mod r]
    have hpos : 0 ≤ max (btc.modulus r) 0 + 1 := by positivity
    simpa [max_eq_left hpos] using ht
  exact hh r t ht1

/-- **Axiom-free Stage 2 → LPP from Stage 1 trajectory bounds**
(closes [LPP] Remark 14's room condition internally via the λ-trick).

Given a Stage 1 BTC with uniform per-species bounds:
  * output satisfies `x_o(σ) ≤ M_out` for all `σ ≥ 0`,
  * non-output species satisfy `0 ≤ x_j(σ) ≤ M_rest` for all `j ≠ o`, `σ ≥ 0`,
and the "small-λ" slack
  `c_room · (d-1) · M_rest ≤ 1 - c_room - M_out`,
the Remark 14 room invariant follows purely algebraically, so this wrapper
needs no `h_room` input. This matches the paper's proof of Theorem 13
(Operation 3, p. 15–16: "pick 0 < λ < 1 small enough that
`x₁ + λ(x₂ + ⋯ + xₙ) < 1 − c`"). -/
theorem stage2_to_lpp_from_bounds {d : ℕ} [NeZero d] {α : ℝ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (btc : BoundedTimeComputable d α)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.pivp.init i = ↑q)
    (c_room : ℝ) (hc_room_pos : 0 < c_room) (hc_room_le_1 : c_room ≤ 1)
    (hc_room_q : ∃ q : ℚ, c_room = (q : ℝ))
    (h_sum_le_room : c_room * ∑ j, btc.pivp.init j ≤ 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (M_out : ℝ)
    (h_out_le : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output ≤ M_out)
    (M_rest : ℝ) (_hM_rest_nn : 0 ≤ M_rest)
    (h_rest_nn : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc.pivp.output →
      0 ≤ btc.sol.trajectory σ j)
    (h_rest_le : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc.pivp.output →
      btc.sol.trajectory σ j ≤ M_rest)
    (h_small_lambda :
      c_room * (((d : ℕ) - 1 : ℕ) : ℝ) * M_rest ≤ 1 - c_room - M_out) :
    ∃ _ : IsLPPComputable α, True := by
  apply stage2_to_lpp_from_room hα01 btc A B hA hB h_field h_init_nn h_init_rat
    c_room hc_room_pos hc_room_le_1 hc_room_q h_sum_le_room h_zero_init
  -- Close h_room algebraically from the bounds.
  intro σ hσ
  set o := btc.pivp.output
  set S : Finset (Fin d) := Finset.univ.erase o
  -- Bound the erased sum by (d - 1) · M_rest.
  have h_card : (S.card : ℝ) = ((d : ℕ) - 1 : ℕ) := by
    simp [S, Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ,
      Fintype.card_fin]
  have h_sum_le : ∑ j ∈ S, btc.sol.trajectory σ j ≤ (S.card : ℝ) * M_rest := by
    have : ∀ j ∈ S, btc.sol.trajectory σ j ≤ M_rest := by
      intro j hj
      have hj_ne : j ≠ o := (Finset.mem_erase.mp hj).1
      exact h_rest_le σ hσ j hj_ne
    calc ∑ j ∈ S, btc.sol.trajectory σ j
        ≤ ∑ _ ∈ S, M_rest := Finset.sum_le_sum (fun j hj => this j hj)
      _ = (S.card : ℝ) * M_rest := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h_sum_le' : ∑ j ∈ S, btc.sol.trajectory σ j
      ≤ (((d : ℕ) - 1 : ℕ) : ℝ) * M_rest := by
    rw [← h_card]; exact h_sum_le
  have h_sum_nn : 0 ≤ ∑ j ∈ S, btc.sol.trajectory σ j :=
    Finset.sum_nonneg fun j hj =>
      h_rest_nn σ hσ j (Finset.mem_erase.mp hj).1
  -- Assemble the room bound.
  calc btc.sol.trajectory σ o + c_room * ∑ j ∈ S, btc.sol.trajectory σ j
      ≤ M_out + c_room * ((((d : ℕ) - 1 : ℕ) : ℝ) * M_rest) := by
        have h1 := h_out_le σ hσ
        have h2 : c_room * ∑ j ∈ S, btc.sol.trajectory σ j
            ≤ c_room * ((((d : ℕ) - 1 : ℕ) : ℝ) * M_rest) :=
          mul_le_mul_of_nonneg_left h_sum_le' hc_room_pos.le
        linarith
    _ = M_out + c_room * (((d : ℕ) - 1 : ℕ) : ℝ) * M_rest := by ring
    _ ≤ 1 - c_room := by linarith [h_small_lambda]

/-- Quantitative Stage 2 → LPP from Stage 1 trajectory bounds. -/
theorem stage2_to_lpp_from_bounds_with_modulus {d : ℕ} [NeZero d] {α : ℝ}
    (hα01 : 0 ≤ α ∧ α ≤ 1)
    (btc : BoundedTimeComputable d α)
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.pivp.init i = ↑q)
    (c_room : ℝ) (hc_room_pos : 0 < c_room) (hc_room_le_1 : c_room ≤ 1)
    (hc_room_q : ∃ q : ℚ, c_room = (q : ℝ))
    (h_sum_le_room : c_room * ∑ j, btc.pivp.init j ≤ 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (M_out : ℝ)
    (h_out_le : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output ≤ M_out)
    (M_rest : ℝ) (_hM_rest_nn : 0 ≤ M_rest)
    (h_rest_nn : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc.pivp.output →
      0 ≤ btc.sol.trajectory σ j)
    (h_rest_le : ∀ σ, 0 ≤ σ → ∀ j, j ≠ btc.pivp.output →
      btc.sol.trajectory σ j ≤ M_rest)
    (h_small_lambda :
      c_room * (((d : ℕ) - 1 : ℕ) : ℝ) * M_rest ≤ 1 - c_room - M_out) :
    ∃ h : IsLPPComputable α,
      ∀ r : ℕ, ∀ t : ℝ, t > max (btc.modulus r) 0 + 1 →
        |∑ i ∈ h.marked, h.sol t i - α| < Real.exp (-(r : ℝ)) := by
  apply stage2_to_lpp_from_room_with_modulus hα01 btc A B hA hB h_field h_init_nn h_init_rat
    c_room hc_room_pos hc_room_le_1 hc_room_q h_sum_le_room h_zero_init
  intro σ hσ
  set o := btc.pivp.output
  set S : Finset (Fin d) := Finset.univ.erase o
  have h_card : (S.card : ℝ) = ((d : ℕ) - 1 : ℕ) := by
    simp [S, Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ,
      Fintype.card_fin]
  have h_sum_le : ∑ j ∈ S, btc.sol.trajectory σ j ≤ (S.card : ℝ) * M_rest := by
    have : ∀ j ∈ S, btc.sol.trajectory σ j ≤ M_rest := by
      intro j hj
      have hj_ne : j ≠ o := (Finset.mem_erase.mp hj).1
      exact h_rest_le σ hσ j hj_ne
    calc ∑ j ∈ S, btc.sol.trajectory σ j
        ≤ ∑ _ ∈ S, M_rest := Finset.sum_le_sum (fun j hj => this j hj)
      _ = (S.card : ℝ) * M_rest := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h_sum_le' : ∑ j ∈ S, btc.sol.trajectory σ j
      ≤ (((d : ℕ) - 1 : ℕ) : ℝ) * M_rest := by
    rw [← h_card]; exact h_sum_le
  have h_sum_nn : 0 ≤ ∑ j ∈ S, btc.sol.trajectory σ j :=
    Finset.sum_nonneg fun j hj =>
      h_rest_nn σ hσ j (Finset.mem_erase.mp hj).1
  calc btc.sol.trajectory σ o + c_room * ∑ j ∈ S, btc.sol.trajectory σ j
      ≤ M_out + c_room * ((((d : ℕ) - 1 : ℕ) : ℝ) * M_rest) := by
        have h1 := h_out_le σ hσ
        have h2 : c_room * ∑ j ∈ S, btc.sol.trajectory σ j
            ≤ c_room * ((((d : ℕ) - 1 : ℕ) : ℝ) * M_rest) :=
          mul_le_mul_of_nonneg_left h_sum_le' hc_room_pos.le
        linarith
    _ = M_out + c_room * (((d : ℕ) - 1 : ℕ) : ℝ) * M_rest := by ring
    _ ≤ 1 - c_room := by linarith [h_small_lambda]

end Ripple
