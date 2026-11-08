/-
  Ripple.LPP.Replication — `m`-fold replication of a PLPP and fractional readouts

  Definition 9 of [LPP] reads a number as the total fraction of a set of *whole* states. A
  construction sometimes produces a trajectory whose limit is a rational combination
  `Σ_q (w_q / m) x_q(t)` with `0 ≤ w_q ≤ m` instead (the Stage 3 half-product lift does:
  `x_o = z_{oo} + ½ Σ_{j ≠ o} z_{oj}`). Replication turns such a readout into a marked set.

  Construction. Give every agent a passive copy index in `Fin m`: the replicated protocol on
  states `Q × [m]` has the rules `(qᵢ, r)(qⱼ, s) → α_{i,j,k,l} (q_k, r)(q_l, s)`. Each agent
  keeps its index, so if all copies of a state carry equal mass, `y_{(q, r)} = x_q / m`, then
  the replicated balance field is `1/m` times the original one at `q`
  (`replicate_balanceField_lift`), and `t ↦ x(t) / m` solves the replicated ODE. Marking
  `w_q` copies of each state `q` reads `Σ_q (w_q / m) x_q`.

  This construction is new to this formalization (the paper's Stage 3 uses ordered pairs, whose
  marked rows read `x_o` directly, but whose lifted field is not formally conservative; see
  `Ripple.LPP.SymmetricSquaring`). Paper proof: `docs/refactor/S1-LPP-PAPER.md` §2.
-/

import Ripple.LPP.Computation

namespace Ripple

/-- The flat encoding `Fin n × Fin m ≃ Fin (n * m)` of (state, copy) pairs. -/
def replicaEquiv (n m : ℕ) : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv

/-- A sum over the flat states is a sum over (state, copy) pairs. -/
theorem sum_replicaEquiv {M : Type*} [AddCommMonoid M] {n m : ℕ} (f : Fin (n * m) → M) :
    ∑ a, f a = ∑ q : Fin n × Fin m, f (replicaEquiv n m q) :=
  (Fintype.sum_equiv (replicaEquiv n m) _ f (fun _ => rfl)).symm

namespace PLPPTransitions

variable {n : ℕ} (tr : PLPPTransitions n)

/-- Probabilities of the replicated table on (state, copy) pairs: the states react as in `tr`,
and each agent keeps its copy index. -/
def replicaα {m : ℕ} (a b c e : Fin n × Fin m) : ℚ :=
  tr.α a.1 b.1 c.1 e.1 * ((if c.2 = a.2 then 1 else 0) * (if e.2 = b.2 then 1 else 0))

theorem replicaα_nonneg {m : ℕ} (a b c e : Fin n × Fin m) : 0 ≤ tr.replicaα a b c e := by
  unfold replicaα
  apply mul_nonneg (tr.nonneg _ _ _ _)
  split_ifs <;> norm_num

/-- Summing out the second output: the first output keeps the first input's copy. -/
theorem sum_replicaα_snd {m : ℕ} (a b c : Fin n × Fin m) :
    ∑ e, tr.replicaα a b c e =
      (if c.2 = a.2 then 1 else 0) * ∑ l, tr.α a.1 b.1 c.1 l := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_eq_single b.2 (fun s _ hs => by simp [replicaα, hs]) (by simp)]
  simp only [replicaα, ↓reduceIte, mul_one, one_mul]
  try ring

/-- Summing out the first output: the second output keeps the second input's copy. -/
theorem sum_replicaα_fst {m : ℕ} (a b e : Fin n × Fin m) :
    ∑ c, tr.replicaα a b c e =
      (if e.2 = b.2 then 1 else 0) * ∑ k, tr.α a.1 b.1 k e.1 := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single a.2 (fun r _ hr => by simp [replicaα, hr]) (by simp)]
  simp only [replicaα, ↓reduceIte, mul_one, one_mul]
  try ring

theorem sum_sum_replicaα {m : ℕ} (a b : Fin n × Fin m) :
    ∑ c, ∑ e, tr.replicaα a b c e = 1 := by
  simp_rw [tr.sum_replicaα_snd a b]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul, ite_mul, zero_mul]
  exact tr.sum_one a.1 b.1

/-- The `m`-fold replication of a PLPP: states `Fin n × Fin m` (flat-encoded), rules
`(qᵢ, r)(qⱼ, s) → α_{i,j,k,l} (q_k, r)(q_l, s)`. -/
def replicate (m : ℕ) : PLPPTransitions (n * m) where
  α a b c e := tr.replicaα ((replicaEquiv n m).symm a) ((replicaEquiv n m).symm b)
    ((replicaEquiv n m).symm c) ((replicaEquiv n m).symm e)
  nonneg a b c e := tr.replicaα_nonneg _ _ _ _
  sum_one a b := by
    simp only [sum_replicaEquiv (n := n) (m := m), Equiv.symm_apply_apply]
    exact tr.sum_sum_replicaα _ _

theorem replicate_α (m : ℕ) (a b c e : Fin (n * m)) :
    (tr.replicate m).α a b c e = tr.replicaα ((replicaEquiv n m).symm a)
      ((replicaEquiv n m).symm b) ((replicaEquiv n m).symm c) ((replicaEquiv n m).symm e) := rfl

/-- The uniform lift `y_{(q, r)} = x_q / m`. -/
noncomputable def replicaLift (m : ℕ) (x : Fin n → ℝ) : Fin (n * m) → ℝ :=
  fun a => x ((replicaEquiv n m).symm a).1 / m

theorem replicaLift_apply (m : ℕ) (x : Fin n → ℝ) (q : Fin n × Fin m) :
    replicaLift m x (replicaEquiv n m q) = x q.1 / m := by
  simp [replicaLift]

theorem sum_replicaLift {m : ℕ} (hm : 0 < m) (x : Fin n → ℝ) :
    ∑ a, replicaLift m x a = ∑ i, x i := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [sum_replicaEquiv]
  simp only [replicaLift_apply, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

private theorem cast_boole (p : Prop) [Decidable p] :
    ((if p then 1 else 0 : ℚ) : ℝ) = if p then 1 else 0 := by
  split_ifs <;> simp

/-- The replicated balance field at a uniform lift is `1/m` times the original balance field. -/
theorem replicate_balanceField_lift {m : ℕ} (hm : 0 < m) (x : Fin n → ℝ) (q : Fin n × Fin m) :
    (tr.replicate m).balanceField (replicaLift m x) (replicaEquiv n m q) =
      tr.balanceField x q.1 / m := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  -- production sums, read on pairs
  have hP1 : ∀ a b : Fin (n * m),
      (∑ c, ((tr.replicate m).α a b (replicaEquiv n m q) c : ℝ)) =
        (if q.2 = ((replicaEquiv n m).symm a).2 then 1 else 0) *
          ∑ l, (tr.α ((replicaEquiv n m).symm a).1 ((replicaEquiv n m).symm b).1 q.1 l : ℝ) := by
    intro a b
    simp only [replicate_α, sum_replicaEquiv (n := n) (m := m), Equiv.symm_apply_apply]
    rw [← Rat.cast_sum, tr.sum_replicaα_snd, Rat.cast_mul, Rat.cast_sum, cast_boole]
  have hP2 : ∀ a b : Fin (n * m),
      (∑ c, ((tr.replicate m).α a b c (replicaEquiv n m q) : ℝ)) =
        (if q.2 = ((replicaEquiv n m).symm b).2 then 1 else 0) *
          ∑ k, (tr.α ((replicaEquiv n m).symm a).1 ((replicaEquiv n m).symm b).1 k q.1 : ℝ) := by
    intro a b
    simp only [replicate_α, sum_replicaEquiv (n := n) (m := m), Equiv.symm_apply_apply]
    rw [← Rat.cast_sum, tr.sum_replicaα_fst, Rat.cast_mul, Rat.cast_sum, cast_boole]
  -- for fixed states, summing over the two copy indices gives the factor `m`
  have hcopy : ∀ i j : Fin n,
      (∑ r : Fin m, ∑ s : Fin m, x i / m * (x j / m) *
          ((if q.2 = r then 1 else 0) * ∑ l, (tr.α i j q.1 l : ℝ) +
            (if q.2 = s then 1 else 0) * ∑ k, (tr.α i j k q.1 : ℝ))) =
        x i * x j * (∑ l, (tr.α i j q.1 l : ℝ) + ∑ k, (tr.α i j k q.1 : ℝ)) / m := by
    intro i j
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, one_mul, zero_mul, mul_one,
      mul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    field_simp
    try ring
  have hprod :
      (∑ a, ∑ b, replicaLift m x a * replicaLift m x b *
        (∑ c, ((tr.replicate m).α a b (replicaEquiv n m q) c : ℝ) +
          ∑ c, ((tr.replicate m).α a b c (replicaEquiv n m q) : ℝ))) =
        (∑ i, ∑ j, x i * x j *
          (∑ l, (tr.α i j q.1 l : ℝ) + ∑ k, (tr.α i j k q.1 : ℝ))) / m := by
    simp only [hP1, hP2]
    simp only [sum_replicaEquiv (n := n) (m := m), Equiv.symm_apply_apply, replicaLift_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    exact hcopy i j
  have hdeg : 2 * replicaLift m x (replicaEquiv n m q) * ∑ c, replicaLift m x c =
      2 * x q.1 * (∑ k, x k) / m := by
    rw [replicaLift_apply, sum_replicaLift hm]
    ring
  unfold PLPPTransitions.balanceField
  rw [hprod, hdeg]
  ring

/-- A PLPP trajectory, lifted uniformly to the `m`-fold replication, solves its balance
equation. -/
theorem replicate_hasDerivAt {m : ℕ} (hm : 0 < m) {x : ℝ → Fin n → ℝ} {t : ℝ}
    (hx : HasDerivAt x (tr.balanceField (x t)) t) :
    HasDerivAt (fun s => replicaLift m (x s))
      ((tr.replicate m).balanceField (replicaLift m (x t))) t := by
  rw [hasDerivAt_pi]
  intro a
  obtain ⟨q, rfl⟩ := (replicaEquiv n m).surjective a
  rw [tr.replicate_balanceField_lift hm (x t) q]
  have hcoord := (hasDerivAt_pi.mp hx) q.1
  simpa [replicaLift, div_eq_mul_inv] using hcoord.mul_const ((m : ℝ)⁻¹)

end PLPPTransitions

/-- **Fractional readout.** A trajectory of a PLPP balance equation with the initial and
invariance conditions of [LPP] Definition 9, whose weighted readout `Σ_q (w_q / m) x_q(t)` with
integer weights `w_q ≤ m` tends to `ν`, gives a PLPP computation of `ν` (on the `m`-fold
replication, marking `w_q` copies of each state `q`). -/
theorem isPLPPComputable_of_fractional_readout {n : ℕ} (tr : PLPPTransitions n)
    (x : ℝ → Fin n → ℝ)
    (init_rational : ∀ i, ∃ q : ℚ, x 0 i = (q : ℝ))
    (init_simplex : ∑ i, x 0 i = 1)
    (init_nonneg : ∀ i, 0 ≤ x 0 i)
    (simplex : ∀ t, 0 ≤ t → ∑ i, x t i = 1)
    (nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ x t i)
    (ode : ∀ t, 0 ≤ t → HasDerivAt x (tr.balanceField (x t)) t)
    (m : ℕ) (hm : 0 < m) (w : Fin n → ℕ) (hw : ∀ i, w i ≤ m) {ν : ℝ}
    (readout : Filter.Tendsto (fun t => ∑ i, ((w i : ℝ) / m) * x t i) Filter.atTop (nhds ν)) :
    IsPLPPComputable ν := by
  classical
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  -- marked copies: `(q, r)` with `r < w q`
  let M : Finset (Fin (n * m)) :=
    (Finset.univ.filter fun q : Fin n × Fin m => (q.2 : ℕ) < w q.1).map
      (replicaEquiv n m).toEmbedding
  have hcount : ∀ i : Fin n,
      ((Finset.univ.filter fun r : Fin m => (r : ℕ) < w i).card : ℝ) = w i := by
    intro i
    have hcard : (Finset.univ.filter fun r : Fin m => (r : ℕ) < w i).card = w i := by
      rw [Fin.card_filter_val_lt]
      exact min_eq_right (hw i)
    exact_mod_cast hcard
  have hread : ∀ t, (∑ a ∈ M, PLPPTransitions.replicaLift m (x t) a) =
      ∑ i, ((w i : ℝ) / m) * x t i := by
    intro t
    rw [Finset.sum_map, Finset.sum_filter]
    simp only [Equiv.toEmbedding_apply, PLPPTransitions.replicaLift_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount i]
    ring
  refine ⟨⟨n * m, tr.replicate m, M, ?_⟩⟩
  exact
    { sol := fun t => PLPPTransitions.replicaLift m (x t)
      init_rational := by
        intro a
        obtain ⟨q, hq⟩ := init_rational (((replicaEquiv n m).symm a).1)
        exact ⟨q / m, by simp [PLPPTransitions.replicaLift, hq]⟩
      init_simplex := by rw [PLPPTransitions.sum_replicaLift hm]; exact init_simplex
      init_nonneg := fun a => div_nonneg (init_nonneg _) (Nat.cast_nonneg _)
      simplex := fun t ht => by rw [PLPPTransitions.sum_replicaLift hm]; exact simplex t ht
      nonneg := fun t ht a => div_nonneg (nonneg t ht _) (Nat.cast_nonneg _)
      ode := fun t ht => tr.replicate_hasDerivAt hm (ode t ht)
      readout_tendsto := by
        simp_rw [hread]
        exact readout }

end Ripple
