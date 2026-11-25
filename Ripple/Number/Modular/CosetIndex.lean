/-
  Stage 2: Index of Γ₀(p) in SL₂(ℤ) for prime p.

  Theorem: [SL₂(ℤ) : Γ₀(p)] = p + 1

  Proof outline:
    SL₂(ℤ) acts on P¹(𝔽ₚ) = OnePoint (ZMod p) by Möbius transformations
    (via reduction mod p, then GL₂ action on the projective line).
    The action is transitive: T^n · S maps ∞ to n for any n.
    The stabilizer of ∞ is Γ₀(p): g • ∞ = ∞ ↔ c(g) ≡ 0 mod p.
    By orbit-stabilizer: index = |P¹(𝔽ₚ)| = p + 1.
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.SetTheory.Cardinal.Finite

open CongruenceSubgroup Matrix SpecialLinearGroup OnePoint

open scoped MatrixGroups ModularGroup

namespace Ripple.CosetIndex

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## SL₂(ℤ) action on P¹(𝔽ₚ) -/

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

/-- The composite monoid homomorphism SL₂(ℤ) → GL₂(𝔽ₚ). -/
noncomputable def sl2ToGL : SL(2, ℤ) →* GL (Fin 2) (ZMod p) :=
  SpecialLinearGroup.toGL.comp (SLMOD(p))

/-- SL₂(ℤ) acts on P¹(𝔽ₚ) = OnePoint (ZMod p) via reduction mod p. -/
noncomputable instance sl2ActionP1 :
    MulAction SL(2, ℤ) (OnePoint (ZMod p)) :=
  MulAction.compHom (OnePoint (ZMod p)) (sl2ToGL p)

/-! ## Stabilizer of ∞ is Γ₀(p) -/

theorem stabilizer_infty_eq_gamma0 :
    MulAction.stabilizer SL(2, ℤ) (∞ : OnePoint (ZMod p)) = Gamma0 p := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, Gamma0_mem]
  change (sl2ToGL p g) • (∞ : OnePoint (ZMod p)) = ∞ ↔ (g 1 0 : ZMod p) = 0
  rw [smul_infty_eq_self_iff]
  rfl

/-! ## Transitivity -/

/-- For `t : ZMod p`, the matrix `[[t.val, -1], [1, 0]] ∈ SL(2, ℤ)` sends `∞` to `t`
    under the projective action. -/
private noncomputable def liftMatrix (t : ZMod p) : SL(2, ℤ) :=
  ⟨!![(t.val : ℤ), -1; 1, 0], by
    simp [Matrix.det_fin_two_of]⟩

private lemma liftMatrix_smul_infty (t : ZMod p) :
    liftMatrix p t • (∞ : OnePoint (ZMod p)) = (t : OnePoint (ZMod p)) := by
  -- Unfold the action via the composite homomorphism.
  change sl2ToGL p (liftMatrix p t) • (∞ : OnePoint (ZMod p))
         = (t : OnePoint (ZMod p))
  -- Compute the GL action on ∞.
  rw [smul_infty_eq_ite]
  -- Compute the (0,0) and (1,0) entries: 1 0 = 1, 0 0 = t.
  have h10 : (sl2ToGL p (liftMatrix p t)) 1 0 = (1 : ZMod p) := by
    change ((1 : ℤ) : ZMod p) = 1
    exact Int.cast_one
  have h00 : (sl2ToGL p (liftMatrix p t)) 0 0 = t := by
    change ((t.val : ℤ) : ZMod p) = t
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  rw [h10, h00]
  simp

/-- SL₂(ℤ) acts transitively on P¹(𝔽ₚ).
    Proof: every point is reachable from `∞`, then compose. -/
instance sl2TransitiveP1 : MulAction.IsPretransitive SL(2, ℤ) (OnePoint (ZMod p)) := by
  refine ⟨fun x y => ?_⟩
  -- It suffices to show every point is reachable from ∞.
  suffices h : ∀ z : OnePoint (ZMod p),
      ∃ g : SL(2, ℤ), g • (∞ : OnePoint (ZMod p)) = z by
    obtain ⟨g₁, hg₁⟩ := h x
    obtain ⟨g₂, hg₂⟩ := h y
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    have hx : g₁⁻¹ • x = ∞ := by
      rw [← hg₁]; exact inv_smul_smul g₁ ∞
    rw [SemigroupAction.mul_smul, hx, hg₂]
  intro z
  cases z with
  | infty => exact ⟨1, one_smul _ _⟩
  | coe t => exact ⟨liftMatrix p t, liftMatrix_smul_infty p t⟩

/-! ## Cardinality of P¹(𝔽ₚ) -/

theorem card_onePoint_zmod :
    Nat.card (OnePoint (ZMod p)) = p + 1 := by
  change Nat.card (Option (ZMod p)) = p + 1
  rw [Finite.card_option, Nat.card_zmod]

/-! ## Main theorem -/

theorem gamma0_index_prime :
    (Gamma0 p).index = p + 1 := by
  rw [← stabilizer_infty_eq_gamma0 p,
      MulAction.index_stabilizer_of_transitive SL(2, ℤ)
        (∞ : OnePoint (ZMod p))]
  exact card_onePoint_zmod p

theorem gamma0_index_41 : (Gamma0 41).index = 42 := by
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  exact gamma0_index_prime 41

/-! ## Connection to the Sturm bound -/

/-- The Sturm bound for weight 1008 on Γ₀(41) is 3528. -/
theorem sturm_bound_value :
    1008 / 12 * ((Gamma0 41).index) = 3528 := by
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  simp [gamma0_index_prime]

end Ripple.CosetIndex
