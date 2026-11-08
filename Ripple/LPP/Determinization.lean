/-
  Ripple.LPP.Determinization — [LPP] Theorem 17 (= [BFK] Lemma 4)

  [LPP] Theorem 17 (p. 23): if a PLPP with rational probabilities computes `ν ∈ [0, 1]`, then a
  deterministic LPP computes `ν`. The paper cites [BFK] (Bournez, Fraigniaud, Koegler,
  MFCS 2012), Lemma 4, and remarks that the construction "still correctly encodes the balance
  equation", so the theorem also holds for the continuum-of-equilibria Definition 9.

  The construction and its balance-equation computation are in `Ripple.LPP.Derandomization`:
  with `m` a common denominator of the probabilities, the deterministic protocol on states
  `Q × [m]` is `(qᵢ, r)(qⱼ, s) → (q_k, r + 1)(q_l, s + 1)`, where `(k, l)` is the outcome whose
  block of `m · α_{i,j,·,·}` consecutive slots contains `r + s mod m`. The uniform lift
  `y_{(q, r)} = x_q / m` of a PLPP trajectory solves its balance equation
  (`derandomize_preserves_continuum_computation`). This module only identifies that table as a
  deterministic transition function (`LPPTransitions`), so the result lands in the faithful
  predicate `IsLPPComputable` of `Ripple.LPP.Computation`. The paper-level proof is
  `docs/refactor/S1-THM17.md`.
-/

import Ripple.LPP.Computation
import Ripple.LPP.Derandomization

namespace Ripple

/-- Two transition tables with the same probabilities are equal. -/
theorem PLPPTransitions.ext_α {n : ℕ} {T₁ T₂ : PLPPTransitions n} (h : T₁.α = T₂.α) :
    T₁ = T₂ := by
  cases T₁
  cases T₂
  cases h
  rfl

/-- The derandomized product protocol of [BFK] Lemma 4 as a deterministic transition function:
`(qᵢ, r)(qⱼ, s) ↦ (q_k, r + 1)(q_l, s + 1)` with `(k, l) = coinSlot i j (r + s)`. -/
noncomputable def PLPPTransitions.derandomizeLPP {d : ℕ} (tr : PLPPTransitions d) :
    LPPTransitions (d * tr.commonDenom) where
  step a b :=
    let hm := tr.commonDenom_pos
    let a' := finProdEquiv d tr.commonDenom a
    let b' := finProdEquiv d tr.commonDenom b
    let out := tr.coinSlot a'.1 b'.1 (coinAdd hm a'.2 b'.2)
    (finProdEncode d tr.commonDenom out.1 (nextCoin hm a'.2),
      finProdEncode d tr.commonDenom out.2 (nextCoin hm b'.2))

/-- The `{0,1}` PLPP `derandomizeTransitions` is the deterministic table `derandomizeLPP`. -/
theorem PLPPTransitions.derandomizeLPP_toPLPP {d : ℕ} (tr : PLPPTransitions d) :
    tr.derandomizeLPP.toPLPP = tr.derandomizeTransitions := by
  apply PLPPTransitions.ext_α
  have key : ∀ (p q c e : Fin (d * tr.commonDenom)),
      (((if (p, q) = (c, e) then 1 else 0 : ℕ) : ℚ)) = if c = p ∧ e = q then 1 else 0 := by
    intro p q c e
    by_cases h : c = p ∧ e = q
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have hne : (p, q) ≠ (c, e) := fun h' =>
        h ⟨(Prod.mk.inj h').1.symm, (Prod.mk.inj h').2.symm⟩
      rw [if_neg h, if_neg hne]
      simp
  funext a b c e
  exact key _ _ c e

/-- **[LPP] Theorem 17** ([BFK] Lemma 4), continuum form: a number computed by a PLPP (with
rational probabilities, which `PLPPTransitions` always has) is computed by a deterministic
LPP. -/
theorem IsPLPPComputable.isLPPComputable {ν : ℝ} (h : IsPLPPComputable ν) :
    IsLPPComputable ν := by
  obtain ⟨⟨n, tr, M, C⟩⟩ := h
  obtain ⟨C'⟩ := derandomize_preserves_continuum_computation C
  rw [← tr.derandomizeLPP_toPLPP] at C'
  exact ⟨⟨_, tr.derandomizeLPP, _, C'⟩⟩

/-- [LPP] Definition 9: the LPP and PLPP clauses define the same class of numbers
(Theorem 17 and the trivial converse). -/
theorem isLPPComputable_iff_isPLPPComputable {ν : ℝ} :
    IsLPPComputable ν ↔ IsPLPPComputable ν :=
  ⟨IsLPPComputable.isPLPPComputable, IsPLPPComputable.isLPPComputable⟩

end Ripple
