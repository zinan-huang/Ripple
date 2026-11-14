/-
  Ripple.LPP.NAPTheoremFour — Theorem 4 of the PP-to-NAP write-up (§6): normal stability of an
  interior equilibrium of the cubed NAP with exchange reactions.

  Setting: `f` a syntactic quartic protocol field on `n` species (`QuarticPP n`, e.g. the r²-lift of a
  PP), `w` a weighted protocol realising its cubed demand (`Realizes (veroneseLift n 3) w (demand n f)`,
  e.g. the transportation NAP), `x*` an equilibrium of `f` in the open simplex, `v* = Ver x*`. For a
  rational exchange rate `K` the protocol `w + K • wE` is the routed NAP plus the exchange reactions.

  * `exchange_keeps_realisation`: `w + K wE` is still a non-negative NAP realisation of the lift;
  * `normal_stability_interior` (**Theorem 4**): there is `K₀` such that for every rational `K > K₀`
      `eigs (D F'_K (v*)) = eigs (D f (x*)) + Σ_K` with `Σ_K ⊂ {Re < 0}` (multisets of complex
      eigenvalues of the full Jacobians);
  * `hurwitz_simplex_iff`: for `K > K₀`, `D F'_K(v*)` restricted to the simplex is Hurwitz iff
      `D f(x*)` restricted to the simplex is, in the form "all eigenvalues other than the one
      conservation-law zero have negative real part" (`Multiset.erase` of one `0`);
  * `zero_mem_eigs_fieldFun`: the full PP Jacobian has the conservation eigenvalue `0`.

  The paper states the spectrum identity for the restrictions to the simplex tangent spaces
  `H` and `TΔ`; since both full Jacobians carry exactly one extra eigenvalue `0` (the left null vector
  `1ᵀ` of a conservative field), the identity on full Jacobians is equivalent and needs no basis
  of `H`. The constant `K₀` is the one of `normal_stability_projection` (`Σ|W D_F| / q₀` in the
  chosen basis of `S`); no claim is made about its size.
-/

import Ripple.LPP.NAPJacobian
import Ripple.LPP.NAPBlockForm

namespace Ripple
namespace NAPTransport

open Finset Matrix NAPStability

variable (n : ℕ)

/-- Adding the exchange reactions keeps a non-negative NAP realisation of the lift. -/
theorem exchange_keeps_realisation (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hw0 : ∀ sh, 0 ≤ w sh) (hnap : w.IsNAP) (hr : Realizes (veroneseLift n 3) w (demand n f))
    (K : ℚ) (hK : 0 ≤ K) :
    (∀ sh, 0 ≤ (w + K • wE n) sh) ∧ (w + K • wE n).IsNAP ∧
      Realizes (veroneseLift n 3) (w + K • wE n) (demand n f) :=
  ⟨add_wE_nonneg n w hw0 K hK, add_wE_isNAP n w hw0 hnap K hK,
    (realizes_add_wE n w (demand n f) K).mpr hr⟩

/-- The Jacobian of the lifted field with exchange rate `K` is `J_F − K M Λ⁻¹`. -/
theorem jac_add_wE (w : WProtocol (MI n 3)) (x : Fin n → ℝ) (hpos : ∀ k, 0 < x k) (K : ℚ) :
    jac (balanceFun n (w + K • wE n)) (ver n x)
      = jac (balanceFun n w) (ver n x) - (K : ℝ) • (exM n x * verInv n x) := by
  rw [jac_balanceFun_add_smul, jac_wE n x hpos, smul_neg, sub_eq_add_neg]

/-- **Theorem 4 (normal stability at an interior equilibrium).** Let `w` realise the cubed demand of
`f` and let `x*` be an equilibrium of `f` in the open simplex. Then there is `K₀` such that for every
rational `K > K₀` the eigenvalues (with multiplicity) of the Jacobian of the lifted field with
exchange rate `K` at `Ver x*` are those of `Df(x*)` together with a multiset of eigenvalues with
negative real part. -/
theorem normal_stability_interior (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f))
    (x : Fin n → ℝ) (hpos : ∀ k, 0 < x k) (hsum : ∑ k, x k = 1) (heq : fieldFun n f x = 0) :
    ∃ K0 : ℝ, ∀ K : ℚ, K0 < K →
      ∃ Sneg : Multiset ℂ,
        eigs (jac (balanceFun n (w + K • wE n)) (ver n x))
          = eigs (jac (fieldFun n f) x) + Sneg ∧ ∀ μ ∈ Sneg, μ.re < 0 := by
  obtain ⟨K0, hK0⟩ := normal_stability_projection
    (jac (balanceFun n w) (ver n x)) (jac (fieldFun n f) x) (Pm n x) (Rm n x)
    (Rm_mul_Pm n x hsum) (jac_balanceFun_mul_Pm n f w hr x heq)
    (ver n x) (ver_pos n x hpos)
    (fun q : ExIdx n => netR n q.1)
    (fun q : ExIdx n => (1 / 2 : ℝ) * mono6 n x (MI.add n 3 q.1.1 q.1.2.1))
    (fun q => by
      show 0 < (1 / 2 : ℝ) * mono6 n x (MI.add n 3 q.1.1 q.1.2.1)
      have := mono6_pos n x hpos (MI.add n 3 q.1.1 q.1.2.1)
      positivity)
    (exM n x) (verInv n x) rfl rfl
    (fun q => Rm_mulVec_netR n x q) (exM_mul_verInv_mul_Pm n x hpos)
    (fun y hy s hs => exchange_span_Rm n x hsum y hy s hs)
  refine ⟨K0, fun K hK => ?_⟩
  obtain ⟨Sneg, h1, h2⟩ := hK0 (K : ℝ) hK
  refine ⟨Sneg, ?_, h2⟩
  rw [jac_add_wE n w x hpos K]
  exact h1

/-- The conservation law gives the eigenvalue `0` of the full PP Jacobian. -/
theorem zero_mem_eigs_fieldFun (f : QuarticPP n) (x : Fin n → ℝ) (hn : Nonempty (Fin n)) :
    (0 : ℂ) ∈ eigs (jac (fieldFun n f) x) := by
  have hF := differentiableAt_fieldFun n f x
  have hS : (fun y => ∑ j, fieldFun n f y j) = fun _ => (0 : ℝ) :=
    funext fun y => fieldFun_sum_zero n f y
  have h1 : HasFDerivAt (fun y => ∑ j, fieldFun n f y j)
      (∑ j, (ContinuousLinearMap.proj j).comp (fderiv ℝ (fieldFun n f) x)) x :=
    HasFDerivAt.fun_sum fun j _ => hasFDerivAt_pi'.mp hF.hasFDerivAt j
  have h2 : HasFDerivAt (fun y => ∑ j, fieldFun n f y j) (0 : (Fin n → ℝ) →L[ℝ] ℝ) x := by
    rw [hS]
    exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x
  have h3 := h1.unique h2
  have hvec : (fun _ => (1 : ℝ)) ᵥ* jac (fieldFun n f) x = 0 := by
    funext i
    have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) h3
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply] at this
    simpa [Matrix.vecMul, dotProduct, jac] using this
  have hne : (fun _ => (1 : ℝ)) ≠ (0 : Fin n → ℝ) := by
    intro h
    obtain ⟨i⟩ := hn
    have := congrFun h i
    simp at this
  have hdet : (jac (fieldFun n f) x).det = 0 :=
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hvec⟩
  rw [mem_eigs_iff]
  simp only [map_zero, zero_sub, Matrix.det_neg]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero, mul_zero]

/-- **Hurwitz within the simplex.** For `K > K₀`, all eigenvalues of `D F'_K(v*)` other than the
conservation zero have negative real part iff the same holds for `D f(x*)`; i.e. `v*` is
exponentially stable for the exchange-augmented NAP within the simplex iff `x*` is for `f`. -/
theorem hurwitz_simplex_iff (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f))
    (x : Fin n → ℝ) (hpos : ∀ k, 0 < x k) (hsum : ∑ k, x k = 1) (heq : fieldFun n f x = 0) :
    ∃ K0 : ℝ, ∀ K : ℚ, K0 < K →
      ((∀ μ ∈ (eigs (jac (balanceFun n (w + K • wE n)) (ver n x))).erase 0, μ.re < 0) ↔
        (∀ μ ∈ (eigs (jac (fieldFun n f) x)).erase 0, μ.re < 0)) := by
  obtain ⟨K0, hK0⟩ := normal_stability_interior n f w hr x hpos hsum heq
  refine ⟨K0, fun K hK => ?_⟩
  obtain ⟨Sneg, h1, h2⟩ := hK0 K hK
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Finset.univ_eq_empty] at hsum
  have h0 := zero_mem_eigs_fieldFun n f x hn
  rw [h1, Multiset.erase_add_left_pos Sneg h0]
  constructor
  · intro h μ hμ
    exact h μ (Multiset.mem_add.mpr (Or.inl hμ))
  · intro h μ hμ
    rcases Multiset.mem_add.mp hμ with hμ | hμ
    · exact h μ hμ
    · exact h2 μ hμ

/-- Non-vacuity of the hypotheses: the zero protocol on one species, realised by the zero
weighted protocol, with the interior equilibrium `x* = 1`. -/
theorem interior_hypotheses_nonvacuous :
    ∃ (f : QuarticPP 1) (w : WProtocol (MI 1 3)) (x : Fin 1 → ℝ),
      Realizes (veroneseLift 1 3) w (demand 1 f) ∧ (∀ k, 0 < x k) ∧ ∑ k, x k = 1 ∧
        fieldFun 1 f x = 0 := by
  refine ⟨⟨fun _ _ => 0, fun _ => by simp, fun _ _ h => absurd h (lt_irrefl 0)⟩, 0, fun _ => 1,
    ?_, fun _ => one_pos, by simp, ?_⟩
  · intro δ α
    simp [coeffAt, demand]
  · funext j
    simp [fieldFun]

end NAPTransport
end Ripple
