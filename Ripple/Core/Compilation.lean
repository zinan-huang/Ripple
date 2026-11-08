/-
  Ripple.Core.Compilation — Bounded Surrogate Compilation ([BAC] §3, §4)

  [BAC] = Chen and Huang, *Bounded Analog Complexity* (DNA 32). Result numbers are those of the
  DNA 32 version, as in `docs/refactor/BC.md`. The journal draft renumbers them;
  `docs/papers/BAC-journal.md` keys each result by its LaTeX label: Prop 3.2 = `prop:dcr-limit`,
  Thm 3.3 = `thm:same-class`, Thm 3.4 = `thm:pole-computable`, Lemma 4.1 = `thm:time-length`,
  Lemma 4.3 = `lem:state-bound`, Thm 4.5 = `thm:compilation` (product-clock form
  `thm:compilation-product`), Thm 4.6 = `thm:poly-equiv`.

  Roots:
  - `bounded_compilation` ([BAC] Thm 3.3): a possibly unbounded ℚ-PIVP whose output converges
    to `α` yields a bounded certified computation of `α` (`IsCRNComputable α`);
    `isGPACComputable_iff_isCRNComputable` states it as an equality of classes.
  - `bounded_compilation_polyTime` ([BAC] Thm 4.6, from Thm 4.5): polynomial trajectory length
    and polynomial physical time give polynomial time in the bounded sense, with exponent
    `k (N + 1)`.
  - `PolyPIVP.arcLength_le_of_bounded` ([BAC] Lemma 4.1, in `Ripple.Core.ArcLength`).
  The construction (one joint time change `dt/dτ = 1/(1 + Σ yᵢ^N)` with the surrogates
  `y^a/(1 + Σ yᵢ^N)`, `|a| ≤ N`) is in `Ripple.Core.SurrogateCompilation`; the paper proofs, the
  repairs of the printed proofs and the route comparison are in `docs/refactor/BC.md`.

  The single-variable surrogates `U_{n,m} = f^m / (1 + f^n)` (`boundedSurrogate`) are kept for
  their users; with odd `n` or negative `f` they are not the surrogates of the compilation
  (BC.md §1.2, erratum E1).
-/

import Ripple.Core.BoundedTime
import Ripple.Core.SurrogateCompilation
import Ripple.LPP.SaturatingSurrogate

namespace Ripple

/-- Bounded surrogate variable: U_{n,m} = f^m / (1 + f^n).
  For f ≥ 0 and n ≥ 1, this is always in [0, 1]. -/
noncomputable def boundedSurrogate (n m : ℕ) (f : ℝ) : ℝ :=
  f ^ m / (1 + f ^ n)

/-- The bounded surrogate is always in [0, 1] for f ≥ 0, n ≥ 1. -/
theorem boundedSurrogate_mem_Icc {n : ℕ} (_hn : 1 ≤ n) {f : ℝ} (hf : 0 ≤ f)
    (m : ℕ) (hm : m ≤ n) :
    0 ≤ boundedSurrogate n m f ∧ boundedSurrogate n m f ≤ 1 := by
  constructor
  · unfold boundedSurrogate
    apply div_nonneg (pow_nonneg hf m)
    linarith [pow_nonneg hf n]
  · unfold boundedSurrogate
    apply div_le_one_of_le₀
    · -- f^m ≤ 1 + f^n
      by_cases hf1 : f ≤ 1
      · calc f ^ m ≤ 1 := pow_le_one₀ hf hf1
          _ ≤ 1 + f ^ n := le_add_of_nonneg_right (pow_nonneg hf n)
      · push Not at hf1
        calc f ^ m ≤ f ^ n := pow_le_pow_right₀ hf1.le hm
          _ ≤ 1 + f ^ n := le_add_of_nonneg_left (by norm_num)
    · linarith [pow_nonneg hf n]

theorem boundedSurrogate_nonneg {n : ℕ} (hn : 1 ≤ n) {f : ℝ} (hf : 0 ≤ f)
    {m : ℕ} (hm : m ≤ n) :
    0 ≤ boundedSurrogate n m f :=
  (boundedSurrogate_mem_Icc hn hf m hm).1

theorem boundedSurrogate_le_one {n : ℕ} (hn : 1 ≤ n) {f : ℝ} (hf : 0 ≤ f)
    {m : ℕ} (hm : m ≤ n) :
    boundedSurrogate n m f ≤ 1 :=
  (boundedSurrogate_mem_Icc hn hf m hm).2

/-- On the diagonal `m = n`, the bounded surrogate is exactly
`1 - 1 / (1 + f^n)`. This is the basic identity behind the limit
`U_{n,n}(f) → 1` as `f → +∞`. -/
theorem boundedSurrogate_diag_eq {n : ℕ} {f : ℝ} (hf : 0 ≤ f) :
    boundedSurrogate n n f = 1 - 1 / (1 + f ^ n) := by
  have hden : 1 + f ^ n ≠ 0 := by
    have hpow : 0 ≤ f ^ n := pow_nonneg hf n
    linarith
  unfold boundedSurrogate
  field_simp [hden]
  ring

/-- The diagonal surrogate error is exactly the reciprocal tail. -/
theorem boundedSurrogate_diag_error {n : ℕ} {f : ℝ} (hf : 0 ≤ f) :
    |1 - boundedSurrogate n n f| = 1 / (1 + f ^ n) := by
  have hpow : 0 ≤ f ^ n := pow_nonneg hf n
  have hfrac_nonneg : 0 ≤ 1 / (1 + f ^ n : ℝ) := by
    have hden : 0 < 1 + f ^ n := by linarith
    positivity
  rw [boundedSurrogate_diag_eq hf]
  have hrewrite : 1 - (1 - 1 / (1 + f ^ n : ℝ)) = 1 / (1 + f ^ n : ℝ) := by
    ring
  rw [hrewrite, abs_of_nonneg hfrac_nonneg]

theorem one_sub_boundedSurrogate_diag {n : ℕ} {f : ℝ} (hf : 0 ≤ f) :
    1 - boundedSurrogate n n f = 1 / (1 + f ^ n) := by
  rw [boundedSurrogate_diag_eq hf]
  have hrewrite : 1 - (1 - 1 / (1 + f ^ n : ℝ)) = 1 / (1 + f ^ n : ℝ) := by
    ring
  exact hrewrite

theorem boundedSurrogate_diag_lt_one {n : ℕ} {f : ℝ} (hf : 0 ≤ f) :
    boundedSurrogate n n f < 1 := by
  have hpow : 0 ≤ f ^ n := pow_nonneg hf n
  rw [boundedSurrogate_diag_eq hf]
  have hfrac_pos : 0 < 1 / (1 + f ^ n : ℝ) := by
    have hden : 0 < 1 + f ^ n := by linarith
    positivity
  linarith

open Topology Filter

theorem boundedSurrogate_one_zero_eq (x : ℝ) :
    boundedSurrogate 1 0 x = ((x + 1 : ℝ))⁻¹ := by
  simp [boundedSurrogate, div_eq_mul_inv, add_comm]

theorem boundedSurrogate_one_zero_tendsto_zero :
    Tendsto (fun x : ℝ => boundedSurrogate 1 0 x) atTop (𝓝 0) := by
  have htail : Tendsto (fun x : ℝ => ((x + 1 : ℝ))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_id.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  refine htail.congr' ?_
  filter_upwards with x
  exact (boundedSurrogate_one_zero_eq x).symm

theorem boundedSurrogate_one_one_tendsto_one :
    Tendsto (fun x : ℝ => boundedSurrogate 1 1 x) atTop (𝓝 1) := by
  have htail : Tendsto (fun x : ℝ => ((x + 1 : ℝ))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_id.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hone : Tendsto (fun x : ℝ => 1 - ((x + 1 : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub htail
  refine hone.congr' ?_
  filter_upwards [eventually_gt_atTop (-1 : ℝ)] with x hx
  have hx1 : (1 + x : ℝ) ≠ 0 := by linarith
  simp only [boundedSurrogate, pow_one]
  rw [show (x + 1 : ℝ)⁻¹ = (1 + x)⁻¹ from by rw [add_comm]]
  field_simp [hx1]
  ring

theorem boundedSurrogate_one_one_error_tendsto_zero :
    Tendsto (fun x : ℝ => |1 - boundedSurrogate 1 1 x|) atTop (𝓝 0) := by
  have htail : Tendsto (fun x : ℝ => ((x + 1 : ℝ))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_id.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  refine htail.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have h := boundedSurrogate_diag_error (n := 1) hx.le
  simp [pow_one, one_div, add_comm] at h
  exact h.symm

theorem hasDerivAt_boundedSurrogate_one_one {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun x : ℝ => boundedSurrogate 1 1 x)
      ((1 - boundedSurrogate 1 1 t) ^ 2) t := by
  have hne : (1 + t : ℝ) ≠ 0 := by
    linarith
  have hdiv :
      HasDerivAt (fun x : ℝ => boundedSurrogate 1 1 x) (1 / (1 + t) ^ 2) t := by
    convert (hasDerivAt_id t).div ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)) hne using 1
    · ext x
      simp [boundedSurrogate, pow_one, add_comm]
    · simp only [Pi.add_apply, id_eq]
      field_simp [hne]
      ring
  have hone :
      1 - boundedSurrogate 1 1 t = (1 + t : ℝ)⁻¹ := by
    simpa [pow_one, add_comm, div_eq_mul_inv] using (one_sub_boundedSurrogate_diag (n := 1) ht)
  convert hdiv using 1
  rw [hone, inv_pow, one_div]

/-- **Bounded-surrogate compilation (CBTC form).**

This is the substantive bounded-compilation statement currently available in
the repository. Given a concrete `CertifiedBoundedTimeComputable + PolyCRNDecomposition`
witness for `α ∈ [0, 1)`, compile it to a new bounded witness for the same `α`
whose output trajectory is pointwise `≤ M_out` for some `M_out < 1`.

This theorem genuinely consumes the input witness
via `Ripple.Saturating.saturating_surrogate_cbtc` and returns the strengthened
CBTC+PCD package used downstream by the LPP pipeline. -/
theorem bounded_compilation_cbtc {d : ℕ} {α : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (hα_nn : 0 ≤ α) (hα_lt : α < 1) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' α)
      (_ : PolyCRNDecomposition d' cbtc'.pivp) (M_out : ℝ),
      α ≤ M_out ∧ M_out < 1 ∧
      (∀ σ, 0 ≤ σ → cbtc'.sol.trajectory σ cbtc'.pivp.output ≤ M_out) :=
  Saturating.saturating_surrogate_cbtc cbtc pcd hα_nn hα_lt

/-- [BAC] §2.3 (Bournez–Graça–Pouly convergence semantics): `α` is computed by a possibly
unbounded GPAC, i.e. by a ℚ-polynomial initial value problem (`PolyPIVP`) with a solution on
`[0, ∞)` whose output tends to `α`. No boundedness and no modulus. -/
def IsGPACComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ P : PolyPIVP d, ∃ sol : PIVP.Solution P.toPIVP, P.toPIVP.Computes sol α

/-- [BAC] Thm 3.3 (bounded GPACs compute the same real numbers): a ℚ-PIVP with a solution on
`[0, ∞)` whose output converges to `α` yields a bounded ℚ-PIVP computing `α` with a time
modulus ([BAC] Def 2.1 + 2.3). The compiled system is `P.jointSurrogateCompile N` with
`N = 2 · max deg` (`bounded_compilation_certified`; Construction 3.1 and Prop 3.2 with one
joint time change, BC.md §1.4). -/
theorem bounded_compilation {d : ℕ} {α : ℝ} (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (hlim : Filter.Tendsto (fun t => sol.trajectory t P.output) Filter.atTop (nhds α)) :
    IsCRNComputable α := by
  have hdeg : ∀ i, (P.field i).totalDegree ≤ 2 * Finset.univ.sup fun j => (P.field j).totalDegree :=
    fun i => (Finset.le_sup (f := fun j => (P.field j).totalDegree) (Finset.mem_univ i)).trans
      (Nat.le_mul_of_pos_left _ two_pos)
  obtain ⟨btc, -⟩ := bounded_compilation_certified P (even_two_mul _) hdeg sol hlim
  exact ⟨_, ⟨btc⟩⟩

/-- [BAC] Thm 3.3 as an equality of classes: unboundedness does not enlarge the class of
GPAC-computable reals. -/
theorem isGPACComputable_iff_isCRNComputable (α : ℝ) :
    IsGPACComputable α ↔ IsCRNComputable α := by
  constructor
  · rintro ⟨d, P, sol, h⟩
    exact bounded_compilation P sol h
  · rintro ⟨d, ⟨btc⟩⟩
    exact ⟨d, btc.pivp, btc.sol, btc.to_tendsto⟩

/-- [BAC] Thm 4.6 (from BGP poly length to bounded poly time), via Thm 4.5 in its joint form
(`bounded_compilation_polyTime_certified`, BC.md §1.6): if the output is `e^{-r}`-close after
`μ r`, with `μ r` and the trajectory length `L(μ r)` at most `C (r+1)^k`, then `α` is computed
by a bounded ℚ-PIVP with time modulus `O((r+1)^{k(N+1)})`, for any even `N` at least the degree
of the field. -/
theorem bounded_compilation_polyTime {d : ℕ} {α : ℝ} (P : PolyPIVP d)
    (sol : PIVP.Solution P.toPIVP) (μ : TimeModulus) (k : ℕ) (C : ℝ)
    (hconv : ∀ r : ℕ, ∀ t : ℝ, t > μ r →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ)))
    (hμ : ∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ C * ((r : ℝ) + 1) ^ k)
    (hL : ∀ r : ℕ, P.arcLength sol.trajectory (μ r) ≤ C * ((r : ℝ) + 1) ^ k)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    IsPolyTimeComputable α (k * (N + 1)) := by
  obtain ⟨btc, -, ⟨C', hC', hmod⟩, -⟩ :=
    bounded_compilation_polyTime_certified P sol μ k C hconv hμ hL hN hdeg
  exact ⟨_, btc, C', hC', hmod⟩

end Ripple
