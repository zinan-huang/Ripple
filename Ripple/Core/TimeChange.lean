/-
  Ripple.Core.TimeChange — the inverse time change of bounded surrogate compilation

  [BAC] Construction 3.1, Step 1, and Prop 3.2 (`T* = ∞`), in the form of `docs/refactor/BC.md`
  §1.4.3: for a continuous speed `ρ ≥ 1`, the clock `θ(t) = ∫₀ᵗ ρ` is an order isomorphism of `ℝ`
  (`θ(t) ≥ t` for `t ≥ 0`, `θ(t) ≤ t` for `t ≤ 0`), and its inverse `s` satisfies
  `s' = 1/ρ(s)`, `s(0) = 0`, `s → ∞`. This repairs the printed proof of Prop 3.2, whose
  "`s(τ) ≤ τ → ∞`" gives only an upper bound (BC.md §1.3.2, erratum E2).

  The proof generalises `Ripple.BoundedUniversality.GPAC.timeChange_via_inverse`
  (`BoundedUniversality/GPAC/ExplicitCompile.lean`), which treats `ρ = 1 + z^N`.

  Numbering of [BAC]: the DNA 32 version, as in `docs/refactor/BC.md` (journal-draft labels in
  `docs/papers/BAC-journal.md` and in the header of `Ripple.Core.SurrogateCompilation`).
-/

import Ripple.Core.PIVP
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inverse

namespace Ripple

open MeasureTheory

/-- The clock `θ(t) = ∫₀ᵗ ρ(u) du` of a time change with speed `dτ/dt = ρ`. -/
noncomputable def clockIntegral (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, ρ u

theorem clockIntegral_zero (ρ : ℝ → ℝ) : clockIntegral ρ 0 = 0 := by
  simp [clockIntegral]

theorem clockIntegral_hasDerivAt {ρ : ℝ → ℝ} (hρ : Continuous ρ) (t : ℝ) :
    HasDerivAt (clockIntegral ρ) (ρ t) t :=
  (hρ.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem clockIntegral_strictMono {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hpos : ∀ u, 0 < ρ u) :
    StrictMono (clockIntegral ρ) := by
  intro a b hab
  have hsplit : clockIntegral ρ b = clockIntegral ρ a + ∫ u in a..b, ρ u := by
    unfold clockIntegral
    have hii1 : IntervalIntegrable ρ volume 0 a := hρ.intervalIntegrable 0 a
    have hii2 : IntervalIntegrable ρ volume a b := hρ.intervalIntegrable a b
    simpa [add_comm, add_left_comm, add_assoc] using
      (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
  have hp : 0 < ∫ u in a..b, ρ u :=
    intervalIntegral.intervalIntegral_pos_of_pos (hρ.intervalIntegrable a b) hpos hab
  linarith

/-- `θ(t) ≥ t` for `t ≥ 0` when `ρ ≥ 1`. -/
theorem le_clockIntegral {ρ : ℝ → ℝ} (hρ : Continuous ρ) (h1 : ∀ u, 1 ≤ ρ u) {t : ℝ}
    (ht : 0 ≤ t) : t ≤ clockIntegral ρ t := by
  have hle : (∫ _u in (0 : ℝ)..t, (1 : ℝ)) ≤ ∫ u in (0 : ℝ)..t, ρ u :=
    intervalIntegral.integral_mono_on ht
      ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable 0 t)
      (hρ.intervalIntegrable 0 t) (fun u _ => h1 u)
  simpa [clockIntegral] using hle

/-- `θ(t) ≤ t` for `t ≤ 0` when `ρ ≥ 1`. -/
theorem clockIntegral_le_of_nonpos {ρ : ℝ → ℝ} (hρ : Continuous ρ) (h1 : ∀ u, 1 ≤ ρ u)
    {t : ℝ} (ht : t ≤ 0) : clockIntegral ρ t ≤ t := by
  have hmono : (∫ _u in t..0, (1 : ℝ)) ≤ ∫ u in t..0, ρ u :=
    intervalIntegral.integral_mono_on ht
      ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable t 0)
      (hρ.intervalIntegrable t 0) (fun u _ => h1 u)
  have hsymm : clockIntegral ρ t = - ∫ u in t..0, ρ u := by
    unfold clockIntegral
    rw [intervalIntegral.integral_symm]
  have hone : (∫ _u in t..0, (1 : ℝ)) = -t := by simp
  linarith

/-- [BAC] Construction 3.1 Step 1 and Prop 3.2 (`T* = ∞`), BC.md §1.4.3: for a continuous
`ρ ≥ 1` there is a time change `s = θ⁻¹`, `θ(t) = ∫₀ᵗ ρ`, with `s(0) = 0`,
`s'(τ) = 1/ρ(s(τ))` at every `τ`, `s` continuous, strictly increasing and tending to `∞`. -/
theorem exists_inverse_timeChange {ρ : ℝ → ℝ} (hρ : Continuous ρ) (h1 : ∀ u, 1 ≤ ρ u) :
    ∃ s : ℝ → ℝ, s 0 = 0 ∧ (∀ τ, HasDerivAt s (ρ (s τ))⁻¹ τ) ∧ Continuous s ∧
      StrictMono s ∧ Filter.Tendsto s Filter.atTop Filter.atTop ∧
      (∀ t, s (clockIntegral ρ t) = t) ∧ (∀ τ, clockIntegral ρ (s τ) = τ) := by
  classical
  set L : ℝ → ℝ := clockIntegral ρ with hL_def
  have hpos : ∀ u, 0 < ρ u := fun u => lt_of_lt_of_le zero_lt_one (h1 u)
  have hL0 : L 0 = 0 := clockIntegral_zero ρ
  have hLderiv : ∀ x : ℝ, HasDerivAt L (ρ x) x := clockIntegral_hasDerivAt hρ
  have hLmono : StrictMono L := clockIntegral_strictMono hρ hpos
  have hLcont : Continuous L := continuous_iff_continuousAt.mpr fun x => (hLderiv x).continuousAt
  have hsurj : Function.Surjective L := by
    intro y
    by_cases hy : 0 ≤ y
    · have hLy : y ≤ L y := le_clockIntegral hρ h1 hy
      obtain ⟨x, _, hx⟩ := intermediate_value_Icc hy hLcont.continuousOn
        ⟨by rw [hL0]; exact hy, hLy⟩
      exact ⟨x, hx⟩
    · have hylt : y < 0 := lt_of_not_ge hy
      have hLy : L y ≤ y := clockIntegral_le_of_nonpos hρ h1 hylt.le
      obtain ⟨x, _, hx⟩ := intermediate_value_Icc hylt.le hLcont.continuousOn
        ⟨hLy, by rw [hL0]; exact hylt.le⟩
      exact ⟨x, hx⟩
  let s : ℝ → ℝ := Function.invFun L
  have hs_inv : ∀ y : ℝ, L (s y) = y := fun y => Function.invFun_eq (hsurj y)
  have hs_left : ∀ t : ℝ, s (L t) = t := fun t => hLmono.injective (hs_inv (L t))
  have hs0 : s 0 = 0 := by
    apply hLmono.injective; rw [hs_inv 0, hL0]
  have hs_strict : StrictMono s := by
    intro a b hab
    by_contra h
    push Not at h
    have := hLmono.monotone h
    rw [hs_inv a, hs_inv b] at this
    linarith
  have hs_cont : Continuous s := by
    let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective L hLmono hsurj
    have hs_eq_e : s = e.symm := by
      funext y
      apply hLmono.injective
      rw [hs_inv y]
      exact (e.apply_symm_apply y).symm
    rw [hs_eq_e]; exact e.symm.continuous
  have hs_tendsto : Filter.Tendsto s Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (L b)] with y hy
    by_contra hnot
    exact not_lt_of_ge (show L b ≤ L (s y) by rw [hs_inv y]; exact hy)
      (hLmono (lt_of_not_ge hnot))
  refine ⟨s, hs0, ?_, hs_cont, hs_strict, hs_tendsto, hs_left, hs_inv⟩
  intro τ
  exact HasDerivAt.of_local_left_inverse hs_cont.continuousAt (hLderiv (s τ))
    (ne_of_gt (hpos (s τ))) (Filter.Eventually.of_forall hs_inv)

end Ripple
