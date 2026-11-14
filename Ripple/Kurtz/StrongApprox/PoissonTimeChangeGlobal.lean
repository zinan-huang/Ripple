-- Ripple/Kurtz/StrongApprox/PoissonTimeChangeGlobal.lean
import Ripple.Kurtz.StrongApprox.PoissonTimeChangeCanonical
import Mathlib.MeasureTheory.Function.Floor

/-!
# Global Poisson time-change solution

At time `t` use the finite-horizon path with integer horizon
`⌊max t 0⌋₊ + 1`.  Finite-horizon uniqueness makes these pieces agree on
overlaps.  A countable-section measurability lemma proves measurability of the
glued physical-time path without any sample-variable measurability claim.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {N : ℕ → Ω → ℕ}
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strictly larger integer horizon for every nonnegative real time. -/
noncomputable def globalHorizonIndex (t : ℝ) : ℕ :=
  ⌊max t 0⌋₊ + 1

theorem globalHorizonIndex_pos (t : ℝ) :
    0 < globalHorizonIndex t := by
  simp [globalHorizonIndex]

theorem lt_globalHorizonIndex_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    t < (globalHorizonIndex t : ℕ) := by
  unfold globalHorizonIndex
  rw [max_eq_left ht]
  push_cast
  exact Nat.lt_floor_add_one t

theorem globalHorizonIndex_mono :
    Monotone globalHorizonIndex := by
  intro s t hst
  unfold globalHorizonIndex
  exact Nat.add_le_add_right
    (Nat.floor_mono (max_le_max hst le_rfl)) 1

/-- Measurable diagonal selection from countably many measurable sections. -/
theorem measurable_nat_diagonal
    {E : Type*} [MeasurableSpace E]
    (f : ℕ → ℝ → E) (hf : ∀ m, Measurable (f m))
    (g : ℝ → ℕ) (hg : Measurable g) :
    Measurable fun t => f (g t) t := by
  intro A hA
  have hpre :
      (fun t => f (g t) t) ⁻¹' A =
        ⋃ m : ℕ, (g ⁻¹' ({m} : Set ℕ)) ∩ (f m ⁻¹' A) := by
    ext t
    simp
  rw [hpre]
  exact MeasurableSet.iUnion fun m =>
    (hg (measurableSet_singleton m)).inter (hf m hA)

/-- The canonical path chosen on the integer horizon `m`. -/
noncomputable def integerPoissonPath
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    (m : ℕ) : ℝ → Fin d → ℝ :=
  poissonHorizonPath (N := N) (v := v)
    hn hβ0 hβb hβm (Nat.cast_nonneg m) x₀ ω

private theorem integerPoissonPath_measurable
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    (m : ℕ) :
    Measurable (integerPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω m) :=
  poissonHorizonPath_measurable (N := N) (v := v)
    hn hβ0 hβb hβm (Nat.cast_nonneg m) x₀ ω

private theorem integerPoissonPath_initial
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    (m : ℕ) :
    integerPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω m 0 = x₀ :=
  poissonHorizonPath_initial (N := N) (v := v)
    hn hβ0 hβb hβm (Nat.cast_nonneg m) x₀ ω

/-- Integer-horizon paths agree on overlaps. -/
theorem integerPoissonPath_consistent
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    {m k : ℕ} (hmk : m ≤ k) :
    Set.EqOn
      (integerPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω m)
      (integerPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω k)
      (Icc (0 : ℝ) (m : ℝ)) := by
  simpa [integerPoissonPath] using
    poissonHorizonPath_consistent (N := N) (v := v)
      hn hβ0 hβb hβm
      (Nat.cast_nonneg m) (by exact_mod_cast hmk) x₀ ω

/-- The consistent gluing of all integer-horizon paths. -/
noncomputable def globalPoissonPath
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    (t : ℝ) : Fin d → ℝ :=
  integerPoissonPath (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω (globalHorizonIndex t) t

/-- On any smaller time, the global path agrees with every sufficiently large
integer-horizon path. -/
theorem globalPoissonPath_eq_integer_of_lt
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (htm : t < m) :
    globalPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω t =
    integerPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω m t := by
  have hindex : globalHorizonIndex t ≤ m := by
    unfold globalHorizonIndex
    rw [max_eq_left ht]
    exact Nat.succ_le_iff.mpr ((Nat.floor_lt ht).2 htm)
  exact integerPoissonPath_consistent (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω hindex
    ⟨ht, (lt_globalHorizonIndex_of_nonneg ht).le⟩

private theorem measurable_globalHorizonIndex :
    Measurable globalHorizonIndex := by
  unfold globalHorizonIndex
  exact (measurable_of_countable (fun m : ℕ => m + 1)).comp
    (Nat.measurable_floor.comp (measurable_id.max measurable_const))

/-- Physical-time measurability of the global gluing. -/
theorem globalPoissonPath_measurable
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) :
    Measurable (globalPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω) := by
  exact measurable_nat_diagonal
    (fun m t => integerPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω m t)
    (fun m => integerPoissonPath_measurable (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω m)
    globalHorizonIndex measurable_globalHorizonIndex

@[simp]
theorem globalPoissonPath_initial
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω) :
    globalPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω 0 = x₀ := by
  unfold globalPoissonPath
  exact integerPoissonPath_initial (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω (globalHorizonIndex 0)

/-- Equality with one fixed integer path on a compact initial interval. -/
private theorem globalPoissonPath_eq_integer_on_Icc
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    {T : ℝ} (hT : 0 ≤ T) :
    Set.EqOn
      (globalPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω)
      (integerPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω (globalHorizonIndex T))
      (Icc (0 : ℝ) T) := by
  intro t ht
  exact globalPoissonPath_eq_integer_of_lt (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω ht.1
    (ht.2.trans_lt (lt_globalHorizonIndex_of_nonneg hT))

/-- The global path solves the Poisson random-time-change equation at every
nonnegative physical time. -/
theorem globalPoissonPath_equation
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    {t : ℝ} (ht : 0 ≤ t) :
    let X := globalPoissonPath (N := N) (v := v)
      hn hβ0 hβb hβm x₀ ω
    X t = X 0 +
      ∑ l, ((poisFamily ι N l
        ((n : ℝ) * clock β X l t) ω : ℝ) /
          (n : ℝ)) • v l := by
  let m := globalHorizonIndex t
  let H := integerPoissonPath (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω m
  let X := globalPoissonPath (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω
  have htm : t < (m : ℕ) := by
    exact lt_globalHorizonIndex_of_nonneg ht
  have hEq : Set.EqOn X H (Icc (0 : ℝ) t) := by
    simpa [m, H, X] using
      globalPoissonPath_eq_integer_on_Icc (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω ht
  have hclock : ∀ l, clock β X l t = clock β H l t := by
    intro l
    unfold clock
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    exact congrArg (β l) (hEq hs)
  have hHeq := poissonHorizonPath_equation (N := N) (v := v)
    hn hβ0 hβb hβm (Nat.cast_nonneg m) x₀ ω
      t ⟨ht, htm.le⟩
  calc
    X t = H t := hEq ⟨ht, le_rfl⟩
    _ = x₀ +
        ∑ l, ((poisFamily ι N l
          ((n : ℝ) * clock β H l t) ω : ℝ) /
            (n : ℝ)) • v l := by
          simpa [H, integerPoissonPath] using hHeq
    _ = X 0 +
        ∑ l, ((poisFamily ι N l
          ((n : ℝ) * clock β X l t) ω : ℝ) /
            (n : ℝ)) • v l := by
          have h0 : X 0 = x₀ := globalPoissonPath_initial (N := N) (v := v)
            hn hβ0 hβb hβm x₀ ω
          rw [h0]
          congr 1
          exact Finset.sum_congr rfl fun l _ => by rw [hclock l]

/-- Right-local constancy of the global path on nonnegative time. -/
theorem globalPoissonPath_eventually_right
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ s in 𝓝[≥] t,
      globalPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω s =
      globalPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω t := by
  let m : ℕ := globalHorizonIndex t + 1
  have htm : t < (m : ℕ) := by
    have hbase := lt_globalHorizonIndex_of_nonneg ht
    exact hbase.trans_le (by exact_mod_cast Nat.le_succ (globalHorizonIndex t))
  have hAt := globalPoissonPath_eq_integer_of_lt (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω ht htm
  have hright := poissonHorizonPath_eventually_right (N := N) (v := v)
    hn hβ0 hβb hβm (Nat.cast_nonneg m) x₀ ω t
  have hbelow : ∀ᶠ s : ℝ in 𝓝[≥] t, s < (m : ℝ) :=
    (eventually_lt_nhds htm).filter_mono nhdsWithin_le_nhds
  filter_upwards [hright, hbelow, self_mem_nhdsWithin]
    with s hHs hsm hts
  have hs0 : 0 ≤ s := ht.trans hts
  calc
    globalPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω s =
        integerPoissonPath (N := N) (v := v)
          hn hβ0 hβb hβm x₀ ω m s :=
      globalPoissonPath_eq_integer_of_lt (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω hs0 hsm
    _ = integerPoissonPath (N := N) (v := v)
          hn hβ0 hβb hβm x₀ ω m t := hHs
    _ = globalPoissonPath (N := N) (v := v)
          hn hβ0 hβb hβm x₀ ω t := hAt.symm

/-- Every compact nonnegative time interval has a finite jump support. -/
theorem globalPoissonPath_locallyFinite
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → PathSpace Ω)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ S : Finset ℝ, ∀ ⦃s t : ℝ⦄,
      0 ≤ s → s ≤ t → t ≤ T →
      Disjoint (Ioc s t : Set ℝ) (S : Set ℝ) →
      globalPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω s =
      globalPoissonPath (N := N) (v := v)
        hn hβ0 hβb hβm x₀ ω t := by
  let m := globalHorizonIndex T
  obtain ⟨S, hS⟩ := poissonHorizonPath_finiteJumpSupport (N := N) (v := v)
    hn hβ0 hβb hβm (Nat.cast_nonneg m) x₀ ω
  refine ⟨S, ?_⟩
  intro s t hs0 hst htT hdisj
  have hsEq := globalPoissonPath_eq_integer_of_lt (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω hs0
    ((hst.trans htT).trans_lt
      (lt_globalHorizonIndex_of_nonneg hT))
  have htEq := globalPoissonPath_eq_integer_of_lt (N := N) (v := v)
    hn hβ0 hβb hβm x₀ ω (hs0.trans hst)
    (htT.trans_lt (lt_globalHorizonIndex_of_nonneg hT))
  exact hsEq.trans ((hS hst hdisj).trans htEq.symm)

end Ripple.Kurtz.StrongApprox

end
