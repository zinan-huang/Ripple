import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledZ

/-!
Ripple.BoundedUniversality.BGP.DirectTrackingInduction
-----------------------------------

Depth-weighted cycle induction for the write-start tracking error.

**Why depth-weighted.**  The previous version of this file ran the cycle
induction in the *unweighted* error `R(j) = max_i |u(mark j) i - enc(cfg j) i|`
through an affine recurrence `R(j+1) ≤ α(j)·R(j) + β(j)` and asked for `α`
eventually `< 1`.  That contraction is unattainable: the one-cycle step passes
through the branch diagonal, whose Lipschitz constant in the stack coordinates
is `coordMultiplier = B_U = 6` (a push multiplies the stack encoding error by
`B`).  So `α(j) ≥ 6` on stack coordinates and
`CoupledEndpointDecay.tendsto_zero_of_recurrence` never applies — the
unweighted recurrence is *expanding*, not contracting.

**The fix.**  Work in the depth-weighted space
`W(j,i) = k^dep(j,i) · E(j,i)` (with `k = B_U` and `dep` the coarse stack
depth, `dep(j+1) = dep(j) - delta(j)`).  The per-cycle comparison
`E(j+1,i) ≤ k^delta(j,i)·E(j,i) + ηc(j,i)`  (the `MURecur_repl` shape, which
is *algebraic* for the positive-part excess `ηc = max(0, next - k^delta·prev)`)
becomes pure accumulation in the weighted space:

  `W(j+1,i) ≤ W(j,i) + k^dep(j+1,i)·ηc(j,i)`.

There is no contraction factor left to fight: the depth weight absorbs the
`B^delta` expansion exactly (`k^dep(j+1)·k^delta = k^dep(j)`).  For the halt
coordinate `delta = 0` and the weighting is trivial; for stack coordinates the
weighting converts the `×6` expansion into bookkeeping.

**Closing the budget.**  The weighted error is then dominated by the recursive
majorant `weightedMajorant W0 g η` with `W(0) ≤ W0`,
`W(j+1) = W(j) + g(j)·η(j)`, where `g(j)` dominates the depth weight
`k^dep(j+1,i)` uniformly in `i` and `η(j)` dominates the excess `ηc(j,i)`
uniformly in `i`.  With

* depth growing at most linearly, `dep(j+1,i) ≤ L + j`, so
  `k^dep(j+1,i) ≤ e^{L·log k}·e^{j·log k}`, and
* the excess geometric at rate `lam > log k`  (supplied downstream by the
  settled write endpoint: the `exp(-Λ)` write-settle contraction kills the
  carried tube, concentration `epsLamSettled → 0` kills the mixture radius;
  cf. `paper3F1Eta_geometric_of_writeStart_succ_endpoint_errors` and
  `GeometricDecayRecurrence.geometric_bound_of_contracting_recurrence`),

the accumulated weighted budget is a convergent geometric series, so
`weightedMajorant` is uniformly bounded by the closed cap
`W0 + Cg·Cη/(1 - e^{log k - lam})`.  Since `dep ≥ 0` and `k > 1` give
`k^dep ≥ 1`, the *unweighted* tracking error is bounded by the same cap:

  `E(j,i) ≤ W(j,i) ≤ weightedMajorant(j) ≤ cap`.

**`hmix_settled` without circularity.**  The settled-window mixture estimate
(`mixTarget_near_next_on_settled_window`) is instantiated with the u-tube
radius `ρu := weightedMajorant W0 g η`, whose defining property is exactly the
simultaneous weighted domination proved here — no reference to the coarse
u-tube budget.  The resulting radius
`Rspread·epsLam(j) + mult·(weightedMajorant(j) + δu(j))` is uniformly bounded
by `weightedMixRadius_le_cap`, which is the input shape
`z_write_settled_endpoint` needs.

Everything here is elementary real analysis / bookkeeping; the per-cycle
estimates enter as hypotheses in the exact shapes produced by the existing
settled-window lemmas (`MURecur_repl` step, `paper3F1Eta`-style excess,
`paper3F1Depth`-style linear depth), so the wiring in `HeadlineUnconditional`
can discharge them without circularity.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open scoped BigOperators

/-! ## The depth-weighted majorant

`weightedMajorant W0 g η` is the recursive prefix-sum budget
`W(0) = W0`, `W(j+1) = W(j) + g(j)·η(j)`: the depth-weighted tracking error is
dominated by it (see `le_weightedMajorant_of_weighted_step`), and the sequence
itself is capped by a convergent geometric series when the weighted defects
`g·η` decay geometrically (`weightedMajorant_le_geomCap`). -/

/-- Recursive depth-weighted majorant: `W(0) = W0` and
`W(j+1) = W(j) + g(j)·η(j)`, where `g(j)` dominates the depth weight
`k^dep(j+1,·)` and `η(j)` dominates the per-cycle excess. -/
def weightedMajorant (W0 : ℝ) (g η : ℕ → ℝ) : ℕ → ℝ
  | 0 => W0
  | j + 1 => weightedMajorant W0 g η j + g j * η j

theorem weightedMajorant_zero (W0 : ℝ) (g η : ℕ → ℝ) :
    weightedMajorant W0 g η 0 = W0 := rfl

theorem weightedMajorant_succ (W0 : ℝ) (g η : ℕ → ℝ) (j : ℕ) :
    weightedMajorant W0 g η (j + 1) =
      weightedMajorant W0 g η j + g j * η j := rfl

/-- Closed form: the majorant is the prefix sum of the weighted defects. -/
theorem weightedMajorant_eq_prefixSum (W0 : ℝ) (g η : ℕ → ℝ) :
    ∀ j, weightedMajorant W0 g η j =
      W0 + ∑ l ∈ Finset.range j, g l * η l := by
  intro j
  induction j with
  | zero =>
      rw [weightedMajorant_zero]
      simp
  | succ j ih =>
      rw [weightedMajorant_succ, ih, Finset.sum_range_succ]
      ring

theorem weightedMajorant_nonneg {W0 : ℝ} {g η : ℕ → ℝ}
    (hW0 : 0 ≤ W0) (hg : ∀ j, 0 ≤ g j) (hη : ∀ j, 0 ≤ η j) :
    ∀ j, 0 ≤ weightedMajorant W0 g η j := by
  intro j
  induction j with
  | zero =>
      rw [weightedMajorant_zero]
      exact hW0
  | succ j ih =>
      rw [weightedMajorant_succ]
      exact add_nonneg ih (mul_nonneg (hg j) (hη j))

/-- The majorant is nondecreasing (nonnegative defects): the weighted picture
has no decay to offer, only a budget to keep finite. -/
theorem weightedMajorant_le_succ {W0 : ℝ} {g η : ℕ → ℝ}
    (hg : ∀ j, 0 ≤ g j) (hη : ∀ j, 0 ≤ η j) (j : ℕ) :
    weightedMajorant W0 g η j ≤ weightedMajorant W0 g η (j + 1) := by
  rw [weightedMajorant_succ]
  linarith [mul_nonneg (hg j) (hη j)]

/-- **The geometric cap.**  If the depth-weight dominator grows at most like
`Cg·e^{β·j}` and the excess dominator decays like `Cη·e^{-lam·j}` with
`β < lam`, the weighted budget converges: every `weightedMajorant` value is
below the closed cap `W0 + Cg·Cη/(1 - e^{β-lam})`.  This is the point where
"excess decays faster than the depth weight grows" pays off. -/
theorem weightedMajorant_le_geomCap {W0 : ℝ} {g η : ℕ → ℝ}
    {Cg Cη β lam : ℝ}
    (hCg : 0 ≤ Cg) (hCη : 0 ≤ Cη) (hβlam : β < lam)
    (hη_nonneg : ∀ j, 0 ≤ η j)
    (hg_le : ∀ j, g j ≤ Cg * Real.exp (β * (j : ℝ)))
    (hη_le : ∀ j, η j ≤ Cη * Real.exp (-lam * (j : ℝ))) :
    ∀ j, weightedMajorant W0 g η j ≤
      W0 + Cg * Cη * (1 / (1 - Real.exp (β - lam))) := by
  intro j
  have hq_nonneg : (0 : ℝ) ≤ Real.exp (β - lam) := (Real.exp_pos _).le
  have hq_lt_one : Real.exp (β - lam) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hterm : ∀ l : ℕ, g l * η l ≤ (Cg * Cη) * Real.exp (β - lam) ^ l := by
    intro l
    have hgexp_nonneg : 0 ≤ Cg * Real.exp (β * (l : ℝ)) :=
      mul_nonneg hCg (Real.exp_pos _).le
    calc g l * η l
        ≤ (Cg * Real.exp (β * (l : ℝ))) * (Cη * Real.exp (-lam * (l : ℝ))) :=
          mul_le_mul (hg_le l) (hη_le l) (hη_nonneg l) hgexp_nonneg
      _ = (Cg * Cη) *
            (Real.exp (β * (l : ℝ)) * Real.exp (-lam * (l : ℝ))) := by ring
      _ = (Cg * Cη) * Real.exp (β * (l : ℝ) + -lam * (l : ℝ)) := by
            rw [Real.exp_add]
      _ = (Cg * Cη) * Real.exp ((l : ℝ) * (β - lam)) := by
            congr 1
            ring
      _ = (Cg * Cη) * Real.exp (β - lam) ^ l := by
            rw [Real.exp_nat_mul]
  have hsum_le : ∑ l ∈ Finset.range j, g l * η l ≤
      ∑ l ∈ Finset.range j, (Cg * Cη) * Real.exp (β - lam) ^ l :=
    Finset.sum_le_sum (fun l _ => hterm l)
  have hgeom : ∑ l ∈ Finset.range j, (Cg * Cη) * Real.exp (β - lam) ^ l ≤
      (Cg * Cη) * (1 / (1 - Real.exp (β - lam))) := by
    have hsum_eq : ∑ l ∈ Finset.range j, (Cg * Cη) * Real.exp (β - lam) ^ l =
        (Cg * Cη) * ∑ l ∈ Finset.range j, Real.exp (β - lam) ^ l := by
      rw [Finset.mul_sum]
    rw [hsum_eq]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCg hCη)
    have hgeom' := geom_sum_Ico_le_of_lt_one (m := 0) (n := j)
      hq_nonneg hq_lt_one
    rw [Finset.range_eq_Ico]
    simpa only [pow_zero, one_div] using hgeom'
  calc weightedMajorant W0 g η j
      = W0 + ∑ l ∈ Finset.range j, g l * η l :=
        weightedMajorant_eq_prefixSum W0 g η j
    _ ≤ W0 + Cg * Cη * (1 / (1 - Real.exp (β - lam))) := by
        linarith [hsum_le.trans hgeom]

/-! ## Generic simultaneous domination in the weighted space

The cycle induction in abstract form: a coordinate-indexed error family whose
weighted cycle-0 slice is `≤ W0` and whose one-cycle step has the
`MURecur`-shape `E(j+1) ≤ k^delta·E(j) + ηc(j)` is, in the weighted space
`k^dep·E`, dominated by the recursive majorant, simultaneously in the
coordinate.  The depth bookkeeping `dep(j+1) = dep(j) - delta(j)` makes the
`k^delta` expansion cancel exactly. -/

/-- **Simultaneous weighted cycle induction.**  The weighted error
`k^dep(j,i)·E(j,i)` never exceeds the recursive budget: the step
`W(j+1,i) ≤ W(j,i) + k^dep(j+1,i)·ηc(j,i)` is the depth-weighted image of the
`MURecur` recurrence, and the increment is dominated by `g(j)·η(j)` uniformly
in the coordinate. -/
theorem le_weightedMajorant_of_weighted_step {ι : Sort*} (E : ℕ → ι → ℝ)
    {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → ι → ℤ) (ηc : ℕ → ι → ℝ) {W0 : ℝ} {g η : ℕ → ℝ}
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hstep : ∀ j i, E (j + 1) i ≤ k ^ delta j i * E j i + ηc j i)
    (hbase : ∀ i, k ^ dep 0 i * E 0 i ≤ W0)
    (hg_dom : ∀ j i, k ^ dep (j + 1) i ≤ g j)
    (hηc_nonneg : ∀ j i, 0 ≤ ηc j i)
    (hη_dom : ∀ j i, ηc j i ≤ η j) :
    ∀ j i, k ^ dep j i * E j i ≤ weightedMajorant W0 g η j := by
  intro j i
  induction j with
  | zero =>
      rw [weightedMajorant_zero]
      exact hbase i
  | succ j ih =>
      have hk0 : (0 : ℝ) ≤ k := (zero_lt_one.trans hk).le
      have hk_ne : k ≠ 0 := (zero_lt_one.trans hk).ne'
      have hpow_nonneg : 0 ≤ k ^ dep (j + 1) i := zpow_nonneg hk0 _
      have hone : k ^ dep (j + 1) i * E (j + 1) i ≤
          k ^ dep j i * E j i + k ^ dep (j + 1) i * ηc j i := by
        calc k ^ dep (j + 1) i * E (j + 1) i
            ≤ k ^ dep (j + 1) i * (k ^ delta j i * E j i + ηc j i) :=
              mul_le_mul_of_nonneg_left (hstep j i) hpow_nonneg
          _ = k ^ (dep (j + 1) i + delta j i) * E j i +
                k ^ dep (j + 1) i * ηc j i := by
              rw [mul_add, ← mul_assoc, ← zpow_add₀ hk_ne]
          _ = k ^ dep j i * E j i + k ^ dep (j + 1) i * ηc j i := by
              have hd : dep (j + 1) i + delta j i = dep j i := by
                rw [hdepth j i]
                abel
              rw [hd]
      have hdefect : k ^ dep (j + 1) i * ηc j i ≤ g j * η j := by
        have hg_nonneg : 0 ≤ g j := le_trans hpow_nonneg (hg_dom j i)
        exact mul_le_mul (hg_dom j i) (hη_dom j i) (hηc_nonneg j i) hg_nonneg
      calc k ^ dep (j + 1) i * E (j + 1) i
          ≤ k ^ dep j i * E j i + k ^ dep (j + 1) i * ηc j i := hone
        _ ≤ weightedMajorant W0 g η j + g j * η j := add_le_add ih hdefect
        _ = weightedMajorant W0 g η (j + 1) :=
            (weightedMajorant_succ W0 g η j).symm

/-- **Unweighted recovery.**  With nonnegative depth and `k > 1` the weight is
`≥ 1`, so the raw error is below the weighted budget:
`E(j,i) ≤ k^dep(j,i)·E(j,i) ≤ weightedMajorant(j)`. -/
theorem le_weightedMajorant_unweighted {ι : Sort*} (E : ℕ → ι → ℝ)
    {k : ℝ} (hk : 1 < k) (dep : ℕ → ι → ℤ) {W0 : ℝ} {g η : ℕ → ℝ}
    (hE_nonneg : ∀ j i, 0 ≤ E j i)
    (hdep_nonneg : ∀ j i, 0 ≤ dep j i)
    (hweighted : ∀ j i, k ^ dep j i * E j i ≤ weightedMajorant W0 g η j) :
    ∀ j i, E j i ≤ weightedMajorant W0 g η j := by
  intro j i
  have hone : (1 : ℝ) ≤ k ^ dep j i := by
    have hmono : k ^ (0 : ℤ) ≤ k ^ dep j i :=
      zpow_le_zpow_right₀ hk.le (hdep_nonneg j i)
    simpa using hmono
  calc E j i = 1 * E j i := (one_mul _).symm
    _ ≤ k ^ dep j i * E j i :=
        mul_le_mul_of_nonneg_right hone (hE_nonneg j i)
    _ ≤ weightedMajorant W0 g η j := hweighted j i

/-- Depth weight below an exponential: if `(n : ℝ) ≤ c` and `k > 1` then
`k^n ≤ e^{c·log k}`.  Converts the integer depth into the exponential scale of
the geometric cap. -/
theorem zpow_le_exp_of_cast_le {k : ℝ} (hk : 1 < k) {n : ℤ} {c : ℝ}
    (hn : (n : ℝ) ≤ c) :
    k ^ n ≤ Real.exp (Real.log k * c) := by
  have hkpos : (0 : ℝ) < k := zero_lt_one.trans hk
  calc k ^ n
      = k ^ ((n : ℤ) : ℝ) := by
        rw [Real.rpow_intCast]
    _ ≤ k ^ c := Real.rpow_le_rpow_of_exponent_le hk.le hn
    _ = Real.exp (Real.log k * c) := by
        rw [Real.rpow_def_of_pos hkpos]

/-- Linear depth growth `dep(j+1,i) ≤ L + j` gives the split exponential
dominator `k^dep(j+1,i) ≤ e^{L·log k}·e^{j·log k}` — the `g`-input of the
geometric cap, with `Cg = e^{L·log k}` and `β = log k`. -/
theorem zpow_dep_le_exp_linear {ι : Sort*} {k : ℝ} (hk : 1 < k)
    {dep : ℕ → ι → ℤ} {L : ℝ}
    (hgrow : ∀ j i, ((dep (j + 1) i : ℤ) : ℝ) ≤ L + (j : ℝ)) :
    ∀ j (i : ι), k ^ dep (j + 1) i ≤
      Real.exp (Real.log k * L) * Real.exp (Real.log k * (j : ℝ)) := by
  intro j i
  calc k ^ dep (j + 1) i
      ≤ Real.exp (Real.log k * (L + (j : ℝ))) :=
        zpow_le_exp_of_cast_le hk (hgrow j i)
    _ = Real.exp (Real.log k * L) * Real.exp (Real.log k * (j : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ## The concrete tracking error -/

/-- Write-start tracking error at cycle `j`, coordinate `i`: the distance of
the held config register `u` from the encoded machine configuration, sampled
at the cycle marker `mark j` (instantiated with `selectorMUWriteHoldTime` for
the settled write window, or `selectorMUWriteStartTime` for the boundary). -/
def trackingErr (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (mark : ℕ → ℝ)
    (j : ℕ) (i : Fin d_U) : ℝ :=
  |u (mark j) i - stackMachineEncodingU.enc (cfg j) i|

theorem trackingErr_nonneg (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf)
    (mark : ℕ → ℝ) (j : ℕ) (i : Fin d_U) :
    0 ≤ trackingErr u cfg mark j i := by
  simpa [trackingErr] using
    abs_nonneg (u (mark j) i - stackMachineEncodingU.enc (cfg j) i)

/-- Triangle split of the tracking error through the Reach register `z`. -/
theorem trackingErr_le_zu_add_zerr (u z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf)
    (mark : ℕ → ℝ) (j : ℕ) (i : Fin d_U) :
    trackingErr u cfg mark j i ≤
      |u (mark j) i - z (mark j) i| +
      |z (mark j) i - stackMachineEncodingU.enc (cfg j) i| := by
  simpa [trackingErr] using
    abs_sub_le (u (mark j) i) (z (mark j) i)
      (stackMachineEncodingU.enc (cfg j) i)

/-! ## The per-cycle excess

The positive part of the one-cycle defect against the `k^delta` comparison.
With this choice the `MURecur`-shape step is *algebraic*
(`trackingErr_succ_le_excess`); the analytic content is entirely in showing
the excess decays geometrically, which the settled write endpoint provides
(`trackingExcess_geometric_of_endpoint_errors`). -/

/-- Positive part of the exact one-cycle excess over the depth-weighted
comparison term. -/
def trackingExcess (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (mark : ℕ → ℝ)
    (k : ℝ) (delta : ℕ → Fin d_U → ℤ) (j : ℕ) (i : Fin d_U) : ℝ :=
  max (0 : ℝ)
    (trackingErr u cfg mark (j + 1) i -
      k ^ delta j i * trackingErr u cfg mark j i)

theorem trackingExcess_nonneg (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf)
    (mark : ℕ → ℝ) (k : ℝ) (delta : ℕ → Fin d_U → ℤ) (j : ℕ) (i : Fin d_U) :
    0 ≤ trackingExcess u cfg mark k delta j i := by
  unfold trackingExcess
  exact le_max_left _ _

/-- The `MURecur`-shape one-cycle step, discharged algebraically by the
positive-part excess. -/
theorem trackingErr_succ_le_excess (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf)
    (mark : ℕ → ℝ) {k : ℝ} (delta : ℕ → Fin d_U → ℤ) (j : ℕ) (i : Fin d_U) :
    trackingErr u cfg mark (j + 1) i ≤
      k ^ delta j i * trackingErr u cfg mark j i +
        trackingExcess u cfg mark k delta j i := by
  have h : trackingErr u cfg mark (j + 1) i -
      k ^ delta j i * trackingErr u cfg mark j i ≤
      trackingExcess u cfg mark k delta j i := by
    unfold trackingExcess
    exact le_max_right _ _
  linarith

/-- The excess is at most the next-cycle error (the comparison term it
discards is nonnegative). -/
theorem trackingExcess_le_trackingErr_succ (u : ℝ → Fin d_U → ℝ)
    (cfg : ℕ → UConf) (mark : ℕ → ℝ) {k : ℝ} (hk0 : 0 ≤ k)
    (delta : ℕ → Fin d_U → ℤ) (j : ℕ) (i : Fin d_U) :
    trackingExcess u cfg mark k delta j i ≤
      trackingErr u cfg mark (j + 1) i := by
  unfold trackingExcess
  refine max_le ?_ ?_
  · exact trackingErr_nonneg u cfg mark (j + 1) i
  · have hpow_nonneg : 0 ≤ k ^ delta j i := zpow_nonneg hk0 _
    have herr_nonneg : 0 ≤ trackingErr u cfg mark j i :=
      trackingErr_nonneg u cfg mark j i
    linarith [mul_nonneg hpow_nonneg herr_nonneg]

/-- Excess through the Reach register: the excess is controlled by the
next-write-start `z-u` transport plus the `z` encoding endpoint — the two
quantities the settled write dynamics estimate. -/
theorem trackingExcess_le_zu_add_zerr (u z : ℝ → Fin d_U → ℝ)
    (cfg : ℕ → UConf) (mark : ℕ → ℝ) {k : ℝ} (hk0 : 0 ≤ k)
    (delta : ℕ → Fin d_U → ℤ) (j : ℕ) (i : Fin d_U) :
    trackingExcess u cfg mark k delta j i ≤
      |u (mark (j + 1)) i - z (mark (j + 1)) i| +
      |z (mark (j + 1)) i - stackMachineEncodingU.enc (cfg (j + 1)) i| :=
  le_trans (trackingExcess_le_trackingErr_succ u cfg mark hk0 delta j i)
    (trackingErr_le_zu_add_zerr u z cfg mark (j + 1) i)

/-- **Excess geometric from endpoint-geometric errors.**  If the
next-write-start `z-u` transport and the `z` encoding endpoint both decay
geometrically at rate `lam`, so does the excess, with constant `Czu + Cz`.
This is the `η`-input of the geometric cap; the rate condition `lam > log k`
is checked there, not here. -/
theorem trackingExcess_geometric_of_endpoint_errors
    (u z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (mark : ℕ → ℝ)
    {k : ℝ} (hk0 : 0 ≤ k) (delta : ℕ → Fin d_U → ℤ) {Czu Cz lam : ℝ}
    (hzu_geo : ∀ j (i : Fin d_U),
      |u (mark (j + 1)) i - z (mark (j + 1)) i| ≤
        Czu * Real.exp (-lam * (j : ℝ)))
    (hzerr_geo : ∀ j (i : Fin d_U),
      |z (mark (j + 1)) i - stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
        Cz * Real.exp (-lam * (j : ℝ))) :
    ∀ j i, trackingExcess u cfg mark k delta j i ≤
      (Czu + Cz) * Real.exp (-lam * (j : ℝ)) := by
  intro j i
  have hsplit := trackingExcess_le_zu_add_zerr u z cfg mark hk0 delta j i
  have hend := add_le_add (hzu_geo j i) (hzerr_geo j i)
  calc trackingExcess u cfg mark k delta j i
      ≤ |u (mark (j + 1)) i - z (mark (j + 1)) i| +
        |z (mark (j + 1)) i - stackMachineEncodingU.enc (cfg (j + 1)) i| :=
        hsplit
    _ ≤ Czu * Real.exp (-lam * (j : ℝ)) +
          Cz * Real.exp (-lam * (j : ℝ)) := hend
    _ = (Czu + Cz) * Real.exp (-lam * (j : ℝ)) := by ring

/-! ## Master induction: weighted domination, unweighted bound -/

/-- Simultaneous domination of the tracking error by the weighted majorant:
the `MURecur`-shape step plus the depth bookkeeping give the weighted budget,
and `dep ≥ 0` recovers the unweighted bound. -/
theorem trackingErr_le_weightedMajorant
    (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (mark : ℕ → ℝ)
    {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin d_U → ℤ) (ηc : ℕ → Fin d_U → ℝ)
    {W0 : ℝ} {g η : ℕ → ℝ}
    (hdepth : ∀ j (i : Fin d_U), dep (j + 1) i = dep j i - delta j i)
    (hdep_nonneg : ∀ j (i : Fin d_U), 0 ≤ dep j i)
    (hstep : ∀ j (i : Fin d_U), trackingErr u cfg mark (j + 1) i ≤
      k ^ delta j i * trackingErr u cfg mark j i + ηc j i)
    (hbase : ∀ i : Fin d_U, k ^ dep 0 i * trackingErr u cfg mark 0 i ≤ W0)
    (hg_dom : ∀ j (i : Fin d_U), k ^ dep (j + 1) i ≤ g j)
    (hηc_nonneg : ∀ j (i : Fin d_U), 0 ≤ ηc j i)
    (hη_dom : ∀ j (i : Fin d_U), ηc j i ≤ η j) :
    ∀ j i, trackingErr u cfg mark j i ≤ weightedMajorant W0 g η j :=
  le_weightedMajorant_unweighted (trackingErr u cfg mark) hk dep
    (fun j i => trackingErr_nonneg u cfg mark j i) hdep_nonneg
    (le_weightedMajorant_of_weighted_step (trackingErr u cfg mark) hk
      dep delta ηc hdepth hstep hbase hg_dom hηc_nonneg hη_dom)

/-- **Combined master theorem.**  With the positive-part excess as the
recurrence defect, linear depth growth `dep(j+1,i) ≤ L + j`, and the two
endpoint errors geometric at a rate `lam > log k`, the tracking error is
uniformly bounded by the closed cap
`W0 + e^{L·log k}·(Czu + Cz)/(1 - e^{log k - lam})`.

The one-cycle step needs no separate hypothesis: it is algebraic for the
positive-part excess.  The depth-weighted contraction replaces the failed
unweighted contraction: the raw step expands by `k^delta ≤ B_U = 6` on stack
coordinates, but the weighted accumulation only has to beat the depth growth
— `η = O(e^{-lam·j})` with `lam > log B_U` suffices. -/
theorem trackingErr_exists_bound_of_depth_linear_and_excess_geometric
    (u z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (mark : ℕ → ℝ)
    {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin d_U → ℤ) {W0 L Czu Cz lam : ℝ}
    (hW0 : 0 ≤ W0) (hCzu : 0 ≤ Czu) (hCz : 0 ≤ Cz)
    (hrate : Real.log k < lam)
    (hdepth : ∀ j (i : Fin d_U), dep (j + 1) i = dep j i - delta j i)
    (hdep_nonneg : ∀ j (i : Fin d_U), 0 ≤ dep j i)
    (hgrow : ∀ j (i : Fin d_U), ((dep (j + 1) i : ℤ) : ℝ) ≤ L + (j : ℝ))
    (hbase : ∀ i : Fin d_U, k ^ dep 0 i * trackingErr u cfg mark 0 i ≤ W0)
    (hzu_geo : ∀ j (i : Fin d_U),
      |u (mark (j + 1)) i - z (mark (j + 1)) i| ≤
        Czu * Real.exp (-lam * (j : ℝ)))
    (hzerr_geo : ∀ j (i : Fin d_U),
      |z (mark (j + 1)) i - stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
        Cz * Real.exp (-lam * (j : ℝ))) :
    ∃ Rmax : ℝ, 0 ≤ Rmax ∧
      ∀ j i, trackingErr u cfg mark j i ≤ Rmax := by
  have hk0 : (0 : ℝ) ≤ k := (zero_lt_one.trans hk).le
  have hdom : ∀ j i, trackingErr u cfg mark j i ≤
      weightedMajorant W0
        (fun m => Real.exp (Real.log k * L) * Real.exp (Real.log k * (m : ℝ)))
        (fun m => (Czu + Cz) * Real.exp (-lam * (m : ℝ))) j :=
    trackingErr_le_weightedMajorant u cfg mark hk dep delta
      (trackingExcess u cfg mark k delta)
      hdepth hdep_nonneg
      (fun j i => trackingErr_succ_le_excess u cfg mark delta j i)
      hbase
      (fun j i => zpow_dep_le_exp_linear hk hgrow j i)
      (fun j i => trackingExcess_nonneg u cfg mark k delta j i)
      (fun j i => trackingExcess_geometric_of_endpoint_errors
        u z cfg mark hk0 delta hzu_geo hzerr_geo j i)
  have hcap : ∀ j, weightedMajorant W0
      (fun m => Real.exp (Real.log k * L) * Real.exp (Real.log k * (m : ℝ)))
      (fun m => (Czu + Cz) * Real.exp (-lam * (m : ℝ))) j ≤
      W0 + Real.exp (Real.log k * L) * (Czu + Cz) *
        (1 / (1 - Real.exp (Real.log k - lam))) :=
    weightedMajorant_le_geomCap
      (Cg := Real.exp (Real.log k * L)) (Cη := Czu + Cz)
      (β := Real.log k) (lam := lam)
      (Real.exp_pos _).le (add_nonneg hCzu hCz) hrate
      (fun m => mul_nonneg (add_nonneg hCzu hCz) (Real.exp_pos _).le)
      (fun m => le_rfl) (fun m => le_rfl)
  have hq_lt_one : Real.exp (Real.log k - lam) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden_pos : 0 < 1 - Real.exp (Real.log k - lam) := by linarith
  have hfrac_nonneg : 0 ≤ 1 / (1 - Real.exp (Real.log k - lam)) :=
    (div_pos one_pos hden_pos).le
  refine ⟨W0 + Real.exp (Real.log k * L) * (Czu + Cz) *
      (1 / (1 - Real.exp (Real.log k - lam))), ?_, ?_⟩
  · exact add_nonneg hW0
      (mul_nonneg
        (mul_nonneg (Real.exp_pos _).le (add_nonneg hCzu hCz))
        hfrac_nonneg)
  · intro j i
    exact (hdom j i).trans (hcap j)

/-! ## `hmix_settled` as a consequence of the weighted cycle induction

The settled-window mixture estimate holds for *every* cycle `j`, with the
u-tube input supplied by the depth-weighted simultaneous induction instead of
the coarse u-tube budget — this is the point where the circular dependency is
broken. -/

/-- `hmix_settled` from the weighted cycle induction, in general window form.
`mixTarget_near_next_on_settled_window` is instantiated with
`ρu := weightedMajorant W0 g η`, whose defining property is exactly the
simultaneous weighted domination proved above. -/
theorem mix_settled_of_weighted_majorant
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38
      selectorSchedule branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf) (writeStart readStart : ℕ → ℝ)
    (epsLam Rspread δu : ℕ → ℝ)
    {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin d_U → ℤ) (ηc : ℕ → Fin d_U → ℝ)
    {mult W0 : ℝ} {g η : ℕ → ℝ}
    (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (hdepth : ∀ j (i : Fin d_U), dep (j + 1) i = dep j i - delta j i)
    (hdep_nonneg : ∀ j (i : Fin d_U), 0 ≤ dep j i)
    (hstep : ∀ j (i : Fin d_U),
      trackingErr sol.u cfg writeStart (j + 1) i ≤
        k ^ delta j i * trackingErr sol.u cfg writeStart j i + ηc j i)
    (hbase : ∀ i : Fin d_U,
      k ^ dep 0 i * trackingErr sol.u cfg writeStart 0 i ≤ W0)
    (hg_dom : ∀ j (i : Fin d_U), k ^ dep (j + 1) i ≤ g j)
    (hηc_nonneg : ∀ j (i : Fin d_U), 0 ≤ ηc j i)
    (hη_dom : ∀ j (i : Fin d_U), ηc j i ≤ η j)
    (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ j, ∀ i : Fin d_U,
      stackMachineEncodingU.coordMultiplier (cfg j) i ≤ mult)
    (hsum : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j),
      (∑ v : UniversalLocalView, sol.lam v t) = 1)
    (hlam_nonneg : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j),
      ∀ v : UniversalLocalView, 0 ≤ sol.lam v t)
    (hloser : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j),
      (Finset.univ.filter
        (fun v : UniversalLocalView => v ≠ localViewU (cfg j))).sum
          (fun v => sol.lam v t) ≤ epsLam j)
    (hRspread_nonneg : ∀ j, 0 ≤ Rspread j)
    (hspread : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j), ∀ i : Fin d_U,
      ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
        |BranchData.evalBranch (branchU v) (sol.u t) i
          - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u t) i|
            ≤ Rspread j)
    (hudrift : ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j), ∀ i : Fin d_U,
      |sol.u t i - sol.u (writeStart j) i| ≤ δu j) :
    ∀ j, ∀ t ∈ Icc (writeStart j) (readStart j), ∀ i : Fin d_U,
      |selectorMixTarget branchU sol.u sol.lam t i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      Rspread j * epsLam j +
        mult * (weightedMajorant W0 g η j + δu j) := by
  have hutube : ∀ j, ∀ i : Fin d_U,
      |sol.u (writeStart j) i - stackMachineEncodingU.enc (cfg j) i| ≤
        weightedMajorant W0 g η j := by
    intro j i
    simpa [trackingErr] using
      trackingErr_le_weightedMajorant sol.u cfg writeStart hk dep delta ηc
        hdepth hdep_nonneg hstep hbase hg_dom hηc_nonneg hη_dom j i
  intro j t ht i
  have h := mixTarget_near_next_on_settled_window sol cfg writeStart readStart
    epsLam Rspread (weightedMajorant W0 g η) δu hmult0 hmultbound
    hsum hlam_nonneg hloser hRspread_nonneg hspread hutube hudrift j t ht i
  rw [hcfg_step j]
  exact h

/-! ## The settled mixture radius of the weighted induction -/

/-- Settled mixture radius produced by the weighted cycle induction:
`Rspread(j)·epsLam(j) + mult·(weightedMajorant(j) + δu(j))`.
This is the `δwSettled` fed to `z_write_settled_endpoint`. -/
def weightedMixRadius (Rspread epsLam δu : ℕ → ℝ) (mult W0 : ℝ)
    (g η : ℕ → ℝ) (j : ℕ) : ℝ :=
  Rspread j * epsLam j + mult * (weightedMajorant W0 g η j + δu j)

/-- **The mixture radius is uniformly bounded.**  The concentration term is
bounded by `Rs·Ce`, and the carried tube is bounded through the geometric cap
of the weighted majorant.  (In the weighted picture boundedness — not decay —
is the deliverable: the decay of the settled write error comes from the
`exp(-Λ)` contraction downstream, not from the tube radius.) -/
theorem weightedMixRadius_le_cap
    {Rspread epsLam δu : ℕ → ℝ} {mult W0 : ℝ} {g η : ℕ → ℝ}
    {Rs Ce Cu Cg Cη β lam : ℝ}
    (hCg : 0 ≤ Cg) (hCη : 0 ≤ Cη) (hβlam : β < lam)
    (hη_nonneg : ∀ j, 0 ≤ η j)
    (hg_le : ∀ j, g j ≤ Cg * Real.exp (β * (j : ℝ)))
    (hη_le : ∀ j, η j ≤ Cη * Real.exp (-lam * (j : ℝ)))
    (hmult0 : 0 ≤ mult)
    (hRspread_nonneg : ∀ j, 0 ≤ Rspread j)
    (hRs : ∀ j, Rspread j ≤ Rs)
    (hepsLam_nonneg : ∀ j, 0 ≤ epsLam j)
    (hCe : ∀ j, epsLam j ≤ Ce)
    (hCu : ∀ j, δu j ≤ Cu) :
    ∀ j, weightedMixRadius Rspread epsLam δu mult W0 g η j ≤
      Rs * Ce +
        mult * (W0 + Cg * Cη * (1 / (1 - Real.exp (β - lam))) + Cu) := by
  intro j
  have h1 : Rspread j * epsLam j ≤ Rs * Ce := by
    have hRs_nonneg : 0 ≤ Rs := le_trans (hRspread_nonneg j) (hRs j)
    exact mul_le_mul (hRs j) (hCe j) (hepsLam_nonneg j) hRs_nonneg
  have h2 : weightedMajorant W0 g η j ≤
      W0 + Cg * Cη * (1 / (1 - Real.exp (β - lam))) :=
    weightedMajorant_le_geomCap hCg hCη hβlam hη_nonneg hg_le hη_le j
  have h3 : weightedMajorant W0 g η j + δu j ≤
      W0 + Cg * Cη * (1 / (1 - Real.exp (β - lam))) + Cu :=
    add_le_add h2 (hCu j)
  have h4 : mult * (weightedMajorant W0 g η j + δu j) ≤
      mult * (W0 + Cg * Cη * (1 / (1 - Real.exp (β - lam))) + Cu) :=
    mul_le_mul_of_nonneg_left h3 hmult0
  unfold weightedMixRadius
  linarith

/-- **`hmix_settled` for all `j` on the settled write window**
`[selectorMUWriteHoldTime j, selectorMUWriteReadTime j]`, with the radius
`weightedMixRadius` — the exact input shape of `z_write_settled_endpoint`.
Combined with `weightedMixRadius_le_cap`, this discharges the settled mixture
input of the endpoint recurrence without the coarse u-tube budget: the u-tube
comes from the depth-weighted induction, not from the budget structure. -/
theorem hmix_settled_of_weighted_tracking
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38
      selectorSchedule branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf)
    (epsLam Rspread δu : ℕ → ℝ)
    {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin d_U → ℤ) (ηc : ℕ → Fin d_U → ℝ)
    {mult W0 : ℝ} {g η : ℕ → ℝ}
    (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (hdepth : ∀ j (i : Fin d_U), dep (j + 1) i = dep j i - delta j i)
    (hdep_nonneg : ∀ j (i : Fin d_U), 0 ≤ dep j i)
    (hstep : ∀ j (i : Fin d_U),
      trackingErr sol.u cfg selectorMUWriteHoldTime (j + 1) i ≤
        k ^ delta j i *
          trackingErr sol.u cfg selectorMUWriteHoldTime j i + ηc j i)
    (hbase : ∀ i : Fin d_U,
      k ^ dep 0 i * trackingErr sol.u cfg selectorMUWriteHoldTime 0 i ≤ W0)
    (hg_dom : ∀ j (i : Fin d_U), k ^ dep (j + 1) i ≤ g j)
    (hηc_nonneg : ∀ j (i : Fin d_U), 0 ≤ ηc j i)
    (hη_dom : ∀ j (i : Fin d_U), ηc j i ≤ η j)
    (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ j, ∀ i : Fin d_U,
      stackMachineEncodingU.coordMultiplier (cfg j) i ≤ mult)
    (hsum : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      (∑ v : UniversalLocalView, sol.lam v t) = 1)
    (hlam_nonneg : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      ∀ v : UniversalLocalView, 0 ≤ sol.lam v t)
    (hloser : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      (Finset.univ.filter
        (fun v : UniversalLocalView => v ≠ localViewU (cfg j))).sum
          (fun v => sol.lam v t) ≤ epsLam j)
    (hRspread_nonneg : ∀ j, 0 ≤ Rspread j)
    (hspread : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      ∀ i : Fin d_U,
      ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
        |BranchData.evalBranch (branchU v) (sol.u t) i
          - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u t) i|
            ≤ Rspread j)
    (hudrift : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      ∀ i : Fin d_U,
      |sol.u t i - sol.u (selectorMUWriteHoldTime j) i| ≤ δu j) :
    ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      ∀ i : Fin d_U,
      |selectorMixTarget branchU sol.u sol.lam t i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      weightedMixRadius Rspread epsLam δu mult W0 g η j := by
  intro j t ht i
  simpa [weightedMixRadius] using
    mix_settled_of_weighted_majorant sol cfg
      selectorMUWriteHoldTime selectorMUWriteReadTime
      epsLam Rspread δu hk dep delta ηc
      hcfg_step hdepth hdep_nonneg hstep hbase hg_dom hηc_nonneg hη_dom
      hmult0 hmultbound hsum hlam_nonneg hloser hRspread_nonneg hspread
      hudrift j t ht i

/-! ## Conditional-step induction: breaking the `hloser` circularity

The unconditional `∀ j` inputs of `le_weightedMajorant_of_weighted_step` and
`hmix_settled_of_weighted_tracking` (`hstep`, `hη_dom`, `hloser`) cannot be
produced non-circularly.  The settled-window loser-mass bound at cycle `j`
comes from `loser_mass_small_on_settled_window`, whose payoff-gap input
`hgap` is discharged by `selector_replicator_hgap_of_utube` — that is, from
the *cycle-`j` readout tube* `UTube r_LE_U (cfg j) (u t)`.  The tube is
exactly what the induction is proving, so demanding `hloser` for all cycles
up front re-imports the coarse u-tube budget and closes the circle.

The escape is not a stronger producer but a weaker consumer.  At step `j` of
the simultaneous induction, the weighted bound `k^dep(j,·)·E(j,·) ≤ W(j)` is
*already established*; with `dep ≥ 0` and `k > 1` it releases the unweighted
cycle-`j` tube `E(j,·) ≤ W(j) ≤ cap ≤ r`.  So the one-cycle step and the
excess domination only ever need to be supplied *conditionally on the
cycle-`j` tube* — the shape the loser-mass/gap machinery actually produces
them in.  Nothing is assumed globally; the induction hypothesis pays for each
cycle's analytic inputs as it goes.

A second structural point (the `δw`-is-not-geometric worry): the settled
mixture radius `Rspread·epsLam + mult·(ρu + δu)` does **not** need to decay.
Per coordinate, the branch multiplier is bounded by the actual stack
operation (`branchU` contract clause: pop ≤ `B_U = k^1`, push `= 1/B_U =
k^{-1}`, stay/replace ≤ `1 = k^0`), i.e. by `k^delta(j,i)`.  Hence the
`mult·ρu` part of the one-cycle estimate is absorbed by the `k^delta·E(j)`
comparison term and never enters the excess: the excess is bounded by the
*source alone* (`trackingExcess_le_source_of_multiplier_step`), and only the
source — loser mass, `u`-drift, gate-contraction residual — has to be
geometric at a rate beating `log k`.  All of these decay per cycle at rates
far above `log B_U` (the qPulse relaxation contributes `e^{-450·Δt}`, and
`epsLam`/gate residuals decay through `ΔG(j) → ∞`). -/

/-- **Conditional simultaneous weighted cycle induction.**  Same conclusion
as `le_weightedMajorant_of_weighted_step`, but the one-cycle step and the
excess domination are required only at cycles where the weighted bound has
already been established — the shape in which the settled-window (loser-mass
driven) estimates can be produced without circularity, since the payoff gap
needs the cycle-`j` tube. -/
theorem le_weightedMajorant_of_conditional_weighted_step {ι : Sort*}
    (E : ℕ → ι → ℝ) {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → ι → ℤ) (ηc : ℕ → ι → ℝ) {W0 : ℝ} {g η : ℕ → ℝ}
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hstep : ∀ j,
      (∀ i, k ^ dep j i * E j i ≤ weightedMajorant W0 g η j) →
      ∀ i, E (j + 1) i ≤ k ^ delta j i * E j i + ηc j i)
    (hbase : ∀ i, k ^ dep 0 i * E 0 i ≤ W0)
    (hg_dom : ∀ j i, k ^ dep (j + 1) i ≤ g j)
    (hηc_nonneg : ∀ j i, 0 ≤ ηc j i)
    (hη_dom : ∀ j,
      (∀ i, k ^ dep j i * E j i ≤ weightedMajorant W0 g η j) →
      ∀ i, ηc j i ≤ η j) :
    ∀ j i, k ^ dep j i * E j i ≤ weightedMajorant W0 g η j := by
  intro j
  induction j with
  | zero =>
      intro i
      rw [weightedMajorant_zero]
      exact hbase i
  | succ j ih =>
      intro i
      have hstepj := hstep j ih
      have hηj := hη_dom j ih
      have hk0 : (0 : ℝ) ≤ k := (zero_lt_one.trans hk).le
      have hk_ne : k ≠ 0 := (zero_lt_one.trans hk).ne'
      have hpow_nonneg : 0 ≤ k ^ dep (j + 1) i := zpow_nonneg hk0 _
      have hone : k ^ dep (j + 1) i * E (j + 1) i ≤
          k ^ dep j i * E j i + k ^ dep (j + 1) i * ηc j i := by
        calc k ^ dep (j + 1) i * E (j + 1) i
            ≤ k ^ dep (j + 1) i * (k ^ delta j i * E j i + ηc j i) :=
              mul_le_mul_of_nonneg_left (hstepj i) hpow_nonneg
          _ = k ^ (dep (j + 1) i + delta j i) * E j i +
                k ^ dep (j + 1) i * ηc j i := by
              rw [mul_add, ← mul_assoc, ← zpow_add₀ hk_ne]
          _ = k ^ dep j i * E j i + k ^ dep (j + 1) i * ηc j i := by
              have hd : dep (j + 1) i + delta j i = dep j i := by
                rw [hdepth j i]
                abel
              rw [hd]
      have hdefect : k ^ dep (j + 1) i * ηc j i ≤ g j * η j := by
        have hg_nonneg : 0 ≤ g j := le_trans hpow_nonneg (hg_dom j i)
        exact mul_le_mul (hg_dom j i) (hηj i) (hηc_nonneg j i) hg_nonneg
      calc k ^ dep (j + 1) i * E (j + 1) i
          ≤ k ^ dep j i * E j i + k ^ dep (j + 1) i * ηc j i := hone
        _ ≤ weightedMajorant W0 g η j + g j * η j := add_le_add (ih i) hdefect
        _ = weightedMajorant W0 g η (j + 1) :=
            (weightedMajorant_succ W0 g η j).symm

/-- The weighted bound at cycle `j` releases the unweighted cycle-`j` tube
whenever the majorant sits below the tube radius: `dep ≥ 0` and `k > 1` give
`k^dep ≥ 1`, so `E(j,i) ≤ k^dep·E(j,i) ≤ W(j) ≤ r`.  This is the unlock that
lets the induction hypothesis pay for the cycle-`j` loser-mass inputs. -/
theorem tube_of_weighted_le {ι : Sort*} (E : ℕ → ι → ℝ)
    {k r : ℝ} (hk : 1 < k) (dep : ℕ → ι → ℤ) {W0 : ℝ} {g η : ℕ → ℝ}
    (hE_nonneg : ∀ j i, 0 ≤ E j i)
    (hdep_nonneg : ∀ j i, 0 ≤ dep j i) (j : ℕ)
    (hcap_j : weightedMajorant W0 g η j ≤ r)
    (hweighted : ∀ i, k ^ dep j i * E j i ≤ weightedMajorant W0 g η j) :
    ∀ i, E j i ≤ r := by
  intro i
  have hone : (1 : ℝ) ≤ k ^ dep j i := by
    have hmono : k ^ (0 : ℤ) ≤ k ^ dep j i :=
      zpow_le_zpow_right₀ hk.le (hdep_nonneg j i)
    simpa using hmono
  calc E j i = 1 * E j i := (one_mul _).symm
    _ ≤ k ^ dep j i * E j i :=
        mul_le_mul_of_nonneg_right hone (hE_nonneg j i)
    _ ≤ weightedMajorant W0 g η j := hweighted i
    _ ≤ r := hcap_j

/-- **Tube-conditional simultaneous weighted cycle induction.**  The step and
the excess domination are required only given the unweighted cycle-`j` tube
of radius `r`; the tube itself is recovered at each step from the weighted
bound through the cap `weightedMajorant ≤ r`. -/
theorem le_weightedMajorant_of_tube_conditional_step {ι : Sort*}
    (E : ℕ → ι → ℝ) {k r : ℝ} (hk : 1 < k)
    (dep delta : ℕ → ι → ℤ) (ηc : ℕ → ι → ℝ) {W0 : ℝ} {g η : ℕ → ℝ}
    (hE_nonneg : ∀ j i, 0 ≤ E j i)
    (hdep_nonneg : ∀ j i, 0 ≤ dep j i)
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hcap : ∀ j, weightedMajorant W0 g η j ≤ r)
    (hstep : ∀ j, (∀ i, E j i ≤ r) →
      ∀ i, E (j + 1) i ≤ k ^ delta j i * E j i + ηc j i)
    (hbase : ∀ i, k ^ dep 0 i * E 0 i ≤ W0)
    (hg_dom : ∀ j i, k ^ dep (j + 1) i ≤ g j)
    (hηc_nonneg : ∀ j i, 0 ≤ ηc j i)
    (hη_dom : ∀ j, (∀ i, E j i ≤ r) → ∀ i, ηc j i ≤ η j) :
    ∀ j i, k ^ dep j i * E j i ≤ weightedMajorant W0 g η j :=
  le_weightedMajorant_of_conditional_weighted_step E hk dep delta ηc hdepth
    (fun j hw => hstep j
      (tube_of_weighted_le E hk dep hE_nonneg hdep_nonneg j (hcap j) hw))
    hbase hg_dom hηc_nonneg
    (fun j hw => hη_dom j
      (tube_of_weighted_le E hk dep hE_nonneg hdep_nonneg j (hcap j) hw))

/-! ## Absorbing the multiplier: the excess needs only the source

The raw one-cycle estimate produced by the settled write endpoint has the
per-coordinate multiplier form `E(j+1,i) ≤ m(j,i)·E(j,i) + s(j,i)`, where
`m(j,i)` is the branch diagonal multiplier at coordinate `i` (bounded by the
actual stack operation: `≤ k^delta(j,i)`) and `s(j,i)` collects the genuinely
decaying sources — `Rspread·epsLam(j)`, the multiplier times the `u`-drift,
the gate-contraction residual, and the endpoint `z-u` transport.  The bounded
tube radius `ρu` multiplies `m`, not `s`: it is absorbed by the comparison
term and never has to decay. -/

/-- `MURecur`-shape step from a raw multiplier step: if the raw one-cycle
estimate has multiplier `m(j,i) ≤ k^delta(j,i)`, the comparison-shaped step
holds with the *same source*. -/
theorem trackingErr_succ_le_of_multiplier_step
    (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (mark : ℕ → ℝ)
    {k : ℝ} (delta : ℕ → Fin d_U → ℤ) {m s : ℕ → Fin d_U → ℝ}
    (j : ℕ) (i : Fin d_U)
    (hm_le : m j i ≤ k ^ delta j i)
    (hraw : trackingErr u cfg mark (j + 1) i ≤
      m j i * trackingErr u cfg mark j i + s j i) :
    trackingErr u cfg mark (j + 1) i ≤
      k ^ delta j i * trackingErr u cfg mark j i + s j i := by
  have hcmp : m j i * trackingErr u cfg mark j i ≤
      k ^ delta j i * trackingErr u cfg mark j i :=
    mul_le_mul_of_nonneg_right hm_le (trackingErr_nonneg u cfg mark j i)
  linarith

/-- **The excess is bounded by the source alone.**  Under a raw multiplier
step with `m(j,i) ≤ k^delta(j,i)`, the positive-part excess discards the
entire comparison term: the bounded-tube contribution `m·ρu` never enters the
excess, so the geometric requirement falls only on the decaying source
`s(j,i)`.  This dissolves the "constant `mult·R` term" obstruction to a
geometric `η`. -/
theorem trackingExcess_le_source_of_multiplier_step
    (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (mark : ℕ → ℝ)
    {k : ℝ} (delta : ℕ → Fin d_U → ℤ) {m s : ℕ → Fin d_U → ℝ}
    (j : ℕ) (i : Fin d_U)
    (hs_nonneg : 0 ≤ s j i)
    (hm_le : m j i ≤ k ^ delta j i)
    (hraw : trackingErr u cfg mark (j + 1) i ≤
      m j i * trackingErr u cfg mark j i + s j i) :
    trackingExcess u cfg mark k delta j i ≤ s j i := by
  have hcmp : m j i * trackingErr u cfg mark j i ≤
      k ^ delta j i * trackingErr u cfg mark j i :=
    mul_le_mul_of_nonneg_right hm_le (trackingErr_nonneg u cfg mark j i)
  unfold trackingExcess
  refine max_le hs_nonneg ?_
  linarith

/-- **Tube-conditional master theorem.**  If

* the one-cycle `MURecur`-shape step and the geometric excess bound are
  available *given the cycle-`j` tube of radius `r`* (the shape the
  settled-window loser-mass machinery produces: the payoff gap needs `u`
  inside the readout tube),
* the depth grows at most linearly and the excess rate beats the depth
  weight (`lam > log k`), and
* the closed geometric cap fits inside the tube radius (the quantitative
  reserve `W0 + e^{L·log k}·Cη/(1 - e^{log k - lam}) ≤ r`),

then the tracking error stays inside the tube at *every* cycle — with no
unconditional all-cycle analytic input anywhere. -/
theorem trackingErr_le_tube_of_conditional_step_geometric
    (u : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (mark : ℕ → ℝ)
    {k r : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin d_U → ℤ) (ηc : ℕ → Fin d_U → ℝ)
    {W0 L Cη lam : ℝ}
    (hCη : 0 ≤ Cη) (hrate : Real.log k < lam)
    (hdepth : ∀ j (i : Fin d_U), dep (j + 1) i = dep j i - delta j i)
    (hdep_nonneg : ∀ j (i : Fin d_U), 0 ≤ dep j i)
    (hgrow : ∀ j (i : Fin d_U), ((dep (j + 1) i : ℤ) : ℝ) ≤ L + (j : ℝ))
    (hbase : ∀ i : Fin d_U, k ^ dep 0 i * trackingErr u cfg mark 0 i ≤ W0)
    (hstep : ∀ j, (∀ i, trackingErr u cfg mark j i ≤ r) →
      ∀ i, trackingErr u cfg mark (j + 1) i ≤
        k ^ delta j i * trackingErr u cfg mark j i + ηc j i)
    (hηc_nonneg : ∀ j (i : Fin d_U), 0 ≤ ηc j i)
    (hη_dom : ∀ j, (∀ i, trackingErr u cfg mark j i ≤ r) →
      ∀ i, ηc j i ≤ Cη * Real.exp (-lam * (j : ℝ)))
    (hreserve : W0 + Real.exp (Real.log k * L) * Cη *
        (1 / (1 - Real.exp (Real.log k - lam))) ≤ r) :
    ∀ j i, trackingErr u cfg mark j i ≤ r := by
  have hcap : ∀ j, weightedMajorant W0
      (fun m => Real.exp (Real.log k * L) * Real.exp (Real.log k * (m : ℝ)))
      (fun m => Cη * Real.exp (-lam * (m : ℝ))) j ≤ r := by
    intro j
    have h := weightedMajorant_le_geomCap
      (W0 := W0)
      (Cg := Real.exp (Real.log k * L)) (Cη := Cη)
      (β := Real.log k) (lam := lam)
      (Real.exp_pos _).le hCη hrate
      (fun m => mul_nonneg hCη (Real.exp_pos _).le)
      (fun m => le_rfl) (fun m => le_rfl) j
    exact h.trans hreserve
  have hweighted :=
    le_weightedMajorant_of_tube_conditional_step
      (trackingErr u cfg mark) hk dep delta ηc
      (fun j i => trackingErr_nonneg u cfg mark j i) hdep_nonneg hdepth hcap
      hstep hbase (fun j i => zpow_dep_le_exp_linear hk hgrow j i)
      hηc_nonneg hη_dom
  intro j i
  exact tube_of_weighted_le (trackingErr u cfg mark) hk dep
    (fun j' i' => trackingErr_nonneg u cfg mark j' i') hdep_nonneg j (hcap j)
    (fun i' => hweighted j i') i

/-- **`hmix_settled` with tube-conditional analytic inputs.**  The step, the
excess domination, and — crucially — the loser-mass bound `hloser` are only
required *given the cycle-`j` tracking tube of radius `r`*.  This is the
non-circular producer shape: `hloser` at cycle `j` comes from
`loser_mass_small_on_settled_window` whose payoff gap
(`selector_replicator_hgap_of_utube`) needs exactly the cycle-`j` tube, which
the weighted induction supplies through the cap `weightedMajorant ≤ r`.  No
coarse all-cycle u-tube budget is consumed anywhere. -/
theorem hmix_settled_of_tube_conditional_tracking
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38
      selectorSchedule branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (cfg : ℕ → UConf)
    (epsLam Rspread δu : ℕ → ℝ)
    {k r : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin d_U → ℤ) (ηc : ℕ → Fin d_U → ℝ)
    {mult W0 : ℝ} {g η : ℕ → ℝ}
    (hcfg_step : ∀ j, cfg (j + 1) = M_U.step (cfg j))
    (hdepth : ∀ j (i : Fin d_U), dep (j + 1) i = dep j i - delta j i)
    (hdep_nonneg : ∀ j (i : Fin d_U), 0 ≤ dep j i)
    (hcap : ∀ j, weightedMajorant W0 g η j ≤ r)
    (hstep : ∀ j,
      (∀ i : Fin d_U, trackingErr sol.u cfg selectorMUWriteHoldTime j i ≤ r) →
      ∀ i : Fin d_U,
        trackingErr sol.u cfg selectorMUWriteHoldTime (j + 1) i ≤
          k ^ delta j i *
            trackingErr sol.u cfg selectorMUWriteHoldTime j i + ηc j i)
    (hbase : ∀ i : Fin d_U,
      k ^ dep 0 i * trackingErr sol.u cfg selectorMUWriteHoldTime 0 i ≤ W0)
    (hg_dom : ∀ j (i : Fin d_U), k ^ dep (j + 1) i ≤ g j)
    (hηc_nonneg : ∀ j (i : Fin d_U), 0 ≤ ηc j i)
    (hη_dom : ∀ j,
      (∀ i : Fin d_U, trackingErr sol.u cfg selectorMUWriteHoldTime j i ≤ r) →
      ∀ i : Fin d_U, ηc j i ≤ η j)
    (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ j, ∀ i : Fin d_U,
      stackMachineEncodingU.coordMultiplier (cfg j) i ≤ mult)
    (hsum : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      (∑ v : UniversalLocalView, sol.lam v t) = 1)
    (hlam_nonneg : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      ∀ v : UniversalLocalView, 0 ≤ sol.lam v t)
    (hloser : ∀ j,
      (∀ i : Fin d_U, trackingErr sol.u cfg selectorMUWriteHoldTime j i ≤ r) →
      ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      (Finset.univ.filter
        (fun v : UniversalLocalView => v ≠ localViewU (cfg j))).sum
          (fun v => sol.lam v t) ≤ epsLam j)
    (hRspread_nonneg : ∀ j, 0 ≤ Rspread j)
    (hspread : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      ∀ i : Fin d_U,
      ∀ v : UniversalLocalView, v ≠ localViewU (cfg j) →
        |BranchData.evalBranch (branchU v) (sol.u t) i
          - BranchData.evalBranch (branchU (localViewU (cfg j))) (sol.u t) i|
            ≤ Rspread j)
    (hudrift : ∀ j, ∀ t ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      ∀ i : Fin d_U,
      |sol.u t i - sol.u (selectorMUWriteHoldTime j) i| ≤ δu j) :
    ∀ j, ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      ∀ i : Fin d_U,
      |selectorMixTarget branchU sol.u sol.lam t i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      weightedMixRadius Rspread epsLam δu mult W0 g η j := by
  have hweighted : ∀ j (i : Fin d_U),
      k ^ dep j i *
        trackingErr sol.u cfg selectorMUWriteHoldTime j i ≤
        weightedMajorant W0 g η j :=
    le_weightedMajorant_of_tube_conditional_step
      (trackingErr sol.u cfg selectorMUWriteHoldTime) hk dep delta ηc
      (fun j i => trackingErr_nonneg sol.u cfg selectorMUWriteHoldTime j i)
      hdep_nonneg hdepth hcap hstep hbase hg_dom hηc_nonneg hη_dom
  have htube : ∀ j, ∀ i : Fin d_U,
      trackingErr sol.u cfg selectorMUWriteHoldTime j i ≤ r := fun j =>
    tube_of_weighted_le (trackingErr sol.u cfg selectorMUWriteHoldTime) hk dep
      (fun j' i' => trackingErr_nonneg sol.u cfg selectorMUWriteHoldTime j' i')
      hdep_nonneg j (hcap j) (fun i => hweighted j i)
  exact hmix_settled_of_weighted_tracking sol cfg epsLam Rspread δu hk
    dep delta ηc hcfg_step hdepth hdep_nonneg
    (fun j i => hstep j (htube j) i) hbase hg_dom hηc_nonneg
    (fun j i => hη_dom j (htube j) i) hmult0 hmultbound hsum hlam_nonneg
    (fun j => hloser j (htube j)) hRspread_nonneg hspread hudrift

#print axioms weightedMajorant_le_geomCap
#print axioms le_weightedMajorant_of_weighted_step
#print axioms le_weightedMajorant_unweighted
#print axioms zpow_dep_le_exp_linear
#print axioms trackingErr_succ_le_excess
#print axioms trackingExcess_geometric_of_endpoint_errors
#print axioms trackingErr_le_weightedMajorant
#print axioms trackingErr_exists_bound_of_depth_linear_and_excess_geometric
#print axioms mix_settled_of_weighted_majorant
#print axioms weightedMixRadius_le_cap
#print axioms hmix_settled_of_weighted_tracking
#print axioms le_weightedMajorant_of_conditional_weighted_step
#print axioms tube_of_weighted_le
#print axioms le_weightedMajorant_of_tube_conditional_step
#print axioms trackingErr_succ_le_of_multiplier_step
#print axioms trackingExcess_le_source_of_multiplier_step
#print axioms trackingErr_le_tube_of_conditional_step_geometric
#print axioms hmix_settled_of_tube_conditional_tracking

end Ripple.BoundedUniversality.BGP
