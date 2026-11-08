/-
  SCWB/Stochastic/UnboundedError.lean

  Error convergence infrastructure for SCWB Theorem 4.1 (Turing-universal,
  unbounded computation).

  Mathematical content (from SCWB paper Section 4):
  - At each tape extension (step n), accuracy species count triples:
      A_n = 3 · A_{n−1}
  - Per-step error at step n: ε_n = O(1/A_n^{l−1}) = O(1/(3^n · A_0)^{l−1})
  - Total error: Σ_{n=0}^∞ ε_n = O(Σ 1/3^{n(l−1)}) which converges for l ≥ 2

  Key result: geometric-decay error sequences have bounded partial sums,
  satisfying the prefix-bound hypothesis of EventBound.countUnion_of_prefixBounds.
-/
import Ripple.sCRNUniversality.Probability.Contracts
import Mathlib.Analysis.SpecificLimits.Basic

namespace Ripple.sCRNUniversality

namespace Probability

namespace UnboundedError

/-- A geometric error sequence: `base * decay^n` at step `n`. -/
noncomputable def geometricErrorSeq (base decay : ENNReal) (n : ℕ) : ENNReal :=
  base * decay ^ n

/-- The total bound for a geometric error sequence: `base / (1 - decay)`,
    written as `base * (1 - decay)⁻¹` in ENNReal. -/
noncomputable def geometricErrorTotal (base decay : ENNReal) : ENNReal :=
  base * (1 - decay)⁻¹

/--
The partial sum `∑_{k=0}^{N-1} decay^k` is bounded by `(1 - decay)⁻¹`.
This is the pure geometric series bound without the leading `base` factor.
-/
theorem geom_partial_sum_le (decay : ENNReal) (N : ℕ) :
    (Finset.range N).sum (fun k => decay ^ k) ≤ (1 - decay)⁻¹ := by
  calc (Finset.range N).sum (fun k => decay ^ k)
      ≤ ∑' k, decay ^ k := ENNReal.sum_le_tsum _
    _ = (1 - decay)⁻¹ := ENNReal.tsum_geometric decay

/--
The partial sum of a geometric error sequence is bounded by the total:
  `∑_{k=0}^{N-1} base * decay^k ≤ base * (1 - decay)⁻¹`

This is the key lemma for Theorem 4.1: when per-step errors decay
geometrically, the total error over unboundedly many steps converges.
-/
theorem geometricErrorSeq_partial_sum_le (base decay : ENNReal) (N : ℕ) :
    (Finset.range N).sum (geometricErrorSeq base decay) ≤
      geometricErrorTotal base decay := by
  unfold geometricErrorSeq geometricErrorTotal
  rw [← Finset.mul_sum]
  exact mul_le_mul_right (geom_partial_sum_le decay N) base

/--
Geometric error sequences satisfy the prefix-bound hypothesis needed by
`EventBound.countUnion_of_prefixBounds`.  That is, for all `N`,
  `∑_{k=0}^{N-1} geometricErrorSeq base decay k ≤ geometricErrorTotal base decay`.
-/
theorem geometricErrorSeq_prefixBounds (base decay : ENNReal) :
    ∀ N, (Finset.range N).sum (geometricErrorSeq base decay) ≤
      geometricErrorTotal base decay :=
  fun N => geometricErrorSeq_partial_sum_le base decay N

/--
Given a sequence of `EventBound`s whose bounds follow a geometric error
sequence, produce a single `EventBound` for the countable union with
the geometric series total as its bound.
-/
noncomputable def geometricCountUnion {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (B : ℕ → EventBound P) (base decay : ENNReal)
    (hbounds : ∀ n, (B n).bound ≤ geometricErrorSeq base decay n) :
    EventBound P :=
  EventBound.countUnion_of_prefixBounds hP
    (fun n => (B n).weaken_bound (hbounds n))
    (geometricErrorTotal base decay)
    (fun N => by
      simp only [EventBound.weaken_bound]
      exact geometricErrorSeq_partial_sum_le base decay N)

/--
The bound produced by `geometricCountUnion` is `geometricErrorTotal base decay`.
-/
theorem geometricCountUnion_bound {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (B : ℕ → EventBound P) (base decay : ENNReal)
    (hbounds : ∀ n, (B n).bound ≤ geometricErrorSeq base decay n) :
    (geometricCountUnion hP B base decay hbounds).bound =
      geometricErrorTotal base decay := by
  rfl

/--
Specialization: when `decay < 1` and `base ≠ ⊤`, the total error is finite.
This is what makes the unbounded computation scheme work:
infinite steps, finite total error.
-/
theorem geometricErrorTotal_lt_top {base decay : ENNReal}
    (hbase : base < ⊤) (hdecay : decay < 1) :
    geometricErrorTotal base decay < ⊤ := by
  unfold geometricErrorTotal
  apply ENNReal.mul_lt_top hbase
  rw [ENNReal.inv_lt_top]
  exact pos_iff_ne_zero.mpr (tsub_pos_iff_lt.mpr hdecay |>.ne')

/--
When `decay = 0`, the geometric error total equals `base`.
(Only the zeroth step contributes.)
-/
theorem geometricErrorTotal_decay_zero (base : ENNReal) :
    geometricErrorTotal base 0 = base := by
  simp [geometricErrorTotal]

/--
Connect to `SuccessContract.countAll`: given per-step success contracts with
geometrically decaying error, produce a single success contract for "all steps
succeed" with the geometric series total as error bound.
-/
noncomputable def geometricCountAllSuccess {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (C : ℕ → SuccessContract P) (base decay : ENNReal)
    (hbounds : ∀ n, (C n).error ≤ geometricErrorSeq base decay n) :
    SuccessContract P :=
  SuccessContract.countAll hP C (geometricErrorTotal base decay)
    (fun N => by
      calc (Finset.range N).sum (fun n => (C n).error)
          ≤ (Finset.range N).sum (geometricErrorSeq base decay) :=
            Finset.sum_le_sum (fun n _hn => hbounds n)
        _ ≤ geometricErrorTotal base decay :=
            geometricErrorSeq_partial_sum_le base decay N)

/--
The error bound of the combined success contract is the geometric total.
-/
theorem geometricCountAllSuccess_error {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (C : ℕ → SuccessContract P) (base decay : ENNReal)
    (hbounds : ∀ n, (C n).error ≤ geometricErrorSeq base decay n) :
    (geometricCountAllSuccess hP C base decay hbounds).error =
      geometricErrorTotal base decay := by
  rfl

/--
All-steps-succeed characterization: `omega` satisfies the combined contract
iff every individual step succeeds.
-/
theorem geometricCountAllSuccess_iff {Omega : Type u} {P : ProbSpec Omega}
    (hP : ProbAxioms P)
    (C : ℕ → SuccessContract P) (base decay : ENNReal)
    (hbounds : ∀ n, (C n).error ≤ geometricErrorSeq base decay n)
    (omega : Omega) :
    (geometricCountAllSuccess hP C base decay hbounds).success omega ↔
      ∀ n, (C n).success omega :=
  SuccessContract.countAll_success_iff hP C _ _ omega

end UnboundedError

end Probability

end Ripple.sCRNUniversality
