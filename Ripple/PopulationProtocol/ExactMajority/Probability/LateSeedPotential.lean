-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedPotential.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePotential

/-!
# The N16 cutoff bounds the compiled N17 potential

This is a deterministic bridge to the existing base-128 potential.
It is evaluated at the late seed configuration itself. No estimate across
arbitrary pending initialization is asserted.
-/

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem StageEventSpec

variable {n : ℕ}

/-- If no Main index lies below ell-q, every contributing base-128 weight
is at most 128^q. Summing gives the initial bound used by a later drain. -/
theorem shallowLargePotential_le_of_noIndexBelow
    (ell q : ℕ) (c : InputCfg n) (hcut : noIndexBelow (ell - q) c) :
    LatePotential.shallowLargePotential ell c ≤ c.card * 128 ^ q := by
  classical
  let f : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 → ℕ :=
    fun a => if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic _ j => if j.val < ell then 128 ^ (ell - j.val - 1) else 0
    else 0
  have hbound : ∀ a ∈ c, f a ≤ 128 ^ q := by
    intro a ha
    by_cases hm : a.role = .main
    · cases hb : a.bias with
      | zero => simp [f, hm, hb]
      | dyadic σ j =>
          by_cases hj : j.val < ell
          · have hlo := hcut a ha hm σ j hb
            have hexp : ell - j.val - 1 ≤ q := by omega
            simpa only [f, if_pos hm, hb, if_pos hj] using
              (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 128) hexp)
          · simp [f, hm, hb, hj]
    · simp [f, hm]
  have hsum : ∀ d : InputCfg n, (∀ a ∈ d, f a ≤ 128 ^ q) →
      (d.map f).sum ≤ d.card * 128 ^ q := by
    intro d
    induction d using Multiset.induction_on with
    | empty =>
        intro hd
        simp
    | cons a d ih =>
        intro hd
        have ha := hd a (Multiset.mem_cons_self a d)
        have ht := ih (fun b hb => hd b (Multiset.mem_cons_of_mem hb))
        calc
          ((a ::ₘ d).map f).sum = f a + (d.map f).sum := by simp
          _ ≤ 128 ^ q + d.card * 128 ^ q := Nat.add_le_add ha ht
          _ = (a ::ₘ d).card * 128 ^ q := by
            simp only [Multiset.card_cons, Nat.succ_mul]
            omega
  change (c.map f).sum ≤ c.card * 128 ^ q
  exact hsum c hbound

/-- The literal N16 old-index clause supplies the initial bound for N17's
already implemented potential. -/
theorem LateSeedReadout.largePotential_le
    {init c : InputCfg n} {M ell : ℕ} {σ : Sign}
    (h : LateSeedReadout init M ell σ c) :
    LatePotential.shallowLargePotential ell c ≤
      c.card * 128 ^ terminalCutoff n :=
  shallowLargePotential_le_of_noIndexBelow ell (terminalCutoff n) c h.oldIndexCutoff

theorem LateSeedReadout.largePotential_le_population
    {init c : InputCfg n} {M ell : ℕ} {σ : Sign}
    (h : LateSeedReadout init M ell σ c) (hcard : c.card = n) :
    LatePotential.shallowLargePotential ell c ≤
      n * 128 ^ terminalCutoff n := by
  simpa only [hcard] using h.largePotential_le

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening
