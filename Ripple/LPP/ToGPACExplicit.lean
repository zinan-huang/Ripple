import Ripple.LPP.ToGPAC

/-!
# LPP and PLPP exports retaining their source computations

These exports retain the source computation, a modulus for its marked
readout, and a certified computation of dimension exactly `c.n + 1`.
The certificate uses the source's polynomial readout system and the
same modulus clipped at zero.
-/

namespace Ripple

open scoped BigOperators

/-- Huang–Huls (2022), [LPP] Main Theorem, easy direction: the PLPP-to-GPAC
export with its source computation, marked-readout modulus, exact dimension,
polynomial readout system, and clipped modulus retained together. -/
theorem plpp_to_gpac_explicit {ν : ℝ} (h : IsPLPPComputable ν) :
    ∃ (c : PLPPComputation ν) (μ : TimeModulus),
      (∀ r : ℕ, ∀ t : ℝ, t > μ r →
        |∑ k ∈ c.marked, c.comp.sol t k - ν|
          < Real.exp (-(r : ℝ))) ∧
      ∃ btc : CertifiedBoundedTimeComputable (c.n + 1) ν,
        btc.pivp = c.readoutPIVP ∧
        ∀ r : ℕ, btc.modulus r = max 0 (μ r) := by
  obtain ⟨c⟩ := h
  obtain ⟨μ, hμ⟩ := c.exists_modulus
  obtain ⟨btc, hP, hclip⟩ := c.exists_cbtc μ hμ
  exact ⟨c, μ, hμ, btc, hP, hclip⟩

/-- Huang–Huls (2022), [LPP] Main Theorem, easy direction: the LPP-to-GPAC
export retaining the original deterministic source. Its conversion to a PLPP
supplies the polynomial readout system while preserving the number of states,
marked set, and source trajectory. -/
theorem lpp_to_gpac_explicit {ν : ℝ} (h : IsLPPComputable ν) :
    ∃ (c : LPPComputation ν) (μ : TimeModulus),
      (∀ r : ℕ, ∀ t : ℝ, t > μ r →
        |∑ k ∈ c.marked, c.comp.sol t k - ν|
          < Real.exp (-(r : ℝ))) ∧
      ∃ btc : CertifiedBoundedTimeComputable (c.n + 1) ν,
        btc.pivp = c.toPLPPComputation.readoutPIVP ∧
        ∀ r : ℕ, btc.modulus r = max 0 (μ r) := by
  obtain ⟨c⟩ := h
  obtain ⟨μ, hμ⟩ := c.toPLPPComputation.exists_modulus
  obtain ⟨btc, hP, hclip⟩ :=
    c.toPLPPComputation.exists_cbtc μ hμ
  exact ⟨c, μ, hμ, btc, hP, hclip⟩

end Ripple
