import Ripple.BoundedUniversality.BGP.ContractTracking

-- Migrated from (1, 3/8) to (1000, 300) for cold-cycle tube closure.

/-!
Ripple.BoundedUniversality.BGP.BGPParams38
----------------------
Shared strict-cascade clock parameters.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

/-! ## Cold-cycle strict-cascade regime -/

/-- Old equality-wall parameters, isolated for comparison. -/
def bgpParams14 : DynGateParams where
  A := 1; L := 1; cμ := 1; cα := (1 : ℝ) / 4

/-- Strict-cascade parameters. -/
def bgpParams38 : DynGateParams where
  A := 1; L := 1; cμ := 1000; cα := (300 : ℝ)

theorem bgpParams38_cα_rat : bgpParams38.cα = ((300 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

/-- χ leak regime stays strict: `1000/2 - 300 = 200`. -/
theorem bgpParams38_chi_regime :
    0 < bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα := by
  norm_num [bgpParams38]

/-- κ cascade stays strict: `300 - 1000/4 = 50`. -/
theorem bgpParams38_kappa_growth_regime :
    0 < bgpParams38.cα - bgpParams38.cμ * (1 / 4 : ℝ) ^ bgpParams38.L := by
  norm_num [bgpParams38]

/-- The old checked-in value is exactly the κ equality wall. -/
theorem bgpParams14_kappa_growth_eq_zero :
    bgpParams14.cα - bgpParams14.cμ * (1 / 4 : ℝ) ^ bgpParams14.L = 0 := by
  norm_num [bgpParams14]

end Ripple.BoundedUniversality.BGP
