import Ripple.BoundedUniversality.BGP.ContractTracking

-- Migrated from (1, 3/8) to (1000, 300) for cold-cycle tube closure.

/-!
Ripple.BoundedUniversality.BGP.BGPParamsBase
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
def bgpParamsBase : DynGateParams where
  A := 1; L := 1; cμ := 1000; cα := (300 : ℝ)

theorem bgpParamsBase_cα_rat : bgpParamsBase.cα = ((300 : ℚ) : ℝ) := by
  norm_num [bgpParamsBase]

/-- χ leak regime stays strict: `1000/2 - 300 = 200`. -/
theorem bgpParamsBase_chi_regime :
    0 < bgpParamsBase.cμ * (1 / 2 : ℝ) ^ bgpParamsBase.L - bgpParamsBase.cα := by
  norm_num [bgpParamsBase]

/-- κ cascade stays strict: `300 - 1000/4 = 50`. -/
theorem bgpParamsBase_kappa_growth_regime :
    0 < bgpParamsBase.cα - bgpParamsBase.cμ * (1 / 4 : ℝ) ^ bgpParamsBase.L := by
  norm_num [bgpParamsBase]

/-- The old checked-in value is exactly the κ equality wall. -/
theorem bgpParams14_kappa_growth_eq_zero :
    bgpParams14.cα - bgpParams14.cμ * (1 / 4 : ℝ) ^ bgpParams14.L = 0 := by
  norm_num [bgpParams14]

end Ripple.BoundedUniversality.BGP
