import Ripple.sCRNUniversality.Core.Petri
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseBimolecularRefinement
import Ripple.sCRNUniversality.Stochastic.MassActionBridge
import Ripple.sCRNUniversality.Stochastic.MassAction.RaceLaw
import Ripple.sCRNUniversality.Stochastic.MassAction.UniformRaceBound
import Ripple.sCRNUniversality.Stochastic.ReachablePropensityDischarge

namespace Ripple.sCRNUniversality

namespace PaperTheorems

universe u v

/-!
Paper-facing wrappers for facts already proved in the core development.

Note: `Decidable (P.CoverableFrom z0 target)` is proved in
`SCWB/Decidability/Coverability.lean` via backward coverability saturation +
WQO termination (Dickson's lemma). The instance is `noncomputable` because the
fuel bound comes from an existence proof; it does not extract to executable code.
The backward algorithm itself (saturation loop, closure check, predecessor
computation) is fully formalized.
-/

variable {S : Type u}

theorem crn_reaches_iff_petri_reaches
    (N : Network S) (z z' : State S) :
    N.Reaches z z' <-> (N.toPetri).Reaches z z' := by
  exact (Network.toPetri_reaches_iff N z z').symm

theorem crn_coverability_iff_petri_coverability
    (N : Network S) (z0 target : State S) :
    N.CoverableFrom z0 target <-> (N.toPetri).CoverableFrom z0 target := by
  exact (Network.toPetri_coverable_iff N z0 target).symm

theorem exists_atMostBimolecularInput_positiveRates_petri_reaches_of_crn_reaches
    {S : Type u} [Fintype S]
    {z0 z1 : State S}
    (h :
      exists N : Network.{u, v} S,
        N.allAtMostBimolecularInput /\
          N.hasPositiveRates /\
            N.Reaches z0 z1) :
    exists N : Network.{u, v} S,
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          (N.toPetri).Reaches z0 z1 := by
  rcases h with ⟨N, hArity, hRates, hReach⟩
  exact ⟨N, hArity, hRates,
    (Network.toPetri_reaches_iff N z0 z1).mpr hReach⟩

theorem exists_atMostBimolecularInput_positiveRates_petri_speciesCoverableFrom_of_crn
    {S : Type u} [Fintype S] [DecidableEq S]
    {z0 : State S} {species : S} {amount : Nat}
    (h :
      exists N : Network.{u, v} S,
        N.allAtMostBimolecularInput /\
          N.hasPositiveRates /\
            N.SpeciesCoverableFrom z0 species amount) :
    exists N : Network.{u, v} S,
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          (N.toPetri).SpeciesCoverableFrom z0 species amount := by
  rcases h with ⟨N, hArity, hRates, hCover⟩
  exact ⟨N, hArity, hRates,
    Network.toPetri_speciesCoverableFrom N hCover⟩

theorem exists_atMostBimolecularInput_positiveRates_petri_coverableFrom_of_crn
    {S : Type u} [Fintype S]
    {z0 target : State S}
    (h :
      exists N : Network.{u, v} S,
        N.allAtMostBimolecularInput /\
          N.hasPositiveRates /\
            N.CoverableFrom z0 target) :
    exists N : Network.{u, v} S,
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          (N.toPetri).CoverableFrom z0 target := by
  rcases h with ⟨N, hArity, hRates, hCover⟩
  exact ⟨N, hArity, hRates,
    (Network.toPetri_coverable_iff N z0 target).mpr hCover⟩

theorem exists_allAtMostBimolecularFull_allUnitRate_petri_reaches_of_crn_reaches
    {S : Type u} [Fintype S]
    {z0 z1 : State S}
    (h :
      exists N : Network.{u, v} S,
        N.allAtMostBimolecularFull /\
          N.allUnitRate /\
            N.Reaches z0 z1) :
    exists N : Network.{u, v} S,
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          (N.toPetri).Reaches z0 z1 := by
  rcases h with ⟨N, hArity, hRates, hReach⟩
  exact ⟨N, hArity, hRates,
    (Network.toPetri_reaches_iff N z0 z1).mpr hReach⟩

theorem exists_allAtMostBimolecularFull_allUnitRate_petri_speciesCoverableFrom_of_crn
    {S : Type u} [Fintype S] [DecidableEq S]
    {z0 : State S} {species : S} {amount : Nat}
    (h :
      exists N : Network.{u, v} S,
        N.allAtMostBimolecularFull /\
          N.allUnitRate /\
            N.SpeciesCoverableFrom z0 species amount) :
    exists N : Network.{u, v} S,
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          (N.toPetri).SpeciesCoverableFrom z0 species amount := by
  rcases h with ⟨N, hArity, hRates, hCover⟩
  exact ⟨N, hArity, hRates,
    Network.toPetri_speciesCoverableFrom N hCover⟩

theorem exists_allAtMostBimolecularFull_allUnitRate_petri_coverableFrom_of_crn
    {S : Type u} [Fintype S]
    {z0 target : State S}
    (h :
      exists N : Network.{u, v} S,
        N.allAtMostBimolecularFull /\
          N.allUnitRate /\
            N.CoverableFrom z0 target) :
    exists N : Network.{u, v} S,
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          (N.toPetri).CoverableFrom z0 target := by
  rcases h with ⟨N, hArity, hRates, hCover⟩
  exact ⟨N, hArity, hRates,
    (Network.toPetri_coverable_iff N z0 target).mpr hCover⟩

theorem statePairTransfer_crn_allAtMostBimolecularInput
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : CTM.Binary Q) :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).allAtMostBimolecularInput :=
  CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork_allAtMostBimolecularInput
    (s := s) M

theorem statePairTransfer_crn_allAtMostBimolecularOutput
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : CTM.Binary Q) :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).allAtMostBimolecularOutput :=
  CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork_allAtMostBimolecularOutput
    (s := s) M

theorem statePairTransfer_crn_allAtMostBimolecularFull
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : CTM.Binary Q) :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).allAtMostBimolecularFull :=
  CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork_allAtMostBimolecularFull
    (s := s) M

theorem statePairTransfer_crn_hasPositiveRates
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : CTM.Binary Q) :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).hasPositiveRates :=
  CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork_hasPositiveRates
    (s := s) M

theorem statePairTransfer_crn_allUnitRate
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : CTM.Binary Q) :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).allUnitRate :=
  CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork_allUnitRate
    (s := s) M

theorem statePairTransfer_crn_equalRates
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s : Nat} (M : CTM.Binary Q) :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).equalRates :=
  CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork_equalRates
    (s := s) M

theorem statePairTransfer_crn_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).Reaches
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg')) :=
  CTM.BimolecularFourPhaseRefinement.statePairTransfer_reaches_of_ctm_steps
    (s := s) M h

theorem statePairTransfer_crn_coverableFrom_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg'))
        target) :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).CoverableFrom
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
      target :=
  CTM.BimolecularFourPhaseRefinement.statePairTransfer_coverableFrom_of_ctm_steps_covers
    (s := s) M h hCovers

theorem statePairTransfer_crn_coverableFrom_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg') species) :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).CoverableFrom
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
      target :=
  statePairTransfer_crn_coverableFrom_of_ctm_steps_covers
    (s := s) M h hTarget

theorem statePairTransfer_crn_tape_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).SpeciesCoverableFrom
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
      CTM.FourPhaseSpecies.tape
      (Encoding.base3Val cfg'.tape) :=
  CTM.BimolecularFourPhaseRefinement.statePairTransfer_tape_speciesCoverableFrom_of_ctm_steps
    (s := s) M h

theorem exists_atMostBimolecularInput_positiveRates_crn_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          N.Reaches
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg')) := by
  exact
    ⟨CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M,
      statePairTransfer_crn_allAtMostBimolecularInput (s := s) M,
      statePairTransfer_crn_hasPositiveRates (s := s) M,
      statePairTransfer_crn_reaches_of_ctm_steps (s := s) M h⟩

theorem exists_atMostBimolecularInput_positiveRates_crn_coverableFrom_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg'))
        target) :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          N.CoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            target := by
  exact
    ⟨CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M,
      statePairTransfer_crn_allAtMostBimolecularInput (s := s) M,
      statePairTransfer_crn_hasPositiveRates (s := s) M,
      statePairTransfer_crn_coverableFrom_of_ctm_steps_covers
        (s := s) M h hCovers⟩

theorem exists_atMostBimolecularInput_positiveRates_crn_coverableFrom_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg') species) :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          N.CoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            target :=
  exists_atMostBimolecularInput_positiveRates_crn_coverableFrom_of_ctm_steps_covers
    (s := s) M h hTarget

theorem exists_atMostBimolecularInput_positiveRates_crn_tape_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          N.SpeciesCoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            CTM.FourPhaseSpecies.tape
            (Encoding.base3Val cfg'.tape) := by
  exact
    ⟨CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M,
      statePairTransfer_crn_allAtMostBimolecularInput (s := s) M,
      statePairTransfer_crn_hasPositiveRates (s := s) M,
      statePairTransfer_crn_tape_speciesCoverableFrom_of_ctm_steps
        (s := s) M h⟩

theorem exists_allAtMostBimolecularFull_allUnitRate_crn_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          N.Reaches
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg')) := by
  exact
    ⟨CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M,
      statePairTransfer_crn_allAtMostBimolecularFull (s := s) M,
      statePairTransfer_crn_allUnitRate (s := s) M,
      statePairTransfer_crn_reaches_of_ctm_steps (s := s) M h⟩

theorem exists_allAtMostBimolecularFull_allUnitRate_crn_coverableFrom_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg'))
        target) :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          N.CoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            target := by
  exact
    ⟨CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M,
      statePairTransfer_crn_allAtMostBimolecularFull (s := s) M,
      statePairTransfer_crn_allUnitRate (s := s) M,
      statePairTransfer_crn_coverableFrom_of_ctm_steps_covers
        (s := s) M h hCovers⟩

theorem exists_allAtMostBimolecularFull_allUnitRate_crn_coverableFrom_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg') species) :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          N.CoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            target :=
  exists_allAtMostBimolecularFull_allUnitRate_crn_coverableFrom_of_ctm_steps_covers
    (s := s) M h hTarget

theorem exists_allAtMostBimolecularFull_allUnitRate_crn_tape_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          N.SpeciesCoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            CTM.FourPhaseSpecies.tape
            (Encoding.base3Val cfg'.tape) := by
  exact
    ⟨CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M,
      statePairTransfer_crn_allAtMostBimolecularFull (s := s) M,
      statePairTransfer_crn_allUnitRate (s := s) M,
      statePairTransfer_crn_tape_speciesCoverableFrom_of_ctm_steps
        (s := s) M h⟩

theorem statePairTransfer_petri_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    ((CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).toPetri).Reaches
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg')) :=
  (Network.toPetri_reaches_iff
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M)
    (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
    (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg'))).mpr
      (statePairTransfer_crn_reaches_of_ctm_steps (s := s) M h)

theorem statePairTransfer_petri_tape_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    ((CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).toPetri).SpeciesCoverableFrom
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
      CTM.FourPhaseSpecies.tape
      (Encoding.base3Val cfg'.tape) :=
  Network.toPetri_speciesCoverableFrom
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M)
    (statePairTransfer_crn_tape_speciesCoverableFrom_of_ctm_steps
      (s := s) M h)

theorem statePairTransfer_petri_coverableFrom_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg'))
        target) :
    ((CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).toPetri).CoverableFrom
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
      target :=
  (Network.toPetri_coverable_iff
    (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M)
    (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
    target).mpr
      (statePairTransfer_crn_coverableFrom_of_ctm_steps_covers
        (s := s) M h hCovers)

theorem statePairTransfer_petri_coverableFrom_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg') species) :
    ((CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
      (s := s) M).toPetri).CoverableFrom
      (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
      target :=
  statePairTransfer_petri_coverableFrom_of_ctm_steps_covers
    (s := s) M h hTarget

theorem exists_atMostBimolecularInput_positiveRates_petri_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          (N.toPetri).Reaches
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg')) := by
  exact
    exists_atMostBimolecularInput_positiveRates_petri_reaches_of_crn_reaches
      (exists_atMostBimolecularInput_positiveRates_crn_reaches_of_ctm_steps
        (s := s) M h)

theorem exists_atMostBimolecularInput_positiveRates_petri_coverableFrom_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg'))
        target) :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          (N.toPetri).CoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            target := by
  exact
    exists_atMostBimolecularInput_positiveRates_petri_coverableFrom_of_crn
      (exists_atMostBimolecularInput_positiveRates_crn_coverableFrom_of_ctm_steps_covers
        (s := s) M h hCovers)

theorem exists_atMostBimolecularInput_positiveRates_petri_coverableFrom_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg') species) :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          (N.toPetri).CoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            target :=
  exists_atMostBimolecularInput_positiveRates_petri_coverableFrom_of_ctm_steps_covers
    (s := s) M h hTarget

theorem exists_atMostBimolecularInput_positiveRates_petri_tape_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularInput /\
        N.hasPositiveRates /\
          (N.toPetri).SpeciesCoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            CTM.FourPhaseSpecies.tape
            (Encoding.base3Val cfg'.tape) := by
  exact
    exists_atMostBimolecularInput_positiveRates_petri_speciesCoverableFrom_of_crn
      (exists_atMostBimolecularInput_positiveRates_crn_tape_speciesCoverableFrom_of_ctm_steps
        (s := s) M h)

theorem exists_allAtMostBimolecularFull_allUnitRate_petri_reaches_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          (N.toPetri).Reaches
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg')) := by
  exact
    exists_allAtMostBimolecularFull_allUnitRate_petri_reaches_of_crn_reaches
      (exists_allAtMostBimolecularFull_allUnitRate_crn_reaches_of_ctm_steps
        (s := s) M h)

theorem exists_allAtMostBimolecularFull_allUnitRate_petri_coverableFrom_of_ctm_steps_covers
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hCovers :
      Covers
        (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg'))
        target) :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          (N.toPetri).CoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            target := by
  exact
    exists_allAtMostBimolecularFull_allUnitRate_petri_coverableFrom_of_crn
      (exists_allAtMostBimolecularFull_allUnitRate_crn_coverableFrom_of_ctm_steps_covers
        (s := s) M h hCovers)

theorem exists_allAtMostBimolecularFull_allUnitRate_petri_coverableFrom_of_ctm_steps_of_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    {target : State (CTM.FourPhaseEncoding.Species Q)}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg')
    (hTarget :
      forall species,
        target species <=
          CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg') species) :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          (N.toPetri).CoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            target :=
  exists_allAtMostBimolecularFull_allUnitRate_petri_coverableFrom_of_ctm_steps_covers
    (s := s) M h hTarget

theorem exists_allAtMostBimolecularFull_allUnitRate_petri_tape_speciesCoverableFrom_of_ctm_steps
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {s n : Nat} (M : CTM.Binary Q)
    {cfg cfg' : CTM.Cfg Q Bool s}
    (h : (M.detSystem (s := s)).steps? n cfg = some cfg') :
    exists N : Network.{u, u} (CTM.FourPhaseEncoding.Species Q),
      N.allAtMostBimolecularFull /\
        N.allUnitRate /\
          (N.toPetri).SpeciesCoverableFrom
            (CTM.FourPhaseEncoding.enc (CTM.MicroCfg.ofCTM cfg))
            CTM.FourPhaseSpecies.tape
            (Encoding.base3Val cfg'.tape) := by
  exact
    exists_allAtMostBimolecularFull_allUnitRate_petri_speciesCoverableFrom_of_crn
      (exists_allAtMostBimolecularFull_allUnitRate_crn_tape_speciesCoverableFrom_of_ctm_steps
        (s := s) M h)

/-! ### Stochastic Correctness

**Probability space (in `Stochastic/MassAction/`):**

- `Weights.lean`: `massActionPMF` from propensity / jumpProbAt
- `Traj.lean`: `stepKernel` + `rawLaw` via Mathlib's Ionescu-Tulcea
- `RaceLaw.lean`: `massActionRaceLaw` — unconditional construction of
  the canonical probability space for CRN mass-action kinetics

**Multi-step stochastic bound (in `Stochastic/`):**

- `MassAction/UniformRaceBound.lean`:
  `rawLaw_multistep_uniform_bound_reachable` — n-step union bound:
  P(any step fires wrong) ≤ n × ε, quantified over all reachable prefix states
- `ReachablePropensityDominance.lean`:
  zero-propensity route — wrong-source reactions have a missing reactant,
  hence zero propensity; reduces the bound to hEnabled + hClock
- `ReachablePropensityDischarge.lean`:
  control P-invariant → unique active control at reachable states →
  wrong-source propensity = 0 (discharged); clock ratio trivially ≤ 1

**Two stochastic bounds are proved:**

1. `scwb_rawLaw_concrete_bound` — unconditional (ε = 1, vacuous but clean-3)
2. `scwb_rawLaw_conditional_bound` — conditional on `hEnabled` (schedule
   enabledness at reachable prefix states) and `hClock` (clock propensity
   ratio). The zero-propensity condition is discharged internally from the
   control P-invariant. Any ε < 1 yields a non-vacuous bound.

The sole remaining mathematical gap is `hEnabled`: proving that the scheduled
reaction is enabled at every reachable prefix state, including states reached
after a clock (same-source) reaction fires.
-/

open Classical in
theorem scwb_stochastic_bound_unconditional
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : CTM.Binary Q) (cfg₀ : CTM.MicroCfg Q s)
    (n : Nat)
    (schedule : Fin n →
      (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I) :
    (Stochastic.MassAction.rawLaw
      (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork (s := s) M)
      (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork_hasPositiveRates
        (s := s) M)
      (CTM.FourPhaseEncoding.enc cfg₀))
      (⋃ k : Fin n,
        {ω | ω (k.val + 1) ≠ some (schedule k)}) ≤
      n * ENNReal.ofReal
        (Stochastic.statePairTransferEpsilonBound : Rat) :=
  Stochastic.scwb_rawLaw_concrete_bound M cfg₀ n schedule

open Classical in
theorem scwb_stochastic_bound_conditional
    {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}
    (M : CTM.Binary Q) (cfg₀ : CTM.MicroCfg Q s)
    (n : Nat)
    (schedule : Fin n →
      (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).I)
    (ε : NNRat)
    (hEnabled : ∀ k : Fin n,
      ∀ z : State (CTM.FourPhaseEncoding.Species Q),
      z ∈ Set.range (Stochastic.MassAction.prefixToState
        (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork (s := s) M)
        (CTM.FourPhaseEncoding.enc cfg₀) k.val) →
      (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
        (s := s) M).EnabledAt z (schedule k))
    (hClock : ∀ k : Fin n,
      ∀ z : State (CTM.FourPhaseEncoding.Species Q),
      z ∈ Set.range (Stochastic.MassAction.prefixToState
        (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork (s := s) M)
        (CTM.FourPhaseEncoding.enc cfg₀) k.val) →
      (Finset.univ.filter (Stochastic.scheduleSourceClock M schedule)).sum
          (fun j =>
            ((CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
              (s := s) M).rxn j).propensity z) ≤
        ε * (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork
          (s := s) M).totalPropensity z) :
    (Stochastic.MassAction.rawLaw
      (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork (s := s) M)
      (CTM.BimolecularFourPhaseRefinement.statePairTransferNetwork_hasPositiveRates
        (s := s) M)
      (CTM.FourPhaseEncoding.enc cfg₀))
      (⋃ k : Fin n,
        {ω | ω (k.val + 1) ≠ some (schedule k)}) ≤
      n * ENNReal.ofReal (ε : Rat) :=
  Stochastic.scwb_rawLaw_conditional_bound M cfg₀ n schedule ε
    hEnabled hClock

end PaperTheorems

end Ripple.sCRNUniversality

#check Ripple.sCRNUniversality.PaperTheorems.scwb_stochastic_bound_unconditional
#check Ripple.sCRNUniversality.PaperTheorems.scwb_stochastic_bound_conditional
#print axioms Ripple.sCRNUniversality.PaperTheorems.scwb_stochastic_bound_unconditional
#print axioms Ripple.sCRNUniversality.PaperTheorems.scwb_stochastic_bound_conditional
