import Ripple.sCRNUniversality.Core.Petri
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseBimolecularRefinement
import Ripple.sCRNUniversality.Stochastic.MassActionBridge
import Ripple.sCRNUniversality.Stochastic.MassAction.RaceLaw
import Ripple.sCRNUniversality.Stochastic.MassAction.UniformRaceBound

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

/-! ### Stochastic Correctness (Theorem 3.2, stochastic part)

The stochastic correctness of the SCWB construction follows from two facts:
1. The cascade shift is fully deterministic (no propensity race)
2. The clock module bounds the per-microstep error

**Proved chain (in `SCWB/Stochastic/`):**

1. `Propensity.lean`: mass-action propensity computation, totalPropensity
2. `CRNtoQMatrix.lean`: `clockError_from_propensity_dominance` — if the
   non-intended propensity is at most ε · total, then P(wrong) ≤ ε
3. `MassActionBridge.lean`: `ClockBoundedLaw.ofMassAction` — constructs
   a `ClockBoundedLaw` from any `MassActionRaceLaw` + propensity bound;
   `stochastic_error_le_of_propensity_dominance` — full error bound
4. `ClockErrorModel.lean`: `error_le_target` — if ε ≤ δ/(4n), total ≤ δ
5. `ClockBoundedLawInstance.lean`: `error_le_inv_pow` — geometric sum → 1/#A^(l-1)
6. `ClockCRN.lean`: concrete clock CRN with catalyst/C-count preservation
7. `GamblersRuin.lean`: clock tick rate ≤ 1/#A^(l-1)

**Probability space construction (in `SCWB/Stochastic/MassAction/`):**

8. `Weights.lean`: `massActionPMF` on `Option N.I` from propensity/jumpProbAt
9. `Traj.lean`: `stepKernel` + `rawLaw` via Mathlib's Ionescu-Tulcea (`Kernel.trajFun`)
10. `RaceLaw.lean`: `massActionRaceLaw` — unconditional construction of
    the canonical probability space for CRN mass-action kinetics

The `MassActionRaceLaw` is now constructed (not assumed). The construction
uses Mathlib's formalized Ionescu-Tulcea theorem (`Kernel.trajFun`) to
build the path-space probability measure from the mass-action step kernels.

**Non-vacuous multi-step stochastic bound:**

11. `MassAction/UniformRaceBound.lean`:
    - `rawLaw_coord_uniform_bound` — at any time step, if the PMF complement
      is ≤ ε at ALL states (not just one deterministic state), then the
      rawLaw measure of the bad-reaction event is ≤ ε. Uses Ionescu-Tulcea
      marginal + lintegral_mono. NO `hstate` (deterministic state) hypothesis.
    - `rawLaw_multistep_uniform_bound` — n-step union bound: if ∀ k, ∀ z,
      the PMF complement for `schedule(k)` is ≤ ε at every state z, then
      P(any step fires wrong) ≤ n × ε.

    This is the correct multi-step bound for combined comp+clock CRNs
    where multiple reactions are enabled. The hypothesis `hUniform` is
    satisfiable when computation and clock species are disjoint and the
    clock propensity is bounded at all reachable states.

12. `PropensityDominance.lean`: sigma-composed CRN propensity dominance.

The deterministic component (CTM `n` steps → CRN.Reaches) is fully
proved above via `statePairTransfer_crn_reaches_of_ctm_steps`.

**Remaining concrete instantiation**: for the specific SCWB four-phase
+ clock CRN, show `hUniform` holds by:
- Quasi-determinism: only one computation reaction enabled at each phase
- Disjoint species: clock reactions don't affect computation propensity
- Clock propensity bound: `GamblersRuin` + `ClockBoundedLawInstance`
-/

end PaperTheorems

end Ripple.sCRNUniversality
