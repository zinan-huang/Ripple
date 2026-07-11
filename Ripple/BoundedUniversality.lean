-- Ripple.BoundedUniversality: Q-rational compact polynomial ODE Turing universality
-- Root module importing all submodules.

import Ripple.BoundedUniversality.Core.Computability
import Ripple.BoundedUniversality.Core.CoeffField

import Ripple.BoundedUniversality.HenonSelector.Henon
import Ripple.BoundedUniversality.HenonSelector.QSemialg
import Ripple.BoundedUniversality.HenonSelector.Markov
import Ripple.BoundedUniversality.HenonSelector.Itinerary
import Ripple.BoundedUniversality.HenonSelector.Cylinder
import Ripple.BoundedUniversality.HenonSelector.Periodic
import Ripple.BoundedUniversality.HenonSelector.Selector
import Ripple.BoundedUniversality.HenonSelector.NoGo
import Ripple.BoundedUniversality.HenonSelector.SelectorConsequences
import Ripple.BoundedUniversality.HenonSelector.RotationCounterexample

import Ripple.BoundedUniversality.GPAC.PIVP
import Ripple.BoundedUniversality.GPAC.Readout
import Ripple.BoundedUniversality.GPAC.Clock
import Ripple.BoundedUniversality.GPAC.BGP
import Ripple.BoundedUniversality.GPAC.BoundedSurrogate
import Ripple.BoundedUniversality.GPAC.Combined
import Ripple.BoundedUniversality.GPAC.RationalReduction
import Ripple.BoundedUniversality.GPAC.SurrogateCompile
import Ripple.BoundedUniversality.GPAC.StrongSemantics
import Ripple.BoundedUniversality.GPAC.TimeChange
import Ripple.BoundedUniversality.GPAC.CompileBridge
import Ripple.BoundedUniversality.GPAC.ReadoutPreserve
import Ripple.BoundedUniversality.GPAC.TimeChangeConstruct
import Ripple.BoundedUniversality.GPAC.Assembly
import Ripple.BoundedUniversality.GPAC.ExplicitCompile

import Ripple.BoundedUniversality.Routes
import Ripple.BoundedUniversality.Assumptions
import Ripple.BoundedUniversality.Verified
