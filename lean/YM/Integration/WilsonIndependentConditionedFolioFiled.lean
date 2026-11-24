import YM.Integration.WilsonOriginalReflectedFiledFolio
import YM.Integration.WilsonIndependentConditionedFolioScalar

/-! All registered nonempty reflected faces at their actual chosen physical sites. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioFiled
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators
open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics
open WilsonVacuumPreResetStationaryChange (step coarse levels)
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonOriginalRawQReversion (coordinates)
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded)
open WilsonReceivedDepositedOrbitalIssuedFilter (share)
open WilsonNeutralSignedPolynomialRate (read)
open FVA1Physical.TwoReset WilsonCoeffUV.Winding Further.PhysicalPeriodLimitF933 Macrame
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider.Canvas FreeResolvent
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Pressure Precision Tree Exterior PertExtension PertExtension.Series WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open scoped Topology ContDiff Matrix.Norms.Frobenius
open Source Labels
open WilsonOriginalFullRosterCouplingClock (work)
open WilsonReceivedChronologicalPanelClock (fare)
open WilsonOriginalOccupiedCorridor (sites)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonOriginalCensusPhysicalAttendance (roots tab Room)
open WilsonReceivedChronologicalPanelClock (debitDepth fare)
open WilsonOriginalOccupiedWindow WilsonOriginalOccupiedCorridor WilsonOriginalJointTrialHearing
open WilsonOriginalCensusPhysicalAttendance (Room roots tab)
open WilsonOriginalCensusFundedAttendance (Demand)
open WilsonReceivedChronologicalFixedLedger (Registered)
open WilsonReceivedChronologicalFixedEarner (programme)
open WilsonReceivedChronologicalFixedReserve (terms)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonOriginalCensusAttendanceStation
open AllOrder AllOrder.Floe
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonOriginalCensusCanonicalAngularMenu (repeated plottedLow)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonOriginalCensusFaceSites (binder port)
open WilsonOriginalCensusFaceSheet (Addressed)
open FundedMarkedPathSelection (output)
open WilsonReceivedFixedDigitCanonical (fixed)
open Comparison.Density.Transport
open WilsonOriginalCensusCanonicalFirstEdgePayer (Source)
open WilsonReceivedChronologicalFixedPlaced (Purchased)
open WilsonReceivedChronologicalFixedSocketLife
open WilsonReceivedChronologicalFixedCellFee
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalSocket (input)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedChronologicalFixedRoster
open WilsonReceivedChronologicalMaterialLine (homes)
open Function Set Filter MeasureTheory Analysis Table Spec Extraction Next.UVStress
open WilsonReceivedChronologicalMaterialSites
open StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open RG16 RG16.Literal
open Extra.Histories Extra.Trajectories Extra.Multi
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonMeasuredPublicEntranceCellWords (physical)
open WilsonMeasuredPublicEntrancePanel (Reading)
open Extra.Trajectories Extra.Multi
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open WilsonOriginalTwoFlatIRSocketPower (debt)
open WilsonReceivedChronologicalFixedRoseFittedDebit (written)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonOriginalReflectedFiledCells (entry)
open WilsonReceivedChronologicalFixedRoseFittedDebit (Plan written)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonOriginalReflectedFiledField (path location)
variable {G:Gauge}(R:Run G)(d D:Fin 2 → ℕ)(pt:Fin 2 → Chamber)(φ:Test 2)(r:ℝ)
  {K N per u f c v requested tag top:ℕ}(uk:u ≤ K)(fK:f ≤ K)(kn:K ≤ N)
  (plan:Plan 2)(file:Filed R d K)
  (panel:cells R φ r (f,per) → Panel R d N per f K fK kn requested plan.pole tag plan.tuition)
  {X:Realm G (top+1) Credit.leanC}(draw:X.draws=R.family.path.levels)

open WilsonOriginalPublicNodalTestedFunctional (deposit)
open WilsonIndependentConditionedFolioWeights (payment)
open WilsonOlderFreshHybridClock (flat)
local notation "κ_" => (fun i=>contact (D i))
local notation "tape_" y:max => path (R:=R) draw fK (y).val
local notation "w_" y:max => votes R d (N:=N) (per:=per) file (panel y).names (panel y).turn
local notation "x_" => Pert.Asymptotics.regulatorRun R.family N per v

theorem original (W:Initialize G)(fit:∀i,d i<D i)(first q:ℕ)(y:cells R φ r (f,per))(S:Finset (Fin 2))[Nonempty S]
    (simple:G.Simple)(ratio:LocalRatio R.metals.O)(vc:v≤c)(ck:c≤K):
    WilsonOriginalReflectedFiledFolio.independent R d D pt φ r (v:=v) (c:=c) fK kn plan file panel draw first q y S=
      ∑b:(i:S)→(R.family.labels.level (d i)).Index,payment R d N per K (w_ y) S b*
      ((touch (present D) S (deposit D κ_ pt S)*flat
        (WilsonIndependentConditionedFolioScalar.column R W d fit N K c v (tape_ y)
          (location (R:=R) draw fK y.val c first) S b) q x_:ℝ):ℂ):=by
  exact WilsonIndependentConditionedFolioScalar.original R W D d fit κ_ pt N per K c v (tape_ y)
    (location (R:=R) draw fK y.val c first) S (touch (present D) S) (w_ y) simple ratio vc ck kn q x_

end YM.Integration.WilsonIndependentConditionedFolioFiled
end
