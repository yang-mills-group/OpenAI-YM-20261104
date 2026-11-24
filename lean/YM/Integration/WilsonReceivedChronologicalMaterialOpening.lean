import YM.Integration.WilsonReceivedChronologicalMaterialApertures
import YM.Integration.WilsonNeutralTwoPrintPathSparseRooms
import YM.Integration.WilsonReceivedChronologicalMaterialPaidFaces
/-! One physical-period opening for all held arrays from the original captured source. -/
set_option autoImplicit false
universe u
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMaterialOpening
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical
open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology
open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding
open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series
open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset
open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead
open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)
open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram
open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonIndependentCollarAddressedSource (Submitted)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedCoverGrade (Same)
open WilsonOriginalCensusDatedMaterial (words)
open WilsonVacuumPreResetStationaryChange (fine coarse)

open WilsonIndependentCollarMaterialHearing (Mounted)
open WilsonOriginalCensusFaceSchools (Account)
open WilsonOriginalMixedBlockRows (room)
open WilsonReceivedDepositedOrbitalLedger (book)

open WilsonOriginalCensusPublicationClock WilsonOriginalCensusMaterialPosting
open MintClock VowsR



open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedCanonicalSocketGaussian
open WilsonOriginalCensusFaceSites (port)
open WilsonOriginalOccupiedCorridor (sites)
open WilsonReceivedFixedDigitHistory
open OriginalIssuedMarkedRows
open scoped Classical

open Function Set Filter MeasureTheory Analysis Table Spec Extraction Next.UVStress
open StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open WilsonReceivedChronologicalMaterialSites (physical digits footprint)
open WilsonOriginalOccupiedCorridor (sites)

open WilsonReceivedChronologicalMaterialCapture (placed pinned)
open WilsonOriginalCensusFaceAdmission (housed)

open WilsonReceivedChronologicalMaterialApertures (spread diameter)
open WilsonOriginalCensusDatedPeriodOpening (Opened)
open WilsonOriginalCensusDatedHeldTariff (Rates)
open WilsonOriginalCensusAngularFace (sides)
variable {G:Gauge}{R:Run G}{n:ℕ}{D:Fin n → ℕ}

abbrev price (R:Run G)(grades:Fin n → ℕ)(j p:ℕ):ℝ:=
  WilsonOriginalCensusCanonicalSparseBudget.winding (R.alloy.B.a.clock.hatBeta j) p
    (WilsonOriginalCensusPhysicalLoad.rank (sides grades grades))

theorem original {axis:Axis}{simple:G.Simple}{ε:ℝ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
    {T:Campaign R}{W:Campaign.Pillars R T}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (WilsonOriginalOpticalSchedule.prepared schedule) R T W)
    (grades:Fin n → ℕ)(κ:∀v,Knob (D v))(pt:Fin n → Chamber)(q p:ℕ):
    ∀ᶠ m:ℕ in atTop,∀K:ℕ,let dates:=Finset.Ico m K
    ∃rates:(j:dates) → Rates R grades κ pt j.val K q,
      (∀j:dates,WilsonOriginalCensusFixedBank.Income (k:=grades) R κ pt q j.val) ∧
      ∀(V:Realm G (q+1) Credit.leanC)(gross:dates → ℝ),∀ᶠ per:ℕ in atTop,∀j:dates,
      (∀tape:Digits V.draws (Fin n),
        let y:=homes tape 0 m (j.val-(m+1))
        housed y R j.val per ∧ spread y ≤ diameter V n m (j.val-(m+1))) ∧
      ∀(J:Finset (Fin n))(a:Fin (q+1)),Opened R j.val per (mass grades J+a.val)
        ((rates j).width J a) ((rates j).fare J a) (gross j) (price R grades j.val p):=by
  filter_upwards [WilsonNeutralTwoPrintPathSparseRooms.original paid grades κ pt q] with m dates₀
  intro K dates
  obtain ⟨rates,pledged,offered⟩:=dates₀ K dates fun _ h=>Finset.mem_Ico.mp h
  refine ⟨rates,fun j=>pledged j D rfl κ HEq.rfl,?_⟩
  intro V gross
  have small(j:dates):0<price R grades j.val p:=by
    unfold price WilsonOriginalCensusCanonicalSparseBudget.winding
    have h:0<R.alloy.B.a.clock.hatBeta j.val:=zero_lt_one.trans (R.alloy.B.a.fits.delayed j.val)
    positivity
  filter_upwards [offered (fun j=>diameter V n m (j.val-(m+1))) gross (fun j=>price R grades j.val p) small]
    with per funded
  intro j
  refine ⟨fun tape=>⟨(funded j).1 _ (WilsonReceivedChronologicalMaterialApertures.bounded tape m _),
    WilsonReceivedChronologicalMaterialApertures.bounded tape m _⟩,?_⟩
  intro J a
  exact (funded j).2 D rfl κ HEq.rfl J a

end YM.Integration.WilsonReceivedChronologicalMaterialOpening
end
