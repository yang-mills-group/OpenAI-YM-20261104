import YM.Integration.WilsonReceivedChronologicalMaterialLine
import YM.Integration.WilsonIndependentCollarOrbitalReception
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstExtent
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


open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance

open WilsonNeutralTwoPrintPathBoxHome (breadth radius)
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonReceivedChronologicalMaterialLine (homes)
variable {G:Gauge}{n q:ℕ}
def locations (L:Levels G)(ground:Fin n → Cover)(m:ℕ):ℕ → Finset (Fin n → Cover)
  | 0=>{ground}
  | a+1=>(locations L ground m a).biUnion fun y=>
      Finset.univ.image (fun b:Fin n → Site (loose L (m+a+1)).L=>chartIn (loose L (m+a+1)) y b)

theorem contains {V:Realm G (q+1) Credit.leanC}(cells:Digits V.draws (Fin n))
    (ground:Fin n → Cover)(m a:ℕ):
    WilsonReceivedChronologicalMaterialLine.homes cells ground m a ∈ locations V.draws ground m a:=by
  induction a with
  | zero=>simp [locations,WilsonReceivedChronologicalMaterialLine.homes]
  | succ a ih=>
    exact Finset.mem_biUnion.mpr ⟨_,ih,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩

def extent (L:Levels G)(ground:Fin n → Cover)(m a:ℕ):ℕ:=
  (locations L ground m a).sup fun y=>Finset.univ.sup fun i:Fin n=>
    Finset.univ.sup fun j:Fin n=>WilsonNeutralTwoPrintPathBoxHome.radius (y i-y j)

theorem original {V:Realm G (q+1) Credit.leanC}(cells:Digits V.draws (Fin n))
    (ground:Fin n → Cover)(m a:ℕ)(S:Finset (Fin n))(o:Fin n):
    WilsonNeutralTwoPrintPathBoxHome.breadth S o 0 (WilsonIndependentCollarOrbitalReception.relative S o (WilsonReceivedChronologicalMaterialLine.homes cells ground m a))≤extent V.draws ground m a:=by
  let y:=WilsonReceivedChronologicalMaterialLine.homes cells ground m a
  apply max_le
  · change Finset.univ.sup (fun j:Axis=>((0:Cover) j).natAbs)≤_
    exact Finset.sup_le (fun i _=>by simp)
  · apply Finset.sup_le
    intro i _
    have h₁:=Finset.le_sup (s:=Finset.univ) (f:=fun j:Fin n=>WilsonNeutralTwoPrintPathBoxHome.radius (y i.val-y j)) (Finset.mem_univ o)
    have h₂:=Finset.le_sup (s:=Finset.univ)
      (f:=fun k:Fin n=>Finset.univ.sup (fun j:Fin n=>WilsonNeutralTwoPrintPathBoxHome.radius (y k-y j))) (Finset.mem_univ i.val)
    have h₃:=Finset.le_sup (f:=fun z:Fin n → Cover=>Finset.univ.sup (fun k:Fin n=>
      Finset.univ.sup (fun j:Fin n=>WilsonNeutralTwoPrintPathBoxHome.radius (z k-z j)))) (contains cells ground m a)
    exact h₁.trans (h₂.trans h₃)

end YM.Integration.WilsonAddressedPublicFirstExtent
end
