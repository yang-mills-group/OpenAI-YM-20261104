import YM.Integration.WilsonReceivedChronologicalMaterialSites
import YM.Integration.WilsonCenteredEnrolledOrigin
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldSockets
/-! The common housing charge at the actual capture of a compact physical test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMaterialCapture
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
variable {G:Gauge}{n f K per:ℕ}(R:Run G)

def placed (fine:f ≤ K)(z:Fin n → Site (R.family.side f per))(v:Fin n):Site (R.family.side K per):=
  (R.family.S.toDepth fine per).embed (z v)

theorem pinned {b:ℕ}(before:b ≤ f)(fine:f ≤ K)(z:Fin n → Site (R.family.side f per))(v:Fin n):
    physical R (placed R fine z) (before.trans fine) v=physical R z before v:=by
  have join:=Next.Rank.Station.parent_nested (R.family.S.toDepth before per) (R.family.S.toDepth fine per)
    (R.family.S.toDepth (before.trans fine) per) (R.family.S.toDepth_odd before per)
    (R.family.S.toDepth_odd fine per) ((R.family.S.toDepth fine per).embed (z v))
  unfold physical placed
  rw [join,Ratio.embed_parent]

theorem enrolled {N requested power t:ℕ}{B:ℝ}(grades:Fin 3 → ℕ)(fk:f ≤ K)(cut:K ≤ N)
    (A:WilsonMeasuredPublicEntrancePanel.Panel R grades N per f K fk cut requested power t B):
    placed R fk A.loc=WilsonOriginalMicroscopicEntranceGridRow.pin R fk A.loc:=rfl

theorem original (φ:Test n):
    ∃scale:ℝ,∃positive:0<scale,∀r:ℝ,0<r → scale*r ≤ R.family.S.a 0 →
    let b:=WilsonCloseCaptureDate.level R.family.S (scale*r)
    ∀(f K per:ℕ)(_:b ≤ f)(fine:f ≤ K),8*R.family.S.a f<R.family.S.a b →
    ∀z:Sites R (f,per) n,WilsonCenteredCompactBooking.mass R φ r (f,per) z≠0 →
    WilsonCenteredCompactBooking.mass R (dilate (inv_pos.mpr positive) φ) (scale*r) (f,per) z=
      WilsonCenteredCompactBooking.mass R φ r (f,per) z ∧
    ∀(q m:ℕ)(V:Realm G (q+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(start:m+1 ≤ K)
      (a:ℕ)(_:m+a+1+1 ≤ K)(past:b ≤ m+a+1),
    let actual:=placed R fine z
    let tape:=onLevels draw.symm (digits R actual)
    let ground:=footprint R actual start
    let port₀:=port (R.family.side (m+a+1+1) per) (homes tape ground m (a+1))
    let home:=(port₀.coarser (R.family.path.levels.clock.op (m+a+1) per).ratio).origin
    ∀(s:Finset (Fin n))(B:ℕ),0<B →
      (∀v∈s,sites R home past v∈({0}:Support (R.family.side b per))) ∧
        coverNumber B ({0}:Support (R.family.side b per)) ≤ 1:=by
  obtain ⟨scale,positive,space⟩:=WilsonCenteredEnrolledOrigin.original R φ
  refine ⟨scale,positive,?_⟩
  intro r rp small b f K per old fine narrow z nonzero
  obtain ⟨mass,arrive⟩:=space r rp small f per old narrow z nonzero
  refine ⟨mass,?_⟩
  intro q m V draw start a live past actual tape ground port₀ home s B width
  constructor
  · apply WilsonReceivedChronologicalMaterialSites.resident R draw actual start a b live past port₀ rfl s {0}
    intro v _
    exact Finset.mem_singleton.mpr ((pinned R old fine z v).trans (arrive v))
  · exact (Corona.cover_mono (Lattice.halo_subset 0 ({0}:Support (R.family.side b per))) B).trans
      (show coverNumber B (halo 0 {0}:Support (R.family.side b per)) ≤ 1 from by simpa using Corona.tile (0:Site _) 0 B width)

end YM.Integration.WilsonReceivedChronologicalMaterialCapture
end
