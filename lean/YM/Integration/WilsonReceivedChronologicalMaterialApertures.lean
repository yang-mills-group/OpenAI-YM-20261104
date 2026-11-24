import YM.Integration.WilsonReceivedChronologicalMaterialCapture
import YM.Integration.WilsonOriginalCensusFaceAdmission
/-! A period opening for every actual child layout of a compact test, fixed before the two regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMaterialApertures
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
variable {G:Gauge}{n K per:ℕ}(R:Run G){q:ℕ}{V:Realm G (q+1) Credit.leanC}

def layouts (V:Realm G (q+1) Credit.leanC)(n m:ℕ):ℕ → Finset (Fin n → Cover)
  | 0=>{0}
  | a+1=>(layouts V n m a).biUnion fun y=>
      (univ:Finset (Fin n → Site (loose V.draws (m+a+1)).L)).image
        (chartIn (loose V.draws (m+a+1)) y)

theorem member (tape:Digits V.draws (Fin n))(m a:ℕ):
    homes tape 0 m a ∈ layouts V n m a:=by
  induction a with
  | zero=>exact Finset.mem_singleton_self _
  | succ a ih=>
    exact mem_biUnion.mpr ⟨_,ih,mem_image.mpr ⟨tape (m+a+1),mem_univ _,rfl⟩⟩

abbrev spread (y:Fin n → Cover):ℕ:=2*((univ:Finset (Fin n)).image y).sup WilsonNeutralTwoPrintPathBoxHome.radius

def diameter (V:Realm G (q+1) Credit.leanC)(n m a:ℕ):ℕ:=(layouts V n m a).sup spread

theorem bounded (tape:Digits V.draws (Fin n))(m a:ℕ):spread (homes tape 0 m a) ≤ diameter V n m a:=
  Finset.le_sup (f:=spread) (member tape m a)

theorem period (V:Realm G (q+1) Credit.leanC)(n m days:ℕ):∀ᶠ per:ℕ in atTop,
    ∀a∈range days,∀tape:Digits V.draws (Fin n),housed (homes tape 0 m a) R (m+a+1) per:=by
  apply (eventually_all_finset (range days)).mpr
  intro a _
  filter_upwards [(eventually_all_finset (layouts V n m a)).mpr (fun y _=>
    WilsonOriginalCensusFaceAdmission.housing y R (m+a+1))] with per fit
  exact fun tape=>fit _ (member tape m a)

private theorem past {b c:ℕ}(z:Fin n → Site (R.family.side K per))(cb:c ≤ b)(born:b ≤ K)
    (v:Fin n)(root:physical R z born v=0):physical R z (cb.trans born) v=0:=by
  have nest:=Next.Rank.Station.parent_nested (R.family.S.toDepth cb per) (R.family.S.toDepth born per)
    (R.family.S.toDepth (cb.trans born) per) (R.family.S.toDepth_odd cb per)
    (R.family.S.toDepth_odd born per) (z v)
  change (R.family.S.toDepth born per).parent (z v)=0 at root
  change (R.family.S.toDepth (cb.trans born) per).parent (z v)=0
  rw [nest,root]
  let ratio:=R.family.S.toDepth cb per
  exact (show ratio.embed 0=0 from ratio.root.map_zero) ▸ ratio.embed_parent 0

theorem original (φ:Test n):∃scale:ℝ,∃positive:0<scale,∀r:ℝ,0<r → scale*r ≤ R.family.S.a 0 →
    let b:=WilsonCloseCaptureDate.level R.family.S (scale*r)
    ∀(m f K per:ℕ)(early:m+1 ≤ b)(old:b ≤ f)(fine:f ≤ K),8*R.family.S.a f<R.family.S.a b →
    ∀z:Sites R (f,per) n,WilsonCenteredCompactBooking.mass R φ r (f,per) z≠0 →
    WilsonCenteredCompactBooking.mass R (dilate (inv_pos.mpr positive) φ) (scale*r) (f,per) z=
      WilsonCenteredCompactBooking.mass R φ r (f,per) z ∧
      (footprint R (placed R fine z) (early.trans (old.trans fine))=0) ∧
      ∀(c:ℕ)(earlier:c ≤ b)(v:Fin n),physical R (placed R fine z) (earlier.trans (old.trans fine)) v=0:=by
  obtain ⟨scale,positive,book⟩:=WilsonCenteredEnrolledOrigin.original R φ
  refine ⟨scale,positive,?_⟩
  intro r rp small b m f K per early old fine narrow z active
  obtain ⟨mass,roots⟩:=book r rp small f per old narrow z active
  have fixed:∀(c:ℕ)(cb:c ≤ b)(v:Fin n),physical R (placed R fine z) (cb.trans (old.trans fine)) v=0:=
    fun _ cb v=>past R _ cb _ v ((pinned R old fine z v).trans (roots v))
  refine ⟨mass,?_,fixed⟩
  funext v
  change lift (physical R (placed R fine z) _ v)=0
  rw [fixed _ early v]
  funext d
  simp [lift]

end YM.Integration.WilsonReceivedChronologicalMaterialApertures
end
