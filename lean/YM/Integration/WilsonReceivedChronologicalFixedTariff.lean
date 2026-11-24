import YM.Integration.WilsonReceivedChronologicalMaterialOpening
import YM.Integration.WilsonIndependentCollarLowerMass
/-! A single physical-period opening for every occupied test on the finite original tape. -/
set_option autoImplicit false
universe u
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedTariff
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


open QuadraticLocal.Affinity WilsonOriginalMixedBlockRows WilsonOriginalSparseFiledOpening
open WilsonReceivedChronologicalMaterialOpening (price)
def gross (caps:Fin n → ℝ):ℝ:=∏v,max 1 (caps v)

theorem weight (caps:Fin n → ℝ)(t:Case D)(inside:∀v,‖t v‖≤caps v)
    (x:Wallet (room (Fin n)))(s:YM.Multi.Hot (Stock.census (Fin n))):
    ‖∏v∈s.val.val,(x v).val‖*‖touch t s.val.val‖≤gross caps:=by
  calc
    _ ≤ 1*‖touch t s.val.val‖:=mul_le_mul_of_nonneg_right (project s.val x ()).property (touch t s.val.val).opNorm_nonneg
    _ ≤ ∏v∈s.val.val,‖t v‖:=by simpa only [one_mul] using WilsonIndependentCollarLowerMass.cartesian t s.val.val
    _ ≤ ∏v∈s.val.val,max 1 (caps v):=Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun v _=>(inside v).trans (le_max_right _ _)
    _ ≤ _:=Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
      (fun v _=>zero_le_one.trans (le_max_left _ _)) (fun v _ _=>le_max_left _ _)

def allowance (R:Run G)(k:Fin n → ℕ)(p i:ℕ)(s:YM.Multi.Hot (Stock.census (Fin n))):ℝ:=
  ((R.alloy.B.a.clock.hatBeta i)^(near (p+1) (WilsonOriginalCensusPhysicalLoad.head (sides k k) s.val) 1))⁻¹

theorem positive (R:Run G)(k:Fin n → ℕ)(p i:ℕ)(s:YM.Multi.Hot (Stock.census (Fin n))):
    0<allowance R k p i s:=inv_pos.mpr (pow_pos (zero_lt_one.trans (R.alloy.B.a.fits.delayed i)) _)

theorem original {axis:Axis}{simple:G.Simple}{ε:ℝ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
    {T:Campaign R}{W:Campaign.Pillars R T}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (WilsonOriginalOpticalSchedule.prepared schedule) R T W)
    (grades:Fin n → ℕ)(κ:∀v,Knob (D v))(pt:Fin n → Chamber)(q p:ℕ)(caps:Fin n → ℝ):
    ∀ᶠ m:ℕ in atTop,∀K:ℕ,let active:=Finset.Ico m (K-1)
    ∃rates:(a:active) → Rates R grades κ pt (a.val+1) K q,
      (∀a:active,WilsonOriginalCensusFixedBank.Income (k:=grades) R κ pt q (a.val+1)) ∧
      ∀V:Realm G (q+1) Credit.leanC,∀ᶠ per:ℕ in atTop,∀a:active,
      (∀cells:Digits V.draws (Fin n),let y:=homes cells 0 m (a.val-m)
        housed y R (a.val+1) per ∧ spread y≤diameter V n m (a.val-m)) ∧
      ∀(s:YM.Multi.Hot (Stock.census (Fin n)))(e:Fin (q+1)),Opened R (a.val+1) per (mass grades s.val.val+e.val)
        ((rates a).width s.val.val e) ((rates a).fare s.val.val e) (gross caps) (price R grades (a.val+1) p):=by
  filter_upwards [WilsonReceivedChronologicalMaterialOpening.original paid grades κ pt q p] with m work
  intro K active
  obtain ⟨rates,rich,offer⟩:=work K
  let next:(a:active) → ↥(Finset.Ico m K):=fun a=>⟨a.val+1,by
    obtain ⟨lower,upper⟩:=Finset.mem_Ico.mp a.property
    apply Finset.mem_Ico.mpr
    constructor <;> omega⟩
  refine ⟨fun a=>rates (next a),fun a=>rich (next a),?_⟩
  intro V
  filter_upwards [offer V (fun _=>gross caps)] with per accounted
  intro a
  obtain ⟨geometry,opened⟩:=accounted (next a)
  refine ⟨?_,fun s e=>opened s.val.val e⟩
  intro cells y
  simpa only [next,Nat.add_sub_add_right] using geometry cells
end YM.Integration.WilsonReceivedChronologicalFixedTariff
end
