import YM.Integration.WilsonIndependentCollarMaterialCruise

/-! Split the complete ordinary material at its true ancestral address and
continue it with the original quiet history on both sides of the stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarMaterialStop
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
open WilsonOriginalCensusFaceSheet (Addressed recenter)
open WilsonIndependentCollarAddressedSource (Submitted)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonOriginalCensusFaceIncome (addressed)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonOriginalCensusFaceSchools (Account)
open WilsonOriginalCensusFixedBank (Income)


open WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonIndependentCollarOrdinaryCruise (address)


theorem append {G:Gauge}{I:Type} [Fintype I] [DecidableEq I]
    (L:Levels G)(cells:Digits L I)(first more i:ℕ)(z:I → Cover):
    address L cells (first+more) i z=
      address L cells more (i+first) (address L cells first i z):=by
  induction first generalizing i z with
  | zero=>simp [WilsonIndependentCollarOrdinaryCruise.address]
  | succ j ih=>
    rw [show (j+1)+more=(j+more)+1 by omega]
    change address L cells (j+more) (i+1) (chartIn (loose L i) z (cells i))=
      address L cells more (i+(j+1)) (address L cells j (i+1) (chartIn (loose L i) z (cells i)))
    rw [ih,show i+1+j=i+(j+1) by omega]

variable {G:Gauge}{n:ℕ}{R:Run G}{N i e:ℕ}{k:Fin n→ℕ}{σ:ℝ}{side:Side}
  {y:Fin n → Cover}(H:Material R N i e k σ (binder side y))
  (κ:(v:Fin n)→Knob (H.tests v))(pt:Fin n→Chamber)(b:ℕ)
  (cells:Digits R.family.path.levels (Fin n))(seed:(v:Fin n)→Choice R k v)

theorem original (simple:G.Simple){c:ℕ}(late:i≤c)(above:c≤b)(hi:b≤N)
    (named:∀z S,output H.prior S N z=fixed R k κ pt N b i cells seed z S)
    (S:Finset (Fin n))(f:Pen H.tests S→L[ℝ] ℝ)(z:Fin n → Cover):
    tuftV f (levelsO (fun J=>output H.prior J N z) S)=
      cruises R.family.path.levels R.metals.O N (mass k S) c i
        (tuftV f (levelsO ((fixed R k κ pt N b c cells seed)
          (address R.family.path.levels cells (c-i) i z)) S)):=by
  let L:=R.family.path.levels
  let whereAt:=address L cells (c-i) i z
  obtain ⟨_,_,hire⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e (s:=1) zero_lt_one
  have older:=WilsonIndependentCollarOrdinaryCruise.original L R.metals.O simple R.alloy.B.ratio
    N cells (start R k κ pt seed) (hire seed).1 S f (b-c) c whereAt (by omega)
  have years:c+(b-c)=b:=by omega
  change tuftV f (levelsO ((fixed R k κ pt N b c cells seed) whereAt) S)=
    cruises L R.metals.O N (mass k S) (c+(b-c)) c
      (tuftV f (levelsO ((start R k κ pt seed) (address L cells (b-c) c whereAt)) S)) at older
  rw [years] at older
  rw [WilsonIndependentCollarMaterialCruise.original H κ pt b cells seed simple (late.trans above) hi named,
    cruisesMore L R.metals.O _ late above]
  change _=cruises L R.metals.O N (mass k S) c i
    (tuftV f (levelsO ((fixed R k κ pt N b c cells seed) whereAt) S))
  rw [older]
  have route:address L cells (b-i) i z=address L cells (b-c) c whereAt:=by
    have combine:=(append L cells (c-i) (b-c) i z)
    simpa only [show c-i+(b-c)=b-i by omega,show i+(c-i)=c by omega,whereAt] using combine
  change cruises L R.metals.O N (mass k S) c i
    (cruises L R.metals.O N (mass k S) b c
      (tuftV f (levelsO ((start R k κ pt seed) (address L cells (b-i) i z)) S)))=_
  rw [route]

end YM.Integration.WilsonIndependentCollarMaterialStop
end

