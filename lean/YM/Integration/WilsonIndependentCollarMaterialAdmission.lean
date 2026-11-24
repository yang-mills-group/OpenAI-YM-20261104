import YM.Integration.WilsonIndependentCollarMaterialStation
import YM.Integration.WilsonOriginalCensusFaceSchools

/-! The two enrolled adjacent fixed-child appointments supply the actual materials read at a physical station. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarMaterialAdmission
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

variable {G:Gauge}{n q j N K:ℕ}{D k:Fin n→ℕ}{R:Run G}{V:Realm G (q+1) Credit.leanC}
  {draw:V.draws=R.family.path.levels}{rate δ σ σₗ:ℝ}
  (upper:Submitted R V draw D k N K (j+1) rate δ σ)(lower:Submitted R V draw D k N K j rate δ σₗ)
  (cells:Digits V.draws (Fin n))(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(seed:(v:Fin n)→Choice R k v)
  (per:ℕ)(y:Fin n → Cover)(t:Case D)(deep:∀s:Hot (Stock.census (Fin n)),0 < mass k s.val.val)
local notation "labels" => Hot (Stock.census (Fin n))
local notation "grid" => coarse R (j+1) per
local notation "fineSide" => fine R (j+1) per
local notation "parent" => binder (grid) y
local notation "younger" => chartIn (loose R.family.path.levels (j+1)) y (onLevels draw cells (j+1))
local notation "child" => binder (fineSide) (younger)

include upper lower in
theorem original :
    ∃(L:Material R N (j+1) q k σₗ (parent))(test:Case L.tests)(knob:(v:Fin n)→Knob (L.tests v))
      (H:Material R N ((j+1)+1) q k σ (child))
      (fund:Paid R H.realm H.start L.tests k H.allowance σ)(closed:Cloze L.tests k H.realm Credit.leanC)
      (X:Input H.realm H.start univ k L.tests H.amplitude),
      HEq test t ∧ HEq knob κ ∧ Account V rate δ (grid) y L t ∧ Addressed y L test ∧
      (∀z s,output L.prior s N z=fixed R k knob pt N K (j+1) (onLevels draw cells) seed z s) ∧
      Account V rate δ (fineSide) (younger) H test ∧
      H=book R H.realm H.start fund N X H.nonneg H.lower H.radius (child) pin (fun _=>subset_univ _)
        (fun s=>s.property.choose_spec) deep (younger) test closed H.tickets ∧
      (∀z s,output X s N z=fixed R k knob pt N K ((j+1)+1) (onLevels draw cells) seed z s) ∧
      ∀(P:Passport (fineSide) (Fin n))(I:Type)
        (printed:I→Row P (Stock.census (Fin n)) G (Affinity.Wallet (room (Fin n)))),
        P=port (fineSide) (younger) → I=((s:labels)×(words H s).Roster) → HEq printed (mounts H) →
      ∀(w:Fin n→ℝ),(∀v,0<w v) → ∀order seats shelf:ℕ,q≤order → 1 ≤ seats → n ≤ seats → (∑v,k v) ≤ shelf →
      ∃F:Mounted R κ pt N per (j+1) K q k y (onLevels draw cells) seed, HEq F.high printed ∧
        F.sheet=P ∧ HEq F.lower L ∧ HEq F.film test ∧ HEq F.knob knob ∧ HEq F.input X ∧
        F.rent=w ∧ F.order=order ∧ F.seats=seats ∧ F.shelf=shelf:=by
  obtain ⟨L,test,knob,actual,correct,acct,atSites,deposited,H,fees,fund,closed,X,bound,sourced⟩:=
    WilsonOriginalCensusFaceSchools.original upper lower cells κ pt seed per y t deep
  refine ⟨L,test,knob,H,fund,closed,X,actual,correct,acct,atSites,deposited,fees,bound,sourced,?_⟩
  intro P I printed placed names mounted w paid order seats shelf shows occupied slots fits
  let F:Mounted R κ pt N per (j+1) K q k y (onLevels draw cells) seed:={
    lowerWidth:=σₗ, lower:=L,chart:=acct.2.1,knob,correct,film:=test,atSites,
    real:=H.realm,late:=H.start,allowance:=H.allowance,breadth:=σ,funded:=fund,amount:=H.amplitude,input:=X,
    nonneg:=H.nonneg,cutoff:=H.lower,positive:=H.radius,depth:=deep,filed:=closed,stores:=H.tickets,carried:=sourced,
    sheet:=P,Kind:=I,high:=printed,placed,names:=by rw [←bound];exact names,
    mounted:=by rw [←bound];exact mounted,
    rent:=w,paid,order,seats,shelf,shows,occupied,slots,fits}
  exact ⟨F,HEq.rfl,rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,rfl,rfl,rfl,rfl⟩

end YM.Integration.WilsonIndependentCollarMaterialAdmission
end
