import YM.Integration.WilsonOriginalCensusFaceSchools

/-! One original dated occupied roster serves as both the previous edge's input and the next edge's physical output. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMaterialRoster
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

open WilsonOriginalCensusFaceSchools (Account)
variable {G:Gauge}{n q N K j:ℕ}{D k:Fin n→ℕ}{R:Run G}{V:Realm G (q+1) Credit.leanC}
  {draw:V.draws=R.family.path.levels}{rate δ σ:ℝ}
  (cells:Digits V.draws (Fin n))(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(seed:(v:Fin n)→Choice R k v)
  (side:Side)(y:Fin n→ Cover)(t:Case D)
local notation "gridWords" => binder side y

def Filed (H:Material R N (j+1) q k σ (binder side y)):Prop:=
  ∃(test:Case H.tests)(knob:(v:Fin n)→Knob (H.tests v)),
    HEq test t ∧ HEq knob κ ∧ Account V rate δ side y H t ∧ Addressed y H test ∧
    (∀z s,output H.prior s N z=fixed R k knob pt N K (j+1) (onLevels draw cells) seed z s) ∧
    ∃X:Input H.realm H.start univ k H.tests H.amplitude,
      H=WilsonReceivedDepositedOrbitalLedger.book R H.realm H.start H.paid N X H.nonneg H.lower H.radius
        (binder side y) pin (fun _=>subset_univ _) (fun s=>s.property.choose_spec) H.positive y test H.closed H.tickets ∧
      ∀z s,output X s N z=fixed R k knob pt N K (j+1) (onLevels draw cells) seed z s

theorem issued (grant:Submitted R V draw D k N K j rate δ σ)
    (deep:∀s:Hot (Stock.census (Fin n)),0 < mass k s.val.val):
    ∃H:Material R N (j+1) q k σ (gridWords),
      Filed (K:=K) (draw:=draw) (rate:=rate) (δ:=δ) cells κ pt seed side y t H:=by
  obtain ⟨H,realm,tests,amp,slack,named,roots,ink,frills,sales,copy,raw⟩:=
    grant cells κ pt seed _ side (port side y) (gridWords) pin (fun s=>s.property.choose_spec) deep y t
  subst D
  have income:=fun s=>eq_of_heq (ink s)
  obtain ⟨X,both,installed⟩:=WilsonOriginalCensusFaceIncome.installed y H t named roots income frills
  refine ⟨H,t,κ,HEq.rfl,HEq.rfl,⟨realm,rfl,amp,slack,sales,raw⟩,
    WilsonOriginalCensusFaceIncome.addressed y H t named roots income frills,?_,X,installed,?_⟩
  · exact fun z s=>eq_of_heq (copy z s)
  · exact fun z s=>(both z s).trans (eq_of_heq (copy z s))

/-- The same material is fixed once at every date before it is used on either adjacent edge. -/
theorem original {m:ℕ}(per:ℕ)(width:ℕ→ℝ)(placed:ℕ→Fin n→ Cover)
    (deep:∀s:Hot (Stock.census (Fin n)),0 < mass k s.val.val)
    (sold:∀a,m≤a→a+2≤K→Submitted R V draw D k N K a rate δ (width a)):
    ∃H:(a:↥(Ico m (K-1)))→Material R N (a.val+1) q k (width a.val)
       (binder (R.family.side (a.val+1) per) (placed a.val)),
      ∀a:↥(Ico m (K-1)),
        Filed (K:=K) (draw:=draw) (rate:=rate) (δ:=δ) cells κ pt seed _ (placed a.val) t (H a):=by
  classical
  have earned (a:↥(Ico m (K-1))):=issued cells κ pt seed
    (R.family.side (a.val+1) per) (placed a.val) t
    (sold a.val (mem_Ico.mp a.property).1 (by have late:=(mem_Ico.mp a.property).2;omega)) deep
  exact ⟨fun a=>(earned a).choose,fun a=>(earned a).choose_spec⟩

end YM.Integration.WilsonReceivedChronologicalMaterialRoster
end
