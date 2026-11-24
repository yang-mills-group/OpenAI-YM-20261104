import YM.Integration.WilsonOriginalFixedTestCensusPublicBase
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFixedTestCensusPublicCalendar
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
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonOriginalCensusFaceSites (root)


open WilsonOriginalCensusFaceSchools (Account)
open WilsonOriginalFixedTestCensusPublicBase (base)
variable {G:Gauge}{n q:ℕ}(R:Run G)(simple:G.Simple)(k:Fin n → ℕ)(B:ℝ)(cap:Fin n → ℝ)
local notation "χ" j:max => R.family.path.levels.clock.hatBeta (j)
local notation "rate" N:max per:max m:max δ:max => (Real.sqrt (R.family.path.β N per (m+1)))^(δ:ℝ)*B^n
local notation "ticket" h:max b:max F:max => fun v=>b v*max 1
  (WilsonOriginalMixedBlockBudget.roots F (WilsonIndependentCollarMaterialWallet.bill h b))

include simple in
theorem original (one:1 ≤ B)(d:Fin n → ℕ) :
    ∀ᶠ m:ℕ in atTop,∀j,m ≤ j → ∀N per:ℕ,m+1 ≤ N → ∀(D:Fin n → ℕ)(t:Case D)
      (δ σ₀ σ₁:ℝ)(side₀ side₁:Side)(y₀ y₁:Fin n → Cover)(V:Realm G (q+1) Credit.leanC)
      (L:Material R N (j+1) q k σ₀ (binder side₀ y₀))(H:Material R N (j+2) q k σ₁ (binder side₁ y₁))
      (t₀:Case L.tests)(t₁:Case H.tests),
      Account V (rate N per m δ) δ side₀ y₀ L t →
      Account V (rate N per m δ) δ side₁ y₁ H t₀ →
      Addressed y₀ L t₀ → Addressed y₁ H t₁ → HEq t₀ t → HEq t₁ t₀ → 0 ≤ δ → δ ≤ 1 →
      (∀v,‖t v‖ ≤ cap v*(χ (j+1))^(d v)) →
      let b:=base B cap d (χ (j+1))
      (∀v,0<b v) ∧ (∀v,(ticket H b (binder side₁ y₁)) v ≤ (χ (j+1))^(d v+6)) ∧
        ∀v,(ticket L b (binder side₀ y₀)) v ≤ (χ (j+1))^(d v+6):=by
  have calendar:=eventually_atTop.mp (WilsonOriginalFixedTestCensusPairedTickets.clock (k:=k) (q:=q) R simple)
  filter_upwards [WilsonOriginalFixedTestCensusPublicBase.opening R simple B cap,eventually_ge_atTop calendar.choose]
    with m offer late
  intro j after N per live D t δ σ₀ σ₁ side₀ side₁ y₀ y₁ V L H t₀ t₁ lower upper locatedL locatedH
    eqL eqH dp ds tests b
  obtain ⟨warm,stage⟩:=offer j after
  obtain ⟨_,gateL,gateH,step⟩:=calendar.choose_spec (j+1) (late.trans (after.trans (Nat.le_succ j)))
  have termsL:=WilsonOriginalFixedTestCensusPublicBase.material R simple B L t lower t₀ eqL after live
    one warm dp ds cap d stage tests
  have localTest:∀v,‖t₀ v‖ ≤ cap v*(χ (j+1))^(d v):=fun v=>by
    rw [WilsonOriginalFixedTestCensusPublicBase.norm_eq t t₀ lower.2.1 eqL v]
    exact tests v
  have termsH:=WilsonOriginalFixedTestCensusPublicBase.material R simple B H t₀ upper t₁ eqH after live
    one warm dp ds cap d stage localTest
  have positive:∀v,0<b v:=fun v=>(termsL v).1
  have made:=WilsonOriginalFixedTestCensusPairedTickets.original R y₀ y₁ L H t₀ t₁ locatedL locatedH
    b b positive positive (fun v=>(termsL v).2.1) (fun v=>(termsH v).2.1)
    (lower.2.2.2.1.trans_le ds) (upper.2.2.2.1.trans_le ds) warm gateL gateH step
    (fun v=>d v+2) (fun v=>(termsL v).2.2) (fun v=>(termsH v).2.2)
  exact ⟨positive,made⟩

end YM.Integration.WilsonOriginalFixedTestCensusPublicCalendar
end
