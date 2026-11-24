import YM.Integration.WilsonOriginalFixedTestCensusPublicCalendar

/-! Each published roster has its own fixed pre-regulator width on both neighboring signed hearings. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMaterialWallet
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
      (δ σ:ℝ)(side:Side)(y:Fin n → Cover)(V:Realm G (q+1) Credit.leanC)
      (M:Material R N (j+1) q k σ (binder side y))(test:Case M.tests),
      Account V (rate N per m δ) δ side y M t → Addressed y M test → HEq test t → 0 ≤ δ → δ ≤ 1 →
      (∀v,‖t v‖ ≤ cap v*(χ (j+1))^(d v)) →
      let b:=base B cap d (χ (j+1))
      (∀v,0<b v) ∧ ∀v,(ticket M b (binder side y)) v ≤ (χ (j+1))^(d v+4):=by
  have calendar:=eventually_atTop.mp (WilsonOriginalFixedTestCensusPairedTickets.clock (k:=k) (q:=q) R simple)
  filter_upwards [WilsonOriginalFixedTestCensusPublicBase.opening R simple B cap,eventually_ge_atTop calendar.choose]
    with m offer arrived
  intro j young N per live D t δ σ side y V M test account located same dp ds fees b
  obtain ⟨warm,small⟩:=offer j young
  have sized:=WilsonOriginalFixedTestCensusPublicBase.material R simple B M t account test same young live
    one warm dp ds cap d small fees
  have positive:∀v,0<b v:=fun v=>(sized v).1
  refine ⟨positive,?_⟩
  intro v
  have stage:=(calendar.choose_spec (j+1) (arrived.trans (young.trans (Nat.le_succ j)))).2.1
  calc
    _ ≤ b v*(χ (j+1))^2:=WilsonOriginalFixedTestCensusTickets.original y M test located b positive
      (fun l=>(sized l).2.1) (account.2.2.2.1.trans_le ds) stage v
    _ ≤ (χ (j+1))^(d v+2)*(χ (j+1))^2:=
      mul_le_mul_of_nonneg_right (sized v).2.2 (sq_nonneg _)
    _ = _:=by rw [←pow_add]

end YM.Integration.WilsonReceivedChronologicalMaterialWallet
end
