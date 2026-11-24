import YM.Integration.WilsonOriginalTwoFlatIRFlatBudget
import YM.Integration.WilsonReceivedChronologicalMaterialRoster
/-! Terminal income of the previously selected original word at the actual signed
test. Its finite order affects the prefactor and leaves the recorded powers visible. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatSalary
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


open WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonIndependentCollarOrdinaryCruise (address)



open WilsonCoeffUV.Wheel.Address (toe)
open WilsonGeneralArityCopyAccount (term)
open WilsonOriginalTwoFlatIRFlatLedger (occupied)

open WilsonCoeffUV.Wheel
variable {G:Gauge}{n e:ℕ}{D k:Fin n→ℕ}{R:Run G}{N K c j:ℕ}
    {V:Realm G (e+1) Credit.leanC}{draw:V.draws=R.family.path.levels}{rate δ σ:ℝ}
    (κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(cells:Digits V.draws (Fin n))(seed:(v:Fin n)→Choice R k v)
    (y:Fin n → Cover)(t:Case D)
local notation "atDate" => j+1
local notation "path" => onLevels draw cells
local notation "bank" => fixed R k κ pt N K c (path) seed
local notation "L_" => R.family.path.levels
local notation "I" => Hot (Stock.census (Fin n))


open WilsonReceivedChronologicalMaterialRoster (Filed)
variable {side:Side}{σ₀:ℝ}(H:Material R N (j+1) e k σ₀ (binder side y))


def head (z:I):ℝ:=
  let T:=z.val.val
  ((e+1:ℕ):ℝ)*((mass k T+e+1:ℕ):ℝ)*
    ((∏v∈T,‖t v‖)*(R.family.path.levels.clock.hatBeta (j+1)^δ*rate^T.card))

theorem original (filed:Filed (K:=K) (draw:=draw) (rate:=rate) (δ:=δ) cells κ pt seed side y t H)
    (z:I):∑a:Fin (e+1),(words H z).fare a ≤ head (R:=R) (k:=k) (e:=e) (δ:=δ) (rate:=rate) (j:=j) t z:=by
  obtain ⟨test,knob,et,_ek,paid,address,_⟩:=filed
  obtain ⟨_,axes,gross,rent,_,_⟩:=paid
  subst D
  obtain rfl:=eq_of_heq et
  have sold:=WilsonOriginalTwoFlatIRFlatBudget.original H z
  apply sold.trans_eq
  unfold WilsonOriginalTwoFlatIRFlatBudget.budget head
  rw [gross,rent,address.ink z]
  rw [show (binder side y z).mode=z.val by rfl]
  ring

end YM.Integration.WilsonOriginalTwoFlatIRFlatSalary
end
