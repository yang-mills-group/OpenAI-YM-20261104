import YM.Integration.WilsonOriginalCensusDatedPhysicalReceiver

/-! The given marked run elects its period wages for the whole finite collar
before source fields or ultraviolet cutoffs. Every real decoder on every
super-board of each allowed period can spend its share of the same tolerance. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusDatedCollarPurchase
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
variable {G:Gauge}{n:ℕ}{R:Run G}{N i e:ℕ}{k:Fin n → ℕ}{σ:ℝ}
  {side:Side}{P:Passport side (Fin n)}{I:Type}[Fintype I]{B:I → Binder P (Stock.census (Fin n))}
  (H:Material R N i e k σ B)
  (κ:(v:Fin n) → Knob (H.tests v))(pt:Fin n → Chamber)(b:ℕ)
  (cells:Digits R.family.path.levels (Fin n))(seed:(v:Fin n) → Choice R k v)
  (x:Affinity.Wallet (room (Fin n)))


open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonOriginalCensusDatedSheets (winding)
open WilsonNeutralTwoPrintPathDatedWage
local notation "block" z:max => (B z).mode.val
local notation "ports" z:max => toe (block z) (H.pin z) (H.root z) (H.frill z)
local notation "older" => fixed R k κ pt N b (i+1) cells seed
local notation "scope" z:max d:max => mass k (block z)+d



variable {D : Fin n → ℕ}


open WilsonOriginalCensusDatedHeldTariff (salary periodTariff Rates)


open WilsonOriginalCensusDatedPeriodOpening (Opened)

theorem original (R:Run G)(k₀:Fin n → ℕ)(κ₀:∀v,Knob (D v))(pt₀:Fin n → Chamber)
    (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (ask:ℕ→Gear G→ℝ)(granted:FundedMarkedCoverRows.prices ask R.kit)(e:ℕ):
    ∀ᶠ m:ℕ in atTop,∀(K:ℕ)(dates:Finset ℕ), (∀j∈dates,m≤j ∧ j<K) →
    ∃rates:(j:dates)→Rates R k₀ κ₀ pt₀ j.val K e,∀(gross ε:ℝ),0<ε →
    ∀ᶠ per:ℕ in atTop,∀(j:dates)(J:Finset (Fin n))(a:Fin (e+1)),
      Opened R j.val per (mass k₀ J+a.val) ((rates j).width J a) ((rates j).fare J a)
        gross (ε/((dates.card:ℝ)+1)):=by
  obtain ⟨m₀,beginning⟩:=eventually_atTop.1
    (WilsonOriginalCensusDatedHeldTariff.purchase R k₀ κ₀ pt₀ simple quiet ask granted e)
  filter_upwards [eventually_ge_atTop m₀] with m ready
  intro K dates subset
  have earned (j:dates):Nonempty (Rates R k₀ κ₀ pt₀ j.val K e):=
    beginning j.val (ready.trans (subset j.val j.property).1) K (subset j.val j.property).2
  let rates: (j:dates)→Rates R k₀ κ₀ pt₀ j.val K e:=fun j=>Classical.choice (earned j)
  refine ⟨rates,?_⟩
  intro gross ε positive
  have portion:0<ε/((dates.card:ℝ)+1):=by positivity
  refine eventually_all.2 fun j=>eventually_all.2 fun J=>eventually_all.2 fun a=>?_
  exact WilsonOriginalCensusDatedPeriodOpening.original R k₀ κ₀ pt₀ (rates j) J a gross portion

theorem total {dates:Finset ℕ}(charge:dates → ℝ){ε:ℝ}(positive:0≤ε)
    (each:∀j,charge j≤ε/((dates.card:ℝ)+1)):∑j,charge j≤ε:=by
  calc
    _ ≤ ∑_j:dates,ε/((dates.card:ℝ)+1):=sum_le_sum fun j _=>each j
    _ = (dates.card:ℝ)/((dates.card:ℝ)+1)*ε:=by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring
    _ ≤ 1*ε:=by
      apply mul_le_mul_of_nonneg_right _ positive
      exact (div_le_one (by positivity)).2 (by linarith)
    _ = ε:=one_mul _

end YM.Integration.WilsonOriginalCensusDatedCollarPurchase
end
