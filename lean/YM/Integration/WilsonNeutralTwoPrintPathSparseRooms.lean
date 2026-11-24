import YM.Integration.WilsonNeutralTwoPrintPathSparseCalendar
import YM.Integration.WilsonOriginalCensusFaceAdmission
import YM.Integration.WilsonOriginalCensusMeasuredCourse
import YM.Integration.WilsonOriginalCensusFixedBank

set_option autoImplicit false
set_option quotPrecheck false
universe u
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathSparseRooms
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



open WilsonNeutralTwoPrintPathBoxHome (radius)
open WilsonNeutralTwoPrintPathSparseCalendar (named)
open WilsonOriginalCensusFaceAdmission (housed)


/-- The original finite housing test holds simultaneously for every configuration
whose announced coordinates lie in the indicated box. -/
theorem housing (R:Run G)(j diameter:ℕ):∀ᶠ per:ℕ in atTop,∀y:Fin n → Cover,
    2*((Finset.univ:Finset (Fin n)).image y).sup radius≤diameter → housed y R j per:=by
  let points:Finset (Fin n → Cover):=Fintype.piFinset (fun _:Fin n=>
    Fintype.piFinset (fun _:Axis=>Finset.Icc (-(diameter:ℤ)) diameter))
  have appointed:∀y:↥points,∀ᶠ per:ℕ in atTop,housed y.val R j per:=fun y=>
    WilsonOriginalCensusFaceAdmission.housing y.val R j
  filter_upwards [eventually_all.2 appointed] with per summer
  intro y survey
  have entrance:y∈points:=by
    change y∈Fintype.piFinset _ 
    simp only [Fintype.mem_piFinset,Finset.mem_Icc]
    intro v axis
    have one:radius (y v)≤((Finset.univ:Finset (Fin n)).image y).sup radius:=
      Finset.le_sup (Finset.mem_image_of_mem _ (Finset.mem_univ v))
    have coord:(y v axis).natAbs≤radius (y v):=
      Finset.le_sup (s:=Finset.univ) (f:=fun a:Axis=>(y v a).natAbs) (Finset.mem_univ axis)
    omega
  exact summer ⟨y,entrance⟩

/-- The same paid physical course supplies the lower input income, its signed
finite-side tariffs and room for all possible source centers before the UV cutoff and period. -/
theorem original {a:Axis}{simple:G.Simple}{ε:ℝ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
    {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (WilsonOriginalOpticalSchedule.prepared schedule) R T W)
    (k₀:Fin n→ℕ)(κ₀:∀v,Knob (D v))(pt₀:Fin n→Chamber)(e:ℕ):
    ∀ᶠ m:ℕ in atTop,∀(K:ℕ)(dates:Finset ℕ),(∀j∈dates,m≤j ∧ j<K) →
    ∃rates:(j:dates)→Rates R k₀ κ₀ pt₀ j.val K e,
      (∀(j:dates)(D':Fin n→ℕ),D'=D → ∀(κ':(v:Fin n)→Knob (D' v)),HEq κ' κ₀ →
        WilsonOriginalCensusFixedBank.Income (k:=k₀) R κ' pt₀ e j.val) ∧
      ∀(diameter:dates→ℕ)(gross wind:dates→ℝ),(∀j,0<wind j) → ∀ᶠ per:ℕ in atTop,∀j:dates,
        (∀y:Fin n → Cover,2*((Finset.univ:Finset (Fin n)).image y).sup radius≤diameter j → housed y R j.val per) ∧
        ∀(D':Fin n→ℕ)(same:D'=D)(κ':(v:Fin n)→Knob (D' v))(printed:HEq κ' κ₀)
          (J:Finset (Fin n))(v:Fin (e+1)),
          Opened R j.val per (mass k₀ J+v.val) ((named (rates j) same κ' printed).width J v)
            ((named (rates j) same κ' printed).fare J v) (gross j) (wind j):=by
  let salary:ℕ→Gear G→ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  have wage:FundedMarkedCoverRows.prices salary R.kit:=paid.billsPaid.1
  filter_upwards [WilsonNeutralTwoPrintPathSparseCalendar.original R k₀ κ₀ pt₀ simple paid.quiet salary wage e] with m funded
  intro K dates enrolled
  obtain ⟨rates,bank,periods⟩:=funded K dates enrolled
  refine ⟨rates,bank,?_⟩
  intro diameter gross wind positive
  have purchased (j:dates):∀ᶠ per:ℕ in atTop,∀(D':Fin n→ℕ)(same:D'=D)(κ':(v:Fin n)→Knob (D' v))
      (printed:HEq κ' κ₀)(J:Finset (Fin n))(v:Fin (e+1)),Opened R j.val per (mass k₀ J+v.val)
      ((named (rates j) same κ' printed).width J v) ((named (rates j) same κ' printed).fare J v) (gross j) (wind j):=by
    filter_upwards [periods (gross j) (wind j) (positive j)] with per earned
    intro D' same κ' printed J v grid divides b low high
    exact (earned j D' same κ' printed J v grid divides b low high).trans
      (div_le_self (positive j).le (by linarith [Nat.cast_nonneg (α:=ℝ) dates.card]))
  filter_upwards [eventually_all.2 purchased,eventually_all.2 (fun j:dates=>housing (n:=n) R j.val (diameter j))]
    with per price fit
  exact fun j=>⟨fit j,price j⟩

end YM.Integration.WilsonNeutralTwoPrintPathSparseRooms
end
