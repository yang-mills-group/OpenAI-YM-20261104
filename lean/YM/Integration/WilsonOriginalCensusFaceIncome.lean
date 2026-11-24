import YM.Integration.WilsonOriginalCensusFaceSheet
import YM.Integration.WilsonReceivedDepositedOrbitalLedger

/-! The full original roster on the actual addressed upper and lower deposits. -/
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFaceIncome
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
variable {G:Gauge}{n q i N:ℕ}{k:Fin n→ℕ}{σ:ℝ}{R:Run G}{side:Side}
  (y:Fin n → Cover)(H:Material R N (i+1) q k σ (binder side y))(t:Case H.tests)
local notation "bank" => Stock.census (Fin n)
local notation "I" => Hot (bank)

theorem full :H.available=univ:=by
  apply eq_univ_of_forall
  intro v
  let s:I:=⟨⟨{v},mem_univ _⟩,singleton_nonempty v⟩
  exact H.included s (mem_singleton_self v)

theorem installed (named:H.pin=pin)(roots:H.root=y ∘ pin)
    (income:∀s,H.source s=t)(offset:∀s,HEq (H.frill s) (front (J:=s.val.val) (pin s) y)):
    ∃X:Input H.realm H.start univ k H.tests H.amplitude,
      (∀z s,output X s N z=output H.prior s N z) ∧
      H=WilsonReceivedDepositedOrbitalLedger.book R H.realm H.start H.paid N X H.nonneg H.lower H.radius
        (binder side y) pin (fun _=>subset_univ _) (fun s=>s.property.choose_spec) H.positive y t H.closed H.tickets:=by
  have all:=full y H
  rcases H with ⟨D,S,A,δ,Y,lo,earned,X,non,cut,pos,c,inside,marked,deep,root,source,rel,closed,tickets⟩
  change Case D at t
  dsimp only at *
  change S=univ at all
  subst S
  change c=pin at named
  subst c
  change root=y ∘ pin at roots
  subst root
  have ink:source=fun _=>t:=funext income
  subst source
  have slit:rel=fun s=>front (J:=s.val.val) (pin s) y:=funext (fun s=>eq_of_heq (offset s))
  subst rel
  exact ⟨X,fun _ _=>rfl,rfl⟩

theorem addressed {j:ℕ}(L:Material R N j q k σ (binder side y))(test:Case L.tests)
    (named:L.pin=pin)(roots:L.root=y ∘ pin)
    (income:∀s,L.source s=test)(offset:∀s,HEq (L.frill s) (front (J:=s.val.val) (pin s) y)):
    Addressed y L test:=by
  refine ⟨income,?_,?_⟩
  · intro s
    rw [roots]
    rfl
  · intro s v mark
    obtain ⟨D,S,A,δ,Y,lo,earned,X,non,cut,pos,c,inside,marked,deep,root,source,rel,closed,tickets⟩:=L
    change c=pin at named
    subst c
    change root=y ∘ pin at roots
    subst root
    have slit:rel=fun s=>front (J:=s.val.val) (pin s) y:=funext (fun l=>eq_of_heq (offset l))
    subst rel
    exact WilsonOriginalCensusFaceSites.source y s v mark

end YM.Integration.WilsonOriginalCensusFaceIncome
end
