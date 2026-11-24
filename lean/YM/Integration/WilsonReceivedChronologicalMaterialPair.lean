import YM.Integration.WilsonReceivedChronologicalMaterialRoster

/-! Adjacent original mounted materials use one common case and its actual dated physical files. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMaterialPair
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

open WilsonReceivedChronologicalMaterialRoster (Filed)
open WilsonReceivedDepositedOrbitalLedger (book)
variable {G:Gauge}{n q N K j:ℕ}{D k:Fin n → ℕ}{R:Run G}{V:Realm G (q+1) Credit.leanC}
  {draw:V.draws=R.family.path.levels}{rate δ σ τ:ℝ}
  (cells:Digits V.draws (Fin n))(κ:(v:Fin n) → Knob (D v))(pt:Fin n → Chamber)(seed:(v:Fin n) → Choice R k v)
  (side upperSide:Side)(y home:Fin n → Cover)(t:Case D)
  (L:Material R N (j+1) q k σ (binder side y))(H:Material R N ((j+1)+1) q k τ (binder upperSide home))

local notation "copy" X:max z:max s:max => output X s N z
local notation "source" knob:max day:max z:max s:max => fixed R k knob pt N K day (onLevels draw cells) seed z s
local notation "print" paid:max X:max test:max closed:max =>
  book R H.realm H.start paid N X H.nonneg H.lower H.radius (binder upperSide home) pin
    (fun _=>subset_univ _) (fun s=>s.property.choose_spec) H.positive home test closed H.tickets

private theorem reprint {E:Fin n → ℕ}(assign:E=H.tests)
    (test:Case E)(knob:(v:Fin n) → Knob (E v))
    (testH:Case H.tests)(knobH:(v:Fin n) → Knob (H.tests v))(ht:HEq test testH)(hk:HEq knob knobH)
    (X:Input H.realm H.start univ k H.tests H.amplitude)(printed:H=(print H.paid X testH H.closed))
    (declared:∀z s, (copy X z s)=(source knobH ((j+1)+1) z s)):
    ∃(fee:Paid R H.realm H.start E k H.allowance τ)(U:Input H.realm H.start univ k E H.amplitude)
      (protection:Cloze E k H.realm Credit.leanC),
      H=(print fee U test protection) ∧ ∀z s,(copy U z s)=(source knob ((j+1)+1) z s):=by
  subst E
  cases eq_of_heq ht
  cases eq_of_heq hk
  exact ⟨H.paid,X,H.closed,printed,declared⟩

/-- The complete upper pupil is the originally posted physical book in the same coordinates as
the lower one, while each actual prior is the independently submitted fixed-digit history. -/
theorem original
    (older:Filed (K:=K) (draw:=draw) (rate:=rate) (δ:=δ) cells κ pt seed side y t L)
    (later:Filed (K:=K) (draw:=draw) (rate:=rate) (δ:=δ) cells κ pt seed upperSide home t H):
    ∃(test:Case L.tests)(knob:(v:Fin n) → Knob (L.tests v)),HEq test t ∧ HEq knob κ ∧
      Addressed y L test ∧ (∀z s,(copy L.prior z s)=(source knob (j+1) z s)) ∧
      ∃(fee:Paid R H.realm H.start L.tests k H.allowance τ)(U:Input H.realm H.start univ k L.tests H.amplitude)
        (protection:Cloze L.tests k H.realm Credit.leanC),
        H=(print fee U test protection) ∧ ∀z s,(copy U z s)=(source knob ((j+1)+1) z s):=by
  obtain ⟨test,knob,ct,ck,rates,loc,old,_⟩:=older
  obtain ⟨testH,knobH,ctH,ckH,ratesH,_,_,X,printed,declared⟩:=later
  exact ⟨test,knob,ct,ck,loc,old,reprint cells pt seed upperSide home H
    (rates.2.1.trans ratesH.2.1.symm) test knob testH knobH (ct.trans ctH.symm) (ck.trans ckH.symm) X printed declared⟩

end YM.Integration.WilsonReceivedChronologicalMaterialPair
end
