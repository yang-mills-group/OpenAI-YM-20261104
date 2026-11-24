import YM.Integration.WilsonLongContactPriorHeld
import YM.Integration.WilsonLongContactPriorLiteral

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorLiteralCourse
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical

open RGLocalTaylor RGLocalTaylor.Laminate

open QLocalRequestedHeirPurchase WilsonCoherentMayerElection
open WilsonPositionSeparatedProfileMayerThermalElection (Sales)
open WilsonLongContactSectorProtection ManuscriptQLocalMarkedHeightRun

open WilsonMovingRoutedMayerStage
open RemainderComparison.Lyric Merge Merge.Palette
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Marker.Census V}
variable {R:Run G} {J:Request V} {A:NumericSchedule R.family J} {d:LocalFormal.Datum R.family Γ}
    {F:AnalyticInput J A d} {η:ℝ} (I:FullPreparedInputAt F η) {book:Booking G}
    (H:WilsonRootedSubmittedTail.CashAt I book)

variable (J:Request V) (extra:Stage→ℕ→ℝ) (γ:ℝ) (ρ:Premium G J.outputFieldOrder)
    (test:Demand G) (R:Run G) (χ:Chi) (δ:Daisy.Charity.RG12.Decal G)
local notation "fees" => (WilsonLongContactPriorRemittance.decal G).paired δ
local notation "fees₁" => calendar G fees
local notation "Δ" => WilsonGaussianDeterminantTender.joined G J χ fees₁
variable (licensed:WilsonLongContactMayerBooking.Sold J
    (WilsonGaussianDeterminantTender.joined G J χ (calendar G ((WilsonLongContactPriorRemittance.decal G).paired δ))) extra γ ρ test R.kit) (A:NumericSchedule R.family J)


theorem original (simple:G.Simple):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family Γ),d.level=m→
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I→
      let lev:=R.alloy.B.a
      let b:=licensed.choose (lev.clock.J (d.level+1)) (lev.clock.J d.level)
      ∀H:WilsonRootedSubmittedTail.CashAt I b,
        ∀ base y E K, WilsonLongContactPriorLiteral.Returned H Chi.canonical (A.outputNorm d.level)
          (ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base y E K).terms F.inputRadii:=by
  filter_upwards [WilsonLongContactPriorHeight.purchased (Γ:=Γ) J extra γ ρ test R χ fees₁ licensed A simple,
    ManuscriptQLocalMarkedHeightRun.reserve (Γ:=Γ) R A simple] with m ranked reserve d hm F η I cut
  dsimp only
  intro H base field E K
  have offer:=(WilsonLongContactMayerAppointment.booking (Γ:=Γ) J Δ extra γ ρ test R licensed d).1
  have paid:=(WilsonMovingRoutedMayerStage.shared J χ fees ρ _ _ _ _ _ _ offer).2.2.1
  obtain ⟨A',b,C',u,rv,v,z,B,e,q,n,N,ready,host,visit,rest⟩:=ranked d hm F I cut H
  let hats:=(ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base field E K).terms
  have supp:(A.outputNorm d.level).supportExponent≤QLocalRequestedHeirQuote.toll J:=by
    rw [(A.output_norm d.level).reserve]; unfold QLocalRequestedHeirQuote.toll; linarith
  exact WilsonLongContactPriorLiteral.received H Chi.canonical N (A.outputNorm d.level)
    (A.output_norm d.level).threshold (A.output_norm d.level).block hats F.inputRadii (rosterBudget I).radii _
    (ManuscriptQLocalMarkedHeightRun.enrolled I base field E K) (reserve d hm F I cut) paid visit supp

end YM.Integration.WilsonLongContactPriorLiteralCourse
