import YM.Integration.WilsonLongContactPriorHeight
import YM.Integration.WilsonLongContactPriorDisbursement
import YM.Integration.WilsonMovingRoutedMayerStage

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorTreasury
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

def Forced (k s:ℕ):Prop:=
  ∀base field E K,
    let roster:=(ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base field E K).terms
    let names:=fun i=>(roster i).M
    let l:=fun i=>Menu.sumFee (roster i) F.inputRadii
    let D:Match.Alliance H H 1 0:=Match.staple rfl rfl rfl
    ∃cash:ℕ→Finset _→ℝ,(∀i p,0≤cash i p ∧ ∀U,‖cod names H Chi.canonical l H D i U p‖≤cash i p) ∧
      Ac.Hit (fun i=>((Beam.marquee H (A.outputNorm d.level)).hard i).support) (A.outputNorm d.level).B
        (fun i=>∑p,if Finset.card p≤k then cash i p else 0) (toll J)
        ((Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1))^s)

variable (J:Request V) (extra:Stage→ℕ→ℝ) (γ:ℝ) (ρ:Premium G J.outputFieldOrder)
    (test:Demand G) (R:Run G) (χ:Chi) (δ:Daisy.Charity.RG12.Decal G)
local notation "fees" => (WilsonLongContactPriorRemittance.decal G).paired δ
local notation "fees₁" => calendar G fees
local notation "Δ" => WilsonGaussianDeterminantTender.joined G J χ fees₁
variable (licensed:WilsonLongContactMayerBooking.Sold J
    (WilsonGaussianDeterminantTender.joined G J χ (calendar G ((WilsonLongContactPriorRemittance.decal G).paired δ))) extra γ ρ test R.kit) (A:NumericSchedule R.family J)

/-- The selected physical house precedes every prior test, regular list, forced list and order. -/
theorem purchased (simple:G.Simple):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family Γ),d.level=m→
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I→
      let lev:=R.alloy.B.a
      let i:=lev.clock.J d.level
      let j:=lev.clock.J (d.level+1)
      let b:=licensed.choose j i
      let S:=lev.clock.op d.level d.period
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      ∃H:WilsonRootedSubmittedTail.CashAt I b, Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
        Crossed J γ R A d b H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
        ∀ k ≤ S.patch.J, ∀ s ≤ S.patch.J, Forced I H k s:=by
  filter_upwards [WilsonLongContactMayerAppointment.original (Γ:=Γ) J Δ extra γ ρ test R licensed A simple,
    WilsonLongContactPriorHeight.purchased (Γ:=Γ) J extra γ ρ test R χ fees₁ licensed A simple,
    ManuscriptQLocalMarkedHeightRun.reserve (Γ:=Γ) R A simple] with m eligible ranked reserve d hm F η I cut
  dsimp only
  obtain ⟨H,renew,cross,offered,sales⟩:=eligible d hm F I cut
  have paid:=(WilsonMovingRoutedMayerStage.shared J χ fees ρ _ _ _ _ _ _ offered).2.2.1
  obtain ⟨A',b,C',u,rv,v,z,B,e,q,n,N,ready,host,visit,rest⟩:=ranked d hm F I cut H
  refine ⟨H,renew,cross,?_⟩
  intro k hk s hs base field E K
  let hats:=(ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base field E K).terms
  exact WilsonLongContactPriorDisbursement.original (k:=k) (s:=s) H Chi.canonical N (A.outputNorm d.level)
    (A.output_norm d.level).threshold (A.output_norm d.level).block hats F.inputRadii (rosterBudget I).radii _
    (ManuscriptQLocalMarkedHeightRun.enrolled I base field E K) (reserve d hm F I cut) paid visit hk hs

end YM.Integration.WilsonLongContactPriorTreasury
