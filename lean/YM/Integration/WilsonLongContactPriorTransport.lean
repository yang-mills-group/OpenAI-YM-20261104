import YM.Integration.WilsonLongContactPriorRoots
import YM.Integration.ActualTrajectoryTransport

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorTransport
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


theorem observed (simple:G.Simple) (k p:ℕ) (ε:ℝ) (small:0<ε):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family Γ),d.level=m→
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I→
      let lev:=R.alloy.B.a
      let b:=licensed.choose (lev.clock.J (d.level+1)) (lev.clock.J d.level)
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      ∀H:WilsonRootedSubmittedTail.CashAt I b,∀base field E K,
        let roster:=(ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base field E K).terms
        let names:=fun i=>(roster i).M
        let l:=fun i=>Menu.sumFee (roster i) F.inputRadii
        let D:Match.Alliance H H 1 0:=Match.staple rfl rfl rfl
        let supports:=fun i=>((Beam.marquee H (A.outputNorm d.level)).hard i).support
        ∀(Z:Support (R.family.side d.level d.period)) (selected:Finset ℕ)
            (τ : ℕ → Finset _ → Config G (R.family.side d.level d.period) → ℂ),
          (∀i t U,‖τ i t U‖≤Real.exp ((toll J)*(coverNumber (A.outputNorm d.level).B (supports i):ℝ)))→
          let score:=fun U=>WilsonLongContactPriorRoots.field supports Z selected k
            (fun i t=>cod names H Chi.canonical l H D i U t) (fun i t=>τ i t U)
          (∀U,‖score U‖≤(Z.card:ℝ)*(ε*g^p)) ∧ ∀j (early:j≤d.level) W,
            ‖actualTransport R.family (N:=d.cutoff) (p:=d.period) score early W‖≤(Z.card:ℝ)*(ε*g^p):=by
  filter_upwards [WilsonLongContactPriorHeld.priced (Γ:=Γ) J extra γ ρ test R χ δ licensed A simple k p ε small]
    with m granted d hm F η I valid
  intro lev b g H base y E K roster names l D supports Z selected τ test₀ score
  obtain ⟨cash,cost,hit⟩:=granted d hm F I valid H base y E K
  have bounded U:‖score U‖≤(Z.card:ℝ)*(ε*g^p):=
    WilsonLongContactPriorRoots.observed supports (A.outputNorm d.level).B (toll J) Z selected
      (fun i t=>cod names H Chi.canonical l H D i U t) cash (fun i t=>τ i t U)
      (fun i t=>(cost i t).2 U) (fun i t=>test₀ i t U) hit
  exact ⟨bounded,fun _ early W=>actualTransport_norm_le R.family R.makes d.below.le bounded early W⟩

end YM.Integration.WilsonLongContactPriorTransport
