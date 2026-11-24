import YM.Integration.WilsonLongContactPriorSoft
import YM.Integration.WilsonLongContactPriorBank

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorFullGas
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


theorem purchased (simple:G.Simple) (p:ℕ) (ε:ℝ) (small:0<ε):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family Γ),d.level=m→
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I→
      let lev:=R.alloy.B.a
      let b:=licensed.choose (lev.clock.J (d.level+1)) (lev.clock.J d.level)
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      ∀H:WilsonRootedSubmittedTail.CashAt I b,∀base field E K,
        let roster:=(ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base field E K).terms
        WilsonLongContactPriorHaar.Returned H Chi.canonical (A.outputNorm d.level) roster F.inputRadii ∧
        WilsonLongContactPriorSoft.Filed H Chi.canonical (A.outputNorm d.level) roster F.inputRadii (ε*g^p) ∧
        WilsonLongContactPriorSoft.Report H Chi.canonical (A.outputNorm d.level) roster F.inputRadii (ε*g^p):=by
  classical
  have half:0<(1/2:ℝ):=by norm_num
  filter_upwards [WilsonLongContactPriorBank.purchased (Γ:=Γ) J extra γ ρ test R χ δ licensed A simple p ε small,
    WilsonLongContactPriorBank.purchased (Γ:=Γ) J extra γ ρ test R χ δ licensed A simple 0 (1/2) half]
    with m high low d hm F η I cut
  intro lev b g H base y E K roster
  have tall:=high d hm F I cut H base y E K
  have flat:=low d hm F I cut H base y E K
  have haar:=WilsonLongContactPriorHaar.received H Chi.canonical (A.outputNorm d.level) roster F.inputRadii tall.1
  have hw:∀v,0<F.inputRadii v:=(rosterBudget I).radii
  have fee:WilsonLongContactPriorSoft.Filed H Chi.canonical (A.outputNorm d.level) roster F.inputRadii (ε*g^p):=by
    intro U
    let D:Match.Alliance H H 1 0:=Match.staple rfl rfl rfl
    let P:=A.outputNorm d.level
    let C:=PhysicalNext.Repeat.Refrain.read H D Chi.canonical (Beam.marquee H P).reg
      (Height.serve H D Chi.canonical (Beam.lit H)).logRead
    let names:=fun i=>(roster i).M
    let l:=fun i=>Menu.sumFee (roster i) F.inputRadii
    let hard:=WilsonLongContactPriorModes.hard roster F.inputRadii (fun i t=>cod names H Chi.canonical l H D i U t)
    let target:=min (ε*g^p) (1/2:ℝ)
    have gp:0<g:=IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
    have tz:0≤target:=le_min (mul_nonneg small.le (pow_nonneg gp.le _)) half.le
    have ts:target≤1:=(min_le_right _ _).trans (by norm_num)
    refine (WilsonLongContactPriorGasResidual.paid C P F.inputRadii hard hw U target ts tz ?_).trans (min_le_left _ _)
    intro x selected
    have h:=(tall.2 {x} selected).1 U
    have z:=(flat.2 {x} selected).1 U
    have hx:((({x}:Finset (Site (R.family.side d.level d.period))).card:ℕ):ℝ)=1:=by exact_mod_cast Finset.card_singleton x
    apply le_min
    · exact h.trans_eq (congrArg (·*(ε*g^p)) hx |>.trans (one_mul _))
    · exact z.trans_eq (congrArg (·*((1/2)*(g^0))) hx |>.trans (by rw [one_mul,pow_zero,mul_one]))
  exact ⟨haar,fee,WilsonLongContactPriorSoft.original H Chi.canonical (A.outputNorm d.level) roster F.inputRadii hw _ haar fee⟩

end YM.Integration.WilsonLongContactPriorFullGas
