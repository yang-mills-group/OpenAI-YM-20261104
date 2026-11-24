import YM.Integration.WilsonLongContactPriorTreasury

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorHeld
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


/-- Every housing admitted to the same b inherits the generated hard budget. -/
theorem original (simple:G.Simple):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family Γ),d.level=m→
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I→
      let lev:=R.alloy.B.a
      let b:=licensed.choose (lev.clock.J (d.level+1)) (lev.clock.J d.level)
      ∀H:WilsonRootedSubmittedTail.CashAt I b,
        ∀ k ≤ (lev.clock.op d.level d.period).patch.J, ∀ s ≤ (lev.clock.op d.level d.period).patch.J,
          WilsonLongContactPriorTreasury.Forced I H k s:=by
  filter_upwards [WilsonLongContactPriorHeight.purchased (Γ:=Γ) J extra γ ρ test R χ fees₁ licensed A simple,
    ManuscriptQLocalMarkedHeightRun.reserve (Γ:=Γ) R A simple] with m ranked reserve d hm F η I cut
  dsimp only
  intro H k hk s hs base field E K
  have offer:=(WilsonLongContactMayerAppointment.booking (Γ:=Γ) J Δ extra γ ρ test R licensed d).1
  have paid:=(WilsonMovingRoutedMayerStage.shared J χ fees ρ _ _ _ _ _ _ offer).2.2.1
  obtain ⟨A',b,C',u,rv,v,z,B,e,q,n,N,ready,host,visit,rest⟩:=ranked d hm F I cut H
  let hats:=(ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base field E K).terms
  exact WilsonLongContactPriorDisbursement.original (k:=k) (s:=s) H Chi.canonical N (A.outputNorm d.level)
    (A.output_norm d.level).threshold (A.output_norm d.level).block hats F.inputRadii (rosterBudget I).radii _
    (ManuscriptQLocalMarkedHeightRun.enrolled I base field E K) (reserve d hm F I cut) paid visit hk hs

/-- The tolerance and output order precede every choice of pose, forest, house, and submitted row. -/
theorem priced (simple:G.Simple) (k p:ℕ) (ε:ℝ) (small:0<ε):
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
        ∃cash:ℕ→Finset _→ℝ,(∀i t,0≤cash i t ∧ ∀U,‖cod names H Chi.canonical l H D i U t‖≤cash i t) ∧
        Ac.Hit (fun i=>((Beam.marquee H (A.outputNorm d.level)).hard i).support) (A.outputNorm d.level).B
          (fun i=>∑t,if Finset.card t≤k then cash i t else 0) (toll J) (ε*g^p):=by
  have deep:Tendsto R.alloy.B.a.clock.J atTop atTop:=R.family.path.levels.fits.deep
  filter_upwards [original (Γ:=Γ) J extra γ ρ test R χ δ licensed A simple,
    (deep.comp (tendsto_add_atTop_nat 1)).eventually (eventually_ge_atTop (max k (p+1))),
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes ε small)]
    with m earned hi rate d hm F η I cut
  dsimp only
  subst m
  intro H base field E K
  have hJ:(R.alloy.B.a.clock.op d.level d.period).patch.J=R.alloy.B.a.clock.J (d.level+1):=
    (Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below).atStep
  change max k (p+1)≤R.alloy.B.a.clock.J (d.level+1) at hi
  rw [←hJ] at hi
  obtain ⟨b,pos,paid⟩:=earned d rfl F I cut H k ((le_max_left ..).trans hi) (p+1)
    ((le_max_right ..).trans hi) base field E K
  let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  have hg:0≤g:=(IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below).le
  have hs:g≤ε:=(rate d.cutoff d.period d.below).le
  exact ⟨b,pos,fun site=>Push.AbsoluteSums.budget_loosen (paid site) (by rw [pow_succ, mul_comm ε];exact mul_le_mul_of_nonneg_left hs (pow_nonneg hg _))⟩

end YM.Integration.WilsonLongContactPriorHeld
