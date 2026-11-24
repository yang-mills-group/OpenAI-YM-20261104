import YM.Integration.WilsonLongContactMayerAppointment
import YM.Integration.WilsonGaussianDeterminantTender
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorHeight
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
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Marker.Census V}
    (J:Request V) (extra:Stage→ℕ→ℝ) (γ:ℝ)
    (ρ:Premium G J.outputFieldOrder) (test:Demand G) (R:Run G) (χ:Chi) (δ:Daisy.Charity.RG12.Decal G)
    (licensed:WilsonLongContactMayerBooking.Sold J
      (WilsonGaussianDeterminantTender.joined G J χ δ) extra γ ρ test R.kit)
    (A:NumericSchedule R.family J)

theorem purchased (simple:G.Simple):
    ∀ᶠm:ℕ in atTop, ∀(d:LocalFormal.Datum R.family Γ), d.level=m→
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I→
      let i:=R.alloy.B.a.clock.J d.level
      let j:=R.alloy.B.a.clock.J (d.level+1)
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      ∀H:WilsonRootedSubmittedTail.CashAt I (licensed.choose j i),
       ManuscriptQLocalMarkedHeightRun.High (expense J (R.kit.target j i)) H J Γ ((2*g)^(J.order+1)):=by
  have warm:=(tendsto_add_atTop_nat 1).eventually (QLocalRequestedSectorIntake.affordable (J:=J) R simple)
  filter_upwards [ManuscriptQLocalVacuumCash.funds (Γ:=Γ) R A simple,warm] with m charge money d hm F η I admitted
  dsimp only
  intro H
  subst m
  let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  let old:=ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) F.layers g 1
  let Y:=QLocalInheritedRegularSlots.carrier old
  have row:=ManuscriptQLocalVacuumFamily.bought I admitted 1
  have hin:=QLocalRequestedSectorIntake.intake R I admitted (I.inherited_bound.trans (money d.cutoff d.period d.below))
  have e:=ManuscriptQLocalVacuumCash.intake R A d F I admitted hin (charge d rfl F I)
  have orig:=QLocalInheritedRegularSlots.intake old e
  let S:=R.alloy.B.a.clock.op d.level d.period
  let T:=ships R.alloy.B d.cutoff d.level d.period
  let x:=R.alloy.B.a.clock.hatBeta d.level
  let β:=betaF G x S.patch.L
  have win:=(WilsonLongContactMayerAppointment.booking (Γ:=Γ) J _ extra γ ρ test R licensed d).1.window
  have works:Works _ S.patch.L x S T:=⟨orig.ready,rfl,by rw [add_comm 1];exact R.alloy.B.a.fits.sizeT _ _⟩
  have stamp:=protocol (n:=d.period) R.alloy.B d.below R.kit.pledging.conducts.full
  apply ManuscriptQLocalMarkedHeightRun.certificate _ H J Γ (i:=S.patch.J)
    (h:=(teller J (query R.metals.p R.metals.K (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))).below) win.analytic.1.1.1 works stamp orig.cap.labels.boundE
  have hb:R.alloy.B.a.clock.hatBeta (d.level+1)=β:=Application.clock_next R.alloy.B.a d.level d.period
  have hp:0<β:=zero_lt_one.trans_le win.analytic.1.1.1.1
  have hh:(Real.sqrt β)⁻¹≤2*g:=by
    rw [←hb]
    exact (IterationFour.Currency.hat_g R.makes d.cutoff d.period (d.level+1) d.below).1
  have hpow:(Real.sqrt β)⁻¹=β^(-(1/2:ℝ)):=by rw [Real.rpow_neg hp.le,Real.sqrt_eq_rpow]
  calc
    β^(-((J.order:ℝ)+1)/2)=((Real.sqrt β)⁻¹)^(J.order+1):=by
      rw [hpow,←Real.rpow_natCast,←Real.rpow_mul hp.le]
      congr 1
      push_cast
      ring
    _ ≤ _:=pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg β)) hh _

end YM.Integration.WilsonLongContactPriorHeight
