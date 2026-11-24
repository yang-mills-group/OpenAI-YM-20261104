import YM.Integration.WilsonOriginalPrimerCourseRead
import YM.Integration.WilsonOriginalPrimerLandedRay
import YM.Integration.WilsonThermometerPositionFilmSelf

/-! Read any previously issued lower basis column directly on its original
side and at its selected site, on every direction of its advertised stamp. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphLowerReading
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Earn
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker AllOrder.Ker.Start
open AllOrder.Haiku QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary
open Push.PriceCompiler Primer AllOrder.Ink Primitives.TwoWave WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase WilsonOlderFreshGraphPainter
open WilsonOlderFreshGraphAward WilsonOlderFreshGraphSlate WilsonElectedPrimaryTensor
open scoped Topology BigOperators Classical
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

open WilsonOlderFreshGraphArmada
variable {G:Gauge}{d kept D:ℕ}{σ:ℝ} (R:Run G)(L:Primer.Families R.family)(a:hue G)(depth:d<D)
variable {i:ℕ}(w:Letter (R.family.labels.level d))(p:Ballot i D)
variable (T:WilsonOlderFreshGraphSlate.Copy G d kept σ)
variable {n:Side}{P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (actors:Unit→Set ℂ)(cap:∀t,‖value actors t‖≤1)(width:0<σ)
include cap width in
theorem original (book:WilsonOlderFreshGraphDatedSalary.Published R L a depth i w p T)
    (layout:Layout G)(stock:Finset Age)(t:Affinity.Wallet actors)(j:ℕ)(active:j≤kept)(B:Stationary.Link G n):
    (FVA1Physical.TwoReset.peek dvd_rfl (T.rows S actors) (fun _:Unit=>d) layout stock t j B).part (submitted S).val=
    value actors t*(MvPolynomial.eval (FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint S.center)
      (PowerSeries.coeff j (Kemp.banner d (Primer.fieldCoeffs R.family a L depth p.1.1 i w p.2) n)):ℝ):=by
  rw [WilsonThermometerPositionFilmSelf.pupil]
  let Z:=WilsonElectedPrimaryTensor.chart R L a depth i w p n S.center
  have filed(A:Stationary.Link G n):MvPolynomial.eval A (PowerSeries.coeff j (WilsonCoeffUV.Blue.flash Z))=
      ∑l:Fin (kept+1),((T.roll l).folded l j).table n (mingle A (WilsonElectedPrimaryTensor.pin S.center)):=by
    rw [WilsonElectedPrimaryTensor.named]
    exact book ⟨j,by omega⟩ n A (WilsonElectedPrimaryTensor.pin S.center)
  have read:=WilsonOriginalPrimerCourseRead.original S T.roll T.fare σ T.paid T.legal T.positive
    actors cap t width layout stock Z j filed B
  change _=value actors t*_ at read
  refine read.trans ?_
  dsimp only [Z,WilsonElectedPrimaryTensor.chart]
  rw [WilsonOriginalPlacedPrimerInk.tested]
  have same:(fun x:Reef.wire G n=>B (S.center+x.1,x.2))=
      FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint S.center:=by
    funext x
    change B (S.center+x.1,x.2)=B (x.1+S.center,x.2)
    rw [add_comm S.center]
  rw [same]
end YM.Integration.WilsonOlderFreshGraphLowerReading
end
