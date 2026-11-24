import YM.Integration.WilsonOlderFreshGraphLowerReading
import YM.Integration.WilsonNeutralLowerColumns

/-! True signed lower records with the previously announced catalogues. Each
transition coefficient has an explicit coupling lag before deployment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphLowerConvolution
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
private theorem combined {I:Type}[Fintype I] (e:ℕ)(weight:ℂ)(target:ℝ)
    (matrix published:I→ℕ→ℝ)(heard:I→ℕ→ℂ)
    (output:target=∑v:I,∑h∈(_root_.Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),matrix v h.1*published v h.2)
    (source:∀v k,k≤e → heard v k=weight*(published v k:ℂ)):
    weight*(target:ℂ)=∑v:I,∑h∈(_root_.Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),(matrix v h.1:ℂ)*heard v h.2:=by
  rw [output]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _=>Finset.sum_congr rfl (fun h hm=>?_))
  have sum:h.1+h.2=e:=_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hm
  rw [source v h.2 (by omega)]
  exact mul_left_comm _ _ _

open WilsonNeutralFiledFieldReversion
variable {G:Gauge}{d kept D N i:ℕ}{σ:ℝ} (R:Run G)(L:Primer.Families R.family)(a:hue G)(depth:d<D)
variable {bound:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical bound R.kit)
variable (simple:G.Simple)(o:Loc G 1)(cut:i≤N)(active:d≤R.family.path.levels.clock.J (i+1))
variable (b:Letter (R.family.labels.level d))(f:Studio D)
variable (T:(Letter (R.family.labels.level d))→WilsonOlderFreshGraphSlate.Copy G d kept σ)
variable {n:Side}{P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (actors:Unit→Set ℂ)(cap:∀t,‖value actors t‖≤1)(width:0<σ)
variable (books:∀v:(Letter (R.family.labels.level d)),WilsonOlderFreshGraphDatedSalary.Published R L a depth i v ⟨⟨N,cut⟩,f⟩ (T v))
attribute [local irreducible] WilsonOlderFreshGraphDatedSalary.Published Primer.fieldCoeffs Primer.fieldStep WilsonNeutralFiledFieldReversion.after
include grant simple o cut active cap width books in
theorem original (layout:Layout G)(stock:Finset Age)(t:Affinity.Wallet actors)(e:ℕ)(he:e≤kept)(B:Stationary.Link G n):
    value actors t*(MvPolynomial.eval (FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint S.center)
      (PowerSeries.coeff e (after R L a depth N i b f n)):ℝ)=
      ∑v:(Letter (R.family.labels.level d)),∑h∈(_root_.Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),
        ((PowerSeries.coeff h.1 (Primer.fieldStep R.family a L depth N i v b):ℝ):ℂ)*
        (FVA1Physical.TwoReset.peek dvd_rfl ((T v).rows S actors) (fun _:Unit=>d) layout stock t h.2 B).part (submitted S).val:=by
  let field:Reef.wire G n→ℝ:=FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint S.center
  let projected (v:(Letter (R.family.labels.level d)))(h:ℕ):ℝ:=MvPolynomial.eval field (PowerSeries.coeff h
    (Kemp.banner d (Primer.fieldCoeffs R.family a L depth N i v f) n))
  let actual (v:(Letter (R.family.labels.level d)))(h:ℕ):ℂ:=
    (FVA1Physical.TwoReset.peek dvd_rfl ((T v).rows S actors) (fun _:Unit=>d) layout stock t h B).part (submitted S).val
  have named (v:Letter (R.family.labels.level d))(h:ℕ)(h₀:h≤e):actual v h=value actors t*(projected v h:ℂ):=by
    have paid:=@WilsonOlderFreshGraphLowerReading.original G d kept D σ R L a depth i
      v ⟨⟨N,cut⟩,f⟩ (T v) n P H S actors cap width
    have seen:=paid (books v) layout stock t h (h₀.trans he) B
    exact seen
  have target:=WilsonNeutralLowerColumns.original (G:=G) (d:=d) (D:=D) (U:=bound) R L a depth grant N i simple o cut active n b f e field
  exact combined (I:=(Letter (R.family.labels.level d))) e (value actors t) _ (fun (v:(Letter (R.family.labels.level d))) h=>PowerSeries.coeff h
      (Primer.fieldStep R.family a L depth N i v b)) projected actual
    target named
end YM.Integration.WilsonOlderFreshGraphLowerConvolution
end
