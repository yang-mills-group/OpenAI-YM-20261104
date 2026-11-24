import YM.Integration.WilsonOlderFreshPointReading
import YM.Integration.WilsonOlderFreshGraphLowerConvolution
/-! Signed numerical lower matrix with a specified child at every date.
The coefficient lag and the placed field both use the receiving clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointConvolution
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

open private combined from YM.Integration.WilsonOlderFreshGraphLowerConvolution
open WilsonNeutralPointCourse

variable {G:Gauge}{d kept D N i:ℕ}{σ:ℝ} (R:Run G)(L:Primer.Families R.family)(a:hue G)(depth:d<D)
variable (digit:∀j,Site (R.family.S.block j))(simple:G.Simple)(o:Loc G 1)
variable (cut:i≤N)(active:d≤R.family.path.levels.clock.J (i+1))
variable (b:Letter (R.family.labels.level d))(f:Studio D)

def after (n:Side):PowerSeries (MvPolynomial (Reef.wire G n) ℝ):=
  Kemp.banner d ((Roof.larch (filed R L a depth digit N i) (transfer R L a depth digit N i)) b f) n

include simple o cut active in
theorem natural (n:Side)(e:ℕ)(U:Reef.wire G n→ℝ):
    MvPolynomial.eval U (coeff e (after (N:=N) (i:=i) R L a depth digit b f n))=
      ∑v:Letter (R.family.labels.level d),∑h∈(_root_.Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),
        coeff h.1 (transfer R L a depth digit N i v b)*
          MvPolynomial.eval U (coeff h.2 (Kemp.banner d (filed R L a depth digit N i v f) n)):=by
  let Y:=filed R L a depth digit N i
  let C:=transfer R L a depth digit N i
  have grant:=WilsonNeutralPointCourse.original R L a depth digit N i simple o cut active
  have good(v:Letter (R.family.labels.level d)):Wade o (Y v) d:=
    ((grant.officers v).fare).through (Pose.slotsFits _ v)
  have full:after (N:=N) (i:=i) R L a depth digit b f n=
      ∑v:Letter (R.family.labels.level d),Wine.worm (Reef.wire G n) (C v b)*Kemp.banner d (Y v f) n:=by
    calc
      _=∑v:Letter (R.family.labels.level d),Kemp.banner d ((launch (C v b) (Y v)) f) n:=
        (Rial.flags_sum Finset.univ (fun v=>launch (C v b) (Y v)) o (fun v _=>(good v).launch (C v b)) f n).2
      _=_:=Finset.sum_congr rfl (fun v _=>Kemp.banner_mul (good v) f (C v b) n)
  rw [full]
  simp only [map_sum,PowerSeries.coeff_mul,Wine.worm,PowerSeries.coeff_map,map_mul,MvPolynomial.eval_C]
  rfl

variable (T:(Letter (R.family.labels.level d))→WilsonOlderFreshGraphSlate.Copy G d kept σ)
variable {n:Side}{P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (actors:Unit→Set ℂ)(cap:∀t,‖value actors t‖≤1)(width:0<σ)
variable (books:∀v:Letter (R.family.labels.level d),
    WilsonOlderFreshPointCommission.Published R L a depth i v (⟨N,cut,digit⟩,f) (T v))
attribute [local irreducible] WilsonOlderFreshPointCommission.Published WilsonNeutralPointCourse.filed
  WilsonNeutralPointCourse.transfer after

include simple o cut active cap width books in
theorem original (layout:Layout G)(stock:Finset Age)(t:Affinity.Wallet actors)(e:ℕ)(he:e≤kept)(B:Stationary.Link G n):
    value actors t*(MvPolynomial.eval (FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint S.center)
      (PowerSeries.coeff e (after (N:=N) (i:=i) R L a depth digit b f n)):ℝ)=
      ∑v:Letter (R.family.labels.level d),∑h∈(_root_.Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),
        ((PowerSeries.coeff h.1 (transfer R L a depth digit N i v b):ℝ):ℂ)*
        (FVA1Physical.TwoReset.peek dvd_rfl ((T v).rows S actors) (fun _:Unit=>d) layout stock t h.2 B).part (submitted S).val:=by
  let field:Reef.wire G n→ℝ:=FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint S.center
  let projected (v:(Letter (R.family.labels.level d)))(h:ℕ):ℝ:=MvPolynomial.eval field (PowerSeries.coeff h
    (Kemp.banner d (filed R L a depth digit N i v f) n))
  let actual (v:(Letter (R.family.labels.level d)))(h:ℕ):ℂ:=
    (FVA1Physical.TwoReset.peek dvd_rfl ((T v).rows S actors) (fun _:Unit=>d) layout stock t h B).part (submitted S).val
  have named (v:Letter (R.family.labels.level d))(h:ℕ)(h₀:h≤e):actual v h=value actors t*(projected v h:ℂ):=by
    have paid:=@WilsonOlderFreshPointReading.original G d kept D σ R L a depth i
      v (⟨N,cut,digit⟩,f) (T v) n P H S actors cap width
    have seen:=paid (books v) layout stock t h (h₀.trans he) B
    exact seen
  have target:=natural R L a depth digit simple o cut active b f n e field
  exact combined (I:=(Letter (R.family.labels.level d))) e (value actors t) _ (fun (v:(Letter (R.family.labels.level d))) h=>PowerSeries.coeff h
      (transfer R L a depth digit N i v b)) projected actual
    target named
end YM.Integration.WilsonOlderFreshPointConvolution
end
