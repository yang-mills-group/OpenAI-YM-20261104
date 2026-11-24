import YM.Integration.WilsonOlderFreshPointHouseRegistry
import YM.Integration.WilsonOlderFreshGraphPointWallet
import YM.Integration.WilsonMeasuredCashRestriction
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointBasisWallet
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

open WilsonNeutralPointCourse
variable {G:Gauge}{d Q D N i:ℕ}{σ:ℝ}(R:Run G)(L:Primer.Families R.family)(a:hue G)(depth:d<D)
variable (digit:∀j,Site (R.family.S.block j))(b:Letter (R.family.labels.level d))(f:Studio D)
variable (T:Letter (R.family.labels.level d)→WilsonOlderFreshGraphSlate.Copy G d Q σ)
variable {n:Side}(y:Site n)(A:Unit→Set ℂ)(cap:∀t,‖value A t‖≤1)
local notation "α" => (fun (v:Letter (R.family.labels.level d)) (j:ℕ)=>PowerSeries.coeff j
  (WilsonNeutralPointCourse.transfer R L a depth digit N i v b))
local notation "point" => WilsonOlderFreshGraphPointWallet.point y
local notation "letter" => Letter (R.family.labels.level d)
local notation "stock" => Stock.census Unit

include cap in
theorem original (σ₀:0<σ) (ord pieces:ℕ)(room:Q≤ord)(fit:1≤pieces)
    {W:ℝ}(bw:1≤W)(funded:∀v:letter,(∑j,(T v).fare j)≤W*(1+‖f‖))
    (paid:∑v:letter,∑j:Fin (Q+1),|α v j.val|≤W):
    ∃w:letter→ℝ,(∀v:letter,0<w v ∧ (w v)⁻¹≤2*W*(1+‖f‖) ∧
        Scene.Armada ((T v).rows point A) (fun _=>w v) (fun _=>d) σ 1 ord pieces d) ∧
      ∀q≤Q,WilsonMeasuredCashRestriction.total ((stock).fire ()) (fun (v:letter) (_:Unit)=>w v) α (fun _=>1) q ≤
        2*W^2*(1+‖f‖):=by
  classical
  have H(v:letter):∃w:ℝ,0<w ∧ w⁻¹≤2*W*(1+‖f‖) ∧
      Scene.Armada ((T v).rows point A) (fun _=>w) (fun _=>d) σ 1 ord pieces d:=by
    obtain ⟨c,w,c₀,cu,_,wp,bill,restored⟩:=WilsonOlderFreshGraphPointWallet.original (T v) y (funded v) 1 zero_lt_one
    refine ⟨w,wp,?_,(T v).earnings point A σ₀.le cap w 1 wp zero_lt_one (bill.trans cu) room fit le_rfl⟩
    have one:1≤W*(1+‖f‖):=one_le_mul_of_one_le_of_one_le bw (by linarith [norm_nonneg f])
    calc
      w⁻¹≤1+(W*(1+‖f‖)):=by simpa only [max_self,one_mul] using restored
      _≤W*(1+‖f‖)+W*(1+‖f‖):=add_le_add one le_rfl
      _=2*W*(1+‖f‖):=by ring
  choose w cards using H
  refine ⟨w,cards,?_⟩
  intro q hq
  have fees:WilsonMeasuredCashRestriction.total ((stock).fire ()) (fun (v:letter) (_:Unit)=>w v) α (fun _=>1) Q ≤
      (∑v:letter,∑j:Fin (Q+1),|α v j.val|)* (2*W*(1+‖f‖)):=by
    unfold WilsonMeasuredCashRestriction.total WilsonEmittedJoinedFares.cash
    simp only [Fintype.sum_prod_type,Poly.toll,Census.fire,Finset.prod_singleton,mul_one,Finset.sum_mul]
    exact Finset.sum_le_sum (fun v _=>Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (cards v).2.1 (abs_nonneg _)))
  have pos:0≤2*W*(1+‖f‖):=by positivity
  have small:=WilsonMeasuredCashRestriction.narrow ((stock).fire ()) (fun (v:letter) (_:Unit)=>w v) α (fun _=>1)
    hq (fun v=>by simpa [Poly.toll,Census.fire] using (cards v).1.le) (fun _=>zero_le_one)
  calc
    _ ≤ _:=small
    _ ≤ _:=fees
    _ ≤ W*(2*W*(1+‖f‖)):=mul_le_mul_of_nonneg_right paid pos
    _ = _:=by ring

end YM.Integration.WilsonOlderFreshPointBasisWallet
end
