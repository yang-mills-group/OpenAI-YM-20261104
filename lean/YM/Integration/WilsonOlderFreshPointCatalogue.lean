import YM.Integration.WilsonOlderFreshGraphPointWallet
import YM.Integration.WilsonOlderFreshPointConvolution
import YM.Integration.WilsonMeasuredUnconditionalCatalogue
/-! The complete signed rooted catalogue for a single selected child.
All declared lower lags and the true unaveraged engineering weight appear
once, on a common original group configuration and valuation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointCatalogue
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


open WilsonNeutralPointCourse WilsonMeasuredTransitionCatalogue WilsonMeasuredOriginalCatalogueUnion

variable {G:Gauge}{d kept D N i:ℕ}{σ:ℝ} (R:Run G)(L:Primer.Families R.family)(a:hue G)(depth:d<D)
variable (digit:∀j,Site (R.family.S.block j))(simple:G.Simple)(o:Loc G 1)
variable (cut:i≤N)(active:d≤R.family.path.levels.clock.J (i+1))
variable (b:Letter (R.family.labels.level d))(f:Studio D)
variable (T:(Letter (R.family.labels.level d))→WilsonOlderFreshGraphSlate.Copy G d kept σ)
variable {n:Side}(y:Site n) (A:Unit→Set ℂ)(cap:∀t,‖WilsonOlderFreshGraphArmada.value A t‖≤1)(width:0<σ)
variable (books:∀v:Letter (R.family.labels.level d),
    WilsonOlderFreshPointCommission.Published R L a depth i v (⟨N,cut,digit⟩,f) (T v))

local notation "S₀" => WilsonOlderFreshGraphPointWallet.point y
local notation "stocks" => Stock.census Unit
local notation "levels" => R.family.path.levels
local notation "letter" => Letter (R.family.labels.level d)
local notation "actors" => Affinity.Wallet A
local notation "mark₀" => WilsonNeutralRenderedColumn.submitted S₀
local notation "code" => (fun _:Unit=>d)
local notation "M₁" => (fun (v:letter) (l:ℕ)=>PowerSeries.coeff l (transfer R L a depth digit N i v b))
local notation "r₁" => (((R.family.S.block i).val:ℝ)^d)
local notation "past" => (fun v:letter=>(T v).rows S₀ A)
variable {I:Type}{P:Earn.Passport n Unit}(F:I→QuadraticLocal.Earn.Row P (Stock.census Unit) G (Affinity.Wallet A))
variable (layout:Layout G)(tape:Finset Age)

local notation "tested" => (fun _:Unit=>F)
local notation "pole₀" => (Launch.index stocks code (mark₀).val+1)

include simple o cut active cap width books in
theorem original (cutoff:ℕ)(ok:cutoff≤kept)(t:actors)
    (outcome:∀e≤cutoff,∀B:Stationary.Link G n,
      (r₁:ℂ)*(peek dvd_rfl F code layout tape t e B).part (mark₀).val=
      WilsonOlderFreshGraphArmada.value A t*(MvPolynomial.eval
        (FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint (S₀).center)
        (PowerSeries.coeff e (WilsonOlderFreshPointConvolution.after (N:=N) (i:=i) R L a depth digit b f n)):ℝ))
    (j:ℕ)(bound:j < pole₀ + cutoff + 1)(u:Directions G n):
    (∑q:WilsonMeasuredTransitionCatalogue.Names Unit letter cutoff,WilsonMeasuredTransitionCatalogue.weight r₁ M₁ q •
      WilsonEmittedFiledGerm.price (WilsonMeasuredOriginalCatalogueUnion.rows tested past) (fun _=>code)
        (fun _=>t) WilsonMeasuredTransitionCatalogue.lag mark₀ (fun _=>layout) (fun _=>tape) j u q)=0:=by
  refine WilsonMeasuredUnconditionalCatalogue.angular tested past d mark₀ t r₁ M₁ layout tape ?_ j bound u
  intro e he B
  rw [Fintype.sum_unique]
  simpa only [Complex.ofReal_pow] using (outcome e he B).trans (WilsonOlderFreshPointConvolution.original R L a depth digit simple o cut active
    b f T S₀ A cap width books layout tape t e (he.trans ok) B)

end YM.Integration.WilsonOlderFreshPointCatalogue
end
