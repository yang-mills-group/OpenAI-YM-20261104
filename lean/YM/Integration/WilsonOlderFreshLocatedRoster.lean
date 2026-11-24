import YM.Integration.WilsonOlderFreshPointHouseRegistry
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshLocatedRoster
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical


open QuadraticLocal.Advent Sycamore WilsonOlderFreshGraphAllStages WilsonOlderFreshGraphCommonSalary
open WilsonWindowBookPurchase WilsonLimitConstruction.FundedCompanySelection WilsonWindowUniversalSchool
variable {G:Gauge} {φ:ℕ → ℕ}


open WilsonOlderFreshGraphCommonHouse WilsonOlderFreshGraphCompiler WilsonOlderFreshGraphSlate

open WilsonNeutralPointCourse
open WilsonOlderFreshPointRegistry


variable {G:Gauge}(R:Run G)(L:Primer.Families R.family)(a:hue G){d D:ℕ}(depth:d<D)(Q:ℕ)
    (σ:ℕ → ℝ)(m N:ℕ)(digit:∀i,Site (R.family.S.block i))
    (T:∀i,m ≤ i  →  i ≤ N  →  Letter (R.family.labels.level d)  →  Studio D  →  WilsonOlderFreshGraphSlate.Copy G d Q (σ i))

def Booked:Prop:=
  (∀i (lo:m ≤ i)(up:i ≤ N)(b:Letter (R.family.labels.level d))(f:Studio D),
    Filed R L a depth (1/4) digit up b f (T i lo up b f)) ∧
  ∀i,m ≤ i  →  i<N  →  ∀b:Letter (R.family.labels.level d),
    (∑v,∑ν:Fin (Q+1),|PowerSeries.coeff ν.val (transfer R L a depth digit N i v b)|)  ≤ 
      (R.alloy.B.a.clock.hatBeta i)^((1:ℝ)/4)

theorem original (registered:Booked R L a depth Q σ m N digit T):
        ∀j (lo:m  ≤  j)(hi:j<N)(w:Letter (R.family.labels.level d))(f:Studio D),
        let g:=Dawn.throughW (digit j) D (Elm.growL R.family.path.levels j) f
        let H:=T (j+1) (lo.trans (Nat.le_succ j)) hi w g
        let T₀:=fun u=>T j lo hi.le u f
        let μ:=fun u (ν:Fin (Q+1))=>|PowerSeries.coeff ν.val (transfer R L a depth digit N j u w)|
        Filed R L a depth (1/4) digit hi w g H ∧
        (∑x,H.fare x)  ≤  (R.alloy.B.a.clock.hatBeta (j+1))^((1:ℝ)/2)*(1+‖g‖) ∧
        (∀u,Filed R L a depth (1/4) digit hi.le u f (T₀ u)) ∧
        (∀u,(∑x,(T₀ u).fare x)  ≤  R.alloy.B.a.clock.hatBeta j*(1+‖f‖)) ∧
        (∑u,∑ν,μ u ν)  ≤  R.alloy.B.a.clock.hatBeta j ∧
        (∑u,∑ν,μ u ν*(∑x,(T₀ u).fare x))   ≤   R.alloy.B.a.clock.hatBeta j^((1:ℝ)/2)*(1+‖f‖):=by
  classical
  obtain ⟨issued,spent⟩:=registered
  intro j lo hi w f
  let g:=Dawn.throughW (digit j) D (Elm.growL R.family.path.levels j) f
  let T₀:=fun u=>T j lo hi.le u f
  let μ:=fun u (ν:Fin (Q+1))=>|PowerSeries.coeff ν.val (transfer R L a depth digit N j u w)|
  have lower:1  ≤  R.alloy.B.a.clock.hatBeta j:=(R.alloy.B.a.fits.delayed j).le
  have upper:1  ≤  R.alloy.B.a.clock.hatBeta (j+1):=(R.alloy.B.a.fits.delayed (j+1)).le
  have h:=issued (j+1) (lo.trans (Nat.le_succ j)) hi w g
  have p:=fun u=>issued j lo hi.le u f
  have price:(∑u,∑ν,μ u ν)  ≤  (R.alloy.B.a.clock.hatBeta j)^((1:ℝ)/4):=spent j lo hi w
  have small:(R.alloy.B.a.clock.hatBeta j)^((1:ℝ)/4)  ≤  R.alloy.B.a.clock.hatBeta j:=by
    simpa using (Real.rpow_le_rpow_of_exponent_le lower (by norm_num:(1:ℝ)/4  ≤  1))
  refine ⟨h,h.1.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le upper (by norm_num)) (by positivity)),
    p,fun u=>(p u).1.trans (mul_le_mul_of_nonneg_right small (by positivity)),price.trans small,?_⟩
  change (∑u,∑ν,μ u ν*(∑x,(T₀ u).fare x))  ≤  _
  let cash:=(R.alloy.B.a.clock.hatBeta j)^((1:ℝ)/4)*(1+‖f‖)
  calc
    _   ≤   ∑u,∑ν,μ u ν*cash:=Finset.sum_le_sum fun u _=>Finset.sum_le_sum fun ν _=>
      mul_le_mul_of_nonneg_left (p u).1 (abs_nonneg _)
    _ = (∑u,∑ν,μ u ν)*cash:=by simp only [Finset.sum_mul]
    _   ≤   (R.alloy.B.a.clock.hatBeta j)^((1:ℝ)/4)*cash:=mul_le_mul_of_nonneg_right price (by dsimp [cash];positivity)
    _ = _:=by
      dsimp only [cash];rw [←mul_assoc,←Real.rpow_add (by linarith:0<R.alloy.B.a.clock.hatBeta j)];norm_num

end YM.Integration.WilsonOlderFreshLocatedRoster
