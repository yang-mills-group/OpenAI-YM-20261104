import YM.Integration.WilsonPointChildHalfCell
import YM.Integration.WilsonPointChildTestCoordinates
import YM.Integration.WilsonNeutralPointWeakIncome
import YM.Integration.WilsonWindowReportingPace

/-! All cutoff births and the native pretest tensor on a single enrolled
    physical course. Each rooted width is settled before the period and test. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildFiledTest
open YM Lattice RG Wilson Filter Function Finset PowerSeries Next.Free Stationary PhysicalNext.Repeat.Legato Next.Foundations
open Laurent FormalBulk08 Flat Lava Lotus Shore Mesa Gorge Rift Kemp Pose Aster Roof Dawn
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildFiledPress WilsonNeutralPointCourse WilsonPointChildNormalizedWidth
open scoped Topology ContDiff ENNReal Matrix BigOperators Classical
variable {G:Gauge}

def Filed (R:Run G):Prop:=∀{d D:ℕ}(wood:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)
    (o:Loc G 1)(E:ℕ){η:ℝ},0<η→∀ᶠi:ℕ in atTop,∀N,i≤N→
    (∀digit:∀j,Site (R.family.S.block j),Wallet o (R.family.labels.level d)
      (filed R wood a depth digit N i) (width R i) E ((R.family.path.levels.clock.hatBeta i)^η)) ∧
    ∀v:Letter (R.family.labels.level d),∀e≤E,∀r,∃K:chain (edgeL G) r→Pen (fun _:Unit=>D) {()},
      (∀x (p:Scroll D),touch (fun _:Unit=>page D p) {()} (K x)=
        filed R wood a depth (fun _=>0) N i v (WilsonPointChildTestCoordinates.physical p) e r x) ∧
      Wig terrain (fun _:Unit=>0) (width R i)
        (WilsonPointChildTestJet.rent D*((R.family.path.levels.clock.hatBeta i)^η)) {()} K

theorem original (R:Run G)(simple:G.Simple){U:ℕ→ℕ}(formal:WilsonWindowFormalPurchase.Canonical U R.kit)
    (strong:WilsonNeutralPointForecast.Filed R.kit)(weakly:WilsonNeutralPointWeakForecast.Filed R.kit)
    (slow:WilsonWindowReportingPace.Slow R.kit):Filed R:=by
  intro d D wood a depth o E η hp
  obtain ⟨weak,fwd⟩:=WilsonNeutralPointWeakIncome.original R wood a depth o simple formal strong weakly E
  have income:=WilsonPointChildInverseIncome.income R wood a depth o simple formal weak fwd
  filter_upwards [WilsonPointChildWidthHistory.original R wood a depth o simple formal slow.2 E income hp,
    WilsonPointChildHalfCell.original R wood a depth o simple formal slow.2 weak fwd hp] with i all whole
  intro N live
  refine ⟨all N live,?_⟩
  intro v e cap r
  obtain ⟨K,read,priced⟩:=whole N live v e cap r
  refine ⟨K,?_,priced⟩
  intro x p
  exact read x (fun _:Unit=>page D p) (WilsonPointChildTestCoordinates.physical p)
    (fun t=>WilsonPointChildTestCoordinates.common p _)

end YM.Integration.WilsonPointChildFiledTest

