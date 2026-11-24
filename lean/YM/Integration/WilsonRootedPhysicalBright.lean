import YM.Integration.WilsonRootedPhysicalLocalGerm
import YM.Integration.WilsonMovingPhysicalChartlet
import YM.Integration.WilsonMovingLogForecast
import YM.UVExt.TotalPeriod

/-! The actual deposited-station living page and its originally issued five Juniper sensors. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalBright
open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March
open Opera Height Beam Song Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open ThroughLaunch Next.Foundations WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open Juniper Juniper.Bright Boulevard
open scoped Topology BigOperators Classical

variable {G : Gauge}

def Eligible : Prediction G := fun {_} {D} {A} K=> Bright.Gems D K.shape A.post A.delay

/-- The original Juniper shell budget is requestable before booking the shared physical run. -/
theorem prepaid : FundedPredictionSupply.AllPrices (@Eligible G) :=by
  intro s prices target expense charted programs wages baton wanting
  refine ⟨fun _=>0,?_⟩
  intro l _ D w U Z postages scouts θ requests post V _
  let M:Metals G:=⟨ThroughLaunch.raise s l,ThroughLaunch.raging s prices,chart G,chart_ok G⟩
  obtain ⟨W,later,h⟩:=(Bright.charging G).buy (X:=M) Z post V
  refine ⟨W,later,?_⟩
  intro W' after bar wait tariff funded _alloy η q E X J K b sheltered working divides
  exact (Bright.charging G).mono h after

variable (R : Run G) {N m per : ℕ}
local notation "β" => R.family.path.β N per (m+1)
local notation "δ" => (R.alloy.B.a.S.oneStep m per).exact_size
local notation "B" => R.alloy.B.a.budget m
local notation "α" => R.alloy.B.kin.alpha N m
local notation "cₘ" => R.family.side m per
local notation "L" => Meadow.studio (Bright.miner R.kit m) (B).B

/-- A buyer on the original delay puts every actual period in the represented sensor range. -/
lemma room (he : Eligible R.kit) (m per : ℕ) : 2*Bright.home R.kit m < (R.family.side m per).val :=
  Bright.highEnough R.kit he per

/-- This is the authentic living row evaluated on the actual incumbent physical Cash. -/
def livingAt (P:Station R N per m) (n:ℕ) : Trio.Offer G cₘ :=
  Bright.living Chi.canonical P.guide (Bright.mast (R.alloy.B.a.clock.J (m+1))) (Bright.flora P.guide n) (B).B n α

/-- The component comparison needs no empty-regular-occurrence premise on the upper rep. -/
theorem held (hm:m<N) (P:Station R N per m) (W:Bright.Guidebook R.kit N m β)
    (large:2*Bright.home R.kit m < (cₘ).val) (n:ℕ):
    Trio.CompatibleP B L (livingAt R P n) (fun i=>Bright.stones R.kit W i n):=by
  let X:=R.family.path.rep N per (m+1)
  have incoming:=((R.T.sticks N per).prices (m+1) (Nat.zero_le _) hm).1
  have path : X.path=R.alloy.B.kin.path N (m+1):=
    incoming.path.trans (congrFun (congrFun R.alloy.B.bases N) (m+1))
  have point : X.p=R.alloy.B.a.budget (m+1):=incoming.point
  have issue : SeekR R.kit.shape R.alloy N m δ P.guide := P.price
  exact Bright.mirrorWarp R.kit δ hm (WilsonMovingPhysicalChartlet.band R hm) W P.guide rfl path point issue large n

/-- At every tested grade use the same five actual finite pages, with their original Cash receipts. -/
theorem original (he : Eligible R.kit) (hm:m<N) :
    ∃W:Bright.Guidebook R.kit N m β,
      (∀i,SeekR R.kit.shape R.alloy N m (Bright.sews R.kit m i) (W.pages i)) ∧
      ∀P:Station R N per m,∀n:ℕ,Trio.CompatibleP B L (livingAt R P n) (fun i=>Bright.stones R.kit W i n):=by
  obtain ⟨W,book⟩:=WilsonMovingPhysicalChartlet.sensors (per:=per) R hm
  exact ⟨W,fun i=>(book i).1,fun P n=>held R hm P W (room R he m per) n⟩

/-- Every already-selected run has the same actual comparison at all cofinally large periods. -/
theorem cofinal (m:ℕ) : ∀ᶠper:ℕ in atTop,∀N:ℕ,∀_hm:m<N,
    ∃W:Bright.Guidebook R.kit N m (R.family.path.β N per (m+1)),∀P:Station R N per m,∀n:ℕ,
      Trio.CompatibleP (R.alloy.B.a.budget m) (Meadow.studio (Bright.miner R.kit m) (R.alloy.B.a.budget m).B)
        (livingAt R P n) (fun i=>Bright.stones R.kit W i n):=by
  filter_upwards [(UVExt.Paths.allLarger R.alloy.B.a m).eventually_ge_atTop (2*Bright.home R.kit m+1)] with n hn N hm
  obtain ⟨W,_⟩:=WilsonMovingPhysicalChartlet.sensors (per:=n) R hm
  exact ⟨W,fun P k=>held R hm P W (Nat.lt_of_succ_le hn) k⟩

end YM.Integration.WilsonRootedPhysicalBright
