import YM.Integration.WilsonConditionalTaylorWheelTorusReed
import YM.Integration.WilsonConditionalTaylorWheelFoldedYields
import YM.Integration.WilsonConditionalTaylorWheelAuthStrip

/-! The changing full previous marked field has one normalized cover transfer.
Both calculations take the limit of the same finite signed joint numerator.
The independent calculation preserves a positive rooted strip. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelMarkedLimit
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open FormalBulk08 Flat Reef Jets Orb Wick Series Next.Free MSbar.Rolling MSbar.Cacao
open Work.F03 Work.F05 Work.F08 PowerSeries Stationary Lotus Shore
open Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Winding AnalyticNext.QuarticMatch.Sheets Next.Foundations
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def upper (N j q:ℕ) (Z:Mesa.Pot G):Mesa.Pot G:=
  windsT (loose V j) (V).clock.kernel R.metals.O (shuttleM (conditional V N j))
    (shuttleM (feedA V N j)) (actionW V R.metals.O N (j+1)) q Z

include simple in
theorem measured (N j q e r:ℕ) (live:j<N) (T:Era G ℝ) (auth:Auth q T):
    Bends 0 (fun n=>WilsonConditionalTaylorWheelTorusReed.filed R N j q T.1 n e r)
      (upper R N j q T.2 e r):=by
  exact river (loose V j) (V).clock.kernel R.metals.O _ _ _ (b j) R.alloy.B.ratio (resin V N j live)
    (fun a t=>WilsonConditionalTaylorWheelFoldedYields.original R simple N (j+1) live a t)
    q 0 (U:=T.1) (fun i t=>by rw [coat0];exact auth.wing i t) e r

include simple in
theorem finite (N j per E e r q:ℕ) (he:e≤E) (live:j<N)
    (history:WilsonConditionalTaylorWheelVacuumHistory.Identified R u N (j+1) E)
    (T:Era G ℝ) (auth:Auth q T):
    let P:=destination V N j
    let n:=R.family.side j per
    let W:=Dove.model V wood b R.metals.O u N (j+1)
    WilsonConditionalTaylorWheelTorusReed.filed R N j q T.1 n e r=
      rancho (Reef.tossed P R.metals.O (b j) (wood j) n (tags j n)
        (Mesa.stone W (n*P.L)) (Blue.flash (T.1 (n*P.L)))) e r:=by
  intro P n W
  let B:=WilsonConditionalTaylorWheelTorusReed.filed R N j q T.1 n
  have old:=emera_far V simple R.alloy.B.ratio (N:=j+1) (m:=N) live (n*P.L)
  have shape:shellK q B:=reed_band _ _ _ _ q old.1 R.alloy.B.ratio (auth.span _)
  have smooth:∀g,Pure (B g):=fun g=>reed_smooth _ _ _ _ q R.metals.O _ (auth.pale _) g
  have declared:=WilsonConditionalTaylorWheelTorusReed.received R simple u tags N j per E q live history T.1 auth.span auth.pale
  have angular:=WilsonConditionalTaylorWheelTensors.actual B q shape smooth e r
  exact angular.symm.trans (congrArg (marble r) (declared e he))

include simple in
theorem original (N j E e r q cap:ℕ) (live:j<N) (he:e≤E) (width:q≤cap)
    (history:WilsonConditionalTaylorWheelVacuumHistory.Identified R u N (j+1) E)
    (T:Era G ℝ) (auth:Auth q T) (a y:Loc G 1):
    let P:=destination V N j
    let W:=Dove.model V wood b R.metals.O u N (j+1)
    let Z:=Kemp.braise P (wood j) W T.2 R.metals.O (b j) cap
    upper R N j q T.2 e r=Z e r ∧
      ∃s:ℝ,0<s ∧ Kemp.Kalm s (Kemp.chief P (0,a) y) (upper R N j q T.2 e r)
      (fun n=>rancho (Reef.tossed P R.metals.O (b j) (wood j) n (tags j n)
        (Mesa.stone W (n*P.L)) (Blue.flash (T.1 (n*P.L)))) e r):=by
  intro P W Z
  have original:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  obtain ⟨s,pos,money⟩:=WilsonConditionalTaylorIndependentMarked.all P (wood j) W T.2 R.metals.O (b j)
    (tags j) (fun n=>Blue.flash (T.1 n)) original R.alloy.B.ratio ((V).clock.adm j) e r cap width
    (WilsonConditionalTaylorWheelAuthStrip.cover T auth) (WilsonConditionalTaylorWheelAuthStrip.finite T auth)
    (0,a) y (fun i _ d _=>WilsonConditionalTaylorWheelAuthStrip.original T auth a i d)
  have eqn:upper R N j q T.2 e r=Z e r:=by
    funext x
    have field:=((measured R simple N j q e r live T auth).point x).comp (WilsonUniformUnmarkedSpatialLimit.sides R j)
    have independent:=(money.1 x).comp (WilsonUniformUnmarkedSpatialLimit.sides R j)
    apply tendsto_nhds_unique field
    refine independent.congr' (Eventually.of_forall (fun per=>?_))
    exact (congrFun (finite R simple u tags N j per E e r q he live history T auth)
      (foldUnder (R.family.side j per) ∘ x)).symm
  exact ⟨eqn,s,pos,eqn.symm ▸ money⟩
end YM.Integration.WilsonConditionalTaylorWheelMarkedLimit
end
