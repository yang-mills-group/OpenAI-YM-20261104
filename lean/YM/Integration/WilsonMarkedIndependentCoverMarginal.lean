import YM.Integration.WilsonMarkedIndependentFoldedIntegral
import YM.Integration.WilsonConditionalTaylorWheelAuthStrip

/-! The independently defined occupied cover kernel on the same funded Wilson course. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentCoverMarginal
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open AnalyticNext.QuarticMatch.Sheets
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Soil
open FormalBulk08.Kemp
open WilsonMarkedIndependentFoldedIntegral
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)

variable (u:G.ColorIndex) (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

theorem angular (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(live:j<N)(q e r:ℕ)(T:Mer.Era G ℝ)(auth:Auth q T)(n:Side):
    let P:=destination V N j
    let W:=Dove.model V wood b R.metals.O u N (j+1)
    folded R N j q T.1 n e r=rancho (Reef.tossed P R.metals.O (b j) (wood j) n (tags j n)
      (Mesa.stone W (n*P.L)) (Blue.flash (T.1 (n*P.L)))) e r:=by
  intro P W
  let B:=folded R N j q T.1 n
  have old:=emera_far V simple R.alloy.B.ratio (N:=j+1) (m:=N) live (n*P.L)
  have shape:shellK q B:=reed_band _ _ _ _ q old.1 R.alloy.B.ratio (auth.span _)
  have smooth:∀g,Pure (B g):=fun g=>reed_smooth _ _ _ _ q R.metals.O _ (auth.pale _) g
  have declared:=WilsonMarkedIndependentFoldedIntegral.finite R u tags simple v funded live q T auth n
  have raw:=WilsonConditionalTaylorWheelTensors.actual B q shape smooth e r
  exact raw.symm.trans (congrArg (fun A=>rancho A e r) declared)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(live:j<N)(e r q cap:ℕ)(width:q≤cap)
    (T:Mer.Era G ℝ)(auth:Auth q T)(a y:Loc G 1):
    let P:=destination V N j
    let W:=Dove.model V wood b R.metals.O u N (j+1)
    let Z:=Kemp.braise P (wood j) W T.2 R.metals.O (b j) cap
    upper R N j q T.2 e r=Z e r ∧
      ∃s:ℝ,0<s ∧ Kemp.Kalm s (Kemp.chief P (0,a) y) (Z e r)
      (fun n=>rancho (Reef.tossed P R.metals.O (b j) (wood j) n (tags j n)
        (Mesa.stone W (n*P.L)) (Blue.flash (T.1 (n*P.L)))) e r):=by
  intro P W Z
  have original:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  obtain ⟨s,pos,money⟩:=WilsonConditionalTaylorIndependentMarked.all P (wood j) W T.2 R.metals.O (b j)
    (tags j) (fun n=>Blue.flash (T.1 n)) original R.alloy.B.ratio ((V).clock.adm j) e r cap width
    (WilsonConditionalTaylorWheelAuthStrip.cover T auth) (WilsonConditionalTaylorWheelAuthStrip.finite T auth)
    (0,a) y (fun i _ d _=>WilsonConditionalTaylorWheelAuthStrip.original T auth a i d)
  refine ⟨?_,s,pos,money⟩
  funext x
  apply tendsto_nhds_unique ((recorded R simple live q e r T auth).point x)
  refine (money.1 x).congr' (Eventually.of_forall (fun n=>?_))
  exact (congrFun (angular R u tags simple v funded live q e r T auth n) (foldUnder n ∘ x)).symm

end YM.Integration.WilsonMarkedIndependentCoverMarginal
end
