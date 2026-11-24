import YM.Integration.WilsonMarkedIndependentCoverMarginal
import YM.Integration.WilsonVacuumPreResetIndependentForecast
import YM.Integration.WilsonConditionalTaylorWheelClock

/-! Same covered marked integral after the independently prescribed own-coupling reset. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedCoverIndependentStep
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

def fixed (N j cap:ℕ)(Z:Mesa.Pot G):Mesa.Pot G:=
  let P:=destination V N j
  let W:=Dove.model V wood b R.metals.O u N (j+1)
  let C:=WilsonVacuumPreResetIndependentForecast.prescription R u N j
  Wine.stamp (Wine.bookH C) (Wine.bookU C) (Kemp.braise P (wood j) W Z R.metals.O (b j) cap)

include tags in
theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(live:j<N)(q cap:ℕ)(width:q≤cap)(T:Mer.Era G ℝ)(auth:Auth q T)(a:Loc G 1):
    (Mer.verseI V R.metals.O j N q T).2=fixed R u N j cap T.2:=by
  let H:=pitch V R.metals.O N j
  let P:=destination V N j
  let W:=Dove.model V wood b R.metals.O u N (j+1)
  have marginal:upper R N j q T.2 = Kemp.braise P (wood j) W T.2 R.metals.O (b j) cap:=by
    funext e r
    exact (WilsonMarkedIndependentCoverMarginal.original R u tags simple v funded live e r q cap width T auth a a).1
  have coin:H=WilsonVacuumPreResetIndependentForecast.prescription R u N j:=
    WilsonVacuumPreResetIndependentForecast.pitch_eq R u simple v funded live
  change Blue.mix (Blue.back H) (upper R N j q T.2)=_
  rw [WilsonConditionalTaylorWheelClock.allRows H (angle_tilt (A:=V) simple R.alloy.B.ratio live),coin,marginal]
  rfl

end YM.Integration.WilsonMarkedCoverIndependentStep
end
