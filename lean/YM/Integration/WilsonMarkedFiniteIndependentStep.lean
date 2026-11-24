import YM.Integration.WilsonMarkedPreResetMaterialHistory
import YM.Integration.WilsonVacuumPreResetFiniteHistory
import YM.Integration.WilsonConditionalTaylorWheelTensors
import YM.Integration.WilsonConditionalTaylorWheelClock

/-! The received finite source is filed with the actual unaliased vacuum and the independently prescribed
own-coupling return at every original date and every torus side. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedFiniteIndependentStep
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open AnalyticNext.QuarticMatch.Sheets
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}

variable (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)


open WilsonVacuumPreResetIndependentForecast (prescription)
open WilsonMarkedPreResetMaterialHistory (before energy)

def fixed (N j:ℕ) (n:Side) (T:PChart G (n*(destination V N j).patch.L)):PChart G n:=
  let P:=destination V N j
  let C:=prescription R u N j
  let old:=WilsonVacuumPreResetFiniteHistory.action R u tags N (N-(j+1)) (j+1) (n*P.patch.L)
  Wine.stamp (Wine.bookH C) (Wine.bookU C) (rancho
    (Reef.tossed P R.metals.O (b j) (wood j) n (tags j n) old (flash T)))

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (N j q:ℕ)(live:j<N)(T:Mer.Era G ℝ)(law:Mer.Auth q T)(n:Side):
    (Mer.verseI V R.metals.O j N q T).1 n=fixed R u tags N j n (T.1 (n*(destination V N j).patch.L)):=by
  let Y:=before R N j q T.1 n
  let H:=pitch V R.metals.O N j
  have dossier:=(WilsonCoeffUV.Bank.old V R.metals.O simple R.alloy.B.ratio N (j+1) live).basis (n*(loose V j).L)
  have out:shellK q Y ∧ ∀e,Pure (Y e):=
    ⟨reed_band _ _ _ _ q dossier.lamp R.alloy.B.ratio (law.span _),
      fun e=>reed_smooth _ _ _ _ q R.metals.O _ (law.pale _) e⟩
  have file:Y=rancho (flash Y):=by
    funext e r
    exact (WilsonConditionalTaylorWheelTensors.actual Y q out.1 out.2 e r).symm
  have current:=WilsonMarkedPreResetMaterialHistory.received R simple tags N j q live T.1 law.span law.pale n
  change flash Y=_ at current
  have quiet:=WilsonVacuumPreResetFiniteHistory.original R u tags simple v funded (N:=N) (j:=j+1) live (n*(destination V N j).patch.L)
  change energy R N (j+1) (n*(destination V N j).patch.L)=_ at quiet
  have coin:H=prescription R u N j:=WilsonVacuumPreResetIndependentForecast.pitch_eq R u simple v funded live
  change Blue.mix (Blue.back H) Y=_
  rw [WilsonConditionalTaylorWheelClock.allRows H (angle_tilt (A:=V) simple R.alloy.B.ratio live) ,coin,file,current]
  let insert (old:Pap (wire G (n*(destination V N j).patch.L))) := Wine.stamp
    (Wine.bookH (prescription R u N j)) (Wine.bookU (prescription R u N j)) (rancho
      (Reef.tossed (destination V N j) R.metals.O (b j) (wood j) n (tags j n) old
        (flash (T.1 (n*(destination V N j).patch.L)))))
  exact congrArg insert quiet

end YM.Integration.WilsonMarkedFiniteIndependentStep
end
