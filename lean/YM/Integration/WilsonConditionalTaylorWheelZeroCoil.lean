import YM.Integration.WilsonConditionalTaylorWheelClassicalHead
import YM.Integration.WilsonConditionalTaylorWheelCoverCoil

/-! Include the complete classical kinetic row in the same signed
pre-reset comparison as the positive-order interactions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelZeroCoil
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) (u:G.ColorIndex) (N j:ℕ)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
local notation "W" => Dove.model V wood b R.metals.O u N (j+1)
local notation "P" => destination V N j

include simple in
theorem finite (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (live:j<N) (per r:ℕ):
    let n:=R.family.side j per;
    (-(coil0 V R.metals.O j N n 0 (r+1)))=
      rancho (FormalBulk08.Bank.burn P (wood j) W R.metals.O (b j) tags n) 0 (r+1):=by
  intro n
  let S:=(V).clock.op j per
  let f:=R.family.side (j+1) per
  let X:=Winding.emera (actionW V R.metals.O N (j+1)) f
  let F:=repeatF S
  let H:=freeForms V N (j+1)
  let Y:=freeForms V N j
  let M:=installed S.ratio (predictionA V N j)
  let T:=winter S F H Y M R.metals.O X
  have present:coil0 V R.metals.O j N n=T:=WilsonConditionalTaylorWheelPhysicalSide.original R N j per
  have available:=Winding.emera_far V simple R.alloy.B.ratio (Nat.succ_le_iff.mpr live) f
  have shape:shellK 2 T:=winter_band S F H Y M R.alloy.B.ratio available.1
  have purity:∀a,Pure (T a):=winter_pure S F H Y M R.alloy.B.ratio ((V).blocks j per).branches
    available.2 (age_sym V ..)
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  have file:=FormalBulk08.Bank.funded P (wood j) W R.metals.O (b j) dossier
    ((V).clock.adm j) R.alloy.B.ratio tags n
  have real:=WilsonConditionalTaylorWheelClassicalHead.recorded R N j per F X
  dsimp only at real
  rw [loc_land V N j live] at real
  rw [present,←WilsonConditionalTaylorWheelCoverBirth.signed T 2 shape purity 0 (r+1)]
  exact congrArg (Lava.marble (r+1)) (real.trans file.symm)

include simple in
theorem original (live:j<N) (E r c q degree:ℕ) (width:Gear G→ℝ)
    (positiveWidth:∀I,0<width I) (Q:Realm G (E+1) Credit.leanC) (here:Q.anchor≤j)
    (invoice:RootedVacuumWinding.ReceiptOn R E 0 r c q degree width j Q here)
    (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices):
    -freshet V R.metals.O N j 0 (r+1)=FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j) 0 (r+1):=
  WilsonConditionalTaylorWheelCoverCoil.identity R simple u N j live E 0 r c q degree width positiveWidth
    Q here invoice tags (fun per=>finite R simple u N j tags live per r)

end YM.Integration.WilsonConditionalTaylorWheelZeroCoil
end
