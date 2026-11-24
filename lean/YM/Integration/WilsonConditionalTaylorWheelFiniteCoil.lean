import YM.Integration.WilsonConditionalTaylorWheelPhysicalSide
import YM.Integration.WilsonConditionalTaylorWheelRecordedEnergy

/-! One induction step before the running coupling is extracted: every
occupied positive-order row of the actual signed finite upper vacuum is
the independent normalized finite Gaussian energy on this same period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelFiniteCoil
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Mesa Gorge City Cork Rift Pose Glide Dawn Rial
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open scoped Classical BigOperators Matrix Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple) (u:G.ColorIndex) (N j:ℕ)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
local notation "W" => Dove.model V wood b R.metals.O u N (j+1)
local notation "P" => destination V N j

include simple in
theorem original (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (live:j<N) (E:ℕ) (previous:∀d≤E,∀s<d+2,-actionW V R.metals.O N (j+1) d (s+1)=W d (s+1))
    (per e r:ℕ) (pos:0<e) (cap:e≤E):
    let n:=R.family.side j per
    (-(Winding.coil0 V R.metals.O j N n e (r+1)))=
      rancho (FormalBulk08.Bank.burn P (wood j) W R.metals.O (b j) tags n) e (r+1):=by
  intro n
  let S:=(V).clock.op j per
  let f:=R.family.side (j+1) per
  let X:=Winding.emera (actionW V R.metals.O N (j+1)) f
  let F:=repeatF S
  let H:=freeForms V N (j+1)
  let Y:=freeForms V N j
  let M:=installed S.ratio (predictionA V N j)
  let raw:=winter S F H Y M R.metals.O X
  have shift:Winding.coil0 V R.metals.O j N n=raw:=
    WilsonConditionalTaylorWheelPhysicalSide.original R N j per
  have available:=Winding.emera_far V simple R.alloy.B.ratio (Nat.succ_le_iff.mpr live) f
  let T:=FormalBulk08.Bank.burn P (wood j) W R.metals.O (b j) tags n
  obtain ⟨F₀,t,issued,_,law⟩:=WilsonRunVacuumWickCubature.filed R N j per live (tags n) wood u simple
  have same:HEq F (Reef.floor (V).clock.kernel P (wood j) n):=
    WilsonConditionalTaylorWheelPhysicalSide.forest S (P).patch (V).clock.kernel rfl rfl
  have joined:F₀=F:=eq_of_heq (issued.trans same.symm)
  subst F₀
  let D:WilsonConditionalTaylorWheelKernel.Stage G:=⟨R,N,j,per,live,F,t⟩
  have previousFinite:Through E (-flash X) (Mesa.stone W f):=
    WilsonConditionalTaylorWheelInputTruncation.retained R simple N (j+1) (Nat.succ_le_iff.mpr live) W E previous f
  have integrated:=WilsonConditionalTaylorWheelRecordedEnergy.occupied D simple (Mesa.stone W f) T
    (Reef.ferry P (b j) (wood j) n).main previousFinite law e (r+1) pos cap (Nat.succ_pos _)
  have shape:shellK 2 raw:=winter_band S F H Y M R.alloy.B.ratio available.1
  have purity:∀d,Pure (raw d):=winter_pure S F H Y M R.alloy.B.ratio ((V).blocks j per).branches
    available.2 (age_sym V ..)
  rw [shift]
  exact (WilsonConditionalTaylorWheelCoverBirth.signed raw 2 shape purity e (r+1)).symm.trans integrated

end YM.Integration.WilsonConditionalTaylorWheelFiniteCoil
end

