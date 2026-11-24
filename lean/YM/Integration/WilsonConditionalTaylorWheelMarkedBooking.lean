import YM.Integration.WilsonConditionalTaylorWheelMarkedLimit

/-! Both originally purchased running clocks enter the whole full nonlinear
marked cover response, simultaneously on every high Wilson date/cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelMarkedBooking
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch
open FormalBulk08 Flat Reef Jets Orb Series Next.Free PowerSeries Stationary Lotus Shore
open Work.F03 Work.F05 Work.F08 Mesa Gorge City Cork Rift Lava Kemp Wine Rial Roof Dove
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil PhysicalNext.Repeat.Legato Next.Foundations
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge}

theorem stamp {I:Type} {E:ℕ} {A B H U:PowerSeries ℝ} (forward:Through E A H) (inverse:Through E B U)
    (F T:OrbitV I) (e r:ℕ) (within:e≤E) (old:∀i≤e,F i r=T i r):
    Wine.stamp A B F e r=Wine.stamp H U T e r:=by
  rw [Wine.stamp,Wine.stamp]
  apply Finset.sum_congr rfl
  intro i hi
  have rank:i≤e:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
  have cost:=((forward.pow i).mul (inverse.pow r)) (e-i) (by omega)
  rw [Wine.bill,Wine.bill,cost,old i rank]

variable (R:Run G) (simple:G.Simple) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun i:ℕ=>Flat.routes (R.family.path.levels.clock.op i 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun i:ℕ=>(R.family.path.levels.blocks i 0).branches)
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def rebook (N j cap:ℕ) (Z:Pot G):Pot G:=
  let P:=destination V N j
  let W:=Dove.model V wood b R.metals.O u N (j+1)
  let H:=Wine.scalar u (FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j))
  Wine.stamp (Wine.bookH H) (Wine.bookU H) (Kemp.braise P (wood j) W Z R.metals.O (b j) cap)

include simple tags in
theorem complete (N j E q cap:ℕ) (live:j<N) (width:q≤cap)
    (old:WilsonConditionalTaylorWheelVacuumHistory.Identified R u N (j+1) E)
    (book:WilsonConditionalTaylorWheelVacuumHistory.Prereset R u N j E)
    (T:Era G ℝ) (auth:Auth q T) (a:Loc G 1) (e r:ℕ) (cost:e≤E):
    (Mer.verseI V R.metals.O j N q T).2 e r=rebook R u N j cap T.2 e r:=by
  let H:=pitch V R.metals.O N j
  let Y:=WilsonConditionalTaylorWheelMarkedLimit.upper R N j q T.2
  change Blue.mix (Blue.back H) Y e r=_
  rw [WilsonConditionalTaylorWheelClock.allRows H (angle_tilt (A:=V) simple R.alloy.B.ratio live)]
  exact stamp book.2.2.1 book.2.2.2 Y _ e r cost (fun i hi=>
    (WilsonConditionalTaylorWheelMarkedLimit.original R simple u tags N j E i r q cap live (hi.trans cost)
      width old T auth a a).1)

include simple tags in
theorem purchased (money:WilsonConditionalTaylorVacuumWindingDeposit.Extra R.kit)
    (period:RG05Preconstruction.ReadoutPurchase R.b) (E:ℕ):
    ∀ᶠk:ℕ in atTop,∀ N j,k≤j→j<N→∀ q cap,q≤cap→∀(T:Era G ℝ),Auth q T→
       ∀(_a:Loc G 1) e r,e≤E→(Mer.verseI V R.metals.O j N q T).2 e r=rebook R u N j cap T.2 e r:=by
  filter_upwards [WilsonConditionalTaylorWheelVacuumHistory.purchased R simple u tags money period E] with k cash N j lower live q cap size T old a e r cost
  exact complete R simple u tags N j E q cap live size (cash N (j+1) (lower.trans (Nat.le_succ _)) live).1
     ((cash N j lower live.le).2 live) T old a e r cost
end YM.Integration.WilsonConditionalTaylorWheelMarkedBooking
end
