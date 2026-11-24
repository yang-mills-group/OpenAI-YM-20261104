import YM.Integration.WilsonConditionalTaylorWheelZeroCoil
import YM.Integration.WilsonConditionalTaylorWheelBookedCoil

/-! The genuine upper Wilson vacuum, its unreset Hessian, and both
running couplings agree with the independently prescribed cover course
at every later cutoff and date, through the single prefixed order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelVacuumHistory
open Function Filter Lattice Laurent RG Wilson Exterior Precision Tree Bloch Next.Foundations PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos PhysicalNext.Repeat.Legato
open Next.Free FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof Lotus Mesa
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def Identified (N j E:ℕ):Prop:=
  ∀e≤E,∀r<E+2,-actionW V R.metals.O N j e (r+1)=Dove.model V wood b R.metals.O u N j e (r+1)

def Prereset (N j E:ℕ):Prop:=
  let W:=Dove.model V wood b R.metals.O u N (j+1)
  let P:=destination V N j
  let T:=FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j)
  let A:=pitch V R.metals.O N j
  let C:=Wine.scalar u T
  (∀e≤E,∀r<E+2,-freshet V R.metals.O N j e (r+1)=T e (r+1)) ∧
    Through E A C ∧ Through E (Wine.bookH A) (Wine.bookH C) ∧ Through E (Wine.bookU A) (Wine.bookU C)

include simple tags in
theorem step (N j E:ℕ) (live:j<N) (cost:WilsonConditionalTaylorWheelRealmLedger.At R E j)
    (previous:Identified R u N (j+1) E):Prereset R u N j E ∧ Identified R u N j E:=by
  let W:=Dove.model V wood b R.metals.O u N (j+1)
  let P:=destination V N j
  let T:=FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j)
  have old:∀d≤E,∀r<d+2,-actionW V R.metals.O N (j+1) d (r+1)=W d (r+1):=
    fun d hd r hr=>previous d hd r (by omega)
  have rows (e:ℕ) (he:e≤E) (r:ℕ) (hr:r<E+2):
      -freshet V R.metals.O N j e (r+1)=T e (r+1):=by
    obtain ⟨s,d,pos,Q,here,_,_,paid⟩:=cost e he r hr
    cases e with
    | zero=>exact WilsonConditionalTaylorWheelZeroCoil.original R simple u N j live E r 0 0 d s pos Q here paid (tags j)
    | succ n=>
      exact WilsonConditionalTaylorWheelCoverCoil.positive R simple u N j live E (n+1) r 0 0 d s pos Q here paid (tags j) old (Nat.succ_pos n) he
  refine ⟨⟨rows,WilsonConditionalTaylorWheelBookedCoil.books R u N j live E cost (fun e he=>rows e he 1 (by omega))⟩,?_⟩
  exact fun e he r hr=>WilsonConditionalTaylorWheelBookedCoil.original R u N j live E cost rows e r he hr

include simple tags in
theorem purchased (money:WilsonConditionalTaylorVacuumWindingDeposit.Extra R.kit)
    (period:RG05Preconstruction.ReadoutPurchase R.b) (E:ℕ):
    ∀ᶠk:ℕ in atTop,∀N j:ℕ,k≤j→j≤N→Identified R u N j E ∧ (j<N→Prereset R u N j E):=by
  filter_upwards [WilsonConditionalTaylorWheelRealmLedger.purchased R simple money period E] with k booked N j lower atN
  revert lower
  induction atN using Nat.decreasingInduction with
  | self=>
    intro _
    exact ⟨fun e _ r _=>WilsonConditionalTaylorWheelCoverBirth.original R simple u wood tags N e r,
      fun h=>False.elim (lt_irrefl _ h)⟩
  | of_succ j live earlier=>
    intro lo
    have row:=step R simple u tags N j E live (booked j lo) (earlier (lo.trans (Nat.le_succ _))).1
    exact ⟨row.2,fun _=>row.1⟩

end YM.Integration.WilsonConditionalTaylorWheelVacuumHistory
end
