import YM.Integration.WilsonConditionalTaylorVacuumWindingDeposit

/-! Only a finite rectangle of ranks is needed at a fixed comparison
order. Its genuine winding receipts are booked on one original family
and hold at every finer date, before any later cutoff is mentioned. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelRealmLedger
open Function Filter Lattice RG Wilson Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Embroider WilsonLimitConstruction
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)

def Row (E e r j:ℕ):Prop:=
  ∃(width:Gear G→ℝ)(degree:ℕ), (∀I,0<width I) ∧
    ∃(Q:Realm G (E+1) Credit.leanC)(here:Q.anchor≤j),
      Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧
        RootedVacuumWinding.ReceiptOn R E e r 0 0 degree width j Q here

def At (E j:ℕ):Prop:=∀e≤E,∀r<E+2,Row R E e r j

theorem purchased (simple:G.Simple) (money:WilsonConditionalTaylorVacuumWindingDeposit.Extra R.kit)
    (period:RG05Preconstruction.ReadoutPurchase R.b) (E:ℕ):
    ∀ᶠk:ℕ in atTop,∀j, k≤j→At R E j:=by
  have bought (i:Fin (E+1)) (r:Fin (E+2)):∀ᶠk:ℕ in atTop,∀j,k≤j→Row R E i.val r.val j:=by
    obtain ⟨s,a,pos,offers⟩:=WilsonConditionalTaylorVacuumWindingDeposit.original R simple money period
      0 (fun x=>Fin.elim0 x) (fun x=>Fin.elim0 x) (fun x=>Fin.elim0 x) E i.val r.val (by omega)
    filter_upwards [offers 0 0] with k offer j kj
    obtain ⟨Q,here,levels,scheme,_,_,_,_,_,priced⟩:=offer
    exact ⟨s,a,pos,Q,here.trans kj,levels,scheme,(priced j kj).2⟩
  have all:∀ᶠk:ℕ in atTop,∀(i:Fin (E+1))(r:Fin (E+2)),∀j,k≤j→Row R E i.val r.val j:=
    eventually_all.mpr fun i=>eventually_all.mpr (bought i)
  filter_upwards [all] with k every j kj i hi r hr
  exact every ⟨i,by omega⟩ ⟨r,hr⟩ j kj

end YM.Integration.WilsonConditionalTaylorWheelRealmLedger
end
