import YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceSeparatedBudget
open Function Filter Finset Set Lattice Wilson Cells Extraction Spec PhysicalNext.Repeat.Legato Next.UVStress
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open WilsonMeasuredPublicEntranceOrderedBasis (form debt compare clears)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
    {n:ℕ}(d:Caps n)(site:ℕ)(o:Fin n→ Cover)
local notation "C₀" => R.family
local notation "E" => fun i:Fin n=>(C₀).label (d i)
local notation "Keys" => Code (fun i:Fin n=>(C₀).label (d i))
local notation "point" => Order.grid (C₀) site o

include F in
theorem ordered (simple:G.Simple)(safe:point∈conf n)(H:Fin n→ℝ){ε:ℝ}(ep:0<ε):
    order.late fun N p=>∀y:(C₀).book.Vector d,(∀i,‖y i‖≤H i) →
      ‖physical d site o N p y-publicValue (S:=S) d site o y‖≤ε:=by
  let upper:=fun (w:ℕ×ℕ)(a:Keys)=>physical (C:=R.family) d site o w.1 w.2 (combination (E) a)
  let lower:=fun (a:Keys)=>S.value d point (combination (E) a)
  have actual(a:Keys):Tendsto (fun w=>upper w a) order.fuse (𝓝 (lower a)):=
    WilsonMeasuredPublicEntranceSeparatedPins.variation R F d site o simple le_rfl
      (fun _=>combination (E) a) (combination (E) a) (fun _=>tendsto_const_nhds) safe
  have good:∀ᶠw:ℕ×ℕ in order.fuse,debt (C:=C₀) d H (upper w) lower<ε:=
    (clears d H upper lower actual).eventually (gt_mem_nhds ep)
  apply (Order.fused order (fun w=>∀y:(C₀).book.Vector d,(∀i,‖y i‖≤H i) →
    ‖physical d site o w.1 w.2 y-publicValue (S:=S) d site o y‖≤ε)).mp
  filter_upwards [good] with w fare y bounded
  have fine:physical d site o w.1 w.2 y=form d (upper w) y:=
    basis_tuple (E) y ((C₀).ensemble d (fun i=>location (C₀).S site w.1 w.2 (o i)))
  have named:publicValue (S:=S) d site o y=form d lower y:=
    (S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) d safe y).trans
      (basis_tuple (E) y (S.value d point))
  rw [fine,named]
  exact (compare d H _ _ bounded).trans fare.le

end YM.Integration.WilsonMeasuredPublicEntranceSeparatedBudget
end
