import YM.Integration.WilsonMeasuredPublicEntranceOrderedBasis
import YM.OPE.Cards.Pressure
/-! The true normalized original product at previously fixed cover positions, including its ordered two-regulator estimates on every bounded changing tuple of labels. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOrderedPins
open Function Filter Finset Set Lattice Wilson Cells Extraction Spec Table Next.UVStress OPE.Cards
open WilsonMeasuredPublicEntranceOrderedBasis (debt clears compare form)
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{order:Extraction.Order}{S:Table C.book}(F:Final C order S)
  {n:ℕ}(d:Caps n)(site:ℕ)(o:Fin n → Cover)
local notation "E" => fun i:Fin n=>C.label (d i)
local notation "Keys" => Code (fun i:Fin n=>C.label (d i))
local notation "point" => Order.grid C site o

def physical (N p:ℕ)(y:C.book.Vector d):ℂ:=
  C.omega N p fun U=>∏i,C.O N p (y i) (location C.S site N p (o i)) U

def publicValue (y:C.book.Vector d):ℂ:=S.classMoment S d point (fun i=>S.project _ (y i))

structure Release (H:Fin n→ℝ) where
  period:ℕ→Keys→ℂ
  ultraviolet:ℕ→ℕ→ℝ
  volume:ℕ→ℝ
  suitable:∀ᶠk in atTop,point∈Cyclic C.S (order.per k) n
  first:∀p,point∈Cyclic C.S p n → Tendsto (fun j=>ultraviolet (order.mesh j) p) atTop (𝓝 0)
  second:Tendsto (fun k=>volume (order.per k)) atTop (𝓝 0)
  fine:∀N p (y:C.book.Vector d),(∀i,‖y i‖≤H i) →
    ‖physical d site o N p y-form d (period p) y‖≤ultraviolet N p
  outer:∀p (y:C.book.Vector d),(∀i,‖y i‖≤H i) →
    ‖form d (period p) y-publicValue (S:=S) d site o y‖≤volume p

include F in
theorem original (generic:point∈ YM.generic n)(H:Fin n→ℝ):Nonempty (Release (C:=C) (S:=S) (order:=order) d site o H):=by
  have same (y:C.book.Vector d):publicValue (S:=S) d site o y=S.value d point y:=
    S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) d (generic_conf n generic) y
  have receipt(a:Keys):order.limits (fun p=>point∈Cyclic C.S p n)
      (fun N p=>physical d site o N p (combination (E) a))
      (S.value d point (combination (E) a)):=
    eventual_grid C order S F.room.generic o generic (fun i=>⟨d i,combination (E) a i⟩)
  choose prices uv vol using fun a=>(receipt a).2
  let lower:=fun a=>S.value d point (combination (E) a)
  let upper:=fun N p a=>physical d site o N p (combination (E) a)
  let middle:=fun p a=>prices a p
  refine ⟨⟨middle,(fun N p=>debt (C:=C) d H (upper N p) (middle p)),
    (fun p=>debt (C:=C) d H (middle p) lower),?_,?_,?_,?_,?_⟩⟩
  · exact (eventual_grid C order S F.room.generic o generic (fun i=>⟨d i,0⟩)).1
  · intro p room
    exact clears d H (fun j=>upper (order.mesh j) p) (middle p) (fun a=>uv a p room)
  · exact clears d H (fun k=>middle (order.per k)) lower vol
  · intro N p y bounded
    have expand:physical d site o N p y=form d (upper N p) y:=
      basis_tuple (E) y (C.ensemble d (fun i=>location C.S site N p (o i)))
    rw [expand]
    exact compare d H _ _ bounded
  · intro p y bounded
    have expand:publicValue (S:=S) d site o y=form d lower y:=(same y).trans (basis_tuple (E) y (S.value d point))
    rw [expand]
    exact compare d H _ _ bounded

theorem ordered {H:Fin n→ℝ}(r:Release (C:=C) (S:=S) (order:=order) d site o H){ε:ℝ}(e:0<ε):
    order.late fun N p=>∀y:C.book.Vector d,(∀i,‖y i‖≤H i) →
      ‖physical d site o N p y-publicValue (S:=S) d site o y‖≤ε:=by
  have ep:0<ε/2:=half_pos e
  filter_upwards [r.suitable,r.second.eventually (gt_mem_nhds ep)] with k room volume
  filter_upwards [(r.first _ room).eventually (gt_mem_nhds ep)] with j ultraviolet
  intro y bounded
  calc
    _ ≤ ‖physical d site o (order.mesh j) (order.per k) y-form d (r.period (order.per k)) y‖+
      ‖form d (r.period (order.per k)) y-publicValue (S:=S) d site o y‖:=norm_sub_le_norm_sub_add_norm_sub .. 
    _ ≤ r.ultraviolet (order.mesh j) (order.per k)+r.volume (order.per k):=
      add_le_add (r.fine _ _ _ bounded) (r.outer _ _ bounded)
    _ ≤ ε:=by change r.ultraviolet (order.mesh j) (order.per k)<ε/2 at ultraviolet;change r.volume (order.per k)<ε/2 at volume;linarith

end YM.Integration.WilsonMeasuredPublicEntranceOrderedPins
end
