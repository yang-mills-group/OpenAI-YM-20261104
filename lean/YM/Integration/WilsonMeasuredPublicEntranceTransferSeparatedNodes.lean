import YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins
/-! Uniform control on the original ordered Wilson cutoffs at every separated reporting-lattice point, including lattice positions that coincide in some transverse coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferSeparatedNodes
open RG Source PhysicalNext.Repeat.Legato
open Filter Function Set Finset Lattice Wilson Cells Extraction Table Spec Next.UVStress OPE.Cards
open WilsonMeasuredPublicEntranceOrderedBasis (debt clears compare form)
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
  {n:ℕ}(d:Caps n)(f:ℕ)(o:Fin n→ Cover)
local notation "C₀" => R.family
local notation "E" => fun i:Fin n=>R.family.label (d i)
local notation "Keys" => Code (fun i:Fin n=>R.family.label (d i))
local notation "point" => Order.grid (C₀) f o

def residual (H:Fin n→ ℝ)(z:ℕ×ℕ):ℝ:=
  debt (C:=C₀) d H (fun a=>physical (C:=C₀) d f o z.1 z.2 (combination (E) a))
    (fun a=>S.value d point (combination (E) a))

include F in
theorem original (simple:G.Simple)(safe:point∈conf n)(H:Fin n→ ℝ):
    Tendsto (residual R (S:=S) d f o H) order.fuse (𝓝 0) ∧
    ∀z:ℕ×ℕ,∀y:(C₀).book.Vector d,(∀i,‖y i‖≤H i)→ 
      ‖physical (C:=C₀) d f o z.1 z.2 y-publicValue (C:=C₀) (S:=S) d f o y‖≤residual R (S:=S) d f o H z:=by
  classical
  constructor
  · apply clears
    intro a
    exact WilsonMeasuredPublicEntranceSeparatedPins.variation R F d f o simple (le_refl order.fuse)
      (fun _=>combination (E) a) (combination (E) a) (fun _=>tendsto_const_nhds) safe
  · intro z y bound
    let u:=fun a:Keys=>physical (C:=C₀) d f o z.1 z.2 (combination (E) a)
    let v:=fun a:Keys=>S.value d point (combination (E) a)
    have issued:physical (C:=C₀) d f o z.1 z.2 y=form (C:=C₀) d u y:=
      basis_tuple (E) y ((C₀).ensemble d (fun i=>location (C₀).S f z.1 z.2 (o i)))
    have named:publicValue (C:=C₀) (S:=S) d f o y=form (C:=C₀) d v y:=
      (S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) d safe y).trans (basis_tuple (E) y (S.value d point))
    rw [issued,named]
    exact compare d H u v bound

include F in
theorem ordered (simple:G.Simple)(safe:point∈conf n)(H:Fin n→ ℝ){ε:ℝ}(ep:0<ε):
    order.late fun N p=>∀y:(C₀).book.Vector d,(∀i,‖y i‖≤H i)→ 
      ‖physical (C:=C₀) d f o N p y-publicValue (C:=C₀) (S:=S) d f o y‖≤ε:=by
  have ⟨fall,fee⟩:=original R F d f o simple safe H
  let P:=fun z:ℕ×ℕ=>∀y:(C₀).book.Vector d,(∀i,‖y i‖≤H i) → 
    ‖physical (C:=C₀) d f o z.1 z.2 y-publicValue (C:=C₀) (S:=S) d f o y‖≤ε
  apply (order.fused P).mp
  filter_upwards [fall.eventually (gt_mem_nhds ep)] with z small
  exact fun y bound=>(fee z y bound).trans small.le

end YM.Integration.WilsonMeasuredPublicEntranceTransferSeparatedNodes
end
