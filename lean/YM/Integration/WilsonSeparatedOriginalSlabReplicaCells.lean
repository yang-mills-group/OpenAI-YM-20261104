import YM.Integration.WilsonSeparatedOriginalSlabReplicaOrbit
import YM.Integration.WilsonPositionSeparatedProfileCenteredCells
import YM.Integration.WilsonPositionSeparatedProfileCenteredOrbit

/-! Reassembly on the original globally smooth test, before conditional
transport. Each of the signed ultraviolet terms keeps the common center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaCells
open Function Set MeasureTheory Finset Lattice Wilson RG Source
open RG05Readout Address Native Pulse Flatten MergeProof Accent Extra.Histories
open WilsonPositionSeparatedProfileCenteredCells
open scoped Classical Topology BigOperators
variable {G:Gauge} (C:Family G) {N p n:ℕ}

local notation "I"=>Fin 3
theorem assembled (D:I→ℕ) (v:(i:I)→Palette C (D i)) (r:ℝ) (Ψ:Wave I) (top:n+1≤N) {cap:ℝ}
    (rp:0<r) (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap) (room:r*cap+2*C.S.a n<C.S.radius p) (m:ℕ) (g:Body) (U:I → Config G (C.side N p)):
    (Fintype.card (Bud C p n):ℂ)⁻¹*∑i:Bud C p n,WilsonSeparatedOriginalSlabReplicaOrbit.surface C D v r Ψ top m (Many.headFee C p n i g)
      (fun d:I=>Lattice.pull 1 ((C.S.toDepth top p).embed (child C p n i)) (U d))=
        WilsonSeparatedOriginalSlabReplicaOrbit.surface C D v r Ψ (n.le_succ.trans top) m g U:=by
  let h (z:E4):=g.val z*((∏_i:I,(r:ℂ)⁻¹^4)*WilsonSeparatedOriginalSlabReplicaTransport.multi C m N p D v (rel r Ψ (C.S.a n • z)) U)
  have smooth:Continuous h:=(body_smooth g 1).continuous.mul (continuous_const.mul ((WilsonSeparatedOriginalSlabReplicaTransport.continuous D v r Ψ m U).comp (continuous_id.const_smul (C.S.a n))))
  have far:C.S.a n+r*cap<C.S.radius p:=by linarith only [room,C.S.a_pos n]
  have small:r*cap+2*C.S.a (n+1)<C.S.radius p:=by linarith only [room,C.S.strictAnti.antitone n.le_succ]
  have one (i:Bud C p n):WilsonSeparatedOriginalSlabReplicaOrbit.surface C D v r Ψ top m (Many.headFee C p n i g) (fun d:I=>Lattice.pull 1 ((C.S.toDepth top p).embed (child C p n i)) (U d))=∫z in Native.box,h (ray C p n i z):=by
    have entry (z:E4) (hz:z∈Native.box):‖voyager C p (n+1) (child C p n i) z‖≤C.S.a n:=by
      rw [child_voyager];exact room_B (C:=C) _ (dist_box C p n i hz)
    rw [WilsonSeparatedOriginalSlabReplicaOrbit.original C D v r Ψ top rp enclosed small far m _ entry]
    apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet
    intro z _;dsimp only;rw [child_voyager];rfl
  have zero:C.S.place (0:Site (C.side n p))=0:=MergeProof.Ribbons.latzero C n
  have vzero (z:E4):voyager C p n 0 z=C.S.a n • z:=by unfold voyager;rw [zero,zero_add]
  have entry (z:E4) (hz:z∈Native.box):‖voyager C p n 0 z‖≤C.S.a n:=by rw [vzero];exact room_B (C:=C) z hz
  have root:(C.S.toDepth (n.le_succ.trans top) p).embed 0=0:=(C.S.toDepth _ p).root.map_zero
  have older:=WilsonSeparatedOriginalSlabReplicaOrbit.original C D v r Ψ (n.le_succ.trans top) rp enclosed room far m 0 entry g U
  simp only [root,Lattice.pull_id,vzero] at older
  simp_rw [one];exact (WilsonPositionSeparatedProfileCenteredCells.original C p n h smooth).trans older.symm

end YM.Integration.WilsonSeparatedOriginalSlabReplicaCells
