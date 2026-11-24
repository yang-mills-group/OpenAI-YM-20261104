import YM.Integration.WilsonSeparatedOriginalSlabReplicaCells
import YM.Integration.WilsonSeparatedOriginalSlabReplicaFilm
import YM.Integration.WilsonSeparatedOriginalSlabReplicaReading

/-! Recelling is an identity of full continuous functions on the three cutoff
fields. A linear experiment tests this single common field translation before
integrating the actual smooth test over each native affine box. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaSurface
open Function MeasureTheory Set Finset Lattice Wilson RG Source
open RG05Readout Address Native Pulse Flatten
open WilsonSeparatedOriginalSlabReplicaReading WilsonSeparatedOriginalSlabReplicaFilm
open WilsonPositionSeparatedProfileCenteredCells 
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{n N per:ℕ}
local notation "I"=>Fin 3
local notation "Space"=>I → Config G (C.side N per)

theorem register (s:I→ℕ)(v:(i:I)→Palette C (s i))(r:ℝ)(Ψ:Wave I)(h:n≤N)(m:ℕ)(g:Body):
    paper s v r Ψ h m g=premiums C s m n r • ∑o:I→Site (C.side n per),film s v o h Ψ r g:=by
  ext W
  simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul];rfl

theorem cut (s:I→ℕ)(v:(i:I)→Palette C (s i))(r:ℝ)(Ψ:Wave I)(top:n+1≤N){cap:ℝ}
    (rp:0<r)(enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*C.S.a n<C.S.radius per)(m:ℕ)(g:Body)(meter:C(Space,ℂ)→ₗ[ℂ]ℂ):
    meter (paper s v r Ψ (n.le_succ.trans top) m g)=
      (Fintype.card (Bud C per n):ℂ)⁻¹*∑c:Bud C per n,meter (turn (C:=C) ((C.S.toDepth top per).embed (child C per n c)) (paper s v r Ψ top m (Many.headFee C per n c g))):=by
  have same:paper s v r Ψ (n.le_succ.trans top) m g=(Fintype.card (Bud C per n):ℂ)⁻¹ • ∑c:Bud C per n,turn (C:=C) ((C.S.toDepth top per).embed (child C per n c)) (paper s v r Ψ top m (Many.headFee C per n c g)):=by
    ext W
    simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul]
    exact (WilsonSeparatedOriginalSlabReplicaCells.assembled C s v r Ψ top rp enclosed room m g W).symm
  rw [same,map_smul,map_sum,smul_eq_mul]

end YM.Integration.WilsonSeparatedOriginalSlabReplicaSurface
