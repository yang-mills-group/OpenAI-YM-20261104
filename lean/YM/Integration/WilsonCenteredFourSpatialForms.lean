import YM.Integration.WilsonCenteredFourSpatialBasis

/-! The exact near multilinear form on the same measured packet, including
all five retained grades. Its finite input basis can be purchased before r. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialForms
open Function Finset Set Filter Spec Table OPE OPE.Orbits OPE.Prescription
open WilsonCenteredFourSpatialNodes WilsonThermometerWeakPairClock
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)
local notation "d₄" => (fun _:Fin 2=>4)

def packet (x:Fin 2→E4):MultilinearMap ℂ (fun _:Fin 2=>S.Field 4) (S.Field 4):=
  ∑i:Fin 5,(F.sector.derivatives.rise (d:=i.val) (by omega)).compMultilinearMap (Q.fresh i.val x 0)

def forms (x:Fin 2→E4)(z:E4)(w:S.Field 4):MultilinearMap ℂ (fun _:Fin 2=>S.Field 4) ℂ :=
  let T:MultilinearMap ℂ (fun _:Fin 2=>S.Field 4) ℂ:=
    sectionLabels (d:=Sum.elim d₄ (fun _:Unit=>4)) (sole w) (moment S (beside x (sole z)))
  T -
    (upon S 4 0 (sole z) (sole w:Labels S (fun _:Unit=>4))).compMultilinearMap (packet F Q x)

theorem actual (x:Fin 2→E4)(u:Fin 2→S.Field 4)(z:E4)(w:S.Field 4)
    (separate:Injective (beside x (sole z)))(distinct:Injective (beside (sole (0:E4)) (sole z))):
    forms F Q x z w u = defect (S:=S) 4 x u (Q.packet 4 x (d:=d₄) u 0) z w:=by
  have pkt:packet F Q x u=Q.packet 4 x (d:=d₄) u 0:=by
    rw [packet,Reader.packet,_root_.sum_apply];rfl
  unfold forms
  change sectionLabels (d:=Sum.elim d₄ (fun _:Unit=>4)) (sole w) (moment S (beside x (sole z))) u -
     upon S 4 0 (sole z) (sole w:Labels S (fun _:Unit=>4)) (packet F Q x u)=_
  rw [sectionLabels_apply,pkt]
  let Y:=Q.packet 4 x (d:=d₄) u 0
  change whole S x u (sole z) (sole w:Labels S (fun _:Unit=>4))-whole S (sole 0) (sole Y:Labels S (fun _:Unit=>4)) (sole z) (sole w:Labels S (fun _:Unit=>4))=_
  rw [←whole_flip u (sole w:Labels S (fun _:Unit=>4)) x (sole z) Q.continuum separate,
    ←whole_flip (sole Y:Labels S (fun _:Unit=>4)) (sole w:Labels S (fun _:Unit=>4)) (sole 0) (sole z) Q.continuum distinct]
  rfl

theorem directions {V:Type*}[NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V]
    {I:Type}[Fintype I](b:Module.Basis I ℂ V)(T:MultilinearMap ℂ (fun _:Fin 2=>V) ℂ)
    (v:Fin 2→V)(C:(Fin 2→I)→ℝ)(fee:ℝ)
    (bought:∀j:Fin 2→I,‖T (fun i=>b (j i))‖≤C j*fee):
    ‖T v‖≤(∑j:Fin 2→I,(∏i,‖(b.coord (j i)).toContinuousLinearMap‖)*C j)*(∏i,‖v i‖)*fee:=by
  let ω:=fun (j:Fin 2→I)=>∏i,b.repr (v i) (j i)
  have expanded:T v=∑j:Fin 2→I,ω j*T (fun i=>b (j i)):=by
    have e:v=fun i=>∑a:I,b.repr (v i) a • b a:=funext fun i=>(b.sum_repr _).symm
    conv_lhs=>rw [e]
    rw [MultilinearMap.map_sum];exact Finset.sum_congr rfl (fun j _=>T.map_smul_univ _ _)
  have terms(j:Fin 2→I):‖ω j‖≤(∏i,‖(b.coord (j i)).toContinuousLinearMap‖)*(∏i,‖v i‖):=by
    dsimp only [ω];rw [norm_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _=>norm_nonneg _) fun i _=>(b.coord (j i)).toContinuousLinearMap.le_opNorm (v i)
  rw [expanded,Finset.sum_mul,Finset.sum_mul]
  apply (norm_sum_le _ _).trans;apply Finset.sum_le_sum;intro j _
  rw [norm_mul]
  exact (mul_le_mul (terms j) (bought j) (norm_nonneg _) (mul_nonneg (Finset.prod_nonneg fun _ _=>norm_nonneg _) (Finset.prod_nonneg fun _ _=>norm_nonneg _))).trans_eq (by ring)

end YM.Integration.WilsonCenteredFourSpatialForms
