import YM.Integration.WilsonThermometerWeakPairRise

/-! The full child subtraction is jointly multilinear in its actual positioned inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairForms
open Function Finset Table Spec OPE OPE.Prescription OPE.Orbits
open scoped Classical BigOperators
variable {G:Gauge}{L:Register G}{S:Table L}(T:Table L){Q:DiffPlan S}
    (P:Prescription Q){I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ}

def fixedFar (h:ℕ)(x:I→E4)(o:E4)(y:J→E4)(w:Labels S e):
    MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ:=
  sectionLabels (d:=Sum.elim d e) w (moment T (beside x y)) -
    ∑ a∈bands Q h, (upon T h o y w (P.loaded a h)) • (checkRow P a x o)

theorem far_eq (hier:S.Hierarchy)(h:ℕ)(x:I→E4)(o:E4)(y:J→E4)(w:Labels S e)(v:Labels S d):
    fixedFar T P h x o y w v = discrepancy T h x o v (shadowOld P h x o v) y w:=by
  unfold fixedFar discrepancy whole shadowOld OPE.shadow
  change sectionLabels (d:=Sum.elim d e) w (moment T (beside x y)) v -
    (∑a∈bands Q h, (upon T h o y w (P.loaded a h)) • (checkRow (d:=d) P a x o)) v = _
  rw [sectionLabels_apply,_root_.sum_apply,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.smul_apply,check_eq P a hier,map_smul,smul_eq_mul]
  exact mul_comm ..

def fixedNear (h:ℕ)(x:I→E4)(o:E4)(v:Labels S d)(z:E4)(e:ℕ):S.Field e→ₗ[ℂ] ℂ:=
  upon T e z x v - upon T e z (sole o) (sole (shadowOld P h x o v):Labels S (fun _:Unit=>h))

theorem near_eq (hier:T.Hierarchy)(h:ℕ)(x:I→E4)(o:E4)(v:Labels S d)(z:E4){e:ℕ}(w:S.Field e)
    (near:Injective (beside x (sole z)))(far:Injective (beside (sole o) (sole z))):
    fixedNear T P h x o v z e w =
      discrepancy T h x o v (shadowOld P h x o v) (sole z) (sole w:Labels S (fun _:Unit=>e)):=by
  unfold fixedNear discrepancy
  change whole T (sole z) (sole w:Labels S (fun _:Unit=>e)) x v -
    whole T (sole z) (sole w:Labels S (fun _:Unit=>e)) (sole o) (sole (shadowOld P h x o v):Labels S (fun _:Unit=>h)) = _
  rw [whole_flip v _ x _ hier near,whole_flip (sole (shadowOld P h x o v):Labels S (fun _:Unit=>h)) _ (sole o) _ hier far]
  rfl

abbrev Lot (Q:DiffPlan S)(d:I→ℕ) := (i:I)→ ↥(bands Q (d i))

def weight (a:Lot Q d)(v:Labels S d):ℂ:=∏i:I,P.test (a i).1 (d i) (v i)
def field (a:Lot Q d):Labels S d:=fun i=>P.loaded (a i).1 (d i)

theorem unfolded (hp:P.Coherent)(M:MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ)(v:Labels S d):
    M v = ∑a:Lot Q d,weight P a v*M (field P a):=by
  have rebuilt (i:I): v i=∑a:↥(bands Q (d i)),P.test a.1 (d i) (v i) • P.loaded a.1 (d i):=by
    exact ((Finset.sum_attach (bands Q (d i)) (fun a=>P.test a (d i) (v i) • P.loaded a (d i))).trans
      ((hp (d i)).rebuilds (v i))).symm
  conv_lhs => rw [show v=(fun i=>∑a:↥(bands Q (d i)),P.test a.1 (d i) (v i) • P.loaded a.1 (d i)) from funext rebuilt]
  simp only [MultilinearMap.map_sum,MultilinearMap.map_smul_univ,smul_eq_mul,weight]
  rfl

end YM.Integration.WilsonThermometerWeakPairForms
end
