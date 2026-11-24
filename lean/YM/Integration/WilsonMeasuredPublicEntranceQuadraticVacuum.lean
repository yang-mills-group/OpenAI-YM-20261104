import YM.Integration.WilsonMeasuredPublicEntranceQuadraticPolarization

/-! On the original grade-four sector the uncontracted scalar component is measured
by the native unit. This accounts for the whole vacuum contribution before comparing
two differently placed fields. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticVacuum
open Maxwell Maxwell.Free Maxwell.Wick XSpace XSpace.Normalize XSpace.Stab
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceQuadraticSpan
open WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticProducts
open WilsonMeasuredPublicEntranceQuadraticContraction
open WilsonMeasuredPublicEntranceQuadraticBonds
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}

theorem one (x y:E4):bond G x y 1 1=1:=by
  rw [bond_eval,show (Fin.cons (α:=fun _:Fin 2=>WickPol G) 1 (fun _=>1))=(fun _=>1) by
    funext i;fin_cases i <;> rfl]
  exact constants _
theorem absent {x y:E4}(apart:x≠y)(hd:4≤d)(i j:Six):
    bond G x y 1 (tile hd i j).val=0:=by
  change bond G x y 1 (∑c:G.ColorIndex,letter (factor c i)*letter (factor c j))=0
  rw [map_sum]
  refine Finset.sum_eq_zero fun c _=>?_
  let v:Fin 2→Fin 1:=fun _=>0
  let E:Fin 2→Factor G:=![factor c i,factor c j]
  let r:List (Fin 2):=[0,1]
  have back:(fun _:Fin 1=>letter (factor c i)*letter (factor c j))=bag v E r:=by
    ext1 t;fin_cases t;simp [v,E,r,bag]
  rw [bond_eval]
  change moment G (Points.cons x (points (fun _:Fin 1=>y))) (Fin.cons _ (fun _=>letter _*letter _))=_
  rw [back,show (1:WickPol G)=(([]:List (Factor G)).map letter).prod by simp,
    planted _ _ _ _ _ (pair_ok apart)]
  change pairCost linkEntry [(y,factor c i),(y,factor c j)]=0
  simp only [pair_step,pulls_cons,pulls_nil,link_zero,zero_mul,add_zero]

def remainder (hd:4≤d)(x y z:E4)(D U V:Plane ℝ):WickPol G→ₗ[ℂ] ℂ:=
  strength y z • triangle G x y z (marked G hd U).val (marked G hd V).val-
    (2*strength x y*strength x z) • bond G y z (marked G hd (product D U V)).val

theorem original (simple:G.Simple){x y z:E4}(a b:Axis){s t u:ℝ}(hs:s≠0)(ht:t≠0)(hu:u≠0)
    (xy:x-y=s • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (xz:x-z=t • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (yz:y-z=u • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (hd:4≤d)(U V:Plane ℝ)(sU:U.transpose=U)(sV:V.transpose=V)
    (w:WickPol G)(low:w∈shellSector G 4):
    let L:=remainder (G:=G) hd x y z (lift (exterior a b)) U V
    L w=L 1*bond G y z 1 w:=by
  intro L
  have apart:y≠z:=fun eq=>(smul_ne_zero hu (WilsonMeasuredPublicEntranceQuadraticKernel.nonzero a b))
    (yz.symm.trans (sub_eq_zero.mpr eq))
  have reduced: shellSector G 4 ≤LinearMap.ker (L-L 1 • bond G y z 1):=by
    rw [low_support simple]
    apply sup_le
    · rw [BottomOnly,Submodule.span_singleton_le_iff_mem]
      change L 1-L 1*bond G y z 1 1=0
      simp [one]
    rw [label_span,Submodule.span_le]
    rintro _ ⟨i,j,_,rfl⟩
    change L (tile hd i j).val-L 1*bond G y z 1 (tile hd i j).val=0
    rw [absent apart hd i j,mul_zero,sub_zero]
    exact sub_eq_zero.mpr (WilsonMeasuredPublicEntranceQuadraticPolarization.original
      a b hs ht hu xy xz yz hd U V sU sV i j)
  exact sub_eq_zero.mp (reduced low)
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticVacuum

