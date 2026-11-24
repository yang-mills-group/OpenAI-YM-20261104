import YM.Integration.WilsonMeasuredPublicEntranceQuadraticKernel
import YM.Integration.WilsonMeasuredPublicEntranceQuadraticWick

/-! The real collinear curl propagator is read on the full gauge-colour sum of each
original posted quadratic. The two Wick matchings use both genuine legs. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticBonds
open Function Maxwell Maxwell.Free Maxwell.Wick XSpace.Normalize
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceQuadraticSpan
open WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticKernel
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}

def factor (c:G.ColorIndex)(i:Six):Factor G:=⟨0,omegaLeg c (left i) (right i)⟩
def beamK (a b:Axis)(x y:E4)(i j:Six):ℂ:=
  ((4*normal*(‖x-y‖^2)⁻¹^2*lift (exterior a b) i j:ℝ):ℂ)
def double {I:Type*}(m:I→I→ℂ)(a b c d:I):ℂ:=m a c*m b d+m a d*m b c
theorem edge {x y:E4}(a b:Axis){t:ℝ}(ht:t≠0)(site:x-y=t • ray a b)
    (k l:G.ColorIndex)(i j:Six):
    linkEntry (x,factor k i) (y,factor l j)=if k=l then beamK a b x y i j else 0:=by
  have apart:x≠y:=fun eq=>(smul_ne_zero ht (nonzero a b)) (site.symm.trans (sub_eq_zero.mpr eq))
  rw [link_eq x y _ _ apart]
  change (↑(K (omegaLeg k _ _) (omegaLeg l _ _) x y):ℂ)=_
  rw [WilsonMeasuredPublicEntranceQuadraticKernel.original a b i j k l ht site]
  split_ifs <;> rfl

theorem physical {x y:E4}(apart:x≠y)(a b c d:Factor G):
    bond G x y (letter a*letter b) (letter c*letter d)=
      double (fun s t=>linkEntry (x,s) (y,t)) a b c d:=by
  let v:Fin 2→Fin 1:=fun _=>0
  let E:Fin 2→Factor G:=![c,d]
  let s:List (Fin 2):=[0,1]
  have back:(fun _:Fin 1=>letter c*letter d)=bag v E s:=by
    ext1 i
    fin_cases i
    simp [v,E,s,bag]
  rw [bond_eval]
  change moment G (Points.cons x (points (fun _:Fin 1=>y))) (Fin.cons _ (fun _=>letter c*letter d))=_
  rw [back,show letter a*letter b=([a,b].map letter).prod by simp,
    planted _ _ _ _ _ (pair_ok apart)]
  change pairCost linkEntry [(x,a),(x,b),(y,c),(y,d)]=_
  simp only [pair_step,pulls_cons,pulls_nil,zero_mul,mul_zero,add_zero,zero_add,link_zero]
  rw [pairCost]
  unfold double
  ring

theorem original {x y:E4}(a b:Axis){t:ℝ}(ht:t≠0)(site:x-y=t • ray a b)
    (hd:4≤d)(i j k l:Six):
    bond G x y (tile hd i j).val (tile hd k l).val=
      (G.lieDim:ℂ)*double (beamK a b x y) i j k l:=by
  have apart:x≠y:=fun eq=>(smul_ne_zero ht (nonzero a b)) (site.symm.trans (sub_eq_zero.mpr eq))
  change bond G x y (∑c:G.ColorIndex,letter (factor c i)*letter (factor c j))
    (∑c:G.ColorIndex,letter (factor c k)*letter (factor c l))=_
  simp only [map_sum,LinearMap.sum_apply,physical apart]
  have tally (h g:G.ColorIndex):
      double (fun s t=>linkEntry (x,s) (y,t)) (factor h i) (factor h j) (factor g k) (factor g l)=
      if h=g then double (beamK a b x y) i j k l else 0:=by
    by_cases same:h=g <;> simp [double,edge a b ht site,same]
  simp [tally,Gauge.ColorIndex]
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticBonds

