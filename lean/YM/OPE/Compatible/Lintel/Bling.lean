import YM.OPE.Compatible.Lintel.Loma
/-!
# Forest stencil abstract CART draws
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff
variable {I J U X Y Z:Type}{G:Gauge}{n m c f:Side} {r d:ℕ}
namespace Script
open Page Virgin
variable [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][Fintype I][Fintype J][Fintype Z][DecidableEq Z]
structure Stand (A:Row J J) (M:Funds Z)(P:(X×Y)→L[ℝ] deck (I⊕J) n)(B:Module.Basis Z ℝ Y)(F:X×Y→ℝ)(g:X→Y)(Q:Script (I⊕J) 3)(C:Z≃Tab J n):Prop where
   h : Stayed F g
   p : M=deposit F g B 0
   unit : M.det≠0
   mark : Voice Q P F
   token (i:Z) : P (0,B i)= deltaH (starJ (C i))
   tariff (i j:Z): A.acts n (C i) (C j)=M⁻¹ i j
namespace Stand
variable {A:Row J J} {M:Funds Z}{P:(X×Y)→L[ℝ] deck (I⊕J) n}{B:Module.Basis Z ℝ Y}{F:X×Y→ℝ}{g:X→Y}{Q:Script (I⊕J) 3}{C:Z≃Tab J n}(s:Stand A M P B F g Q C) {x y: X×Y}
def beat (F:X×Y→ℝ)(B:Module.Basis Z ℝ Y)(p q:X×Y): Corn Z:=fun i=> iteratedFDeriv ℝ 3 F 0 ![(0,B i),p,q]
include s
omit [Fintype I] [Fintype J] in
lemma seeBeat (u v:X×Y)(i:Z) : boom Q ![P u, P v] (starJ (C i))= beat F B u v i:=by
    unfold boom beat; rw [← s.mark]; apply congr_arg; ext1 j; fin_cases j <;> first | rfl | exact (s.token i).symm
lemma corral (u v x y:X×Y)(hp:Whole A)(hx:Summable Q): library n (cotton (ROOT A) Q Q) ![P u,P v,P x,P y]= dotProduct (beat F B u v) (M⁻¹*ᵥ beat F B x y):=by
    rw [show ![P u,P v,P x,P y]=Fin.append ![P u,P v] ![P x,P y] from funext fun i=> by fin_cases i<;> rfl, dairies (ROOT A) (root_cash A hp) Q hx Q hx, rootD]
    unfold dotProduct; rw [← C.sum_comp]; refine Finset.sum_congr rfl (fun i _=>?_); let z:=boom Q ![P x,P y]; simp only [Function.comp_apply,s.seeBeat]
    apply congr_arg; unfold mulVec dotProduct; dsimp only [Function.comp_apply]; rw [← C.sum_comp]; exact Finset.sum_congr rfl fun j _=>by rw [s.tariff,s.seeBeat x y]
omit [Fintype I] [Fintype J] in
lemma balanceTerm (a b:X):cash B (fieldU g a b).2 = -(M⁻¹ *ᵥ beat F B (fieldT g a) (fieldT g b)):=by
    let k:= cash B (fieldU g a b).2; let y:=beat F B (fieldT g a) (fieldT g b); have he : M*ᵥ k= -y:= s.p.symm ▸ (show deposit F g B 0 *ᵥ k= - y from (YSolve B s.h ..)); have ht: IsUnit M.det:= s.unit.isUnit
    calc
       k=M⁻¹*ᵥ(M*ᵥ k):= by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ht, Matrix.one_mulVec]
       _= _:= by rw [he,Matrix.mulVec_neg]
omit s [Fintype I] [Fintype J] [DecidableEq Z] in -- won't accept s. remove; prove general expand
lemma expandK (D:Tensor.T (X×Y) ℝ 3)(B:Module.Basis Z ℝ Y)(a:Y)(v w:X×Y):D ![(0,a),v,w]=∑ i,cash B a i * D ![(0,B i),v,w]:=by
    let L: X×Y→L[ℝ] ℝ:= ContinuousMultilinearMap.apply ℝ _ ℝ ![v,w] ∘L D.curryLeft -- wrong CML apply
    have hl(x:X×Y):L x=D ![x,v,w]:=rfl
    let T := L ∘L ContinuousLinearMap.inr ℝ X Y; have hh(i:Y):T i=D ![(0,i),v,w]:= hl (0,i)
    rw [← hh]; conv_lhs=> rw [← B.sum_equivFun a, map_sum]
    apply Finset.sum_congr rfl fun i _=>by rw [map_smul,hh]; rfl
lemma cots (D: X)(i:X×Y)(j:X×Y)(hp:Whole A)(hx:Summable Q): -(library n (cotton (ROOT A) Q Q) ![P i,P j,P (fieldT g D),P (fieldT g D)]) = iteratedFDeriv ℝ 3 F 0 ![fieldU g D D,i,j] :=by
    rw [s.corral _ _ _ _ hp hx,s.h.lower,expandK _ B,s.balanceTerm]; let u:= fieldT g D; let v:= M⁻¹ *ᵥ beat F B u u; simp_rw [Pi.neg_apply]; change - dotProduct _ v=∑ i',-v i'*beat F B i j i'; simp_rw [neg_mul, sum_neg_distrib, dotProduct_comm (beat F B i j) v]; rfl
end Stand
end Script
end YM.OPE.Flume
