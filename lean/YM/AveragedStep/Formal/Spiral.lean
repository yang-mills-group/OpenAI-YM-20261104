import YM.AveragedStep.Formal.Wicks
import Mathlib.Analysis.Analytic.IteratedFDeriv
/- Diagonal jet differentiation on the analytic germ, no period bound
intended at this algebraic stage. Reconcile normalization with score
jets of Orders/Template. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open PertExtension.Series.Radial
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
lemma incline_front (f:X→ℝ)(hf:ContDiffAt ℝ ω f 0)(k:ℕ)(x u:X)(i:Fin (k+1)) :
    iteratedFDeriv ℝ (k+1) f 0 (update (fun _=>x) i u)= iteratedFDeriv ℝ k (fun y=> fderiv ℝ f y u) 0 (fun _=> x):=by
 let σ:= Equiv.swap i (Fin.last k)
 let Z := update (fun _:Fin (k+1)=>x) i u
 rw [← hf.iteratedFDeriv_comp_perm Z σ,iteratedFDeriv_succ_apply_right]
 let p:=fderiv ℝ f
 let a:=ContinuousLinearMap.apply ℝ ℝ u
 have hp: ContDiffAt ℝ ω p 0:=hf.fderiv_right (m:=ω) (by simp)
 rw [show (fun y=>fderiv ℝ f y u)=a ∘ p from rfl,a.iteratedFDeriv_comp_left hp le_top]
 have hz:(Z∘σ) (Fin.last k)=u:=by simp [Z,σ,Function.comp_apply]
 have hy:Fin.init (Z∘σ)=fun _=> x:=by
   funext j; change update (β:=fun _:Fin (k+1)=>X) (fun _=> x) i u (σ j.castSucc)=x
   apply update_of_ne
   rintro he
   have : σ j.castSucc=σ (Fin.last k):= he.trans (Equiv.swap_apply_right ..).symm
   have h:(j.castSucc:Fin (k+1))=Fin.last k:=σ.injective this
   exact Fin.ne_of_lt (Fin.castSucc_lt_last j) h
 rw [hz,hy]; rfl

def dup (k:ℕ):X→L[ℝ] (Fin k→X):=ContinuousLinearMap.pi fun _=> ContinuousLinearMap.id ℝ X
lemma radial_front (f:X→ℝ)(hf:ContDiffAt ℝ ω f 0)(k:ℕ)(x u:X): fderiv ℝ (jet f (k+1)) x u=jet (fun y=>fderiv ℝ f y u) k x:=by
 let D:=dup (X:=X) (k+1)
 let I:=iteratedFDeriv ℝ (k+1) f 0
 let c:ℝ:= ((k+1).factorial:ℝ)⁻¹
 change fderiv ℝ (fun x=>c * (I (D x))) x u=_
 have he:=(((I.hasFDerivAt (D x)).comp (g:=I) x (D.hasFDerivAt)).const_mul c).fderiv
 rw [show (fun x=>c*I (D x))=fun x=>c*(I∘D) x from rfl,he, _root_.smul_apply,ContinuousLinearMap.comp_apply,ContinuousMultilinearMap.linearDeriv_apply]; change c*(∑ i,I (update (fun _=>x) i u))= _
 simp only [I,incline_front f hf,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,jet,c,Nat.factorial,Nat.cast_mul,Nat.cast_add,Nat.cast_one]; field_simp; simp
end YM.AveragedStep.SD
