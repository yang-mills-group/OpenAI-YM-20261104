import YM.Comparison.RG02.Valence.Script
import Mathlib.Algebra.MvPolynomial.Funext
/-! Padding the Gaussian list by formal external-slot keys. Exact receipts, also for complex data.
No positivity or regulator/gap role when reprojecting. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence
open Function Filter Finset YM.Analysis YM.Marker YM.Multi Cumulants Cumulants.Wick
open YM.Extra.Trajectories (connected)
open YM.Next.Rank
open scoped Topology BigOperators Classical ContDiff

namespace Stamp
open MvPolynomial Normal
variable {I J : Type*} (Q : Normal.Symmetric I) (μ : J→ℂ) (p : I→ℂ)
def pad (Q : Symmetric I) : Symmetric (I⊕J) where
   cov := Sum.elim (fun i=>Sum.elim (Q.cov i) (fun _=>0)) (fun _=>fun _=>0)
   symm i j := by rcases i with i|i <;> rcases j with j|j <;> first | rfl | exact Q.symm ..
def descend : Normal.poly (I⊕J) →ₐ[ℂ] Normal.poly I := aeval (Sum.elim X (fun j=> C (μ j)))
-- verify push-forward on corresponding blend. Cov stays in original gauge legs, cup = external constants
lemma inl (i:I): descend (I:=I) μ (X (.inl i))=X i:= aeval_X ..
lemma inr (j:J): descend (I:=I) μ (X (.inr j))=C (μ j):= aeval_X ..
lemma down (c:ℂ): descend (I:=I) μ (C c)=C c:= aeval_C ..
lemma slits (x : I) (f : Normal.poly (I⊕J)) : descend μ (slit ((pad Q).cov (.inl x)) f)=slit (Q.cov x) (descend μ f) := by
   let L := slit (Q.cov x); have he (v:Normal.poly I) (z:ℂ): L (C z*v)=C z*L v:=by rw [L.leibniz,show L (C z)=0 from slit_C ..]; simp
   induction f using MvPolynomial.induction_on with
   | C a=> rw [down]; simp
   | add b c h H=> rw [map_add,map_add,h,H,map_add,map_add]
   | mul_X f i h=>
      rw [mul_comm f]; simp only [slit_prod, map_add, map_mul (descend μ),down,h]; rcases i with i|j
      · simp only [inl, pad, slit_prod,Sum.elim_inl]
      simp only [inr,pad,Sum.elim_inl,Sum.elim_inr,map_zero,zero_mul,add_zero]; exact (he (descend μ f) (μ j)).symm

lemma milk_down (f : Normal.poly (I⊕J)) : descend μ (milk (pad Q) f)=milk Q (descend μ f) := by
   induction f using MvPolynomial.induction_on with
   | C a=> rw [fine,down,fine]
   | add b c h H=> rw [map_add,map_add,h,H,map_add,map_add]
   | mul_X f i h=>
      rw [mul_comm f,feeds,map_add,map_mul,map_mul]
      rcases i with i|j
      · rw [inl,slits Q μ i,h,feeds]
      rw [show (pad Q).cov (.inr j)=(0:I⊕J→ℂ) from _root_.funext fun _=> rfl,slit_zero,map_zero,add_zero,inr,h,drink]

lemma direction : (aeval p).comp (descend (I:=I) μ) = aeval (Sum.elim p μ) := by
   ext i; rw [AlgHom.comp_apply, aeval_X]; rcases i with i|j
   · rw [inl, aeval_X]; rfl
   rw [inr,aeval_C]; rfl
lemma attends (f : Normal.poly (I⊕J)) : blend Q p (descend μ f)=blend (pad Q) (Sum.elim p μ) f := by
   rw [blend_components,blend_components,← milk_down]; exact DFunLike.congr_fun (direction μ p) _

variable {V : Type*} [DecidableEq V] {R : Census V}
lemma with_legs (P : V→ Normal.poly (I⊕J)) :
    moments R (blend Q p) (fun i => descend μ (P i))=moments R (blend (pad Q) (Sum.elim p μ)) P := by
   ext1 t; rw [moments_part,moments_part,← map_prod,attends]
end Stamp
end YM.Comparison.RG02.Valence
