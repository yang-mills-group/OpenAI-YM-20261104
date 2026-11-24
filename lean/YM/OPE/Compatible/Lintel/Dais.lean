import YM.OPE.Compatible.Lintel.Matte
/-! # Operations along vertically restricted tabs -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff
variable {I J: Type*}{G:Gauge}{n m c f:Side}{r d: ℕ}
namespace Script
open Page
variable [Fintype I] [Fintype J]
lemma vertVec (A:Row J J)(x:deck (I⊕J) n)(i:Tab I n): ((ROOT A).acts n*ᵥ x) (starI i)=0:=by
     unfold Matrix.mulVec dotProduct; simp_rw [ROOT_left,zero_mul,sum_const_zero]
lemma vertV (A:Row J J)(x:deck (I⊕J) n)(i:Tab J n): ((ROOT A).acts n*ᵥ x) (starJ i)= (A.acts n *ᵥ (x∘starJ)) i:=by
     rw [splitMargin]; simp_rw [ROOT_cross,zero_mul,sum_const_zero,zero_add]; rfl
lemma rootD (A:Row J J)(x y:deck (I⊕J) n): dotProduct x ((ROOT A).acts n *ᵥ y)=dotProduct (x∘starJ) (A.acts n *ᵥ (y ∘starJ)):=by unfold dotProduct; rw [sumBoard];simp_rw [vertVec,mul_zero,sum_const_zero,zero_add,vertV]; rfl
lemma rootTap (A:Row J J)(p : Script (I⊕J) (r+2))(x: Fin r→deck (I⊕J) n):cityTap ((ROOT A).acts n) p x=∑ i:Tab J n,∑ j:Tab J n,A.acts n i j*library n p (Fin.cons (deltaH (starJ i)) (Fin.cons (deltaH (starJ j)) x)):=by unfold cityTap; rw [sumBoard];simp_rw [ROOT_left,zero_mul,sum_const_zero,zero_add]; apply Finset.sum_congr rfl; intro i _; rw [sumBoard]; simp_rw [ROOT_cross,zero_mul,sum_const_zero,zero_add,ROOT_right]
omit [Fintype I] in
lemma summ_two_v {E:Type*}[Fintype E](w:E≃Tab J n)(f:Tab J n→ Tab J n→ℝ): (∑ i:Tab J n,∑ j:Tab J n,f i j)=∑ i:E,∑ j:E,f (w i) (w j):=by rw [← w.sum_comp]; exact sum_congr rfl (fun i _=> (w.sum_comp (f _)).symm)
end Script
end YM.OPE.Flume
