import YM.FormalBulk08.Orb.Annex

/-! Determine leading covariance and external normalization from formal
transformation of the quadratic ledger. With parameters, this checks the shift as
well as the Hessian. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick Matrix
open scoped BigOperators
open MvPolynomial hiding map
variable {R V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq V] [Fintype V] (T D : Saddle R V)
variable (L M : Matrix V V R) (Z : V→R) (a b : R)
def tilt (Z : V→R) (L : Matrix V V R) (i : V) : Glyphs R V:=∑ j,C (L i j)*X j + C (Z i)
omit [Algebra ℚ R] [DecidableEq V] in
lemma tilt_eq (i:V) : tilt Z L i=mixRows L (X i)+C (Z i) := by simp [mixRows,tilt]
omit [Algebra ℚ R] in
lemma tilt_grad (i j : V) : pderiv i (tilt Z L j)= C (L j i) := by
   simp only [tilt,map_add,map_sum,pderiv_C_mul,pderiv_X,Pi.single_apply,pderiv_C,add_zero];simp [mul_ite]
omit [Algebra ℚ R] in
lemma pick_grad (v : V→Glyphs R V) (i : V) (F : Glyphs R V) : pderiv i (MvPolynomial.aeval v F)=∑ j,pderiv i (v j)*MvPolynomial.aeval v (pderiv j F) := by
   induction F using MvPolynomial.induction_on with
   | C a=> simp
   | add p g hp hg=> simp only [map_add,hp,hg,mul_add,Finset.sum_add_distrib]
   | mul_X p j hp=>
     simp only [map_mul,pderiv_mul,map_add,hp,aeval_X,mul_add,Finset.sum_mul,Finset.sum_add_distrib,pderiv_X,Pi.single_apply, mul_assoc];
     simp [apply_ite (MvPolynomial.aeval v),mul_ite]; ring

lemma oar (hl : L*M=1) (e : T.base+C a = aeval (tilt Z L) D.base+C b) :
    L.transpose * D.P*L=T.P ∧ Z=0 ∧ a=b := by
   have h (i) := congr_arg (pderiv i) e
   simp_rw [map_add,pderiv_C,add_zero,pick_grad,tilt_grad,Saddle.d_base] at h
   have hg i : ∑ j,C (T.P i j)*X j=∑ j,∑ k,C (L j i)* (C (D.P j k)*tilt Z L k) := by
     apply neg_injective; have hv:=h i; simp_rw [map_neg,map_sum,map_mul, aeval_C, aeval_X,mul_neg,Finset.mul_sum, Finset.sum_neg_distrib] at hv; exact hv
   let Q : V→R := L.transpose *ᵥ (D.P *ᵥ Z)
   have hz : Q=0 := by
      funext i; have hx:= congr_arg (aeval (0 : V→R) (R:=R)) (hg i);
      change (∑ j,L j i * ∑ k,D.P j k*Z k)=0
      simpa [tilt,Finset.mul_sum] using hx.symm
   have hb : Z=0 := by
      have hu : D.q*D.P=1 := mul_eq_one_comm.mpr D.inv
      have hx : D.q*ᵥ (M.transpose *ᵥ Q)=Z := by unfold Q; rw [mulVec_mulVec (M:=M.transpose) (N:=L.transpose),←transpose_mul,hl,transpose_one,one_mulVec, mulVec_mulVec,hu,one_mulVec]
      rw [←hx,hz]; simp
   have hj : L.transpose*D.P*L=T.P := by
      ext i j
      have he := congr_arg (pderiv j) (hg i)
      simp only [map_sum,pderiv_C_mul,pderiv_X,Pi.single_apply,tilt_grad] at he
      simp [mul_ite] at he -- he : C T.P = sum ...
      apply C_injective (σ:=V); rw [he]
      simp_rw [Matrix.mul_apply, Finset.sum_mul,_root_.map_sum, _root_.map_mul,transpose_apply]
      rw [Finset.sum_comm]; simp only [mul_assoc]
   refine ⟨hj,hb,C_injective (σ:=V) R ?_⟩
   have ht : C a = T.base+C a - T.base := by ring
   rw [ht,e,show aeval (tilt Z L) = mixRows L from ?hex, slide_base T D L hj]; ring
   case hex => ext i; simp [tilt_eq,hb]
end YM.FormalBulk08.Orb
