import YM.FVAAlt2.Grass
/-! Saturating the ghost slots. Uses alternating algebra over an arbitrary ring,
so applies directly with coefficients of finite arity Bose kernels and power series.
No integration by parts *in a Grassmann-valued measure*. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Glue
open Finset Function Matrix
variable {R : Type*} {J:Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (q: Matrix J J R) (hn:∀ i j k,q i k*q j k=0)(hv:∀ i j k l,q i k*q j l= -(q i l*q j k))

def prize (i:J): (J→R)→ₗ[R] R:=∑ j:J, q i j • LinearMap.proj (R:=R) j
omit [DecidableEq J] in
lemma prize_eq(i:J) (f:J→R): prize q i f=∑ j:J,q i j*f j:=by rw [prize,LinearMap.sum_apply];rfl
include hn hv in
private lemma prize_zero (i j:J)(f:J→R): prize q i f*prize q j f=0:=by
 rw [prize_eq,prize_eq]; suffices h:∀ s:Finset J,(∑ a∈s,q i a*f a)*(∑ a∈s,q j a*f a)=0 from h univ
 intro s; induction s using Finset.induction with
 | empty=> simp
 | insert a s h ih=>
   rw [sum_insert h,sum_insert h,mul_add,add_mul,add_mul,ih]
   have he(k): q i k*f k*(q j a*f a)=-(q i a*f a*(q j k*f k)):= calc
      _=q i k*q j a*(f a*f k):=by ring
      _=_:=by rw [hv i j k a]; ring
   rw [Finset.sum_mul,show q i a*f a*(q j a*f a)=0 from by rw [mul_mul_mul_comm, hn]; simp]
   simp_rw [he,Finset.sum_neg_distrib,← Finset.mul_sum]; ring -- abel

open scoped Classical in
-- uses target decidableeq to control multiplicity of diagonal terms
private def painter : AlternatingMap R (J→R) R J := by
 let L:= (MultilinearMap.mkPiAlgebra R J R).compLinearMap (fun i:J=> prize q i)
 refine { L with map_eq_zero_of_eq' := ?_ }
 intro X i j he h
 change (∏ k:J, prize q k (X k))=0
 rw [ ← Finset.mul_prod_erase univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase (univ.erase i) _ (Finset.mem_erase.mpr ⟨Ne.symm h,Finset.mem_univ j⟩), ←mul_assoc, he, prize_zero q hn hv, zero_mul]

include hn hv
lemma determinant (x:Matrix J J R): (∏ i:J,∑ j:J,q i j*x i j)=(∏ i:J,q i i)* x.det := by
 let e:= Pi.basisFun R J
 let L:= painter q hn hv
 have h(y: J→J→R): L y= ∏ i, ∑ j,q i j*y i j:= by simp_rw [← prize_eq]; rfl
 have hv :e.toMatrix (fun i=> x i) =x.transpose:= by ext; simp [e,Module.Basis.toMatrix_apply]
 have hE: L e=∏ i,q i i:=by rw [h]; simp [e, Pi.single_apply]
 rw [← Matrix.det_transpose x,← hv, ← Module.Basis.det_apply,← hE]
 calc
   _ = L (fun i=> x i):= (h _).symm
   _ = _ := DFunLike.congr_fun (AlternatingMap.eq_smul_basis_det e L) (fun i=> x i) -- type order
end YM.FVAAlt2.Glue
