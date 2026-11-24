import YM.FormalBulk08.Plait.Page

/-! Rank2 identical normalization with counting basis minus signs. Use trace lemma for curve and cross. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Wick Orb Series MvPolynomial
open Matrix (of)
open scoped BigOperators Topology Classical Matrix
variable {R S V I:Type*}[CommRing R][Algebra ℚ R] [Fintype V]

section algebra
def rect (T:Matrix V V R): Glyphs R V:= -∑ i,∑ j, C (halve (T i j))*X i*X j
lemma rectangle {T:Matrix V V R}(h:Tᵀ=T)(i : V): pderiv i (rect T)= -∑ j,C (T i j)*X j:= by
   simp_rw [rect,map_neg,_root_.map_sum,mul_assoc,pderiv_C_mul,pderiv_mul,pderiv_X,Pi.single_apply,mul_ite,ite_mul,zero_mul,mul_zero,mul_one,one_mul,mul_add,mul_ite,mul_zero]
   congr 1
   -- trace
   simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_ite_irrel,Finset.mem_univ,↓reduceIte,Finset.sum_const_zero]; rw [←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
   rw [show T j i=T i j from congr_fun (congr_fun h i) j,←add_mul,←_root_.map_add,half_twice]
lemma rect_corner (T:Matrix V V R): constantCoeff (rect T)=0 := by simp [rect]
lemma rect_trim {T:Matrix V V R}(h:Tᵀ=T)(i: V): constantCoeff (pderiv i (rect T))=0:= by rw [rectangle h]; simp
lemma rect_cease {T:Matrix V V R}(h:Tᵀ=T)(i j:V): pderiv i (pderiv j (rect T)) = -C (T i j) := by
   rw [rectangle h j]; simp only [map_neg,_root_.map_sum,pderiv_C_mul,pderiv_X, Pi.single_apply, mul_ite,mul_zero,mul_one]; simp [eq_comm]; rw [show T j i=T i j from congr_fun (congr_fun h i) j]
lemma pull_x (Q : Matrix V V R)(h:Qᵀ=Q)(p:Glyphs R V)(i j:V):
   moment (fun i j=>Q i j) (X i*X j*p)= Q i j*moment Q p + ∑ a,∑ b,Q i a*Q j b* moment Q (pderiv b (pderiv a p)) := by
   let q:= fun i j=> Q i j; have hx i j: q i j=q j i:=congr_fun (congr_fun h j) i
   rw [mul_assoc]; change moment q (X i * (X j*p))=q i j*moment q p+ ∑ a,∑ b,q i a*q j b*moment q (pderiv b (pderiv a p)); rw [paired q hx]; simp only [pderiv_mul,pderiv_X,Pi.single_apply,ite_mul,one_mul,zero_mul,map_add,apply_ite (moment q),map_zero,paired q hx,mul_add,mul_ite,mul_zero, Finset.sum_add_distrib,Finset.sum_ite_eq, Finset.mem_univ,↓reduceIte, Finset.mul_sum, mul_assoc]
lemma moment_rect (Q T:Matrix V V R)(h:Qᵀ=Q)(p:Glyphs R V):
   moment (fun i j=>Q i j) (rect T*p)= -halve ((Q*T).trace)*moment (fun i j=>Q i j) p -(∑ i, ∑ j,∑ a, ∑ b, (halve (T i j))*Q i a*Q j b *moment (fun i j=>Q i j) (pderiv b (pderiv a p))) := by
   have he i j: C (σ:=V) (halve (T i j))*X i*X j*p = C (halve (T i j))*(X i*X j*p):= by ring
   unfold rect;simp_rw [neg_mul, Finset.sum_mul,he,map_neg,_root_.map_sum,C_mul',map_smul,smul_eq_mul,pull_x Q h]
   simp_rw [mul_add, Finset.sum_add_distrib,neg_add]; rw [sub_eq_add_neg]; congr 2 -- may close
   · unfold halve; simp_rw [Matrix.trace,Matrix.diag, Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul, mul_assoc]; rw [Finset.sum_comm];refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ;rw [show Q j i=Q i j from congr_fun (congr_fun h i) j]; ring
   simp_rw [Finset.mul_sum,mul_assoc]
lemma income_rect (Q T:Matrix V V R)(h:Qᵀ=Q): moment Q (rect T)= -halve ((Q*T).trace) := by simpa using moment_rect Q T h 1
-- sum of traces rearrange
omit [Algebra ℚ R] in lemma charge_trace (Q A T:Matrix V V R)(hp:Qᵀ=Q) : (Q*A*Q*T).trace=∑ i,∑ j,∑ a,∑ b, A i j*Q i a*Q j b*T b a:= by
    unfold Matrix.trace; simp_rw [Matrix.diag,Matrix.mul_apply,Finset.sum_mul];
    let g i j a b:= A i j*Q i a*Q j b*T b a
    have he b j i a : Q b j * A j i * Q i a * T a b=g j i b a:= by rw [show Q b j= Q j b from congr_fun (congr_fun hp j) b];unfold g;ring
    simp_rw [he]; change (∑ a:V,∑ b:V,∑ j:V,∑ i:V,g i j a b)=∑ i:V,∑ j:V,∑ a:V,∑ b:V,g i j a b
    have hx a b: (∑ j:V,∑ i:V,g i j a b) = ∑ x:V×V,g x.1 x.2 a b:= by rw [Finset.sum_comm,Fintype.sum_prod_type]
    simp_rw [hx]; calc
        _ = ∑ x:V×V, ∑ w:V×V,g w.1 w.2 x.1 x.2:= (Fintype.sum_prod_type ..).symm
        _ = _:= by rw [Finset.sum_comm,Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]
lemma square_rep (Q T:Matrix V V R)(h:Tᵀ=T)(hp:Qᵀ=Q): moment Q (rect T*rect T)= moment Q (rect T)*moment Q (rect T)+halve ((Q*T*Q*T).trace) := by
    rw [moment_rect Q T hp, ← income_rect Q T hp,charge_trace Q T T hp]; simp_rw [rect_cease h, map_neg,moment_C,mul_neg, Finset.sum_neg_distrib,sub_neg_eq_add]; unfold halve;simp_rw [Finset.mul_sum,mul_assoc]
end algebra
lemma Tally.rect {n:ℕ}{M:Matrix V V (TypeR I)}(h:∀ i j, (M i j).IsHomogeneous n): Tally (rect M) (n+2):= by
   unfold Plait.rect; refine (Tally.sum _ (fun i _=> Tally.sum _ (fun j _=> ((Tally.base (p:=halve (M i j)) ?_).mul Tally.xt).mul Tally.xt))).neg
   rw [halve,show (algebraMap ℚ (TypeR I)) _=C (1/2:ℝ) by rw [IsScalarTower.algebraMap_apply ℚ ℝ]; congr; norm_num]; apply IsHomogeneous.C_mul (h ..)
end YM.FormalBulk08.Plait
