import YM.FormalBulk08.Wick.Ash

/-! Compare Gaussians and retain parameters. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series
open scoped Classical BigOperators
variable {R S : Type*} {V U : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
variable [Fintype V] [Fintype U] (q : V → V → R) (f : R →+* S) (t : U→U→R)
open MvPolynomial
lemma halve_map (a : R) : f (halve a)=halve (f a) := by simp [halve]
lemma press_map (p : Glyphs R V) : map f (press q p)=press (fun i j=>f (q i j)) (map f p) := by simp [press_eq,pderiv_map,halve_map]
lemma bake_map (p : Glyphs R V) : Polynomial.map (map f) (bake q p)=bake (fun i j=> f (q i j)) (map f p) := by
   ext1 n; rw [Polynomial.coeff_map,bake_coeff,bake_coeff,smul_eq_C_mul,smul_eq_C_mul,_root_.map_mul,map_C,ounce_map]
   congr 1
   induction n with
   | zero=> simp
   | succ n ih=> rw [pow_succ',Module.End.mul_apply,pow_succ',Module.End.mul_apply,press_map,ih]
lemma hearth_map (p : Glyphs R V) : map f (hearth q p)=hearth (fun i j=> f (q i j)) (map f p) := by
   rw [hearth_def,hearth_def,← bake_map]; simp
lemma moment_map (p : Glyphs R V) : f (moment q p)=moment (fun i j=> f (q i j)) (map f p) := by
   simp_rw [moment_eq,← hearth_map]
   have he : f.comp (MvPolynomial.aeval (R:=R) (0 : V→R)).toRingHom = (MvPolynomial.aeval (R:=S) (0 : V→S)).toRingHom.comp (map f) := by ext <;> simp
   exact DFunLike.congr_fun he _

omit [Algebra ℚ R] in
def mixRows (F : U→V→R) : Glyphs R U →ₐ[R] Glyphs R V:= MvPolynomial.aeval fun i=> ∑ j,C (F i j)*X j

omit [Algebra ℚ R] in
lemma pderiv_mix (F : U→V→R) (i : V) (p : Glyphs R U) : pderiv i (mixRows F p)=∑ j,C (F j i)*mixRows F (pderiv j p) := by
   induction p using MvPolynomial.induction_on with
   | C c=> simp [mixRows]
   | add p r hp hr=> simp only [map_add,hp,hr,mul_add,Finset.sum_add_distrib]
   | mul_X p j hp=>
      have h : pderiv i (mixRows F (X j))=C (F j i) := by simp [mixRows,Pi.single_apply, mul_ite,eq_comm]
      rw [_root_.map_mul,pderiv_mul,h,hp];
      simp_rw [pderiv_mul,map_add,_root_.map_mul,pderiv_X,Pi.single_apply,apply_ite (mixRows F), mul_ite,map_zero,map_one,mul_one,mul_zero,mul_add];
      simp_rw [Finset.sum_mul,Finset.sum_add_distrib]; simp only [mul_assoc,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]; ring

lemma slide_trail (F : U→V→R) (hs : ∀ i j,q i j=q j i) (ht : ∀ i j,t i j=t j i) (hf : ∀ i j,t i j = ∑ u,∑ v,F i u*F j v*q u v) (p : Glyphs R U) :
    moment q (mixRows F p)=moment t p := by
   let A : Glyphs R U →ₗ[R] R := (moment q).comp (mixRows F).toLinearMap
   have ha : A=moment t := moment_unique t ht A (by simp [A]) (fun p i=> by
       change moment q (mixRows F (X i*p))=_
       rw [_root_.map_mul,show mixRows F (X i)=_ from MvPolynomial.aeval_X (fun i=> ∑ j,C (F i j)*X j) i]
       simp_rw [Finset.sum_mul,_root_.map_sum,mul_assoc,C_mul',map_smul,smul_eq_mul,paired q hs,pderiv_mix F,_root_.map_sum, C_mul',map_smul,smul_eq_mul,hf,Finset.mul_sum,Finset.sum_mul]
       simp_rw [Finset.sum_comm (s:= (Finset.univ : Finset V)) (t:= (Finset.univ : Finset U))]
       apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; simp [A];ring)
   exact DFunLike.congr_fun ha p
end YM.FormalBulk08.Wick
