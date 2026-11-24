import YM.FormalBulk08.Wick.Vane

/-! Invertible leading substitution covariance. Formula suitable also with vacuum sources. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series PowerSeries Matrix
open scoped BigOperators
variable {R V : Type*} [CommRing R] [Fintype V] [DecidableEq V]
variable (L M : Matrix V V R)
def quilt (y : V→Plate R V) : V→Plate R V:=(PowerSeries.C.comp MvPolynomial.C).mapMatrix L *ᵥ y
lemma quilt_apply (y : V→Plate R V) (i) : quilt L y i =∑ j,C (MvPolynomial.C (L i j))*y j := rfl
lemma quilt_mul (y : V→Plate R V) : quilt (L*M) y=quilt L (quilt M y) := by unfold quilt; rw [_root_.map_mul,mulVec_mulVec]
@[simp] lemma quilt_one (y : V→Plate R V) : quilt 1 y=y := by unfold quilt; rw [_root_.map_one,one_mulVec]
lemma blend_change (y : V→Plate R V) (p : Plate R V): roam R y (PowerSeries.map (mixRows L).toRingHom p)=roam R (quilt L y) p := by
   unfold roam;rw [change_after];
   have h : (insertAt R y).comp (mixRows L).toRingHom = insertAt R (quilt L y) := by ext <;> simp [mixRows,quilt_apply]
   rw [h]
lemma quilt_zero (y : V→Plate R V) (i) : coeff 0 (quilt L y i)= MvPolynomial.aeval (fun i=>coeff 0 (y i)) (mixRows L (MvPolynomial.X i)) := by
   rw [quilt_apply]; simp [mixRows, coeff_zero_eq_constantCoeff_apply]
lemma back_stem (y : V → Plate R V) (hy : ∀ i,coeff 0 (y i)=mixRows L (MvPolynomial.X i)) (hm : M*L=1) (i) : coeff 0 (quilt M y i)=MvPolynomial.X i := by
   rw [quilt_zero]; simp_rw [hy]
   simp only [mixRows, MvPolynomial.aeval_X,map_sum, _root_.map_mul,MvPolynomial.aeval_C];
   simp_rw [show algebraMap R (Glyphs R V)=MvPolynomial.C from rfl, Finset.mul_sum]; rw [Finset.sum_comm]; simp_rw [←mul_assoc,←map_mul MvPolynomial.C,←Finset.sum_mul, ←map_sum, ←Matrix.mul_apply,hm,Matrix.one_apply]; simp [apply_ite MvPolynomial.C,ite_mul]
lemma clock_mix (y : V→ Plate R V) : clock (quilt L y)= (PowerSeries.C.comp MvPolynomial.C).mapMatrix L*clock y := by
   ext1 i j; change shaft (MvPolynomial.pderiv (R:=R) j) (quilt L y i)=∑ k,C (MvPolynomial.C (L i k))*shaft (MvPolynomial.pderiv j) (y k)
   rw [quilt_apply]; simp
lemma beam_swing [Algebra ℚ R] (T : Saddle R V) (p : Plate R V) (a:R) : beam T.call (C (MvPolynomial.C a)*p)=C a*beam T.call p := by ext1 n; simp [coeff_C_mul,MvPolynomial.C_mul']

variable [Algebra ℚ R]
/-- all coefficients calculated at same base coupling. Both Gauss variations include leading normalization; no absolute scalar implied. -/
theorem pivot (T D : Saddle R V) (F : Plate R V) (y : V → Plate R V) (h : L.transpose * D.P * L = T.P) (hl : L*M=1) (hm : M*L=1) (hy : ∀ i,coeff 0 (y i)=mixRows L (MvPolynomial.X i)) :
   beam T.call ((clock y).det * expan (roam R y (C D.base)-C T.base)*roam R y F)=C L.det*beam D.call F := by
    let z:=quilt M y
    have he:=smooth T z (PowerSeries.map (mixRows L).toRingHom F) (back_stem _ _ _ hy hm)
    have hx : quilt L z=y := by unfold z; rw [←quilt_mul,hl,quilt_one]
    rw [blend_change,hx,slide_series T D L M hl hm h] at he
    rw [←he,show roam R y (C D.base)=roam R z (C T.base) by
         rw [←hx,←blend_change,PowerSeries.map_C, show (mixRows L).toRingHom D.base=T.base from slide_base T D L h]]
    have hz : (clock y).det=C (MvPolynomial.C (L.det))*(clock z).det := by nth_rw 1 [←hx, clock_mix]; rw [Matrix.det_mul,←RingHom.map_det]; rfl
    rw [hz,mul_assoc,mul_assoc,beam_swing,mul_assoc]
end YM.FormalBulk08.Wick
