import YM.MSbar.Cacao.Flow
import Mathlib.Algebra.MvPolynomial.Derivation
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open PowerSeries Finset Function
open scoped BigOperators Classical
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B] (f g h:PowerSeries A)(m n : ℕ)
local notation "G"=> PowerSeries A
def pulled (f : A →ₗ[ℝ] B) : PowerSeries A→ₗ[ℝ]PowerSeries B where
   toFun m:= PowerSeries.mk fun i=> f (PowerSeries.coeff i m)
   map_add' m m':= PowerSeries.ext fun i=>by simp
   map_smul' r m:= PowerSeries.ext fun i=>by simp only [PowerSeries.coeff_mk,RingHom.id_apply,PowerSeries.coeff_smul,map_smul]
lemma ride (e:A→ₗ[ℝ] B)(p:G)(i:ℕ): PowerSeries.coeff i (pulled e p)=e (PowerSeries.coeff i p):=coeff_mk i (fun i=>e (PowerSeries.coeff i p))
omit [Algebra ℝ A] in
lemma elevator (f : PowerSeries A)(g : PowerSeries A)(i:ℕ): PowerSeries.coeff i (f*g)=∑ j∈range (i+1),PowerSeries.coeff j f* PowerSeries.coeff (i-j) g:=by rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk] -- Nat vs Finset.Nat
-- Leibniz maps.D comm. on G.
variable (D:A→ₗ[ℝ] A)(hD : ∀ x y, D (x*y)=D x*y+x*D y)
local notation "F"=>pulled D
include hD
lemma ascent (f g:G): F (f*g)=F f*g+f* F g:=by
    apply PowerSeries.ext; intro j; rw [ride,elevator,map_sum,_root_.map_add,elevator,elevator,← Finset.sum_add_distrib]; refine sum_congr rfl ?_; intro i hi; rw [ride,ride,hD]
lemma powers (f:G)(n:ℕ): F (f^(n+1)) = (n+1:ℝ) • (F f*f^n):=by
    induction n with
    | zero=> simp
    | succ n ih=> rw [pow_succ _ (n+1),ascent D hD,ih,smul_mul_assoc,mul_assoc (F f),← pow_succ,mul_comm (_^(n+1))]; push_cast; simp only [add_smul,one_smul] -- edit
lemma from_1 (n:ℕ): ((n+1).factorial:ℝ)⁻¹ * (n+1:ℝ) = (n.factorial:ℝ)⁻¹ :=by
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one]; have h : 0<(n+1:ℝ):=by positivity
    field_simp
-- D coeff.
lemma up (f:G)(n:ℕ) : F (Aroma f (n+1))=F f *Aroma f n :=by
    have hz : F 1=0:=by have hh:= ascent D hD (1:G) 1; simp only [one_mul,mul_one] at hh; exact add_left_cancel (hh.symm.trans (add_zero _).symm)
    unfold Aroma; rw [map_sum, Finset.sum_range_succ',Finset.mul_sum]; simp only [map_smul,pow_zero,hz,smul_zero,add_zero]; apply sum_congr rfl; intro i hi; rw [powers D hD,smul_smul, from_1 D hD i, mul_smul_comm] -- binder
lemma springUp (hf:Kind f): F (Spring f)= F f * Spring f:=by
    apply PowerSeries.ext; intro n
    rw [ride,issues hf (Nat.le_add_right n 1), ← ride, up D hD]; refine Lap.rises (f:=F f) (k:=n) (fun i _=> rfl) ?_ n le_rfl; intro i hi; exact (issues hf hi).symm
omit hD in
lemma solitary (hf:Kind f): IsUnit (Spring f):= by apply PowerSeries.isUnit_iff_constantCoeff.mpr; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, covers hf]; exact isUnit_one
end YM.MSbar.Cacao
