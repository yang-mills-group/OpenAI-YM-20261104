import YM.Contacts.Pulse.Weather
import Mathlib.RingTheory.PowerSeries.Derivative
/-! Lifting field and time derivatives through the positive hierarchy. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Filter Finset RG PowerSeries
open scoped BigOperators Topology Classical NNReal
variable {X Y : Type*} {n a b : ℕ}
namespace Form
variable [CommRing X] [CommRing Y] [Algebra ℝ X] [Algebra ℝ Y]
-- Always use ℝ scalar through tower.
def linear (v:X→ₗ[ℝ] Y): PowerSeries X→ₗ[ℝ]PowerSeries Y where
  toFun p:= PowerSeries.mk fun n=> v (coeff n p)
  map_add' f g:= by apply PowerSeries.ext; intro n; simp
  map_smul' f g:= by apply PowerSeries.ext; intro n; simp
@[simp] lemma linear_coeff (v:X→ₗ[ℝ]Y)(f:PowerSeries X) (n): coeff n (linear v f)=v (coeff n f):= by simp [linear]
-- can use PowerSeries.smul_eq_C_mul when converting plate derivative
omit [Algebra ℝ X] in
private lemma turn_swap (f g:ℕ→ X) (n) : (∑ i ∈ antidiagonal n, f i.2*g i.1)=∑ i∈antidiagonal n, f i.1*g i.2:= Eq.trans (by rfl) (Finset.Nat.sum_antidiagonal_swap (n:=n) (f:=fun i : ℕ × ℕ=> f i.1*g i.2))

def grows (D : Derivation ℝ X X): Derivation ℝ (PowerSeries X) (PowerSeries X) where
  toLinearMap := linear D.toLinearMap
  map_one_eq_zero' := by apply PowerSeries.ext; intro n; simp only [linear_coeff,map_zero,coeff_one]; cases n <;> simp
  leibniz' f g:= by
    apply PowerSeries.ext; intro n; simp only [linear_coeff,_root_.smul_eq_mul,map_add,coeff_mul,map_sum]; simp_rw [show ∀ f : X,D.toLinearMap f=D f from fun _=>rfl,Derivation.leibniz,_root_.smul_eq_mul, Finset.sum_add_distrib]
    congr 1; exact turn_swap (fun i=>coeff i g) (fun i=> D (coeff i f)) n
@[simp] lemma grows_coeff (D : Derivation ℝ X X)(f:PowerSeries X)(n) : coeff n (grows D f)= D (coeff n f) := linear_coeff ..

-- lift every derivation through exponential of positive-degree interaction
def expansion (f:PowerSeries X)(n:ℕ) := ∑ i∈ Finset.range (n+1), ((i.factorial:ℝ)⁻¹) • f^i
def breath (f:PowerSeries X): PowerSeries X:= PowerSeries.mk fun n=> coeff n (expansion f n)
variable {f:PowerSeries X}(h:coeff 0 f=0)
omit [Algebra ℝ X] in
lemma starts_late (h:coeff 0 f=0)(he:a<n): coeff a (f^n)=0:=by
  induction n generalizing a with
  | zero=> omega
  | succ n ih=>
    rw [pow_succ,coeff_mul]; apply sum_eq_zero; intro i hi; by_cases hz:i.2=0; · rw [hz,h,mul_zero]
    rw [ih (by have := mem_antidiagonal.mp hi; omega),zero_mul]
lemma breath_coeff (h:coeff 0 f=0)(he:b≤n) : coeff b (breath f)=coeff b (expansion f n):= by
  rw [breath,coeff_mk]; unfold expansion; rw [map_sum,map_sum]; apply sum_subset (by intro i hi; refine mem_range.mpr ?_; have := mem_range.mp hi; omega)
  intro i _ hi; rw [coeff_smul,starts_late h (by simp only [Finset.mem_range] at hi; omega),smul_zero]
lemma expansion_deriv (D:Derivation ℝ (PowerSeries X) (PowerSeries X)) (p:PowerSeries X)(n:ℕ): D (expansion p (n+1)) = expansion p n * D p:= by
  simp only [expansion,map_sum,sum_mul]; rw [sum_range_succ']; simp_rw [Derivation.map_smul]; simp only [pow_zero, Derivation.map_one_eq_zero,smul_zero,add_zero];
  apply sum_congr rfl; intro i _; rw [Derivation.leibniz_pow]; simp only [_root_.smul_eq_mul,add_tsub_cancel_right, ← _root_.smul_mul_assoc, Nat.factorial_succ]; rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_mul]; congr 1; field_simp
lemma breath_deriv (D:Derivation ℝ X X)(h:coeff 0 f=0): grows D (breath f)=breath f*grows D f := by
  apply PowerSeries.ext; intro i; rw [grows_coeff, breath_coeff h (Nat.le_succ i),←grows_coeff, expansion_deriv, coeff_mul,coeff_mul]; apply Finset.sum_congr rfl; intro p hp; rw [breath_coeff h (show p.1≤ i from (by have := mem_antidiagonal.mp hp; omega))]
end Form
end YM.Pulse
