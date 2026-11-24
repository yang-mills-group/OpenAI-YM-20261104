import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic

/-! Positive-order exponential over ℝ algebras. Coefficient formulas keep
factorials; no substitution convergence. Lift any derivation on coefficients
(here time and field derivatives only). -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram.Formal
open Finset PowerSeries Function
open scoped ENNReal BigOperators Classical PowerSeries
variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℝ R] [Algebra ℝ S]

private def uplift (D:Derivation ℝ R R)(p:R⟦X⟧) : R⟦X⟧:= PowerSeries.mk fun i=> D (coeff i p)
private lemma uplift_v (D:Derivation ℝ R R)(p:R⟦X⟧)(i): coeff i (uplift D p)=D (coeff i p):=coeff_mk ..
/-- coefficientwise derivation, not the formal coupling derivative -/
def farther (D:Derivation ℝ R R):Derivation ℝ R⟦X⟧ R⟦X⟧ where
 toFun:=uplift D
 map_add' P Q:=by ext i; simp_rw [uplift_v,map_add, uplift_v]
 map_smul' r P:=by ext i; change coeff _ (uplift D _)=coeff _ (r • _); rw [uplift_v,coeff_smul,coeff_smul,D.map_smul,uplift_v]
 map_one_eq_zero' := by ext i;change coeff i (uplift D _) =_;simp [uplift_v,PowerSeries.coeff_one,apply_ite D]
 leibniz' p q:= by
   ext i; change coeff i (uplift D (p*q))=coeff i (p*(uplift D q)+q*uplift D p); simp only [uplift_v,map_add,coeff_mul,map_sum]
   simp_rw [D.leibniz, Finset.sum_add_distrib,smul_eq_mul]; congr 1
   exact Finset.sum_bij (fun a ha=> (a.2,a.1)) (fun a h=> Finset.mem_antidiagonal.mpr ((add_comm ..).trans (Finset.mem_antidiagonal.mp h))) (fun a _ b _ h=> Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1) (fun a h=> ⟨(a.2,a.1),Finset.mem_antidiagonal.mpr ((add_comm ..).trans (Finset.mem_antidiagonal.mp h)),rfl⟩) (fun _ _=> rfl)
lemma farther_v (D:Derivation ℝ R R)(p:R⟦X⟧)(i): coeff i (farther D p)=D (coeff i p):= uplift_v ..

/-- Finite coefficient formula used throughout. -/
def truncP (f:R⟦X⟧)(n:ℕ):R⟦X⟧:= ∑ i∈range (n+1), (i.factorial:ℝ)⁻¹ • f^i
def expo (f:R⟦X⟧): R⟦X⟧:= PowerSeries.mk fun i=>coeff i (truncP f i)

lemma exp_start (f:R⟦X⟧): coeff 0 (expo f)=1:=by simp [expo,truncP]
omit [Algebra ℝ R] in
lemma high_order {f:R⟦X⟧}(h:coeff 0 f=0){n i:ℕ}(hi:i<n): coeff i (f^n)=0:=by
 induction n generalizing i with
 | zero=> omega
 | succ n ih=>
     rw [pow_succ,coeff_mul]; apply sum_eq_zero;intro x hx;have H:=Finset.mem_antidiagonal.mp hx
     by_cases hh:x.1<n
     · rw [ih hh,zero_mul]
     rw [show x.2=0 by omega, h,mul_zero]
lemma expo_any {f:R⟦X⟧}(h:coeff 0 f=0){n i:ℕ}(hh:i≤n): coeff i (expo f)=coeff i (truncP f n):=by
 rw [expo,coeff_mk]; simp_rw [truncP,map_sum]; apply sum_subset (range_mono (by omega))
 intro q hv hj; have hh : i<q:=by rw [mem_range] at hj; omega
 rw [coeff_smul,high_order h hh,smul_zero]
lemma rise_exp (D:Derivation ℝ R R)(f:R⟦X⟧)(n:ℕ): farther D (truncP f (n+1)) = truncP f n * (farther D f):=by
 unfold truncP; rw [map_sum,sum_range_succ']; simp_rw [Derivation.map_smul]; simp only [pow_zero,Derivation.map_one_eq_zero,smul_zero,add_zero]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=>?_
 let H:=farther D
 have hv : (i+1-1:ℕ)=i:=by omega
 rw [H.leibniz_pow, hv, smul_eq_mul, ← smul_mul_assoc]
 -- module factorial
 rw [← smul_mul_assoc, ← Nat.cast_smul_eq_nsmul ℝ (i+1),smul_smul]
 congr 2
 rw [Nat.factorial_succ]; push_cast; field_simp
lemma derive_exp {f:R⟦X⟧}(h:coeff 0 f=0)(D:Derivation ℝ R R) : farther D (expo f)=expo f* farther D f := by
 ext i
 calc
   _ = coeff i (farther D (truncP f (i+1))) :=by rw [farther_v,farther_v,expo_any h (Nat.le_succ i)]
   _ = _ :=by rw [rise_exp, coeff_mul, coeff_mul]; exact Finset.sum_congr rfl fun j hj=> by rw [expo_any h (show j.1 ≤ i from by have hx:= Finset.mem_antidiagonal.mp hj;omega)]
lemma map_exp (G:R→ₐ[ℝ] S)(f:R⟦X⟧):PowerSeries.map G.toRingHom (expo f)=expo (PowerSeries.map G.toRingHom f):=by
 ext i; simp_rw [PowerSeries.coeff_map, expo,PowerSeries.coeff_mk,truncP,map_sum,coeff_smul]
 apply Finset.sum_congr rfl; intro k h; rw [← map_pow,PowerSeries.coeff_map]; exact G.toLinearMap.map_smul _ _
end YM.RegulatorIR.Diagram.Formal
