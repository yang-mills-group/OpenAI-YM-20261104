import YM.FVA2.Recall.Euler
import YM.PertExtension.CoefficientLimit
import Mathlib.RingTheory.PowerSeries.Derivative
/-! # Moment generating function in the gauge quadratic argument -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall.Book
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint Euler PertExtension PertExtension.Series Radial GaussianScore
open scoped Classical Topology BigOperators ContDiff
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (L:Law E)[MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure]
local notation "d"=> Module.finrank ℝ E
local notation "H"=> Euler.fuel L.P
local notation "I"=> Papers.opening μ L

variable (t:Permit E){j:ℕ}(h: Paint.Values t j)
include h
def factor (n:ℕ):= (( Nat.factorial n:ℝ )⁻¹)* I (H^n*t)
local notation "M"=> factor L μ t
omit [MeasurableSpace E] [BorelSpace E] in
lemma powers (n:ℕ) : Paint.Values (H^n*t) (2*n+j):= by
 intro x y; have he(x:E): (H^n*t).val x=(H).val x ^ n * t.val x:= by change ((papers E).val (H^n*t)) x=_; simp only [map_mul,map_pow,Pi.pow_apply,Pi.mul_apply]; rfl
 rw [he, he,h,homo_fuel,pow_add,pow_mul]; ring
lemma equ (n:ℕ) : 2*(n+1:ℕ)*factor L μ t (n+1) = ((d+2*n+j:ℕ):ℝ)*factor L μ t n:= by
 have hp: ((n+1:ℕ):ℝ)≠0:= by norm_cast
 have hx:= Euler.Prices.twoH L μ (powers L t h n)
 unfold factor; rw [ Nat.factorial_succ, Nat.cast_mul,pow_succ',mul_assoc (H),mul_inv_rev ]; -- goal
 push_cast at *; field_simp; linarith -- simplify d?

-- external univariate PS without determinant shift yet
omit h

def archive := PowerSeries.mk (factor L μ t)
local notation "G"=> archive L μ t
local notation "D"=> PowerSeries.derivative ℝ
lemma archive_c (i:ℕ): coeff i (G)=M i:= coeff_mk ..
lemma archive_z : constantCoeff (G)=I t:= by rw [←coeff_zero_eq_constantCoeff_apply,archive_c]; simp [factor]
include h
lemma climb : C (2:ℝ)*((1-X)*D G)=C ((d+j:ℕ):ℝ)*G:= by
 apply PowerSeries.ext; intro i; rw [coeff_C_mul,coeff_C_mul,sub_mul,one_mul,map_sub,coeff_derivative,archive_c,archive_c]; obtain H':= equ L μ t h i; cases i with
 | zero=> rw [coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_X,zero_mul,sub_zero]; norm_num at *; exact H' -- orientation
 | succ k=> rw [coeff_succ_X_mul, coeff_derivative,archive_c]; push_cast at *; linarith
end YM.FVA2.Recall.Book
namespace YM.FVA2.Recall.Move
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint PertExtension PertExtension.Series Radial GaussianScore
open scoped Classical Topology BigOperators ContDiff
variable (m:Move)
abbrev drift : PowerSeries ℝ:= 1-m.q^2
@[simp] lemma drift0 : constantCoeff ( drift m )=0:= by simp [drift,m.initial]
local notation "D"=> PowerSeries.derivative ℝ
variable (k: ℕ) (P:PowerSeries ℝ)

lemma climbs (h:C (2:ℝ)*((1-X)*D P)=C (k:ℝ)*P) : P.subst (m.drift) = C (constantCoeff P)*m.p^k := by
 let ζ:= P.subst m.drift; let A:= constantCoeff P; let N:= C (k:ℝ); let q:= m.q; have ho:=m.drift0; have hx:=HasSubst.of_constantCoeff_zero' ho; have he: q*m.p=1:= mul_comm ..|>.trans m.old; have hs: q≠0:=fun ht=> by rw [ht,zero_mul] at he; exact zero_ne_one he
 have hζ: C (2:ℝ)*(q^2*D ζ) = C (k:ℝ)*ζ * (-(q*D q + q* D q)):= by
    unfold ζ; rw [derivative_subst ℝ hx]; obtain hP:= congr_arg (fun v:PowerSeries ℝ=> (substAlgHom hx) v) h; rw [ show D (m.drift)= -(q*D q+q*D q) from ?_ ]; swap
    · unfold drift; rw [map_sub, pow_two,Derivation.leibniz, Derivation.map_one_eq_zero, zero_sub];rfl
    simp only [ map_mul, map_sub, map_one, PowerSeries.coe_substAlgHom,subst_X hx,subst_C ] at hP; rw [show 1-drift m=q^2 from sub_sub_cancel 1 _] at hP; rw [←mul_assoc (q^2), ←mul_assoc]
    exact congr_arg (· * _) hP
 -- first-order
 have hi := congr_arg (fun v:PowerSeries ℝ=> v) hζ
 have ht:q*D ζ + (k:PowerSeries ℝ)*D q*ζ=0:= by
    rw [ map_ofNat, map_natCast ] at hζ; -- maybe
    apply mul_left_cancel₀ (show 2*q ≠ 0 from mul_ne_zero (fun H=> by have he:= congr_arg constantCoeff H; rw [ map_ofNat, map_zero] at he; norm_num at he) hs); rw [mul_zero]; linear_combination hζ
 have hw : constantCoeff ζ= A:= by unfold ζ; rw [← coeff_zero_eq_constantCoeff_apply, Position.AlignSeries.subst_finite ho]; simp [A]
 have hh : D (q^k * ζ)=0:= by
    cases k with
    | zero=> simp only [pow_zero,one_mul]; rw [Nat.cast_zero,zero_mul,zero_mul, add_zero] at ht; exact (mul_eq_zero.mp ht).resolve_left hs
    | succ k=> rw [ Derivation.leibniz, derivative_pow,pow_succ ]; change _ * _ + ζ * ( ((k+1:ℕ):PowerSeries ℝ) * (q^(_-1)) * _)=_; rw [Nat.add_sub_cancel]; linear_combination (q^k) * ht
 have hp:q^k*ζ=C A:= PowerSeries.derivative.ext (hh.trans ( PowerSeries.derivative_C A ).symm) (by rw [ map_mul,map_pow,show constantCoeff q=1 from m.initial,one_pow, one_mul, constantCoeff_C ]; exact hw)
 calc
    _ = (q*m.p)^k * ζ:= by rw [he,one_pow,one_mul]
    _ = (q^k*ζ)*m.p^k:= by rw [mul_pow];ring
    _ = _:= congr_arg (· * _) hp
end YM.FVA2.Recall.Move
