import YM.Integration.WilsonConditionalTaylorKineticProjection
import YM.Integration.WilsonMarkedScalarEquation

/-! The full real formal scalar prescribed by the finite physical two-leg
action. Its inverse is the change of coupling in the original tilt map. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorKineticRebooking

open Finset Function PowerSeries Lattice RG Wilson Precision Exterior Push.Uniform MSbar MSbar.Rolling
open MSbar.Midpoint MSbar.Bakery MSbar.Cacao MSbar.Wave FormalBulk08 FormalBulk08.Series
open WilsonConditionalTaylorKineticProjection WilsonMarkedScalarEquation
open scoped BigOperators Classical

variable {G : Gauge} {c : Side} (v : G.Color) (T : PowerSeries (MSbar.Cacao.Pot (Primary c G)))
    (K : MSbar.Cacao.Pot (Primary c G))

def projection : PowerSeries ℝ := mk fun i=>caliper c v (coeff i T)

def primitive : PowerSeries ℝ := 1-C (caliper c v K)⁻¹ * projection v T

private theorem capped (f b : PowerSeries ℝ) (n : ℕ) :
    Through n (f.subst (X*b)) (table n (fun j=>coeff j f) b) := by
  have head : coeff 0 (X*b)=0 := by simp [coeff_zero_eq_constantCoeff_apply]
  intro i hi
  rw [subst_coeff head f n i hi,table,map_sum]
  simp only [coeff_C_mul]

theorem read (b : PowerSeries ℝ) : projection v (bley b T K) =
    (projection v T).subst (X*b⁻¹) * b^2 - C (caliper c v K)*(b^2-1) := by
  ext1 i
  have finite:=(capped (projection v T) b⁻¹ i).mul (Through.exact_eq (b^2) i) i le_rfl
  simp only [projection,coeff_mk] at finite ⊢
  rw [_root_.map_sub (coeff i),finite,table,Finset.sum_mul,map_sum,coeff_C_mul]
  unfold bley ticket
  rw [_root_.map_sub,_root_.map_sub,coeff_mk,map_sum,coeff_mk,map_smul,smul_eq_mul]
  congr 1
  · apply sum_congr rfl
    intro j hj
    rw [row,term,if_pos (Nat.le_of_lt_succ (mem_range.mp hj)),mul_comm (b^2) ((b⁻¹)^j)]
  · ring

theorem head (kind : Kind T) : Wine.Fresh (primitive v T K) := by
  change coeff 0 (1-C _*projection v T)=1
  rw [map_sub,coeff_one,if_pos rfl,coeff_C_mul,projection,coeff_mk,kind,map_zero,mul_zero,sub_zero]

theorem inverse (A : PowerSeries ℝ) : (Wine.bookU A)⁻¹=Wine.bookH A := by
  have valid : constantCoeff (Wine.bookU A)≠0 :=
    ((coeff_zero_eq_constantCoeff_apply _).symm.trans (Wine.book_guard A)).trans_ne one_ne_zero
  calc
    _=(Wine.bookH A*Wine.bookU A)*(Wine.bookU A)⁻¹ := by rw [Wine.book_equal,one_mul]
    _=_:=by rw [mul_assoc,PowerSeries.mul_inv_cancel _ valid,mul_one]

theorem clears (kind : Kind T) (den : caliper c v K≠0) :
    projection v (bley (Wine.bookU (primitive v T K)) T K)=0 := by
  let H:=primitive v T K
  let b:=Wine.bookU H
  let B:=Wine.bookH H
  let q:=projection v T
  let k:=caliper c v K
  let a:=C k
  let t:=C k⁻¹
  have unit : a*t=1 := by dsimp only [a,t]; rw [←map_mul,mul_inv_cancel₀ den,map_one]
  have fresh : Wine.Fresh H:=head v T K kind
  have credit := Wine.correction_read H fresh
  have at0 : coeff 0 (X*B)=0 := by simp [coeff_zero_eq_constantCoeff_apply]
  have sub : H.subst (X*B)=1-t*(q.subst (X*B)) := by
    change (1-C k⁻¹*q).subst (X*B)=_
    rw [←PowerSeries.coe_substAlgHom (tribe at0),map_sub,map_one,map_mul]
    have fixed : (PowerSeries.substAlgHom (R:=ℝ) (tribe at0)) (C k⁻¹)=C k⁻¹ :=
      (PowerSeries.substAlgHom (R:=ℝ) (tribe at0)).commutes _
    rw [fixed]
  change H.subst (Wine.runic H)*b^2=1 at credit
  rw [←Wine.forward_green,sub] at credit
  rw [read,inverse]
  change q.subst (X*B)*b^2-a*(b^2-1)=0
  calc
    _=a-a*b^2+(a*t)*(q.subst (X*B)*b^2) := by rw [unit];ring
    _=a-a*((1-t*q.subst (X*B))*b^2) := by ring
    _=0 := by rw [credit,mul_one,sub_self]

end YM.Integration.WilsonConditionalTaylorKineticRebooking
end

