import YM.Integration.WilsonThermometerCenteredCompensation

/-! Restore the fixed cost of the same three-source thermometer when its
booked entrance or returned aperture is the reciprocal of one common fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredRadius
open ConnectedActivityE6 Finset Marker Filter Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open WilsonFiniteOrdinaryInverse RG Wilson PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
local notation "cost" => WilsonFiniteOrdinaryInverse.fee J

theorem restore (Q : Poly J) (w : Fin 3 → ℝ) {c g : ℝ} (gp : 0<g) (small : g≤1)
    (costly : 1≤c) (rwgt : ∀ v,w v=c⁻¹)
    (budget : Poly.price (fun v=>g*w v) (inverseMass Q) ≤ cost) :
    g^3*(∑ s : (J).Mode,‖weight Q s‖) ≤ c^3*cost := by
  have cp : 0<c := zero_lt_one.trans_le costly
  have pp : 0<g/c := div_pos gp cp
  have small' : g/c≤1 := (div_le_one cp).2 (small.trans costly)
  have funs : (fun v=>g*w v) = (fun _ : Fin 3=>(g/c)*(1:ℝ)) := by
    funext v; rw [rwgt v,mul_one,div_eq_mul_inv]
  rw [funs] at budget
  have fee := WilsonThermometerCenteredCompensation.faces Q (fun _=>1) (g/c) pp small' 0
    (fun t=>by simp [Poly.toll]) budget
  simp only [Nat.add_zero] at fee
  calc
    g^3*(∑ s : (J).Mode,‖weight Q s‖) = c^3*((g/c)^3*(∑ s : (J).Mode,‖weight Q s‖)) := by field_simp
    _ ≤ c^3*cost := mul_le_mul_of_nonneg_left fee (pow_nonneg cp.le _)

theorem temperature {G : Gauge} (R : Run G) (N per j : ℕ) (hj : j≤N) :
    let g := Coat.gStep (R.family.path.rep N per j).beta
    R.alloy.B.a.clock.hatBeta j*g^2 ≤ 2 := by
  intro g
  let b := (R.family.path.rep N per j).beta
  have band := (R.makes.wilson.represents N per j hj).band
  change R.alloy.B.a.clock.hatBeta j/2 ≤ b ∧ b ≤ 2*R.alloy.B.a.clock.hatBeta j at band
  have bp : 0<b := Overlay.beta_positive R.makes.wilson hj
  have sq : g^2 = b⁻¹ := by change (Real.sqrt b)⁻¹^2 = _; rw [inv_pow,Real.sq_sqrt bp.le]
  rw [sq,←div_eq_mul_inv]
  exact (div_le_iff₀ bp).2 (by linarith only [band.1])

theorem charge (Q : Poly J) {c C g y : ℝ} (d : ℕ) (gp : 0<g) (cp : 0≤c)
    (non : 0≤C) (yn : 0≤y) {κ : ℝ} (band : y*g^2 ≤ κ) (cap : c≤C*y^d)
    (wallet : g^3*(∑ s : (J).Mode,‖weight Q s‖) ≤ c^3*cost) :
    g^(3+6*d)*(∑ s : (J).Mode,‖weight Q s‖) ≤ (C*κ^d)^3*cost := by
  have k0 : 0≤κ := (mul_nonneg yn (pow_nonneg gp.le _)).trans band
  have pay : c*g^(2*d) ≤ C*κ^d := by
    calc _ ≤ (C*y^d)*g^(2*d) := mul_le_mul_of_nonneg_right cap (pow_nonneg gp.le _)
         _ = C*(y*g^2)^d := by rw [mul_pow,pow_mul]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg yn (pow_nonneg gp.le _)) band d) non
  have fc : 0≤cost := sum_nonneg (fun n _=>pow_nonneg (add_nonneg zero_le_one
    (sum_nonneg (fun s _=>mul_nonneg (by norm_num) (Nat.cast_nonneg _)))) _)
  calc
    _ = g^(6*d)*(g^3*(∑ s : (J).Mode,‖weight Q s‖)) := by rw [pow_add]; ring
    _ ≤ g^(6*d)*(c^3*cost) := mul_le_mul_of_nonneg_left wallet (pow_nonneg gp.le _)
    _ = (c*g^(2*d))^3*cost := by rw [mul_pow,←pow_mul]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg cp (pow_nonneg gp.le _)) pay 3) fc

end YM.Integration.WilsonThermometerCenteredRadius
