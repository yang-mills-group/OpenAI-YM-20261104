import YM.Integration.WilsonThermometerMixedWages
import YM.Integration.WilsonOriginalThermometerTollBudget

/-! The two original temperatures at the last separated return use the native
Wilson band. All three radius reductions have one fixed physical cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedThermal
open Filter Finset RG Wilson FVA1 RG16.Literal Marker QuadraticLocal WilsonGeometricSignedCapture
open Filter Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Advent PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6
open Pert.Asymptotics AllOrder
open scoped Classical BigOperators
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) {N per j:ℕ} (live:j+1 ≤ N)
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per (j+1)
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
local notation "H" => R.family.path.levels.clock.hatBeta (j+1)
local notation "H₀" => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin 3)

include simple live in
theorem heat : 0 < g ∧ 0 < g₀ ∧ g ≤ 2*g₀ ∧ g^2*H ≤ 2 ∧ H₀ ≤ H := by
  let hi := R.family.path.β N per (j+1)
  let lo := R.family.path.β N per j
  have gj := ActualRunKernelPackets.regulator_pos R N per j (by omega)
  have gs := ActualRunKernelPackets.regulator_pos R N per (j+1) live
  have a : 0 < Real.sqrt hi := inv_pos.mp gs
  have b : 0 < Real.sqrt lo := inv_pos.mp gj
  have band₁ : H/2 ≤ hi := (R.makes.wilson.represents N per (j+1) live).band.1
  have band₀ : lo ≤ 2*H₀ := (R.makes.wilson.represents N per j (by omega)).band.2
  have mono:H₀ ≤ H:=WilsonStartup.Timing.hat_mono R.family.path.levels
    (Gauge.slopeConstant_pos simple).le (Nat.le_succ j)
  have ah : Real.sqrt hi^2=hi:=Real.sq_sqrt (Real.sqrt_pos.mp a).le
  have bh : Real.sqrt lo^2=lo:=Real.sq_sqrt (Real.sqrt_pos.mp b).le
  have root : Real.sqrt lo ≤ 2*Real.sqrt hi := by
    have cmp : Real.sqrt lo^2 ≤ (2*Real.sqrt hi)^2 := by nlinarith only [ah,bh,band₁,band₀,mono]
    exact (sq_le_sq₀ b.le (by positivity)).mp cmp
  refine ⟨gs,gj,?_,?_,mono⟩
  · change (Real.sqrt hi)⁻¹ ≤ 2*(Real.sqrt lo)⁻¹
    rw [←div_eq_mul_inv,le_div_iff₀ b,mul_comm (Real.sqrt hi)⁻¹,←div_eq_mul_inv,div_le_iff₀ a]
    exact root
  · change (Real.sqrt hi)⁻¹^2*H ≤ 2
    rw [inv_pow,inv_mul_le_iff₀ (sq_pos_of_pos a),ah]
    linarith only [band₁]

include simple live in
theorem wages (c:(J).Mode→ℂ)(w:Fin 3→ℝ)(hp:∀v,0 < w v)
    {x r y F : ℝ} (hx:1 ≤ x)(hr:1 ≤ r)(hy:1 ≤ y)(nx:x ≤ H)(refund:r ≤ 2*H₀)(ny:y ≤ H₀)
    (l:ℕ)(paid:g^l*weightBill c w ≤ F) :
    g^(l+78)*weightBill c (Stoop.radius (Stoop.radius (Stoop.radius w (x^6)) r) (y^6)) ≤
      ((2:ℝ)^6*4*2^6)^3*F := by
  obtain ⟨gp,_,_,band,mono⟩ := heat R simple live
  apply WilsonThermometerMixedWages.scaled c w hp hx hr hy gp l _ _ _ paid
  · exact (mul_le_mul_of_nonneg_left nx (sq_nonneg _)).trans band
  · have rr := mul_le_mul_of_nonneg_left (refund.trans (mul_le_mul_of_nonneg_left mono (by norm_num : (0:ℝ)≤2))) (sq_nonneg (g))
    nlinarith only [rr,band]
  · exact (mul_le_mul_of_nonneg_left (ny.trans mono) (sq_nonneg _)).trans band
end YM.Integration.WilsonThermometerMixedThermal
end
