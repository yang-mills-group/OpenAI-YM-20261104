import YM.QuadraticLocal.Close
import YM.Integration.WilsonCloseCaptureDate
import YM.Pert.Asymptotics.RawAxis

/-! The original stage budgets over the physical capture interval, expressed
in the measured coupling on that same Wilson torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseInterval
open Filter Lattice Wilson RG RG16 QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "H" => R.alloy.B.a.clock.hatBeta
local notation "β" => R.family.path.β

private theorem currency {x y : ℝ} (hx : 4 ≤ x) (lower : x/2 ≤ y)
    {η : ℝ} (ep : 0 < η) : x^(η/4) ≤ ((Real.sqrt y)⁻¹)^(-η) := by
  have y0 : 0 < y := by linarith
  have fit : x ≤ y^2 := by nlinarith only [lower,hx,sq_nonneg (y-2)]
  have yp : (Real.sqrt y)⁻¹=y^(-(1/2:ℝ)) := by rw [Real.rpow_neg y0.le,Real.sqrt_eq_rpow]
  rw [yp, ←Real.rpow_mul y0.le]
  calc
    _ ≤ (y^2)^(η/4) := Real.rpow_le_rpow (by linarith) fit (by positivity)
    _ = _ := by rw [← Real.rpow_natCast y 2, ← Real.rpow_mul y0.le]; congr 1; norm_num; ring

private theorem compare {x y : ℝ} (xp : 0 < x) (yp : 0 < y) (near : y ≤ 8*x) :
    (Real.sqrt x)⁻¹ ≤ 3*(Real.sqrt y)⁻¹ := by
  have a := Real.sqrt_pos.mpr xp
  have b := Real.sqrt_pos.mpr yp
  have bound : Real.sqrt y ≤ 3*Real.sqrt x := by
    nlinarith only [a,b,near, Real.sq_sqrt xp.le,Real.sq_sqrt yp.le,
      sq_nonneg (3*Real.sqrt x+Real.sqrt y),sq_nonneg (Real.sqrt x)]
  rw [← one_div, ← div_eq_mul_inv, le_div_iff₀ b, div_mul_eq_mul_div, one_mul, div_le_iff₀ a]
  exact bound

include simple in
theorem purchased (degree arity : ℕ) {Q η : ℝ} (qpos : 0 ≤ Q) (ep : 0 < η) :
    ∀ᶠ b : ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree Q m b →
      ∀ N per : ℕ, b ≤ N →
      (∀ i : ℕ, m ≤ i → i ≤ b → (PaceR.roof R i b)^(arity+2) ≤
        (regulatorRun R.family N per b)^(-η)) ∧
      (∀ i : ℕ, m ≤ i → i ≤ b → regulatorRun R.family N per i ≤ 3*regulatorRun R.family N per b) := by
  have tends : Tendsto H atTop atTop :=
    tendsto_const_nhds.add_atTop (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [PaceR.gives R simple degree (arity+2) Q qpos (η/4) (by positivity),
    PaceR.covers_hat R simple degree Q,tends.eventually_ge_atTop (4:ℝ)] with b bill temp warm
  intro m mb close N per top
  obtain ⟨lo,hi⟩ := (R.makes.wilson.represents N per b top).band
  have pos : 0 < β N per b := by change H b/2 ≤ β N per b at lo; linarith
  constructor
  · intro i mi ib
    exact (bill m i mi ib close).trans (currency warm lo ep)
  · intro i mi ib
    have earlier := (R.makes.wilson.represents N per i (ib.trans top)).band.1
    have half := temp i m mi ib close
    change H i/2 ≤ β N per i at earlier
    change β N per b ≤ 2*H b at hi
    have xp : 0 < β N per i := by linarith only [half,earlier,warm]
    exact compare xp pos (by linarith only [hi,half,earlier])

end YM.Integration.WilsonReceivedCloseInterval
