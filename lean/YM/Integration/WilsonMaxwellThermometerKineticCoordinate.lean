import YM.Integration.WilsonPositionRawPolynomial
import YM.Integration.WilsonPositionGradedThermometerHearing

/-! The unsubtracted original thermometer and the kinetic coordinate of the independently
fitted target. The printed constant travels on the same mesh as the signed slope. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticCoordinate
open Set Filter Function Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Scale MS MS.WilsonBridge.Coupling PowerSeries
open WilsonPositionRawMesh
open scoped BigOperators Classical Polynomial
variable {G : Gauge} (Z : WilsonPrescription G) (m : Mesh) (q : ℕ)

def ground : ℝ := (coeff 0 (Rose.Detector Z.scheme Z.criterion m)).re

def printed (u : ℝ) : ℝ := ∑ j : Fin (q+1),
  (coeff j (Rose.Detector Z.scheme Z.criterion m)).re * u^(j:ℕ)

theorem centered (u : ℝ) :
    forward Z m q u = (printed Z m q u - ground Z m) / Rose.c_T Z.criterion := by
  classical
  let b (j : Fin (q+1)) := (coeff j (Rose.Detector Z.scheme Z.criterion m)).re * u^(j:ℕ)
  have z : detector Z m q 0 = 0 := by
    change (coeff 0 (Rose.chosen Z.scheme Z.criterion m)).re = 0
    rw [coeff_zero_eq_constantCoeff_apply,Rose.zero_choice]; rfl
  have e (i : Fin q) :
      detector Z m q i.succ * u^(i.succ:ℕ) = b i.succ / Rose.c_T Z.criterion := by
    rw [detector, Rose.puts Z.scheme Z.criterion m _ (by simp),←Complex.ofReal_inv,
      Complex.re_ofReal_mul]
    dsimp [b]
    ring
  have total : printed Z m q u = ground Z m + ∑ j : Fin q, b j.succ := by
    change (∑ j, b j) = _
    rw [Fin.sum_univ_succ]
    simp [b,ground]
  rw [WilsonPositionRawMesh.forward, Fin.sum_univ_succ, z, zero_mul, zero_add, total, add_sub_cancel_left, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => e i

/-- The finite comparison uses the original unshifted seven-face reading and the filed
target with all its lower-field corrections; the same internal real appears on both. -/
theorem bill {d n : ℕ} (φ : Test n) (v : Tags G d n) (u : ℝ) (reading target : ℂ)
    (use : Rose.Use Z.scheme Z.criterion m) (hu : |u|≤1)
    (hr : |reading.re / Rose.c_T Z.criterion|≤1) (hf : |forward Z m q u|≤1) :
    ‖target - WilsonPositionFiniteMSBank.finite Z m d φ v q (reading.re / Rose.c_T Z.criterion)‖ ≤
      ‖target - (trunc (q+1) (said (WilsonPositionRawFiling.published Z m d) φ v)).eval (u:ℂ)‖ +
      (slope Z m q d φ v *
       ((|reading.re - printed Z m q u| + |ground Z m|) / |Rose.c_T Z.criterion|) +
        price Z m q d φ v * |u|^(q+1)) := by
  have meter : |reading.re / Rose.c_T Z.criterion - forward Z m q u| ≤
      (|reading.re - printed Z m q u| + |ground Z m|) / |Rose.c_T Z.criterion| := by
    rw [centered,←sub_div,abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [sub_sub_eq_add_sub,add_sub_right_comm]
    exact abs_add_le ..
  have nonneg : 0 ≤ slope Z m q d φ v := Finset.sum_nonneg fun _ _ => by positivity
  have h := finite_change Z m q d φ v u (reading.re / Rose.c_T Z.criterion) hu hr hf
  rw [WilsonPositionRawPolynomial.issued Z m q d φ v use, norm_sub_rev] at h
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (le_refl _) (h.trans (add_le_add (mul_le_mul_of_nonneg_left meter nonneg) (le_refl _))))

end YM.Integration.WilsonMaxwellThermometerKineticCoordinate

