/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.WilsonSeparatedOriginalSlabFourierOrbit
import YM.Integration.WilsonSeparatedOriginalSlabDifferences

/-! Fourier coefficients of the physically measured test retain a fixed count of actual spatial derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierScore
open Function Set MeasureTheory UnitAddTorus WilsonSeparatedOriginalSlabFourierOrbit WilsonSeparatedOriginalSlabDifferences
open scoped Topology BigOperators Classical ContDiff
variable {J:Type*}[Fintype J]
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

omit [Fintype J] in
theorem onto: Function.Surjective (@wrap J):=by
  intro y;choose x hx using fun i:J=>QuotientAddGroup.mk_surjective (y i);exact ⟨x,funext hx⟩

theorem lift (F:C(UnitAddTorus J,ℂ))(h:J→ℝ)(n:ℕ)(x:J→ℝ):
    copies (wrap h) n F (wrap x)=steps h n (fun y=>F (wrap y)) x:=by
  induction n generalizing F x with
  | zero=>rfl
  | succ n ih=>rw [copies,ih]; rfl

theorem bounded (F:C(UnitAddTorus J,ℂ))(k:J→ℤ)(B:ℝ)(cap:∀x,‖F x‖≤B):‖mFourierCoeff F k‖≤B:=by
  have line:∀x:UnitAddTorus J,‖mFourier (-k) x • F x‖≤B:=by
    intro x; rw [norm_smul]
    have pt:‖mFourier (-k) x‖≤1:=(ContinuousMap.norm_coe_le_norm _ _).trans (le_of_eq mFourier_norm)
    exact (mul_le_mul_of_nonneg_right pt (norm_nonneg _)).trans (by simpa only [one_mul] using cap x)
  simpa [mFourierCoeff] using norm_integral_le_of_norm_le_const (μ:=(volume:Measure (UnitAddTorus J))) (Filter.Eventually.of_forall line)

theorem priced (F:C(UnitAddTorus J,ℂ))(smooth:ContDiff ℝ ∞ (fun x:J→ℝ=>F (wrap x)))(n:ℕ)(B:ℝ)(hB:0≤B)
    (cap:∀x,‖iteratedFDeriv ℝ n (fun y:J→ℝ=>F (wrap y)) x‖≤B)(k:J→ℤ)(i:J)(hi:k i≠0):
    ‖mFourierCoeff F k‖*|(k i:ℝ)|^n≤B:=by
  let a:=shift k i
  have nz:(k i:ℝ)≠0:=by exact_mod_cast hi
  have step:‖a‖≤|(k i:ℝ)|⁻¹:=by
    rw [show ‖a‖=|(1:ℝ)/2/((-(k i):ℤ):ℝ)| from Pi.norm_single _,abs_div,abs_div]
    push_cast; rw [abs_neg,abs_one,abs_of_pos (by norm_num : (0:ℝ)<2)]
    rw [div_eq_mul_inv]; exact (mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ)/2≤1) (by positivity)).trans (by simp)
  have hc:= bounded (copies (wrap a) n F) k (B*‖a‖^n) (by
    intro z; obtain ⟨x,rfl⟩:=onto z; rw [lift]; exact paid n a _ smooth B cap x)
  rw [powers n k i hi F,norm_mul,norm_pow] at hc
  have grow:1≤‖(-2:ℂ)‖^n:=one_le_pow₀ (by norm_num)
  have halt:= (le_mul_of_one_le_left (norm_nonneg (mFourierCoeff F k)) grow).trans hc
  have upper:= halt.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg a) step n) hB)
  rw [inv_pow,←div_eq_mul_inv] at upper
  exact (le_div_iff₀ (pow_pos (abs_pos.mpr nz) n)).mp upper

end YM.Integration.WilsonSeparatedOriginalSlabFourierScore
