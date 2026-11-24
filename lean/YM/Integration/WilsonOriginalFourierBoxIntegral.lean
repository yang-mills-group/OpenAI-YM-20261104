import YM.Integration.WilsonOriginalFiledBoxWindow
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! The normalized torus coefficient is the integral of the original field
against its signed, compactly supported Fourier test in the physical chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFourierBoxIntegral
open Set Filter Finset MeasureTheory AddCircle UnitAddTorus
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalBoxFourierProfiles (frequency)
open WilsonOriginalModulatedProfiles (wave)

def box {d : ℕ} (a : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Ioc (a i) (a i+1)}

def test {d : ℕ} (l h : Fin d → ℝ) (v : Fin d → ℤ) (x : Fin d → ℝ) : ℂ :=
  ∏ i, (window (l i) (h i) * wave (frequency (v i))) (x i)

def localize {d : ℕ} (a l h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ)
    (z : UnitAddTorus (Fin d)) : ℂ :=
  let x : Fin d → ℝ := fun i => (AddCircle.equivIoc (1:ℝ) (a i) (z i)).val
  (∏ i, window (l i) (h i) (x i))*f x

theorem original {d : ℕ} (a l h : Fin d → ℝ) (v : Fin d → ℤ) (f : (Fin d → ℝ) → ℂ)
    (left : ∀ i, a i ≤ l i) (right : ∀ i, h i ≤ a i+1) :
    mFourierCoeff (localize a l h f) v = ∫ x, test l h v x*f x := by
  rw [mFourierCoeff_eq_integral _ _ a]
  have phase (k : ℤ) (s : ℝ) : fourier (-k) (s : UnitAddCircle) = wave (frequency k) s := by
    rw [fourier_coe_apply]
    simp only [wave,frequency,Complex.ofReal_one,div_one,Int.cast_neg]
    congr 1;ring
  have expr (x : Fin d → ℝ) (hx : x ∈ box a) :
      mFourier (-v) (fun i => (x i : UnitAddCircle)) •
        localize a l h f (fun i => (x i : UnitAddCircle)) = test l h v x*f x := by
    have seat (i : Fin d) : (AddCircle.equivIoc (1:ℝ) (a i) (x i)).val = x i :=
      AddCircle.equivIoc_coe_of_mem (hx i)
    simp only [mFourier,ContinuousMap.coe_mk,Pi.neg_apply,phase,localize,seat,smul_eq_mul,
      test,Pi.mul_apply,Finset.prod_mul_distrib]
    ring
  change (∫ x in box a, _) = _
  have hbox : box a = ⋂ i, (fun x : Fin d → ℝ => x i) ⁻¹' Ioc (a i) (a i+1) := by
    ext x;simp [box]
  have measurable : MeasurableSet (box a) := by
    rw [hbox]
    exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioc
  rw [setIntegral_congr_fun measurable expr]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have outside : ∃ i, x i ∉ Ioc (a i) (a i+1) := by
    simpa [box] using hx
  obtain ⟨i,hi⟩ := outside
  have van : window (l i) (h i) (x i) = 0 := by
    rcases not_and_or.mp hi with low|high
    · simp [window,WilsonOriginalGevreyCutoffDisc.leaf,
        expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr ((not_lt.mp low).trans (left i)))]
    · simp [window,WilsonOriginalGevreyCutoffDisc.leaf,
        expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr ((right i).trans (not_le.mp high).le))]
  have gone : test l h v x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [van])
  rw [gone,zero_mul]

end YM.Integration.WilsonOriginalFourierBoxIntegral
