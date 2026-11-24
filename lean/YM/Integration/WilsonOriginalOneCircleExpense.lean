import YM.Integration.WilsonOriginalCircleFourierJets

/-! Repeated integrations by parts use the actual periodic section of the
field. Only derivatives along this one real coordinate enter the estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOneCircleExpense
open AddCircle MeasureTheory Set
open scoped Interval Topology

theorem original (F : UnitAddCircle → ℂ) (v : ℤ) (hv : v ≠ 0) (n : ℕ) (C : ℝ)
    (smooth : ∀ j t, t ∈ Icc (0:ℝ) 1 → DifferentiableAt ℝ
      (iteratedDeriv j (fun s : ℝ => F s)) t)
    (price : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedDeriv n (fun s : ℝ => F s) t‖ ≤ C) :
    ‖(2*(Real.pi:ℂ)*Complex.I*(v:ℂ))^n * fourierCoeff F v‖ ≤ C := by
  let f := fun t : ℝ => F t
  have periodic : (fun t : ℝ => f (t+1)) = f := by
    funext t;simp [f]
  have endpoints (j : ℕ) : iteratedDeriv j f 1 = iteratedDeriv j f 0 := by
    have e := congrFun (iteratedDeriv_comp_add_const j f 1) 0
    rw [periodic] at e
    simpa only [zero_add] using e.symm
  have step (j : ℕ) (t : ℝ) (ht : t ∈ [[(0:ℝ),1]]) :
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j+1) f t) t := by
    rw [iteratedDeriv_succ]
    exact (smooth j t (by simpa [uIcc_of_le zero_le_one] using ht)).hasDerivAt
  have buy := WilsonOriginalPeriodicSliceJets.original (fun j => iteratedDeriv j f) v hv step endpoints n
  simp only [iteratedDeriv_zero] at buy
  rw [← WilsonOriginalCircleFourierJets.clocked,← show f = fun t : ℝ => F t from rfl,buy,
    fourierCoeffOn_eq_integral]
  simp only [sub_zero,div_one,one_smul]
  have cost := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1) (C:=C)
    (f:=fun t : ℝ => fourier (-v) (t:UnitAddCircle) • iteratedDeriv n f t) (by
      intro t ht
      have hm : t ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (((fourier (-v) : C(UnitAddCircle,ℂ)).norm_coe_le_norm _).trans_eq (fourier_norm _))).trans (price t hm))
  simpa using cost

end YM.Integration.WilsonOriginalOneCircleExpense
