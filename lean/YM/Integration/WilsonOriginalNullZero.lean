import YM.Integration.WilsonOriginalNullClock

/-! An atom with zero paid size has zero actual masked insertion on every
field. Its full conditional return is represented by the zero coefficient
on the original receiving representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullZero
open Function Filter Lattice Wilson RG Source Extra.Histories Labels Next.Foundations
open scoped Classical BigOperators
variable {G : Gauge} {n ν : Side} {d : ℕ}

theorem masked_zero (R : Rep G n) (o : Site n) (X : Support n)
    (f : Config G n → ℂ) (c : ℝ) (hc : R.p.supBounds o X f c)
    (empty : R.p.mass X c = 0) : masked R.p.threshold X f = 0 := by
  have hzero : c = 0 := (mul_eq_zero.mp empty).resolve_left (Real.exp_pos _).ne'
  funext U
  by_cases live : Healthy R.p.threshold X U
  · rw [masked_eq _ _ _ _ live]
    apply norm_le_zero_iff.mp
    have value := hc.2 U live [] (Nat.zero_le _) (by simp)
    simpa [leftDerivs,hzero] using value
  · exact masked_ne _ _ _ _ live

theorem original (S : StepData ν n) (R : Rep G n) (R' : Rep G ν)
    (o : Site n) (X : Support n) (f : Config G n → ℂ) (c : ℝ)
    (hc : R.p.supBounds o X f c) (empty : R.p.mass X c = 0) (k : ℂ) (v : ℝ) (hv : 0 < v) :
    ∃ Y : Source.Coefficient ((Labels.frames G).level d) ν,
      Y.Format (S.ratio.parent o) (hol G) R' ∧ Y.remBound (S.ratio.parent o) R' v 0 ∧
      ((Labels.frames G).level d).coeffSize Y.x ≤ 0 ∧ ∀ W, Y.density (S.ratio.parent o)
      (Next.Foundations.localSection G d) R' W = k * S.push R.beta
      (fun U => (R.eval U : ℂ) * masked R.p.threshold X f U) W := by
  let Y := Extra.Histories.primary (F := (Labels.frames G).level d) (S.ratio.parent o) 0
  refine ⟨Y, primary_format _, primary_rem 0 hv, ?_, ?_⟩
  · simp [Y,Extra.Histories.primary,Labels.Frame.coeffSize]
  intro W
  rw [masked_zero R o X f c hc empty]
  simp [Y,primary_density,StepData.push]

end YM.Integration.WilsonOriginalNullZero
