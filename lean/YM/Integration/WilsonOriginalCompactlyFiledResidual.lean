import YM.Integration.WilsonOriginalSupportedBoxChart
import YM.Integration.WilsonOriginalLocalizedResidual

/-! The actual signed polynomial remainder, including its zeroth deposited
coefficient, localized on the real box before the Fourier operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactlyFiledResidual
open Set Filter Finset UnitAddTorus
open WilsonOriginalInteriorValues (weight)
open WilsonOriginalSupportedBoxChart
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalGevreyCutoffDisc (leaf)
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalSignedTailSum (remainder)
open scoped ContDiff BigOperators Topology

def mask {d : ℕ} (l h : Space d) (f : Space d → ℂ) : Space d → ℂ :=
  fun x => weight l h x*f x

theorem supported {d : ℕ} (l h : Space d) (f : Space d → ℂ) : Supported l h (mask l h f) := by
  intro i x hx
  have zero : window (l i) (h i) (x i) = 0 := by
    rcases not_and_or.mp hx with lo|hi
    · simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp lo).le)]
    · simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp hi).le)]
  rw [mask,weight,Finset.prod_eq_zero (mem_univ i) zero,zero_mul]

theorem smooth {d : ℕ} (l h : Space d) (f : Space d → ℂ)
    (sf : ∀ x : Space d, (∀ i, x i ∈ Icc (l i) (h i)) → ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (mask l h f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases inBox : ∀ i, x i ∈ Icc (l i) (h i)
  · have wnd (i : Fin d) : ContDiff ℝ ∞ (fun y : Space d => window (l i) (h i) (y i)) :=
      (WilsonOriginalFiledBoxWindow.smooth _ _).comp (contDiff_apply ℝ ℝ i)
    exact (ContDiff.contDiffAt (contDiff_prod (fun i _ => wnd i))).mul (sf x inBox)
  · obtain ⟨i,hi⟩ := not_forall.mp inBox
    have outside : (fun z : Space d => z i) ⁻¹' (Icc (l i) (h i))ᶜ ∈ 𝓝 x :=
      (isClosed_Icc.isOpen_compl.preimage (continuous_apply i)).mem_nhds hi
    exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
      (Filter.mem_of_superset outside fun z hz => supported l h f i z hz)

def raw {d : ℕ} (l h : Space d) (f : Space d → ℂ) (a : ℕ → Space d → ℂ)
    (u : ℝ) (p : ℕ) := mask l h (fun x => f x-∑ k : Fin (p+1), (u:ℂ)^k.val*a k.val x)

theorem original {d : ℕ} (l h : Space d) (f : Space d → ℂ) (a : ℕ → Space d → ℂ)
    (u : ℝ) (p : ℕ) (v : Fin d → ℤ)
    (left : ∀ i, 0 ≤ l i) (right : ∀ i, h i ≤ 1)
    (sf : ContinuousOn f {x | ∀ i, x i ∈ Icc (0:ℝ) 1})
    (sa : ∀ k, ContinuousOn (a k) {x | ∀ i, x i ∈ Icc (0:ℝ) 1}) :
    mFourierCoeff (read (raw l h f a u p)) v =
      remainder u p (fun t => mFourierCoeff (localize 0 l h f) t)
        (fun k t => mFourierCoeff (localize 0 l h (a k)) t) v := by
  let lift (g : Space d → ℂ) (c : ContinuousOn g {x | ∀ i, x i ∈ Icc (0:ℝ) 1}) :=
    WilsonOriginalMeasuredBoxResidual.chart 0 l h g left (by simpa using right) (by simpa using c)
  have terms : read (raw l h f a u p) =
      ⇑(WilsonOriginalLocalizedResidual.field u p (lift f sf) (fun k => lift (a k) (sa k))) := by
    funext z
    simp only [WilsonOriginalSupportedBoxChart.read,raw,mask,weight,localize,WilsonOriginalLocalizedResidual.field,lift,
      WilsonOriginalMeasuredBoxResidual.chart,ContinuousMap.coe_mk,ContinuousMap.sub_apply,
      ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,Pi.zero_apply,mul_sub,Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro k _
    ring
  rw [terms,WilsonOriginalLocalizedResidual.original]
  rfl

end YM.Integration.WilsonOriginalCompactlyFiledResidual
