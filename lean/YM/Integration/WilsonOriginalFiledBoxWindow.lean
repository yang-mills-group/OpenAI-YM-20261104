import YM.Integration.WilsonOriginalGevreyWindow
import YM.Integration.WilsonOriginalBoxFourierProfiles

/-! The concrete compact box used for the Fourier tests has smooth real
windows, a fixed interior lower bound, and the required modulation cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledBoxWindow
open Set Finset
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalGevreyCutoffDisc (leaf)
open WilsonOriginalBoxFourierProfiles (frequency)
open WilsonOriginalModulatedProfiles (wave)
open WilsonOriginalFourierLattice (height)

theorem smooth (a b : ℝ) {n : ℕ∞} : ContDiff ℝ n (window a b) :=
  (WilsonOriginalGevreyWindow.smooth.comp (contDiff_id.sub contDiff_const)).mul
   (WilsonOriginalGevreyWindow.smooth.comp (contDiff_const.sub contDiff_id))

theorem compact (a b : ℝ) : HasCompactSupport (window a b) := by
  apply HasCompactSupport.intro' (isCompact_Icc : IsCompact (Icc a b)) isClosed_Icc
  intro x hx
  rcases not_and_or.mp hx with h|h
  · simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp h).le)]
  · simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp h).le)]

theorem norm_window (a b x : ℝ) :
    ‖window a b x‖ = expNegInvGlue (x-a)*expNegInvGlue (b-x) := by
  simp [window,leaf,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (expNegInvGlue.nonneg _)]

theorem interior {a b x δ : ℝ} (gap : 0 < δ) (left : δ ≤ x-a) (right : δ ≤ b-x) :
    0 < (expNegInvGlue δ)^2 ∧ (expNegInvGlue δ)^2 ≤ ‖window a b x‖ := by
  have pos := expNegInvGlue.pos_of_pos gap
  refine ⟨sq_pos_of_pos pos,?_⟩
  rw [norm_window,pow_two]
  exact mul_le_mul (expNegInvGlue.monotone left) (expNegInvGlue.monotone right)
    pos.le (expNegInvGlue.nonneg _)

theorem original {d : ℕ} (a b x : Fin d → ℝ) (v : Fin d → ℤ) (order : Fin d → ℕ) :
    ‖∏ i, iteratedDeriv (order i) (window (a i) (b i) * wave (frequency (v i))) (x i)‖ ≤
    (∏ i, ((2:ℝ)^(order i)*(32^(order i)*((order i).factorial:ℝ)^2))*
      (1+2*Real.pi)^(order i))*(1+(height v:ℝ))^(∑ i,order i) := by
  apply WilsonOriginalBoxFourierProfiles.original
  · exact fun i => (smooth ..).contDiffAt
  · intro i; positivity
  · intro i k hk
    apply (WilsonOriginalGevreyWindow.original _ _ _ k).trans
    gcongr; norm_num

end YM.Integration.WilsonOriginalFiledBoxWindow
