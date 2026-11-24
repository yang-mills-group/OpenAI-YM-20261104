import YM.Integration.WilsonOriginalFiledBoxWindow

/-! The fixed-order profile price of every authentic compactly supported
product test, including all lower derivative orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalUniformBoxProfiles
open Set Finset
open WilsonOriginalFourierLattice (height)
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalBoxFourierProfiles (frequency)
open WilsonOriginalModulatedProfiles (wave)
open scoped ContDiff BigOperators

def head {d : ℕ} (ord : Fin d → ℕ) : ℝ :=
  ∏ i, ((2:ℝ)^(ord i)*(32^(ord i)*((ord i).factorial:ℝ)^2))*(1+2*Real.pi)^(ord i)

theorem nonnegative {d : ℕ} (order : Fin d → ℕ) : 0 ≤ head order := by
  unfold head
  exact prod_nonneg fun i _ => by positivity

def budget (d k : ℕ) : ℝ := ∑ β : Fin d → Fin (k+1), head (fun i => (β i).val)

theorem original {d : ℕ} (l h : Fin d → ℝ) (v : Fin d → ℤ) (k : ℕ) :
    0 ≤ budget d k ∧
    (∀ i, ContDiff ℝ ∞ (window (l i) (h i)*wave (frequency (v i)))) ∧
    (∀ i t, t ∉ Icc (l i) (h i) → (window (l i) (h i)*wave (frequency (v i))) t = 0) ∧
    ∀ ord : Fin d → ℕ, (∀ i, ord i ≤ k) → ∀ x : Fin d → ℝ,
      ‖∏ i, iteratedDeriv (ord i) (window (l i) (h i)*wave (frequency (v i))) (x i)‖ ≤
        budget d k*(1+(height v:ℝ))^(d*k) := by
  refine ⟨sum_nonneg (fun _ _ => nonnegative _),?_,?_,?_⟩
  · intro i
    have cast : ContDiff ℝ ∞ (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
    exact (WilsonOriginalFiledBoxWindow.smooth ..).mul (contDiff_const.mul cast).cexp
  · intro i t ht
    rcases not_and_or.mp ht with low|high
    · simp [window,WilsonOriginalGevreyCutoffDisc.leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp low).le)]
    · simp [window,WilsonOriginalGevreyCutoffDisc.leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (not_le.mp high).le)]
  · intro ord hok x
    let β : Fin d → Fin (k+1) := fun i => ⟨ord i,Nat.lt_succ_of_le (hok i)⟩
    have payment : head ord ≤ budget d k :=
      single_le_sum (fun b _ => nonnegative (fun i => (b i : Fin (k+1)).val)) (mem_univ β)
    have orders : ∑ i, ord i ≤ d*k := by
      simpa using (sum_le_sum (s:=univ) (f:=ord) (g:=fun _ => k) (fun i _ => hok i))
    apply (WilsonOriginalFiledBoxWindow.original l h x v ord).trans
    exact mul_le_mul payment (pow_le_pow_right₀ (by linarith [show (0:ℝ) ≤ (height v : ℝ) by positivity]) orders) (by positivity) (nonnegative _ |>.trans payment)

end YM.Integration.WilsonOriginalUniformBoxProfiles
