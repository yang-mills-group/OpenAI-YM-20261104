import YM.Integration.WilsonIndependentCapturedFiledDirections
import YM.Integration.WilsonMarkedHeldPolarization

/-! Convert the paid angular coefficient masses of a thermal grade into the
whole mixed differential on the actual thermal and link variables. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonEmittedAngularJointFare
open Function Filter Finset Tensor
open scoped Topology BigOperators Classical
variable {I E : Type} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

def mass (b : (r:ℕ) → (Fin r→I) → ℂ) (d : ℕ) := ∑ r ∈ range (d+1), ∑ x, ‖b r x‖
def held (b : (r:ℕ) → (Fin r→I) → ℂ) (p : E → I → ℂ) (d : ℕ) (y : E) :=
  ∑ r ∈ range (d+1), ∑ x, b r x * ∏ j,p y (x j)

omit [NormedSpace ℝ E] in
private theorem fixed (b : (r:ℕ) → (Fin r→I) → ℂ) (p : E → I → ℂ)
    (h : ∀ y a, ‖p y a‖ ≤ ‖y‖) (d : ℕ) (y : E) :
    ‖held b p d y‖ ≤ mass b d*(1+‖y‖)^d := by
  have base : 1 ≤ 1+‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  unfold held mass
  rw [sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro r hr
  rw [sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro x _
  rw [norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∏ _j:Fin r, (1+‖y‖) := prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>(h _ _).trans (by linarith))
    _ = (1+‖y‖)^r := by simp
    _ ≤ _ := pow_le_pow_right₀ base (Nat.le_of_lt_succ (mem_range.mp hr))

theorem mixed {d : ℕ} (T : Tensor.T (ℝ×E) ℂ d) (sym : Tensor.Sym T)
    (b : (r:ℕ) → (Fin r→I) → ℂ) (p : E → I → ℂ) (h : ∀ y a, ‖p y a‖ ≤ ‖y‖)
    (registered : ∀ y, diagonal T (1,y)=held b p d y) :
    ‖T‖ ≤ Planned.AtomRegular.polarCost d * (mass b d * 2^d) := by
  have budget : 0 ≤ mass b d := by unfold mass; positivity
  have dilate (t:ℝ) (z:E) (nz:t≠0) : ‖diagonal T (t,z)‖ ≤ mass b d*(|t|+‖z‖)^d := by
    have replace : t • ((1:ℝ),t⁻¹ • z)=(t,z) := by simp [Prod.smul_mk,smul_smul,nz]
    have scale : |t| *(1+‖t⁻¹ • z‖)=|t|+‖z‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,mul_add,mul_one,←mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr nz),one_mul]
    calc
      _ = |t|^d * ‖held b p d (t⁻¹ • z)‖ := by
        rw [←replace,homogeneous,registered,norm_smul,Real.norm_eq_abs,abs_pow]
      _ ≤ |t|^d * (mass b d * (1+‖t⁻¹ • z‖)^d) :=
        mul_le_mul_of_nonneg_left (fixed b p h d _) (by positivity)
      _ = _ := by rw [←scale,mul_pow]; ring
  have atZero (z:E) : ‖diagonal T (0,z)‖ ≤ mass b d*(|(0:ℝ)|+‖z‖)^d := by
    have lhs : Continuous (fun s:ℝ=>‖diagonal T (s,z)‖) :=
      (T.cont.comp (continuous_pi fun _=>continuous_id.prodMk continuous_const)).norm
    have rhs : Continuous (fun s:ℝ=>mass b d*(|s|+‖z‖)^d) := by fun_prop
    apply le_of_tendsto_of_tendsto (b:=𝓝[>] (0:ℝ)) ((lhs.tendsto 0).mono_left nhdsWithin_le_nhds)
      ((rhs.tendsto 0).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact dilate s z (ne_of_gt hs)
  apply Planned.AtomRegular.op_polar sym (mul_nonneg budget (by positivity))
  rintro ⟨t,z⟩ small
  have a : |t| ≤ 1 := (le_max_left ‖t‖ ‖z‖).trans small
  have v : ‖z‖ ≤ 1 := (le_max_right ‖t‖ ‖z‖).trans small
  have witness : ‖diagonal T (t,z)‖ ≤ mass b d*(|t|+‖z‖)^d := by
    rcases eq_or_ne t 0 with eq|nz
    · subst t; exact atZero _
    · exact dilate t z nz
  exact witness.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) budget)

theorem germ {d:ℕ} (F:ℝ×E→ℂ) (smooth:ContDiffAt ℝ d F 0)
    (b : (r:ℕ) → (Fin r→I) → ℂ) (p : E → I → ℂ) (h : ∀ y a, ‖p y a‖ ≤ ‖y‖)
    (registered : ∀ y, diagonal (Tensor.coeff F d 0) (1,y)=held b p d y) :
    ‖iteratedFDeriv ℝ d F 0‖ ≤ (d.factorial:ℝ)*Planned.AtomRegular.polarCost d*(mass b d*2^d) := by
  have result := mixed (Tensor.coeff F d 0) (Tensor.coeff_symm smooth) b p h registered
  have recover : (d.factorial:ℝ) • Tensor.coeff F d 0=iteratedFDeriv ℝ d F 0 := by
    simp [Tensor.coeff,smul_smul,Nat.factorial_ne_zero]
  rw [←recover,norm_smul,Real.norm_natCast,mul_assoc]
  exact mul_le_mul_of_nonneg_left result (Nat.cast_nonneg _)
end YM.Integration.WilsonEmittedAngularJointFare
