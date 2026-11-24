import YM.RG01.Kernel.Play

/-! Derivatives of the true conditional generating function are charged to
the integral of the absolute marked source against the very same law.
A finite global bound only witnesses analyticity and integrability. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalMomentBrush
open Function Filter MeasureTheory Complex Finset RG01.Kernel RG01.Kernel.Wheel
open ConnectedActivityE6.Blaze
open scoped Topology ContDiff BigOperators Classical

variable {κ Ω : Type} [Fintype κ] [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {Z : κ → Ω → E →L[ℂ] ℂ} {K b : ℝ} {w : κ → Ω → ℝ} {F : κ → Ω → ℂ}

def absolute (w : κ → Ω → ℝ) (μ : Measure Ω) (F : κ → Ω → ℂ) : ℝ :=
  ∑i,∫ x,w i x*‖F i x‖ ∂μ

theorem nonnegative (H : Caliber w μ) : 0 ≤ absolute w μ F :=
  Finset.sum_nonneg fun i _=>integral_nonneg fun x=>mul_nonneg (H.pos i x) (norm_nonneg _)

theorem integrable (H : Caliber w μ) (a : Bounded μ F b) (i : κ) :
    Integrable (fun x=>w i x*‖F i x‖) μ := by
  refine (H.funds a i).norm.congr (ae_of_all _ fun x=>?_ )
  change ‖(w i x:ℂ)*F i x‖ = w i x*‖F i x‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (H.pos i x)]

theorem raw (H : Caliber w μ) (L : Wheel μ Z K) (a : Bounded μ F b) (hb : 0 ≤ b) (k : ℕ) :
    Brush k (absolute w μ F) K (generating w Z μ F) 0 := by
  have fee := nonnegative (F:=F) H
  refine ⟨(L.rawBrush H a hb k).smooth,L.sign,fun j _=>ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg fee (pow_nonneg L.sign _)) fun x=>?_⟩
  rw [L.real_derivative H a hb ..]
  let v := K^j * ∏ d,‖x d‖
  have charge (i : κ) (p : Ω) :
      ‖(w i p:ℂ)*carrier Z F x i p‖ ≤ w i p*‖F i p‖*v := by
    have hv : ∏ d,‖Z i p (x d)‖ ≤ v := by
      calc
        _ ≤ ∏d,K*‖x d‖ := Finset.prod_le_prod (fun d _=>norm_nonneg _) (fun d _=>
          ((Z i p).le_opNorm (x d)).trans (mul_le_mul_of_nonneg_right (L.uniform i p) (norm_nonneg _)))
        _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,v]
    unfold carrier
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (H.pos i p),norm_mul,norm_prod,←mul_assoc]
    exact mul_le_mul_of_nonneg_left hv (mul_nonneg (H.pos _ _) (norm_nonneg _))
  unfold moment
  calc
    _ ≤ ∑i,∫ p,‖(w i p:ℂ)*carrier Z F x i p‖ ∂μ :=
      (norm_sum_le ..).trans (Finset.sum_le_sum fun _ _=>norm_integral_le_integral_norm _)
    _ ≤ ∑i,∫ p,(w i p*‖F i p‖)*v ∂μ := Finset.sum_le_sum fun i _=>
      integral_mono ((H.funds (L.pay_norm a x hb) i).norm) ((integrable H a i).mul_const v) (charge i)
    _ = (∑i,∫ p,w i p*‖F i p‖ ∂μ)*v := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _=>integral_mul_const v _
    _ = _ := by unfold absolute v;ring

theorem normalized (H : Caliber w μ) (L : Wheel μ Z K) (a : Bounded μ F b) (hb : 0 ≤ b) (k : ℕ) :
    Brush k (invoice k (absolute w μ F)) (K+2*K) (quota w Z μ F) 0 := by
  let f := generating w Z μ (1 : κ→Ω→ℂ)
  have unit : Bounded μ (1:κ→Ω→ℂ) 1 := ⟨fun _=>aestronglyMeasurable_const,fun _ _=>le_of_eq norm_one⟩
  have den := L.rawBrush H unit zero_le_one k
  have inv : Brush k (inverse_cost k).choose 1 (Inv.inv : ℂ→ℂ) (f 0) := by
    unfold f
    rw [Wheel.base H]
    exact (inverse_cost k).choose_spec.2
  have joint := (raw H L a hb k).paints (den.pine inv)
  have eq : quota w Z μ F = fun x=>generating w Z μ F x*(f x)⁻¹ := by
    funext x
    rw [quota,Pi.div_apply,div_eq_mul_inv]
  rw [eq]
  simpa only [one_add_one_eq_two] using! joint

end YM.Integration.WilsonConditionalMomentBrush
end
