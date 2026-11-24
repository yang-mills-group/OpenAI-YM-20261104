import YM.SchemeRG11.Steam.Puff
import YM.SchemeRG11.Probe.Displacement
/-!
Bounds for the integral over vertex point at fixed positive times.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set Metric MeasureTheory Filter Function Cluster MSbar
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
open ConeProbe

lemma curly (t : ℝ) (l : List Axis) : ∃ p : ConeProbe.Pol, ∀ x : E4, (tint l t x:ℂ)= (gauze t x:ℂ)*scored p x := by
  induction l with
  | nil => refine ⟨1,fun x=> by rw [scored_one]; simp [tint,series]⟩
  | cons v l ih =>
    obtain ⟨p,hp⟩:=ih
    let H := fun x : E4=> (tint l t x:ℂ)
    let G := fun x : E4=> (gauze t x:ℂ)
    have h : H=G*scored p := funext hp
    refine ⟨MvPolynomial.pderiv v p+MvPolynomial.C (↑(-2*α t):ℂ)*MvPolynomial.X v*p,fun x=> ?_⟩
    have hg : (fderiv ℝ G x) (basis v)=(↑((-2*α t)*(x v)*gauze t x):ℂ) := by
      rw [← show tint [v] t x = -2*α t*x v*gauze t x from congr_fun (first_line v t) x]; exact reflect_real _ x ((gauze_diff t).differentiable (by simp) x) _
    change (↑(Analysis.D (basis v) (tint l t) x):ℂ)= _
    have hh := reflect_real (tint l t) x ((series_calm (gauze_diff t) _).differentiable (by simp) x) v
    have hk : (fderiv ℝ H x) (basis v)= (↑(Analysis.D (basis v) (tint l t) x):ℂ):= hh
    rw [← hk,h, fderiv_mul (show DifferentiableAt ℝ G x from Complex.ofRealCLM.differentiableAt.comp _ ((gauze_diff t).differentiable (by simp) x)) (scored_diff p x)]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,hg,show fderiv ℝ (scored p) x (basis v)= _ from grad_score p v x,scored_add,scored_mul,scored_X,scored_C,Pi.add_apply,Pi.mul_apply]; unfold G cast4; push_cast; ring

lemma enroll (p : ConeProbe.Pol) : ∃ C>0, ∃ k : ℕ, ∀ x : E4, ‖scored p x‖ ≤ C*(1+‖x‖)^k := by
  induction p using MvPolynomial.induction_on with
  | C u => exact ⟨1+‖u‖,by positivity,0,fun x=>by simp only [scored_C,pow_zero,mul_one]; linarith⟩
  | mul_X p i hp =>
    obtain ⟨C,hC,k,h⟩:=hp
    refine ⟨C,hC,k+1,fun x=>?_⟩
    rw [scored_mul,scored_X,Pi.mul_apply,norm_mul]; unfold cast4; rw [Complex.norm_real]
    have hx : ‖x i‖ ≤ ‖x‖ := by rw [Real.norm_eq_abs, ← basis_inner]; grw [abs_real_inner_le_norm]; simp
    rw [pow_succ,←mul_assoc]; exact mul_le_mul (h _) (by linarith) (norm_nonneg _) (by positivity)
  | add p q hp hq =>
    obtain ⟨C,hC,k,h⟩:=hp; obtain ⟨D,hD,n,h'⟩:=hq
    refine ⟨C+D,by positivity,max k n,fun x=>?_⟩
    rw [scored_add, Pi.add_apply]; apply (norm_add_le ..).trans
    grw [h x,h' x]; rw [add_mul]; gcongr <;> first | exact le_max_left .. | exact le_max_right .. | linarith [norm_nonneg x]
lemma breath {t : ℝ} (ht : 0<t) (k : ℕ) : ∃ C>0, ∀ x:E4, ‖gauze t x‖ * (1+‖x‖)^k ≤ C := by
  let b:= base*(t^2)⁻¹
  have hα : 0<α t := by unfold α; positivity
  obtain ⟨C,hC,e⟩:=Hot.rain hα k
  have hp (x : E4) : Real.exp (-α t*‖x‖^2) ≤ 1:= Real.exp_le_one_iff.mpr (by rw [neg_mul]; exact neg_nonpos.mpr (by positivity))
  have hb : 0<b:=by unfold b base; positivity
  refine ⟨b*(2^k)*(1+C),by positivity,fun x=>?_⟩
  unfold gauze; change ‖b*Real.exp _‖ * _ ≤ _; rw [Real.norm_of_nonneg (by positivity : 0≤b*Real.exp _)]
  rcases le_total ‖x‖ 1 with H|H
  · grw [hp x,H]; simp only [one_add_one_eq_two,mul_one]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  grw [show 1+‖x‖ ≤ 2*‖x‖ by linarith,
       show -α t*‖x‖^2 ≤ -α t*‖x‖ from mul_le_mul_of_nonpos_left (by nlinarith) (by linarith)]
  calc _ = b*2^k*(‖x‖^k*Real.exp (-α t*‖x‖)) := by rw [mul_pow]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left ((e _ (norm_nonneg _)).trans (by linarith)) (by positivity)
lemma skim (l : List Axis) {t : ℝ} (ht: 0<t) (n : ℕ) : ∃ C>0, ∀ x : E4, ‖tint l t x‖ ≤ C/(1+‖x‖)^n := by
  obtain ⟨p,hp⟩:=curly t l
  obtain ⟨C,hC,k,h⟩:=enroll p
  obtain ⟨D,hD,e⟩:=breath ht (k+n)
  refine ⟨C*D,by positivity,fun x=> (le_div_iff₀ (by positivity)).mpr ?_⟩
  rw [← Complex.norm_real,hp,norm_mul,Complex.norm_real]; grw [h x]
  refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left (e x) hC.le); rw [pow_add]; ring

lemma sheer (l : List Axis) {t : ℝ} (ht : 0<t) (n : ℕ) (R : ℝ) : ∃ C>0, ∀ x y : E4, ‖x‖ ≤ R → ‖tint l t (x-y)‖ ≤ C/(1+‖y‖)^n := by
  obtain ⟨C,hC,h⟩:=skim l ht n
  refine ⟨C*(1+|R|)^n,by positivity,fun x y he=>?_⟩
  have hh:= norm_sub_norm_le x y
  have hk : 1+‖y‖ ≤ (1+|R|)*(1+‖x-y‖):= by nlinarith [norm_sub_norm_le y x,norm_sub_rev x y,abs_nonneg R,le_abs_self R,norm_nonneg (x-y)]
  refine (h _).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  grw [hk]; rw [mul_pow, mul_assoc]
end YM.SchemeRG11.Steam
