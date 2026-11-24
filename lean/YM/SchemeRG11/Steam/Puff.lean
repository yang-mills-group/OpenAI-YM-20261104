import YM.SchemeRG11.Cluster.Purse
import YM.Maxwell.PotentialKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
/-!
Heat kernels in the FOUR-dimensional finite parts. Applied AFTER subtraction.
Stay away from other singular supports. Exact d4 Gaussian verification.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set Metric Function Filter MeasureTheory Cluster MSbar
open scoped ContDiff Topology Real BigOperators RealInnerProductSpace

lemma factor_zero (μ : ℝ) : Pole.factor μ 0= ((4 * Real.pi:ℝ)^2)⁻¹ := by
  unfold Pole.factor Pole.dimension
  norm_num
  have hp : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'; field_simp; ring

def base := ((4*Real.pi)^2)⁻¹
def α (t : ℝ) := (4*t)⁻¹
def gauze (t : ℝ) (x : E4) := base*(t^2)⁻¹ * Real.exp (-α t*‖x‖^2)
lemma prefer (μ : ℝ) (t : ℝ) (x : E4) : (gauze t x:ℂ)=fog μ t 0 x := by
  rw [fog,gauze,factor_zero]; simp only [base,α,zero_sub,Complex.cpow_neg,Complex.cpow_ofNat]
  rw [show -((4*t)⁻¹)*‖x‖^2 = -t⁻¹*(‖x‖^2/4) by ring]; push_cast; ring

lemma gauze_diff (t : ℝ) : ContDiff ℝ ∞ (gauze t) := contDiff_const.mul (ContDiff.exp (contDiff_const.mul (contDiff_norm_sq ℝ)))

lemma series_calm {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f:X→Y} (h : ContDiff ℝ ∞ f) (l : List X) : ContDiff ℝ ∞ (series f l) := by
  induction l with
  | nil => exact h
  | cons v l ih => exact ((ih.fderiv_right (by simp)).clm_apply contDiff_const)

lemma series_c {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X→ℝ} (h : ContDiff ℝ ∞ f) (l : List X) : series (Complex.ofRealCLM ∘ f) l= Complex.ofRealCLM ∘ series f l := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    simp only [series,ih,show ∀ p, fderiv ℝ (Complex.ofRealCLM ∘ series f l) p=Complex.ofRealCLM.comp (fderiv ℝ (series f l) p) from fun p=> by rw [fderiv_comp p Complex.ofRealCLM.differentiableAt ((series_calm h l).differentiable (by simp) p),Complex.ofRealCLM.fderiv]]; rfl

def tint (l : List Axis) (t : ℝ) : E4→ℝ := series (gauze t) (l.map basis)
lemma melt (μ : ℝ) (l : List Axis) (t : ℝ) (x : E4) : (tint l t x:ℂ)=plume μ l t 0 x := by
  rw [plume,show fog μ t 0 (n:=4)=Complex.ofRealCLM ∘ gauze t from funext fun _=> Eq.symm (prefer ..),series_c (gauze_diff t)]; rfl

lemma first_line (a : Axis) (t : ℝ) : tint [a] t = fun x=> (-2*α t)*(x a)*gauze t x := by
  funext x
  change fderiv ℝ (gauze t) x (basis a)=_
  have hd:= ((((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-α t)).exp).const_mul (base*(t^2)⁻¹)).fderiv
  unfold gauze; rw [hd]
  simp [two_smul,← real_inner_comm x,basis_inner]; ring
lemma second_line (a b : Axis) (t : ℝ) :
    tint [a,b] t = fun x=> ((-2 * α t)*(basis a b)+(2*α t)^2*(x a*x b))*gauze t x := by
  funext x
  have hd:= ((compAxis b).hasFDerivAt.const_mul (-2*α t)).mul ((gauze_diff t).differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ (tint [b] t) x (basis a) = _
  rw [first_line]; rw [show (fun x:E4=> -2*α t * x b * gauze t x)=(fun x=> -2*α t*(compAxis b) x)*(gauze t) from rfl,hd.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]; change _*tint [a] t x + _=_
  rw [first_line]; unfold compAxis; dsimp; ring
lemma stave (x : E4) {t : ℝ} (ht : 0 < t) : HasDerivAt (fun t=> gauze t x) (∑ a,tint [a,a] t x) t := by
  let F := fun u:ℝ=> base*u⁻¹^2
  have he t : gauze t x= F t * Real.exp (- (4:ℝ)⁻¹ * t⁻¹ * ‖x‖^2) := by unfold gauze F α; rw [mul_inv_rev,inv_pow]; congr 2; ring
  simp_rw [he]
  have hu := ((hasDerivAt_inv ht.ne').pow 2).const_mul base
  let f := fun t:ℝ=> Real.exp (- (4:ℝ)⁻¹ * t⁻¹ * ‖x‖^2)
  have hd := ((((hasDerivAt_inv ht.ne').const_mul (- (4:ℝ)⁻¹)).mul_const (‖x‖^2)).exp)
  convert! hu.mul hd using 1
  simp only [second_line, basis_eq, ← sq, add_mul, Finset.sum_add_distrib,← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← EuclideanSpace.real_norm_sq_eq]
  simp only [Axis, Fintype.card_fin, he, Pi.pow_apply, F,α,mul_inv_rev]; push_cast; ring
end YM.SchemeRG11.Steam
