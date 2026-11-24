import YM.MS.FlatJet
import YM.Space.Index
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Momentum and lattice gradient, in midpoint convention

Coordinate convention matches `YM.Axis`. More axes are admitted for dimensions and for
finite ambient D-index calculations. For products use sup norm; in symbols `q⋅q`, not that norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Filter Real
open scoped Topology ContDiff
abbrev Momentum (A : Type*) := A → ℝ
variable {A ι : Type*} [Fintype A]
namespace Momentum
def pairing (p q : Momentum A) := ∑ i, p i * q i
def sq (p : Momentum A) : ℝ := ∑ i, p i ^ 2
lemma sq_eq (p : Momentum A) : sq p = pairing p p := by simp only [sq,pairing,pow_two]
lemma sq_nonnegative (p : Momentum A) : 0 ≤ sq p:= Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma sqrt_le' (p : Momentum A) : ‖p‖ ≤ √(sq p) := by
   rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
   intro i; rw [Real.le_sqrt (norm_nonneg _) (sq_nonnegative p), Real.norm_eq_abs, sq_abs]; exact Finset.single_le_sum (fun j _=> sq_nonneg _) (Finset.mem_univ i)
lemma sup_square (p : Momentum A) : ‖p‖ ^ 2 ≤ sq p := (Real.le_sqrt (norm_nonneg _) (sq_nonnegative p)).mp (sqrt_le' p)
lemma scaling (p : Momentum A) (r:ℝ) : sq (r • p)= r^2*sq p:= by simp only [sq,Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
-- θ is smoothly periodic with shifted convention up to the known phases.
def theta (x : ℝ) := 2*sin (2⁻¹*x)
def wave (p : Momentum A) : Momentum A := theta ∘ p
lemma theta_small (x : ℝ) : |theta x| ≤ |x| := calc
    _ = 2*|sin (2⁻¹*x)| := by rw [theta, abs_mul, abs_two]
    _ ≤ 2* |2⁻¹*x| := mul_le_mul_of_nonneg_left abs_sin_le_abs (by norm_num : (0:ℝ)≤2)
    _ = _ := by rw [abs_mul]; norm_num; ring
lemma theta_large (x : ℝ) (hx : |x| ≤ π) : (1/2:ℝ)*|x| ≤ |theta x| := by
   have hv := pi_pos
   have hb : |(2⁻¹:ℝ)*x|= 2⁻¹*|x| := by rw [abs_mul,abs_of_nonneg (by positivity)]
   have hl : 2⁻¹*|x| ≤ π/2 := by linarith
   rw [theta,abs_mul, abs_two, Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [hb]; linarith),hb]; apply le_trans ?_ (mul_le_mul_of_nonneg_left (Real.mul_le_sin (by positivity) hl) (by norm_num : (0:ℝ) ≤ 2))
   have he: (1/2:ℝ) ≤ 2/π:= by rw [le_div_iff₀ hv]; linarith [Real.pi_le_four]
   calc
    _ ≤ 2/π* |x| := by gcongr
    _ = _ := by ring
lemma wave_small (p : Momentum A) : ‖wave p‖ ≤ ‖p‖ := by
   rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
   exact fun i => le_trans (theta_small (p i)) (norm_le_pi_norm p i)
lemma wave_large (p : Momentum A) (hx : ‖p‖ ≤ π) : ‖p‖ ≤ 2*‖wave p‖ := by
   apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i
   have h:=theta_large (p i) (le_trans (norm_le_pi_norm p i) hx); have he: |theta (p i)| ≤ ‖wave p‖ := norm_le_pi_norm (wave p) i; rw [Real.norm_eq_abs]; linarith

lemma theta_tame : theta.HasTemperateGrowth := by
   have hs : sin.HasTemperateGrowth := by
      refine ⟨contDiff_sin, fun n=> ⟨0,1, fun x=>?_⟩⟩; simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using (Real.abs_iteratedDeriv_sin_le_one n x)
   unfold theta; fun_prop
lemma defect {S : Scale ι} (ht : ∀ i, 1≤ S.length i) (a : A) :
    Bound S (fun _ p => wave p a-p a) (fun i=> (S.length i^3)⁻¹) := by
   let f := fun x : ℝ => theta x-x
   refine Bound.linear (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : A=> ℝ) a)
     (Scale.flat_right (f:=f) ht 3 (theta_tame.sub (Function.HasTemperateGrowth.id')) (fun k hk=> ?_))
   apply norm_eq_zero.mp; rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
   have he : deriv f = fun x=> cos (2⁻¹*x) -1 := by
      ext x; apply HasDerivAt.deriv
      convert! (((((hasDerivAt_id' x).const_mul (2:ℝ)⁻¹).sin).const_mul 2).sub (hasDerivAt_id' x)) using 1; ring
   interval_cases k
   · simp [f,theta]
   · simp [he]
   simp_rw [show (2:ℕ)=1+1 by decide, iteratedDeriv_succ',he]; have hz := (((hasDerivAt_id' (0:ℝ)).const_mul (2:ℝ)⁻¹).cos).sub_const (1:ℝ); simpa only [iteratedDeriv_zero,mul_zero, sin_zero, neg_zero, zero_mul, norm_zero] using congr_arg norm hz.deriv
end Momentum
end YM.MS
