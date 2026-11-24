import YM.Contacts.Power.Shorter
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Lagrange
/-!
# Tensor-ready Taylor error accounting

One-sided arbitrary radius. Jet may take values in any real normed vector space; later for valuation choose higher derivatives to pay a margin even off coordinate seams. We operate only at one stage at a time and can vary every spacing and field budget with i; no uniform high-order in shrinking exponents here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Mat
open Function Filter Metric Set Power
open scoped Topology BigOperators ContDiff
variable {α E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
variable {n:ℕ} {x y t:ℝ}

def unitMonomial (j:ℕ)(t:ℝ):ℝ:= (j.factorial:ℝ)⁻¹*t^j
@[simp] lemma unitMonomial_zero (t:ℝ): unitMonomial 0 t = 1:=by simp [unitMonomial]
lemma derivative (t y:ℝ)(j:ℕ): HasDerivAt (fun x=> unitMonomial (j+1) (t-x)) (-unitMonomial j (t-y)) y:=by
    have hx:HasDerivAt (fun x:ℝ=> t-x) (-1) y := (hasDerivAt_id' y).const_sub t
    unfold unitMonomial
    convert ((hx.pow (j+1)).const_mul ((↑(j+1).factorial : ℝ)⁻¹)) using 1 <;> try rfl
    rw [Nat.factorial_succ]; simp only [Nat.add_sub_cancel]; push_cast; field_simp

variable (f:ℕ→ℝ→ E)
def series (n:ℕ)(u x:ℝ):E:= ∑ i∈ Finset.range (n+1), unitMonomial i (x-u) • f i u
lemma series_step (n:ℕ)(u x:ℝ): series f (n+1) u x=series f n u x+unitMonomial (n+1) (x-u) • f (n+1) u:= by unfold series;rw [Finset.sum_range_succ]
@[simp] lemma series_start (u x:ℝ):series f 0 u x = f 0 u:=by simp [series]
@[simp] lemma series_center (u:ℝ) (n:ℕ):series f n u u= f 0 u:=by induction n with
   | zero=> simp
   | succ n ih=>simp [series_step,ih,unitMonomial]
lemma series_deriv (t:ℝ) (h:∀ i≤n,HasDerivAt (f i) (f (i+1) y) y):
    HasDerivAt (fun x=>series f n x t) (unitMonomial n (t-y) • f (n+1) y) y:=by
  induction n with
  | zero=>simpa using! h 0 (le_refl _)
  | succ n ih=>
    simp_rw [series_step]
    let X:= ih (fun i hi=> h i (hi.trans n.le_succ)); convert X.add ((derivative t y n).smul (h (n+1) le_rfl)) using 1 <;> try rfl
    rw [neg_smul];abel

lemma approx (b A:ℝ)(h:∀ x∈Icc 0 b,∀ j≤ n,HasDerivAt (f j) (f (j+1) x) x)(hp:0 ≤ A)(he:∀ x∈Icc 0 b,‖f (n+1) x‖ ≤ A)(hx:x∈Icc 0 b): ‖f 0 x-series f n 0 x‖ ≤ A*(b^(n+1) / n.factorial):=by
  have hh: Icc 0 x⊆ Icc 0 b:= Icc_subset_Icc_right hx.2
  let f' t:= unitMonomial n (x-t) • f (n+1) t; let a:= ((↑(n.factorial):ℝ)⁻¹ * x^n)
  have ht t (ht:t∈Ico 0 x): ‖f' t‖ ≤ (a*A):= by
       have ht':=Ico_subset_Icc_self ht; unfold f' unitMonomial; rw [norm_smul, norm_mul,Real.norm_of_nonneg (by positivity :0≤(↑n.factorial:ℝ)⁻¹),Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr ht'.2) _)]
       exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr ht'.2) (sub_le_self _ ht'.1) n) (by positivity)) (he _ (hh ht')) (norm_nonneg _) (mul_nonneg (by positivity) (pow_nonneg hx.1 _))
  apply le_trans ((by simpa only [series_center,sub_zero] using norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht=> (series_deriv f x (h t (hh ht)) |>.hasDerivWithinAt)) ht x (right_mem_Icc.mpr hx.1)) : _ ≤ a*A*x)
  apply le_trans (Eq.le (?_: a*A*x=A*(x^(n+1)/n.factorial))) (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (pow_le_pow_left₀ hx.1 hx.2 _) (by positivity)) hp)
  unfold a; ring

variable {P:Pace α}{g:α→ℕ→ℝ→ E}{a b:ℝ}
lemma cost (hb:0≤b)(h:∀ᶠ i in P.net, ∀ t∈Icc 0 b, ∀ j≤n, HasDerivAt (g i j) (g i (j+1) t) t)
    (he:∀ x:α→ℝ,(∀ᶠ i in P.net,x i∈ Icc 0 b)→ P.Priced a (fun i=>g i (n+1) (x i))) (x:α→ℝ)(hx: ∀ᶠ i in P.net,x i∈ Icc 0 b):
    P.Priced a (fun i=> g i 0 (x i)-series (g i) n 0 (x i)):=by
    let t:=Icc (0:ℝ) b; apply Pace.Priced.exacts; intro r hr
    let χ:ℝ:= b^(n+1)/n.factorial; let p:= P.rate r; have hu : ∀ᶠ i in P.net, ∀ y∈ t, ‖g i (n+1) y‖ ≤ p i:= Pace.Priced.holdsFor _ _ (Eventually.of_forall fun i=> ⟨0,left_mem_Icc.mpr hb⟩) he _ hr
    exact (((P.rate_grade r).priced.mul (Pace.Priced.constants χ)).capped_by (((h.and hx).and hu).mono fun i H=> approx _ b (p i) H.1.1 (P.rate_pos .. |>.le) H.2 H.1.2)).shift (by simp)
end YM.Contacts.Mat
