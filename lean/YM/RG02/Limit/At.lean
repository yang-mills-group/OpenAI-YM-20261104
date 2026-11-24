import YM.PertExtension.Aspiration

/-!
Utilities for the actual finite-volume pointwise Laplace tests.
These cells give order-by-order pointwise precision; not a growth
estimate as the order, stencil or volume goes up. Not the uniform masked
analytic estimates. Work on t>0 only; need no analytic tuning in t on the
physical cutoff path. Scalars may represent separately subtracted costs,
and need bounds elsewhere.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG02.Asym
open PertExtension.Series.Tested PertExtension.Series Filter Finset Topology PowerSeries
open scoped BigOperators Classical

section plain
variable {E F : Type*}[NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
lemma bill_at {x y : ℝ→E}{n}(h : Bill n x)(hx : x =ᶠ[Tested.germ] y) : Bill n y := by
   obtain ⟨C,hC,H⟩ := h; refine ⟨C,hC,?_⟩
   filter_upwards [H,hx] with i hi he; rwa [← he]

lemma agreement {x y : ℝ→E}{f : ℕ→ E}(h : Aspiration x f)(he : x =ᶠ[Tested.germ] y) : Aspiration y f := fun n =>
    bill_at (h n) (he.sub (Filter.EventuallyEq.refl ..))

lemma transport {x : ℝ→E}{a : ℕ→E}(h : Aspiration x a)(L : E →L[ℝ] F) :
    Aspiration (L ∘ x) (L ∘ a) := by
  intro n
  obtain ⟨C,hC,H⟩ := h n
  refine ⟨‖L‖*C,mul_nonneg (norm_nonneg _) hC,H.mono fun i hi => ?_⟩
  have he : (L ∘ x-peval (L ∘ a) n) i=L ((x-peval a n) i) := by
    simp [peval,Zone.eval, map_sum]
  rw [he]; exact ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))).trans_eq (mul_assoc ..).symm

lemma convert_x {x : ℝ→ℝ}{g : ℕ → ℝ}(h : Aspiration x g) : Aspiration (Complex.ofReal ∘ x) (Complex.ofReal ∘ g) := transport h Complex.ofRealCLM

lemma scalar_mul_lift {x : ℝ→ℂ}{g : ℕ→ℂ}(h : Aspiration x g)(c : ℂ) :
    Aspiration (c • x) (c • g) := transport h (c • ContinuousLinearMap.id ℝ ℂ)

end plain

section field
variable {K : Type*}[NormedField K][NormedAlgebra ℝ K]{x y : ℝ→K} {f g : PowerSeries K}

-- One variable only; marker algebra gets the graded API below.
abbrev Near (x : ℝ→K)(f : PowerSeries K) := Aspiration x (fun i => coeff i f)

namespace Near
lemma from_map (h : ∀ i, ∀ᶠ t in Tested.germ, ‖x t-y t‖ ≤ t^i)(H : Near x f) : Near y f := by
  -- very strong pointwise tail; use `mapped` with cost when no infinite remainder known.
  intro n; obtain ⟨C,hC,H⟩:= H n; refine ⟨1+C,by positivity,?_⟩
  filter_upwards [h (n+1),H] with t ht Ht
  dsimp only [Pi.sub_apply] at *
  rw [show y t-_=(y t-x t)+(x t-_) by exact (sub_add_sub_cancel ..).symm, add_mul,one_mul]
  exact (norm_add_le ..).trans (add_le_add ((norm_sub_rev ..).le.trans ht) Ht)

lemma same (h : Near x f)(H : x =ᶠ[Tested.germ] y) : Near y f := agreement h H
lemma unique' (h : Near x f)(H : Near x g) : f=g := PowerSeries.ext (congr_fun (Aspiration.unique h H))
lemma mult (h : Near x f)(H : Near y g) : Near (x*y) (f*g) := by
  have hf : PowerSeries.mk (fun i => coeff i f)=f := PowerSeries.ext (fun i => PowerSeries.coeff_mk ..)
  have hg : PowerSeries.mk (fun i => coeff i g)=g := PowerSeries.ext (fun i => PowerSeries.coeff_mk ..)
  have hh := Aspiration.prod h H
  rw [conv,hf,hg] at hh
  exact hh
lemma incline (h : Near x f)(H : Near y g) : Near (x+y) (f+g) := by
  have hh := Aspiration.add h H; unfold Near; simp_rw [map_add]; exact hh
lemma fine_inverse (h : Near x f)(hr : coeff 0 f ≠ 0) : Near x⁻¹ f⁻¹ := by
  have hi := Aspiration.inverse h hr
  rw [reciprocal,show PowerSeries.mk (fun i => coeff i f)=f from PowerSeries.ext (fun i => PowerSeries.coeff_mk ..)] at hi; exact hi
lemma mono (c : K)(k : ℕ) : Near (fun t=>t^k • c) (PowerSeries.monomial k c) := by
  unfold Near; simp_rw [PowerSeries.coeff_monomial]; exact Aspiration.single c k
lemma fixed (c : K) : Near (fun _=>c) (PowerSeries.C c) := by
   convert mono c 0 using 1
   · funext t; simp
   exact (PowerSeries.monomial_zero_eq_C_apply ..).symm
lemma down (h : Near x f) : Near (-x) (-f) := by
  have he := mult (fixed (-1:K)) h
  rw [map_neg,map_one,neg_one_mul] at he
  convert he using 1; funext t; simp [Pi.neg_apply]
lemma lower (h : Near x f)(H : Near y g) : Near (x-y) (f-g) := by simp_rw [sub_eq_add_neg]; exact incline h (down H)
lemma sums_at {I : Type*}{x : I→ℝ→K}{f : I→PowerSeries K}(s : Finset I)(h : ∀ i∈s,Near (x i) (f i)) : Near (∑ i∈s,x i) (∑ i∈s,f i) := by
  unfold Near; simp_rw [map_sum]
  convert Aspiration.sum s x (fun i k => coeff k (f i)) h using 1
  funext t; rw [Finset.sum_apply]
lemma terms_at {I : Type*}{x : I→ℝ→K}{f : I→PowerSeries K}(s : Finset I)(h : ∀ i∈s,Near (x i) (f i)) :
    Near (fun t => ∑ i∈s,x i t) (∑ i∈s,f i) := by
  convert sums_at s h using 1
  funext t; rw [Finset.sum_apply]
lemma stand (h : Near x f) (s : ℕ) : Near (x^s) (f^s) := by
  induction s with
  | zero => rw [pow_zero,pow_zero]; have he := fixed (1:K); rw [map_one] at he; exact he
  | succ k ih => rw [pow_succ,pow_succ]; exact mult ih h
lemma scaled (h : Near x f)(c : K) : Near (c • x) (PowerSeries.C c*f) := mult (fixed c) h
lemma promote (h : Near x f)(k : ℕ) : Near (fun t => t^k • x t) (X^k*f) := by
   have hh := mult (mono (1:K) k) h
   rw [← PowerSeries.X_pow_eq] at hh
   convert hh using 1
   funext t; simp
lemma priced {k : ℕ}(h : Near (fun t=>t^k • x t) (PowerSeries.X^k*f)) : Near x f := by
   intro n
   obtain ⟨C,hC,H⟩ := h (k+n)
   refine ⟨C,hC,?_⟩
   filter_upwards [H,Tested.eventually_pos] with t ht hT
   let F m := coeff m f
   have hr : peval (fun i => coeff i (PowerSeries.X^k*f)) (k+n) t=t^k • peval F n t := by
     unfold peval Zone.eval
     rw [show k+n+1=k+(n+1) from Nat.add_assoc k n 1, Finset.sum_range_add,Finset.sum_eq_zero (f:= fun i=> t^i • coeff i (PowerSeries.X^k*f)),zero_add, Finset.smul_sum]; swap
     · intro i hi; rw [PowerSeries.coeff_X_pow_mul',if_neg (Nat.not_le.mpr (mem_range.mp hi)),smul_zero]
     apply sum_congr rfl; intro i _
     dsimp only; rw [add_comm k i, PowerSeries.coeff_X_pow_mul _ _ _, pow_add,mul_comm (t^i),mul_smul]
   change ‖t^k • x t-peval _ (k+n) t‖≤_ at ht
   rw [hr,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos hT _),add_assoc,pow_add,mul_left_comm] at ht
   exact le_of_mul_le_mul_left ht (pow_pos hT _)
end Near
end field
end YM.RG02.Asym
