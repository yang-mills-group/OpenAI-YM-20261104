import YM.Euclid.Test
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Fixed-compact geometry and quantitative seminorm price

Use a max-style `C1` cost, holding across shape support, so this is continuous
for the indicated profile tests (pay more derivatives later only when explicitly
needed). Norm on Points n is ordinary Euclidean throughout, bilinear evaluation.
No accuracy claim on eventual contact components.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.TestBudget
open Filter Function Set MeasureTheory
open scoped Topology ContDiff BigOperators
variable {n : ℕ} {K : Set (Points n)} (f : Test n)

def Bound (b : ℝ) := ∀ x:Points n, ‖f x‖ ≤ b ∧ ‖fderiv ℝ (f:Points n → ℂ) x‖ ≤ b
lemma bound_fin : ∃ b:ℝ,0<b ∧ Bound f b:=by
  obtain ⟨C,h⟩:= f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨D,h'⟩:= (f.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support (f.hasCompactSupport.fderiv ℝ)
  obtain ⟨B,hB⟩:= exists_gt (max (max C D) 0)
  refine ⟨B,lt_of_le_of_lt (le_max_right ..) hB,fun x=>⟨?_,?_⟩⟩
  · exact (h x).trans (le_trans (le_max_left ..) ((le_max_left ..).trans hB.le))
  exact (h' x).trans (le_trans (le_max_right ..) ((le_max_left ..).trans hB.le))
lemma bound_nonneg {b : ℝ} (h : Bound f b): 0≤b := (norm_nonneg _).trans (h 0).1

def Damp (P : Points n→ℂ): Points n→ℂ:= (f:Points n → ℂ)* P
lemma damped (P : Points n→ℂ): tsupport (Damp f P) ⊆ tsupport f := by unfold tsupport; apply closure_mono; exact fun x hx => (left_ne_zero_of_mul (show f x*P x ≠ 0 from hx))
lemma charges (P : Points n→ℂ) (h: ∀ x∈conf n, ContDiffAt ℝ ∞ P x) : ContDiff ℝ ∞ (Damp f P):=by
  rw [contDiff_iff_contDiffAt]; intro x; by_cases hx:x∈tsupport f
  · exact f.contDiff.contDiffAt.mul (h _ (f.tsupport_subset hx))
  refine (show ContDiffAt ℝ ∞ (fun _ : Points n => (0:ℂ)) x from contDiffAt_const).congr_of_eventuallyEq ?_
  filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds (show x∈(tsupport f)ᶜ from hx)] with y hy
  exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hy) (P y)
lemma integral_pays (P : Points n→ℂ) (h: ∀ x∈conf n, ContDiffAt ℝ ∞ P x): Integrable (Damp f P):= ((charges f P h).continuous).integrable_of_hasCompactSupport (f.hasCompactSupport.mul_right)

-- price of smooth kernels smeared on this shape. Uniform when crossing into or out of diagonal collar.
lemma global (h : IsCompact K) (hp : K⊆ conf n) (P : Points n→ℂ) (H : ∀ x∈conf n,ContDiffAt ℝ ∞ P x): ∃ C:ℝ, 0 ≤ C∧∀ f : Test n, tsupport f ⊆ K → ∀ b:ℝ, Bound f b→ ∀ x y:Points n, ‖Damp f P x-Damp f P y‖ ≤ b*C*dist x y:=by
  have hu:ContinuousOn P K:= fun x hx=> ((H x (hp hx)).continuousAt).continuousWithinAt
  have hu' : ContinuousOn (fderiv ℝ P) K:=fun x hx=> ((H x (hp hx)).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := (h.image_of_continuousOn hu.norm).bddAbove; obtain ⟨T,hT⟩:=(h.image_of_continuousOn hu'.norm).bddAbove
  let D:=max C 0; let S:=max T 0; have hd : 0≤D:=le_max_right ..; have hS:0≤S:=le_max_right ..
  refine ⟨D+S,add_nonneg hd hS,fun f hf b hb x y=>?_⟩
  rw [dist_eq_norm]; apply (convex_univ (𝕜:=ℝ)).norm_image_sub_le_of_norm_fderiv_le (fun x _=> (charges f _ H).differentiable (by simp) x) _ (mem_univ y) (mem_univ x)
  intro i _; have hh:=bound_nonneg f hb; by_cases hx:i∈ tsupport f
  · have ht:‖P i‖≤D:=(hC (mem_image_of_mem (fun x=>‖P x‖) (hf hx))).trans (le_max_left ..); have hp': ‖fderiv ℝ P i‖≤S:=(hT (mem_image_of_mem (fun x=>‖fderiv ℝ P x‖) (hf hx))).trans (le_max_left ..)
    rw [Damp,fderiv_mul (f.contDiff.differentiable (by simp) i) ((H _ (hp (hf hx))).differentiableAt (by simp))]
    apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,mul_add,add_comm (b*D),mul_comm b D]; gcongr
    · exact (hb i).1
    exact (hb i).2
  have he:i∉ tsupport (Damp f P) := fun hk=>hx (damped f _ hk)
  rw [fderiv_of_notMem_tsupport ℝ he,norm_zero]; positivity
end YM.XSpace.TestBudget
