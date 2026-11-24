import YM.Comparison.RG02.Assembly.Contact
import Mathlib.Analysis.Calculus.ContDiff.Bounds
/-!
# Grade protocol under valuation shifts

Track the actual field/t powers in the underlying input germs, with no
 statement yet on sizes. Works also for source monomial weights when a power
 starts negative in the coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly.GradeAt
open Function Filter PertExtension.Series ContinuousLinearMap
open scoped Topology BigOperators Classical ContDiff

variable {X Y W Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
 [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
 {i k n : ℕ} {f : X→W} {g : X→Y}

lemma unchecked {f : X→Y} (h : ContDiffAt ℝ ω f 0) : GradeAt 0 f := ⟨h,fun _ hh=>False.elim (by omega)⟩
lemma anchored {f : X→Y} (h : ContDiffAt ℝ ω f 0) (he : f 0=0) : GradeAt 1 f := ⟨h,fun j hj=> by
   have he' : j=0 := by omega
   subst j; ext x; rw [iteratedFDeriv_zero_apply,he]; rfl⟩
lemma linear_contact (L : W→L[ℝ]Y) (h : GradeAt k f) : GradeAt k (L∘f) := by
  refine ⟨L.contDiff.contDiffAt.comp _ h.smooth, fun i hi=>?_⟩; rw [L.iteratedFDeriv_comp_left h.smooth le_top,h.vanish i hi]; ext x; exact map_zero L
lemma combo (B : W→L[ℝ]Y→L[ℝ]Z) (hf : GradeAt k f) (hg : GradeAt i g) : GradeAt (k+i) (fun x=> B (f x) (g x)) := by
  refine ⟨(B.contDiff.contDiffAt.comp _ hf.smooth).clm_apply hg.smooth,fun j hj=>?_⟩
  obtain ⟨s,hs₁,hs⟩:= hf.smooth.contDiffOn (m:=ω) le_rfl (by simp)
  obtain ⟨v,hv₁,hv⟩:= hg.smooth.contDiffOn (m:=ω) le_rfl (by simp)
  obtain ⟨r,hr,H⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hs₁ hv₁)
  have hx:=Metric.isOpen_ball (x:=(0:X)) (ε:=r)
  have hy:=Metric.mem_ball_self (x:=(0:X)) hr
  have he := B.norm_iteratedFDerivWithin_le_of_bilinear (hs.mono (H.trans Set.inter_subset_left)) (hg:=hv.mono (H.trans Set.inter_subset_right)) hx.uniqueDiffOn hy (show (j:WithTop ℕ∞) ≤ ω from le_top)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hx hy] at he
  rw [Finset.sum_eq_zero, mul_zero] at he
  · exact norm_le_zero_iff.mp he
  intro n hn; simp only [Finset.mem_range] at hn
  rcases lt_or_ge n k with h|h
  · rw [hf.vanish n h]; simp
  rw [hg.vanish (j-n) (by omega)]; simp

lemma scale {f : X→ℝ} (hf : GradeAt k f) (hg : GradeAt i g) : GradeAt (k+i) (fun x=> f x • g x) := combo (lsmul ℝ ℝ) hf hg
lemma mul {A:Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g:X→A} (hf : GradeAt k f) (hg : GradeAt i g) : GradeAt (k+i) (f*g) := combo (ContinuousLinearMap.mul ℝ A) hf hg

lemma shifts (f : X→ℝ) (h : ContDiffAt ℝ ω f 0) (hv : f 0=0) (n : ℕ) : GradeAt n (fun y=> f y ^ n) := by
  induction n with
  | zero=> simp_rw [pow_zero]; exact unchecked contDiffAt_const
  | succ n ih=> simp_rw [pow_succ]; exact ih.mul (anchored h hv)

lemma list_sum {I:Type*} (s:Finset I) (f:I→X→Y) (h : ∀ v∈s,GradeAt k (f v)) : GradeAt k (fun x=> ∑ j∈s,f j x) := by
 induction s using Finset.induction with
 | empty => simp only [Finset.sum_empty]; exact grade_zero _
 | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (h _ (Finset.mem_insert_self ..)).add (ih (fun v hv=> h v (Finset.mem_insert_of_mem hv)))
end YM.Comparison.RG02.Assembly.GradeAt
