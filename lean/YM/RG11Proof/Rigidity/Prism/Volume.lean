import YM.RG11Proof.Rigidity.Prism.WordPolar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Compact-support moment comparison. Reflection in a line suffices; no claims
about all invariant tensors of the color-group Lie algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Prism
open scoped BigOperators InnerProductSpace Topology
open Function Set MeasureTheory Metric Maxwell.Free

-- finite-dimensional samples of the REAL label frames. Only the intrinsic
-- Euclidean measure (not a white noise measure).
variable {I : Type*} [Fintype I]
abbrev Desk (I : Type*) := EuclideanSpace ℝ I
def circle (I : Type*) [Fintype I] : Set (Desk I) := closedBall 0 1
lemma circle_mem {a : Desk I} : a∈circle I ↔ ‖a‖≤1 := by simp [circle]
lemma transitive (a b : Desk I) (h : ‖a‖=‖b‖) : ∃ S : Desk I≃ₗᵢ[ℝ] Desk I, S a=b := by
  by_cases hh : a+b=0
  · exact ⟨.neg _, (eq_neg_of_add_eq_zero_right hh).symm⟩
  have he : ‖a+b‖^2=2*inner ℝ (a+b) a := by
    rw [norm_add_sq_real, inner_add_left,real_inner_self_eq_norm_sq,real_inner_comm b,h]
    ring
  have ht : ‖a+b‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hh)
  refine ⟨Submodule.reflection (Submodule.span ℝ {a+b}),?_⟩
  rw [Submodule.reflection_singleton_apply,two_smul ℕ,← add_smul]
  change (inner ℝ (a+b) a/‖a+b‖^2+(inner ℝ (a+b) a/‖a+b‖^2)) • (a+b)-a=b
  rw [show (inner ℝ (a+b) a/‖a+b‖^2)+(inner ℝ (a+b) a/‖a+b‖^2)=1 from ?_,one_smul]; abel
  field_simp; linarith

def hue (l : List (Desk I)) (x : Desk I) := (l.map fun a=>inner ℝ a x).prod
def tour (l : List (Desk I)) := ∫ x in circle I, hue l x
lemma hue_nil (x : Desk I) : hue [] x=1 := rfl
lemma hue_a (a x : Desk I) (l : List (Desk I)) : hue (a::l) x = inner ℝ a x * hue l x := by simp [hue]
lemma hue_cont (l : List (Desk I)) : Continuous (hue l) := by
  induction l with | nil=> exact continuous_const | cons a l h=> rw [funext (fun x=> hue_a a x l)]; exact (continuous_const.inner continuous_id).mul h
lemma hue_cash (l : List (Desk I)) : IntegrableOn (hue l) (circle I) :=
  (hue_cont l).continuousOn.integrableOn_compact (isCompact_closedBall ..)

lemma rotate (l : List (Desk I)) (R : Desk I≃ₗᵢ[ℝ] Desk I) : tour (l.map R) = tour l := by
  have ht : R.toHomeomorph ⁻¹' (circle I)=circle I := by ext x; change R x∈circle I ↔ _; rw [circle_mem,circle_mem]; simp
  unfold tour
  have hR := R.measurePreserving
  have hi := hR.setIntegral_preimage_emb (g:=hue (l.map R)) R.toHomeomorph.toMeasurableEquiv.measurableEmbedding (circle I)
  change (∫ x in R.toHomeomorph ⁻¹' circle I, hue (l.map R) (R x))= _ at hi
  rw [ht] at hi; rw [← hi]
  simp [hue,List.map_map,comp_def]

variable {I : Type} [Fintype I]
lemma circle_scale (s : ℝ) (n : ℕ) (a : Desk I) : tour (List.replicate n (s • a))=s^n*tour (List.replicate n a) := by
  unfold tour hue
  simp [real_inner_smul_left,mul_pow, MeasureTheory.integral_const_mul]
lemma tour_law : Weight (tour (I:=I)) where
  swappable {L t} h := by unfold tour hue; simp_rw [fun x : Desk I=> (h.map (fun a=> inner ℝ a x)).prod_eq]
  ratio c a L:=by unfold tour; simp_rw [hue_a,real_inner_smul_left,mul_assoc,integral_const_mul]
  plus a b L := by
    unfold tour; simp_rw [hue_a,inner_add_left,add_mul]
    rw [integral_add]; all_goals exact hue_cash (_::L)

lemma pair_law : Weight (pairCost (@inner ℝ (Desk I) _)) where
  swappable h := pair_perm _ (fun a b=> real_inner_comm b a) h
  ratio t a L := by rw [pair_step,pair_step]; unfold pulls; simp [real_inner_smul_left,Finset.mul_sum,mul_assoc]
  plus a b L := by rw [pair_step,pair_step,pair_step]; unfold pulls; simp [inner_add_left,add_mul, Finset.sum_add_distrib]

end YM.RG11.Rigidity.Prism
