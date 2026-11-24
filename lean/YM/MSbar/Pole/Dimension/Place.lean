import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Tensor variables, in arbitrarily high honest dimension

`place n` has real dimension `2n`, used for DIMENSIONAL tensors, not a spinning color space.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped Topology InnerProductSpace Classical BigOperators
abbrev place (n : ℕ) := EuclideanSpace ℝ (Fin (2*n))

namespace place

/-- Arbitrary fixed choice of isometric embedding plus two new axes (identified with ℂ). -/
def globe (n : ℕ) : WithLp 2 (place n × ℂ) ≃ₗᵢ[ℝ] place (n+1) :=
    (((EuclideanSpace.basisFun (Fin (2*n)) ℝ).prod Complex.orthonormalBasisOneI).reindex
         (finSumFinEquiv.trans (finCongr (by ring)))).repr

def portal (n : ℕ) : (place n × ℂ) ≃L[ℝ] place (n+1) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (place n) ℂ).symm.trans (globe n).toContinuousLinearEquiv
@[simp] lemma via (n : ℕ) (v : place n × ℂ) : globe n (WithLp.toLp 2 v)=portal n v:= rfl

lemma volumeThrough (n : ℕ): MeasurePreserving (portal n) :=
    (globe n).measurePreserving.comp (WithLp.volume_preserving_toLp (place n) ℂ)
variable {n : ℕ}
def pad (n : ℕ) : place n →L[ℝ] place (n+1) := (portal n).toContinuousLinearMap.comp (ContinuousLinearMap.inl ..)
def room (n : ℕ):ℂ →L[ℝ] place (n+1) := (portal n).toContinuousLinearMap.comp (ContinuousLinearMap.inr ..)
@[simp] lemma pad_at (x : place n) : pad n x = portal n (x,0):=rfl
@[simp] lemma room_at (y : ℂ) : room n y = portal n (0,y):=rfl
lemma split (x : place n) (y : ℂ) : portal n (x,y)=pad n x+room n y:= by rw [pad_at,room_at,← map_add]; simp
@[simp] lemma dot (x y : place n × ℂ) : inner ℝ (portal n x) (portal n y)=inner ℝ x.1 y.1 + inner ℝ x.2 y.2 := by rw [← via,← via]; rw [LinearIsometryEquiv.inner_map_map]; rfl
lemma squared (x : place n × ℂ) : ‖portal n x‖^2 = ‖x.1‖^2+‖x.2‖^2:= by rw [← via,LinearIsometryEquiv.norm_map,WithLp.prod_norm_sq_eq_of_L2]; rfl

def grow (J : place n ≃ₗᵢ[ℝ] place n) : place (n+1) ≃ₗᵢ[ℝ] place (n+1) := (globe n).symm.trans
      ((LinearIsometryEquiv.withLpProdCongr 2 J (LinearIsometryEquiv.refl ℝ ℂ)).trans (globe n))
@[simp] lemma grow_apply (J : place n ≃ₗᵢ[ℝ] place n) (x : place n × ℂ) : grow J (portal n x) = portal n (J x.1,x.2) := by rw [← via]; simp only [grow,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_apply_apply]; rfl

/-- Rotate displacements with fixed inner products with the external vectors; useful with soft
probes and when lifting traces. -/
lemma sphere {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {x y : E} (h : ‖x‖^2=‖y‖^2) : ∃ J : E≃ₗᵢ[ℝ] E,J x=y ∧ ∀ z:E, inner ℝ z x=inner ℝ z y → J z=z := by
  refine ⟨Submodule.reflection (ℝ ∙ (x-y))ᗮ, Submodule.reflection_sub ?_,fun z hx=> Submodule.reflection_mem_subspace_eq_self ?_⟩
  · nlinarith [norm_nonneg x,norm_nonneg y]
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right,hx,sub_self]
end place
end YM.MSbar.Pole
