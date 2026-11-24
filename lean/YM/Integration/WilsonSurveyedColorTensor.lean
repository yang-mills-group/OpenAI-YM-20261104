import YM.SchemeConversionRG11.Maxwell.Cartan
import YM.MSbar.Pole.Book.Action
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Receipt

/-! The real color convention on the independent continuum numerator. The
two indices at a sewn line transform separately before the color sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorTensor
open Function Maxwell Maxwell.Free SchemeConversionRG11.Corona
open scoped BigOperators InnerProductSpace Classical

variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "I" => G.ColorIndex
local notation "e" => EuclideanSpace.basisFun I ℝ

theorem bracket (same : ∀ x y z, arch (U x) (U y) (U z) = arch x y z)
    (x y : G.Color) : U (G.ad x y) = G.ad (U x) (U y) := by
  apply ext_inner_left ℝ
  intro z
  obtain ⟨w,rfl⟩ := U.surjective z
  exact (U.inner_map_map w (G.ad x y)).trans (same w x y).symm

theorem observed (reading : ∀ A, Maxwell.probe
    (commerce U.toContinuousLinearEquiv.toContinuousLinearMap A) (vase G) =
      Maxwell.probe A (vase G)) :
    bracketForm U.toContinuousLinearEquiv.toContinuousLinearMap :=
  vase_forces U.norm_map reading

def entry (i j : I) : ℂ := ((U (e j)) i : ℝ)

theorem sewn (i j : I) :
    ∑ a, entry U a i * entry U a j = if i=j then 1 else 0 := by
  have h : ∑ a, (U (e i)) a * (U (e j)) a = if i=j then 1 else 0 := by
    change inner ℝ (U (e j)) (U (e i)) = _
    rw [U.inner_map_map, EuclideanSpace.basisFun_inner]
    simp [EuclideanSpace.basisFun_apply, eq_comm]
  unfold entry
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, h]
  split <;> simp

/-- The product basis on a complete finite set of open color ports. -/
def ports {E : Type} [Fintype E] (i j : E → I) : ℂ :=
  ∏ k, entry U (i k) (j k)

theorem wires {E : Type} [Fintype E] (a b : E → I) :
    ∑ i, ports U i a * ports U i b = if a=b then 1 else 0 := by
  simp only [ports, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (f:=fun k i => entry U i (a k) * entry U i (b k))]
  simp_rw [sewn]
  by_cases h : a=b
  · subst b
    simp
  rw [if_neg h]
  obtain ⟨k,hk⟩ : ∃ k, a k ≠ b k := by
    by_contra! contra
    exact h (funext contra)
  exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- Contract every labeled edge, allowing self loops and edges between
different source vertices. Any external source or Laurent coefficient can
be held fixed in the body. -/
theorem closed {E : Type} [Fintype E] (body : (E→I) → (E→I) → ℂ) :
    (∑ i, ∑ a, ∑ b, ports U i a * ports U i b * body a b) = ∑ a, body a a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, wires]
  simp

end YM.Integration.WilsonSurveyedColorTensor
end
