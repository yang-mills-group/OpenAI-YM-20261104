import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! A finite collection of possibly dependent emissions pays its complete
moment from its measured one-variable moments, with the same total price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMeasuredPathMoments
open MeasureTheory Finset Set
open scoped BigOperators Classical

variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem pooled (μ : Measure Ω) (S : Finset ι) (c : ι → ℝ) (f : ι → Ω → ℝ)
    (pos : ∀ i ∈ S,0 < c i) (nonneg : ∀ i ∈ S,∀ω,0 ≤ f i ω)
    (hm : ∀ i ∈ S,AEStronglyMeasurable (f i) μ) (l : ℕ)
    (hp : ∀ i ∈ S,Integrable (fun ω => (f i ω)^(l+1)) μ ∧
      (∫ω,(f i ω)^(l+1) ∂μ) ≤ (c i)^(l+1)) :
    let total := ∑i∈S,c i
    let Y ω := (∑i∈S,f i ω)^(l+1)
    Integrable Y μ ∧ (∫ω,Y ω ∂μ) ≤ total^(l+1) := by
  classical
  intro total Y
  rcases S.eq_empty_or_nonempty with hs|hs
  · subst S
    simp [Y,total]
  have ht : 0 < total := Finset.sum_pos pos hs
  let θ (i : ι) := c i/total
  have positive i (hi : i∈S) : 0 ≤ θ i := (div_pos (pos i hi) ht).le
  have unit : ∑ i∈S,θ i=1 := by
    change (∑ i∈S,c i/total)=1
    rw [←Finset.sum_div]
    exact div_self ht.ne'
  let u (i : ι) (ω : Ω) := (f i ω/c i)^(l+1)
  have scaled (i) (hi : i∈S) : Integrable (u i) μ ∧ (∫ω,u i ω ∂μ) ≤ 1 := by
    have h := hp i hi
    constructor
    · simpa only [u,div_pow] using h.1.div_const ((c i)^(l+1))
    · simp only [u,div_pow,integral_div]
      exact (div_le_one (pow_pos (pos i hi) _)).mpr h.2
  let Q ω := total^(l+1)*(∑i∈S,θ i*u i ω)
  have qi : Integrable Q μ :=
    (integrable_finsetSum _ fun i hi => (scaled i hi).1.const_mul (θ i)).const_mul _
  have cover (ω : Ω) : Y ω ≤ Q ω := by
    have jensen := (convexOn_pow (𝕜:=ℝ) (l+1)).map_sum_le (t:=S) (w:=θ) (p:=fun i=>f i ω/c i)
      positive unit (fun i hi => div_nonneg (nonneg i hi ω) (pos i hi).le)
    have same : (∑i∈S,f i ω)=total*(∑i∈S,θ i*(f i ω/c i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      dsimp only [θ]
      field_simp [ht.ne',(pos i hi).ne']
    change (∑i∈S,f i ω)^(l+1) ≤ _
    rw [same,mul_pow]
    exact mul_le_mul_of_nonneg_left jensen (pow_nonneg ht.le _)
  have yi : Integrable Y μ := qi.mono'
    ((continuous_pow (l+1)).comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum S hm)) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (Finset.sum_nonneg fun i hi=>nonneg i hi ω) _)]
      exact cover ω)
  refine ⟨yi,?_⟩
  calc
    _ ≤ ∫ω,Q ω ∂μ := integral_mono yi qi cover
    _ = total^(l+1)*(∑i∈S,θ i*(∫ω,u i ω ∂μ)) := by
      unfold Q
      rw [integral_const_mul,integral_finsetSum _ (fun i hi=>(scaled i hi).1.const_mul (θ i))]
      simp only [integral_const_mul]
    _ ≤ total^(l+1)*(∑i∈S,θ i*1) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi=>mul_le_mul_of_nonneg_left (scaled i hi).2 (positive i hi)) (pow_nonneg ht.le _)
    _ = total^(l+1) := by simp [unit]

end YM.Integration.QLocalMeasuredPathMoments
end

