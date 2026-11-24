import YM.Dash.Limits

/-! A finite test basis gives a common bound on every pair of bounded source vectors,
from convergence of the actually measured scalar matrix entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteReflectedMatrix
open Filter Set
open scoped Topology Classical BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
private theorem expand {I : Type*} [Fintype I] (e : Module.Basis I ℂ E) (L : E→ₗ[ℂ] ℂ) (x : E) :
    L x = ∑ i,e.repr x i * L (e i) := by
  conv_lhs => rw [←e.sum_repr x]
  simp only [map_sum,map_smul,smul_eq_mul]

theorem bounded {I : Type*} (l : Filter I) (q : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) (a : I→E →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (entry : ∀ x y,Tendsto (fun r=>a r x y) l (𝓝 (q x y))) {U V : ℝ} (hU : 0≤U) (hV : 0≤V) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ r in l, ∀ x y : E, ‖x‖≤U → ‖y‖≤V → ‖a r x y‖≤B := by
  let e := Module.finBasis ℂ E
  let T := Fin (Module.finrank ℂ E)
  let co (i : T) := (e.coord i).toContinuousLinearMap
  let c (i j : T) := ‖q (e i) (e j)‖+1
  have nonneg (i j : T) : 0≤c i j := by dsimp [c]; positivity
  have price : ∀ᶠ r in l, ∀ i j : T, ‖a r (e i) (e j)‖<c i j := eventually_all.mpr
    (fun i=>eventually_all.mpr (fun j=>(entry (e i) (e j)).norm.eventually_lt_const (lt_add_one _)))
  let H (i : T) := ∑ j:T,(‖co j‖*V)*c i j
  have hH (i : T) : 0≤H i := Finset.sum_nonneg (fun j _=>mul_nonneg (mul_nonneg (norm_nonneg _) hV) (nonneg i j))
  refine ⟨∑ i:T,(‖co i‖*U)*H i,Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (norm_nonneg _) hU) (hH i)),?_⟩
  filter_upwards [price] with r h x y hx hy
  have coord (i : T) (z : E) : ‖e.repr z i‖≤‖co i‖*‖z‖ := (co i).le_opNorm z
  have row (i : T) : ‖a r (e i) y‖≤H i := by
    rw [expand e (a r (e i)) y]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _=>?_))
    rw [norm_mul]
    exact mul_le_mul ((coord j y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _)))
      (h i j).le (norm_nonneg _) (mul_nonneg (norm_nonneg _) hV)
  let first := (LinearMap.applyₗ (R:=ℂ) y : (E→ₗ[ℂ]ℂ)→ₗ[ℂ]ℂ).comp (a r)
  change ‖first x‖≤_
  rw [expand e first x]
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>?_))
  rw [norm_mul]
  exact mul_le_mul ((coord i x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))
    (row i) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hU)

end YM.Integration.WilsonFiniteReflectedMatrix
