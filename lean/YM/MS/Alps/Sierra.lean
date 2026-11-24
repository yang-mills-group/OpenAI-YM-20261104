import YM.MS.Alps.Small
/-!
# Differentiation estimates on scaled parameter windows

Use order-two Taylor testers with cost chosen any (pol or swift or a delta gauge).
 ∫ control not hidden; real z parameter possible. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{I A E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
   [NormedAddCommGroup A][NormedSpace ℝ A]
def Town0 (t:ℝ) := closedBall t 1 -- subtype? note Set coerced
variable (t:ℝ)
abbrev Trail0 (t:ℝ) := (Town0 t).Elem -- syntax .Elem?
def cord (x:Trail0 t):= (x:ℝ) - t
def slopeP (f:ℝ→ A)(Y:A) (x:Trail0 t): A:= f x-f t -cord t x • Y
variable {s:ℝ}
variable {f g H:ℝ→ A}
lemma taylor2 (h:∀ x, HasDerivAt f (g x) x) (hh:∀ x,HasDerivAt g (H x) x) {K:ℝ} (hk:∀ x∈closedBall t 1,‖H x‖≤K)(x:Trail0 t): ‖slopeP t f (g t) x‖ ≤ K * (cord t x)^2:= by
   let w:= cord t x; let X:=‖w‖; let U:=closedBall t X; have hx : 0≤X:=norm_nonneg _; have he: U⊆ closedBall t 1 := closedBall_subset_closedBall (mem_closedBall_iff_norm.mp x.property)
   have hp : t∈U:=mem_closedBall_self hx; have ht : (x:ℝ)∈U := mem_closedBall_iff_norm.mpr (le_refl X)
   let L(c:A):ℝ→L[ℝ] A:= ContinuousLinearMap.toSpanSingleton ℝ c
   have hL(y:ℝ)(hy:y∈U): ‖(L (g y)) - L (g t)‖ ≤ K* X:= by
       rw [show L (g y)-L (g t)=L (g y-g t) by ext; simp [L,smul_sub]]; unfold L; rw [ContinuousLinearMap.norm_toSpanSingleton]; -- inspect
       apply ((convex_closedBall t X).norm_image_sub_le_of_norm_hasDerivWithin_le (fun y hy=> (hh y).hasDerivWithinAt) (fun y hy=> hk y (he hy)) hp hy).trans; have hP:0 ≤K := (norm_nonneg _).trans (hk t (he hp)); gcongr; exact mem_closedBall_iff_norm.mp hy
   apply le_trans ((convex_closedBall t X).norm_image_sub_le_of_norm_hasFDerivWithin_le' (f:=f) (φ:= L (g t)) (fun y hy=> (h y).hasFDerivAt.hasFDerivWithinAt) hL hp ht); change K*X*X≤ K*w^2; rw [mul_assoc, ← pow_two]; simp [X,Real.norm_eq_abs,sq_abs]
end YM.MS.Alps
