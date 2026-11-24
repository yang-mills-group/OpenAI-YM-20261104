import YM.AnalyticNext.CUBIC_MATCH.Terms.Normal
/-!
# Charts of countably many mark arrangements at once (analytic)

Applications use W gauges and θ links at each volume-seam pose. This calculus is
useful: like `CubicMatch.compose_series` but returns all finite order *tensor*
evaluants on **multidimensional real** path. No topology in the label address of the
test; the bound is earned from analytic kernel widths for every pulse separately.
 `normal` establishes termwise differentiation so also ties Work at any Sobolev
 approximate shading after projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Brilliant
open Filter Function Set Metric ContinuousMultilinearMap Work.F02
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {ι E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F][CompleteSpace F]
variable [NormedSpace ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
variable {u:ι→ℝ} {f:ι→ E→ F}{z:E}{r:ℝ}
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] (P: Z→ E)(x:Z)(hP:ContDiffAt ℝ ω P x)
variable (hr:0<r) (hu:Summable u)
variable (h:∀i, ContDiff ℂ ω (f i))(he:∀ i y,y∈ball (P x) r → ‖f i y‖ ≤ u i)
include h he hu hr hP
-- Watch α before orders. Keep all directions.
lemma path : ContDiffAt ℝ ω (fun t=> ∑' i, f i (P t)) x := ((Work.F02.analytic_series f hr (fun i=> (h i).differentiable (by simp)) hu he).contDiffAt.restrict_scalars ℝ).comp x hP
lemma attends (k:ℕ)(y:Fin k→ Z): HasSum (fun i=> iteratedFDeriv ℝ k (f i ∘ P) x y) (iteratedFDeriv ℝ k (fun t=>∑' i, f i (P t)) x y):= by
 let F₀ (u:OrderedFinpartition k)(g:E→F):= (iteratedFDeriv ℝ u.length g (P x)) (fun i=> iteratedFDeriv ℝ (u.partSize i) P x (fun j=> y (u.emb i j)))
 have hv (g:E→ F)(hc:ContDiffAt ℝ ω g (P x)): iteratedFDeriv ℝ k (g ∘ P) x y=∑ u: OrderedFinpartition k, F₀ u g:= by rw [iteratedFDeriv_comp hc hP le_top,FormalMultilinearSeries.taylorComp,_root_.sum_apply]; rfl
 let g (s:E):= ∑' i,f i s; have hg: ContDiffAt ℝ ω g (P x):= (Work.F02.analytic_series f hr (fun i=> (h i).differentiable (by simp)) hu he).contDiffAt.restrict_scalars ℝ
 rw [show (fun i=>iteratedFDeriv ℝ k (f i ∘ P) x y)=(fun i=>∑ u:OrderedFinpartition k,F₀ u (f i)) from funext (fun i=> hv _ ((h i).contDiffAt.restrict_scalars ℝ)),show (fun t=>∑' i, f i (P t))=g∘ P from rfl, hv g hg]; exact hasSum_sum (fun i _=> ContinuousMultilinearMap.hasSum_eval (CubicMatch.real_sum_terms i.length hr h hu he) _)
end YM.QuadraticLocal.Brilliant
