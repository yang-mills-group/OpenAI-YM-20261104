import YM.QuadraticLocal.Fk.Fiber
import YM.Comparison.RG02.Bulk.Fk
/-! # Map the entire input action and the conditional denominator to actual mark queries

Exact identity, separately use the available estimates. The hypothesis on `laid` is proved
for query bindings in next layer; hence no assumption of feasibility of transfer across *all*
label geometries or unknown analytic tasks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Morph
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series
open Marker Multi Next.SectorChange
open Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V W : Type} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
variable {R : Census V} {S : Census W}
variable {k:ℕ}
variable (F:Poly R →ₐ[ℂ] Poly S) (h:∀x,(F x).part S.quiet=x.part R.quiet)
section integ
omit [Fintype V] in
private lemma scaled (a:ℂ)(p:R.Mode): Poly.send p a=a • Poly.send p 1:=by ext1 s; simp [mul_ite]
-- fiber expression good for mode clearance
omit [Fintype W] in
lemma aggregate (x:Poly R): F x=∑ j:R.Mode,x.part j • F (Poly.send j 1) := by nth_rw 1 [← Poly.studs x]; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> Eq.trans (congr_arg F (scaled _ _)) (map_smul F _ _)
variable {I:Type*}[MeasurableSpace I](p:I→Poly R)(q:I→Poly S)(μ:Measure I)(x:Poly R)(y:Poly S)
lemma boarding (he:q=F ∘ p)(hp:∀ j,Integrable (fun i=>(p i).part j) μ ∧ x.part j=∫ i,(p i).part j ∂μ)(hq:∀ s,y.part s=∫ i,(q i).part s ∂μ): F x=y:=by
 ext1 s; rw [aggregate F x,hq s]; subst q; change _= ∫ i,(F (p i)).part s ∂μ; conv_rhs=> enter [2,i]; rw [aggregate] -- check
 simp_rw [Poly.part_sum,Poly.part_smul]; rw [integral_finsetSum]; rotate_left;
 · exact fun i _=> ((hp i).1.mul_const _)
 exact Finset.sum_congr rfl fun i _=> by rw [(hp i).2,integral_mul_const]
end integ
variable {G:Gauge}{c f:Side}{T: StepData c f}{B:Clip}{P:PathData G}{O:ChartRatio G}
open Comparison.RG02 Assembly Bulk
variable (L: Comparison.RG02.Bulk.Kernel T B P O)(X: Forest T.ratio)(C: Colors R G f)(W':Colors S G f)(t:T.Choices)(x: Exterior.fieldDir G c 1)
set_option quotPrecheck false
local notation "Q"=> liftH k F
local notation "Ω" v:max=> Bulk.Fk L X t v x k
local notation "Ξ"=> Precision.Key X G
local notation "e₀"=> (Bulk.covariance L X t) -- check
local notation "u₀"=> (L.covariance X t)
local notation "μ"=> (Gaussian.cloud u₀)
local notation "Φ" v:max y:max=> (Assembly.affine (v).power (Bulk.markFn T X v) (Bulk.geometric L X t v) y)
local notation "ρ"=> (Bulk.translated L X x)
variable (hV: ∀ x:Bulk.Joint (G:=G) T X, PowerSeries.map F.toRingHom (Assembly.affine C.power (Bulk.markFn T X C) (Bulk.geometric L X t C) x) = Assembly.affine W'.power (Bulk.markFn T X W') (Bulk.geometric L X t W') x)
local notation "Wv" v:max=> Assembly.expansions (v).power (Bulk.markFn T X v) (Bulk.geometric L X t v)
include h hV
set_option maxHeartbeats 610000 in
lemma native : liftH k F (Ω C)=Ω W':= by
   let p (z:Ξ→ℝ):= (Order.series R k ((Wv C) ((ρ) z))); let q (z:Ξ→ℝ) := Order.series S k ((Wv W') ((ρ) z));
   refine boarding ( liftH k F ) p q μ (Ω C) (Ω W') ?_ (Assembly.contracted ( Bulk.stage L X x) (Bulk.hinge X) C.power (Bulk.markFn T X C) (Bulk.geometric L X t C) u₀ (L.symm X t) (L.positive X t) k) (fun j=> (Assembly.contracted (Bulk.stage L X x) (Bulk.hinge X) W'.power (Bulk.markFn T X W') (Bulk.geometric L X t W') u₀ (L.symm X t) (L.positive X t) k j).2)
   funext y; unfold Function.comp p q; let v:= Order.series R k (Assembly.affine C.power (Bulk.markFn T X C) (Bulk.geometric L X t C) ((ρ) y)); have he:= hV ((ρ) y); have hv:v.part (Board R k).quiet=0:= Assembly.driver_quiet ..; change Order.series S k ( (Wv W') ((ρ) y)) = Q (Order.series R k ((Wv C) ((ρ) y))); rw [Assembly.exponent_identity,Assembly.exponent_identity, ← he, ← even F, pass_map (liftH k F) v hv ((Morph.quiet F h v).trans hv)] -- let v.Morph effect subst
lemma inspection (u:ℕ): Order.observe S k (Order.logMarked (Ω W')) u= F ( Order.observe R k ( Order.logMarked (Ω C)) u):= by rw [← native F h L X C W' t x hV]; rw [logarithm F h _ (Bulk.fk_unit ..),wire]
end YM.QuadraticLocal.Morph
