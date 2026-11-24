import YM.QuadraticLocal.Fk.Maps
/-!
# Carry field-independent marks unchanged

Core identity for projecting nonextensive terms in the prescription when
some sources entered as analytic global marks. Does not impose differentiability
on a normalized *error* or assume it analytic. No data flattenings in the regulator.
Hypothesis δz ∀ noise: uses only TRUE linear translation of Bulk.
 Inspired by `Comparison.RG02.Gallery.Append`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Morph
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series
open Marker Multi Next.SectorChange
open Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V W : Type} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
variable {R : Census V}
variable {k:ℕ}
section integ
-- equivalent of (linear map) specialized to not need norm/Cl.Env reader Card imports.
variable {I:Type*}[MeasurableSpace I](p:I→Poly R)(μ:Measure I)(x a:Poly R)
omit [Fintype V] in
private lemma ar (f g: Poly R)(i:R.Mode)(s:R.Mode)(t:R.Mode) : (if Poly.merges i s t then f.part i*g.part s else 0)= (if Poly.merges i s t then f.part i else 0)*g.part s:=by split <;> simp
lemma shares (s:R.Mode)(hp:∀ j,Integrable (fun i=>(p i).part j) μ ∧ x.part j=∫ i,(p i).part j ∂μ) : (a*x).part s=∫ i, (a*p i).part s ∂μ:=by
 simp_rw [Poly.part_mul,ar]; rw [integral_finsetSum]; rotate_left;
 · exact fun i _=> integrable_finsetSum _ (fun k _=> (hp k).1.const_mul _)
 refine Finset.sum_congr rfl (fun i _=>?_); rw [integral_finsetSum] -- rewrite reason?
 rotate_left
 · exact fun k _=> (hp k).1.const_mul _
 refine Finset.sum_congr rfl (fun i _=>?_); rw [ (hp i).2,integral_const_mul]
end integ
variable {G:Gauge}{c f:Side}{T: StepData c f}{B:Clip}{P:PathData G}{O:ChartRatio G}
open Comparison.RG02 Assembly Bulk
open Extra.Trajectories (pass_connected pass_zero pass_add)
variable (L: Comparison.RG02.Bulk.Kernel T B P O)(X: Forest T.ratio)(C W': Colors R G f)(t:T.Choices)(x: Exterior.fieldDir G c 1)
set_option quotPrecheck false
local notation "Q"=> Grade R k
local notation "Ω" v:max=> Bulk.Fk L X t v x k
local notation "Ξ"=> Precision.Key X G
local notation "u₀"=> (L.covariance X t)
local notation "μ"=> (Gaussian.cloud u₀)
local notation "Φ" v:max y:max=> (Assembly.affine (v).power (Bulk.markFn T X v) (Bulk.geometric L X t v) y)
local notation "ρ"=> (Bulk.translated L X x)
variable (a₀:Grade R k) (ha: denominator a₀=0)
variable (hV: ∀ z: Precision.Key X G→ℝ, Order.series R k ( Assembly.affine W'.power (Bulk.markFn T X W') (Bulk.geometric L X t W') (Bulk.translated L X x z))= a₀+Order.series R k (Assembly.affine C.power (Bulk.markFn T X C) (Bulk.geometric L X t C) (Bulk.translated L X x z)))
local notation "Wv" v:max=> Assembly.expansions (v).power (Bulk.markFn T X v) (Bulk.geometric L X t v)
include hV ha
lemma boost : (Ω W')= Poly.pass a₀ * (Ω C):= by
   let p (z:Ξ→ℝ):= (Order.series R k ((Wv C) ((ρ) z))); let q (z:Ξ→ℝ) := Order.series R k ((Wv W') ((ρ) z));
   have he:= Assembly.contracted ( Bulk.stage L X x) (Bulk.hinge X) C.power (Bulk.markFn T X C) (Bulk.geometric L X t C) u₀ (L.symm X t) (L.positive X t) k; let h:= Assembly.contracted (Bulk.stage L X x) (Bulk.hinge X) W'.power (Bulk.markFn T X W') (Bulk.geometric L X t W') u₀ (L.symm X t) (L.positive X t) k; have hx:a₀.part (Board R k).quiet=0:= (Order.bottom_quiet a₀).symm.trans (congr_arg (fun i:Grade R k=> i.part (Board R k).quiet) ha)
   have hp (z): q z=Poly.pass a₀ * p z := by unfold q p; rw [Assembly.exponent_identity,Assembly.exponent_identity,hV z, pass_add hx (Assembly.driver_quiet ..)]
   apply Marker.Poly.ext; intro i; rw [Morph.shares p μ (Ω C) (Poly.pass a₀) i he]; refine (h i).2.trans ?_; change (∫ z,(q z).part i ∂μ)=_; apply integral_congr_ae (Eventually.of_forall fun z=>?_); rw [hp]; -- no goal
lemma regularize : Order.logMarked (Ω W')=a₀+Order.logMarked (Ω C):= by
 let g:= (Ω C); let u:= Poly.pass a₀; have hx : a₀.part (Board R k).quiet=0:= (Order.bottom_quiet a₀).symm.trans (congr_arg (fun i:Grade R k=> i.part (Board R k).quiet) ha); have he : Order.denominator (Poly.pass a₀)=1:=by rw [Order.denominator, Multi.pass_map _ a₀ hx ((bottom_quiet a₀).trans hx), show Order.bottom R k a₀=0 from ha, pass_zero] -- might ambiguous
 rw [boost L X C W' t x a₀ ha hV]; let hq := Ω W'; have hg : Order.ratio (Poly.pass a₀ * g)= u * Order.ratio g:= by unfold ratio denominator; rw [_root_.map_mul,show Order.bottom R k (Poly.pass a₀)=1 from he,one_mul,mul_assoc]
 change Order.logMarked (Poly.pass a₀ * g)=_; unfold Order.logMarked; rw [hg, connected_mul (Poly.pass_part a₀ hx) (Order.ratio_quiet (show Order.UnitLeading g from Bulk.fk_unit ..)), connected_pass hx]
end YM.QuadraticLocal.Morph
