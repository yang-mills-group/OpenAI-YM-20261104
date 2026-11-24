import YM.FVA2.Feyn.Frill
import YM.FVA2.Arrival.Folio
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
/-!
 # Shared prescription with Gaussian-smeared gauges, instantiated and registered ports

 In particular use linear Landau condition on these orbit links. See `Feyn/Canonical` regarding
 coordinatization by `Root`. The FP derivative uses Root parameters (at the fixed
 site 0) also for the smeared calculation; gauge condition **values** can be expressed as
 actual divergence (mean-zero).
 FP on all link directions. Full gauge fluctuation covariance can use ANY compatible Law.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Feyn.Scent
open Function Set Filter Finset MeasureTheory PertExtension Orb Orbit Series Radial GaussianScore
open Laplace FormalOPE.RG10.MultiGauge Splice FVA2.Arrival
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable (G:Gauge) {n:Lattice.Side} (ev:Even n.val)
local notation "R"=> Root G n
local notation "V"=> Rep G n
local notation "S"=> Slice.Transverse G n -- check abbrev maybe FVA2.Slice?
open FVA2.Slice FVA2.Slice.FiniteOrbit  -- use level
-- choose the true normal to Landau

def divF : V →L[ℝ] R:= ContinuousLinearMap.fst ℝ R (Slice.Transverse G n) ∘L ( land G ev ).hurdle.symm.toContinuousLinearMap
include ev in
lemma clicks (p:R): divF G ev (vertical (0:V) p)=p:= by
 unfold divF; rw [ContinuousLinearMap.comp_apply]; rw [show vertical (0:V) p=(land G ev).hurdle (p,0) from Eq.symm ( ( tilted_here ev p 0 ).trans (by rw [map_zero,add_zero]) ) ]; exact congr_arg Prod.fst ( (land G ev).hurdle.symm_apply_apply _ )
lemma line_gauge (p:Rep G n): divF G ev p=0 ↔ p∈Set.range (( land G ev ).σ) := by
 constructor
 · intro h; let s:=land G ev; let v:= s.hurdle.symm p; refine ⟨v.2,?_⟩; change v.1=0 at h; have ht:s.hurdle (0,v.2)= s.σ v.2:= by rw [show s.hurdle (0,v.2)=_ from tilted_here ev 0 v.2,map_zero,zero_add]; rfl
   rw [← show _=( land G ev ).σ v.2 from ht,← show v.1=(0:R) from h]; exact s.hurdle.apply_symm_apply _
 rintro ⟨x,rfl⟩; have ht:( land G ev ).hurdle (0,x)=(land G ev).σ x:= by rw [tilted_here,map_zero,zero_add]; rfl
 rw [← ht]; exact congr_arg Prod.fst ((land G ev).hurdle.symm_apply_apply _)
def foil : Scent G n where
 d:= divF G ev
 origin:=map_zero _
 analytic:= (divF G ev).contDiff.contDiffAt
 shape:= by
    rw [ContinuousLinearMap.fderiv]; rw [ show divF G ev ∘L (vertical (0:Rep G n)).toContinuousLinearMap=ContinuousLinearMap.id ℝ R from ContinuousLinearMap.ext (fun x=> clicks G ev x) ]; exact bijective_id

private def reserve (n:ℕ): Law (EuclideanSpace ℝ (Fin n)) where
 P:= innerₛₗ ℝ
 turns x y:= real_inner_comm y x
 slope:= ⟨2⁻¹,by norm_num,fun x=> (le_of_eq ( by change _=inner ℝ x x/2; rw [real_inner_self_eq_norm_sq]; ring))⟩
 smooth:= continuous_id.inner continuous_id
-- can of course use other geometry to get diagonal shell formulas
variable (n) in
def replica : Law (Root G n):= focusWith (reserve (Module.finrank ℝ ( Root G n ))) toEuclidean.toLinearEquiv.toLinearMap toEuclidean.injective

variable {G} (Y:XSpace.Initialize G) (L:Scent G n) (z:Law (Root G n))
    (μ:Measure (Rep G n))[μ.IsAddHaarMeasure]
include ev in
/-- Applies to ANY list of the tilted mark stencils, at exactly its required Laurent valuation. -/
theorem here (v:List (Arrival.Folio G)): PowerSeries.X^(Folio.asset v)*Folio.coefficients Y n v= check L z μ ( Folio.scenario Y n v ):= by rw [grams _ _ ev (Folio.matured Y n v ev),Folio.external Y v ev ]
end YM.FVA2.Feyn.Scent
