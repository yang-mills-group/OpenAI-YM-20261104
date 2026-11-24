import YM.FormalOPE.RG10.MarkovChain.Journey
/-!
 # Multi-step local mark projection.  Gauge convention explicit.
 Courses per transition may supply extra operator marks in Both adjacent variable windows;
 no requirement that they all come priced, dollar signs or disjoint subsets. This describes
 the ordinary coefficient algorithm. Support restrictions for physical OPE still not here. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
namespace Router
variable {L:Fabric G n}(T:Cloth L) (w:L.Accounts→PowerSeries ℝ) (hw:∀ i,0<term (w i) 0){P:ChartRatio G}(H:LocalRatio P)
local notation "Ξ"=> model L T.choose w

-- family of mixed operators living both on layers & parent-child links (not genuine footprint cost).
include H in
theorem anyPanel (J:Sack T)(A:Panel T): journey T (evidence _ (enough L T.choose w hw).entire) J A (weight P Ξ)= enjoy (evidence _ (enough L T.choose w hw).entire) (tangent G T.choose.Bulk) (transmit T A * gauged T J) (weight P Ξ):= by rw [completes T _ J A (Actual.credible T w hw) (Library.weightSaved w hw H) (checked_up H), recorded T _ _ _ (checked_up H)]
lemma observed {O:Wilson.Config G n→ℝ}(h:Orb.PreTest O): Present T (imbed (attending L O ∘ T.choose.board)):= by
 intro x y hu; apply PowerSeries.ext; intro i
 let a:= (attending L O ∘ T.choose.board) ∘ expLinks G T.choose.Bulk
 have he:(fun s:ℝ=> a (s • x))=fun s:ℝ=>a (s • y):= funext fun r=> by simp only [a,attending, comp_apply, Line.portrayed, map_smul,hu]
 have hv: ContDiffAt ℝ ∞ a 0:= ((eligible L h).passes _ _).germ
 change coeff i (Stack.read x (rise a))=coeff i (Stack.read y (rise a)); rw [read_rise,read_rise]
 have hp:= directions hv x; rw [he] at hp; exact congr_fun (hp.unique (directions hv y)) _

include H
theorem root_projection (ht:w none=1){O:Wilson.Config G n→ℝ}(h:Orb.PreTest O): journey T (evidence _ (enough L T.choose w hw).entire) (blank T) (toRow T (imbed (attending L O∘ T.choose.board))) (weight P Ξ)= PowerSeries.mk (Orb.diag (Orb.restrictedO O)):= by
 rw [completes T _ _ _ (Actual.credible T w hw) (Library.weightSaved w hw H) (checked_up H),available T (observed T h), nominal, mul_one]; exact top_projection T w H hw ht h
end Router
end YM.FormalOPE.RG10.MarkovChain
