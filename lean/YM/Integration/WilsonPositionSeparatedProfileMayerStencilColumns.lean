import YM.Integration.WilsonPositionSeparatedProfileMayerStencilSites

/-! Signed basis coefficients on the fixed local stencil of the submitted registered fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerStencilColumns
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonPositionSeparatedProfileMayerWickInputs WilsonRetainedSignedStencilTaylor
open WilsonCoherentMayerHearing Dict06.Series
open WilsonPositionSeparatedProfileMayerStencilSites WilsonRetainedSignedStencilBasis
variable {I:Type} [Fintype I] (run:Run G) (d:I→ℕ)
abbrev Mark:=WilsonRetainedStencilMass.Index run d × (I→Bool)
def cell (v:Mark run d) (j:ℕ):Normal.poly (Letter run d):=kernelJet (0:Panels run d) (slots run d)
  (material run d (part ∘ v.2) (WilsonRetainedStencilMass.basis run d v.1)) j

theorem component (a:Letter run d→ℝ) (v:Mark run d) (j:ℕ):Cloud.paint a (cell run d v j)=
    ordinary j (fun t:ℝ=>material run d (part ∘ v.2) (WilsonRetainedStencilMass.basis run d v.1) (t•slots run d a)):=by
  unfold cell;rw [Comparison.RG02.Assembly.reading,Comparison.RG02.Assembly.translate,zero_add]
  exact (Dict06.Series.radial_eq j ((smooth run d (part ∘ v.2) (WilsonRetainedStencilMass.basis run d v.1)).contDiffAt.of_le le_top) _).symm

theorem bound (v:Mark run d) (j:ℕ):(cell run d v j).totalDegree≤j:=by
  unfold cell kernelJet wordL
  apply MvPolynomial.totalDegree_finsetSum_le;intro z _
  apply (MvPolynomial.totalDegree_mul _ _).trans;rw [MvPolynomial.totalDegree_C,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  calc _≤∑ _ : Fin j,1:=by
          apply Finset.sum_le_sum;intro a _
          change ((z a).elim (1:Normal.poly (Letter run d)) MvPolynomial.X).totalDegree≤1
          cases z a <;> simp
       _=j:=by simp

variable (φ:I→Reading) (θ:ℝ) (y:∀i,run.family.label (d i))
def debit (v:Mark run d):ℂ:=coefficient run d φ (fun i=>(run.family.labels.level (d i)).scaled θ⁻¹ (y i)) v.1 v.2

def registered (j:ℕ):Normal.poly (Letter run d):=∑v:Mark run d,MvPolynomial.C (debit run d φ θ y v)*cell run d v j

theorem order (j:ℕ):(registered run d φ θ y j).totalDegree≤j:=by
  apply MvPolynomial.totalDegree_finsetSum_le;intro v _
  apply (MvPolynomial.totalDegree_mul _ _).trans;rw [MvPolynomial.totalDegree_C,zero_add];exact bound run d v j

theorem observed (X:Coat T F) (loc:I→Site f) (z:Air f G) (j:ℕ):
    Cloud.paint (fun i=>z (tube X i)) (Normal.exchange (wires (filed run d X loc)) (registered run d φ θ y j))=
      (PowerSeries.coeff j (WilsonRetainedSignedStencilBooks.books run d F loc φ θ y z):ℝ):=by
  let a:=WilsonCoherentMayerProjection.restrict run d F loc z
  let mark (v:Mark run d) (t:ℝ):=material run d (part ∘ v.2) (WilsonRetainedStencilMass.basis run d v.1) (t•a)
  let c:=debit run d φ θ y
  have sm (v:Mark run d):ContDiffAt ℝ ω (mark v) 0:=((smooth run d (part ∘ v.2) (WilsonRetainedStencilMass.basis run d v.1)).comp (contDiff_id.smul contDiff_const)).contDiffAt
  have expand:(fun t:ℝ=>material run d φ (fun i=>(run.family.labels.level (d i)).scaled θ⁻¹ (y i)) (t•a)) =
      (fun t=>∑v:Mark run d,c v*mark v t):=by funext t;rw [Fintype.sum_prod_type];exact expanded run d φ _ _
  rw [WilsonPositionSeparatedProfileMayerStencilSites.read,←WilsonRetainedSignedStencilBooks.graded run d F loc φ θ y z j]
  change (Cloud.paint _) (registered run d φ θ y j)=ordinary j (fun t:ℝ=>material run d φ (fun i=>(run.family.labels.level (d i)).scaled θ⁻¹ (y i)) (t•a))
  rw [expand,ordinary_sum univ (fun v t=>c v*mark v t) j (fun v _=>contDiffAt_const.mul ((sm v).of_le le_top)),registered,map_sum]
  apply Finset.sum_congr rfl;intro v _
  rw [map_mul,component,placed]
  have pull:ordinary j (fun t=>c v*mark v t)=c v*ordinary j (mark v):=by
    let L:ℂ→L[ℝ]ℂ:=c v • ContinuousLinearMap.id ℝ ℂ
    exact ordinary_map (mark v) j ((sm v).of_le le_top) L
  rw [pull];simp only [Cloud.paint,MvPolynomial.aeval_C];rfl

end YM.Integration.WilsonPositionSeparatedProfileMayerStencilColumns
