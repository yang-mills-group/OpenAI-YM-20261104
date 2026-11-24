import YM.Integration.WilsonPositionSeparatedProfileMayerFlat
import YM.Integration.WilsonCoherentMayerSignedCharge
import YM.Comparison.RG02.Assembly.Kernel

/-! The angular panel of the genuine registered Wilson words depends on
the independently commissioned free coordinates of the flat coat. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerWickInputs
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
variable (X:Coat T F)

private def pack (a:Eye X→ℝ):Air f G:=WithLp.toLp 2 fun t:Tubular f G=>
  if h:t.1∈F.trunks then 0 else a (Native.lineEquiv (G:=G) F X.x (⟨t.1,h⟩,t.2))

def lift:(Eye X→ℝ)→ₗ[ℝ]Air f G where
  toFun:=pack X
  map_add' a b:=by
    apply PiLp.ext;intro t;by_cases ht:t.1∈F.trunks <;> simp [pack,ht]
  map_smul' a b:=by
    apply PiLp.ext;intro t;by_cases ht:t.1∈F.trunks <;> simp [pack,ht]

theorem fields (z:Air f G):WilsonCoherentMayerNoise.row F (lift X (fun i=>z (tube X i)))=WilsonCoherentMayerNoise.row F z:=by
  funext e;by_cases he:e∈F.trunks
  · simp [WilsonCoherentMayerNoise.row,he]
  · simp only [WilsonCoherentMayerNoise.row,he,↓reduceIte]
    apply PiLp.ext;intro i
    change (if h:e∈F.trunks then 0 else z (tube X (Native.lineEquiv (G:=G) F X.x (⟨e,h⟩,i))))=z (e,i)
    rw [dif_neg he];rfl

variable (run:Run G) {I:Type} [Fintype I] (d:I→ℕ) (o:I→Site f)

def panel : (Eye X→ℝ)→ₗ[ℝ] Panels run d :=(restrict run d F o).toLinearMap.comp (lift X)

omit [Fintype I] in
theorem original (z:Air f G):panel X run d o (fun i=>z (tube X i))=restrict run d F o z:=by
  let project (a:Directions G f):Panels run d:=fun i=>Dict06.Wil.restrictLog (run.family.localSection (d i)).stencil (expandAt (o i) a)
  exact congrArg project (fields X z)

end YM.Integration.WilsonPositionSeparatedProfileMayerWickInputs
