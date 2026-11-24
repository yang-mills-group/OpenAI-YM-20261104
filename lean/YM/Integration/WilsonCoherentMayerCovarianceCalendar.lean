import YM.Integration.WilsonReportingDecoratedStage
import YM.Integration.WilsonRootedJointCalendar

/-! Before a reporting run chooses a period or a physical conductor, buy the
actual decorated moment for every order up to the already appointed stage. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerCovarianceCalendar
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Port RGLocalTaylor RGLocalTaylor.Insert RGLocalTaylor.Mayer
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Daisy.Charity.RG12
open WilsonRetainedMiniatureTaylor WilsonRetainedDecoratedWord
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

/-- The book and original block determine this standard deviation before any finite
forest, regulator, marked source, or local integration variable is selected. -/
def deviation (G:Gauge) (L:Side) {W:ℝ} (o:Target.Order G W):ℝ:=
  Real.sqrt (Window.payE o.eta o.gap o.ample (Census.tubularPrice G L))

def decal (G:Gauge):Decal G where
  rub _ _ _ L _ _ o _ _ x:=deviation G L o≤1+Real.log (betaF G x L)
  good _ _ _:=by
    refine ⟨0,fun L _ W _ o _ _ _ _ _=>?_⟩
    filter_upwards [(Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L)).eventually_ge_atTop (deviation G L o)] with x hx
    change deviation G L o≤Real.log (betaF G x L) at hx
    linarith

end YM.Integration.WilsonCoherentMayerCovarianceCalendar
