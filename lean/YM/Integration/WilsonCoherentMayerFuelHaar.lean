import YM.Integration.WilsonCoherentMayerFuelSector
import YM.Integration.WilsonPositionSeparatedProfileMayerFlat

/-! The original auxiliary tree Haar variable does not alter the chosen
quadratic or its two genuine cutoffs on the blank, healthy chamber. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerFuelHaar
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




open LocalTaylorR2.Exponent WilsonCoherentMayerFuelGate

open WilsonCoherentMayerFuelPolynomial

private theorem mean (fund:P.Funds S T) (Z:Coat T F):voltage Z.blank=0:=by
  have start:timeΛ Z 0=Z.blank:=by
    unfold timeΛ Vine.pass dry
    simp only [Prod.snd_zero,Work.G07.at_zero_increment]
    rfl
  exact start ▸ LocalLTE.Fan.volt0 Z fund

theorem sampled (H:Cash W s μ L Q o C T R) (X:Coat T F) (hx:X.x=s)
    (flat:X.blank=X) (manifest:X.manifest) (y:F.Slice G) (z:Air f G) (q:Ledger f 2):
    Mayer.exponent H (X.wrapY y) z (label (S:=S) q)= Mayer.exponent H X z (label q):=by
  let Z:=X.wrapY y
  have zm:Z.manifest:=manifest
  have same:Z.blank=Z:=show X.blank.wrapY y=X.wrapY y from congrArg (fun A:Coat T F=>A.wrapY y) flat
  have funds:=H.laws.data.funds.funds
  have μX:=mean funds X
  have μZ:=mean funds Z
  rw [flat] at μX
  rw [same] at μZ
  have room:Room P S T X.x:=hx.symm ▸ H.laws.data.room
  have wire:(Z.liftA R.beta z)=X.liftA R.beta z:=by
    rw [shine Z room zm,shine X room manifest]
    simp only [worldZ,μX,μZ,zero_add]
    rfl
  have aperture(e:Bond f):Z.aperture R.beta z o.a e=X.aperture R.beta z o.a e:=by
    unfold Coat.aperture
    rw [wire]
    rfl
  change Z.chain R.beta z o.a q=X.chain R.beta z o.a q
  simp only [Coat.chain,aperture]
  rfl

end YM.Integration.WilsonCoherentMayerFuelHaar
