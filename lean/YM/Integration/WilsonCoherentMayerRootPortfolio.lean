import YM.Integration.WilsonCoherentMayerRootKernel
import YM.Integration.WilsonCoherentMayerRootWriting

/-! A spatially rooted old action polynomial including every previous registered
path and its signed orientation average, at any angular grade. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerRootPortfolio
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

variable (X:Coat T F)


open WilsonCoherentMayerFuelPolynomial (coordinate read_coordinate)
open OriginalMarkedRunAction WilsonCoherentMayerNoise Work.F03 Bid

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoherentMayerRootWriting
variable {h:ℕ}{σ D:ℝ}

def deposit (A:ℕ→Atom G h)(x:Site f)(j:ℕ):Normal.poly (Eye X):=
  blended j (fun s i=>WilsonCoherentMayerRootKernel.written X (A i) x s j)

theorem original (A:ℕ→Atom G h)(hs:0<σ)(paid:SumBudget (fun i=>(A i).budget σ) D)(x:Site f)(j:ℕ):
    (deposit X A x j).totalDegree≤j ∧ Rise.coin (deposit X A x j)≤D*WilsonCoherentMayerRootTariff.price G σ h j ∧
    ∀z:Air f G,Cloud.paint (fun e=>z (tube X e)) (deposit X A x j)=
      Complex.ofReal (CubicMatch.term j (fun t:ℝ=>sitePacket A x (represent (t • angularSample F z)))):=by
  have fee:0≤WilsonCoherentMayerRootTariff.price G σ h j:=by
    cases j with
    | zero=>exact Bank.Mosaic.Near.flour_nn ..
    | succ j=>exact mul_nonneg (Bank.Mosaic.Near.flour_nn ..) (pow_nonneg (Bank.boardPay_nn (α:=Hooks G) (show 0<(σ/2)/(j+1) by positivity)) _)
  have h:=WilsonCoherentMayerRootWriting.original j (fun s i=>WilsonCoherentMayerRootKernel.written X (A i) x s j)
    (fun s i=>WilsonCoherentMayerRootKernel.degree X (A i) x s j) (fun s=>income paid fee _ (fun i=>WilsonCoherentMayerRootKernel.financed X (A i) hs x s j))
  refine ⟨h.1,h.2.1,?_⟩
  intro z
  rw [site_coefficient A hs paid x (angularSample F z) j]
  unfold deposit
  change MvPolynomial.aeval (fun e=>(z (tube X e):ℂ)) _=_
  rw [h.2.2]
  have read (s:Signed)(i:ℕ):MvPolynomial.aeval (fun e=>(z (tube X e):ℂ)) (WilsonCoherentMayerRootKernel.written X (A i) x s j)=
      Complex.ofReal (CubicMatch.term j (fun t:ℝ=>(A i).unmasked (represent (t • pulled (angularSample F z) s)) x)):=
    (WilsonCoherentMayerRootKernel.material X (A i) x s j z).trans (congrArg Complex.ofReal (WilsonCoherentMayerRootKernel.coefficient (A i) x j _))
  simp_rw [read]
  unfold Patch.average
  push_cast
  rfl

theorem measured (A:ℕ→Atom G h)(hs:0<σ)(paid:SumBudget (fun i=>(A i).budget σ) D)
    (x:Site f)(q:ℕ)(g:ℝ)(z:Air f G):
    siteTaylor A x (angularSample F z) q g=
      ∑ j ∈ range (q+1),(g:ℂ)^j*Cloud.paint (fun e=>z (tube X e)) (deposit X A x j):=by
  rw [OriginalMarkedRunAction.site_jet A hs paid x (angularSample F z) q g,Complex.ofReal_sum]
  apply Finset.sum_congr rfl;intro j _
  rw [(original X A hs paid x j).2.2 z,Complex.ofReal_mul,Complex.ofReal_pow]

end YM.Integration.WilsonCoherentMayerRootPortfolio
