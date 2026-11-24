import YM.Integration.WilsonCoherentMayerFuelSquare
import YM.Integration.WilsonRetainedStencilMoment

/-! Hölder on the original joint Gaussian, using only the finite set of
coordinates of the booked compact-group source and the actual old polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerMixedMoment
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


open WilsonRetainedStencilMoment ProbabilityTheory
attribute [local instance] Gauge.frobInner
variable (run:Run G) {I:Type} [Fintype I] (ds:I→ℕ)
def panel (deviation:ℝ) (n:ℕ):ℝ:=
  ‖restore run ds‖^n*((Fintype.card (Keys run ds):ℝ)*(deviation^n*unitMoment n))

theorem original {η r K Y:ℝ} (X:Coat T F) (A:Rotator P L η r K Y X)
    (loc:I→Site f) (B:Normal.poly (Eye X)) (d n:ℕ) (hd:B.totalDegree≤d) :
    let read:=fun z:Air f G=>‖Cloud.paint (fun i=>z (tube X i)) B‖
    let radial:=fun z:Air f G=>‖restrict run ds F loc z‖^(n+1)
    let gross:=fun z:Air f G=>read z*radial z
    Integrable gross X.dice ∧ (∫z,gross z ∂X.dice)≤
      (Rise.coin B*Real.sqrt (Common.priced (1+payE η r K (tubularPrice G L)) (2*d)))*
        Real.sqrt (panel run ds (Real.sqrt (payE η r K (tubularPrice G L))) (2*(n+1))) := by
  intro read radial gross
  haveI:IsGaussian X.dice:=inferInstanceAs (IsGaussian (multivariateGaussian 0 X.relating))
  let aperture:=restrict run ds F loc
  have hr := WilsonCoherentMayerFuelSquare.sampled X A.fullC B
  have hc := WilsonCoherentMayerFuelSquare.second X A B d hd
  have first:MemLp read 2 X.dice := (memLp_two_iff_integrable_sq hr.1.norm.aestronglyMeasurable).2 hc.1
  have second:MemLp radial 2 X.dice := by
    apply (memLp_two_iff_integrable_sq (by dsimp [radial];fun_prop)).2
    have measured:Integrable (fun z:Air f G=>‖aperture z‖^(2*(n+1))) X.dice:=by
      have hi:Integrable (fun v:Panels run ds=>‖v‖^(2*(n+1))) (X.dice.map aperture):=
        MemLp.integrable_norm_pow' (p:=2*(n+1)) (f:=id) (IsGaussian.memLp_id (X.dice.map aperture) (2*(n+1):ℕ) (ENNReal.natCast_ne_top _))
      exact (integrable_map_measure (by fun_prop) aperture.continuous.aemeasurable).mp hi
    simpa only [radial,←pow_mul,mul_comm (n+1) 2] using measured
  refine ⟨first.integrable_mul second,?_⟩
  have twice:ENNReal.ofReal 2=2:=by norm_num
  have hold:=integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (show (0:Air f G→ℝ)≤ᵐ[X.dice] read from ae_of_all _ fun _=>norm_nonneg _)
    (show (0:Air f G→ℝ)≤ᵐ[X.dice] radial from ae_of_all _ fun z=>pow_nonneg (norm_nonneg _) _) (by rwa [twice]) (by rwa [twice])
  have hs:(∫z,gross z ∂X.dice)≤Real.sqrt (∫z,read z^2 ∂X.dice)*Real.sqrt (∫z,radial z^2 ∂X.dice):=by
    simpa [Real.rpow_two,Real.sqrt_eq_rpow,gross] using hold
  have support:=WilsonRetainedStencilMoment.purchased run ds F loc A (2*n+1)
  have even:(∫z,radial z^2 ∂X.dice)≤panel run ds (Real.sqrt (payE η r K (tubularPrice G L))) (2*(n+1)):=by
    have eq:2*n+1+1=2*(n+1):=by omega
    simpa only [eq,radial,←pow_mul,mul_comm (n+1) 2,panel] using support
  apply hs.trans
  have hcoin:0≤Rise.coin B:=by rw [Rise.metal];positivity
  have pencil:=Real.sqrt_le_sqrt hc.2
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hcoin] at pencil
  exact mul_le_mul pencil (Real.sqrt_le_sqrt even) (Real.sqrt_nonneg _)
    (mul_nonneg hcoin (Real.sqrt_nonneg _))

end YM.Integration.WilsonCoherentMayerMixedMoment
