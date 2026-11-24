import YM.Integration.WilsonCoherentMayerFuelReport
import YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn

/-! The angular warning on the whole original enrolled marked stencil against a
repeated covariance term, with the old nonlinear signed team on the same sample. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerSectorWarning
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
variable (X:Coat T F)


theorem measured {η r K Y:ℝ} (A:Rotator P L η r K Y X) (B:Normal.poly (Eye X)) (d:ℕ) (degree:B.totalDegree≤d)
    (D:Set (Air f G)) (hD:MeasurableSet D) (W:momentSpace X→ℝ) (mW:Measurable W) {b:ℝ} (hb:0≤b)
    (bound:∀z,|W z|≤b) (support:∀z:momentSpace X,z.2∉D→W z=0):
    let element:=fun z:momentSpace X=>(W z:ℂ)*Cloud.paint (fun i=>z.2 (tube X i)) B
    Integrable element (moment X) ∧ (∫z,‖element z‖ ∂moment X)≤
      b*((Rise.coin B*Real.sqrt (Common.priced (1+payE η r K (tubularPrice G L)) (2*d)))*Real.sqrt (X.dice.real D)):=by
  let read (z:Air f G):=Cloud.paint (fun a=>z (tube X a)) B
  let fiscal:=Common.priced (1+payE η r K (tubularPrice G L)) (2*d)
  have non:0≤fiscal:=by
    have base:0≤1+payE η r K (tubularPrice G L):=by linarith [A.scale.disc]
    unfold fiscal Common.priced;positivity
  have coin:0≤Rise.coin B:=by rw [Rise.metal];positivity
  have readInt:Integrable read X.dice:=(WilsonCoherentMayerFuelSquare.sampled X A.fullC B).1
  have readOn:Integrable (D.indicator (fun z=>‖read z‖)) X.dice:=readInt.norm.indicator hD
  have cap:Integrable (fun z:momentSpace X=>b*D.indicator (fun z=>‖read z‖) z.2) (moment X):=(readOn.comp_snd (F.order G)).const_mul b
  have point (z:momentSpace X):‖(W z:ℂ)*read z.2‖≤b*D.indicator (fun z=>‖read z‖) z.2:=by
    by_cases h:z.2∈D
    · rw [Set.indicator_of_mem h,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (bound z) (norm_nonneg _)
    · rw [Set.indicator_of_notMem h,support z h];simp
  have hi:Integrable (fun z:momentSpace X=>(W z:ℂ)*read z.2) (moment X):=by
    apply cap.mono' _ (ae_of_all _ point)
    exact (Complex.continuous_ofReal.measurable.comp mW).aestronglyMeasurable.mul (readInt.comp_snd (F.order G)).aestronglyMeasurable
  refine ⟨hi,(integral_mono hi.norm cap point).trans ?_⟩
  change (∫z:momentSpace X,b*D.indicator (fun z=>‖read z‖) z.2 ∂((F.order G).prod X.dice)) ≤ _
  rw [integral_const_mul,integral_fun_snd]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  apply mul_le_mul_of_nonneg_left _ hb
  have hh:=WilsonCoherentMayerFuelSquare.second X A B d degree
  apply divideC X.dice (fun z=>‖read z‖) readInt.norm _ (mul_nonneg coin (Real.sqrt_nonneg _)) D hD
    (le_of_eq (Real.sq_sqrt measureReal_nonneg).symm) (Real.sqrt_nonneg _) hh.1
  rw [mul_pow,Real.sq_sqrt non];exact hh.2

end YM.Integration.WilsonCoherentMayerSectorWarning
