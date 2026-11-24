import YM.Integration.WilsonCoherentMayerFuelSquare
import YM.Integration.WilsonCoherentMayerFuelTariff

/-! Deleting the two physical taper factors under the same charged Gaussian
uses only the measured warning at the genuine two endpoints. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerFuelRemoval
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

theorem borel (q:Ledger f 2) (β a:ℝ) (k:ℕ):Measurable (weight X q β a k):=by
  have tangent:Measurable (fun z:Air f G=>X.atmos z):=measurable_pi_lambda _ fun i=>(X.tale i).measurable
  have aperture (i:Bond f):Measurable (fun z:Air f G=>X.aperture β z a i):=by
    unfold Coat.aperture;split_ifs
    · apply (X.cone_b i _).comp
      exact measurable_const.add (tangent.const_smul (Coat.gStep β))
    · exact measurable_const
  exact ((aperture q.2.1).mul (aperture (arrive q.2.1 q.2.2))).pow_const k

theorem second (H:Cash W X.x μ L Q o C T R) (fitted:X.width=o.K) (manifest:X.manifest)
    (q:Ledger f 2) (k:ℕ) (B:Normal.poly (Eye X)) (d:ℕ) (deg:B.totalDegree≤d):
    ‖(∫z:Air f G,(weight X q R.beta o.a k z:ℂ)*Cloud.paint (fun i=>z (tube X i)) B ∂X.dice)-
      ∫z:Air f G,Cloud.paint (fun i=>z (tube X i)) B ∂X.dice‖ ≤
      Rise.coin B * (Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L)) (2*d)) *
      Real.sqrt (X.dice.real (eerie X (sites (S:=S) q) o.ξ R.beta))) := by
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl fitted manifest
  let read:=fun z:Air f G=>Cloud.paint (fun i=>z (tube X i)) B
  let g:=weight X q R.beta o.a k
  let D:=eerie X (sites (S:=S) q) o.ξ R.beta
  let fiscal:=Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L)) (2*d)
  have paid:0≤fiscal:=by
    have hr:0≤1+payE o.eta o.gap o.ample (tubularPrice G L):=by linarith [A.scale.disc]
    dsimp [fiscal,Common.priced];positivity
  have pos:0≤Rise.coin B:=by rw [Rise.metal];positivity
  have hread:Integrable read X.dice:=(WilsonCoherentMayerFuelSquare.sampled X A.fullC B).1
  have hh:=WilsonCoherentMayerFuelSquare.second X A B d deg
  have hD:MeasurableSet D:=measurable_eerie ..
  have hg:Measurable g:=borel X q R.beta o.a k
  have hrange (z):0≤g z ∧ g z≤1:=WilsonCoherentMayerFuelGate.range .. 
  have product:Integrable (fun z=>(g z:ℂ)*read z) X.dice:=by
    apply hread.norm.mono' ((Complex.continuous_ofReal.measurable.comp hg).aestronglyMeasurable.mul hread.aestronglyMeasurable)
    filter_upwards with z
    change ‖(g z:ℂ)*read z‖ ≤ ‖read z‖
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hrange z).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hrange z).2
  change ‖(∫z,(g z:ℂ)*read z ∂X.dice)- ∫z,read z ∂X.dice‖≤_
  rw [←integral_sub product hread]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫z,D.indicator (fun y=>‖read y‖) z ∂X.dice:=by
      apply integral_mono (product.sub hread).norm (hread.norm.indicator hD)
      intro z
      change ‖(g z:ℂ)*read z-read z‖≤D.indicator (fun y=>‖read y‖) z
      by_cases h:z∈D
      · rw [Set.indicator_of_mem h,←sub_one_mul,norm_mul]
        have realnorm: ‖(g z:ℂ)-1‖=1-g z:=by
          rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith [(hrange z).2])];ring
        rw [realnorm];exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hrange z).1])
      · have same:g z=1:=live X H fitted manifest q k z h
        simp [Set.indicator_of_notMem h,same]
    _ ≤ (Rise.coin B*Real.sqrt fiscal)*Real.sqrt (X.dice.real D):=by
      apply divideC X.dice (fun z=>‖read z‖) hread.norm _ (mul_nonneg pos (Real.sqrt_nonneg _)) D hD
        (le_of_eq (Real.sq_sqrt measureReal_nonneg).symm) (Real.sqrt_nonneg _) hh.1
      rw [mul_pow,Real.sq_sqrt paid];exact hh.2
    _ = _:=mul_assoc .. 

end YM.Integration.WilsonCoherentMayerFuelRemoval
