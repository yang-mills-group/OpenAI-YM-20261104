import YM.Integration.WilsonCoherentMayerRootPlaquette
import YM.Integration.WilsonCoherentMayerRootTariff
import YM.Integration.WilsonRetainedJointVertexFiling

/-! The first live radial coefficient of a complete rooted old atom has an
absolute polynomial cost independent of its path length and the torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerRootKernel
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

open WilsonCoherentMayerRootPlaquette WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open private atomReal from YM.Integration.WilsonRetainedJointVertexFiling
variable {h:ℕ}

def variableAt (s:Signed)(u:Woods G f):Normal.poly (Eye X):=turn X s (u.1,axisEquiv.symm u.2.1) u.2.2

private theorem evaluate (s:Signed)(u:Woods G f)(z:Air f G):
    Cloud.paint (fun i=>z (tube X i)) (variableAt X s u)=Complex.ofReal ((cloth G f) (pulled (angularSample F z) s) u):=by
  rw [variableAt,turn_read]
  have back:coord (axisEquiv.symm u.2.1)=u.2.1:=axisEquiv.apply_symm_apply _
  rw [back]
  rfl

def written (a:Atom G h)(x:Site f)(s:Signed)(j:ℕ):Normal.poly (Eye X):=
  ∑ u:Fin j→Woods G f,MvPolynomial.C (Complex.ofReal (rye (meter a x) j u))*∏ i,variableAt X s (u i)

theorem material (a:Atom G h)(x:Site f)(s:Signed)(j:ℕ)(z:Air f G):
    Cloud.paint (fun i=>z (tube X i)) (written X a x s j)=
      Complex.ofReal (MvPolynomial.eval ((cloth G f) (pulled (angularSample F z) s)) (PowerSeries.coeff j (Blue.jet (meter a x)))):=by
  rw [Blue.jet_apply]
  change _=Complex.ofReal (MvPolynomial.eval _ (∑ u:Fin j→Woods G f, (rye (meter a x) j u) • ∏ i,MvPolynomial.X (u i)))
  simp only [written,map_sum,map_mul,map_prod,evaluate,Cloud.paint,MvPolynomial.aeval_C,MvPolynomial.smul_eq_C_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]
  rfl

theorem coefficient (a:Atom G h)(x:Site f)(j:ℕ)(y:Dir G f):
    MvPolynomial.eval ((cloth G f) y) (PowerSeries.coeff j (Blue.jet (meter a x)))=
      CubicMatch.term j (fun t:ℝ=>a.unmasked (represent (t • y)) x):=by
  rw [Blue.rayon]
  have ray:=PertExtension.Series.Radial.homogeneous_derivative (meter a x) ((cloth G f) y) j ((meter_hot a x).contDiffAt.of_le le_top)
  have physical (t:ℝ):meter a x (t • (cloth G f) y)=a.unmasked (represent (t • y)) x:=by
    unfold WilsonCoeffUV.Bank.Mosaic.Near.meter
    rw [WilsonCoeffUV.Bank.Mosaic.mantle_input]
    unfold WilsonCoeffUV.mantle
    rw [map_smul,ContinuousLinearEquiv.symm_apply_apply]
  simp_rw [physical] at ray
  exact ray

theorem radial (a:Atom G h)(x:Site f)(s:Signed)(z:Air f G)(q:ℕ)(g:ℝ):
    FundedCurvatureRayTaylor.polynomial a x (collect G (pulled (angularSample F z) s)) q g=
      ∑ j ∈ range (q+1),(g:ℂ)^j * Cloud.paint (fun i=>z (tube X i)) (written X a x s j):=by
  rw [atomReal,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [material,coefficient,Complex.ofReal_mul,Complex.ofReal_pow]

theorem degree (a:Atom G h)(x:Site f)(s:Signed)(j:ℕ):(written X a x s j).totalDegree≤j:=by
  unfold written;apply MvPolynomial.totalDegree_finsetSum_le;intro u _
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [MvPolynomial.totalDegree_C,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd ..).trans
  exact (Finset.sum_le_sum (fun i _=>(turn_pay X s ((u i).1,axisEquiv.symm (u i).2.1) (u i).2.2).2)).trans_eq (by simp)

theorem financed (a:Atom G h){σ:ℝ}(hs:0<σ)(x:Site f)(s:Signed)(j:ℕ):
    Rise.coin (written X a x s j)≤a.budget σ*WilsonCoherentMayerRootTariff.price G σ h j:=by
  unfold written;apply (Rise.collect 0 zero_le_one _ _).trans
  apply (Finset.sum_le_sum (fun u _=>?_)).trans (WilsonCoherentMayerRootTariff.coefficients a hs x j)
  apply (Rise.funds 0 zero_le_one _ _).trans
  rw [Rise.pay_C,Complex.norm_real]
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply (Rise.purchased 0 zero_le_one _ _).trans
  exact Finset.prod_le_one (fun i _=>Rise.sign 0 _ zero_le_one) (fun i _=>(turn_pay X s ((u i).1,axisEquiv.symm (u i).2.1) (u i).2.2).1)

end YM.Integration.WilsonCoherentMayerRootKernel
