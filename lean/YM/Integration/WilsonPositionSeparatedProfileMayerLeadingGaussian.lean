import YM.Integration.WilsonPositionSeparatedProfileMayerStencilPrice
import YM.Integration.WilsonPositionSeparatedProfileMayerLeadingTaylor

/-! The Gaussian numerical read on every genuine forest and tag, including
the measured coefficient budget before the choice of finite volume. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerLeadingGaussian
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

open WilsonPositionSeparatedProfileMayerMasks WilsonPositionSeparatedProfileMayerGateReturn
open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences WilsonCoherentMayerHearing
open WilsonPositionSeparatedProfileMayerGateSafety LocalTaylorR2.Exponent
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Comparison.RG02.Cumulants WilsonPositionSeparatedProfileMayerStencilPrice
variable {run:Run G} {I:Type} [Fintype I] (entry:Submitted run R I)

def branch (T:Tube G S) (s:ℝ) (o:Target.Order G W) (χ:Chi) (t:ℕ) (i:Greenbelt.Reserve S) (tag:S.Choices):ℂ:=
  let F:=Greenbelt.allot i
  let X:=chamber T s o.K χ 1 ∅ i tag
  let word:=deposited run entry.grade entry.phase R.p.threshold entry.label (Coat.gStep R.beta) t X entry.site
  Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s) (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 word

def forecast (T:Tube G S) (s:ℝ) (o:Target.Order G W) (χ:Chi) (t:ℕ):ℝ:=
  likely fun i:Greenbelt.Reserve S=>likely fun tag:S.Choices=>(branch entry T s o χ t i tag).re

theorem measured (H:Cash W s μ L Q o C T R) (temp:0≤Pressure.temp s) (cap:∀i z,|entry.phase i z|≤‖z‖) (hg:|Coat.gStep R.beta|≤1)
    (old:Team R) (vacant:old.own=∅) (χ:Chi) (t:ℕ) (i:Greenbelt.Reserve S) (tag:S.Choices):
    let X:=chamber T s o.K χ 1 ∅ i tag
    |(∫z,WilsonPositionSeparatedProfileMayerLeadingTaylor.printed old o.a X run entry t z ∂Insert.moment X)-(branch entry T s o χ t i tag).re|≤
    WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label*budget run entry.grade t*|WilsonOriginalSignedSamplerMoment.fee T L P o t s|:=by
  intro X
  let F:=Greenbelt.allot i
  let word:=deposited run entry.grade entry.phase R.p.threshold entry.label (Coat.gStep R.beta) t X entry.site
  let amount:=WilsonCoherentMayerSignedCharge.polynomial run entry.grade (F:=F) entry.site entry.phase R.p.threshold (Coat.gStep R.beta) entry.label t
  have paid:=WilsonOriginalSignedSamplerMoment.original T H temp χ ∅ i tag word t (degree run entry.grade entry.phase R.p.threshold entry.label (Coat.gStep R.beta) t X entry.site)
  have printed:(∫z:Air f G,(amount z:ℂ) ∂X.dice)=∫z:Air f G,Cloud.paint (fun u=>z (tube X u)) word ∂X.dice:=by
    apply integral_congr_ae;filter_upwards with z
    exact (WilsonPositionSeparatedProfileMayerStencilPrice.printed run entry.grade entry.phase R.p.threshold entry.label (Coat.gStep R.beta) t X entry.site z).symm
  have bill:=preperiod run entry.grade entry.phase R.p.threshold entry.label cap (Coat.gStep R.beta) hg t X entry.site
  have gross:‖Complex.ofReal (∫z:Air f G,amount z ∂X.dice)-branch entry T s o χ t i tag‖≤Next.Rank.Rise.coin word*WilsonOriginalSignedSamplerMoment.fee T L P o t s:=by
    rw [←integral_complex_ofReal,printed];exact paid
  have total:=((Complex.abs_re_le_norm _).trans gross).trans ((mul_le_mul_of_nonneg_left (le_abs_self _) (Next.Rank.Rise.sign 0 word zero_le_one)).trans (mul_le_mul_of_nonneg_right bill (abs_nonneg _)))
  have erase:(∫z,WilsonPositionSeparatedProfileMayerLeadingTaylor.printed old o.a X run entry t z ∂Insert.moment X)=∫z:Air f G,amount z ∂X.dice:=by
    simp only [WilsonPositionSeparatedProfileMayerLeadingTaylor.printed,WilsonPositionSeparatedProfileMayerLeadingTaylor.prior,vacant,Finset.prod_empty,one_mul]
    change (∫z:momentSpace X,amount z.2 ∂(F.order G).prod X.dice)=_
    rw [integral_fun_snd];simp
  rw [erase];simpa only [Complex.sub_re,Complex.ofReal_re] using total

end YM.Integration.WilsonPositionSeparatedProfileMayerLeadingGaussian
