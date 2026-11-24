import YM.Integration.WilsonOriginalSignedSamplerMoment

/-! The genuine covariance truncation rate before all admitted finite tubes. -/
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerSamplingCurrency
open Function Filter Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Matrix
open Pressure Pressure.Tube Pressure.Stores FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open Next.SectorChange Next.SectorChange.Rows Next.Fluctuations Next.Fluctuations.Sector
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws AnalyticBridge.GaussianFieldAlignment
open ConnectedActivityE6 ConnectedActivityE6.Window ConnectedActivityE6.Control ConnectedActivityE6.Census
open PhysicalNext.Repeat PhysicalNext.Repeat.Malachite Comparison.RG02.Cumulants
open Next.Rank WilsonCoherentMayerHearing
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Next.SectorChange ConnectedActivityE6.Control ConnectedActivityE6.Census
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine PhysicalNext.Repeat.Malachite
open Comparison.RG02.Cumulants Next.Rank WilsonCoherentMayerHearing
open scoped Topology Classical BigOperators

variable {G:Gauge}

def charge (P:Teller G) (L:Side) (D:Patch) {W:ℝ} (o:Target.Order G W) (t:ℕ) (s:ℝ):ℝ:=
  WilsonOriginalSignedShutterMoment.fee G L o t s+
    (WilsonOriginalSignedPathCut.price G D P.bind P.top.clip P.top.paths P.top.width * Real.exp (-(P.top.width/4)*till s))*
        Common.priced (max 1 (headGap G D P.bind P.top.clip)⁻¹) t

theorem priced (P:Teller G) (L:Side) (D:Patch) {W:ℝ} (o:Target.Order G W) (t:ℕ) (p:ℝ): Rate G L p (charge P L D o t):=by
  apply (WilsonOriginalSignedShutterMoment.rate G L o t p).add
  exact (((Rate.cutoff (G:=G) (L:=L) (a:=p) (δ:=P.top.width/4) (div_pos P.top.width_pos (by norm_num))).mul_left _).mul_right _)

variable {c f:Side} {S:StepData c f} {T:Tube G S} {P:Teller G} {W:ℝ}
theorem funded (D:Patch) (same:S.patch=D) (fund:P.Funds S T) (L:Side) (o:Target.Order G W) (t:ℕ) (s:ℝ):WilsonOriginalSignedSamplerMoment.fee T L P o t s=charge P L D o t s:=by
  unfold WilsonOriginalSignedSamplerMoment.fee WilsonOriginalSignedSamplerMoment.cap charge
  rw [same,fund.knobs,fund.high]

theorem original (P:Teller G) (L:Side) (D:Patch) (o:Target.Order G W) (t:ℕ) (p:ℝ):
    ∀ᶠs:ℝ in atTop,∀ {c f:Side} {S:StepData c f} (T:Tube G S),S.patch=D→P.Funds S T→
       |WilsonOriginalSignedSamplerMoment.fee T L P o t s|≤betaF G s L^p:=by
  filter_upwards [priced P L D o t (p-1) p (by linarith)] with s sale
  intro c f S T same fund;rw [funded D same fund];exact sale

end YM.Integration.WilsonPositionSeparatedProfileMayerSamplingCurrency
