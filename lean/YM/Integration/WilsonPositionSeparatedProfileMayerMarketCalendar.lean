import YM.Integration.WilsonPositionSeparatedProfileMayerSamplingCurrency
import YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn

/-! The complete original regulator-independent covariance and rare-cell fees in the physical temperature. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerMarketCalendar
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
open Precision Coat Source Matrix Dict06 AnalyticBridge.LocalGaussianLaws ProbabilityTheory
private theorem converted {E:ℝ→ℝ} (p:ℕ) (rate:Rate G L (-(p:ℝ)-1) E) (ε:ℝ) (ep:0<ε):
    ∀ᶠs:ℝ in atTop,∀β:ℝ,0<β→β≤2*betaF G s L→|E s|≤ε*(Coat.gStep β)^p:=by
  have credit:=rate.mul ((Coat.burst_rate G L).pow p)
  have neg:-(p:ℝ)-1+1/2*p<0:=by have:=Nat.cast_nonneg (α:=ℝ) p;linarith
  filter_upwards [credit.below neg ε ep] with s h
  intro β pos upper
  have hg:0<Coat.gStep β:=inv_pos.mpr (Real.sqrt_pos.mpr pos)
  have hi:=pow_le_pow_left₀ (inv_nonneg.mpr hg.le) (Coat.burst_h (G:=G) (x:=s) (L:=L) upper) p
  have hn:0≤Coat.burst G L s:=Real.sqrt_nonneg _
  change |E s*(Coat.burst G L s)^p|≤ε at h
  rw [abs_mul,abs_of_nonneg (pow_nonneg hn _)] at h
  rw [←div_le_iff₀ (pow_pos hg p),div_eq_mul_inv,←inv_pow]
  exact (mul_le_mul_of_nonneg_left hi (abs_nonneg _)).trans h

private theorem cooled (G:Gauge) (L:Side) (A:ℝ) (hA:0≤A) (ε:ℝ) (ep:0<ε):
    ∀ᶠs:ℝ in atTop,∀β:ℝ,betaF G s L/2≤β→A*Coat.gStep β≤ε:=by
  have divpos:0≤A/ε:=div_nonneg hA ep.le
  filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop (2*(1+A/ε)^2)] with s large
  intro β lower
  have enough:(1+A/ε)^2≤β:=by linarith
  have root:=Real.sqrt_le_sqrt enough
  rw [Real.sqrt_sq (by linarith)] at root
  have rb:0<Real.sqrt β:=by linarith
  change A*(Real.sqrt β)⁻¹≤ε; rw [←div_eq_mul_inv,div_le_iff₀ rb]
  simpa only [mul_comm] using (div_le_iff₀ ep).mp (show A/ε≤Real.sqrt β by linarith)

theorem original (P:Teller G) (L:Side) (D:Patch) {W:ℝ} (o:Target.Order G W) (p:ℕ)
    (E:ℝ→ℝ) (rate:Rate G L (-(p:ℝ)-1) E) (a b c:ℝ) (hc:0≤c) (ε:ℝ) (ep:0<ε):
    ∀ᶠs:ℝ in atTop,∀ {f k:Side} {S:StepData k f} (T:Tube G S) {A:Rep G f}
    {Q:ConnectedActivityE6.Target G P} {μ C:ℝ} (_:Cash W s μ L Q o C T A),S.patch=D→S.patch.L=L→
     |a*E s| + |b*WilsonOriginalSignedSamplerMoment.fee T L P o p s|+c*(Coat.gStep A.beta)^(p+1)≤ε*(Coat.gStep A.beta)^p:=by
  let F:=WilsonPositionSeparatedProfileMayerSamplingCurrency.charge P L D o p
  have hf:Rate G L (-(p:ℝ)-1) F:=WilsonPositionSeparatedProfileMayerSamplingCurrency.priced P L D o p (-(p:ℝ)-1)
  have third:0<ε/3:=by linarith
  filter_upwards [converted p (rate.mul_left a) (ε/3) third,converted p (hf.mul_left b) (ε/3) third,cooled G L c hc (ε/3) third] with s sale raw chill
  intro f k S T A Q μ C H same chart
  have upper:=H.laws.intake.window.2;have lower:=H.laws.intake.window.1;rw [chart] at upper lower
  have hg:0<Coat.gStep A.beta:=inv_pos.mpr (Real.sqrt_pos.mpr H.laws.intake.positive)
  have first:=sale _ H.laws.intake.positive upper
  have second:=raw _ H.laws.intake.positive upper
  have last:=mul_le_mul_of_nonneg_right (chill _ lower) (pow_nonneg hg.le p)
  rw [WilsonPositionSeparatedProfileMayerSamplingCurrency.funded D same H.laws.data.funds.funds]
  change |a*E s|≤_ at first;change |b*F s|≤_ at second
  change |a*E s|+|b*F s|+c*(Coat.gStep A.beta)^(p+1)≤_
  rw [pow_succ];linarith

end YM.Integration.WilsonPositionSeparatedProfileMayerMarketCalendar
