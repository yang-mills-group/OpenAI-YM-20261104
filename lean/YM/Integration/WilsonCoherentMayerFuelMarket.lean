import YM.Integration.WilsonCoherentMayerFuelRemoval
import YM.Integration.WilsonCoherentMayerFuelSector
import YM.Integration.WilsonPositionSeparatedProfileMayerSamplingCurrency

/-! The positive repeated covariance head on the complete incoming polynomial,
with the same physical Gaussian and its original stage price. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerFuelMarket
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
theorem original (H:Cash W s μ L Q o C T R) (temp:0≤Pressure.temp s) (χ:Chi)
    (v:Finset (LocalLTE.Fan.Veil c f)) (i:Greenbelt.Reserve S) (tag:S.Choices):
    let X:=chamber T s o.K χ 1 v i tag
    let F:=Greenbelt.allot i
    ∀(q:Ledger f 2) (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks)
      (k d:ℕ) (B:Normal.poly (Eye X)),B.totalDegree≤d→
      let D:=2*k+d
      let joint:=WilsonCoherentMayerFuelWick.word X q first last k B
      ‖(∫z:Air f G,(((Mayer.exponent H X z (label q))^k/k.factorial:ℝ):ℂ)*
          Cloud.paint (fun a=>z (tube X a)) B ∂X.dice)-
        Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
          (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 joint‖ ≤
      ((Coat.capQ S o.eta o.gap o.ample (tubularPrice G L) X.B G 1 q)^k/k.factorial * Rise.coin B)*
        (Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L)) (2*D))*
          Real.sqrt (X.dice.real (eerie X (sites (S:=S) q) o.ξ R.beta))+
            |WilsonOriginalSignedSamplerMoment.fee T L P o D s|) := by
  intro X F q first last k d B deg D joint
  have manifest:X.manifest:=by
    change (ConnectedActivityE6.Matter.roster (LocalLTE.Fan.arm (S:=S) v)).flags = RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have degree:joint.totalDegree≤D:=WilsonCoherentMayerFuelWick.degree X q first last k d B deg
  have cut:=WilsonCoherentMayerFuelRemoval.second X H rfl manifest q k joint D degree
  have opened:=WilsonOriginalSignedSamplerMoment.original T H temp χ v i tag joint D degree
  have exactRow (z:Air f G): (((Mayer.exponent H X z (label q))^k/k.factorial:ℝ):ℂ)*
      Cloud.paint (fun a=>z (tube X a)) B = (weight X q R.beta o.a k z:ℂ)*Cloud.paint (fun a=>z (tube X a)) joint :=
    WilsonCoherentMayerFuelWick.incidence X q first last H k B z
  simp_rw [exactRow]
  have physical:=dist_triangle (∫z:Air f G,(weight X q R.beta o.a k z:ℂ)*Cloud.paint (fun a=>z (tube X a)) joint ∂X.dice)
    (∫z:Air f G,Cloud.paint (fun a=>z (tube X a)) joint ∂X.dice)
    (Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s) (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 joint)
  simp only [dist_eq_norm] at physical
  apply physical.trans ((add_le_add cut opened).trans _)
  rw [←mul_add]
  have cash:=WilsonCoherentMayerFuelTariff.repeated X A q first last k B
  have positive:0≤Rise.coin joint:=by rw [Rise.metal];positivity
  let charge:=Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L)) (2*D))*
    Real.sqrt (X.dice.real (eerie X (sites (S:=S) q) o.ξ R.beta))
  let error:=WilsonOriginalSignedSamplerMoment.fee T L P o D s
  have bound:charge+error≤charge+|error|:=by linarith [le_abs_self error]
  have earned:0≤charge+|error|:=add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (abs_nonneg _)
  exact (mul_le_mul_of_nonneg_left bound positive).trans (mul_le_mul_of_nonneg_right cash earned)

end YM.Integration.WilsonCoherentMayerFuelMarket
