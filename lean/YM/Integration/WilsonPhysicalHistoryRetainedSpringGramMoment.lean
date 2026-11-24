import YM.Integration.WilsonPhysicalHistoryRetainedSpringGram
import YM.Integration.WilsonPhysicalHistoryRetainedSpringChamberMoment
import YM.Integration.WilsonPhysicalHistoryRetainedSpringBareSite

/-! The genuine paired kinetic path row in the original Wilson chamber. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f}
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}

theorem chamber_gram_rows (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) {K : PathData G} {B : Clip} {σ D Λ : ℝ}
    (paid : K.Bounds B σ D Λ) (x : Site f) (q l : ℕ)
    (g w : ℝ) (hg : 0<g) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let F:=Greenbelt.allot i
    let A:=gramEntries K
    let d:=fun z : Air f G=>(w:ℂ)*((sitePacket A x ((X.wrapY y).input
      ((X.wrapY y).liftA (Integral.temperature g) z)):ℂ)-siteTaylor A x (angularSample F z) q g)
    Integrable d X.dice ∧ Integrable (fun z=>‖d z‖^(l+1)) X.dice ∧ (∫ z,‖d z‖^(l+1) ∂X.dice)≤
      (|w| *(Stationary.gramCost G D*(2*speedPrice G L o.eta o.gap o.ample ((q+1)*(l+1)-1)*|g|/σ)^(q+1)))^(l+1) := by
  intro X F A d
  have manifest : X.manifest:=by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  obtain ⟨turn,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have budget:=gram_finance K paid
  have bg : 0<Integral.temperature g:=by unfold Integral.temperature; positivity
  have sample (z : Air f G) : (X.wrapY y).input ((X.wrapY y).liftA (Integral.temperature g) z)=
      represent (g • angularSample F z):=by
    simpa only [inverse_temperature_step hg,mul_inv_cancel₀ hg.ne',one_smul] using
      chamber_path H.laws.data.funds.funds s o.K χ i v tag bg y z g
  have crystal (z : Air f G) : d z=(w:ℂ)*((sitePacket A x (represent (g • angularSample F z)):ℂ)-
      siteTaylor A x (angularSample F z) q g):=by dsimp only [d]; rw [sample]
  refine ⟨by rw [funext crystal]; exact (site_in_mean turn A paid.width budget x q g).1.const_mul _,?_⟩
  exact registered_moment turn A paid.width budget x q l g w _ (funext sample)

end YM.Integration.OriginalMarkedRunAction
