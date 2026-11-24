import YM.Integration.WilsonCoherentMayerMixedTaylor
import YM.Integration.WilsonCoherentMayerFuelHaar
import YM.Integration.WilsonCoherentMayerFuelTariff
import YM.Integration.WilsonCoherentMayerFuelRemoval

/-! The actual repeated covariance occurrence inside the original Haar and
angular-noise experiment buys the signed compact mark Taylor remainder,
including an arbitrary bounded, genuinely correlated incumbent. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerFuelStencil
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

open WilsonCoherentMayerMixedMoment
open WilsonCoherentMayerSignedCharge (residual)


open WilsonCoherentMayerFuelPolynomial (label)
open WilsonCoherentMayerFuelWick (word)
open WilsonCoherentMayerFuelGate (weight)

def price (L:Side) {w:ℝ} (o:Target.Order G w) (k p:ℕ):ℝ:=
  Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L)) (2*(2*k)))*
  Real.sqrt (panel run ds (Real.sqrt (payE o.eta o.gap o.ample (tubularPrice G L))) (2*(p+1)))

theorem purchased (p:ℕ):∃C:ℝ,0≤C ∧ ∀ (φ:I→Reading), (∀i a,|φ i a|≤‖a‖)→
    ∀{c f:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}{P:Teller G}{L:Side}
      {w s μ M:ℝ}{Q:Target G P}{o:Target.Order G w}{Y:Rep G f}(H:Cash w s μ L Q o M T Y)
      (X:Coat T F),X.x=s→X.blank=X→X.manifest→X.V=1→Assembly.Clear S X.x X.seeds F→
      (∃n,Rotator P L o.eta o.gap o.ample n X)→
    ∀(loc:I→Site f)(θ g:ℝ),0<Y.beta→0<g→∀(y:∀i,run.family.label (ds i))
      (q:Ledger f 2),q.2.1∉F.trunks→arrive q.2.1 q.2.2∉F.trunks→
    ∀(k:ℕ)(W:momentSpace X→ℝ)(b:ℝ),0≤b→Measurable W→(∀z,|W z|≤b)→
      let v:=fun z:momentSpace X=>((W z*residual run ds loc X φ θ Y.beta g y p z:ℝ):ℂ)*
        (((Mayer.exponent H (X.wrapY z.1) z.2 (label q))^k/k.factorial:ℝ):ℂ)
      Integrable v (moment X) ∧ (∫z,‖v z‖ ∂moment X)≤
        (b*(WilsonCoherentReportingPivot.mass run ds θ y*(C*g^(p+1))))*
        ((Coat.capQ S o.eta o.gap o.ample (tubularPrice G L) X.B G 1 q)^k/k.factorial * price run ds L o k p):=by
  obtain ⟨C,hC,pay⟩:=WilsonCoherentMayerMixedTaylor.purchased run ds p
  refine ⟨C,hC,?_⟩
  intro φ hc c f S T F P L w s μ M Q o Y H X hx blank live held clear active loc θ g hβ hg y q first last k W b hb hW cap v
  obtain ⟨n,A⟩:=active
  let aug (z:momentSpace X):=W z*weight X q Y.beta o.a k z.2
  let B:=word X q first last k (1:Normal.poly (Eye X))
  have hd:B.totalDegree≤2*k:=by
    simpa using WilsonCoherentMayerFuelWick.degree X q first last k 0 (1:Normal.poly (Eye X)) (by simp)
  have intg:=pay φ hc loc X A H.laws.data.funds.funds held clear Y.beta g θ hβ hg y B (2*k) hd aug b hb
    (hW.mul ((WilsonCoherentMayerFuelRemoval.borel X q Y.beta o.a k).comp measurable_snd)) (fun z=>by
      have n:=WilsonCoherentMayerFuelGate.range X q Y.beta o.a k z.2
      rw [show |aug z| = |W z| * |weight X q Y.beta o.a k z.2| from abs_mul ..,abs_of_nonneg n.1]
      exact (mul_le_mul (cap z) n.2 n.1 hb).trans_eq (mul_one _))
  have eq:v=(fun z:momentSpace X=>((aug z*residual run ds loc X φ θ Y.beta g y p z:ℝ):ℂ)*Cloud.paint (fun i=>z.2 (tube X i)) B):=by
    funext z
    have field:=WilsonCoherentMayerFuelWick.incidence X q first last H k (1:Normal.poly (Eye X)) z.2
    rw [map_one,mul_one] at field
    dsimp only [v,aug,B]
    rw [WilsonCoherentMayerFuelHaar.sampled H X hx blank live z.1 z.2 q,field]
    unfold WilsonCoherentMayerFuelGate.weight
    push_cast;ring
  rw [eq]
  refine ⟨intg.1,intg.2.trans ?_⟩
  have single:Rise.coin (1:Normal.poly (Eye X))=1:=by
    rw [show (1:Normal.poly (Eye X))=MvPolynomial.C 1 from map_one MvPolynomial.C |>.symm,Rise.coin,Rise.pay_C,norm_one]
  have orig:=WilsonCoherentMayerFuelTariff.repeated X A q first last k (1:Normal.poly (Eye X))
  rw [single,mul_one] at orig
  have nm:0≤WilsonCoherentReportingPivot.mass run ds θ y:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  unfold price
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right orig (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).trans_eq (mul_assoc ..)

end YM.Integration.WilsonCoherentMayerFuelStencil
