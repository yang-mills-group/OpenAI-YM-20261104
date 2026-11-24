import YM.Integration.WilsonCoherentMayerMixedMoment
import YM.Integration.WilsonCoherentMayerSignedCharge

/-! Taylor approximation of the compact submitted marks under the original
joint Haar and Gaussian law.  The complete signed incumbent remains inside
the integral; the other polynomial may be any original finite decoration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerMixedTaylor
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

theorem charged {η r K Y:ℝ} (loc:I→Site f) (X:Coat T F) (A:Rotator P L η r K Y X)
    (B:Normal.poly (Eye X)) (d p:ℕ) (hd:B.totalDegree≤d) (W D:momentSpace X→ℝ)
    (wm:Measurable W) (dm:Measurable D) {weight fee:ℝ} (hw:0≤weight) (hf:0≤fee)
    (coat:∀z,|W z|≤weight) (bill:∀z,|D z|≤fee*‖restrict run ds F loc z.2‖^(p+1)):
    let v:=fun z:momentSpace X=>((W z*D z:ℝ):ℂ)*Cloud.paint (fun i=>z.2 (tube X i)) B
    Integrable v (moment X) ∧ (∫z,‖v z‖ ∂moment X)≤
      (weight*fee)*(Rise.coin B*Real.sqrt (Common.priced
        (1+Window.payE η r K (tubularPrice G L)) (2*d))*
        Real.sqrt (panel run ds (Real.sqrt (Window.payE η r K (tubularPrice G L))) (2*(p+1)))):=by
  let painted (z:Air f G):=Cloud.paint (fun i=>z (tube X i)) B
  let g (z:Air f G):=‖painted z‖*‖restrict run ds F loc z‖^(p+1)
  have h:=WilsonCoherentMayerMixedMoment.original run ds X A loc B d p hd
  have cmp (z:momentSpace X):‖((W z*D z:ℝ):ℂ)*painted z.2‖≤(weight*fee)*g z.2:=by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    have hm:=mul_le_mul (coat z) (bill z) (abs_nonneg _) hw
    apply (mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans_eq
    unfold g;ring
  have weighted:Integrable (fun z:momentSpace X=>(weight*fee)*g z.2) (moment X):=
    ((h.1.comp_snd (F.order G)).const_mul (weight*fee))
  have hi:Integrable (fun z:momentSpace X=>((W z*D z:ℝ):ℂ)*painted z.2) (moment X):=by
    apply weighted.mono' _ (ae_of_all _ cmp)
    have mf:Integrable (fun z:momentSpace X=>painted z.2) (moment X):=
      (WilsonCoherentMayerFuelSquare.sampled X A.fullC B).1.comp_snd (F.order G)
    exact (Complex.continuous_ofReal.measurable.comp (wm.mul dm)).aestronglyMeasurable.mul mf.aestronglyMeasurable
  refine ⟨hi,(integral_mono hi.norm weighted cmp).trans ?_⟩
  change (∫z:momentSpace X,(weight*fee)*g z.2 ∂((F.order G).prod X.dice))≤_
  rw [integral_const_mul,integral_fun_snd]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  exact mul_le_mul_of_nonneg_left h.2 (mul_nonneg hw hf)

theorem purchased (p:ℕ):∃C:ℝ,0≤C ∧ ∀ (φ:I→Reading), (∀i a,|φ i a|≤‖a‖)→
    ∀{c f:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}{P:Teller G}{L:Side}{η r K Y:ℝ},
    ∀(loc:I→Site f)(X:Coat T F)(_A:Rotator P L η r K Y X), P.Funds S T→X.V=1→Assembly.Clear S X.x X.seeds F→
    ∀(β g θ:ℝ),0<β→0<g→∀(y:∀i,run.family.label (ds i))(B:Normal.poly (Eye X))(d:ℕ),B.totalDegree≤d→
    ∀(W:momentSpace X→ℝ)(weight:ℝ),0≤weight→Measurable W→(∀z,|W z|≤weight)→
    let v:=fun z:momentSpace X=>((W z*residual run ds loc X φ θ β g y p z:ℝ):ℂ)*Cloud.paint (fun i=>z.2 (tube X i)) B
    Integrable v (moment X) ∧ (∫z,‖v z‖ ∂moment X)≤
      (weight*(WilsonCoherentReportingPivot.mass run ds θ y*(C*g^(p+1))))*
        (Rise.coin B*Real.sqrt (Common.priced
          (1+Window.payE η r K (tubularPrice G L)) (2*d))*
          Real.sqrt (panel run ds (Real.sqrt (Window.payE η r K (tubularPrice G L))) (2*(p+1)))):=by
  obtain ⟨C,hC,h⟩:=WilsonRetainedSignedStencilPhysical.purchased run ds p
  refine ⟨C,hC,?_⟩
  intro φ contract c f S T F P L η r K Y loc X A funds V clear β g θ hβ hg y B d hd W weight hw hW coat
  have nm:0≤WilsonCoherentReportingPivot.mass run ds θ y:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  apply charged run ds loc X A B d p hd W _ hW (WilsonCoherentMayerSignedCharge.measurable run ds funds loc X V clear φ θ β g hβ y p) hw (by positivity) coat
  intro z
  apply (h φ contract θ y loc funds X V clear β hβ z g hg).trans_eq
  rw [mul_pow];ring

end YM.Integration.WilsonCoherentMayerMixedTaylor
