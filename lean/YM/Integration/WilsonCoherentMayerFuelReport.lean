import YM.Integration.WilsonCoherentMayerFuelStencil
import YM.Integration.WilsonCoherentMayerFuelThermal
import YM.Integration.WilsonPositionSeparatedProfileMayerStencilPrice
import YM.Integration.WilsonOriginalSignedShutterSquare

/-! The compact submitted signed Wilson markings and one actual repeated
E6 covariance occurrence in the original joint experiment, compared directly
to their deposited finite polynomial on the prescribed forest covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerFuelReport
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


open WilsonPositionSeparatedProfileMayerStencilPrice (deposited budget)

private theorem integrable {W s μ L C:ℝ} {r:Side} {o:Target.Order G W}
    {Q:Target G P} {Y:Rep G f} (H:Cash W s μ r Q o C T Y)
    (X:Coat T F) (A:Rotator P r o.eta o.gap o.ample L X)
    (q:Ledger f 2) (first:q.2.1∉F.trunks)(last:arrive q.2.1 q.2.2∉F.trunks)
    (k:ℕ)(B:Normal.poly (Eye X)):
    Integrable (fun z:Air f G=>(((Mayer.exponent H X z (label q))^k/k.factorial:ℝ):ℂ)*
      Cloud.paint (fun i=>z (tube X i)) B) X.dice:=by
  let g:=WilsonCoherentMayerFuelGate.weight X q Y.beta o.a k
  let C:=word X q first last k B
  let read (z:Air f G):=Cloud.paint (fun i=>z (tube X i)) C
  have hread:Integrable read X.dice:=(WilsonCoherentMayerFuelSquare.sampled X A.fullC C).1
  have hg:Measurable g:=WilsonCoherentMayerFuelRemoval.borel X q Y.beta o.a k
  have weighted:Integrable (fun z=>(g z:ℂ)*read z) X.dice:=by
    apply hread.norm.mono' ((Complex.continuous_ofReal.measurable.comp hg).aestronglyMeasurable.mul hread.aestronglyMeasurable)
    filter_upwards with z
    change ‖(g z:ℂ)*read z‖≤‖read z‖
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (WilsonCoherentMayerFuelGate.range ..).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (WilsonCoherentMayerFuelGate.range ..).2
  exact weighted.congr (ae_of_all _ fun z=>(WilsonCoherentMayerFuelWick.incidence X q first last H k B z).symm)

theorem purchased (P:Teller G) (L:Side) (D:Patch) {w:ℝ} (o:Target.Order G w)
    (k p:ℕ) (ε:ℝ) (ep:0<ε):
    ∃C:ℝ,0≤C ∧ ∀ᶠs:ℝ in atTop,∀{c f:Side}{S:StepData c f}(T:Tube G S)
      {Y:Rep G f}{Q:Target G P}{μ h:ℝ}(H:Cash w s μ L Q o h T Y),
      S.patch=D→S.patch.L=L→0≤Pressure.temp s→0<Y.beta→
      ∀(χ:Chi)(v:Finset (LocalLTE.Fan.Veil c f))(i:Greenbelt.Reserve S)(tag:S.Choices),
      let X:=chamber T s o.K χ 1 v i tag
      let F:=Greenbelt.allot i
      let g:=Coat.gStep Y.beta
      ∀(q:Ledger f 2)(first:q.2.1∉F.trunks)(last:arrive q.2.1 q.2.2∉F.trunks)
        (loc:I→Site f)(φ:I→Reading),(∀i z,|φ i z|≤‖z‖)→∀θ:ℝ,∀y:∀i,run.family.label (ds i),
      let B:=deposited run ds φ θ y g p X loc
      let whole:=fun z:momentSpace X=>(WilsonRetainedSignedStencilPhysical.marked run ds φ θ y loc X Y.beta z g:ℂ)*
        (((Mayer.exponent H (X.wrapY z.1) z.2 (label q))^k/k.factorial:ℝ):ℂ)
      Integrable whole (moment X) ∧
      ‖(∫z,whole z ∂moment X)-Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
        (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 (word X q first last k B)‖≤
      (WilsonCoherentReportingPivot.mass run ds θ y*(C*g^(p+1)))*
        ((Coat.capQ S o.eta o.gap o.ample (tubularPrice G L) X.B G 1 q)^k/k.factorial*
          WilsonCoherentMayerFuelStencil.price run ds L o k p) +
      ((Coat.capQ S o.eta o.gap o.ample (tubularPrice G L) X.B G 1 q)^k/k.factorial*Rise.coin B)*
        (ε*g^(2*k+p)):=by
  obtain ⟨C,hC,source⟩:=WilsonCoherentMayerFuelStencil.purchased run ds p
  refine ⟨C,hC,?_⟩
  filter_upwards [WilsonCoherentMayerFuelThermal.purchased P L D o k p ε ep] with s market
  intro c f S T Y Q μ h H patch side temp positive χ v i tag X F g q first last loc φ cap θ y B whole
  have manifest:X.manifest:=by
    change (ConnectedActivityE6.Matter.roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD];exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  have clear:Assembly.Clear S X.x X.seeds F:=by
    change Assembly.Clear S s (ConnectedActivityE6.Matter.roster (LocalLTE.Fan.arm (S:=S) v)) F
    rw [LocalLTE.Fan.Field.rosterD];exact Assembly.bare_is_Clear S s F
  have blank:=WilsonOriginalSignedShutterSquare.blank (T:=T) χ s o.K v i tag
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have hg:0<g:=by dsimp [g,Coat.gStep];positivity
  let delta (z:momentSpace X):=((residual run ds loc X φ θ Y.beta g y p z:ℝ):ℂ)*
    (((Mayer.exponent H (X.wrapY z.1) z.2 (label q))^k/k.factorial:ℝ):ℂ)
  have paid:=source φ cap H X rfl blank manifest rfl clear ⟨_,A⟩ loc θ g positive hg y q first last k
    (fun _=>1) 1 zero_le_one measurable_const (by simp)
  simp only [one_mul] at paid
  let booked (z:Air f G):=(((Mayer.exponent H X z (label q))^k/k.factorial:ℝ):ℂ)*
    Cloud.paint (fun a=>z (tube X a)) B
  have hi:Integrable booked X.dice:=integrable H X A q first last k B
  have shifted:Integrable (fun z:momentSpace X=>booked z.2) (moment X):=hi.comp_snd (F.order G)
  have split:whole=fun z:momentSpace X=>delta z + booked z.2:=by
    funext z
    dsimp only [whole,delta,booked]
    rw [WilsonCoherentMayerFuelHaar.sampled H X rfl blank manifest z.1 z.2 q,
      WilsonPositionSeparatedProfileMayerStencilPrice.printed]
    unfold WilsonCoherentMayerSignedCharge.residual
    push_cast;ring
  have cross:(∫z:momentSpace X,booked z.2 ∂moment X)=(∫z:Air f G,booked z ∂X.dice):=by
    change (∫z:momentSpace X,booked z.2 ∂((F.order G).prod X.dice))=_
    rw [integral_fun_snd];simp [Measure.real]
  have fi:Integrable delta (moment X):=paid.1
  refine ⟨split ▸ (fi.add shifted),?_⟩
  rw [split,integral_add fi shifted,cross,add_sub_assoc]
  exact (norm_add_le _ _).trans (add_le_add ((norm_integral_le_integral_norm _).trans paid.2)
    (market T H patch side temp χ v i tag q first last B
      (WilsonPositionSeparatedProfileMayerStencilPrice.degree run ds φ θ y g p X loc)))

end YM.Integration.WilsonCoherentMayerFuelReport
