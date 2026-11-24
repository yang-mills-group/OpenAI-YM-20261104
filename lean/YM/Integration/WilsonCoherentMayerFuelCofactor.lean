import YM.Integration.WilsonCoherentMayerFuelEntered
import YM.Integration.WilsonPhysicalHistoryRetainedSpringChamberMoment

/-! The actual signed old placement can be tested against the repeated
two-bond E6 quadratic on its own joint angular law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerFuelCofactor
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


open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences
open WilsonPositionSeparatedProfileMayerMasks (gates)
open WilsonPositionSeparatedProfileMayerGateSafety (sites)
open WilsonPositionSeparatedProfileMayerGateReturn (source bank)
open private measurable layers from YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn
open WilsonCoherentMayerFuelSector (patch)


open OriginalMarkedRunAction
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open IterationFour.Vacuum Comparison.RG02

def cofactor (entry:Submitted run R I)(old:Team R)(a:ℝ)(X:Coat T F)(q:Ledger f 2)(k:ℕ)(z:momentSpace X):ℝ:=
  source entry old a X z*(∏i,gates entry i a X z)*WilsonCoherentMayerFuelGate.weight X q R.beta a k z.2

theorem funded (entry:Submitted run R I)(old:Team R)(a:ℝ)(X:Coat T F)(flat:X.blank=X)(fund:P.Funds S T)(q:Ledger f 2)(k:ℕ):
    Measurable (cofactor run entry old a X q k) ∧ ∀z,‖cofactor run entry old a X q k z‖≤bank entry old:=by
  have seen:=measurable entry old fund a X flat
  refine ⟨(seen.1.mul seen.2).mul ((WilsonCoherentMayerFuelRemoval.borel X q R.beta a k).comp measurable_snd),?_⟩
  intro z
  have gate:=layers entry a X z
  have weight:=WilsonCoherentMayerFuelGate.range X q R.beta a k z.2
  have h1:=WilsonPositionSeparatedProfileMayerGateReturn.bound entry old a X z
  simp only [cofactor,norm_mul,Real.norm_eq_abs,abs_of_nonneg (show 0≤_ from gate.1),abs_of_nonneg (show 0≤_ from weight.1)]
  exact (mul_le_of_le_one_right (mul_nonneg (abs_nonneg (source entry old a X z)) gate.1) weight.2).trans ((mul_le_of_le_one_right (abs_nonneg _) gate.2).trans h1)

theorem sampled (entry:Submitted run R I)(old:Team R)(fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
    (X:Coat T F)(H:Cash W X.x μ L Q o C T R)(manifest:X.manifest)(flat:X.blank=X)
    (q:Ledger f 2)(first:q.2.1∉F.trunks)(last:arrive q.2.1 q.2.2∉F.trunks)
    {M:ℕ}(u:Mayer.Decors (WilsonCoherentMayerFuelSector.patch (S:=S) q (together entry old fresh) \ (together entry old fresh).signs S) M)
    (z:momentSpace X):
    let prior:=together entry old fresh
    let k:=Mayer.decorOrder u
    (Mayer.planned H (WilsonCoherentMayerFuelSector.patch q prior) u (Laminate.partner prior H) X z:ℂ)=
      (cofactor run entry old o.a X q k z:ℂ)*Cloud.paint (fun i=>z.2 (tube X i)) (word X q first last k 1):=by
  intro prior k
  have subset:prior.signs S⊆WilsonCoherentMayerFuelSector.patch q prior:=Finset.subset_insert ..
  have read:=WilsonCoherentMayerFuelSector.issued (p:=WilsonCoherentMayerFuelSector.patch q prior) q u
    (WilsonCoherentMayerFuelSector.appended q prior (WilsonCoherentMayerFuelEntered.absent q prior)) H (Laminate.partner prior H) X z
  rw [Laminate.compartments prior _ subset,WilsonPositionSeparatedProfileMayerMasks.products entry old fresh] at read
  have issue:=WilsonCoherentMayerFuelWick.incidence X q first last H k (1:Normal.poly (Eye X)) z.2
  rw [map_one,mul_one] at issue
  rw [read,WilsonCoherentMayerFuelHaar.sampled H X rfl flat manifest z.1 z.2 q]
  unfold cofactor WilsonPositionSeparatedProfileMayerGateReturn.source
  push_cast
  rw [show ((Mayer.exponent H X z.2 (label q):ℝ):ℂ)^k/(k.factorial:ℂ)=
       ((WilsonCoherentMayerFuelGate.weight X q R.beta o.a k z.2:ℝ):ℂ)*Cloud.paint (fun i=>z.2 (tube X i)) (word X q first last k 1)
      from by unfold WilsonCoherentMayerFuelGate.weight;push_cast at issue ⊢;exact issue]
  ring

theorem mixed (X:Coat T F) (Z B:Air f G→ℂ) {a b:ℝ} (ha:0≤a)(hb:0≤b)
    (mz:AEStronglyMeasurable Z X.dice)(mb:AEStronglyMeasurable B X.dice)
    (zz:Integrable (fun z=>‖Z z‖^2) X.dice)(bb:Integrable (fun z=>‖B z‖^2) X.dice)
    (hz:(∫z,‖Z z‖^2 ∂X.dice)≤a^2)(hB:(∫z,‖B z‖^2 ∂X.dice)≤b^2):
    Integrable (fun z=>‖Z z‖*‖B z‖) X.dice ∧
      (∫z,‖Z z‖*‖B z‖ ∂X.dice)≤a*b:=by
  let f:=fun z=>‖Z z‖
  let g:=fun z=>‖B z‖
  have first:MemLp f 2 X.dice:=(memLp_two_iff_integrable_sq mz.norm).2 zz
  have second:MemLp g 2 X.dice:=(memLp_two_iff_integrable_sq mb.norm).2 bb
  have twice:ENNReal.ofReal 2=2:=by norm_num
  have hold:=integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (show (0:Air _ G→ℝ)≤ᵐ[X.dice] f from ae_of_all _ fun _=>norm_nonneg _)
    (show (0:Air _ G→ℝ)≤ᵐ[X.dice] g from ae_of_all _ fun _=>norm_nonneg _)
    (by rwa [twice]) (by rwa [twice])
  have left:=Real.sqrt_le_sqrt hz;rw [Real.sqrt_sq ha] at left
  have right:=Real.sqrt_le_sqrt hB;rw [Real.sqrt_sq hb] at right
  refine ⟨first.integrable_mul second,?_⟩
  apply (show (∫z,f z*g z ∂X.dice)≤Real.sqrt (∫ z,f z^2 ∂X.dice)*Real.sqrt (∫z,g z^2 ∂X.dice) from ?_).trans
    (mul_le_mul left right (Real.sqrt_nonneg _) ha)
  simpa [Real.rpow_two,Real.sqrt_eq_rpow] using hold

end YM.Integration.WilsonCoherentMayerFuelCofactor
