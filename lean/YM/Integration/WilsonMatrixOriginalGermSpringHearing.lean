import YM.Integration.WilsonMatrixOriginalGermSignedPrior

/-! The original signed spring can be inserted at any earlier RG date in
the complete two-source Wilson response. Its proved site bill multiplies
one centered moment on the physical UV law, including both proper means. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermSpringHearing
open MeasureTheory Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox
open WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermTwoMarkJoint WilsonMatrixOriginalGermFourRawMarks
open WilsonMatrixOriginalGermSignedPrior WilsonRootedUnnormalizedHearing
open Laurent Bloch Precision Exterior Tree PowerSeries Marker IterationFour IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Assembly WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank Stationary
open WilsonCoeffUV.Bank.Mosaic FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open OriginalMarkedRunAction
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {m k N p:ℕ}

def centered (X Y:Config G (R.family.side N p)→ℂ):Config G (R.family.side N p)→ℂ:=
  let μ:=scene R.family.path N p N
  pair (∫U,X U ∂μ) (∫U,Y U ∂μ) (moment μ X Y) X Y

def debit (upper:k≤N) (W:Config G (R.family.side k p)→ℂ)
    (X Y:Config G (R.family.side N p)→ℂ):ℂ:=
  ∫U,backTo R.family.path N p upper W U*centered R X Y U ∂scene R.family.path N p N

theorem measured (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (hW:Envelope W)
    (B:ℝ) (bound:∀V,‖W V‖≤B) (X Y:Config G (R.family.side N p)→ℂ) (hX:Envelope X) (hY:Envelope Y):
    HasDerivAt (invoice R lower upper W X Y) (debit R upper W X Y) 0 ∧
      ‖debit R upper W X Y‖≤B*∫U,‖centered R X Y U‖ ∂scene R.family.path N p N:=by
  let μ:=scene R.family.path N p N
  let α:=∫U,X U ∂μ
  let β:=∫U,Y U ∂μ
  let c:=moment μ X Y
  have returned:=WilsonMatrixOriginalGermFourRawMarks.charged R lower upper W hW X Y hX hY
  have shift:=WilsonMatrixOriginalGermSignedPrior.value R lower upper W hW X Y hX hY α β c
  constructor
  · exact (congrArg (fun q:ℂ=>HasDerivAt (invoice R lower upper W X Y) q 0) shift).mp returned
  · letI:IsProbabilityMeasure μ:=probability R.makes.wilson (le_refl N)
    have data:Envelope (centered R X Y):=((hX.subC (Envelope.constC α)).mulC (hY.subC (Envelope.constC β))).subC (Envelope.constC c)
    have test:=backTo_bound R.family.path N p upper hW.meas B bound
    calc
      _≤∫U,B*‖centered R X Y U‖ ∂μ:=by
        apply norm_integral_le_of_norm_le ((data.integrableC μ).norm.const_mul B)
        exact Filter.Eventually.of_forall fun U=>(norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (test U) (norm_nonneg _))
      _=_:=integral_const_mul _ _

theorem original (lower:m≤k) (upper:k≤N) (r:ℕ) (Z:SeriesA G) {σ b:ℝ} (hs:0<σ) (paid:Draw Z σ b)
    (g:ℝ) (x:Site (R.family.side k p)) (w z:R.family.label 4) (o t:Site (R.family.side m p)):
    let W:=fun U=>((-springAt R N p k r Z g x U:ℝ):ℂ)
    let X:=asset R (lower.trans upper) w o
    let Y:=asset R (lower.trans upper) z t
    HasDerivAt (invoice R lower upper W X Y) (debit R upper W X Y) 0 ∧
      ‖debit R upper W X Y‖ ≤ springSiteBill R N k r Z g b*∫U,‖centered R X Y U‖ ∂scene R.family.path N p N:=by
  intro W X Y
  obtain ⟨hm,hb⟩:=filed_site_price R N p k r upper Z hs paid g x
  have cap (U:Config G (R.family.side k p)):‖W U‖ ≤ springSiteBill R N k r Z g b:=by
    change ‖((-springAt R N p k r Z g x U:ℝ):ℂ)‖≤_
    rw [Complex.norm_real,norm_neg]
    exact hb U
  have sealed:Envelope W:=⟨Complex.continuous_ofReal.measurable.comp hm.neg,_,cap⟩
  exact measured R lower upper W sealed _ cap X Y (Envelope.compactC (R.family.continuousO ..))
    (Envelope.compactC (R.family.continuousO ..))

end YM.Integration.WilsonMatrixOriginalGermSpringHearing
