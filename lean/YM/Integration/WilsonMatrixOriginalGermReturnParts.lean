import YM.Integration.WilsonMatrixOriginalGermSlabOriginal
import YM.Integration.WilsonMatrixOriginalGermContamination

/-! The two proper means in the earlier Ward field are taken on the same
earlier Wilson law. The covariance inside each conditional fibre is centered
separately before the four regular and forced terms are added. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermReturnParts
open MeasureTheory Lattice Wilson RG Source MergeProof OPE.Therm PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalGermTwoMarkJoint WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermSignedPrior
open WilsonMatrixOriginalGermSpringHearing WilsonMatrixOriginalGermReplica WilsonInheritedRegisteredField
open WilsonMatrixOriginalGermContamination WilsonRegisteredRegularQuota
open private add_left add_right from YM.Integration.WilsonMatrixOriginalGermContamination
open private marked from YM.Integration.WilsonMatrixOriginalGermGram
open scoped Classical BigOperators
variable {Ω:Type*} [MeasurableSpace Ω]

def proper (μ:Measure Ω) (f g:Ω→ℂ):Ω→ℂ:=pair (∫x,f x ∂μ) (∫x,g x ∂μ) (moment μ f g) f g

theorem bounded (μ:Measure Ω) [IsProbabilityMeasure μ] {f g:Ω→ℂ} {a b:ℝ}
    (ap:0≤a) (hf:∀x,‖f x‖≤a) (hg:∀x,‖g x‖≤b) (u:Ω):‖proper μ f g u‖≤6*(a*b):=by
  have price {H:Ω→ℂ} {c:ℝ} (h:∀x,‖H x‖≤c):‖∫x,H x ∂μ‖≤c:=by
    simpa using norm_integral_le_of_norm_le_const (μ:=μ) (Filter.Eventually.of_forall h)
  have px:=price hf
  have py:=price hg
  have joint:‖∫x,f x*g x ∂μ‖≤a*b:=price (fun x=>by rw [norm_mul];exact mul_le_mul (hf x) (hg x) (norm_nonneg _) ap)
  have cov:‖moment μ f g‖≤a*b+a*b:=(norm_sub_le _ _).trans (add_le_add joint
    (by rw [norm_mul];exact mul_le_mul px py (norm_nonneg _) ap))
  have ac:‖f u-(∫x,f x ∂μ)‖≤a+a:=(norm_sub_le _ _).trans (add_le_add (hf u) px)
  have bc:‖g u-(∫x,g x ∂μ)‖≤b+b:=(norm_sub_le _ _).trans (add_le_add (hg u) py)
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact (add_le_add (mul_le_mul ac bc (norm_nonneg _) (add_nonneg ap ap)) cov).trans (le_of_eq (by ring))

theorem assembled (μ:Measure Ω) [IsFiniteMeasure μ] {f g u v:Ω→ℂ}
    (hf:Envelope f) (hg:Envelope g) (hu:Envelope u) (hv:Envelope v) (x:Ω):
    proper μ (fun z=>f z+u z) (fun z=>g z+v z) x=
      proper μ f g x+proper μ f v x+proper μ u g x+proper μ u v x:=by
  simp only [proper,pair,integral_add (hf.integrableC μ) (hu.integrableC μ),
    integral_add (hg.integrableC μ) (hv.integrableC μ),add_left μ hf hu (hg.addC hv),
    add_right μ hf hg hv,add_right μ hu hg hv]
  ring

theorem received (μ κ:Measure Ω) [IsProbabilityMeasure κ] {f g:Ω→ℂ} (hf:Envelope f) (hg:Envelope g):
    (∫x,proper μ f g x ∂κ)=moment κ f g+((∫x,f x ∂κ)-(∫x,f x ∂μ))*((∫x,g x ∂κ)-(∫x,g x ∂μ))-moment μ f g:=by
  let a:=∫x,f x ∂μ
  let b:=∫x,g x ∂μ
  let c:=moment μ f g
  have eqn (x:Ω):proper μ f g x=WilsonRootedUnnormalizedHearing.center a b c (fun _=>1) f g (fun v=>f v*g v) x:=by
    change (f x-a)*(g x-b)-c=f x*g x-a*g x-b*f x+(a*b-c)*1
    ring
  simp_rw [eqn]
  rw [WilsonRootedUnnormalizedHearing.measure κ a b c _ _ _ _ (integrable_const _)
    (hf.integrableC κ) (hg.integrableC κ) ((hf.mulC hg).integrableC κ)]
  simp only [integral_const,probReal_univ,one_smul,mul_one]
  change _=(∫x,f x*g x ∂κ)-(∫x,f x ∂κ)*(∫x,g x ∂κ)+((∫x,f x ∂κ)-a)*((∫x,g x ∂κ)-b)-c
  ring

end YM.Integration.WilsonMatrixOriginalGermReturnParts
