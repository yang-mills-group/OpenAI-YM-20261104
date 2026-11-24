import YM.Integration.WilsonMatrixOriginalGermTwoMarkJoint
import YM.Integration.WilsonRegisteredFiledOccurrence

/-! A single physical insertion on an arbitrary intermediate date acts on
all four UV mark rows before the original push continues. The two proper
means and their connected subtraction are taken on the full Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermFourRawMarks
open MeasureTheory Lattice Wilson RG MergeProof.Accent OPE.Therm PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermTwoMarkJoint WilsonRootedUnnormalizedHearing
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {m k N p:ℕ}

def inserted (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ)
    (X:Config G (R.family.side N p)→ℂ):Config G (R.family.side m p)→ℂ:=
  gust R.family.path N p k (fun V=>W V*raw R upper X V) m lower

theorem counted (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (hW:Envelope W)
    (X:Config G (R.family.side N p)→ℂ) (hX:Envelope X):
    Integrable (inserted R lower upper W X) (Wilson.prior G (R.family.side m p)) ∧
    (∫V,inserted R lower upper W X V ∂Wilson.prior G (R.family.side m p))=
      ∫V,W V*raw R upper X V ∂Wilson.prior G (R.family.side k p):=by
  obtain ⟨iX,-⟩:=integrated R upper X hX
  have live:Integrable (fun V=>W V*raw R upper X V) (Wilson.prior G (R.family.side k p)):=
    iX.bdd_mul hW.meas.aestronglyMeasurable (Filter.Eventually.of_forall hW.cost.choose_spec)
  exact ⟨gust_live R.family.path N p k _ live lower,gust_sum R.family.path N p k _ live lower⟩

theorem vacuum (live:m≤N) (V:Config G (R.family.side m p)):
    raw R live (fun _=>1) V=((R.family.path.rep N p m).eval V:ℂ):=by
  rw [←denominator,actualTransport_const R.family R.makes (le_refl N) (1:ℂ) live V,mul_one]

def invoice (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ)
    (X Y:Config G (R.family.side N p)→ℂ):ℂ→ℂ:=
  let live:=lower.trans upper
  let rawRow:=raw R live
  let D:=inserted R lower upper W
  hearing (Wilson.prior G (R.family.side m p)) (rawRow (fun _=>1)) (rawRow X) (rawRow Y)
    (rawRow (fun U=>X U*Y U)) (D (fun _=>1)) (D X) (D Y) (D (fun U=>X U*Y U))

theorem charged (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (hW:Envelope W)
    (X Y:Config G (R.family.side N p)→ℂ) (hX:Envelope X) (hY:Envelope Y):
    let μ:=scene R.family.path N p N
    let η:=Wilson.prior G (R.family.side m p)
    let z:ℂ:=partition G (R.family.side N p) (R.family.path.β N p N)
    let D:=inserted R lower upper W
    HasDerivAt (invoice R lower upper W X Y) ((∫V,center (∫U,X U ∂μ) (∫U,Y U ∂μ) (moment μ X Y)
      (D (fun _=>1)) (D X) (D Y) (D (fun U=>X U*Y U)) V ∂η)/z) 0:=by
  intro μ η z D
  let l:=lower.trans upper
  let a:Config G (R.family.side N p)→ℂ:=fun _=>1
  let c:Config G (R.family.side N p)→ℂ:=fun U=>X U*Y U
  have one:Envelope a:=Envelope.compactC continuous_const
  have prod:Envelope c:=hX.mulC hY
  have funded:=integrated R l a one
  have fx:=integrated R l X hX
  have fy:=integrated R l Y hY
  have fj:=integrated R l c prod
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson (le_refl N)
  have amount:(∫V,raw R l a V ∂η)=z:=by
    rw [funded.2]
    change z*(∫ _U, (1:ℂ) ∂μ)=z
    simp
  have nonzero:z≠0:=Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
  have normalized (f : Config G (R.family.side N p)→ℂ) (hf:Envelope f):
      (∫V,raw R l f V ∂η)/z=∫U,f U ∂μ:=by
    rw [(integrated R l f hf).2]
    change (z*_)/z=_
    field_simp
    rfl
  have answer:=WilsonRootedUnnormalizedHearing.original η (raw R l a) (raw R l X) (raw R l Y) (raw R l c)
    (D a) (D X) (D Y) (D c) funded.1 fx.1 fy.1 fj.1 (counted R lower upper W hW a one).1
    (counted R lower upper W hW X hX).1 (counted R lower upper W hW Y hY).1 (counted R lower upper W hW c prod).1
    (amount.trans_ne nonzero)
  dsimp only at answer
  rw [amount,normalized X hX,normalized Y hY,normalized c prod] at answer
  exact answer

theorem observed (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (hW:Envelope W)
    (w z:R.family.label 4) (o t:Site (R.family.side m p)):
    let X:=asset R (lower.trans upper) w o
    let Y:=asset R (lower.trans upper) z t
    let μ:=scene R.family.path N p N
    let η:=Wilson.prior G (R.family.side m p)
    let D:=inserted R lower upper W
    HasDerivAt (invoice R lower upper W X Y) ((∫V,center (∫U,X U ∂μ) (∫U,Y U ∂μ) (moment μ X Y)
      (D (fun _=>1)) (D X) (D Y) (D (fun U=>X U*Y U)) V ∂η)/
        (partition G (R.family.side N p) (R.family.path.β N p N):ℂ)) 0:=
  charged R lower upper W hW _ _ (Envelope.compactC (R.family.continuousO ..))
    (Envelope.compactC (R.family.continuousO ..))

end YM.Integration.WilsonMatrixOriginalGermFourRawMarks
