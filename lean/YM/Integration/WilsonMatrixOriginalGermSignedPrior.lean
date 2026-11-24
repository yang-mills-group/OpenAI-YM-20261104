import YM.Integration.WilsonMatrixOriginalGermFourRawMarks

/-! The true old insertion has one backward observable on the complete UV
law after all four unnormalized marked rows and the old means are restored. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermSignedPrior
open MeasureTheory Lattice Wilson RG MergeProof.Accent OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox
open WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermTwoMarkJoint WilsonMatrixOriginalGermFourRawMarks
open WilsonRootedUnnormalizedHearing
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {m k N p:ℕ}

private theorem forward (H:History G) (n p j:ℕ) (f:Config G (H.S.side j p)→ℂ) {i:ℕ} (h:i≤j):
    gust H n p j f i h=pushTo H n p h f:=by
  induction h using Nat.decreasingInduction with
  | self=>rw [gust_base,pushTo_self]
  | of_succ l hl ih=>rw [gust_step H n p j f hl,Birth.push_first H n p hl,ih]

theorem charged (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (hW:Envelope W)
    (X:Config G (R.family.side N p)→ℂ) (hX:Envelope X):
    (∫V,inserted R lower upper W X V ∂Wilson.prior G (R.family.side m p))=
      (partition G (R.family.side N p) (R.family.path.β N p N):ℂ)*
        ∫U,X U*backTo R.family.path N p upper W U ∂scene R.family.path N p N:=by
  let Q:=R.family.path.rep N p N
  let f:Config G (R.family.side N p)→ℂ:=fun U=>Q.eval U • X U
  have good:Envelope Q.eval:=Q.envelope (R.makes.wilson.represents N p N (le_refl N)).good
  have usable:Integrable f (Wilson.prior G (R.family.side N p)):=((good.ofReal_env).mulC hX).integrableC _
  rw [(counted R lower upper W hW X hX).2]
  refine Eq.trans ?_ (OPE.Therm.invoice R.makes.wilson (le_refl N) (fun U=>X U*backTo R.family.path N p upper W U))
  calc
    _=∫V,pushTo R.family.path N p upper f V*W V ∂Wilson.prior G _:=by
      rw [←forward]
      exact integral_congr_ae (Filter.Eventually.of_forall fun V=>mul_comm _ _)
    _=∫U,f U*backTo R.family.path N p upper W U ∂Wilson.prior G _:=pushTo_dual R.family.path N p upper hW f usable
    _=_:=by
      apply integral_congr_ae (Filter.Eventually.of_forall fun U=>?_)
      dsimp only [f,Q]
      rw [Complex.real_smul,mul_assoc]
      rfl

def pair {X:Type*} (a b c:ℂ) (x y:X→ℂ) (u:X):ℂ:=(x u-a)*(y u-b)-c

theorem value (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (hW:Envelope W)
    (X Y:Config G (R.family.side N p)→ℂ) (hX:Envelope X) (hY:Envelope Y) (α β c:ℂ):
    let D:=inserted R lower upper W
    (∫V,center α β c (D (fun _=>1)) (D X) (D Y) (D (fun U=>X U*Y U)) V ∂Wilson.prior G _)/
      (partition G (R.family.side N p) (R.family.path.β N p N):ℂ)=
       ∫U,backTo R.family.path N p upper W U*pair α β c X Y U ∂scene R.family.path N p N:=by
  intro D
  let η:=Wilson.prior G (R.family.side m p)
  let μ:=scene R.family.path N p N
  let z:ℂ:=partition G (R.family.side N p) (R.family.path.β N p N)
  let a:Config G (R.family.side N p)→ℂ:=fun _=>1
  let j:Config G (R.family.side N p)→ℂ:=fun U=>X U*Y U
  let B:=backTo R.family.path N p upper W
  have eb:Envelope B:=backTo_env R.family.path N p upper hW
  have ea:Envelope a:=Envelope.compactC continuous_const
  have ej:Envelope j:=hX.mulC hY
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson (le_refl N)
  have s (f:Config G (R.family.side N p)→ℂ) (hf:Envelope f):
      Integrable (D f) η:=(counted R lower upper W hW f hf).1
  have t (f:Config G (R.family.side N p)→ℂ) (hf:Envelope f):
      Integrable (fun U=>f U*B U) μ:=(hf.mulC eb).integrableC _
  have rawPrice (f:Config G (R.family.side N p)→ℂ) (hf:Envelope f):
      (∫V,D f V ∂η)=z*(∫U,f U*B U ∂μ):=charged R lower upper W hW f hf
  have hi:=WilsonRootedUnnormalizedHearing.measure η α β c (D a) (D X) (D Y) (D j) (s a ea) (s X hX) (s Y hY) (s j ej)
  have hf:=WilsonRootedUnnormalizedHearing.measure μ α β c _ _ _ _ (t a ea) (t X hX) (t Y hY) (t j ej)
  have nz:z≠0:=Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
  change (∫V,center α β c (D a) (D X) (D Y) (D j) V ∂η)/z=∫U,B U*pair α β c X Y U ∂μ
  calc
    _=(∫U,center α β c (fun U=>a U*B U) (fun U=>X U*B U) (fun U=>Y U*B U) (fun U=>j U*B U) U ∂μ):=by
      rw [hi,hf,rawPrice j ej,rawPrice X hX,rawPrice Y hY,rawPrice a ea]
      field_simp
    _=_:=by
      apply integral_congr_ae (Filter.Eventually.of_forall fun U=>?_)
      dsimp only [a,j,center,pair]
      ring

end YM.Integration.WilsonMatrixOriginalGermSignedPrior
