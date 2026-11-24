import YM.Integration.WilsonMatrixOriginalGermGram
import YM.Integration.WilsonInvariantActionAnchoredProfile
import YM.Integration.WilsonRootedUnnormalizedHearing

/-! Restoring the conditional pair at the exact two marked addresses returns
the full Wilson two-point log on the original law. The depot is the original
unnormalized push of their product, including every compatible spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermTwoMarkJoint
open MeasureTheory Lattice Wilson RG Source Labels MergeProof MergeProof.Accent
open Push.GridApprox RGComparison.Core16 Extra.Histories PhysicalNext.Repeat.Legato OPE.Therm
open WilsonInheritedRegisteredField WilsonMatrixOriginalGermGram WilsonInvariantActionPairPosterior
open private transfer from YM.Integration.WilsonInvariantActionAnchoredProfile
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {m N p:ℕ}

def raw (live:m≤N) (X:Config G (R.family.side N p)→ℂ) (V:Config G (R.family.side m p)):ℂ:=
  gust R.family.path N p N (fun U=>(R.family.path.rep N p N).eval U • X U) m live V

def asset (live:m≤N) (w:R.family.label 4) (o:Site (R.family.side m p)):Config G (R.family.side N p)→ℂ:=
  R.family.O N p w ((R.family.S.toDepth live p).embed o)

theorem denominator (live:m≤N) (X:Config G (R.family.side N p)→ℂ) (V:Config G (R.family.side m p)):
    ((R.family.path.rep N p m).eval V:ℂ)*actualTransport R.family (N:=N) X live V=raw R live X V:=by
  let q:ℝ:=(R.family.path.rep N p m).eval V
  have pos:0<q:=Multi.AxisShift.chosen_positive R.makes.wilson live V
  change (q:ℂ)*(q⁻¹ • raw R live X V)=_
  rw [Complex.real_smul,Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr pos.ne'),one_mul]

theorem filed (age:R.family.ref 4 ≤ m) (live:m≤N) (w:R.family.label 4) (o:Site (R.family.side m p))
    (V:Config G (R.family.side m p)):
    raw R live (asset R live w o) V=((R.family.path.rep N p m).eval V:ℂ)*field R.makes live w o V:=by
  rw [←denominator]
  exact congrArg (fun a:ℂ=>((R.family.path.rep N p m).eval V:ℂ)*a)
    (congrFun (WilsonInheritedRegisteredField.original R.makes live age w o) V)

theorem integrated (live:m≤N) (X:Config G (R.family.side N p)→ℂ) (hX:Envelope X):
    Integrable (raw R live X) (Wilson.prior G (R.family.side m p)) ∧
    (∫V,raw R live X V ∂Wilson.prior G (R.family.side m p))=
      (partition G (R.family.side N p) (R.family.path.β N p N):ℂ)*(∫U,X U ∂scene R.family.path N p N):=by
  let Q:=R.family.path.rep N p N
  have bare:Envelope Q.eval:=Q.envelope (R.makes.wilson.represents N p N (le_refl N)).good
  have f:Integrable (fun U=>Q.eval U • X U) (Wilson.prior G (R.family.side N p)):=
    ((bare.ofReal_env).mulC hX).integrableC _
  exact ⟨gust_live R.family.path N p N _ f live,(gust_sum R.family.path N p N _ f live).trans
    (OPE.Therm.invoice R.makes.wilson (le_refl N) X)⟩

theorem restored (T:Slices R.family.path.levels p) (age:R.family.ref 4 ≤ m) (live:m≤N) (w z:R.family.label 4)
    (o t:Site (R.family.side m p)):
    let X:=asset R live w o
    let Y:=asset R live z t
    let ν:=scene R.family.path N p m
    let f:=field R.makes live w o
    let g:=field R.makes live z t
    WilsonMatrixOriginalGermGram.moment (scene R.family.path N p N) X Y=
       (∫V,actualTransport R.family (N:=N) (fun U=>X U*Y U) live V-f V*g V ∂ν)+
       WilsonMatrixOriginalGermGram.moment ν f g:=by
  intro X Y ν f g
  have full:=WilsonInvariantActionPairPosterior.original R T live w z ((R.family.S.toDepth live p).embed o)
    ((R.family.S.toDepth live p).embed t)
  change _=(∫V,held R T live (fun U=>X U*Y U) V-held R T live X V*held R T live Y V ∂ν)+
    WilsonMatrixOriginalGermGram.moment ν (held R T live X) (held R T live Y) at full
  rw [transfer R T live,transfer R T live,transfer R T live] at full
  have one:actualTransport R.family (N:=N) X live=f:=WilsonInheritedRegisteredField.original R.makes live age w o
  have two:actualTransport R.family (N:=N) Y live=g:=WilsonInheritedRegisteredField.original R.makes live age z t
  rwa [one,two] at full

end YM.Integration.WilsonMatrixOriginalGermTwoMarkJoint
