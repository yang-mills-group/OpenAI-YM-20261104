import YM.Integration.WilsonSeparatedPrefixMovingJointProfile
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! A single continuous separated expansion of the actual translated compact exterior field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointSpectrum
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingAddressInk (writer)

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap RealInnerProductSpace
abbrev Euclid:=EuclideanSpace ℝ Axis
def physical:Euclid≃L[ℝ]Point4:=PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)
def profile (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val):𝓢(Euclid,ℂ):=by
  let f:Euclid→ℂ:=fun x=>(φ.ψ.val (physical x):ℂ)
  have cmp:HasCompactSupport f:=by
    let ball:=Metric.closedBall (0:Point4) φ.radius
    have compact:IsCompact (physical ⁻¹' ball):=
      physical.toHomeomorph.isProperMap.isCompact_preimage (isCompact_closedBall ..)
    apply compact.of_isClosed_subset (isClosed_tsupport f)
    apply closure_minimal _ (isClosed_closedBall.preimage physical.continuous)
    intro x hx
    apply φ.support
    apply subset_closure
    change φ.ψ.val (physical x)≠0
    change (φ.ψ.val (physical x):ℂ)≠0 at hx
    exact_mod_cast hx
  exact cmp.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (hf.comp physical.contDiff))
def character (ξ:Euclid)(q:Point4):ℂ:=Complex.exp (((2*Real.pi*inner ℝ ξ (physical.symm q):ℝ):ℂ)*Complex.I)
theorem modulus (ξ:Euclid)(q:Point4):‖character ξ q‖=1:=by
  unfold character
  rw [Complex.norm_exp];simp
theorem pair (ξ:Euclid)(p q:Point4):
    character ξ (q-p)=character ξ (-p)*character ξ q:=by
  unfold character
  rw [←Complex.exp_add,map_sub,map_neg,inner_sub_right,inner_neg_right]
  push_cast;ring_nf
def transformed (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val):𝓢(Euclid,ℂ):=𝓕 (profile φ hf)
theorem declared (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val):
    ∃ spectrum:𝓢(Euclid,ℂ),spectrum=transformed φ hf ∧ (∀k:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^k)*‖spectrum ξ‖)) ∧
      ∀p q:Point4,(φ.ψ.val (q-p):ℂ)=∫ξ:Euclid,spectrum ξ*(character ξ (-p)*character ξ q):=by
  let F:=profile φ hf
  let spectrum:𝓢(Euclid,ℂ):=𝓕 F
  refine ⟨spectrum,rfl,?_,?_⟩
  · intro k
    apply (spectrum.integrable.norm.add (spectrum.integrable_pow_mul volume k)).congr
    filter_upwards [] with ξ
    simp only [Pi.add_apply,add_mul,one_mul]
  intro p q
  have inv: (𝓕⁻ spectrum) (physical.symm (q-p))=F (physical.symm (q-p)):=by
    rw [show (𝓕⁻ spectrum:𝓢(Euclid,ℂ))=F from FourierTransform.fourierInv_fourier_eq _]
  have basis:F (physical.symm (q-p))=(φ.ψ.val (q-p):ℂ):=by
    change (φ.ψ.val (physical (physical.symm (q-p))):ℂ)=_;rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [←basis,←inv]
  change ((𝓕⁻ spectrum:𝓢(Euclid,ℂ)):Euclid→ℂ) (physical.symm (q-p))=_
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with ξ
  change character ξ (q-p)*spectrum ξ=_
  rw [pair,mul_comm]
theorem original (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val):
    ∃ spectrum:𝓢(Euclid,ℂ),(∀k:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^k)*‖spectrum ξ‖)) ∧
      ∀p q:Point4,(φ.ψ.val (q-p):ℂ)=∫ξ:Euclid,spectrum ξ*(character ξ (-p)*character ξ q):=by
  obtain ⟨S,_,data⟩:=declared φ hf
  exact ⟨S,data⟩
end YM.Integration.WilsonSeparatedPrefixMovingJointSpectrum
