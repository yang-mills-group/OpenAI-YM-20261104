import YM.Integration.WilsonSeparatedPrefixMovingJointWaveBudget
import YM.Integration.WilsonSeparatedPrefixMovingJointIntegral
import YM.Integration.WilsonSeparatedPrefixMovingJointPartial
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of the signed physical test before the native vote. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointKernel
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


open MeasureTheory Set
open scoped ContDiff
variable {Ω:Type*}[MeasurableSpace Ω]{μ:Measure Ω}
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWaves (sheet wave)
open WilsonSeparatedPrefixMovingJointExpansion (angle coefficient coin)
open WilsonSeparatedPrefixMovingJointSpectrum (physical)
open WilsonSeparatedPrefixMovingJointIntegral (growth multiplier)
open scoped SchwartzMap
variable {E:ℕ}
def ink (φ:Rarity D)(χ:Rarity E)(S:𝓢(Euclid,ℂ))(p:Point4)(c d:Bool)(ξ:Euclid)(q:Point4):ℝ:=
  (coefficient (S ξ) c d * (sheet φ (angle ξ) c).ψ.val p) • (sheet χ (angle ξ) d).ψ.val q
theorem smooth (φ:Rarity D)(χ:Rarity E)(S:𝓢(Euclid,ℂ))(p:Point4)(c d:Bool)(hχ:ContDiff ℝ ∞ χ.ψ.val):
    ContDiff ℝ ∞ (fun a:Euclid×Point4=>ink φ χ S p c d a.1 a.2):=by
  have priced:ContDiff ℝ ∞ (fun a:Euclid×Point4=>S a.1):=(S.smooth ⊤).comp contDiff_fst
  have angleF:ContDiff ℝ ∞ (fun a:Euclid×Point4=>angle a.1 a.2):=by
    change ContDiff ℝ ∞ (fun a:Euclid×Point4=>(2*Real.pi)*inner ℝ a.1 (physical.symm a.2))
    exact contDiff_const.mul (contDiff_fst.inner ℝ (physical.symm.contDiff.comp contDiff_snd))
  have angleN:ContDiff ℝ ∞ (fun a:Euclid×Point4=>angle a.1 p):=by
    change ContDiff ℝ ∞ (fun a:Euclid×Point4=>(2*Real.pi)*inner ℝ a.1 (physical.symm p))
    exact contDiff_const.mul (contDiff_fst.inner ℝ contDiff_const)
  have cum:ContDiff ℝ ∞ (fun a:Euclid×Point4=>coefficient (S a.1) c d):=by
    cases c <;> cases d <;> simp only [coefficient]
    · exact Complex.reCLM.contDiff.comp priced
    · exact (Complex.imCLM.contDiff.comp priced).neg
    · exact Complex.imCLM.contDiff.comp priced
    · exact Complex.reCLM.contDiff.comp priced
  exact (cum.mul (contDiff_const.mul ((WilsonSeparatedPrefixMovingJointWaves.smooth c).comp angleN))).smul
    ((hχ.comp contDiff_snd).mul ((WilsonSeparatedPrefixMovingJointWaves.smooth d).comp angleF))
theorem original (φ:Rarity D)(χ:Rarity E)(S:𝓢(Euclid,ℂ))(p:Point4)(c d:Bool)(hχ:ContDiff ℝ ∞ χ.ψ.val)(n:ℕ):
    ∃B:ℝ,0≤B ∧ ∀ξ q,‖iteratedFDeriv ℝ n (ink φ χ S p c d ξ) q‖≤B*((1+‖ξ‖^n)*‖S ξ‖):=by
  obtain ⟨A,hA,wa⟩:=WilsonSeparatedPrefixMovingJointWaveBudget.original χ hχ n
  have mp:0 ≤ multiplier:=by unfold multiplier;positivity
  refine ⟨‖φ.ψ.val p‖*A*multiplier^n,by positivity,?_⟩
  intro ξ q
  have source:ContDiff ℝ ∞ (sheet χ (angle ξ) d).ψ.val:=hχ.mul ((WilsonSeparatedPrefixMovingJointWaves.smooth d).comp (angle ξ).contDiff)
  rw [show ink φ χ S p c d ξ = fun z=>(coefficient (S ξ) c d*(sheet φ (angle ξ) c).ψ.val p) • (sheet χ (angle ξ) d).ψ.val z from rfl,
    iteratedFDeriv_const_smul_apply' ((contDiff_infty.mp source n).contDiffAt),norm_smul,norm_mul]
  have waveB:‖wave c (angle ξ p)‖≤1:=by cases c <;> simp only [WilsonSeparatedPrefixMovingJointWaves.wave,Real.norm_eq_abs] <;>
    first | exact Real.abs_sin_le_one _ | exact Real.abs_cos_le_one _
  have nearB:‖(sheet φ (angle ξ) c).ψ.val p‖≤‖φ.ψ.val p‖:=by
    change ‖φ.ψ.val p*wave c (angle ξ p)‖≤_
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left waveB (norm_nonneg (φ.ψ.val p))
  calc
    _≤(‖S ξ‖*‖φ.ψ.val p‖)*(A*(1+‖angle ξ‖)^n):=by
      exact mul_le_mul (mul_le_mul (coin ..) nearB (norm_nonneg _) (norm_nonneg _))
        (wa _ d n le_rfl q) (norm_nonneg _) (by positivity)
    _≤(‖S ξ‖*‖φ.ψ.val p‖)*(A*(multiplier^n*(1+‖ξ‖^n))):=by gcongr;exact growth n ξ
    _= _:=by ring
end YM.Integration.WilsonSeparatedPrefixMovingJointKernel
