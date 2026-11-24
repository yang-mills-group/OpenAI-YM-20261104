import YM.Integration.WilsonSeparatedPrefixMovingJointKernel
import YM.Integration.WilsonSeparatedPrefixMovingJointDerivatives
import YM.Integration.WilsonSeparatedPrefixMovingJointIntegral
import YM.Integration.WilsonSeparatedPrefixMovingJointPartial
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of the signed physical test before the native vote. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointKernelRead
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
open WilsonSeparatedPrefixMovingJointKernel (ink)
def painted (φ:Rarity D)(χ:Rarity E)(S:𝓢(Euclid,ℂ))(p:Point4)(ξ:Euclid)(q:Point4):ℝ:=
  ∑c:Bool,∑d:Bool,ink φ χ S p c d ξ q
theorem whole (φ:Rarity D)(χ:Rarity E)(S:𝓢(Euclid,ℂ))(p:Point4)(hχ:ContDiff ℝ ∞ χ.ψ.val):
    ContDiff ℝ ∞ (fun a:Euclid×Point4=>painted φ χ S p a.1 a.2):=by
  exact ContDiff.sum fun c _=>ContDiff.sum fun d _=>WilsonSeparatedPrefixMovingJointKernel.smooth φ χ S p c d hχ
theorem expense (φ:Rarity D)(χ:Rarity E)(S:𝓢(Euclid,ℂ))(p:Point4)(hχ:ContDiff ℝ ∞ χ.ψ.val)(n:ℕ):
    ∃B:ℝ,0≤B∧∀ξ q,‖iteratedFDeriv ℝ n (painted φ χ S p ξ) q‖≤B*((1+‖ξ‖^n)*‖S ξ‖):=by
  choose B positive bought using fun c d=>WilsonSeparatedPrefixMovingJointKernel.original φ χ S p c d hχ n
  refine ⟨∑c:Bool,∑d:Bool,B c d,Finset.sum_nonneg fun c _=>Finset.sum_nonneg fun d _=>positive c d,?_⟩
  intro ξ q
  have single (c d:Bool):ContDiff ℝ ∞ (ink φ χ S p c d ξ):=
    (WilsonSeparatedPrefixMovingJointKernel.smooth φ χ S p c d hχ).comp (contDiff_const.prodMk contDiff_id)
  have pair (c:Bool):ContDiff ℝ ∞ (fun z=>∑d:Bool,ink φ χ S p c d ξ z):=ContDiff.sum fun d _=>single c d
  change ‖iteratedFDeriv ℝ n (fun z=>∑c:Bool,∑d:Bool,ink φ χ S p c d ξ z) q‖≤_
  rw [iteratedFDeriv_fun_sum_apply (fun c _=>(contDiff_infty.mp (pair c) n).contDiffAt)]
  simp_rw [iteratedFDeriv_fun_sum_apply (fun d _=>(contDiff_infty.mp (single _ d) n).contDiffAt)]
  simp_rw [Finset.sum_mul]
  apply (norm_sum_le ..).trans
  exact Finset.sum_le_sum fun c _=>(norm_sum_le ..).trans (Finset.sum_le_sum fun d _=>bought c d ξ q)
theorem declared (φ:Rarity D)(ψ χ:Rarity E)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),S=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ ∧ (∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖))∧
    ∀(p:Point4)(n:ℕ)(q:Point4),Integrable (fun ξ=>iteratedFDeriv ℝ n (painted φ χ S p ξ) q)∧
      iteratedFDeriv ℝ n (fun z=>φ.ψ.val p*ψ.ψ.val (z-p)) q =
        ∫ξ,iteratedFDeriv ℝ n (painted φ χ S p ξ) q:=by
  obtain ⟨S,identity,wage,ear⟩:=WilsonSeparatedPrefixMovingJointExpansion.declared φ ψ χ hψ window
  refine ⟨S,identity,wage,?_⟩
  intro p n q
  have old:=whole φ χ S p hχ
  have terms (ξ:Euclid):ContDiff ℝ ∞ (painted φ χ S p ξ):=old.comp (contDiff_const.prodMk contDiff_id)
  have seen (m:ℕ)(z:Point4):AEStronglyMeasurable (fun ξ=>iteratedFDeriv ℝ m (painted φ χ S p ξ) z) volume:=
    ((WilsonSeparatedPrefixMovingJointPartial.original _ old m).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have charges (m:ℕ):∃b:Euclid→ℝ,Integrable b∧∀ξ z,‖iteratedFDeriv ℝ m (painted φ χ S p ξ) z‖≤b ξ:=by
    obtain ⟨B,_,due⟩:=expense φ χ S p hχ m
    exact ⟨_,(wage m).const_mul B,due⟩
  obtain ⟨b,hb,atQ⟩:=charges n
  constructor
  · exact hb.mono' (seen n q) (ae_of_all _ fun ξ=>atQ ξ q)
  · rw [show (fun z=>φ.ψ.val p*ψ.ψ.val (z-p))=(fun z=>∫ξ,painted φ χ S p ξ z) from funext (ear p)]
    exact WilsonSeparatedPrefixMovingJointDerivatives.original (μ:=MeasureTheory.volume) (painted φ χ S p) terms seen charges n q
theorem original (φ:Rarity D)(ψ χ:Rarity E)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),(∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖))∧
    ∀(p:Point4)(n:ℕ)(q:Point4),Integrable (fun ξ=>iteratedFDeriv ℝ n (painted φ χ S p ξ) q)∧
      iteratedFDeriv ℝ n (fun z=>φ.ψ.val p*ψ.ψ.val (z-p)) q =
        ∫ξ,iteratedFDeriv ℝ n (painted φ χ S p ξ) q:=by
  obtain ⟨S,_,data⟩:=declared φ ψ χ hψ hχ window
  exact ⟨S,data⟩
end YM.Integration.WilsonSeparatedPrefixMovingJointKernelRead
