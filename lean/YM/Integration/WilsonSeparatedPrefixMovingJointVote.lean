import YM.Integration.WilsonSeparatedPrefixMovingJointExpansion
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Pass a signed integral of genuine local angular pages through any original filed vote. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointVote
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


open MeasureTheory
variable {Ω:Type*}[MeasurableSpace Ω]{μ:Measure Ω}
def inspect (i:Knob D)(z:Chamber):Sleeves D→L[ℝ]ℝ:=
  (ContinuousMap.evalCLM ℝ z).comp (ContinuousLinearMap.proj i)
theorem original (V:Volume D)(F:Ω→Volume D)
    (absolute:Integrable (fun ξ=>(F ξ).val) μ)
    (lanes:∀(i:Knob D)(z:Chamber),V.val i z=∫ξ,(F ξ).val i z ∂μ):
    ∀L:Vote D,Integrable (fun ξ=>L (F ξ)) μ ∧ L V=∫ξ,L (F ξ) ∂μ:=by
  have whole:V.val=∫ξ,(F ξ).val ∂μ:=by
    funext i
    ext z
    have observed:inspect i z (∫ξ,(F ξ).val ∂μ)=∫ξ,inspect i z ((F ξ).val) ∂μ:=
      ((inspect i z).integral_comp_comm absolute).symm
    exact (lanes i z).trans observed.symm
  intro L
  obtain ⟨M,same,_⟩:=exists_extension_norm_eq (LinearMap.range (write D)) L
  have hfun:(fun ξ=>L (F ξ))=(fun ξ=>M (F ξ).val):=funext fun ξ=>(same (F ξ)).symm
  rw [hfun,←same,whole]
  exact ⟨M.integrable_comp absolute,(M.integral_comp_comm absolute).symm⟩
end YM.Integration.WilsonSeparatedPrefixMovingJointVote
