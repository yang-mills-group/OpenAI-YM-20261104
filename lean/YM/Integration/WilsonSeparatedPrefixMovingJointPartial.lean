import YM.Integration.WilsonSeparatedPrefixMovingJointExpansion
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of the signed physical test before the native vote. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointPartial
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
def second:Point4→L[ℝ](Euclid×Point4):=ContinuousLinearMap.inr ℝ Euclid Point4
theorem situated (U:Euclid×Point4→ℝ)(smooth:ContDiff ℝ ∞ U)(n:ℕ)(ξ:Euclid)(x:Point4):
    iteratedFDeriv ℝ n (fun z=>U (ξ,z)) x =
    (iteratedFDeriv ℝ n U (ξ,x)).compContinuousLinearMap (fun _:Fin n=>second):=by
  let V:=fun t:Euclid×Point4=>U ((ξ,0)+t)
  have shift:ContDiff ℝ ∞ V:=smooth.comp (contDiff_const.add contDiff_id)
  have loc:(fun z:Point4=>U (ξ,z)) = V ∘ second:=funext fun z=>by simp [V,second]
  rw [loc,second.iteratedFDeriv_comp_right shift x (WithTop.coe_le_coe.mpr le_top)]
  congr 1
  simpa [V,second] using iteratedFDeriv_comp_add_left (𝕜:=ℝ) (f:=U) n (ξ,0) (second x)
theorem original (U:Euclid×Point4→ℝ)(smooth:ContDiff ℝ ∞ U)(n:ℕ):
    Continuous (fun a:Euclid×Point4=>iteratedFDeriv ℝ n (fun z=>U (a.1,z)) a.2):=by
  simp_rw [situated U smooth]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL (F:=ℝ) (fun _:Fin n=>second)).continuous.comp
    ((contDiff_infty.mp smooth n).continuous_iteratedFDeriv' )
end YM.Integration.WilsonSeparatedPrefixMovingJointPartial
