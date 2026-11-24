import YM.Integration.WilsonSeparatedPrefixMovingJointVote
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of the signed physical test before the native vote. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointDerivatives
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
set_option backward.isDefEq.respectTransparency false in
theorem original (A:Ω→Point4→ℝ)(smooth:∀ξ,ContDiff ℝ ∞ (A ξ))
    (seen:∀(n:ℕ)(x:Point4),AEStronglyMeasurable (fun ξ=>iteratedFDeriv ℝ n (A ξ) x) μ)
    (bound:∀n:ℕ,∃b:Ω→ℝ,Integrable b μ∧∀ξ x,‖iteratedFDeriv ℝ n (A ξ) x‖≤b ξ):
    ∀(n:ℕ)(x:Point4),iteratedFDeriv ℝ n (fun z=>∫ξ,A ξ z ∂μ) x=∫ξ,iteratedFDeriv ℝ n (A ξ) x ∂μ:=by
  have inc (n:ℕ)(x:Point4):Integrable (fun ξ=>iteratedFDeriv ℝ n (A ξ) x) μ:=by
    obtain ⟨b,hb,h⟩:=bound n
    exact hb.mono' (seen n x) (ae_of_all _ fun ξ=>h ξ x)
  intro n
  induction n with
  | zero=>
    intro x
    let E:=continuousMultilinearCurryFin0 ℝ Point4 ℝ
    have value:Integrable (fun ξ=>A ξ x) μ:=E.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (inc 0 x)
    exact (E.symm.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm value).symm
  | succ n ih=>
    intro x
    let E:=continuousMultilinearCurryLeftEquiv ℝ (fun _:Fin (n+1)=>Point4) ℝ
    let U:=fun z ξ=>iteratedFDeriv ℝ n (A ξ) z
    let K:=fun z ξ=>fderiv ℝ (iteratedFDeriv ℝ n (A ξ)) z
    have invoice (z:Point4)(ξ:Ω):K z ξ=E (iteratedFDeriv ℝ (n+1) (A ξ) z):=by
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
      exact (E.apply_symm_apply _).symm
    obtain ⟨b,hb,cost⟩:=bound (n+1)
    have meet (ξ:Ω)(z:Point4):HasFDerivAt (U · ξ) (K z ξ) z:=by
      exact ((contDiff_infty.mp (smooth ξ) (n+1)).differentiable_iteratedFDeriv
        (m:=n) (by exact_mod_cast Nat.lt_succ_self n) z).hasFDerivAt
    have bought:HasFDerivAt (fun z=>∫ξ,U z ξ ∂μ) (∫ξ,K x ξ ∂μ) x:=by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=K) (s:=univ) (bound:=b) Filter.univ_mem
      · exact Filter.Eventually.of_forall (seen n)
      · exact inc n x
      · rw [show K x = fun ξ=>E (iteratedFDeriv ℝ (n+1) (A ξ) x) from funext (invoice x)]
        exact E.continuous.comp_aestronglyMeasurable (seen (n+1) x)
      · apply ae_of_all
        intro ξ z _
        simpa only [invoice,LinearIsometryEquiv.norm_map] using cost ξ z
      · exact hb
      · exact ae_of_all _ fun ξ z _=>meet ξ z
    have motion:(∫ξ,K x ξ ∂μ)=E (∫ξ,iteratedFDeriv ℝ (n+1) (A ξ) x ∂μ):=by
      simp_rw [invoice]
      exact ContinuousLinearEquiv.integral_comp_comm (μ:=μ) (𝕜:=ℝ) (E:=Point4 [×(n+1)]→L[ℝ] ℝ)
        (F:=Point4 →L[ℝ] Point4 [×n]→L[ℝ] ℝ) E.toContinuousLinearEquiv (fun ξ:Ω=>iteratedFDeriv ℝ (n+1) (A ξ) x)
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,funext ih,bought.fderiv,motion,E.symm_apply_apply]
end YM.Integration.WilsonSeparatedPrefixMovingJointDerivatives
