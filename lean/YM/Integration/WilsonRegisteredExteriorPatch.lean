import YM.Integration.WilsonHeldExteriorLaw
import YM.Integration.WilsonHeldRetainedAction

/-! Both the retained local action and the physical saved-link experiment vary
the tails in the declared support against the same original compact Haar. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredExteriorPatch
open Function Set MeasureTheory Lattice RG Wilson WilsonHeldExteriorLaw
open private total from YM.Integration.WilsonHeldExteriorLaw
open scoped Classical
variable {G:Gauge}{n:Side}
theorem original (S:Support n)(ext U:Config G n):
    OriginalMarkedConditionalAction.patch S ext U=
    (cut G (exterior S)).symm (((cut G (exterior S)) ext).1,((cut G (exterior S)) U).2):=by
  apply (cut G (exterior S)).injective
  rw [MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · funext e
    change (if e.val.1∈S then U e.val else ext e.val)=ext e.val
    exact if_neg e.property
  · funext e
    change (if e.val.1∈S then U e.val else ext e.val)=U e.val
    exact if_pos (Classical.not_not.mp e.property)

theorem measured {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
    [MeasurableSpace E][BorelSpace E][SecondCountableTopology E](S:Support n)(ext:Config G n)(f:Config G n→E)(ef:Envelope f):
    (∫U,f (OriginalMarkedConditionalAction.patch S ext U) ∂prior G n)=
      marginal (exterior S) f (((cut G (exterior S)) ext).1):=by
  let A:=exterior S
  let ξ:=OriginalMarkedConditionalAction.patch S ext
  have bound:Envelope (fun U=>f (ξ U)):=by
    obtain ⟨K,cap⟩:=ef.cost
    exact ⟨ef.meas.comp (OriginalMarkedConditionalAction.measurable_patch S ext),K,fun U=>cap _⟩
  have data:Integrable (fun U=>f (ξ U)) (prior G n):=by
    obtain ⟨K,cap⟩:=bound.cost
    exact Integrable.of_bound bound.meas.aestronglyMeasurable K (Filter.Eventually.of_forall fun U=>by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using cap U)
  rw [←total A data]
  simp [marginal,ξ,original,A]
end YM.Integration.WilsonRegisteredExteriorPatch
