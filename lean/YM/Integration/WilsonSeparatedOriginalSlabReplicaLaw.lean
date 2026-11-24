import YM.Integration.WilsonSeparatedOriginalSlabChildLaw
import YM.Integration.WilsonSeparatedOriginalReplicaScanner

/-! An old-cell translation preserves the entire positive Wilson law clamped
at the identity, including all true earlier gauge integrations and their common vacuum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaLaw
open Function MeasureTheory Set Lattice Wilson RG Source Extraction Push.GridApprox
open OPE.Therm PhysicalNext.Repeat.Legato RG05Readout.Records
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N per b:ℕ}(top:b+1 ≤ N)
local notation "A"=>Config G (R.family.side N per)
local notation "h"=>b.le_succ.trans top
local notation "μ"=>WilsonMacroscopicRichFlatPosteriorLaw.law R N per top (1:Config G (R.family.side b per))

theorem paid (f:A→ℂ)(regular:Continuous f):(∫W,f W ∂μ)=actualTransport R.family (N:=N) f h 1:=by
  letI:IsProbabilityMeasure (scene R.family.path N per N):=OPE.Therm.probability R.makes.wilson le_rfl
  have bill:Integrable f (scene R.family.path N per N):=regular.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have price:=WilsonMacroscopicRichFlatPosteriorLaw.reading R top le_rfl 1 f bill
  exact price.symm.trans (congrFun (WilsonSeparatedOriginalPosteriorTransport.realized R.makes le_rfl h f bill) 1)

theorem law (c:Site (R.family.side b per)):MeasurePreserving (pull 1 ((R.family.S.toDepth h per).embed c):A→A) μ μ:=by
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R top le_rfl (1:Config G (R.family.side b per))
  let t:A→A:=pull 1 ((R.family.S.toDepth h per).embed c)
  have continuous:Continuous t:=continuous_pull ..
  refine ⟨continuous.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let F:A→ℂ:=Complex.ofReal ∘ f
  have hc:Continuous F:=Complex.continuous_ofReal.comp f.continuous
  have equal:(∫W,(F ∘ t) W ∂μ)=∫W,F W ∂μ:=by
    rw [paid R top (F ∘ t) (hc.comp continuous),paid R top F hc]
    exact WilsonSeparatedOriginalSlabChildLaw.invariant R h c F hc
  change (∫W,f W ∂Measure.map t μ)=∫W,f W ∂μ
  rw [integral_map (φ:=t) (f:=fun W:A=>(f W:ℝ)) continuous.aemeasurable f.continuous.aestronglyMeasurable]
  change (∫W,f (t W) ∂μ)=∫W,f W ∂μ
  simpa only [F,comp_apply,integral_complex_ofReal,Complex.ofReal_inj] using equal

end YM.Integration.WilsonSeparatedOriginalSlabReplicaLaw
