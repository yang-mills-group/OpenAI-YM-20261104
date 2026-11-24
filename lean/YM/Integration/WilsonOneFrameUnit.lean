import YM.Integration.WilsonOneFramePhysicalPivot

/-! Both directions of the change from the original leading frame to the
final appointed frame, at each cap on the same physical radius tail. -/
set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOneFrameUnit
open Filter Function Set Matrix Lattice Wilson RG Source Extraction Table Spec RG17 Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMacroscopicRichTwoDatePivot (active)
open private cost clm_bound from YM.Integration.WilsonOrdinaryMixedDetectors
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}


theorem original (lead : Leading F J) (owed : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (simple : G.Simple) (d : ℕ) :
    Tendsto (fun r => (homogeneous F J Z r d).symm (S.unit d))
      trail (𝓝 ((Bel R.family.book).unit d)) := by
  let v := (Bel R.family.book).unit d
  have enrolled : Tendsto (fun r => (J r d).symm (S.unit d)) trail (𝓝 v) := by
    apply (tendsto_const_nhds (x:=v)).congr'
    filter_upwards [lead.unit d] with r h
    rw [←h,LinearEquiv.symm_apply_apply]
  have moved := WilsonMacroscopicRichTwoDatePivot.field F J Z lead owed simple d v
  have van : Tendsto (fun r => ‖(J r d).symm (S.unit d) - active F J Z r d v‖) trail (𝓝 0) := by
    simpa using (enrolled.sub moved).norm
  obtain ⟨_,_,room⟩ := WilsonOneFramePhysicalPivot.original F J Z lead owed simple d
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa using (tendsto_const_nhds (x:=(2:ℝ))).mul van)
  filter_upwards [room] with r use
  let A := active F J Z r d
  have cost := (use ((J r d).symm (S.unit d) - A v)).2
  rw [map_sub,A.symm_apply_apply] at cost
  have same : A.symm ((J r d).symm (S.unit d)) = (homogeneous F J Z r d).symm (S.unit d) := by
    change (homogeneous F J Z r d).symm (J r d ((J r d).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
  rwa [same] at cost

end YM.Integration.WilsonOneFrameUnit
end
