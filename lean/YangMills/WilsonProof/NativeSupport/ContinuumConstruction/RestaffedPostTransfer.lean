import YM.Integration.WilsonOneFramePhysicalPivot
set_option maxHeartbeats 850000
set_option maxRecDepth 8192
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RestaffedPostTransfer
open Filter Function Set Matrix Lattice Wilson RG Source Extraction Table Spec RG17 Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMacroscopicRichTwoDatePivot (active)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}
theorem stress (lead : Leading F J) (owed : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (simple : G.Simple) (i j : Axis) (v : RG17.Free R.family 4)
    (enrolled : Tendsto (fun r : ℝ => (J r 4).symm (r^4 • F.sector.energy i j)) trail (𝓝 v)) :
    Tendsto (fun r : ℝ => (homogeneous F J Z r 4).symm (r^4 • F.sector.energy i j)) trail (𝓝 v) := by
  have atV := WilsonMacroscopicRichTwoDatePivot.field F J Z lead owed simple 4 v
  have van : Tendsto (fun r => ‖(J r 4).symm (r^4 • F.sector.energy i j) -
      active F J Z r 4 v‖) trail (𝓝 0) := by
    simpa using (enrolled.sub atV).norm
  obtain ⟨_,_,room⟩ := WilsonOneFramePhysicalPivot.original F J Z lead owed simple 4
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa using (tendsto_const_nhds (x:=(2:ℝ))).mul van)
  filter_upwards [room] with r use
  let A := active F J Z r 4
  have cost := (use ((J r 4).symm (r^4 • F.sector.energy i j) - A v)).2
  rw [map_sub,A.symm_apply_apply] at cost
  have paid : A.symm ((J r 4).symm (r^4 • F.sector.energy i j)) =
      (homogeneous F J Z r 4).symm (r^4 • F.sector.energy i j) := by
    change (homogeneous F J Z r 4).symm (J r 4 ((J r 4).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
  rwa [paid] at cost
end YM.Integration.RestaffedPostTransfer
end
