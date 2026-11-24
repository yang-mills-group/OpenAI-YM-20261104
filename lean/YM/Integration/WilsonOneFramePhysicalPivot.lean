import YM.Integration.WilsonMacroscopicRichTwoDatePivot

/-! Both directions of the change from the original leading frame to the
final appointed frame, at each cap on the same physical radius tail. -/
set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOneFramePhysicalPivot
open Filter Function Set Matrix Lattice Wilson RG Source Extraction Table Spec RG17 Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMacroscopicRichTwoDatePivot (active)
open private cost clm_bound from YM.Integration.WilsonOrdinaryMixedDetectors
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}

theorem original (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (simple:G.Simple)(h:ℕ) :
    ∃ A:ℝ,0≤A ∧ ∀ᶠr in trail,∀ v:RG17.Free R.family h,
      ‖active F J Z r h v‖≤A*‖v‖ ∧ ‖(active F J Z r h).symm v‖≤2*‖v‖ := by
  classical
  let e:=Module.finBasis ℝ (RG17.Free R.family h)
  have cp:0≤cost e:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  let δ : ℝ := (2*(1+cost e))⁻¹
  have dp:0<δ := by dsimp [δ];positivity
  have room : cost e*δ ≤ 1/2 := by
    dsimp [δ]
    rw [←div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have before : ∀ᶠr in trail,∀i, ‖active F J Z r h (e i)-e i‖≤δ :=
    eventually_all.mpr fun i=>by
      have small := ((WilsonMacroscopicRichTwoDatePivot.field F J Z lead owed simple h (e i)).sub
        (tendsto_const_nhds (x:=e i))).norm
      have target:‖e i-e i‖<δ:=by simpa using dp
      filter_upwards [small.eventually (gt_mem_nhds target)] with r hr using hr.le
  obtain ⟨A,ap,funded⟩:=WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple h
  refine ⟨A,ap,?_⟩
  filter_upwards [before,funded] with r close forward v
  refine ⟨forward v,?_⟩
  let U:=active F J Z r h
  let D : RG17.Free R.family h →L[ℝ] RG17.Free R.family h :=
    U.toLinearMap.toContinuousLinearMap.restrictScalars ℝ - ContinuousLinearMap.id ℝ _
  have op : ‖D‖ ≤ 1/2 := (clm_bound e D dp.le close).trans room
  let u:=U.symm v
  have defect : ‖U u-u‖ ≤ (1/2:ℝ)*‖u‖ :=
    (D.le_opNorm u).trans (mul_le_mul_of_nonneg_right op (norm_nonneg _))
  have measured : U u=v:= U.apply_symm_apply _
  have triangle:=norm_le_norm_sub_add u (U u)
  rw [norm_sub_rev u (U u)] at triangle
  rw [measured] at defect triangle
  change ‖u‖ ≤ 2*‖v‖
  linarith only [defect,triangle]

end YM.Integration.WilsonOneFramePhysicalPivot
end
