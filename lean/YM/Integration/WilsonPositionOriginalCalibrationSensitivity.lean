import YM.Integration.WilsonPositionPrescribedLift

/-! Quantitative dependence of the actual positioned field on the original
finite tested hierarchy of the one chosen position prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalCalibrationSensitivity
open Function Set Filter Maxwell Maxwell.Free XSpace XSpace.Normalize Extraction Table Spec PhysMS
open WilsonPositionPrescribedScreen WilsonPositionPrescribedFrame
open scoped Topology Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
  (F:Final C f S)(J:ℝ→tower S)(V:Store G)

def price (d:ℕ)(r:ℝ):ℝ:=
  ‖(V.survey d).purse (hierarchy F J d r)-(V.survey d).purse (reference G d)‖

theorem coordinates (lead:Leading F J)(d:ℕ):
    ∃c:ℝ,0<c ∧ ∀ᶠr in Trace.Pilot.trail,‖guide G d (correction F J V d r)‖≤c*price F J V d r:=by
  let D:=V.survey d
  have atZero:=((D.train (V.prepared d)).differentiableAt (by simp)).hasFDerivAt.isBigO_sub
  obtain ⟨c,hc,w⟩:=atZero.exists_pos
  refine ⟨c,hc,?_⟩
  have paid:= (WilsonPositionPrescribedScreen.warm F J lead V d).eventually w.bound
  filter_upwards [paid] with r hr
  change ‖guide G d (D.firstPass (V.prepared d) (hierarchy F J d r))‖≤c*_
  rw [D.guid,price]
  have base : D.route (V.prepared d) (D.purse (reference G d))=0:=D.ground0 (V.prepared d)
  simpa only [Fray.opening,base,sub_zero,D] using hr

private def response (C:Family G){d:ℕ}(b:Sec G d):MoveSpace G d→ₗ[ℝ] RG17.Free C d where
  toFun x:=(fields C.labels d).symm (((guide G d).symm x).val b)
  map_add' x y:=by rw [map_add];exact (fields C.labels d).symm.map_add _ _
  map_smul' c x:=by rw [map_smul];exact ((fields C.labels d).symm.toLinearMap.restrictScalars ℝ).map_smul c _

/-- Every actual lower component of the prescribed field is priced by the
signed physical finite survey on the same F, including any cap-six input. -/
theorem field (lead:Leading F J)(d:ℕ)(b:Sec G d):
    ∃c:ℝ,0≤c ∧ ∀ᶠr in Trace.Pilot.trail,
    ‖change F J V d r ((fields C.labels d).symm b)-(fields C.labels d).symm b‖≤c*price F J V d r:=by
  let A:MoveSpace G d→L[ℝ] RG17.Free C d:=(response C b).toContinuousLinearMap
  obtain ⟨c,hc,fee⟩:=coordinates F J V lead d
  refine ⟨‖A‖*c,mul_nonneg (ContinuousLinearMap.opNorm_nonneg A) hc.le,?_⟩
  filter_upwards [fee,(WilsonPositionPrescribedScreen.original F J lead V d).2] with r due accepted
  rw [leg F J V accepted.2.1]
  change ‖(fields C.labels d).symm (b+(correction F J V d r).val b)-(fields C.labels d).symm b‖≤_
  rw [map_add,add_sub_cancel_left,mul_assoc]
  apply le_trans _ (mul_le_mul_of_nonneg_left due (ContinuousLinearMap.opNorm_nonneg A))
  have exactValue:
      A (guide G d (correction F J V d r))=(fields C.labels d).symm ((correction F J V d r).val b):=by
    change (fields C.labels d).symm (((guide G d).symm (guide G d (correction F J V d r))).val b)=_
    rw [LinearEquiv.symm_apply_apply]
  rw [←exactValue]
  exact A.le_opNorm _

end YM.Integration.WilsonPositionOriginalCalibrationSensitivity
