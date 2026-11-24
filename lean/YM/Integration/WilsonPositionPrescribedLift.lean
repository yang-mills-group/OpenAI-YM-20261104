import YM.Integration.WilsonPositionPrescribedFrame
import YM.Integration.WilsonPositionThermometerAtRefAssay

/-! Keep the old funded layout while inserting the physical solution of the
independent position equations. The field change has an actual bounded
operator norm on each true Maxwell grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedLift
open Function Filter Set Finset Metric MeasureTheory Extraction Table Spec OPE OPE.Orbits Climb PhysMS Maxwell Maxwell.Free
open Trace.Pilot XSpace XSpace.Normalize WilsonPositionPrescribedScreen WilsonPositionPrescribedFrame
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ→PhysMS.tower S) (V : Store G)

private def increment (C : Family G) (d : ℕ) : MoveSpace G d →ₗ[ℝ] (RG17.Free C d →L[ℂ] RG17.Free C d) where
  toFun u := ((Maxwell.Free.fields C.labels d).symm.toLinearMap.comp
    (((guide G d).symm u).val.comp (Maxwell.Free.fields C.labels d).toLinearMap)).toContinuousLinearMap
  map_add' u v := by
    ext x
    change (Maxwell.Free.fields C.labels d).symm (((guide G d).symm (u+v)).val ((Maxwell.Free.fields C.labels d) x)) = _
    rw [map_add]
    change (Maxwell.Free.fields C.labels d).symm (_+_) = _
    rw [map_add];rfl
  map_smul' a u := by
    ext x
    change (Maxwell.Free.fields C.labels d).symm (((guide G d).symm (a•u)).val ((Maxwell.Free.fields C.labels d) x)) = _
    rw [map_smul]
    change (Maxwell.Free.fields C.labels d).symm (a • _) = _
    exact ((Maxwell.Free.fields C.labels d).symm.toLinearMap.restrictScalars ℝ).map_smul a _

def field (d : ℕ) (r : ℝ) : RG17.Free C d →L[ℂ] RG17.Free C d :=
  (WilsonPositionPrescribedFrame.change F J V d r).toLinearMap.toContinuousLinearMap

private theorem bound (C : Family G) (d : ℕ) (u : MoveSpace G d) :
    let B := Pi.basisFun ℝ (Fin (Module.finrank ℝ (Change G d)))
    ‖increment C d u‖≤∑ i,|u i| * ‖increment C d (B i)‖ := by
  let B := Pi.basisFun ℝ (Fin (Module.finrank ℝ (Change G d)))
  let D := increment C d
  have parts : D u = ∑ i,(u i:ℂ) • D (B i) := by
    have h := congrArg D (B.sum_repr u)
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h.symm
  change ‖D u‖ ≤ _
  rw [parts]
  refine (norm_sum_le Finset.univ (fun i=>(u i:ℂ) • D (B i))).trans ?_
  apply Finset.sum_le_sum
  intro i _
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg _) (ContinuousLinearMap.opNorm_nonneg _))
  intro x
  rw [smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
  exact mul_le_mul_of_nonneg_left ((D (B i)).le_opNorm x) (abs_nonneg _)

theorem near (lead : PhysMS.Leading F J) (d : ℕ) :
    Tendsto (fun r=>‖field F J V d r-ContinuousLinearMap.id ℂ (RG17.Free C d)‖) Trace.Pilot.trail (𝓝 0) := by
  let A := increment C d
  let I := ContinuousLinearMap.id ℂ (RG17.Free C d)
  let u (r : ℝ) := guide G d (correction F J V d r)
  let B := Pi.basisFun ℝ (Fin (Module.finrank ℝ (Change G d)))
  have hu : Tendsto u Trace.Pilot.trail (𝓝 0) := (WilsonPositionPrescribedScreen.original F J lead V d).1
  have hs : Tendsto (fun r=>∑ i,|u r i| * ‖A (B i)‖) Trace.Pilot.trail (𝓝 0) := by
    have one (i) : Tendsto (fun r=>|u r i| * ‖A (B i)‖) Trace.Pilot.trail (𝓝 0) := by
      have hi : Tendsto (fun r=>u r i) Trace.Pilot.trail (𝓝 (0:ℝ)) := tendsto_pi_nhds.mp hu i
      simpa using (hi.abs.mul_const ‖A (B i)‖)
    simpa using tendsto_finsetSum Finset.univ (fun i _=>one i)
  have lim : Tendsto (fun r=>‖A (u r)‖) Trace.Pilot.trail (𝓝 0) :=
    squeeze_zero (fun _=>ContinuousLinearMap.opNorm_nonneg _) (fun r=>bound C d (u r)) hs
  apply lim.congr'
  filter_upwards [(WilsonPositionPrescribedScreen.original F J lead V d).2] with r good
  apply congrArg norm
  symm
  apply sub_eq_iff_eq_add.mpr
  ext x
  obtain ⟨v,rfl⟩ := (Maxwell.Free.fields C.labels d).symm.surjective x
  rw [add_apply,add_comm]
  change _=(Maxwell.Free.fields C.labels d).symm v+
     (Maxwell.Free.fields C.labels d).symm (((guide G d).symm (guide G d (correction F J V d r))).val
       ((Maxwell.Free.fields C.labels d) ((Maxwell.Free.fields C.labels d).symm v)))
  rw [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply,←map_add]
  exact WilsonPositionPrescribedFrame.leg F J V good.2.1 v

theorem fee (lead : PhysMS.Leading F J) (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail,‖field F J V d r‖≤‖ContinuousLinearMap.id ℂ (RG17.Free C d)‖+1 := by
  filter_upwards [(tendsto_order.mp (near F J V lead d)).2 1 zero_lt_one] with r hr
  linarith [norm_sub_norm_le (field F J V d r) (ContinuousLinearMap.id ℂ (RG17.Free C d))]

end YM.Integration.WilsonPositionPrescribedLift
