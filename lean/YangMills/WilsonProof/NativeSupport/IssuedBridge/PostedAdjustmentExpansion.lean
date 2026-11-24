import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAdjustmentFields
import YM.Integration.WilsonPositionScaleLawMeasuredAdjustment
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedAdjustmentExpansion
open YangMills YangMills.Wilson YM YM.Integration YM.Maxwell YM.Maxwell.Free WilsonLimitConstruction
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale MS MS.Land
open WilsonPositionHomogeneousCoefficients PostedBilateralAdjustment
open WilsonPositionScaleLawGuardHomePrint (tab)
open WilsonPositionScaleLawMeasuredWordExpansion (leg)
open Function Filter Set
open scoped Topology ContDiff BigOperators Classical
theorem original {g : GaugeGroup} (Z : WilsonPrescription g.core) (law : Warrant Z)
    (d q : ℕ) (v : (maxwellReference g).sector d) (out : (maxwellReference g).sector d →ₗ[ℂ] ℂ) :
    Tendsto (fun t : ℝ =>
      (out (value Z d t v) - ∑ k : Fin (q+1), (t : ℂ)^k.val *
        out (PowerSeries.coeff k.val (Measure.adjust Z.scheme Z.criterion d) v)) / (t : ℂ)^q)
      (𝓝[>] 0) (𝓝 0) := by
  let outN : Sec g.core d →ₗ[ℂ] ℂ := out
  let vN : Sec g.core d := v
  let eval : MoveSpace g.core d →ₗ[ℝ] (maxwellReference g).sector d :=
    { toFun x := ((guide g.core d).symm x).val v
      map_add' := by intro a b; rw [map_add]; rfl
      map_smul' := by intro a b; rw [map_smul]; rfl }
  let L := ((out.restrictScalars ℝ).comp eval).toContinuousLinearMap
  let x (t : ℝ) := guide g.core d (WilsonPositionHomogeneousRealization.correction Z d t)
  obtain ⟨A,_,est⟩ := WilsonPositionHomogeneousRealization.expansion Z d q
  apply squeeze_zero_norm' (a:=fun t : ℝ => (‖L‖ * A) * t)
  · filter_upwards [est,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t money inside
    have ht : 0 < t := inside
    have act : out (value Z d t v) = out v + L (x t) := by
      change outN (vN + (limb Z d t).val vN) = outN vN + outN (((guide g.core d).symm (x t)).val vN)
      rw [positive Z d ht,map_add]
      simp only [x,LinearEquiv.symm_apply_apply]
    have poly := congrArg outN (WilsonPositionScaleLawMeasuredAdjustment.polynomial Z law q t vN)
    have row : (∑ k : Fin (q+1), (t : ℂ)^k.val *
        out (PowerSeries.coeff k.val (Measure.adjust Z.scheme Z.criterion d) v)) =
        out v + L (tab Z d q t) := by
      rw [WilsonPositionScaleLawMeasuredWordExpansion.leg,map_sum] at poly
      simp only [map_smul,smul_eq_mul] at poly
      exact poly.symm.trans (map_add outN vN (eval (tab Z d q t)))
    have sub : out v + L (x t) - (out v + L (tab Z d q t)) = L (x t - tab Z d q t) := by
      rw [map_sub]; abel
    rw [act,row,sub,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    apply (div_le_iff₀ (pow_pos ht q)).mpr
    calc
      ‖L (x t - tab Z d q t)‖ ≤ ‖L‖ * ‖x t - tab Z d q t‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (A * t^(q+1)) := mul_le_mul_of_nonneg_left money (norm_nonneg _)
      _ = ‖L‖ * A * t * t^q := by rw [pow_succ]; ring
  · have conv : Tendsto (fun t : ℝ => (‖L‖ * A) * t) (𝓝 0) (𝓝 ((‖L‖ * A) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa only [mul_zero] using conv.mono_left nhdsWithin_le_nhds
end IssuedBridge.PostedAdjustmentExpansion
