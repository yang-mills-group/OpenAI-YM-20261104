import YM.XSpace.Compat.Field
import YM.Further.FREE_COVARIANCE_KP.KP.Growth

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP.Profit
open YM.Further.FreeCovariance.KP
open YM.XSpace.Compat.KP
open Filter Set Function Metric Complex MeasureTheory VectorFourier
open scoped Topology ContDiff BigOperators InnerProductSpace FourierTransform Real
variable {f g:E4→ℂ}

lemma delivered (h : Profit f) : Integrable f := by
  have he := h.moment 0
  simp only [pow_zero,one_mul] at he
  exact he.mono' h.seen (Eventually.of_forall fun i=>le_rfl)

lemma owned : Profit (fun _:E4 => (0:ℂ)) := ⟨aestronglyMeasurable_const,fun k => by simp⟩

lemma scale (h : Profit f) (a:ℂ) : Profit (fun p:E4 => a*f p) := by
  refine ⟨aestronglyMeasurable_const.mul h.seen,fun j => ?_⟩
  convert! (h.moment j).const_mul ‖a‖ using 1; funext p; rw [norm_mul]; ring

lemma join (h : Profit f) (hg : Profit g) : Profit (fun p=> f p+g p) := by
  refine ⟨h.seen.add hg.seen,fun j => ((h.moment j).add (hg.moment j)).mono' ?_ ?_⟩
  · exact (continuous_norm.pow j).aestronglyMeasurable.mul (h.seen.add hg.seen).norm
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)).trans_eq (mul_add ..)

lemma bill_one (h : Profit f) (i : Axis) : Profit (fun p => turned p i * f p) := by
  have hf : Continuous (fun p => turned p i) := (london _).continuous
  refine ⟨hf.aestronglyMeasurable.mul h.seen,fun k => (h.moment (k+1)).mono' ?_ ?_⟩
  · exact (continuous_norm.pow k).aestronglyMeasurable.mul (hf.aestronglyMeasurable.mul h.seen).norm
  apply Eventually.of_forall
  intro p
  have hh : ‖turned p i‖ ≤ ‖p‖ := by
    rw [turned_at,norm_mul,norm_I, one_mul]
    simpa using abs_real_inner_le_norm (basis i) p
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_mul,pow_succ,mul_assoc]; gcongr

lemma continuous_feed (h : Profit f) : ContDiff ℝ ∞ (feed f) := by rw [← funext (shade_drops f)]; exact contDiff_fourierIntegral shade (fun n _ => h.moment n)

lemma rate (h : Profit f) (x:E4) (i:Axis) : Maxwell.grad i (feed f) x=feed (fun p => turned p i*f p) x := by
  have he : Integrable (fun p:E4=> ‖p‖*‖f p‖) := by simpa only [pow_one] using h.moment 1
  let J := fourierSMulRight shade f
  have hJ : Integrable J := by
    apply (he.const_mul (2*Real.pi*‖shade‖)).mono' h.seen.fourierSMulRight
    exact Eventually.of_forall fun i => (norm_fourierSMulRight_le shade f i).trans_eq (mul_assoc ..)
  unfold Maxwell.grad Analysis.D
  rw [← funext (shade_drops f), VectorFourier.fderiv_fourierIntegral shade h.delivered he,Real.fourierIntegral_continuousLinearMap_apply' hJ,shade_drops]
  congr 1
  funext p; rw [fourierSMulRight_apply,turned_at]; unfold shade height
  have hπ := Real.pi_ne_zero
  change (-(2*↑π*I)) * ((↑(- (2*π)⁻¹ *⟪p,basis i⟫_ℝ):ℂ)*f p) = _
  rw [real_inner_comm, basis_inner]; push_cast; have hp : (π:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hπ; field_simp

lemma timed (h : Profit f) (i:Axis) : Maxwell.grad i (retract f)=retract (fun p => turned p i*f p) := by
  unfold retract
  funext x
  unfold Maxwell.grad Analysis.D
  rw [show (fun a => (↑tally:ℂ)*feed f a)=(↑tally:ℂ) • feed f from rfl,fderiv_const_smul ((continuous_feed h).differentiable (by simp) x)]
  change (↑tally:ℂ) * Maxwell.grad i (feed f) x = _
  rw [rate h]
end YM.Further.FreeCovariance.KP.Profit

namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory VectorFourier
open scoped Topology ContDiff BigOperators InnerProductSpace FourierTransform Real

lemma water_rich : Profit water := by
  have hh : Measurable water := by unfold water breeze spine polar; fun_prop
  refine ⟨hh.aestronglyMeasurable,fun j => ?_⟩
  let h (p:E4) := ‖p‖^j*‖water p‖
  have ht p : ‖h p‖= ‖p‖^j * (polar 1 p * (‖p‖^2)⁻¹) := by
    unfold h
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    unfold water breeze spine
    congr 1
    rw [norm_mul,norm_inv,norm_real,norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (show 0<polar 1 p from Real.exp_pos _), abs_of_nonneg (sq_nonneg _)]
  let U := ball (0:E4) 2; let V : Set E4 := {p| 1 < ‖p‖}
  have hu : U ∪ V=univ := by
    ext x
    simp only [U,V,mem_union,mem_setOf_eq,mem_univ,mem_ball_zero_iff,iff_true]
    by_cases hp:‖x‖<2
    exact Or.inl hp
    exact Or.inr (by linarith)
  have hU : MeasurableSet U := measurableSet_ball
  have hV : MeasurableSet V := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hb : AEStronglyMeasurable h := (continuous_norm.pow j).aestronglyMeasurable.mul hh.aestronglyMeasurable.norm
  change Integrable h
  rw [← integrableOn_univ, ← hu,integrableOn_union]
  refine ⟨integrableOn_ball_of_norm_le_rpow (C:=2^j) (by simp [E4,YM.Axis]) (α:=((2:ℕ):ℝ)) (by norm_num [E4,YM.Axis]) ?_ hb,?_⟩
  · filter_upwards [ae_restrict_mem (μ:=volume) hU] with p hp
    rw [ht,Real.rpow_neg (norm_nonneg _),Real.rpow_natCast,← mul_assoc]
    gcongr
    apply mul_le_of_le_one_right (by positivity) (show polar 1 p≤1 from Real.exp_le_one_iff.mpr (by linarith [sq_nonneg ‖p‖])) |>.trans
    gcongr
    exact (mem_ball_zero_iff.mp hp).le
  obtain ⟨A,hA,H⟩ := (negative_quote (ι:=Unit) (5+j) (le_refl _) zero_lt_one zero_lt_one).quotes 0
  apply ((basin.const_mul (2^5*A)).integrableOn).mono' hb.restrict
  filter_upwards [ae_restrict_mem (μ:=volume) hV] with p hp
  let r := ‖p‖; have ht' : 1<r := hp; have hr : 0<r := zero_lt_one.trans ht'
  have he : polar 1 p≤ A*(r^(5+j))⁻¹ := by
    specialize H () p hp
    rw [norm_iteratedFDeriv_zero,breeze,norm_real,Real.norm_eq_abs,abs_of_pos (show 0<polar 1 p from Real.exp_pos _)] at H
    simpa only [Nat.cast_zero,sub_zero,zpow_neg,zpow_natCast] using H
  rw [ht]; change r^j*(_*_)≤ 2^5*A*((1+r)^5)⁻¹
  calc
    _ ≤ r^j*((A*(r^(5+j))⁻¹)*1) := by gcongr; exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ ht'.le)
    _ = A*(r^5)⁻¹ := by field_simp; ring
    _ ≤ _ := by
      have he := pow_le_pow_left₀ (a:=1+r) (by positivity) (show 1+r≤2*r by linarith) 5
      rw [mul_pow] at he
      field_simp
      linarith [mul_le_mul_of_nonneg_left he hA]

end YM.XSpace.Compat.KP
end
