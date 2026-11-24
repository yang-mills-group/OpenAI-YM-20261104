import YM.Pert.Triangle.Kernels
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
/-! Line estimates (before any ultraviolet subtraction). Separated mixed potentials are locally integrable with absolute IR overlap. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
noncomputable section

namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3

section radial
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma price {k} {f : E4→E} (h : Scale.Rays f k) : ∃ C>0, ∀ x, x ≠ 0 → ‖f x‖ ≤ C / ‖x‖^k := by
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:E4) 1).exists_bound_of_continuousOn (f:=f) (fun x hx => (h.diff (by rintro rfl; simp at hx)).continuousAt.continuousWithinAt)
  refine ⟨1+|C|,by positivity,?_⟩
  intro x hx
  have H := norm_pos_iff.mpr hx
  let w := ‖x‖⁻¹ • x
  have hw : w ∈ sphere (0:E4) 1 := by unfold w; rw [mem_sphere_iff_norm,sub_zero,norm_smul,Real.norm_of_nonneg (inv_nonneg_of_nonneg H.le),inv_mul_cancel₀ H.ne']
  have e : f x = ‖x‖⁻¹^k • f w := (h.stretch hx (inv_ne_zero H.ne')).symm
  have ht := hC w hw
  rw [e,norm_smul,Real.norm_of_nonneg (by positivity),inv_pow]
  grw [ht,← le_abs_self C]
  -- fragile maybe
  rw [div_eq_mul_inv,mul_comm]; gcongr; linarith
lemma rayMeasurable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {k} {f : E4→E} (h : Scale.Rays f k) : Measurable f :=
  measurable_of_continuousOn_compl_singleton 0 fun _ hx=> ContinuousAt.continuousWithinAt (h.diff hx |>.continuousAt)
end radial

lemma four_rank : Module.finrank ℝ E4 = 4 := by norm_num
lemma inv_power (x : ℝ) (k : ℕ) : x ^ (-(k:ℝ)) = (x^k)⁻¹ := by rw [Real.rpow_neg_natCast,zpow_neg,zpow_natCast]
lemma pay_outer (C : ℝ) : Integrable (fun w : E4 => C / (1 + ‖w‖)^6) := by
  have : Integrable (fun w : E4 => (1+‖w‖)^(-(6:ℕ) : ℝ)) := integrable_one_add_norm (by norm_num [four_rank])
  simpa only [inv_power,div_eq_mul_inv] using this.const_mul C

lemma flow_rays (a : Axis) : Scale.Rays (flow a) 3 where
  diff {w} hw := gradGradientSmooth hw a |>.neg
  stretch {w} hw := fun {r} hr=> by
     change r^3 • (-_) = -_
     rw [smul_neg]
     exact congrArg Neg.neg ((Scale.rays_green.step (basis a)).stretch hw hr)
lemma shifted_price (x : E4) (a : Axis) : ∃ C>0, ∀ᶠ w in cocompact E4, ‖flow a (w-x)‖ ≤ C / (1+‖w‖)^3 := by
  obtain ⟨C,hC,he⟩ := price (flow_rays a)
  refine ⟨8*C,by positivity,?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (2+2*‖x‖))] with w hw
  have h := norm_add_le (w-x) x
  rw [sub_add_cancel] at h
  have hw' : (1+‖w‖)/2 ≤ ‖w-x‖ := by change 2+2*‖x‖ ≤ ‖w‖ at hw; linarith
  have hwz := norm_nonneg w
  grw [he _ (norm_pos_iff.mp (by linarith : 0 < ‖w-x‖)), ←hw']
  field_simp
  linarith

lemma flowLocal (x : E4) (a : Axis) : LocallyIntegrable (fun w : E4=> flow a (w-x)) := by
  obtain ⟨C,hC,he⟩ := price (flow_rays a)
  have hi : LocallyIntegrable (flow a) := locallyIntegrable_of_norm_le_rpow (α:=((3:ℕ):ℝ)) (C:=C)
    (by norm_num [four_rank]) (by norm_num [four_rank]) ((volume.ae_ne 0).mono (fun w hw=>by rw [inv_power,←div_eq_mul_inv]; exact he w hw)) (rayMeasurable (flow_rays a)).aestronglyMeasurable
  let e := Homeomorph.addRight (-x)
  have : Measure.map e volume = (volume : Measure E4) := map_add_right_eq_self volume (-x)
  rw [←this,locallyIntegrable_map_homeomorph] at hi
  rw [show (fun w : E4=>flow a (w-x))=flow a ∘ e from by funext; exact congrArg _ (sub_eq_add_neg ..)]
  convert! hi
  /- maybe e = ? -/
lemma smallBall (x y : E4) (h : y≠x) (a : Axis) :
   ∃ K ∈ 𝓝 y, IsCompact K ∧ ContinuousOn (fun w : E4=> flow a (w-x)) K := by
  let r := ‖y-x‖/2
  have hr : 0<r := half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h))
  refine ⟨closedBall y r,closedBall_mem_nhds _ hr,isCompact_closedBall .., fun w hw=>?_⟩
  have q : w-x≠0 := fun e=> (show False from (not_le_of_gt (show r<‖x-y‖ from by rw [norm_sub_rev]; dsimp [r] at hr ⊢; linarith)) (by simpa only [mem_closedBall_iff_norm,sub_eq_zero.mp e] using hw))
  have he : ContinuousWithinAt (fun u=>u-x) (closedBall y r) w := continuousWithinAt_id.fun_sub continuousWithinAt_const
  exact ContinuousAt.comp_continuousWithinAt (f:=fun u=>u-x) (s:=closedBall y r) (flow_rays a |>.diff q).continuousAt he

lemma overlapLocal (a b : Axis) {x y : E4} (h : x≠y) : LocallyIntegrable (fun w:E4=>flow a (w-x) * flow b (w-y)) := by
  intro z
  by_cases he : z≠x
  · obtain ⟨K,hK,hC,hE⟩ := smallBall x z he a
    exact ⟨K,hK, IntegrableOn.continuousOn_mul hE ((flowLocal y b).integrableOn_isCompact hC) hC⟩
  obtain ⟨K,hK,hC,hE⟩ := smallBall y z (by rw [ne_eq,not_not] at he; rwa [he]) b
  exact ⟨K,hK, IntegrableOn.mul_continuousOn ((flowLocal x a).integrableOn_isCompact hC) hE hC⟩
lemma overlapPayable (a b : Axis) {x y : E4} (h : x ≠ y) : Integrable (fun w : E4 => flow a (w-x) * flow b (w-y)) := by
  apply integrable_iff_integrableAtFilter_cocompact.mpr
  have il := overlapLocal a b h
  refine ⟨?_,il⟩
  obtain ⟨C,hC,he⟩ := shifted_price x a
  obtain ⟨D,hD,hf⟩ := shifted_price y b
  let f := fun w:E4=> flow a (w-x)*flow b (w-y)
  have hm (g : Axis) (v : E4) : Measurable (fun w : E4=> flow g (w-v)) := Measurable.comp (f:=fun u=>u-v) (g:=flow g) (rayMeasurable (flow_rays g)) (measurable_id.sub_const _)
  let s := {w:E4 | ‖f w‖ ≤ (C*D) / (1+‖w‖)^6}
  have hms : MeasurableSet s := measurableSet_le ((hm a x).mul (hm b y)).norm (by fun_prop)
  have hhit : s ∈ cocompact E4 := (he.and hf).mono (fun w hw=> by
    apply (norm_mul_le ..).trans
    grw [hw.1,hw.2]
    rw [div_mul_div_comm,← pow_add])
  exact ⟨s,hhit, (pay_outer (C*D) |>.integrableOn (s:=s)).mono' il.aestronglyMeasurable.restrict (ae_restrict_of_forall_mem hms (fun w hw=>hw))⟩
lemma inputPayable (t m n : I3) {x y : E4} (h : x ≠ y) : Integrable (integralInput t m n x y) := by
  conv => enter [1, w]; rw [input_expand]
  apply integrable_finsetSum; intro a _
  exact integrable_finsetSum _ (fun b _=> Integrable.const_mul (overlapPayable a b h) _)

end YM.Pert.Triangle
