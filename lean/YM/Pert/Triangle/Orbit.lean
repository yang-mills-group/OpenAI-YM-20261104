import YM.Pert.Triangle.Estimate
/-!
Spherical transfer identities for the continuum expression. The epsilon-weighted
determinant at large radius is independent of the direction; the convolution
of the two gradient legs only supplies an off-site scalar.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section

namespace YM.Pert.Triangle
open Maxwell Analysis Set Function Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Matrix
local notation "I3" => Fin 3

lemma flow_dot {x y: E4} (hx:x≠0) (hy:y≠0) :
    ∑ a, flow a x * flow a y = (4*normal^2 * (‖x‖^2)⁻¹^2 * (‖y‖^2)⁻¹^2) * inner ℝ y x := by
  unfold flow
  simp only [PiLp.inner_apply,RCLike.inner_apply,Finset.mul_sum]
  simp_rw [first_Green hx, first_Green hy]
  exact Finset.sum_congr rfl (fun _ _ => by simp;ring)
lemma overlap_rigid (K : E4 ≃ₗᵢ[ℝ] E4) {x y:E4} (h : x≠y) : overlap (K x) (K y) = overlap x y := by
  unfold overlap
  conv_lhs => rw [← show Measure.map K volume = volume from K.measurePreserving.map_eq]
  erw [K.toHomeomorph.measurableEmbedding.integral_map]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne x, volume.ae_ne y] with w hx hy
  dsimp
  have e (z:E4) (hz : w≠z) : K w - K z≠0 := (sub_ne_zero.mpr (K.injective.ne hz))
  rw [flow_dot (e x hx) (e y hy), ←K.map_sub, ←K.map_sub, LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map, K.inner_map_map,flow_dot (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)]
lemma overlap_shift (x y:E4) : overlap x y = overlap (x-y) 0 := by
  let f(w : E4) := ∑ a, flow a (w-(x-y))*flow a w
  calc
     _ = ∫ w:E4, f (w-y) := (integral_congr_ae (Eventually.of_forall fun w:E4=> by dsimp[f]; congr 1; funext a; rw [show w-y-(x-y)=w-x by abel]))
     _ = ∫ w:E4, f w := integral_sub_right_eq_self f y
     _ = _ := by simp [overlap,f]
lemma overlap_energy (x : E4) {a:ℝ} (ha:0<a) : a^2 * overlap (a • x) 0 = overlap x 0 := by
  let f (w : E4) := ∑ i, flow i (w - a • x) * flow i w
  have h : a^6 * ∫ w, f (a•w) ∂volume = a^6 * ((a^4)⁻¹ * ∫ w, f w ∂volume) := congrArg _ (by simpa only [smul_eq_mul,four_rank] using Measure.integral_comp_smul_of_nonneg (hR:=ha.le) volume f a)
  rw [← integral_const_mul (r:=a^6)] at h
  unfold overlap; simp only [sub_zero]
  calc _ = (∫ w,a^6 * f (a•w) ∂volume) := by
              change a^2 * ∫ w, f w = _
              rw [h]; field_simp
       _ = _ := integral_congr_ae ((volume.ae_ne 0).mono (fun w hw=>by
      dsimp only [f]
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>by
        by_cases he : w=x
        · rw [he]
          have hi := flow_odd 0 i
          rw [neg_zero] at hi
          have hh : flow i 0=0 := by linarith [hi]
          simp [hh]
        rw [←smul_sub,show ∀ p q:ℝ,a^6*(p*q) = (a^3*p)*(a^3*q) from fun _ _=>by ring,flow_energy i ha.ne' (sub_ne_zero.mpr he),flow_energy i ha.ne' hw]))
lemma overlap_rule {x y : E4} (h : x≠y) : overlap x y = overlap along 0 / ‖x-y‖^2 := by
  rw [overlap_shift]
  let a := ‖x-y‖
  have ha : 0<a := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  let v := a • along
  have hv : ‖v‖ = a := by dsimp [v]; rw [norm_smul,along_norm,Real.norm_of_nonneg ha.le,mul_one]
  let K := Submodule.reflection (ℝ ∙ (x-y-v))ᗮ
  have he := overlap_rigid K (x:=x-y) (y:=(0:E4)) (sub_ne_zero.mpr h)
  rw [show K (x-y) = v from Submodule.reflection_sub hv.symm,K.map_zero] at he
  rw [← he,eq_div_iff (pow_ne_zero 2 ha.ne')]
  exact (mul_comm ..).trans (overlap_energy along ha)
lemma overlap_ref : overlap along 0 ≠ 0 := by
  obtain ⟨x,-,y,-,hx,hy⟩ := overlap_exists_nonzero
  exact fun H=>hy (overlap_rule hx |>.trans (by rw [H];ring))


end YM.Pert.Triangle
