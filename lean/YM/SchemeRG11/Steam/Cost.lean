import YM.SchemeRG11.Steam.Green
/-!
Absolute heat-time cost of lines. Does not assign to the value at the origin.
-/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace

lemma charges {r : ℝ} (hr : 0<r) (l : List Axis) (t : ℝ) :
    ∀ x:E4, tint l (r^2*t) (r • x)= (r⁻¹^(4+l.length))*tint l t x := by
  induction l with
  | nil =>
     intro x
     change gauze _ _ = r⁻¹^4*gauze _ _
     rw [gauze,gauze,norm_smul,Real.norm_of_nonneg hr.le]
     rw [show -α (r^2*t) * (r*‖x‖)^2=-α t*‖x‖^2 by unfold α; rw [mul_inv_rev]; field_simp]; ring
  | cons a l ih =>
     intro x
     let h := ContinuousLinearMap.id ℝ E4
     let G := r • h
     have hk : DifferentiableAt ℝ (tint l t) x := (series_calm (gauze_diff t) _).differentiable (by simp) x
     let f := tint l (r^2*t)
     have hp := ((series_calm (gauze_diff (r^2*t)) (l.map basis)).differentiable (by simp) (G x))
     have hh : f ∘ G=fun x=> r⁻¹^(4+l.length)*tint l t x:=funext ih
     have he : fderiv ℝ (f ∘ G) x (basis a)=r⁻¹^(4+l.length)*tint (a::l) t x := by
       rw [hh,fderiv_const_mul hk]; rfl
     rw [fderiv_comp x (show DifferentiableAt ℝ f _ from hp) G.differentiableAt,G.fderiv] at he
     change (fderiv ℝ f (G x)) (r • basis a)=_ at he
     rw [map_smul] at he
     change r*tint (a::l) (r^2*t) (r • x)=_ at he
     simp only [List.length_cons,← Nat.add_assoc,pow_succ]; field_simp at he ⊢; linear_combination he

lemma fortune (l : List Axis) (x : E4) {r : ℝ} (hr : 0<r) :
    (∫ t in openZen, ‖tint l t (r • x)‖)= r⁻¹^(2+l.length) * ∫ t in openZen, ‖tint l t x‖ := by
  have he:= integral_comp_mul_left_Ioi (fun t=> ‖tint l t (r • x)‖) (0:ℝ) (sq_pos_of_pos hr)
  simp_rw [mul_zero,charges hr,norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ r⁻¹^(4+l.length)),integral_const_mul,smul_eq_mul] at he
  change r⁻¹^(4+l.length)*(∫ t in openZen, ‖tint l t x‖) = (r^2)⁻¹ * ∫ t in openZen, ‖tint l t (r • x)‖ at he
  simp only [pow_add, inv_pow] at he ⊢; field_simp at he ⊢; linear_combination -he
lemma income (l : List Axis) : ∃ C>0, ∀ x:E4,x≠0 →
    (∫ t in openZen, ‖tint l t x‖) ≤ C/‖x‖^(2+l.length) := by
  obtain ⟨C,hC,h⟩:= costs l (isCompact_sphere (0:E4) 1) (by simp)
  let g := fun t=> C*Hearth.coat t
  refine ⟨|∫ t in openZen,g t|+1,by positivity,fun x hx=>?_⟩
  have hh:=norm_pos_iff.mpr hx
  let w:= ‖x‖⁻¹ • x
  have he : ‖x‖ • w=x:= smul_inv_smul₀ hh.ne' _
  have ht : w∈ sphere (0:E4) 1:= by rw [mem_sphere_iff_norm, sub_zero,show ‖w‖= ‖(‖x‖⁻¹:ℝ)‖*‖x‖ from norm_smul ..,Real.norm_of_nonneg (by positivity :0≤‖x‖⁻¹), inv_mul_cancel₀ hh.ne']
  have hB : w≠0:=fun hr=> by simp [hr] at ht
  have hi:=integral_mono_ae (tint_i l hB|>.norm) (Hearth.pay_coat.const_mul C) (ae_restrict_of_forall_mem measurableSet_Ioi (fun p hp=>h w ht p hp))
  calc (∫ t in openZen, ‖tint l t x‖) = ‖x‖⁻¹^(2+l.length) * ∫ t in openZen, ‖tint l t w‖ := by simpa only [he] using fortune l w hh
       _ ≤ _ := by rw [div_eq_mul_inv,mul_comm _ ((‖x‖^_)⁻¹),←inv_pow]; exact mul_le_mul_of_nonneg_left (hi.trans ((le_abs_self (∫ t in openZen,g t)).trans (by linarith))) (by positivity)
end YM.SchemeRG11.Steam
