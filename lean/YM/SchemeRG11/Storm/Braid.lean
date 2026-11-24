import YM.SchemeRG11.Storm.Joint
/-! Subtracted mixed term. -/
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.SchemeRG11.Storm
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
variable (i j : Eye)(a b : Axis)(z x y:E4)
local notation "V" => zone z x y

def atopin (p : E4×Time) := fused true i false j p.2.1 (z-p.1)*(hedge a b x y p.2.2 p.1-hedge a b x y p.2.2 z)
def atopout (p : E4×Time) := fused true i false j p.2.1 (z-p.1)*hedge a b x y p.2.2 p.1
lemma atops_in : Measurable (atopin i j a b z x y) := by
  unfold atopin fused hedge; simp only [first_line,second_line,gauze, Steam.α]; fun_prop
lemma atops_out : Measurable (atopout i j a b z x y) := by
  unfold atopout fused hedge; simp only [first_line,second_line,gauze,Steam.α]; fun_prop
variable {z x y} (hx:z≠x)(hy:z≠y)
local notation "tree" => volume.restrict tripod
include hx hy
theorem bud : Integrable (atopin i j a b z x y) ((volume.restrict V).prod tree) := by
  let F := atopin i j a b z x y
  have hm:= (atops_in i j a b z x y).aestronglyMeasurable (μ:= ((volume.restrict V).prod tree))
  let ν:=Zen.prod Zen
  obtain ⟨g,hg,h⟩:= treasure a b (x:=x) (y:=y) (isCompact_closedBall z (pairHole z x y)) (convex_closedBall z _) (show x∉V from fun hw=> (zone_separated hx hy hw).1 rfl) (show y∉V from fun hw=> (zone_separated hx hy hw).2 rfl)
  obtain ⟨C,hC,e⟩:= fuse_pays true i false j
  let b₁:= |∫ p,g p ∂ν|
  have hg' (w:E4) (hw:w∈V): Integrable (fun p=> hedge a b x y p w) ν := by
     have hp:=zone_separated hx hy hw
     exact (tint_i [a] (sub_ne_zero.mpr hp.1.symm)).mul_prod (tint_i [b] (sub_ne_zero.mpr hp.2.symm))
  have hmK : MeasurableSet V:=isClosed_closedBall.measurableSet
  suffices he: ∀ᵐ w ∂volume.restrict V, Integrable (fun p=>F (w,p)) tree ∧
      (∫ p, ‖F (w,p)‖ ∂tree) ≤ (C*b₁)*wharf z w by
    refine (integrable_prod_iff hm).mpr ⟨he.mono (fun x h=>h.1), (((docks z).integrableOn_isCompact (isCompact_closedBall ..)).const_mul _).mono' hm.norm.integral_prod_right' ((he.mono fun x h=> by rw [Real.norm_of_nonneg (integral_nonneg (fun _=>norm_nonneg (F (x,_))))]; exact h.2))⟩
  filter_upwards [ae_restrict_mem hmK, ae_restrict_of_ae (s:=V) (μ:=volume) (volume.ae_ne z)] with w hw he
  have hz' := sub_ne_zero.mpr (show z≠w from Ne.symm he)
  have hu := fuse_pay true i false j hz'
  let f := fun p=> hedge a b x y p w- hedge a b x y p z
  have hq: Integrable f ν := (hg' w hw).sub (hg' _ (zone_self z x y))
  have hk : (∫ p, ‖f p‖ ∂ν) ≤ b₁*‖w-z‖ := by
    have ha: ∀ᵐ p∂ν, ‖f p‖ ≤ g p * ‖w-z‖:=by rw [show ν=(volume:Measure (ℝ×ℝ)).restrict (openZen ×ˢ openZen) from Measure.prod_restrict ..]; apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi); exact fun p hp => h _ _ hp.1 hp.2 w hw z (zone_self z x y)
    apply (integral_mono_ae hq.norm (hg.mul_const _) ha).trans; rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  rw [tree_m]
  refine ⟨hu.mul_prod hq,?_⟩
  change (∫ p:Time, ‖fused true i false j p.1 (z-w)*f p.2‖ ∂Zen.prod ν) ≤ _
  simp_rw [norm_mul]
  rw [integral_prod_mul (fun t=>‖fused true i false j t (z-w)‖) (fun p=> ‖f p‖) (ν:=ν)]
  have hh:0≤∫ p, ‖f p‖ ∂ν:=integral_nonneg (fun _=> norm_nonneg _)
  apply (mul_le_mul (e _ hz') hk hh (by positivity)).trans
  unfold wharf; rw [norm_sub_rev z w]; have hn:=norm_pos_iff.mpr (sub_ne_zero.mpr he); field_simp
  linarith

lemma twig (hh:x≠y) : Integrable (atopout i j a b z x y) ((volume.restrict (V)ᶜ).prod tree) := by
  let F:=atopout i j a b z x y
  have hm:= (atops_out i j a b z x y).aestronglyMeasurable (μ:= ((volume.restrict (V)ᶜ).prod tree))
  let ν:=Zen.prod Zen
  obtain ⟨A,hA,e⟩:= income [a]; obtain ⟨B,hB,H⟩:= income [b]
  obtain ⟨C,hC,d⟩:= fuse_pays true i false j
  let W:=wharf x * wharf y
  let r:=pairHole z x y
  have hr: 0<r:=half_pos (lt_min (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) (norm_pos_iff.mpr (sub_ne_zero.mpr hy)))
  let L:= C/r^4*(A*B)
  suffices he : ∀ᵐ w ∂volume.restrict ((V)ᶜ), Integrable (fun p=> F (w,p)) tree ∧
      (∫ p, ‖F (w,p)‖ ∂tree) ≤ L*W w by
    refine (integrable_prod_iff hm).mpr ⟨he.mono (fun x h=>h.1), ((docked hh).integrableOn.const_mul _).mono' hm.norm.integral_prod_right' (he.mono fun x h=> by rw [Real.norm_of_nonneg (integral_nonneg (fun _=>norm_nonneg (F (x,_))))]; exact h.2)⟩
  filter_upwards [ae_restrict_mem (show MeasurableSet (V)ᶜ from isClosed_closedBall.measurableSet.compl), ae_restrict_of_ae (s:=(V)ᶜ) (μ:=volume) (volume.ae_ne x),ae_restrict_of_ae (s:=(V)ᶜ) (μ:=volume) (volume.ae_ne y)] with w hw hu hv
  have h₁: x-w ≠ 0:=sub_ne_zero.mpr (Ne.symm hu); have h₂:y-w≠0:=sub_ne_zero.mpr (Ne.symm hv)
  have hz : r<‖z-w‖:=lt_of_not_ge (fun hp=> hw (mem_closedBall_iff_norm.mpr (by rwa [norm_sub_rev])))
  have h₃:=norm_pos_iff.mp (lt_trans hr hz)
  let f:= fun p=> hedge a b x y p w
  have he : (∫ p, ‖f p‖ ∂ν) ≤ A*B * W w := by
    simp_rw [ν,f,hedge,norm_mul]
    rw [integral_prod_mul (fun t=> ‖tint [a] t (x-w)‖) (fun t=> ‖Steam.tint [b] t (y-w)‖)]
    apply (mul_le_mul (e _ h₁) (H _ h₂) (integral_nonneg fun _=> norm_nonneg _) (by positivity)).trans; dsimp only [W,wharf,Pi.mul_apply]; rw [norm_sub_rev x w,norm_sub_rev y w]; exact le_of_eq (by simp [div_eq_mul_inv,mul_left_comm,mul_assoc])
  rw [tree_m]
  refine ⟨(fuse_pay true i false j h₃).mul_prod ((tint_i [a] h₁).mul_prod (tint_i [b] h₂)),?_⟩
  change (∫ p:Time, ‖fused true i false j p.1 (z-w)*f p.2‖ ∂Zen.prod ν) ≤ _
  simp_rw [norm_mul]
  rw [integral_prod_mul (fun t=>‖fused true i false j t (z-w)‖) (fun p=>‖f p‖) (ν:=ν)]
  exact (mul_le_mul ((d _ h₃).trans (by gcongr : _ ≤ C/r^4)) he (integral_nonneg fun _=>norm_nonneg _) (by positivity)).trans_eq (mul_assoc ..).symm
end YM.SchemeRG11.Storm
