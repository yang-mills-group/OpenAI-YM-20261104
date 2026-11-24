import YM.SchemeRG11.Bubble.Price

/-! Supply the two kinds of tests. The open density test retains its pole intact until DRESSES. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Function Set MeasureTheory Metric Filter Asymptotics Hot MSbar
open scoped ContDiff Topology

lemma window {F G H : ℝ→ℂ} {R C : ℝ} (_ : 1≤R) (hC : 0≤C)
    (hp : ∀ t∈Icc 0 R, ‖F t‖ ≤ C)
    (hd : ∀ t∈Icc 0 1, HasDerivAt F (G t) t ∧ ‖G t‖ ≤ C)
    (he : ∀ t∈Icc 0 1, HasDerivAt G (H t) t ∧ ‖H t‖ ≤ C) : Ticket F (G 0) R C := by
  have hr : (0:ℝ)∈ Icc 0 1:= ⟨le_rfl,zero_le_one⟩
  refine ⟨hp,(hd 0 hr).2,fun t ht=> ?_,fun t ht=>?_⟩
  · simpa only [sub_zero,Real.norm_of_nonneg ht.1] using (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (fun u hu=> (hd u hu).1.hasDerivWithinAt) (fun u hu=> (hd u hu).2) hr ht
  let U := Icc 0 t
  have hh : U ⊆ Icc 0 1:= Icc_subset_Icc_right ht.2
  let M := fun r : ℝ=> F r-(F 0+(r:ℂ)*G 0)
  have hm (r) (hr : r∈U) : HasDerivAt M (G r-G 0) r := by
    let f (r : ℝ):= (r:ℂ)*G 0
    have hc : HasDerivAt f (G 0) r := by simpa only [f,id_eq,Complex.ofReal_one,one_mul] using (((hasDerivAt_id r).ofReal_comp).mul_const (G 0))
    exact (hd r (hh hr)).1.sub (hc.const_add _)
  have hb (r) (hp : r∈U) : ‖G r-G 0‖ ≤ C*t := by
     refine (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun u hu=>(he u hu).1.hasDerivWithinAt) (fun u hu=>(he u hu).2) (convex_Icc (𝕜:=ℝ) (0:ℝ) 1) hr (hh hp)).trans ?_
     rw [sub_zero,Real.norm_of_nonneg hp.1]
     exact mul_le_mul_of_nonneg_left hp.2 hC
  have hk:= (convex_Icc (𝕜:=ℝ) (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le (f':=fun r=>G r-G 0) (fun r hr=> (hm r hr).hasDerivWithinAt) hb (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1)
  simpa only [show M 0=0 by simp [M],sub_zero,Real.norm_of_nonneg ht.1, pow_two,mul_assoc] using hk

variable {n : ℕ}
/-- External unamputated vs open density: this is the pure AMPUTATED strand. -/
def vertex (p : Space n) (_z : ℂ) (t : ℝ) : ℂ := Real.exp (-t*‖p‖^2)
def grade (p : Space n) (_z : ℂ) : ℂ := -(‖p‖^2:ℝ)
lemma amplitude (p : Space n) : Glaze (vertex p) (grade p) := by
  let r : ℝ := -‖p‖^2
  let F (t:ℝ) : ℂ:= Real.exp (t*r)
  have he e : vertex p e=F := funext fun t=> by simp [F,r,vertex]
  have hd t : HasDerivAt F (r*F t) t := by
    convert! ((((hasDerivAt_id' t).mul_const r).exp).ofReal_comp) using 1
    simp [F,mul_comm]
  let G := fun t => (r:ℂ)*F t
  let H := fun t => (r:ℂ)*G t
  have hq t : HasDerivAt G (H t) t := by
    convert! (hd t).const_mul (r:ℂ) using 1
  refine ⟨fun e=> by rw [he]; exact (continuous_iff_continuousAt.mpr fun t=> (hd t).continuousAt).continuousOn, fun _ _=> differentiable_const _,differentiable_const _, fun R hr K _=> ?_⟩
  obtain ⟨A,hA⟩:= (isCompact_Icc (a:=(0:ℝ)) (b:=R)).exists_bound_of_continuousOn (f:=F) (fun t _=> (hd t).continuousAt.continuousWithinAt)
  obtain ⟨B,hB⟩:= (isCompact_Icc (a:=(0:ℝ)) (b:=1)).exists_bound_of_continuousOn (f:=G) (fun t _=> (hq t).continuousAt.continuousWithinAt)
  obtain ⟨C,hC⟩:= (isCompact_Icc (a:=(0:ℝ)) (b:=1)).exists_bound_of_continuousOn (f:=H) (fun t ht=> (continuousWithinAt_const.mul (hq t).continuousAt.continuousWithinAt))
  refine ⟨1+(max (max |A| |B|) |C|),by positivity, fun z hz=>?_⟩
  rw [he,show grade p z=G 0 by simp [grade,G,F,r]]
  refine window (F:=F) (G:=G) (H:=H) hr (by positivity) (fun t ht=> (hA t ht).trans ?_) (fun t ht=> ⟨hd t,(hB t ht).trans ?_⟩) (fun t ht=> ⟨hq t,(hC t ht).trans ?_⟩)
  · linarith [le_max_left (max |A| |B|) |C|,le_max_left |A| |B|,le_abs_self A]
  · linarith [le_max_left (max |A| |B|) |C|,le_max_right |A| |B|,le_abs_self B]
  linarith [le_max_right (max |A| |B|) |C|,le_abs_self C]
end YM.SchemeRG11.Bubble
