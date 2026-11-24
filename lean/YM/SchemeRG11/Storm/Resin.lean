import YM.SchemeRG11.Steam.Dew

/-!
Stop against the first mark. Control the two outward legs as functions of
TIME before restoring subtracted principal values.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.SchemeRG11.Storm
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster Steam MSbar Pert Triangle
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace

lemma past (f : E4 →L[ℝ] ℝ) (c : Axis→ℝ) (hp : ∀ i, ‖f (basis i)‖ ≤ c i) : ‖f‖ ≤ ∑ i,c i := by
  have hc i : 0≤c i := le_trans (norm_nonneg _) (hp i)
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun i _=> hc i))
  intro x
  have he : (∑ i : Axis, x i • basis i)=x := by ext i; simp [WithLp.ofLp_sum,Finset.sum_apply]
  rw [show f x=f (∑ i : Axis, x i •basis i) from by rw [he], map_sum,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> ?_))
  rw [map_smul, norm_smul]; grw [hp i]; rw [mul_comm]; gcongr
  · exact hc i
  rw [Real.norm_eq_abs,← basis_inner]; grw [abs_real_inner_le_norm]; simp
lemma yearn (l : Sl) {K : Set E4} (hk : IsCompact K) {x : E4} (hx : x∉K) : ∃ C>0,
    ∀ t>0, ∀ u∈K, ‖tint l t (x-u)‖ ≤ C*Hearth.coat t := by
  let S := (fun u=> x-u) '' K
  have he : IsCompact S:=hk.image (continuous_const.sub continuous_id)
  obtain ⟨C,hC,h⟩:= costs l he (show 0∉S from fun ⟨v,hv,h⟩ => hx ((sub_eq_zero.mp h).symm ▸ hv))
  exact ⟨C,hC,fun t ht u hu=> h (x-u) (mem_image_of_mem _ hu) t ht⟩
lemma springs (l : Sl) {K : Set E4} (hk : IsCompact K) (h : Convex ℝ K) {x : E4} (hx : x∉K) :
    ∃ C>0, ∀ t>0, ∀ u∈K, ∀ v∈K, ‖tint l t (x-u)-tint l t (x-v)‖ ≤ C*Hearth.coat t*‖u-v‖ := by
  choose C hC hc using fun i => yearn (i::l) hk hx
  refine ⟨∑ i,C i,Finset.sum_pos (fun i _=>hC i) Finset.univ_nonempty,fun t ht u hu v hv=>?_⟩
  let g := fun u:E4 => x-u
  let f := tint l t ∘ g
  have he : Differentiable ℝ (tint l t):= (series_calm (gauze_diff t) (l.map basis)).differentiable (by simp)
  have hg : Differentiable ℝ g := by unfold g; fun_prop
  apply h.norm_image_sub_le_of_norm_fderiv_le (x:=v) (y:=u) (f:=f) (fun i _=> he.comp hg i) _ hv hu
  intro y hy
  rw [Finset.sum_mul]; apply past
  intro i
  rw [show fderiv ℝ f y=_ from fderiv_comp y (he (g y)) (hg y), show fderiv ℝ g y=-ContinuousLinearMap.id ℝ E4 from (show fderiv ℝ (fun y=> x-id y) y= _ from by rw [fderiv_const_sub x]; simp only [fderiv_id])]
  change ‖(fderiv ℝ (tint l t) _ ) (-(basis i))‖ ≤ _
  rw [map_neg,norm_neg]
  exact hc i _ ht _ hy

def hedge (a b : Axis) (x y : E4) (V : ℝ×ℝ) (w : E4) := tint [a] V.1 (x-w)*tint [b] V.2 (y-w)
lemma treasure (a b : Axis) {x y : E4} {K : Set E4} (hk:IsCompact K) (hV:Convex ℝ K) (hx:x∉K) (hy:y∉K) :
    ∃ g : ℝ×ℝ→ℝ, Integrable g (Zen.prod Zen) ∧
    ∀ (s t:ℝ), 0<s → 0<t → ∀ u∈K, ∀ w∈K, ‖hedge a b x y (s,t) u-hedge a b x y (s,t) w‖ ≤ g (s,t)*‖u-w‖ := by
  obtain ⟨A,hA,e⟩:= yearn [a] hk hx; obtain ⟨B,hB,H⟩:=yearn [b] hk hy
  obtain ⟨D,hD,h⟩:= springs [a] hk hV hx; obtain ⟨C,hC,k⟩:= springs [b] hk hV hy
  refine ⟨fun q=> (A*C+D*B)*(Hearth.coat q.1* Hearth.coat q.2), (Hearth.pay_coat.mul_prod Hearth.pay_coat).const_mul _,fun s t hs ht u hu w hw=>?_⟩
  unfold hedge; dsimp only
  rw [show ∀ a b c d : ℝ,a*b-c*d=a*(b-d)+(a-c)*d from fun _ _ _ _=>by ring]
  refine (norm_add_le ..).trans ?_; rw [norm_mul,norm_mul]
  have hp : 0 ≤ Hearth.coat s:=sq_nonneg _; have hq : 0≤Hearth.coat t:=sq_nonneg _
  grw [h s hs u hu w hw,k t ht u hu w hw,e s hs u hu,H t ht w hw]; exact le_of_eq (by ring)
end YM.SchemeRG11.Storm
