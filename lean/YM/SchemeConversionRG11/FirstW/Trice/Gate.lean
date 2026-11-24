import YM.SchemeConversionRG11.FirstW.Trice.World
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS
open scoped Topology ContDiff BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side} {G:Gauge}{s t u:StepPath T} {A B C:Sight T G}{v x y z:E4}{R:ℝ}
-- backward bank moved differentiation. test BCH near.
def torso (P:Hall T ℝ)(W:Hall T G.Color): Hall T G.Color:=fun i v=>P i v • W i v
def stance (P: E4→ℝ)(W:E4→G.Color):E4→ G.Color:=fun x=>P x • W x
def rating (F W:Hall T G.Color)(i:Axis):Hall T ℝ:= fun k x=> -(inner ℝ (F k x) (mailR T (ray i W) (-step i) k x))
lemma shift_inner (f:Hall T G.Color)(w:Hall T G.Color)(i:Axis)(k:ℕ): (∑ x:Site (T.period k),inner ℝ (ray i f k x) (w k x)) =∑ x:Site (T.period k), rating f w i k x:= by
 let L:=innerSL ℝ (E:=G.Color); let q := (fun (k:ℕ) (x:Site (T.period k))=> L (w k x))
 have he:= settle_air i q f k; unfold tollH at he; apply mul_left_cancel₀ (show T.gap k ^4 ≠ 0 from pow_ne_zero _ (T.positive k).ne')
 rw [← Finset.sum_congr rfl (fun x (_:x∈(Finset.univ:Finset (Site (T.period k))))=> real_inner_comm (ray i f k x) (w k x))]; apply Eq.trans he; apply congrArg _; apply Finset.sum_congr rfl; intro x _
 unfold rating q ray surface mailR; simp only [L,Pi.neg_apply,Pi.smul_apply,combine,up,smul_sub,sub_apply,smul_apply,neg_apply,innerSL_apply_apply, inner_sub_right,real_inner_smul_right, smul_eq_mul]; congr 2 <;> rw [real_inner_comm]
lemma grade_zero (Q:Wash)(W:E4→ G.Color){z:E4}(h:R<‖z‖)(ht:Q.rOut<R)(a:Axis): grad a (stance (blot Q 0) W) z=0:=by
 have hz: stance (blot Q 0) W=ᶠ[𝓝 z] (fun _=>0):= (continuous_norm.continuousAt.tendsto.eventually (lt_mem_nhds (ht.trans h))).mono fun i hi=>by unfold stance blot; rw [sub_zero,soft_life Q i (le_of_lt hi), zero_smul]
 unfold grad Analysis.D; rw [hz.fderiv_eq]; simp
variable {A₀ B₀ C₀:Badge G}{b₁ b₂ b₃: Bool}
lemma local_rate (Q:Wash)(hr:Q.rOut<R)(hy:R<‖y‖)(hz:R<‖z‖)(hT:sails T t y)(hU:sails T u z)(hc:MarkGrid T c)(i j a b:Axis) :
 let f:= stalkH T (Laurel A₀ b₁ T 0) j; let W:= torso (T:=T) (Mask T 0 Q) (claw T (Laurel B₀ b₂ T t) (Laurel C₀ b₃ T u) a b); let S:= stance (blot Q 0) (pitch (toast B₀ b₂ y) (toast C₀ b₃ z) a b)
 Market T (rating f W i) (fun v=> -(inner ℝ (toast A₀ b₁ 0 j v) (grad i S v))) := by
 intro f W X; let L:=ContinuousLinearMap.lsmul ℝ ℝ (E:=G.Color); let K: Set E4:={x|x≠y}∩{x|x≠z}
 have hp: Town R ⊆ K:= fun v hv=> ⟨fun h=>hy.not_ge (by subst v; simpa using hv),fun h=>hz.not_ge (by subst v;simpa using hv)⟩
 have hB:= laurel_scans B₀ b₂ t hT; have hC:= laurel_scans C₀ b₃ u hU
 have hX: Pleased T K (claw T (Laurel B₀ b₂ T t) (Laurel C₀ b₃ T u) a b):= spireP (fun i=> (hB i).squash inter_subset_left) (fun i=> (hC i).squash inter_subset_right) _
 have hw: Pleased T K W:= ((warm_site sails_zero Q).squash (subset_univ _)).map₂ hX L
 have hh:Meets T K W X:=by
    have h : Meets T K (Mask T 0 Q) (blot Q 0):= (mask_meet _ sails_zero).restrict (subset_univ _)
    have hA:= clawV (p:=toast B₀ b₂ y) (q:=toast C₀ b₃ z) (show landingL T K (Laurel B₀ b₂ T t) _ from fun i=> (send_all B₀ b₂ i hT).restrict inter_subset_left) (show landingL T K (Laurel C₀ b₃ T u) _ from fun i=> (send_all C₀ b₃ i hU).restrict inter_subset_right) a b
    exact h.price hA (fun (z:ℝ)(x:G.Color)=>z • x) (show Continuous (uncurry fun (z:ℝ)(x:G.Color)=> z • x) from (L.continuous.comp continuous_fst).clm_apply continuous_snd)
 have he : Meets T K (mailR T (ray i W) (-step i)) (grad i X) := by
    apply (matched (K:=K) hh ((isOpen_ne_fun continuous_id continuous_const).inter (isOpen_ne_fun continuous_id continuous_const)) i hw hc _).east (-step i)
    intro v hv; obtain ⟨hv,he⟩:= hv; unfold X stance pitch
    obtain ⟨L,H⟩:=doubles G.ad; simp_rw [←H]; have hP:ContDiff ℝ ∞ (blot Q (0:E4)):= (soft_price Q).comp (f:=fun v:E4=>v-0) (by fun_prop)
    have H1(j:Axis): DifferentiableAt ℝ (toast B₀ b₂ y j) v:= (toast_diff B₀ b₂ a j hv).1
    have H2(j:Axis): DifferentiableAt ℝ (toast C₀ b₃ z j) v:= (toast_diff C₀ b₃ a j he).1
    exact (hP.differentiable (by simp) v).smul (((L.differentiableAt.comp v (H1 _)).clm_apply (H2 _)).sub ((L.differentiableAt.comp v (H1 _)).clm_apply (H2 _)))
 let A:= mailR T (ray i W) (-step i)
 obtain ⟨s,hs,hR⟩:=exists_between hr; obtain ⟨r,hh,he'⟩:= exists_between hs
 have hx: Placed T Q.rOut W := Eventually.mono (mask_placed (T:=T) Q) (fun j hj x hx=> hj x (fun h=>hx (by unfold W torso; rw [h,zero_smul])))
 have hv: Placed T s A := (place_air hx hh i).flow he' _
 let I:= -(innerSL ℝ (E:=G.Color)); have HH:= cap_power (p:=f) (save_0 (((ShoreD 0 A₀ b₁).1) j)) hc (send_0 _ _ _) hR (by linarith [Q.rOut_pos] :0≤ s) le_rfl (he.restrict hp) hv I
 let F:E4→ℝ:= fun v=> -(inner ℝ (toast A₀ b₁ 0 j v) (grad i X v))
 have hz: (fun v=>if v∈Town R then I (toast A₀ b₁ 0 j v) (grad i X v) else 0) = F:= funext fun v=>by split; rfl; rename_i h; unfold F X; rw [grade_zero Q _ (by simpa [Town] using h) hr,inner_zero_right,neg_zero]
 dsimp only at HH; rw [hz] at HH; exact HH
end YM.RG11.FirstW
