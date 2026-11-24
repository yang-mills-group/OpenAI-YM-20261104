import YM.SchemeConversionRG11.FirstW.Trice.Crop
/-! Tools for masks (unbounded, nonwrapping, single-derivative IR grants still basis controlled). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS
open scoped ContDiff BigOperators Topology Classical
variable {T:Itinerary} {c:ℕ→Side} {G:Gauge}{F E I:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {P W:Hall T ℝ}{P' W':E4→ℝ}{S:Set E4}{f:Hall T E}{y:E4→E}{x:StepPath T}{v:E4}{r R:ℝ}
def slipU (T:Itinerary)(x:StepPath T)(f: Hall T E): Hall T E:=fun i z=> f i (z+x i)
def blot (Q:Wash)(x:E4) : E4→ℝ:= fun y=> soft Q (y-x)
lemma mask_meet (Q:Wash)(p:sails T x v): Meets T univ (Mask T x Q) (blot Q v):= by
 rw [rose_mask]; have h : Meets T univ (Mask T 0 Q) (soft Q):= by
   rw [rose_mask,neg_zero,show resiteR T (slide T 0 (soft Q)) 0=slide T 0 (soft Q) from funext fun i=>funext fun x=> by simp [resiteR]]; exact (slide_scores (soft_price Q) _).identity
 have he : slide T 0 (soft Q)=Mask T 0 Q:= funext fun i=>funext fun z=>by simp [slide,Mask]
 rw [he]; unfold blot; simp only [sub_eq_add_neg]; exact h.quote _ (sails_neg p) _ fun _ _=>mem_univ _
lemma soft_ring (Q:Wash): HasCompactSupport (blot Q v) := by refine (isCompact_closedBall v Q.rOut).of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun x hx=>?_) (isClosed_closedBall ..)); rw [Metric.mem_closedBall]; by_contra! h; rw [dist_eq_norm] at h; exact hx (soft_life Q _ h.le)
lemma blossom (Q:Wash): blot Q v=ᶠ[𝓝 v] fun _=>1:= Eventually.mono ((isOpen_ball.mem_nhds (mem_ball_self Q.rIn_pos)) : ∀ᶠ x in 𝓝 v,x∈ ball v Q.rIn) fun _ hi=>soft_clear _ _ (mem_ball_iff_norm.mp hi).le
lemma stalk_shift (x:StepPath T)(A:Sight T G)(s:Axis): slipU T x (stalkH T A s)=stalkH T (passA T x A) s := rfl
lemma rise_jet {X Y:Sight T G}(x:StepPath T)(a b:Axis): slipU T x (claw T X Y a b)=claw T (passA T x X) (passA T x Y) a b:= by
 -- use wrap
 let A:=passA T x X; let B:=passA T x Y; funext i p; unfold slipU; unfold claw; change spire _ _ _ _ _=spire G _ _ (tracing (x i) _) (tracing (x i) _)
 suffices ht: ∀ X Y:FullT G (T.period i),swerve p (Lattice.square a b) (tracing (x i) X) (tracing (x i) Y)=swerve (p+x i) (Lattice.square a b) X Y by simp only [spire,LinearMap.smul_apply,LinearMap.add_apply, LinearMap.flip_apply,ht]
 intro X Y
 have h(X:FullT G (T.period i)): terms p (tracing (x i) X)=terms (p+x i) X:= funext fun t=>by simp [terms,tracing,add_assoc]
 have ht := swerve_wrap (tracing (x i) X) (tracing (x i) Y) p 0 (Lattice.square a b); simpa only [h,swerve_wrap,map_zero, zero_add] using ht.symm
lemma slip_ray (x:StepPath T)(a:Axis)(f:Hall T E): slipU T x (ray a f)=ray a (slipU T x f):= by
 funext i y; simp [ray,surface,slipU,combine,up,add_right_comm]
omit [NormedSpace ℝ E] in
lemma save_0 {p:Hall T E}{k:ℕ}(h:Dune T 0 k p): SaveB T k p:= by simpa only [SaveB,Pi.zero_apply,Dune,sub_zero] using h
lemma vine_site {X:Sight T G}{p:Axis→E4→ G.Color}(h:landingL T S X p)(s:StepPath T)(hp:sails T s v){K:Set E4}(hk:∀ x∈K,x+v∈S): landingL T K (passA T s X) (fun i x=>p i (x+v)) := by intro i; rw [← stalk_shift]; exact (h i).quote s hp K hk
lemma extra_shore (o:StepPath T)(b:Badge G)(h:Bool)(s t:Axis): Dune T o 4 (ray s (stalkH T (Laurel b h T o) t)):=by
 let f (u:Who G 6): Hall T G.Color:= token b h u • stalkH T (SeaA T u.val o) t
 have hp : stalkH T (Laurel b h T o) t= ∑ u,f u:= by funext k x; simp only [Laurel,Stele,stalkH,Pi.smul_apply,Finset.smul_sum,f,SeaA,Finset.sum_apply]; exact Finset.sum_congr rfl fun u _=> smul_comm ..
 rw [hp]
 have ht(Q:Finset (Who G 6)) : Dune T o 4 (ray s (∑ i∈Q,f i)):= by
   induction Q using Finset.induction with
   | empty=>rw [Finset.sum_empty, show ray s (0:Hall T G.Color)=0 from funext fun i=>funext fun x=>by simp [ray,surface,combine,up]]; exact skyhut
   | insert x Q e ih=>
     rw [Finset.sum_insert e]; unfold ray; rw [surface_add]; apply Dune.roll _ ih
     by_cases ht:x.val.1=0
     · change Dune T o 4 (ray s (f x)); unfold f; rw [ray_weight]; apply Dune.scale; have H:= seaA_prices x.val t o [s]; rw [List.length_singleton,mass,ht] at H; exact H
     unfold f; rw [occur _ _ _ ht,zero_smul, show surface [s] (0:Hall T G.Color)=0 from funext fun i=>funext fun x=>by simp [surface,combine,up]]; exact skyhut
 exact ht _
lemma mask_ticket (Q:Wash) (o:StepPath T)(j:ℕ)(x:Site (T.period j)): ‖(1-Mask T o Q j x)‖≤ 2:= (norm_sub_le ..).trans ((add_le_add_right (mask_budget T Q o j x) _).trans_eq (by norm_num))
lemma meets_goods (h: Meets T S P P')(e:Meets T S W W'): Meets T S (P*W) (P'*W'):= fun σ hs x hx y hy=> (h σ hs x hx y hy).mul (e σ hs x hx y hy)
lemma meets_ice (Q:Wash)(h:sails T x v): Meets T univ (1-Mask T x Q) (1-blot Q v) := Meets.diff (f:=1) (W:=1) (fun _ _ _ _ _ _ => tendsto_const_nhds) (mask_meet Q h)
end YM.RG11.FirstW
