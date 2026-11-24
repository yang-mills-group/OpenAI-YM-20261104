import YM.SchemeConversionRG11.FirstW.Fade.Grid
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical ContDiff
variable {T:Itinerary} {c:ℕ→Side} {G:Gauge}
variable {o p r:StepPath T}{A B C: Sight T G}{x y z:E4}{a b c': Labels.Key G}{R:ℝ}{Q:Wash}
lemma sails_zero: sails T 0 0:= by have h:= sails_sub (sails_step (T:=T) 0) (sails_step (T:=T) 0); simpa using h
lemma mask_taut (T:Itinerary): Pleased T univ (1:Hall T ℝ):=by
 have h:Pleased T univ (slide T (0:E4) (fun _=>(1:ℝ))):=⟨_,slide_scores contDiff_const _⟩; exact h
lemma pleased_prod {K:Set E4}{f g:Hall T ℝ}(h:Pleased T K f)(p:Pleased T K g): Pleased T K (f*g):= h.map₂ p (ContinuousLinearMap.mul ℝ ℝ)
lemma stripe (h:sails T o x)(Q:Wash): Pleased T univ (1-Mask T o Q):= (mask_taut _).left (warm_site h Q)
lemma horizon_end (h:sails T o x)(hp:sails T p y)(e:sails T r z){P:Hall T ℝ} (hP:Pleased T univ P)(hu:Gloam T P 0 P)(f₁:Leeway T o P)(f₂: Leeway T p P)(f₃:Leeway T r P)(i j:Step)(hc:MarkGrid T c) : Helen (CrestBill T (SeaA T a o) (SeaA T b p) (SeaA T c' r) i j P) := by
 let S:=({u:E4| u≠x}∩{u|u≠y})∩{u|u≠z}; have he(x:E4):{u:E4|u≠x} ∈ ae volume:= volume.ae_ne _
 have hx: S∈ ae volume:= inter_mem (inter_mem (he x) (he y)) (he z)
 exact outmask (hP.squash (subset_univ S)) hx hu hc (riseP o h a (fun _ hv=> hv.1.1)) (riseP p hp b (fun _ hv=> hv.1.2)) (riseP r e c' (fun _ hv=>hv.2)) h hp e f₁ f₂ f₃ (shore_quote a _) (shore_quote b _) (shore_quote c' _) (by unfold mass;omega) (by unfold mass;omega) (by unfold mass;omega) i j
lemma crest_roll {i j:Step}{P Q:Hall T ℝ}(h:Helen (CrestBill T A B C i j P))(hp:Helen (CrestBill T A B C i j Q)) : Helen (CrestBill T A B C i j (P+Q)) := by obtain ⟨x,h⟩:=h; obtain ⟨y,hp⟩:=hp; refine ⟨_,(h.add hp).congr fun l=>?_⟩; simp only [CrestBill,Pi.add_apply,add_mul,Finset.sum_add_distrib,mul_add]
lemma crest_flip (P: Hall T ℝ)(A B C:Sight T G)(i j:Step): CrestBill T A B C i j P=CrestBill T B C A i j P := funext fun _=>by unfold CrestBill SeatD; simp_rw [tower_cycles (A:=B _) (B:=C _)]
lemma liner (Q:Wash)(i j:Step)(hv:sails T o x)(hz:sails T p y)(hk:sails T r z)(hc:MarkGrid T c)(hp:Q.rOut<R)(hw:R<‖y-x‖)(h:R<‖z-x‖)(he:R<‖z-y‖): Helen (CrestBill T (SeaA T a o) (SeaA T b p) (SeaA T c' r) i j 1) := by
 let u:=Mask T o Q; let v:=Mask T p Q; let w:=Mask T r Q; let F:Hall T ℝ:=1-u; let H:Hall T ℝ:= 1-v; let W:Hall T ℝ:=1-w
 let A:=SeaA T a o; let B:=SeaA T b p; let C:=SeaA T c' r
 let s:=(F*H)*W; have hf:Pleased T univ F:=stripe hv Q; have hg:Pleased T univ H:=stripe hz Q; have hu:Pleased T univ W:=stripe hk Q
 have hr: Leeway T o s:= waymore (iced_way o Q) (fun i x hx=> (mul_ne_zero_iff.mp (show F i x*H i x ≠0 from (mul_ne_zero_iff.mp hx).1)).1); have hs : Leeway T p s:=waymore (iced_way p Q) (fun i x hx=> (mul_ne_zero_iff.mp (show F i x * H i x ≠ 0 from (mul_ne_zero_iff.mp hx).1)).2); have ht:Leeway T r s:= waymore (iced_way r Q) fun _ _ h=>(mul_ne_zero_iff.mp h).2
 have hQ(i j): Gloam T s 0 (1-Mask T i j):= ara i j
 let L:= ContinuousLinearMap.mul ℝ ℝ; have hy:Gloam T s 0 s:= ((hQ o Q).map₂ (hQ p Q) L).map₂ (hQ r Q) L
 have h1:= horizon_end (a:=a) (b:=b) (c':=c') hv hz hk (pleased_prod (pleased_prod hf hg) hu) hy hr hs ht i j hc
 have h2 : Helen (CrestBill T A B C i j u):= by simpa only [mul_one] using near_lattice Q T hv hz hk hp hw h _ (mask_taut T) a b c' i j hc
 have h3 : Helen (CrestBill T A B C i j (v*F)):= by rw [crest_flip]; exact near_lattice Q T hz hk hv hp he (by rw [norm_sub_rev]; exact hw) F hf b c' a i j hc
 have h4 : Helen (CrestBill T A B C i j (w*(F*H))):= by rw [←crest_flip _ C]; exact near_lattice Q T hk hv hz hp (by rw [norm_sub_rev]; exact h) (by rw [norm_sub_rev];exact he) _ (pleased_prod hf hg) c' a b i j hc
 have he:u + v*F+w*(F*H)+s=1:=by unfold s F H W; ring
 simpa only [← he] using (crest_roll (crest_roll (crest_roll h2 h3) h4) h1) -- loops
-- two-same V distant weight. requires P for p at exterior mask; o on 0.
lemma border (Q U:Wash)(i j:Step)(hv:sails T o x)(hz:sails T p y)(hc:MarkGrid T c)(hp:U.rOut<R)(h:R<‖x-y‖): Helen (CrestBill T (SeaA T a o) (SeaA T b o) (SeaA T c' p) i j (1-Mask T o Q)):=by
 let P:=Mask T p U; let W:Hall T ℝ:=1-Mask T o Q; let A:=SeaA T a o; let B:=SeaA T b o; let C:=SeaA T c' p
 have H : Helen (CrestBill T A B C i j (P* W)):= by rw [←crest_flip _ C]; exact near_lattice U T hz hv hv hp h h _ (stripe hv Q) c' a b i j hc
 let s:Hall T ℝ:=(1-P)*W
 have ho: Leeway T o s:= waymore (iced_way o Q) fun i x hx=> (mul_ne_zero_iff.mp hx).2
 have hp: Leeway T p s:= waymore (iced_way p U) fun i x hx=> (mul_ne_zero_iff.mp hx).1
 have h:Gloam T s 0 s:= (ara (P:=s) p U).map₂ (ara o Q) (ContinuousLinearMap.mul ℝ ℝ)
 have he:Helen (CrestBill T A B C i j s):= horizon_end hv hv hz (pleased_prod (stripe hz U) (stripe hv Q)) h ho ho hp i j hc
 change Helen (CrestBill T A B C i j W); convert crest_roll H he using 1; unfold s; ring_nf
end YM.RG11.FirstW
