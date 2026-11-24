import YM.SchemeConversionRG11.FirstW.Trice.FirstStar
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical
variable {T: Itinerary}{G:Gauge}{x y o:StepPath T}{q r:E4}
abbrev Sat (h:Badge G)(e:Bool)(T:Itinerary)(x:StepPath T)(k:ℕ):= Stele h e (x k) (T.gap k)
def hopC (T:Itinerary)(h:Badge G)(e:Bool)(o:StepPath T)(A B:Sight T G)(k:ℕ):= CardC h e (T.gap k) (o k) (A k) (B k)
lemma hop_eq (T:Itinerary)(h:Badge G)(e:Bool)(o:StepPath T)(A B:Sight T G)(k:ℕ): hopC T h e o A B k=CardC h e (T.gap k) (0:Site (T.period k)) (passA T o A k) (passA T o B k) := by
 let hx {n:Side}(U V:FullT G n)(x:Site n)(t:ℝ): CardC h e t x U V=CardC h e t 0 (tracing x U) (tracing x V):=by unfold CardC; simp only [echoLeg,LinearMap.smul_apply,echo_translate,zero_add]
 exact hx ..
lemma move_stat (T:Itinerary)(h:Badge G)(e:Bool)(o x:StepPath T)(k): passA T o (Sat h e T x) k=nativeM T (Laurel h e T (x-o)) k:= by unfold Sat; simp only [passA,Stele,map_sum,map_smul,river,consumes]; simp only [nativeM,Laurel,smul_inv_smul₀ (T.positive k).ne',Stele,Pi.sub_apply,river]
private lemma fan_t (b: Bool)(h:Badge G)(Q:Labels.Taylor G 0): lineReader b h.1 h.2 Q=fanReading b h.1 Q h.2:=rfl
lemma cap_ink (h a b:Badge G)(r s t: Bool)(q x:E4): lineReader r h.1 h.2 (Bare.radialMap (door (fun i j=>pitch (toast a s q) (toast b t x) i j 0)))=colorF a.2 b.2 h.2 * ∑ i:Axis,∑ j:Axis,fan r h.1 i j * soff s a.1 i 0 (-q) * soff t b.1 j 0 (-x) := by
 let Y:=toast a s q; let Z:=toast b t x
 have hp:= vector_at (G:=G) (fun i j=>pitch Y Z i j 0) (pitched_skew _ _ _) r h.1
 have hx(i j:Axis): (G.ad (unitColor G a.2) (unitColor G b.2)) h.2=colorF a.2 b.2 h.2:=by unfold colorF; rw [to_color]
 let p(i j:Axis):ℝ:= fan r h.1 i j * soff s a.1 i 0 (-q)*soff t b.1 j 0 (-x)
 let e:=colorF a.2 b.2 h.2
 have he(i j:Axis) : (fan r h.1 i j • pitch Y Z i j 0:G.Color) h.2 = e*(p i j+p j i):= by
    unfold pitch p Y Z toast; simp only [map_smul, LinearMap.smul_apply,zero_sub,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]; rw [hx i j,fan_flip r h.1 j i]; unfold e; -- fan_flip maybe orientation
    ring
 change _ = e * ∑ i:Axis,∑ j:Axis,p i j
 rw [fan_t]; unfold Y Z at hp he; rw [hp,PiLp.smul_apply]; simp_rw [WithLp.ofLp_sum, Finset.sum_apply, he,← Finset.mul_sum, Finset.sum_add_distrib]; rw [Finset.sum_comm (f:=fun i j:Axis=>p j i)]; simp only [smul_eq_mul]; ring
lemma hop_read (T:Itinerary)(h a b: Badge G)(r s t:Bool)(o x y:StepPath T){q z:E4}(hq:q≠0)(hz:z≠0)(hx:sails T (x-o) q)(hy:sails T (y-o) z): Tendsto (hopC T h r o (Sat a s T x) (Sat b t T y)) atTop (𝓝 (colorF a.2 b.2 h.2 * ∑ i:Axis,∑ j:Axis,fan r h.1 i j * soff s a.1 i 0 (-q) * soff t b.1 j 0 (-z))) := by
 let S:= {v:E4|v≠q} ∩{v|v≠z}
 have h1: landingL T S (Laurel a s T (x-o)) (toast a s q):= fun i=> (send_all _ _ i hx).restrict inter_subset_left
 have h2: landingL T S (Laurel b t T (y-o)) (toast b t z):= fun i=>(send_all _ _ i hy).restrict inter_subset_right
 rw [←cap_ink]; refine (receive h r h1 h2 (show 0∈S from ⟨hq.symm,hz.symm⟩)).congr fun k=> ?_; rw [hop_eq,move_stat,move_stat]
variable {s:P→StepPath T}{w:Nodes}
def levyC (T:Itinerary)(g:P→ Badge G)(s:P→StepPath T)(j:P)(i:ℕ): ℂ:=↑(hopC T (g j) (glow j) (s j) (Sat (g (foreL j)) (glow (foreL j)) T (s (foreL j))) (Sat (g (aft j)) (glow (aft j)) T (s (aft j))) i)
lemma earned (g:P→Badge G)(j:P)(hs:∀ i,sails T (s i) (w i))(hw:w∈conf 3) : Tendsto (levyC T g s j) atTop (𝓝 (colC g * atMarkQ (fun i=>(g i).1) w j 0)) := by
 let k:=foreL j; let l:=aft j
 have hk:w k-w j≠0:=sub_ne_zero.mpr (hw.ne (neg1 j)); have hl:w l-w j≠0:=sub_ne_zero.mpr (hw.ne (neg2 j))
 have H:= hop_read T (g j) (g k) (g l) (glow j) (glow k) (glow l) (s j) (s k) (s l) hk hl (sails_sub (hs k) (hs j)) (sails_sub (hs l) (hs j)); rw [Triad.color_rotate (g k).2, color_loop (fun i=>(g i).2) j,neg_sub,neg_sub] at H -- matcher cycle
 have ht:=continuous_ofReal.continuousAt.tendsto.comp H; convert! ht using 2; unfold colC atMarkQ; push_cast; apply congrArg _; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; rw [kernel_real _ _ _ (sub_ne_zero.mpr (hw.ne (neg1 j).symm)),kernel_real _ _ _ (sub_ne_zero.mpr (hw.ne (neg2 j).symm))]
 -- adjust explicit
end YM.RG11.FirstW.Branch
