import YM.SchemeConversionRG11.FirstW.Trice.Learn
import YM.SchemeConversionRG11.FirstMS.Triad.Vigor
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck YM.SchemeConversionRG11.FirstMS
open scoped ContDiff BigOperators Classical
variable {T: Itinerary} {c:ℕ→Side} {G:Gauge} {o:StepPath T}{K:Set E4}{v:E4}
def toast (b:Badge G)(h:Bool)(v:E4)(μ:Axis)(x:E4) := Triad.soff h b.1 μ 0 (x-v) • unitColor G b.2
lemma laurel_scans (b:Badge G)(h:Bool)(o:StepPath T)(p:sails T o v): HatP T {x|x≠v} (Laurel b h T o):= by
 intro i; let f (u:Who G 6): Hall T G.Color:= token b h u • stalkH T (SeaA T u.val o) i
 have hz (u:Who G 6): Pleased T {x:E4|x≠v} (f u):= ((riseP o p u.val (subset_refl _) i).scale _)
 choose S hs using hz
 rw [show stalkH T (Laurel b h T o) i= ∑ u,f u from funext fun k=>funext fun x=>by simp only [Laurel,stalkH,Stele,SeaA,f, Pi.smul_apply, Finset.sum_apply, Finset.smul_sum]; apply Finset.sum_congr rfl; intro u _; exact smul_comm ..]; exact ⟨_,Score.sum Finset.univ (fun a _=>hs a)⟩
lemma send_0 (b:Badge G)(h:Bool)(i:Axis): Meets T {v:E4|v≠0} (stalkH T (Laurel b h T 0) i) (toast b h 0 i):= by
 intro σ hs v hv o H; let M:=Rig.path T σ hs; apply inkL; intro a
 have he(v): ∑ j: Axis,fan h b.1 j i*grad j Green (-v) = Triad.soff h b.1 i 0 v:= by
    have ht (j): grad j Green (-v)= Triad.sol j 0 v:= by
       rw [Triad.sol,Maxwell.Free.soften_zero]
       linarith only [show -grad j Green (-v)= -(-grad j Green v) from flow_odd v j]
    unfold Triad.soff; simp_rw [ht]
 have hh: inner ℝ (unitColor G a) (toast b h 0 i v)=(∑ j:Axis,fan h b.1 j i*grad j Green (-v)) * (unitColor G a b.2):=by simp only [toast,sub_zero,he,real_inner_smul_right]; rw [unit_hit,unitPaint]
 rw [hh]; exact corn (unitColor G a) i b h (T:=M) H hv
lemma send_all (b:Badge G)(h:Bool)(i:Axis)(p:sails T o v): Meets T ({x:E4| x≠v}) (stalkH T (Laurel b h T o) i) (toast b h v i) := by
 have H: Meets T {x:E4|x≠v} (fun k x=> stalkH T (Laurel b h T 0) i k (x-o k)) (toast b h v i):= by
    have H: Meets T {x:E4|x≠v} (fun k x => stalkH T (Laurel b h T 0) i k (x+(-o) k)) (fun x=>toast b h 0 i (x+-v)):= (send_0 b h i).quote _ (sails_neg p) {x:E4|x≠v} (fun x hx=> by change x + -v≠0; rw [←sub_eq_add_neg];exact sub_ne_zero.mpr hx)
    simpa only [Pi.neg_apply,←sub_eq_add_neg, toast,sub_zero] using! H
 apply H.congr (Eventually.of_forall fun k=>funext fun x=>?_) (fun _ _=> rfl); nth_rw 1 [show (0:StepPath T)=o-o from (sub_self o).symm,←statue]; unfold stalkH passA tracing; rw [LinearMap.pi_apply,LinearMap.proj_apply,sub_add_cancel]
lemma toast_diff (b:Badge G)(h:Bool)(a i:Axis){x v:E4}(hx:x≠v): DifferentiableAt ℝ (toast b h v i) x ∧ grad a (toast b h v i) x= Triad.surf h b.1 a i 0 (x-v) • unitColor G b.2:= by
 let f:=(Triad.soff h b.1 i) 0
 have he : DifferentiableAt ℝ f (x-v):= ((Triad.soff_ok h b.1 i (p:=(0,x-v)) (by simp [sub_ne_zero.mpr hx])).comp (x-v) (f:=fun v:E4=>((0:ℝ),v)) (by fun_prop)).differentiableAt (by simp)
 let L:ℝ→L[ℝ] G.Color:= ((ContinuousLinearMap.id ℝ ℝ).smulRight (unitColor G b.2)); have h:= L.hasFDerivAt.comp x (he.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const _)); exact ⟨h.differentiableAt,DFunLike.congr_fun h.fderiv _⟩
lemma toast_ray (b:Badge G)(h:Bool)(a i:Axis)(p:sails T o v)(hc:MarkGrid T c): Meets T {x:E4| x≠v} (ray a (stalkH T (Laurel b h T o) i)) (fun x=> Triad.surf h b.1 a i 0 (x-v) • unitColor G b.2) := by
 have H:= matched (send_all b h i p) (isOpen_ne_fun continuous_id continuous_const) a (laurel_scans b h o p i) hc (fun _ hx=> (toast_diff b h a i hx).1)
 exact H.congr (Eventually.of_forall fun _=>rfl) fun _ hx=> (toast_diff b h a i hx).2
end YM.RG11.FirstW
