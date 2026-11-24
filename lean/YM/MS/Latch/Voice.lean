import YM.MS.Latch.Music
/-!
# Integral continuity.Polished all 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch.Job
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Belt
open scoped Topology ContDiff Interval
variable {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{G:Gauge}{b:Bool}{V:ℝ→ QP→ ℂ}{a:QP→ℂ}{f:ℝ→ QP× E→ℂ}
 {r:ℝ}{x:E}{μ:Measure QP}{F H:Moments I (Law G)}{P: I→QP}{A B:Moments I (Edge G)}{m:I→Measure QP}
abbrev slice (r:ℝ)(F:ℝ→ E) (x:camp r) := F x.2
lemma lamp (t:ℝ): Set.Icc (-(‖t‖+1)) (‖t‖+1)∈𝓝 t:= by rw [ norm_eq_abs ]; obtain ⟨hT,hP⟩:= abs_lt.mp (show |t| < |t|+1 by linarith); exact Icc_mem_nhds hT hP
lemma he_src (h:Cohere μ)(hp:pole (single (camp r)) (slice r f) 1 ) (hx:Peak a) (x:E) {t:ℝ} (he:t∈Set.Icc (-r) r) : Integrable (fun q=> a q*f t (q,x)) μ:= by
   obtain ⟨d,hD,hW⟩:= funds (camp r) h; exact (rayTag (U:=fun _=>a) (fun _=>hx) hW hp (⟨ (),t,he ⟩:camp r)).values x
lemma Tick (h:Cohere μ)(hp:∀ r:ℝ,0≤r→ pole (single (camp r)) ( slice r f ) 1 )(hu:∀ q,Continuous (fun t=> V t q))(he:∀ q t, V t q=a q*f t (q,x))(hV:Peak a): Continuous (fun t=>∫ p, V t p ∂μ):= by -- x implicit pp
    rw [ continuous_iff_continuousAt ]; intro t; let T:=‖t‖+1; have HR:0≤ T:= by unfold T; positivity
    specialize hp T HR; obtain ⟨d,hD,hW⟩:= funds (camp T) h; obtain ⟨ C,hC,k,H⟩ := hp.dominates 0 d; simp only [norm_iteratedFDeriv_zero] at H; let P:= ( single (camp T) ); let M:=C*( 1+‖x‖ )^k;
    have ht: Integrable (fun i=>M*(single Unit).dust d () i) μ:= by have hx:= hW.integrable (⟨ (),t,existsC t ⟩:camp T); exact hx.const_mul M
    apply continuousAt_of_dominated (μ:=μ) _ _ ht (.of_forall (fun i=> (hu i).continuousAt)); all_goals filter_upwards [lamp t] with s hs; let v:camp T:= ⟨ (),s,hs ⟩ -- let not have
    · simp_rw [funext (fun p=>he p s)]; exact (he_src h hp hV x hs).1
    · refine Filter.Eventually.of_forall fun p=>?_ ; rw [he,norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (hV.pays p)).trans; specialize H v p x trivial; simp only [pow_zero,Pi.one_apply, mul_one, tx] at H; exact H -- v unfolds?
variable (Hμ:∀ i,Cohere (m i))(hA:BackF A)
include Hμ hA
lemma warmCycle (hx:Warm F b) : Warm (fun i t=> cycle (A i t) (m i) (F i t)) b:= by
    constructor
    · intro i T hT; obtain ⟨d,hD,hW⟩:=funds (camp T) (Hμ i); convert planC (Lease.highp ( hx.cost i T hT )) ( hA.cost i T hT ) hW hD ( fun i=>zero_le_one ) ( fun i=>zero_le_one ) using 1; rfl; simp
    intro i l hl; unfold cycle; refine Tick ( Hμ i) ( f:=fun t (q:QP × ℝ)=>trc (A i t) q.1 (F i t) (sail (ray l) q.2)) ?_ ?_ (x:=(1:ℝ)) (a:=fun _=>1) (fun q t=> by rw [ray_sail,one_mul] ) ⟨fun _=>by simp, continuous_const⟩;
    · intro T hT; convert topCycle ( Lease.highp (hx.cost i T hT)) ( hA.cost i T hT ) (ray_course hl) (fun _=>zero_le_one) (fun _=>zero_le_one) using 1; rfl; ext; simp [positive,cw]
    intro q; simp_rw [at_trc]; refine continuous_finsetSum _ (fun s _=> continuous_finsetSum _ (fun j _=>( hA.span i s j q).mul ( hx.walk _ _ (fun i=>by simp [hl i]) ))) -- net unfold
lemma warmJoin (hF:Warm F false)(hx:Warm H false) : Warm (fun i t=> Cabin ( P i ) (A i t) (m i) ( F i t ) (H i t)) false:= by
    constructor
    · intro i T hT; obtain ⟨d,hD,hW⟩:=funds (camp T) (Hμ i); convert hob ( hA.cost i T hT ) (Lease.highp ( hF.cost i T hT )) ( Lease.highp ( hx.cost i T hT )) (fun _=>zero_le_one) (fun _=>zero_le_one) (fun _=>zero_le_one) (A:=fun _=>P i) hW hD (fun E _ _=>?_ ) using 1; rfl; simp; exact ⟨‖P i‖+1, (by positivity),0, (fun j p hx=> by simp [cw])⟩ -- i shadow t
    intro i w hw; unfold Cabin; apply walk_tree.gath; intro l r hl; refine continuous_const.mul ( continuous_finsetSum _ (fun s _=> continuous_finsetSum _ (fun j _=>?_)) ); let f (t):= packMesh s j ( A i ) ( F i ) ( H i ) (ray l) (ray r) t; refine Tick (f:=f) ( Hμ i ) ?_ ?_ (x:=(1:ℝ)) (a:=Tone.bill ( P i )) (fun q t=> (by unfold f packMesh; rw [ray_sail,ray_sail])) ( sailor .. ); -- `gath` implicit K param
    · intro T hT; convert meshC (hA.cost i T hT) s j (add_split ( ray l) (ray r)) (Lease.highp ( hF.cost i T hT )) ( Lease.highp ( hx.cost i T hT )) using 1; rfl; ext; simp [ Qbud, positive, cw ]
    · intro q; unfold meshZ; exact continuous_const.mul ( ( ( continuous_const.mul (hA.span ..)).mul ( continuous_const.mul ( hF.walk _ _ (fun q=> Bool.noConfusion q) )) ).mul (hx.walk _ _ (fun q=> Bool.noConfusion q)) )
end YM.MS.Latch.Job
