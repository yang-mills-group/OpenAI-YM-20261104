import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.House
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-!
# Local parameter proof of continued operations

Integrals outward, using polynomial envelopes. This works even at n, at Re=0, punctured.
 Later Laurent-$D$ values use over disks. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {I E F G: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F][CompleteSpace F] [NormedAddCommGroup G][NormedSpace ℝ G]
-- full and rapid versions
def Court (D:Set ℂ)(f:ℂ→ E× G→ F): Prop:= ∀ c R,0<R→closedBall c R⊆D→ quiet 0 (fun i:closedBall c R=> f i) 1
structure Tracks (D:Set ℂ)(f:ℂ→E× G→ F): Prop where
    price: Court D f
    rays: keys D f
variable {f:ℂ→ Tree E F}{D:Set ℂ}{c:ℂ}{R:ℝ}{r:ℕ}
lemma radius_pay (h:IsOpen D)(hc:c∈D): ∃ r:ℝ,0<r∧ closedBall c (2*r)⊆D:=by
    obtain ⟨r,hr,hk⟩:= Metric.mem_nhds_iff.mp (h.mem_nhds hc); exact ⟨r/4,by linarith,Subset.trans (closedBall_subset_ball (by linarith)) hk⟩
omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma Tracks.plot {f:ℂ→ E× G→ F}(H:Tracks D f): Plots D f:= ⟨fun c R hx he=> Q.common (H.price c R hx he), H.rays⟩ -- ellipsis check
variable (h:IsOpen D)
include h
lemma Tracks.zone (H:Tracks D f): Tracks D (fun i=> d (f i)):=⟨fun c R hx he=> Q.at_d (H.price c R hx he), fun p=> trees_at H.plot h p (1,0)⟩
omit h [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma area_smooth (H:Plots D f)(h:IsOpen D)(hp:c∈D): ContDiff ℝ ∞ (f c):= by
    obtain ⟨r,hx,hh,hB⟩:= plotnear H.span h hp; exact hB.smooth ⟨c,mem_closedBall_self hx.le⟩
lemma Tracks.ch (H:Tracks D f) (hm:∀ i∈D, Reflect (f i)): Tracks D (fun i=> chop (f i)) := by
    refine ⟨fun c R hh he=> Q.at_chop (H.price c R hh he) (fun i=>hm _ (he i.property)),?_⟩; intro x z hz; let U (i:ℂ) (t:ℝ):= d (d (f i)) (t*x.1,x.2); let μ:=volume.restrict (Ioc (0:ℝ) 1); obtain ⟨R,hx,hR⟩:= radius_pay h hz;
    let P:= (H.zone h).zone h;
    have ht : ∀ᵐ y:ℝ ∂μ, Forest D (fun i=>U i y):= Eventually.of_forall (fun t=> P.rays (t*x.1,x.2))
    have hQ : borelad μ D U:= fun i hi=> (((area_smooth P.plot h hi).continuous).comp (f:=fun t:ℝ=> (t*x.1,x.2)) (by fun_prop)).aestronglyMeasurable -- wrong named
    have he:= P.plot.span z (2*R) (by linarith) hR; obtain ⟨C,hC,b,hb⟩:=ride he 0; let W:= C*(1+‖x‖)^b; have hw : ∀ᵐ i ∂μ,∀ p∈closedBall z (2*R),‖U p i‖≤W:= by
        filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with i hi p hp; obtain ⟨hδ,hε⟩:=hi; specialize hb (⟨p,hp⟩:closedBall z (2*R)) (i*x.1,x.2); simp only [norm_iteratedFDeriv_zero,Pi.zero_apply, Pi.one_apply, abs_zero,add_zero,mul_one,one_mul] at hb; apply hb.trans; unfold W; rw [Prod.norm_def,Prod.norm_def,norm_mul,norm_of_nonneg hδ.le]; gcongr; exact mul_le_of_le_one_left (norm_nonneg _) hε -- maybe inequality goal
    simp_rw [chop,intervalIntegral.integral_of_le zero_le_one]; letI : IsFiniteMeasure μ:= inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1))); exact (middle h ht hQ hx hR (integrable_const (μ:=μ) W) hw).differentiableAt
lemma Tracks.pr (H:Tracks D f)(hm:∀ i∈D, Reflect (f i))(m:ℕ) : Tracks D (fun i=>pruning m (f i))∧∀ i∈D, Reflect (pruning m (f i)):= by
   induction m with| zero=> exact ⟨H,hm⟩| succ i ih=> simp_rw [spent]; exact ⟨ih.1.ch h ih.2,fun i hi=> chop_even (ih.2 i hi) (area_smooth ih.1.plot h hi)⟩
end YM.MS.Arc
