import YangMills.WilsonProof.NativeSupport.YM.MS.Hem.Glory
/-!
# Smoothing Mellin base length meromorphic

`s=t` shifted family, all momentum smooth. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{j m n k:ℕ}{x:ℂ}{R:ℝ}{F H:Mob G}
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {u:ℂ→ℂ}{a:ℝ}{f:ℂ→ Mob G}
def progress (k:ℕ)(i:ℂ)(F:Mob G) : Mob G:= mend (fun t=> wood k i t F) 0
lemma prog_smile (t:ℝ)(l:Legs (Shore G m))(hx:Forest (disc R) u)(hs:Hol (disc R) f) : Forest (disc R) (fun z=> wood k (u z) t (f z) m l):= by
   intro z hz; unfold wood plow amount; exact ((( ( hx z hz).add_const _).const_mul _).cexp).mul ( clear_hol hs k|>.top m _ z hz)
lemma prog_hol (he:0<a)(hp:∀ i∈disc R,a≤(u i).re+k)(hx:Forest (disc R) u)(hs: Hol (disc R) f): Hol ( disc R) (fun i=> progress k (u i) (f i)) where
   price c T ht hd:= matt_fell (hs.price c T ht hd) (fun i:closedBall c T=>hp i (hd i.property)) he
   top:= by
      intro m l z hz; let D:= disc R; let Q(w:ℂ)(s:ℝ):= wood k (u w) s (f w) m l; have hZ: ∀ᵐ s ∂μ0, Forest D (fun w=> Q w s):= Eventually.of_forall ( fun t=> prog_smile t l hx hs); have hb : borelad μ0 D Q:= fun i hi=> (sturdy_wood (hs.link hi isOpen_ball) l).aestronglyMeasurable
      obtain ⟨T,hT,hc⟩:=Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hz); let t:=T/3; have ht:0<t:= (by unfold t; linarith); let X:=closedBall z (2*t); have hh:X⊆D:=Subset.trans (closedBall_subset_ball (by unfold t;linarith)) hc; have hm:=hs.price _ _ (by linarith) hh; have hQ := bill (u:=fun i:X×Iic (0:ℝ)=>u i.1) (a:=a) (f:=fun (i:X × Iic (0:ℝ))=> f i.1) (fun m E _ _ _ w=> uGrab ( hm m E w) (fun i:X×Iic (0:ℝ)=>i.1)) (fun i:X × Iic (0:ℝ)=>i.2.property) (fun i=> hp i.1 (hh i.1.property))
      obtain ⟨C,hC,b,hB⟩:= ride (hQ m ℝ (ray l)) 0; refine ( middle (show IsOpen D from isOpen_ball) hZ hb ht hh (( (integrableOn_exp_mul_Iic he 0)).const_mul (C*(1+‖(1:ℝ)‖)^b)) ( (ae_restrict_mem measurableSet_Iic).mono fun s hs p hp=>?_)).differentiableAt; simpa only [norm_iteratedFDeriv_zero,fieldVal,ray_sail,Pi.zero_apply,abs_zero, add_zero,one_mul] using hB ((⟨p,hp⟩:X),(⟨s,hs⟩:Iic (0:ℝ))) 1 -- remove extra T param
lemma prog_mint (h:kPrice F)(ht:0<x.re+k): kPrice (progress k x F):= matt_fell (u:=fun _:Unit=>x) (travel h) (a:=x.re+k) (fun _=>le_rfl) ht
lemma prog_m (q z:ℂ)(k:ℕ) : progress k z (q • F) = q • progress k z F:= by ext; simp only [progress,mend,wood,Hem.clear_pose,← cert,map_smul,Pi.smul_apply,integral_smul]
lemma prog_mer (h:mer f)(hp:∀ i∈disc R,a≤(u i).re+k)(ha:0<a)(hv:Forest (disc R) u)(hr:0<R): mer (fun i=> progress k (u i) (f i)):= by
   obtain ⟨v,H,g,V,hV,h,Hx,Ht⟩:= h; let W:=min V R; have hw:disc W⊆disc R:=ball_subset_ball (min_le_right ..); have hh:= prog_hol ha (fun i hi=>hp i (hw hi)) (fun i hi=>hv i (hw hi)) (h.mono (ball_subset_ball (min_le_left ..))); refine ⟨v,_,Lift.congr (Lift.trim hh (lt_min hV hr)) ?_⟩; filter_upwards [Hx] with i hi; change progress k _ _ = i^v • progress k _ _; rw [hi]; exact prog_m ..
-- needed Gather all x
lemma frame (h:kPrice F)(ht:0<x.re+k)(t:ℝ): Gather (fun s=> wood k x s F) t := by
    intro m l; apply integrableOn_Iic_iff_integrableAtFilter_atBot.mpr; refine ⟨⟨_,Iic_mem_atBot (0:ℝ),?_⟩,(sturdy_wood h l).locallyIntegrable.locallyIntegrableOn (Iic t)⟩ -- expects subset
    obtain he:= ( matt_w (u:=fun _:Unit=>x) (a:=x.re+k) h (fun _=>le_rfl) ht () (ray l)).values 1; simpa only [IntegrableOn,μ0,fieldVal,ray_sail] using he
end YM.MS.Hem.Mell
