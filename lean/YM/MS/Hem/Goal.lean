import YM.MS.Hem.Rita
/-!
# Resolvent solves scaled IVP (constant Euler pole argument)

Projection polynomial part treated separately, no heat-scale lower cutoff.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff Interval
variable {I:Type} {G:Gauge} {W S: Mob G} {x:ℂ} {n m:ℕ}
lemma word (p q:ℝ): plow x p (wood n x q W) = wood n x (p+q) W:= snow ..
lemma frame_time (p:ℝ): plow x p (progress n x W)=mend (fun s=>wood n x s W) p:= by
    funext m l; change Alps.amount _ p * (∫ t in Iic (0:ℝ), wood n x t W m (sr p l))=_; rw [← integral_const_mul]; change (∫ t in Iic (0:ℝ), plow x p (wood n x t W) m l)=_ ; simp_rw [word]; unfold mend; obtain he:= (measurePreserving_add_left (MeasureSpace.volume:Measure ℝ) p).setIntegral_preimage_emb (Homeomorph.addLeft p|>.measurableEmbedding) (fun t=>wood n x t W m l) (Iic p); have hm:(p + · ) ⁻¹' (Iic p)= Set.Iic (0:ℝ):= (by ext; simp); simpa only [hm] using he -- lint
lemma frame_lim : Wind (fun t=> plow x t (progress n x W)) atBot 0:= by
    intro m l; simp_rw [frame_time]; exact tendsto_integral_Iic_zero tendsto_id -- check start
lemma frame_inv (h:kPrice W)(hp:0<x.re+n)(s:ℝ) : speed (fun t=> plow x t (progress n x W)) (wood n x s W) s:= by
    intro m l; let F(t:ℝ):=wood n x t W m l; simp_rw [frame_time,mend]; obtain hz:Continuous F:= sturdy_wood h l; have hv := frame h hp;
    let H (t:ℝ):= ∫ x in Iic t,F x; change HasDerivAt H (F s) s; rw [show H=(fun t=> (∫ x in (0:ℝ)..t, F x)+ H 0) from funext (fun i=> sub_eq_iff_eq_add.mp (intervalIntegral.integral_Iic_sub_Iic (hv 0 m l) (hv i m l)))]; exact ( intervalIntegral.integral_hasDerivAt_right (hz.intervalIntegrable _ _) hz.aestronglyMeasurable.stronglyMeasurableAtFilter hz.continuousAt).add_const (H 0)
lemma senior_c (h:kPrice W)(s:ℝ) : speed (fun t=> plow x t (Tad W n)) ((x+n) • (plow x s (Tad W n))) s:= by
    intro m l; simp_rw [move_tad h]; convert (amountD (x+n) s).mul_const (Tad W n m l) using 1; rfl; rfl; exact mul_assoc (x+n) (amount (x+n) s) (Tad W n m l) |>.symm
-- package ODE
structure Trail (F J:Mob G)(a:ℂ): Prop where
   derive s: speed (fun s=> plow a s F) ( plow a s J) s
-- ∆ phase later
namespace Trail
variable {L R T: Mob G}
lemma plus (h:Trail W S x)(hv:Trail L R x): Trail (W+L) (S+R) x:= by constructor; intro i; simp_rw [← cert,map_add]; exact speed_add (h.derive i) (hv.derive i)
lemma smul (h:Trail W S x)(q:ℂ): Trail (q • W) (q • S) x:= by constructor; intro t; simp_rw [← cert,map_smul]; exact speed_mul (h.derive t) q
lemma zero : Trail (0:Mob G) 0 x:= by constructor; intro s; simp_rw [← cert,map_zero]; exact fun _ _=> hasDerivAt_const _ _ -- check
lemma prog_p (h:kPrice W)(hp:0<x.re+n): Trail (progress n x W) (Hem.clear n W) x:= ⟨ frame_inv h hp ⟩
lemma u_pose (h:kPrice W): Trail (Tad W n) ((x+n) • Tad W n) x := ⟨fun s=> by rw [← cert,map_smul]; exact senior_c h s⟩
end Trail
end YM.MS.Hem.Mell
