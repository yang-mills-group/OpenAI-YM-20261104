import YM.MS.Hem.Glory
import YM.MS.Hem.Green
/-!
# Fields of pedested amplitude in continued dimension: Mellin integrals

Pack $ζzeta real monotonic estimate and pole selection. Tad includes evidence. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{j m n k:ℕ}{x:ℂ}{R:ℝ}{F H:Mob G}
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {u:I→ℂ}{v:I→ℝ}{a:ℝ}{f:I→Mob G}(h:fell 0 1 f)(hp:∀ i,v i≤0)(hu:∀ i,a≤(u i).re+k)
def wood (n:ℕ)(q:ℂ)(t:ℝ)(F:Mob G): Mob G:= plow q t (Hem.clear n F)
lemma woodC (w: Touch G m E)(h:kPrice F)(v0:E) : Continuous (fun t=>fieldVal (wood k x t F m) w v0) := by -- unbound
    unfold wood; simp_rw [s_p_vector]; exact (Differentiable.continuous (fun t=> (amountD _ t).differentiableAt )).mul ((((clear_p h k) m E w).smooth ()).continuous.comp (f:=fun t:ℝ=> exp t • v0) (by fun_prop))
include h hp hu
lemma bill : fell 0 (fun i=>exp (a*v i)) (fun i=> wood k (u i) (v i) (f i)) := by
    intro m E _ _ _ w; let U := fun i=> fieldVal (Hem.clear k (f i) m) w; have hF : fell 0 1 (fun i=> Hem.clear k (f i)):= fall_sub h ( fall_sum (Finset.range k) (f:=fun j i=>Tad (f i) j) (fun i _=>tad_fall h i) (fun _=>zero_le_one))
    unfold wood; rw [(show _ = _ from funext (show ∀ i,fieldVal (plow (u i) (v i) (Hem.clear k (f i)) m) w = Alps.Bench.Forest.patch (U i) (u i+mass w) (v i) from fun i=> funext fun p=> s_p_vector ..))] -- uncertain
    let K:=((k:ℤ) - mass w).toNat; apply Mell.fade (hF m E w) hp (u:=fun i=>u i+ ↑(mass w)) (a:=a) (k:=K)
    · intro i; simp only [Complex.add_re,Complex.intCast_re]; specialize hu i; have he:(k:ℤ) ≤ mass w+K:= by unfold K; omega
      have hl : (k:ℝ) ≤ (mass w:ℝ)+K:= by exact_mod_cast he
      linarith
    intro i j hj; exact fire (fee h i) k w (by unfold K at hj; omega)
omit h hp hu
variable (h0:0<a)
def μ0:= volume.restrict (Iic (0:ℝ))
abbrev Gather (U:ℝ→Mob G)(x:ℝ): Prop:=∀ m l, IntegrableOn (fun t=> U t m l) (Iic x)
lemma sturdy_wood (h:kPrice F)(l:Legs (Shore G m)): Continuous (fun t=>wood k x t F m l):= by simpa only [fieldVal,ray_sail] using woodC (k:=k) (x:=x) (ray l) h 1 -- numbers
lemma wood_lim (h:kPrice F)(hx:0<x.re+k): Wind (fun t=> wood k x t F) atBot 0:= by
    let a:= x.re+k; have hv := bill (a:=a) (u:=fun _:Iic (0:ℝ)=> x) (f:=fun _=> F) (travel h) (fun i:Iic (0:ℝ)=>i.property) (fun _=> le_refl a); intro m l; obtain ⟨C,hC,b,hb⟩:= ride (hv m ℝ (ray l)) 0
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (g:=fun i:ℝ=> C*(1+‖(1:ℝ)‖)^b*exp (a*i)) (Eventually.of_forall fun _=> norm_nonneg _) ?_ ?_; · filter_upwards [ eventually_le_atBot (0:ℝ)] with p hp; simpa only [norm_iteratedFDeriv_zero,Pi.zero_apply,abs_zero,add_zero,one_mul,fieldVal,ray_sail] using hb (⟨p,hp⟩:Iic (0:ℝ)) 1 -- squeeze cannot infer g
    have hu := ((tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos hx).mpr tendsto_id )).const_mul (C*(1+‖(1:ℝ)‖)^b)); simpa only [mul_zero,Function.comp_apply,id_eq,a] using hu
include h hu h0
omit h0 in
lemma mat_lawn (W:Touch G m E): Lawn μ0 (fun i t=> fieldVal (wood k (u i) t (f i) m) W) (fun t=> exp (a*t)):= by
    intro j; let L:= Iic (0:ℝ); have hz := bill (u:=fun i:I×L=> u i.1) (f:=fun i:I×L=> f i.1) (fun m E _ _ _ w=> uGrab (h m E w) (fun i:I×L=> i.1)) (fun i:I×L=> i.2.property) (fun i=>hu i.1); obtain ⟨C,hC,b,hb⟩:=ride (hz m E W) j; exact ⟨C,hC,b,fun i=> (ae_restrict_mem measurableSet_Iic).mono fun p hp t=> by simpa only [Pi.zero_apply,abs_zero,add_zero,one_mul] using hb (i,(⟨p,hp⟩:L)) t⟩
lemma matt_w (i:I)(W:Touch G m E) : Majorant μ0 (fun t=> fieldVal (wood k (u i) t (f i) m) W):= lawn (integrableOn_exp_mul_Iic h0 0) (fun i=> Eventually.of_forall fun t=>(powder (clear_p (fee h i) k) (u i) t m E W).smooth ()) (fun i x=> (woodC W (fee h i) x).aestronglyMeasurable) (mat_lawn h hu W) i -- placeholders
lemma matt_fell : fell 0 1 (fun i=> mend (fun t=> wood k (u i) t (f i)) 0):= fun m E _ _ _ w=> plush (integrableOn_exp_mul_Iic h0 0) (fun i=>Eventually.of_forall fun t=>(powder (clear_p (fee h i) k) (u i) t m E w).smooth ()) (fun i x=> (woodC w (fee h i) x).aestronglyMeasurable) (mat_lawn h hu w)
end YM.MS.Hem.Mell
