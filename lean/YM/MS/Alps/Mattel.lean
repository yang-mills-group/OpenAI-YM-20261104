import YM.MS.Alps.Bench
/-!
# Strong derivatives in heat log time

Packages $∆$ fixtures and merom RHS smooth already supplied by lengths, enough to
 conclude differential formula after choosing all subtractions. Independent of y. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff Interval
open Bench Forest -- ambiguous
variable {E F I: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F]
 {G:Gauge}{b c:Bool}{p t:ℝ}
variable {u v:ℝ→ Mob G}{r:ℝ→ Rip G}{H Y: Mob G}{V:Rip G} 
-- two types of Taylor testing cost.
def polar (v:ℝ→Mob G)(X:Mob G)(t:ℝ)(p:Trail0 t):= v p-v t-(cord t p:ℂ) • X
def beamR (v:ℝ→ Rip G)(X:Rip G)(t:ℝ)(p:Trail0 t) := v p-v t-(cord t p:ℂ) • X

structure Curve (v:ℝ→ Mob G)(Y:Mob G)(t:ℝ): Prop where
   pay: fell 0 (flag t) (polar v Y t)
structure BeamR (v:ℝ→ Rip G)(U:Rip G)(t:ℝ): Prop where
   pay: rib 0 (flag t) (beamR v U t)
abbrev speed (u:ℝ→ Mob G)(H:Mob G)(t:ℝ): Prop:=∀ m l, HasDerivAt (fun i:ℝ=> u i m l) (H m l) t
abbrev speedR (u:ℝ→ Rip G)(V:Rip G)(t:ℝ): Prop:=∀ m i j q, HasDerivAt (fun t:ℝ=> u t m i j q) (V m i j q) t
lemma horizonP (a:ℂ){F:Mob G} (hf:kPrice F)(h:speed (fun t=>plow a t F) H t): Curve (fun t=> plow a t F) H t:= by
   refine ⟨fun m E _ _ _ w=>?_⟩; let u:=fieldVal (F m) w; let A:= a+(mass w:ℂ); have hv:Told u:= hf m E w;
   convert Bench.Forest.Zed hv t A using 1; funext i x; simp only [polar, fieldVal,Pi.smul_apply, Pi.sub_apply,fragment]; simp_rw [show ∀ s:ℝ,plow a s F m (sail w x)= Bench.Forest.patch u A s x from fun s=> s_p_vector ..];
   have hh : H m (sail w x)=Bench.Forest.patch (loadC u A) A t x:= by
       obtain hD:= h m (sail w x); rw [show (fun i:ℝ=>plow a i F m _ )=(fun i:ℝ=>Bench.Forest.patch u A i x) from funext fun s=> s_p_vector ..] at hD; exact hD.unique ((Bench.Forest.plot (hv.smooth ()) A).deriv x t)
   rw [hh, ← IsScalarTower.algebraMap_smul ℂ (cord t i)]; rfl -- rw real? check
lemma horizonR (a:ℂ){U:Rip G} (h:rPrice U)(hp:speedR (fun t=>pulse a t U) V t): BeamR (fun t=> pulse a t U) V t:= by
    refine ⟨fun m i j=>?_⟩; let T:= U m i j; let p:=a-wfield i-wfield j; have he: Vign T:= h m i j; let f:= Bench.Forest.patch T p;
    convert Bench.Forest.DimL he t p using 1; funext k x; have hh: V m i j x=Bench.Forest.patch (loadC T p) p t x:= (hp m i j x).unique ((Bench.Forest.plot ((railto he).smooth ()) p).deriv x t)
    simp only [beamR,Pi.sub_apply,Pi.smul_apply,fragment]; rw [hh,← IsScalarTower.algebraMap_smul ℂ (cord t k)]; rfl
lemma decayFlag (g:ℝ→ ℂ)(Y:ℂ)(C:ℝ)(h:∀ i:Trail0 t,‖slopeP t g Y i‖≤ C*flag t i): HasDerivAt g Y t:= by
    apply hasDerivAt_iff_tendsto_slope.mpr; apply tendsto_iff_dist_tendsto_zero.mpr
    have hp : Tendsto (fun u:ℝ=> C*dist u t) (𝓝[≠] t) (𝓝 0) := by
        refine Tendsto.mono_left ?_ (show 𝓝[≠] t ≤ 𝓝 t from nhdsWithin_le_nhds)
        simpa only [dist_self,mul_zero] using (show Continuous (fun u:ℝ=> C*dist u t) by fun_prop).tendsto t
    refine squeeze_zero' (.of_forall (fun _=>dist_nonneg)) ?_ hp; filter_upwards [mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds t (zero_lt_one)),self_mem_nhdsWithin] with i hi he; rw [dist_eq_norm,dist_eq_norm,slope_def_module]; let x:Trail0 t:=⟨i,hi⟩; let V:=i-t; have hV:V≠0:=sub_ne_zero.mpr he;
    change ‖V⁻¹ • (g i-g t)-Y‖≤ C*‖V‖; rw [show V⁻¹ • (g i-g t)-Y=V⁻¹ • (g i-g t - V • Y) by rw [smul_sub V⁻¹ (g i-g t),inv_smul_smul₀ hV], norm_smul,norm_inv]; apply (le_trans (mul_le_mul_of_nonneg_left (h x) (inv_nonneg.mpr (norm_nonneg V))))
    rw [← div_eq_inv_mul,div_le_iff₀ (norm_pos_iff.mpr hV),mul_assoc, ← pow_two, Real.norm_eq_abs,sq_abs]; exact le_refl _
lemma Curve.valid (h:Curve u H t): speed u H t:=by
    intro m l; obtain ⟨C,hC,b,hb⟩:= ride (h.pay m ℝ (ray l)) 0; let D:= C*(1+‖(1:ℝ)‖)^b; refine decayFlag _ _ D fun x=> ?_; specialize hb x 1; simpa only [norm_iteratedFDeriv_zero,Pi.zero_apply,abs_zero,add_zero,one_mul,fieldVal, ray_sail,slopeP,polar,Pi.sub_apply,Pi.smul_apply,D,Complex.real_smul,smul_eq_mul] using hb
end YM.MS.Alps
