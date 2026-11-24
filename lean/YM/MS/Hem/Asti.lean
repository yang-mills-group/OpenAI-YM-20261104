import YM.MS.Hem.Dane
/-!
# Uniqueness lemmas and read leading scaling jets

Non-resonant including marks on continuation axes. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff Interval
variable {I E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge}{F R W S: Mob G} {x:ℂ} {b:Bool} {n m j:ℕ}
lemma steady (h:∀ s,∀ n w,Course b w→ HasDerivAt (fun t=>plow x t W n w) 0 s): Steady0 b x W:= by
   intro t m w hp; have ht:=is_const_of_deriv_eq_zero (fun s=> (h s m w hp).differentiableAt) (fun s=> (h s m w hp).deriv) t 0; rwa [posing] at ht -- no `hp`
lemma IdEq (h:Equal false W S): W=S:= funext fun i=> funext fun w=> h i w (fun t=> Bool.noConfusion t)
lemma ray_white (h:kPrice F)(v:ℕ): Wind (fun t=> wood v (-(v:ℂ)) t F) atBot (Tad F v) := by
    let y:ℂ:=-(v:ℂ); have he: 0<y.re+(↑(v+1:ℕ):ℝ):= by simp [y]
    have hw (t:ℝ) : wood v y t F = wood (v+1) y t F+ Tad F v:= by
       have ht : Hem.clear v F=Hem.clear (v+1) F+ Tad F v:= by rw [Hem.clear,Hem.clear,haze_step]; abel
       unfold wood; rw [ht, ← cert, map_add, cert,cert,move_tad h]; simp [y,amount]
    intro m l; change Tendsto (fun t=>wood v y t F m l) _ _; simp_rw [hw]; convert (wood_lim h he m l).add_const (Tad F v m l) using 1; rfl; simp -- `.add_const`
lemma x_scale0 (h:0<x.re): Tendsto (amount x) atBot (𝓝 0):= by
   apply tendsto_zero_iff_norm_tendsto_zero.mpr; simp_rw [amount_norm]; exact tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos h).mpr tendsto_id)
lemma peer (hp:kPrice F)(h:Wind (fun t=> plow (-(n:ℂ)) t F) atBot 0): Hem.clear (n+1) F=F:= by
    suffices ht: ∀ k:ℕ,k≤n+1→haze k F=0 by rw [Hem.clear,ht (n+1) (le_refl _),sub_zero]
    intro k; induction k with
    | zero=> intro h; rw [haze_zero]
    | succ k ih=>
       intro hi; have ht:= ih (Nat.le_trans k.le_succ hi); rw [haze_step,ht,zero_add]; let x:ℂ:= -(k:ℂ); let y:= (-(n:ℂ));
       apply (ray_white hp k).unique; unfold wood; rw [show Hem.clear k F=F by rw [Hem.clear,ht,sub_zero] ]; by_cases H:k=n; · subst k; exact h
       have he:0<(x-y).re:= by simp only [x,y,sub_eq_add_neg,neg_neg,Complex.add_re,Complex.neg_re,Complex.natCast_re]; have hm: k<n:= (by omega); exact_mod_cast (by omega: 0< -(k:ℤ)+n)
       intro m l; change Tendsto (fun t=> plow x t F m l) _ _; simp_rw [show ∀ t,plow x t F= amount (x-y) t • plow y t F from fun t=> by nth_rw 1 [show x=y+(x-y) from Eq.symm (add_sub_cancel ..)]; exact shift .. ]; convert (x_scale0 he).smul (h m l) using 1; rfl; simp
lemma stay0 (h:Trail F R x)(hp:Trail S R x) : Steady0 false x (F-S):= by apply steady; intro t m w hp0; simp_rw [← cert,map_sub]; convert (h.derive t m w).sub (hp.derive t m w) using 1 <;> first| rfl| simp
lemma found (h:Trail F R x)(hp:Trail S R x)(hF:kPrice F)(hS:kPrice S) (hu:∀ i:ℕ,i<n→ x+i≠0)(hk:0<x.re+n): F=S:= by
   apply sub_eq_zero.mp; have hm := stay0 h hp; let T : kPrice (F-S):=fall_sub hF hS; exact IdEq (decide0 hm T hk (fun i hi=> resonance hm T (hu i hi)))
lemma tbase (h:Trail F R x)(he:Wind (fun t=> plow x t F) atBot W)(hp:Trail S R x)(hr: Wind (fun t=>plow x t S) atBot W): F=S:= by
   have ht (s:ℝ) : plow x s (F-S)=F-S:= IdEq (stay0 h hp s); apply sub_eq_zero.mp; apply Wind.unique (A:=fun t=> plow x t (F-S)) (Y:=atBot) _ _; simp_rw [ht]; exact fun _ _ => tendsto_const_nhds; simp_rw [← cert,map_sub]; intro m l; convert ( he m l).sub (hr m l) using 1 <;> first| rfl| simp -- test
end YM.MS.Hem.Mell
