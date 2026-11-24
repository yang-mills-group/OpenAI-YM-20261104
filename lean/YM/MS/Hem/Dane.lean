import YM.MS.Hem.Goal
/-!
# Taylor extraction commutation and non-resonance (scale covariance)
 Also determines where allowed resonances only at z=0 or elsewhere.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff Interval
variable {I E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge} {W S: Mob G} {x:ℂ} {b:Bool} {n m j:ℕ}
lemma shift_stage (f:E→ℂ)(h:ContDiff ℝ ∞ f)(x:ℂ)(t:ℝ)(j:ℕ): stage j (Alps.Bench.Forest.patch f x t)= Alps.amount (x+j) t • stage j f := by
    let Q(p:E):= exp t • p; let V:= f ∘ Q; have hz:ContDiff ℝ j (fun p:E=>f (exp t • p)) := (h.comp (g:=f) (f:=Q) (contDiff_const.smul contDiff_id)).of_le (by exact_mod_cast le_top); have hV: Alps.Bench.Forest.patch f x t=amount x t • (fun p:E=>f (exp t • p)):= rfl
    unfold stage Tensor.coeff; funext p; rw [hV,iteratedFDeriv_const_smul_apply hz.contDiffAt,iteratedFDeriv_comp_const_smul (exp t) (h.of_le (by exact_mod_cast le_top))]; simp only [smul_zero,Tensor.diagonal, smul_apply,Pi.smul_apply, Complex.real_smul,smul_eq_mul,amount_add,tack]; ring
lemma Tad_scale (h:kPrice W)(n:ℕ)(x:ℂ)(s:ℝ): Tad (plow x s W) n= amount (x+n) s • Tad W n:= by
   funext m l; rcases lt_or_ge (n:ℤ) (mass l) with hx|hx; · rw [t_exc hx,Pi.smul_apply,Pi.smul_apply,t_exc hx,smul_zero]
   let j:= ((n:ℤ)-mass l).toNat; have h0 : mass l+j=n:=by unfold j;omega
   rw [t_bud _ h0,Pi.smul_apply,Pi.smul_apply,t_bud _ h0]; unfold torch; rw [show fieldVal (plow x s W m) _= Alps.Bench.Forest.patch ( fieldVal (W m) (ray l)) (x+mass (ray l)) s from funext fun i=>s_p_vector .., shift_stage _ ((h m ℝ (ray l)).smooth ()), Pi.smul_apply,add_assoc]; congr 2; rw [mass,ray_dim]; rw [show (fieldDim wfield l:ℂ) + j = n by exact_mod_cast h0]
abbrev Equal (b:Bool)(W V:Mob G): Prop:=∀ m l, Course b l→ W m l=V m l
lemma tuck (h:Equal b W S)(n:ℕ): Equal b (Tad W n) (Tad S n):= by
   intro m l hp; rcases lt_or_ge (n:ℤ) (mass l) with hx|hx; rw [t_exc hx,t_exc hx]; have hu:mass l+(((n:ℤ)- mass l).toNat:ℤ)=n:= by omega
   rw [t_bud _ hu,t_bud _ hu]; unfold torch; rw [show fieldVal (W m) (ray l)=fieldVal (S m) (ray l) from funext (fun p:ℝ=> h m (sail (ray l) p) (sail_course p (ray_course hp)))] -- wrong layout
lemma shadow (h:Equal b W S)(x:ℂ)(t:ℝ): Equal b (plow x t W) (plow x t S):= by intro m l hp; unfold plow; rw [h m _ (fun a=> by rw [net_sr,hp a,smul_zero])]
abbrev Steady0 (b:Bool)(a:ℂ)(F:Mob G):=∀ t:ℝ, Equal b (plow a t F) F
lemma resonance (h: Steady0 b x W)(hp:kPrice W)(hc:x+m≠0): Equal b (Tad W m) 0:= by
    intro n l hl; let y:= Tad W m n l; have ht {s:ℝ}: amount (x+m) s*y=y:= by obtain H:=tuck (h s) m n l hl; rw [Tad_scale hp] at H; exact H
    have hm:= (amountD (x+m) 0).mul_const y; rw [funext (fun s=> show amount (x+m) s*y=y from ht)] at hm; apply eq_zero_of_ne (c:=x+m) hc; obtain he:= hm.unique (hasDerivAt_const 0 y); simpa [amount] using he -- wrong lemma
where eq_zero_of_ne {c y:ℂ}(h:c≠0)(hv:c*y=0): y=0:= (mul_eq_zero.mp hv).resolve_left h
lemma decide0 (h:Steady0 b x W)(hp:kPrice W)(hx:0 < x.re+n)(hs:∀ i:ℕ,i<n→ Equal b (Tad W i) 0): Equal b W 0:= by
    intro m l hl; have he : Equal b (haze n W) 0:= by intro m l hq; unfold haze; simp only [Finset.sum_apply]; exact Finset.sum_eq_zero fun i hi=> hs i ( Finset.mem_range.mp hi) m l hq
    have hm : ∀ t, wood n x t W m l=W m l:= by intro t; obtain he:= shadow (W:=Hem.clear n W) (S:=W) (b:=b) (fun m l hl=> by simp only [Hem.clear,Pi.sub_apply,he m l hl,Pi.zero_apply,sub_zero]) x t; exact (he m l hl).trans (h t m l hl)
    apply tendsto_nhds_unique (f:=fun t:ℝ=>wood n x t W m l) (l:=atBot) _ (wood_lim hp hx m l); simp_rw [hm]; exact tendsto_const_nhds -- parameter names
end YM.MS.Hem.Mell
