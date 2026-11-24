import YangMills.WilsonProof.NativeSupport.YM.MS.Rock.Fell
/-!
# Cost combin library for price tags

Including scaleC and positive at various finite tags. Generic uniform in dimensions
 across rank, no x parameters besides ext. Later blow exp. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
variable {G:Gauge}{I E F H J A:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup H] [NormedSpace ℝ H]
variable {z:UScale I}{a b r:I→ℝ}
section body
variable {f g:I→ Mob G} {u:I→ Rip G} {U:I→ ℂ}
lemma znon (h:fell z a f): ∀ i,0≤a i:=terrain (h 0 ℝ [])
lemma line_nn {m}(h:rib z a u) (p q:Cfield G m): ∀ i,0≤a i:= fun i=>by
   have hm: 0≤a i / (path z).weight i (0: SectorP m)^0:= (h m p q 0).nonneg i 0 (mem_univ _); simpa only [pow_zero,div_one] using hm
lemma fee (h:fell z a f)(x:I): fell 0 (fun _:Unit=>1) (fun _=> f x):= fun m E _ _ _ w=> fall_here (h m E w) x
lemma fall_zero (h:∀ i,0 ≤ a i): fell z a (fun _=> (0:Mob G)) := fun _ _ _ _ _ _=> Costs.zero (fun i _ _=>h i)
lemma fall_add (h: fell z a f)(hv: fell z a g): fell z a (fun i=>f i+g i):= fun m E _ _ _ w=> Costs.add (h m E w) (hv m E w)
lemma fall_sub (h: fell z a f)(hv: fell z a g): fell z a (fun i=>f i-g i):= fun m E _ _ _ w=> Costs.sub (h m E w) (hv m E w)
lemma fall_sum (J:Finset A) {f:A→ I→Mob G} (h:∀ j∈J,fell z a (f j))(hp:∀ i,0≤a i): fell z a (fun i=>∑ j∈J,f j i):= by intro m E _ _ _ w; convert! Costs.sum J (fun i he=> h i he m E w) (fun i _ _=> hp i) using 1; ext; simp [fieldVal]
lemma fall_scale (h : fell z a f)(hz:scaleC z b fun i=> ‖U i‖): fell z (fun i=>b i*a i) (fun i=> U i • f i):= fun m E _ _ _ w=> Costs.mul (at_rate hz) (h m E w) -- scaleC arg order? defined scaleC z a f
end body
section rapid
variable {u:I→ E→ F}{v:I→ E×F→ H}
abbrev rails (z:UScale I)(a:I→ℝ)(u:I→ E→F): Prop:= Line (path z) (fun _=>Set.univ) u a
lemma railto (h:rails z a u) : veg z u a:= by let A:= ContinuousLinearMap.inl ℝ E ℝ; have he : quiet z (fun i (p:E×ℝ)=> u i p.1) a:= Line.rapid h; exact Bound.linear A (Q.common he)
lemma fastline (h:rails z a u)(x:I): rails 0 (fun _:Unit=>1) (fun _=>u x):= by
    intro b; refine ⟨fun _=> (h b).smooth x,fun j=>?_⟩; obtain ⟨C,hC,k,hk⟩:=(h b).quoted j; have hp:= (terrain (railto h) x); let V:=C*(path z).basic x^k; have hx : 0<V:=by have hh:=(path z).basic_pos x; unfold V; positivity
    refine ⟨V*(a x+1),mul_pos hx (by linarith),0,fun i p _=>?_⟩; apply le_trans (hk x p (mem_univ _)); simp only [cheap_length,one_pow,mul_one,pow_zero,Scale.strict]; let W:=(1+‖p‖)^b; have hW:0<W:= pow_pos (by positivity) _; simp only [Scale.weight,cheap_length,one_mul]; change V*(a x/ W)≤ V*(a x +1)*(1/W); rw [one_div,← div_eq_mul_inv,← mul_div_assoc]; gcongr; simp
lemma tranquil (J:Finset A){f: A→ I→ E×F→ H}(h:∀ j∈J,quiet z (f j) a)(hp:∀ i,0≤a i): quiet z (fun i p =>∑ j∈J,f j i p) a:= fun b=> Costs.sum _ (fun i hi=> h i hi b) (fun i p _=> div_nonneg (hp i) (pow_nonneg ((path z).weight_pos i p.1).le _))
lemma Cquiet {f:I→ E×F→ ℂ}{u:I→ℂ}(h:quiet z f a)(he:scaleC z b fun i=>‖u i‖): quiet z (fun i p=>u i*f i p) (fun i=> a i*b i):= by simp_rw [mul_comm (u _)]; exact h.mul (at_rate he)
end rapid
end YM.MS.Rock
