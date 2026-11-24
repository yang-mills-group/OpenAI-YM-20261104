import YM.MS.Damping
import YM.MS.PricedLine
/-!
# Oscillatory and high density estimates in rapid cost norms. Translation gain.
Use a finite-difference proof also at discrete positive measures. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Osc
open Set Filter Function Finset Metric MeasureTheory Real
open scoped Topology ContDiff
variable {I J E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G] {C:ℝ} {z:Scale I}
   {i:I}{u:E} {x:I→ℝ}{f g:I→ E×F→ G}{T:I→E}
def Captain (S: Scale I)(c:ℝ)(x y:E)(i:I): Prop:= S.length i* ‖x-y‖ ≤ c
omit [NormedSpace ℝ E] in
lemma windy {x y:E} (h: Captain z C x y i) (hp:C≥0): z.weight i x ≤ (1+C)* z.weight i y:= by
    unfold Captain at h; have ha := mul_le_mul_of_nonneg_left (norm_sub_norm_le x y) (z.pos i|>.le); unfold Scale.weight; have ht :0≤ z.length i * ‖y‖ := mul_nonneg (z.pos i|>.le) (norm_nonneg y); nlinarith
omit [NormedSpace ℝ E] in
lemma windy_pay {x y:E}{c d:ℝ}(h:Captain z C x y i) (hp:C≥0)(b:ℕ)(hc:c≥0)(hd:d≥0): c/z.weight i y^b *d ≤ (1+C)^b*(c/z.weight i x^b*d):= by
    have he:= z.weight_pos i y; have hv:= z.weight_pos i x; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hd; rw [← mul_div_assoc, mul_comm _ c,div_le_div_iff₀ (by positivity) (by positivity), mul_assoc,← mul_pow]; gcongr; exact windy h hp
abbrev pole (z:Scale I)(f:I→E× F→G)(x:I→ℝ): Prop:= Rapid z (fun _=>Set.univ) f x
-- ambient sup
lemma sane (h:pole z f x) (i:I):0≤x i:= h.nn i (0,0) trivial
lemma speed (h:pole z f x)(hp:∀ i,z.length i* ‖T i‖≤ C)(hx:0≤ C): pole z (fun i (x:E× F)=>f i (x+(T i,0))) x:= by
   intro b; refine ⟨fun i=> (h.smooth i).comp (f:=fun x:E × F=> x+(T i,0)) (by fun_prop), fun j=>?_⟩; obtain ⟨M,hM,k,hk⟩:= (h b).quoted j; let H:=(1+C)^b; refine ⟨M*(1+C)^b,mul_pos hM (by positivity),k,fun i p hpv=>?_⟩; dsimp only; rw [ iteratedFDeriv_comp_add_right ]; apply (hk i (p+( T i,0)) trivial).trans; rcases p with ⟨a,b'⟩; simp only [Scale.slow,Prod.mk_add_mk,add_zero]; change M* z.full.cheap i b'^k * ( x i / z.weight i (a+T i)^b * z.length i^j ) ≤ _; conv_rhs=> rw [mul_right_comm M ((1+C)^b), mul_assoc ( M*_ )];
   apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM.le (pow_nonneg (z.full.cheap_pos trivial).le _)); exact windy_pay (C:=C) (by simpa [Captain] using hp i) hx _ (sane h i) (pow_nonneg (z.pos i).le _) -- zpow nonneg?
lemma billed (h:pole z f x)(hx:0≤ C)(b j:ℕ):∃ M:ℝ,0<M∧∃ k:ℕ,∀ i (p q:E)(s:F), Captain z C p q i→ ‖iteratedFDeriv ℝ j (f i) (q,s)‖ ≤ M*z.full.cheap i s^k*(x i/z.weight i p ^b * z.length i^j):= by
    obtain ⟨A,hA,k,hk⟩:= (h b).quoted j; refine ⟨ _,mul_pos hA (pow_pos (show (0:ℝ)<1+C by positivity) b),k,fun i p q s ht=>?_⟩; refine (hk i (q,s) trivial).trans ?_; change A*z.full.cheap i s^k *(x i/z.weight i q^b*_)≤_; conv_rhs=> rw [mul_right_comm A ((1+C)^b), mul_assoc (A * _)];
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA.le (pow_nonneg (z.full.cheap_pos trivial).le _)); exact windy_pay ht hx _ (sane h i) (pow_nonneg (z.pos i).le _)
-- difference integrated in real t.W
abbrev shift (T:I→E)(f:I→ E × F→G)(i:I)(p:E× F):= f i p-f i (p+(T i,0))
lemma step (h:pole z f x)(hp:∀ i,z.length i * ‖T i‖ ≤ C)(hx:0≤ C): pole z (shift T f) (fun i=>x i*(z.length i*‖T i‖)):= by
   have ht:= speed h hp hx; intro b; refine ⟨fun i=>( h.smooth i ).sub (ht.smooth i), fun j=>?_⟩; obtain ⟨M,hM,k,hk⟩:= billed h hx b (j+1); refine ⟨M,hM,k,fun i p h' =>?_⟩; obtain ⟨a,y⟩:=p;
   dsimp only; rw [show iteratedFDeriv ℝ j (shift T f i) (a,y)=_ from iteratedFDeriv_sub_apply ( (h.smooth i).contDiffAt.of_le (by exact_mod_cast le_top)) ((ht.smooth i).contDiffAt.of_le (by exact_mod_cast le_top))]; rw [iteratedFDeriv_comp_add_right]; -- Ny
   let f':= iteratedFDeriv ℝ j (f i); let c:= T i; let P:= fun u: ℝ=> ( a+u • c,y ); have hs (u:ℝ):‖fderiv ℝ f' (P u) (c,0)‖ ≤ ‖ fderiv ℝ f' (P u)‖ * ‖c‖:= by convert (fderiv ℝ f' ( P u )).le_opNorm (c,0) using 1; rw [Prod.norm_mk,_root_.norm_zero,max_eq_left (norm_nonneg _)]
   have hr (u:ℝ)(hu:u∈Set.Icc 0 1): Captain z C a (a+u • c) i:= by simp [Captain, sub_add_cancel_left, norm_neg,norm_smul_of_nonneg hu.1]; refine le_trans ?_ (hp i); exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg c) hu.2) (z.pos i).le -- `sub_add_cancel_left` wrong lemma
   let Y (j':ℕ) := M*z.full.cheap i y^k*( x i / z.weight i a^b * z.length i^j'); have hm := norm_image_sub_le_of_norm_deriv_le_segment_01' ( C:=Y (j+1)*‖c‖) ( f:=f'∘P ) (f':=fun u=>fderiv ℝ f' ( P u ) (c,0)) ( fun u hu=> HasDerivAt.hasDerivWithinAt ((h.smooth i|>.differentiable_iteratedFDeriv (m:=j) (by exact_mod_cast (WithTop.coe_lt_top j)) _).hasFDerivAt.comp_hasDerivAt u ?_)) (fun u hu=> (hs u).trans ?_); rotate_left -- subgoals order!
   · convert (( ( hasDerivAt_id' u ).smul_const c ).const_add a).prodMk ( hasDerivAt_const u y ) using 1 <;> (first|rfl|ext <;> simp) -- proof
   · gcongr; rw [show ‖fderiv ℝ f' _‖=_ from norm_fderiv_iteratedFDeriv]; exact hk i a _ y (hr _ ⟨hu.1,hu.2.le⟩) -- goal gcongr extra
   unfold P comp at hm; simp only [one_smul,zero_smul, add_zero] at hm;
   rw [Prod.mk_add_mk,add_zero,norm_sub_rev]; apply hm.trans_eq; unfold Y c Scale.slow; rw [pow_succ,div_eq_mul_inv,div_eq_mul_inv]; ring -- using hm may `add_zero`
def borrow (S:Scale I)(k:J→I): Scale J:={ length:= S.length∘k,basic:= S.basic∘k,one_le i:=S.one_le (k i),pos i:= S.pos (k i) } -- change to def
end YM.MS.Osc
