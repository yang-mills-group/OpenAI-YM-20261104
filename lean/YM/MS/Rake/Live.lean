import YM.MS.Rake.Solo
/-!
# Warm lengths all around negative times
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open scoped Topology ContDiff Interval
variable {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{G:Gauge}{S:Scale I}
 {f:E→F}{T p:ℝ}{b c:Bool}{z a:I→ℝ}{n:ℤ}
lemma a_e (x:ℝ)(z:ℤ): exp x ^ z = exp ( x * z ):= by rw [← Real.rpow_intCast, Real.exp_mul]
lemma transport (hp:total (Job.single Unit) (fun _=>f) 1)(hx:∀ i,‖a i‖≤T)(hT:T≥0) : total (Job.single I) (fun i=> era (exp (a i)) f n ) 1:= by
   let P:=exp T; have hs:P>0:= exp_pos _; intro b; let Ht:= ( hp b ).smooth (); refine ⟨ fun i=> grow_r Ht _,fun j=>?_⟩; obtain ⟨C,hC,hp⟩:= balance hp b j; let V:=(j:ℤ)+n; let W:= exp (T*|(V:ℝ)|); have hW:0<W:= exp_pos _; refine ⟨ C*W* P^b,(by positivity),0,fun i p ht=>?_⟩; dsimp only; rw [era_spec (exp_pos _) Ht, pow_zero,mul_one]; let u:= exp (a i); have hU:u>0:= exp_pos _; obtain ⟨ha,hp'⟩:= abs_le.mp (show |a i|≤T from hx i)
   have he: P⁻¹ ≤ u:= (by unfold P; rw [ ← Real.exp_neg ]; exact exp_monotone ha ); have hsV : u^V ≤ W:= by unfold W u; rw [ a_e ]; apply exp_monotone; apply le_trans ( le_abs_self _ ); rw [abs_mul]; gcongr; exact hx i
   have hw: 1+‖p‖ ≤ P*(1+‖u • p‖):= by rw [norm_smul_of_nonneg hU.le]; have h:P≥1:= Real.one_le_exp hT; have hV : 1 ≤ u*P:= (div_le_iff₀ hs).mp (by simpa using he); nlinarith [ norm_nonneg p]
   obtain hl:=hp (u • p); apply le_trans (mul_le_mul_of_nonneg_left hl (zpow_nonneg hU.le V)); simp only [Scale.weight, one_pow,Job.cw,Pi.one_apply,mul_one,one_mul];
   apply le_trans (mul_le_mul_of_nonneg_right hsV (div_nonneg hC.le (pow_nonneg (by positivity) _))); rw [← mul_div_assoc,← mul_div_assoc,mul_one,div_le_div_iff₀ (by positivity) (by positivity), mul_comm W, mul_assoc _ (P^b), ← mul_pow]; gcongr -- patch
variable (G I)
lemma Upcoming : BackF (fun (_:I)=> PlanetD G):= by
   constructor; · exact fun _ j k p=> crossD G j k p
   intro i T hT s t; simp only [tap,Pi.one_apply, cw,one_zpow,mul_one]; convert transport (star_r s t) (fun i=> htT i) hT ( n:=(4:ℤ)-wfield s-wfield t ) using 1; ext; rw [planetEra]; rfl -- match
lemma sugar {F:Planet G I}(h:BackF F) : S0 F:=⟨ h.span, fun i t ht s j=> Latch.polar (h.cost i t ht s j ) ⟩
lemma raise_here {t:ℝ}(p:camp t): exp (tstart p) ≤ exp t:= exp_monotone p.2.property.2
lemma cap_M {T:ℝ}: paid (Job.single (camp T)) (fun s=> exp (tstart s)) 1:= ⟨_,exp_pos T,0,fun i=> by simpa only [pow_zero, Pi.one_apply, mul_one] using raise_here i⟩
lemma HereL : BackF (fun (_:I)=> PlanetL G):= by
   refine ⟨ fun _ i j p=> continuous_const.mul (continuousLb G i j p), fun _ t ht i j=>?_⟩; intro b; obtain hv := crown (S:=Job.single (camp t)) (a:=tstart) raise_here (fun _=> rfl) i j b; simp_rw [Job.cw,one_zpow,one_mul] at hv ⊢; refine hv.raise ?_; simp_rw [div_eq_mul_inv]; exact Cost.Le.cancel (paidStrict _ cap_M) ( fun i p _=> inv_nonneg.mpr (pow_nonneg ((Job.single (camp t)).weight_pos ..|>.le) _))
lemma MainL : S0 (fun (_:I)=> LowP G):= by
   refine ⟨ fun _ i j p=> continuousLb G i j p, fun i t hp j k=>?_⟩; obtain hh:=cost_L0 (S:=Job.single (camp t)) (a:=tstart) raise_here (fun _=> rfl) j k; simp_rw [Job.cw,one_zpow,one_mul] at hh ⊢; exact hh.raise (paid_at cap_M (fun _=>zero_le_one))
end YM.MS.Rake
