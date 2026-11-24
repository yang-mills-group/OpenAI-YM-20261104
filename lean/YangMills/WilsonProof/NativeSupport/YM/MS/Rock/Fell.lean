import YM.MS.Rock.Fell
import YM.MS.Arts.Tone
import YM.MS.Arc.Doves
/-!
# Cost forest for D-dimensional amplitudes

Uniform in `z` via Gal, or generic index `ι` with Gain. Prices here for all
 W even in bulk rows. Also `fell` includes finiteD tests only; projection to
 any via `Fin Canon`. Logs assigned later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
variable {G:Gauge}{I E F H J:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup H] [NormedSpace ℝ H]
-- line price
def rib (z:UScale I)(a:I→ℝ)(f:I→Rip G): Prop:= ∀ m p q, Line (path z) (fun _=>Set.univ) (fun i=> f i m p q) a
def scaleC (z:UScale I)(a:I→ℝ)(f:I→ℝ) : Prop:= ((path z).strict fun _=> (Set.univ:Set ℝ)).Le (fun i _=>f i) (fun i _=>a i) -- f costs
variable {z:UScale I}{a b:I→ℝ} {f v:I→ E→ F}{u:I→ E→ℂ}{r s: I→ ℝ}
lemma fasten {w:I→H} (hp:scaleC z a (fun i=>‖w i‖)) {S:Cost I E}(hs:∀ i x,x∈S.zone i→ (path z).basic i ≤ S.cheap i x): Costs S (path z) (fun i _=>w i) (fun i _=>a i):= by
   obtain ⟨C,hC,b,hb⟩:= hp; refine Costs.scalar ⟨C,hC,b,fun i x hx=>?_⟩; refine (hb i 0 (mem_univ _)).trans ?_; have he : (path z).basic i>0:= (path z).basic_pos _; have hB :0≤a i:= by_contradiction fun h=> by
       have hL:(a i)<0:=lt_of_not_ge h; exact (not_lt_of_ge (le_trans (b:=‖w i‖) (norm_nonneg (w i)) (hb i 0 (mem_univ _)))) (mul_neg_of_pos_of_neg (show 0<C*(path z).basic i^b from by positivity) hL)
   change C*(path z).basic i^b*a i≤ C*S.cheap i x^b*_; gcongr; exact hs i x hx
lemma at_rate {w:I→H}(h:scaleC z a (fun i=>‖w i‖)): veg z (fun i (_:E)=>w i) a:= fasten h (fun i x _=> le_mul_of_one_le_right ((path z).basic_pos i).le ((path z).one_le_weight i x))
lemma fall_here (h:veg z f a)(i:I): veg 0 (fun _:Unit => f i) 1:= by
   refine hike (fun _=>h.smooth i) ?_; intro j; obtain ⟨C,hC,b,hb⟩:=ride h j; let U:=C*(1+|z i|)^b; have ha:=terrain h i; have hU : U>0:= by unfold U; positivity
   refine ⟨U*(a i+1),mul_pos hU (by linarith),b,fun _ p=>?_⟩; refine (hb i p).trans ?_; simp only [mul_pow, Pi.zero_apply,Pi.one_apply,abs_zero,add_zero,one_mul,mul_one,← mul_assoc C]; change U*_ * a i≤ U*(a i+1)*_; rw [mul_right_comm]; gcongr; simp -- goal cleanup
lemma step_here {v0:I→ E× F→H}(h:quiet z (fun i (x:E×F)=>v0 i x) a) (i:I): Ultra (v0 i):= by
   refine Q.fromM (fun _=>h.smooth i) ?_; intro j k; obtain ⟨C,hC,b,hb⟩:=Q.man h j k; let L:=C*(1+|z i|)^b; have hz: L>0:= by unfold L; positivity
   have hV:= Q.nonneg h i; refine ⟨L*(a i+1),mul_pos hz (by linarith),b,fun _ p q=>?_⟩; refine (hb i p q).trans ?_; simp only [mul_pow, Pi.zero_apply,Pi.one_apply,abs_zero,add_zero,one_mul,mul_one,← mul_assoc C]; change L*_*a i≤ L*(a i+1)*_; rw [mul_right_comm]; gcongr; simp
lemma ride_peak {f':I→ F→H}{A: E→L[ℝ] F}{C:F→L[ℝ] E} (h:Line (path z) (fun _=>Set.univ) f' a)(hv:∀ x,C (A x)=x) : Line (path z) (fun _=>Set.univ) (fun i (p:E)=> f' i (A p)) a:= by
   intro b; let S := path z; have ht : ((path z).strict fun _=> (Set.univ:Set E)).Le (fun i p=> (path z).basic i) (fun _ _=>1) := ⟨1,zero_lt_one,1,fun i p hp=> by simp [Scale.strict]⟩
   have he:= Costs.linear A (h b) (fun i _ _=> mem_univ _) ht; refine he.raise ⟨(1+‖C‖)^b,pow_pos (by positivity) _,0,fun i p hp=>?_⟩
   rw [pow_zero,mul_one]; have hz:= Cost.Part.nonneg _ ((h b).quoted 0) i (A p) (mem_univ _); have hQ : 0 ≤ a i:= by have he :=(h 0).nonneg i 0 (mem_univ _); simpa only [pow_zero,div_one] using he
   have hL : S.weight i p≤ (1+‖C‖)*S.weight i (A p):= (by nth_rw 1 [← hv p]; exact S.weight_L ..)
   have hw : (p:F)→ S.weight i p >0:= fun p=> S.weight_pos i p; have ht:= S.weight_pos i p; change a i / S.weight i (A p)^b ≤ (1+‖C‖)^b * (a i / S.weight i p ^ b); rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos (hw _) _) (pow_pos ht _),mul_comm ((1+‖C‖)^b),mul_assoc,← mul_pow]; gcongr
end YM.MS.Rock
