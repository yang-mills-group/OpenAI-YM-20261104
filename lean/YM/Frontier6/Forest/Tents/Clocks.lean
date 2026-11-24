import YM.Frontier6.Multi.Merge.Consult

/-!
# Renormalizing the clock at a positive band

Value signs: walking *width* uses positive for shrinking.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Set Spec Fareway Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V:Type}{T: Fareway I}{a b:ℝ}
namespace Fareway
def surge (T:Fareway I){b:ℝ}(hb:0<b) : Fareway I:= ⟨T.via,fun i=> b*T.scale i, Tendsto.const_mul_atTop hb T.follows⟩
lemma reach_mint_iff {f:I→ℝ} (he:T.Costs f a)(h:∀ b<a, ∀ᶠ i in T.via,Real.exp (T.scale i*b) ≤ f i): T.Mint f a:=by
   have hp:∀ᶠ i in T.via,0 < f i:= (h _ (show a-1<a from sub_one_lt a)).mono fun i hi=>(Real.exp_pos _).trans_le hi
   refine ⟨hp,tendsto_order.mpr ⟨fun b hb=> ?_,fun b hb=> ?_⟩⟩
   · obtain ⟨c,hc,hc'⟩:= exists_between hb
     filter_upwards [T.ahead,h c hc',hp] with i hi hc' hp; exact lt_of_lt_of_le hc ((le_div_iff₀ hi).mpr (by simpa only [mul_comm c,Real.log_exp] using Real.log_le_log (Real.exp_pos _) hc'))
   obtain ⟨c,hc,hc'⟩:= exists_between hb
   filter_upwards [T.ahead,he c hc,hp] with i hi hc hp; exact lt_of_le_of_lt ((div_le_iff₀ hi).mpr (by simpa only [Real.log_exp,mul_comm c] using Real.log_le_log hp ((show f i≤‖f i‖ from le_abs_self _).trans hc))) hc'
lemma surges {X:Type*}[SeminormedAddCommGroup X] (f:I→ X)(hp:0<b): T.Costs f (b*a) ↔ (T.surge hp).Costs f a:=by
   constructor <;> intro h c hc
   · filter_upwards [h (b*c) (mul_lt_mul_of_pos_left hc hp)] with i hi; exact le_trans hi (le_of_eq (congr_arg Real.exp (by ring : T.scale i*(b*c)=b * T.scale i *c))) -- defeq tactic
   filter_upwards [h (c/b) ((lt_div_iff₀ hp).mpr (by rwa [mul_comm]))] with i hi; change ‖f i‖ ≤ Real.exp (b*T.scale i*(c/b)) at hi; rwa [show b * T.scale i*(c/b)=T.scale i*c by field_simp] at hi
end Fareway
lemma ReachWide.surging {x y:I→ E4}(hp:0<b) (he:ReachWide T x y (b*a)): ReachWide (T.surge hp) x y a:=by
   intro c hc; filter_upwards [he (b*c) (mul_lt_mul_of_pos_left hc hp)] with i hi; convert hi using 2 <;> try rfl
   unfold Fareway.surge; dsimp only; ring
lemma Wide.surging {x:I→ V→ E4}(hp:0<b) (he:Wide T x (b*a)): Wide (T.surge hp) x a:=fun _ _ hi=>(he hi).surging hp
lemma Wide.ties {x:I→V→ E4}(he: Wide T x b)(hh:∀ i:V,T.Costs (fun j=>x j i) (-b))(hb:0<b): Aspect (T.surge hb) x:=by
   have h:∀ i:V,(T.surge hb).Costs (fun j=>x j i) (-1):= fun i=> (surges _ hb).mp (by simpa only [mul_neg,mul_one] using hh i)
   have hf: Wide (T.surge hb) x 1:= Wide.surging hb ((show b*1=b by ring).symm ▸ he)
   exact ⟨h,fun i j hi=> reach_mint_iff ((h i).sub (h j)).norm (fun k hk=>by simpa only [neg_neg] using hf hi (-k) (by linarith))⟩
lemma pin_physical {G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}(K:Final C H S)(hC:Ribbon C H S)
 [Fintype V][DecidableEq V][Nonempty V]{x:I→ V→ E4}(p:I→ E4)(v:V→S.Tag)
 (hx:Wide T x b)(hp:∀ i:V,T.Costs (fun j=>x j i-p j) (-b))(hb:0<b)(d:ℕ)(w:Fin (d+1)):
   T.Costs (fun j=> weight K w (reach K d w (absorb K (p j) d (assembly S (x j) v)))) (b*(load v-(w:ℝ))):=by
   let y(j:I)(i:V):= x j i -p j
   have hz: Wide T y b:=by
       intro i j hi a ha
       filter_upwards [hx hi a ha] with k hk; unfold y; rw [sub_sub_sub_cancel_right]; exact hk -- lemma?
   apply (surges _ hb).mpr; apply (ample K hC v d (hz.ties hp hb) w).cf; filter_upwards with i
   have he:(fun j=> y i j+p i)= x i:=funext fun _=> sub_add_cancel ..
   rw [← throughShift K d (p i) v (x:=y i),he]
end YM.Frontier6.Road
