import YM.Frontier6.Multi.Capture.Stamp

/-!
# Valuation estimates along pricing curves

All strict inequalities on asymptotic prices, relative to a common clock. Useful
for the subpower-versus-power separation of regimes. Outer order or taylor
seminorm requests do not enter this toolkit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Set Finset Topology
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators
structure Fareway (I : Type*) where
   via : Filter I
   scale : I→ℝ
   follows : Tendsto scale via atTop
variable {I J : Type*}
namespace Fareway
variable (T:Fareway I)
variable {X Y:Type*}[SeminormedAddCommGroup X][SeminormedAddCommGroup Y]
structure Mint (f:I→ℝ)(a:ℝ):Prop where
   pos : ∀ᶠ i in T.via,0<f i
   pitch : Tendsto (fun i=>Real.log (f i)/T.scale i) T.via (𝓝 a)
def Costs (f:I→X)(a:ℝ):Prop:=∀ b:ℝ, a<b→∀ᶠ i in T.via, ‖f i‖≤ Real.exp (T.scale i*b)
lemma ahead : ∀ᶠ i in T.via, 0 < T.scale i:= T.follows.eventually_gt_atTop _
lemma minted (a:ℝ): T.Mint (fun i=>Real.exp (T.scale i*a)) a:=by
   refine ⟨Eventually.of_forall fun i=>Real.exp_pos _,?_⟩; refine tendsto_const_nhds.congr' (f₁:= fun _:I=> a) (T.ahead.mono fun i hi=>?_); dsimp only; rw [Real.log_exp,mul_comm, mul_div_cancel_right₀ _ hi.ne']
lemma minted_c (a:ℝ)(ha:0<a):T.Mint (fun _=>a) 0:= ⟨Eventually.of_forall fun _=>ha,tendsto_const_nhds.div_atTop T.follows⟩
namespace Mint
variable {T}{f g:I→ℝ}{a b:ℝ}(h:T.Mint f a)
include h
lemma eq (hp:a=b): T.Mint f b:= hp ▸ h
lemma congr (he:f=ᶠ[T.via] g) : T.Mint g a:= by
   refine ⟨?_, h.pitch.congr' ?_⟩; exact (h.pos.and he).mono fun i hi=> hi.2 ▸ hi.1; filter_upwards [he] with i hi; rw [hi]
lemma mul (he:T.Mint g b): T.Mint (fun i=>f i*g i) (a+b):=by
   refine ⟨(h.pos.and he.pos).mono (fun i hi=>mul_pos hi.1 hi.2),(h.pitch.add he.pitch).congr' ?_⟩; filter_upwards [h.pos,he.pos] with i hi hj; rw [Real.log_mul hi.ne' hj.ne',add_div]
lemma div (he:T.Mint g b): T.Mint (fun i=>f i/g i) (a-b):=by
   refine ⟨(h.pos.and he.pos).mono (fun i hi=>div_pos hi.1 hi.2),(h.pitch.sub he.pitch).congr' ?_⟩; filter_upwards [h.pos,he.pos] with i hi hj; rw [Real.log_div hi.ne' hj.ne',sub_div]
lemma inv : T.Mint (fun i=>(f i)⁻¹) (-a):=by simpa only [one_div,zero_sub] using (T.minted_c 1 one_pos).div h
lemma powers (b:ℝ): T.Mint (fun i=>f i^b) (a*b):=by
   refine ⟨h.pos.mono fun _ hi=>Real.rpow_pos_of_pos hi _, (h.pitch.mul_const b).congr' ?_⟩; filter_upwards [h.pos] with i hi; rw [Real.log_rpow hi]; ring
lemma power (n:ℕ) : T.Mint (fun i=>f i^n) (a*n):= by simpa only [Real.rpow_natCast] using h.powers n
lemma cheaper (hs:T.Mint g b)(he:a<b) : ∀ᶠ i in T.via, f i < g i:=by
   let y:=(a+b)/2; have hz:y<b:=by unfold y; linarith
   filter_upwards [T.ahead,h.pos, hs.pos,h.pitch.eventually (gt_mem_nhds (show a<y by unfold y; linarith)),hs.pitch.eventually (lt_mem_nhds hz)] with i hi ha hb hp hq
   exact (Real.log_lt_log_iff ha hb).1 ((div_lt_div_iff_of_pos_right hi).1 (lt_trans hp hq))
lemma within (hs:T.Mint g a): T.Mint (fun i=> max (f i) (g i)) a:=by
   refine ⟨h.pos.mono (fun i hi=>hi.trans_le (le_max_left ..)), ?_⟩; have hh:max a a=a:=by simp
   apply hh ▸ (h.pitch.max hs.pitch).congr' (f₂:=fun i=>Real.log (max (f i) (g i))/T.scale i) ?_; filter_upwards [T.ahead,h.pos,hs.pos] with i hi ha hb
   by_cases ht:f i ≤ g i; rw [max_eq_right ht,max_eq_right (div_le_div_of_nonneg_right (Real.log_le_log ha ht) hi.le)]
   rw [max_eq_left (not_le.mp ht).le,max_eq_left (div_le_div_of_nonneg_right (Real.log_le_log hb (not_le.mp ht).le) hi.le)]
lemma common (hs:T.Mint g a): T.Mint (fun i=>f i+g i) a:=by
   let z i:= max (f i) (g i); have hz:= h.within hs; have ht: T.Mint (fun i=>2*z i) a:= (T.minted_c _ zero_lt_two|>.mul hz).eq (by ring)
   have hv(i):f i+g i≤ 2*z i:= (add_le_add (le_max_left ..) (le_max_right ..)).trans_eq (two_mul _).symm
   refine ⟨(h.pos.and hs.pos).mono (fun i hi=> add_pos hi.1 hi.2), tendsto_of_tendsto_of_tendsto_of_le_of_le' hz.pitch ht.pitch ?_ ?_⟩
   · filter_upwards [h.pos,hs.pos,T.ahead,hz.pos] with i hL hN hi hx; exact div_le_div_of_nonneg_right (Real.log_le_log hx (max_le (le_add_of_nonneg_right hN.le) (le_add_of_nonneg_left hL.le))) hi.le
   filter_upwards [h.pos,hs.pos,T.ahead] with i hL hN hi; exact div_le_div_of_nonneg_right (Real.log_le_log (add_pos hL hN) (hv i)) hi.le
lemma pay : T.Costs f a:=by
   intro b hb; filter_upwards [h.cheaper (T.minted b) hb,h.pos] with i hi hp; simpa only [Real.norm_of_nonneg hp.le] using hi.le
omit h
lemma mass (s:Finset J)(F:J→I→ℝ)(a:J→ℝ)(h:∀ j∈s,T.Mint (F j) (a j)): T.Mint (fun i=>∏ j∈s,F j i) (∑ j∈s,a j):=by
   induction s using Finset.induction_on with
   | empty=>simp only [prod_empty,sum_empty]; exact T.minted_c _ one_pos
   | @insert i s hi ih=> simp_rw [sum_insert hi,prod_insert hi]; exact (h _ (mem_insert_self ..)).mul (ih (fun j hj=>h _ (mem_insert_of_mem hj)))
end Mint
namespace Costs
variable {T}{f g:I→X}{F:I→Y}{a b:ℝ} (h:T.Costs f a)
include h
lemma too (he:a≤b): T.Costs f b:=fun c hc=> h c (lt_of_le_of_lt he hc)
lemma smaller (he:∀ᶠ i in T.via,‖F i‖≤‖f i‖) : T.Costs F a:= fun _ hb=> (he.and (h _ hb)).mono fun _ hi=>hi.1.trans hi.2
lemma cf (he:f=ᶠ[T.via] g): T.Costs g a:= h.smaller (he.mono fun i hi=> by rw [hi])
lemma neg : T.Costs (fun i=> -(f i)) a:= h.smaller (Eventually.of_forall fun i=> (norm_neg _).le)
lemma add (he:T.Costs g a): T.Costs (fun i=> f i+g i) a:=by
   intro b hb; let x:=(a+b)/2; have hx:a<x:=by unfold x; linarith
   have hy:T.Mint (fun i=> 2*Real.exp (T.scale i*x)) x:= ((T.minted_c 2 two_pos).mul (T.minted x)).eq (by ring)
   filter_upwards [h x hx,he x hx, hy.cheaper (T.minted b) (show x<b by unfold x;linarith)] with i hi hh hf
   exact (norm_add_le ..).trans ((add_le_add hi hh).trans (((two_mul _).symm).trans_le hf.le))
lemma sub (he:T.Costs g a): T.Costs (fun i=> f i-g i) a:= by simpa only [← sub_eq_add_neg] using h.add he.neg
lemma from_allowance {Z:I→ℝ}(he:T.Mint Z b)(ha:a<b): ∀ᶠ i in T.via,‖f i‖ ≤ Z i:=by
   let y:=(a+b)/2; have hy:a<y:=by unfold y; linarith
   exact ((h y hy).and ((T.minted y).cheaper he (by unfold y; linarith))).mono fun i hi=> le_trans hi.1 hi.2.le
lemma coordinated {Y':Type*}[SeminormedAddCommGroup Y'](hs:T.Costs F b)(G:I→Y')(ht: ∀ᶠ i in T.via, ‖G i‖ ≤ ‖f i‖*‖F i‖) : T.Costs G (a+b):=by
   intro c hc; let z:=(c-(a+b))/2; have h0:0<z:=by unfold z; linarith
   filter_upwards [ht,h (a+z) (by linarith),hs (b+z) (by linarith)] with i hi ha hb; refine hi.trans ((mul_le_mul ha hb (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_); rw [← Real.exp_add,← mul_add]; congr 2; unfold z; ring
omit h
lemma allows_norm {z:I→ℝ}(h:T.Costs z a)(hl:∀ᶠ i in T.via,‖f i‖≤ z i): T.Costs f a:= h.smaller (hl.mono (fun i hi=> hi.trans (le_abs_self ..)))
lemma free : T.Costs (fun _:I=> (0:X)) a:= fun b hb=>Eventually.of_forall fun i=> by rw [norm_zero]; exact (Real.exp_pos _).le
lemma const (x:X) : T.Costs (fun _=>x) 0:= allows_norm (T.minted_c (1+‖x‖) (by positivity)).pay (Eventually.of_forall fun _=> le_add_of_nonneg_left zero_le_one)
lemma unlimited (z:ℝ) (he:∀ᶠ i in T.via, ‖f i‖≤ z): T.Costs f 0:= allows_norm (const _) he
lemma sum (s:Finset J)(G:J→I→X)(ht:∀ j∈s,T.Costs (G j) a): T.Costs (fun i=>∑ j∈s,G j i) a:= by induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; exact free
   | @insert j s hx ih=> simp only [sum_insert hx]; exact (ht _ (mem_insert_self ..)).add (ih (fun j h=> ht _ (mem_insert_of_mem h)))

lemma norm {f:I→X} (h:T.Costs f a):T.Costs (fun i=>‖f i‖) a:=h.smaller (Eventually.of_forall (fun i=> by rw [Real.norm_of_nonneg (norm_nonneg _)]))
lemma mul {R:Type*}[SeminormedRing R]{u v:I→R}(hh:T.Costs u a)(hv:T.Costs v b): T.Costs (fun i=> u i*v i) (a+b):=hh.coordinated hv _ (Eventually.of_forall fun i=> norm_mul_le ..)
end Costs
end Fareway
end YM.Frontier6.Road
