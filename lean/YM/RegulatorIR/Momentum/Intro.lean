import YM.RegulatorIR.Momentum.Sequences

/-!
# Contract a held-root table with an explicit polar test

Use probed slot costs. This uses moment bounds ONLY on input kernel,
NOT assumes curvature lifting. One genuine moment currency gain on tail,
summing against all coarse output slots. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry
open scoped Topology ENNReal NNReal BigOperators Classical
variable {J X Y:Type}{u m r s:ℕ}

def porter (p:Cover) (T:Tuple (Long X) r) : MovesR r:= fun v=> (area (T v.1)-p) v.2
def charges (p:Cover)(A:Fin r→Regalia X)(v:MovesR r) : Tuple (Long X) r:= fun i=>ask (p+confers v i) (A i)
def transport (p:Cover) (X:Type)(r:ℕ): (Fin r→Regalia X) × MovesR r≃ Tuple (Long X) r where
 toFun i:= charges p i.1 i.2
 invFun v:= (fun i=>tariff (v i),porter p v)
 left_inv i:= Prod.ext rfl (funext (fun v=>by simp only [porter, charges,area, ask,Pi.sub_apply,Pi.add_apply, add_sub_cancel_left,confers]))
 right_inv i:=by ext1 j; refine Prod.ext (Prod.ext ?_ rfl) rfl; ext1 v; change p v + ((area (i j)-p):Cover) v=_; simp [area]

lemma price_par (p:Cover)(t:Tuple (Long X) r) : postage u (porter p t)=wall p 1 u t:=by
 unfold wall awayZ postage; rw [← dollars]; simp only [award,Nat.cast_one,inv_one,one_mul,one_smul];rw [add_comm 1]; congr 2; apply sum_congr rfl;intro i _; exact extent_rev ..
lemma seek (v:MovesR r)(p:Cover)(T:Fin r→ Regalia X): postage u v=wall p 1 u (charges p T v):= by rw [← price_par,show porter p (charges p T v)=v from congr_arg Prod.snd ((transport p X r).left_inv (T,v))]
lemma price_H (p:Cover)(s u:ℕ)(y:Long X)(v:Tuple (Long X) r):wall p s u (Fin.cons y v)=(1+(awayZ p y s +∑ i,awayZ p (v i) s))^u:=by unfold wall; rw [Fin.sum_univ_succ]; simp
lemma price_held (y:Long X)(v:Tuple (Long X) r):wall (area y) 1 u (Fin.cons y v)=wall (area y) 1 u v:=by rw [price_H,awayZ,one_smul,sub_self,extent_zero,mul_zero,zero_add];rfl
lemma cost_basis {T : Packet (Long X) r}(v:Cover)(R:Fin r→Regalia X): quota (T ∘ charges v R) (postage u)≤quota T (wall v 1 u):=by
 rw [show postage u = fun x:MovesR r=> wall v 1 u (charges v R x) from funext fun y=> seek ..]; exact quota_restrict (charges v R) (fun _ _ h=> Prod.mk.inj ((transport v X r).injective h) |>.2) T _

variable (K:Fin r→Long X→Long Y→ℝ)(p:Cover)(T: Packet (Long X) r)
def unfoldQ (K:Fin r→Long X→Long Y→ℝ)(T:Packet (Long X) r) : Packet (Long Y) r:= fun v=> ∑' t:Tuple (Long X) r, T t*∏ i,K i (t i) (v i)
lemma restates (v:Tuple (Long Y) r)(x: (Fin r→Regalia X) × MovesR r): T (transport p X r x)* (∏ i:Fin r,K i ((transport p X r x) i) (v i))= fixed (mint K p x.1 []) (T∘charges p x.1) x.2 v :=by rfl

variable [Fintype X]{F B H:ℝ≥0∞}(hs:0<s) (A:∀ i,PriceW (K i) s u m F)(ht: m≤u)
variable (hc:F≠⊤)(hb:quota T (wall p 1 u)≠⊤)

def seedQ (F:ℝ≥0∞)(s r u:ℕ):ℝ≥0∞:= (F*award s)^r*2^u
lemma small_coin (r u:ℕ) {hs:0<s}(hc:F≠⊤) : seedQ F s r u≠⊤:=by unfold seedQ;exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top hc (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr hs.ne')))) (by finiteness) -- requires h
include p A ht hs hc hb
lemma readyV (v:Tuple (Long Y) r): Summable fun t: Tuple (Long X) r=> T t*∏ i,K i (t i) (v i) :=by
 rw [← (transport p X r).summable_iff]; apply quota_summable (w:=1) (fun _=>le_rfl); rw [quota_base]
 let f(i: (Fin r→Regalia X)× MovesR r):= fixed (mint K p i.1 []) (T∘ charges p i.1) i.2 v
 dsimp only [Function.comp_apply]; simp_rw [restates K p T]; change (∑' i, ‖f i‖ₑ)≠⊤; rw [ENNReal.tsum_prod']; conv_lhs => rw [tsum_fintype]
 refine ENNReal.sum_ne_top.mpr (fun i _=> ?_); apply tsum_enorm_ne_top_iff_summable_norm.mpr
 exact ((collect_all (itinerary_forms K p i A hs) _ (fun _=>wall_one p s u _) ht (small_coin r u (hs:=hs) hc) (ne_top_of_le_ne_top hb (cost_basis p _)) v).1).norm

def ledger_c (X:Type)[Fintype X](r u m:ℕ) := (Fintype.card (Fin r→Regalia X):ℝ≥0∞)*limitedC (Fin r×Axis) u m
def ledger_d (X:Type)[Fintype X](r m:ℕ) := (Fintype.card (Fin r→Regalia X):ℝ≥0∞)* displayC (Fin r×Axis) m
lemma approval (hv:∀ (A:Fin r→Regalia X),∀ i<m,∀ x, ‖readsP (T ∘ charges p A) i x‖ₑ ≤ B): quota (unfoldQ K T) (wall p s u) ≤ seedQ F s r u * (ledger_c X r u m*(award s)^m*quota T (wall p 1 u)+ledger_d X r m*B):=by
 let c:=transport p X r
 let f (t:Tuple (Long Y) r) (i : (Fin r→Regalia X)×MovesR r):=T (c i)*∏ j,K j (c i j) (t j)
 let V (i): Tuple (Long Y) r→ℝ:=receive (mint K p i []) (T ∘ charges p i)
 have he:unfoldQ K T=∑ i,V i:=by
    ext1 v; rw [unfoldQ,← c.tsum_eq (fun t=>T t*∏ j,K j (t j) (v j)),Finset.sum_apply]; let g(t:Tuple (Long X) r):=T t*∏ j,K j (t j) (v j)
    have H:Summable g:=readyV K p T hs A ht hc hb v; have h:Summable (g ∘ c):= c.summable_iff.mpr H
    change (∑' t, (g ∘ c) t)= ∑ i,V i v;rw [h.tsum_prod,tsum_fintype]; rfl
 let W:= wall p s u (r:=r) (X:=Y); let a:=seedQ F s r u; let M:=limitedC (Fin r×Axis) u m; let N:=displayC (Fin r ×Axis) m; let J:=quota T (wall p 1 u)
 rw [he]; apply (quota_sum ..).trans
 calc
    _ ≤ ∑ _:(Fin r→Regalia X),(a*M*award s^m*J+N*(B*a)):= Finset.sum_le_sum fun i _=> (show quota (V i) W ≤ seedQ F s r u * M * award s ^m * quota (T∘ charges p i) (postage u) + N*(B * a) from distilled (itinerary_forms K p i A hs) _ (fun v=>wall_one p s u v) ht (small_coin r u (hs:=hs) hc) (ne_top_of_le_ne_top hb (cost_basis p _)) (hv i)).trans (add_le_add_left (mul_le_mul_right (cost_basis p _) _) _)
    _ = _:=by rw [Finset.sum_const, card_univ,nsmul_eq_mul]; unfold ledger_c ledger_d; change _= a*(_*M*_ *J + (_*N)*_);ring
end YM.RegulatorIR.Momentum
