import YM.RegulatorIR.Momentum.Arcs

/-!
# Integrating over the anchor. No power of L for each relative field, even
at strict degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry Spatial
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y W:Type} {u m i r s:ℕ}

def anchored (x:X) (T:Packet X (r+1)):Packet X r:= fun v=> T (Fin.cons x v)
def Held (T: Packet (Long X) (r+1))(u:ℕ)(c:ℝ≥0∞):Prop:=∀ i, quota (anchored i T) (wall (area i) 1 u) ≤ c
def MomentsP (T:Packet (Long X) (r+1))(m:ℕ)(c:ℝ≥0∞):Prop:=∀ i A,∀ j<m,∀ x, ‖readsP (anchored i T ∘ charges (area i) A) j x‖ₑ≤ c
-- absolute summability before any taper.Pivot. (compare ENNReal not signed until summability)
variable [Fintype X] (K:Fin (r+1)→ Layer (Long X) (Long Y)) (T:Packet (Long X) (r+1))
def reports (y:Tuple (Long Y) (r+1)) (x:Tuple (Long X) (r+1)):ℝ:= T x * ∏ i, K i (x i) (y i)

variable {C F A B:ℝ≥0∞} (hf: C≠⊤)(ha:A≠⊤)(hF:F≠⊤)
variable (S:∀ i, PriceW (K i) s u m F)(G:RootsBudget (K 0) s u C)(H: Held T u A)
variable (ht: 0<s)
include H S hF ha hf ht G
omit [Fintype X] in
lemma full_abs (y: Long Y) (v : Tuple (Long Y) r) : quota (reports K T (Fin.cons y v)) 1≠⊤:=by
 -- rows/columns alone, no wall output here. Need held input for absolute. finite constants. Bring $K x ≤F$
 rw [← quota_perm (Tuple.glueEquiv (Long X) r), show (1 : Tuple (Long X) _→_) ∘ (glueEquiv (Long X) r)= (1:Long X × Tuple (Long X) r→_) from rfl,quota_base]; rw [ENNReal.tsum_prod'];
 have h₀ : (∑'x:Long X, ‖K 0 x y‖ₑ) ≤ C:= by simpa only [← quota_base] using! (quota_mono _ (fun x:Long X=>quote_one (area x) y _ _)).trans (G y)
 have hq (i:Fin (r+1))(x:Long X)(t:Long Y): ‖K i x t‖ₑ ≤ F:= by
    have he:quota (K i x) (fun q=> quotes (area x) q s u) ≤ F*award s:= by
       have hz:= (S i).cost (area x) (tariff x) [] (by simp) 0; simpa only [show ask (area x) (tariff x)=x from rfl,journey,windA,add_zero,List.length_nil,pow_one] using hz
    have hh:= term_le (K i x) _ t|>.trans he
    exact (mul_one _).ge.trans (mul_le_mul_right (quote_one _ _ _ _) _) |>.trans hh |>.trans ((mul_le_mul_right (show award s ≤ 1 from by simpa only [award,inv_one] using ENNReal.inv_le_inv.mpr (show 1≤ (s:ℝ≥0∞) by exact_mod_cast ht)) _).trans (mul_one _).le)
 apply ne_top_of_le_ne_top (show (C*(A * F^r))≠⊤ from ENNReal.mul_ne_top hf (ENNReal.mul_ne_top ha (ENNReal.pow_ne_top hF)))
 calc
    _ ≤ ∑' x:Long X, ‖K 0 x y‖ₑ*(A*F^r):= ENNReal.tsum_le_tsum (fun x=>?_) -- goals later
    _ ≤ _:=by rw [ENNReal.tsum_mul_right]; exact mul_le_mul_left h₀ _
 apply le_trans _ (mul_le_mul_right (mul_le_mul_left (le_trans (quota_mono (anchored x T) fun w=>wall_one (area x) 1 u w) (H x)) (F^r)) ‖K 0 x y‖ₑ)
 rw [show quota (anchored x T) (fun _=> (1:ℝ≥0∞)) = ∑' z,‖T (Fin.cons x z)‖ₑ from quota_base (anchored x T),← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum
 intro b; change ‖reports K T (Fin.cons y v) (Fin.cons x b)‖ₑ ≤ _; unfold reports;rw [Fin.prod_univ_succ]; simp only [Fin.cons_succ,Fin.cons_zero,enorm_mul,mul_left_comm ‖K 0 x y‖ₑ]; apply mul_le_mul_right _; apply mul_le_mul_right
 have hE (L:Finset (Fin r)): ‖∏ i∈L,K i.succ (b i) (v i)‖ₑ ≤ F^L.card:=by induction L using Finset.induction_on with
   | empty=>simp
   | insert i L h ih=> rw [Finset.prod_insert h,Finset.card_insert_of_notMem h,enorm_mul,pow_succ, mul_comm _ F]; exact mul_le_mul' (hq ..) ih
 simpa using hE Finset.univ

omit [Fintype X] in
lemma anchored_charge (y:Long Y) (v:Tuple (Long Y) r) : anchored y (unfoldQ K T) v= ∑' x:Long X,K 0 x y * unfoldQ (fun i:Fin r=>K i.succ) (anchored x T) v:=by
 change (∑' x, reports K T (Fin.cons y v) x)= _
 let e:= Tuple.glueEquiv (Long X) r; let g:=reports K T (Fin.cons y v); let f:= g ∘ e
 have hz: Summable (reports K T (Fin.cons y v)):= quota_summable (fun _=> le_rfl) (full_abs K T hf ha hF S G H ht y v)
 change Summable g at hz; have hp:Summable (g ∘ e) := e.summable_iff.mpr hz
 rw [← e.tsum_eq (reports K T _)];change (∑' t, (g ∘ e) t)= _;rw [hp.tsum_prod]; apply tsum_congr; intro a
 rw [unfoldQ,← tsum_mul_left]; apply tsum_congr;intro b;change T (Fin.cons a b)*(∏ i,K i _ _) = _;rw [Fin.prod_univ_succ]; exact mul_left_comm ..
variable (M: MomentsP T m B)
include M
lemma band (hr:m ≤ u) : Held (unfoldQ K T) u (C*((1+r:ℝ≥0∞)^u*seedQ F s r u * (ledger_c X r u m*award s ^m * A + ledger_d X r m * B))):=by
 intro i
 let f (x:Long X)(v:Tuple (Long Y) r):= K 0 x i * unfoldQ (fun i:Fin r=> K i.succ) (anchored x T) v
 let W:=wall (area i) 1 u (X:=Y) (r:=r);let C':=(1+r:ℝ≥0∞)^u; let Z:=seedQ F s r u;let A':= ledger_c X r u m * award s^m
 let c:=fun (x:Long X)=> quotes (area x) i s u
 rw [show anchored i (unfoldQ K T)=fun v=>∑' x, f x v from funext fun v=> anchored_charge K T hf ha hF S G H ht i v]
 apply (inside_quota _ _).trans; unfold quota; rw [ENNReal.tsum_comm]; apply le_trans _ (mul_le_mul_left (G i) _)
 rw [quota,← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro x
 change quota (f x) W ≤ (‖K 0 x i‖ₑ*c x)*(C'*Z*(A'*A+ledger_d X r m * B)); unfold f; rw [quota_times];rw [mul_assoc (‖K 0 x i‖ₑ)]; apply mul_le_mul_right
 let g:= unfoldQ (fun i:Fin r=> K i.succ) (anchored x T); let h (v:Tuple (Long Y) r):= wall (area x) s u v
 apply le_trans (quota_mono (g) (u:=fun v=> h v*(c x*C')) (fun v=>?_)) ?_
 · rw [quota_raised]; apply le_trans (mul_le_mul_left (approval (fun i:Fin r=> K i.succ) (area x) (anchored x T) ht (fun i=> S i.succ) hr hF (ne_top_of_le_ne_top ha (H x)) (M x)) (c x*C'))
   apply le_trans (mul_le_mul_left (mul_le_mul_right (add_le_add_left (mul_le_mul_right (H x) _) _) _) _); apply le_of_eq; change Z*(A'*A+_) * (_*C')= c x*(C'*Z* _);ring
 apply le_trans (b:=wall (area i) 1 u (Fin.cons i v)) (price_held i v|>.symm.le); apply le_trans (porter_width i v (area x) ht); rw [mul_comm, mul_comm C']
end YM.RegulatorIR.Momentum
