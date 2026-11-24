import YM.WilsonCoeffUV.Product.I.Cruise
/-!
# I-decay at all horizons
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open scoped Topology BigOperators
open PowerSeries
open Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
variable {U V:Type*}{N M k e t m n u i r z:ℕ}{A:ℝ}{G:Gauge}
open Ore
variable {C D E W:Credit}{c b i j r N M k e m u:ℕ}{t x Z δ:ℝ}{R:Realm G (e+1) E}{η:ℕ→ℝ}
structure PadRank (V:Realm G e E)(m c:ℕ)(Z:ℝ) : Prop where
   year (i:ℕ):m ≤ i → i ≤ c → V.y i ≤ Z
   lengthS : ((c-m:ℕ):ℝ)≤ Z
lemma PadRank.frugal (R:Realm G e E)(v:R.anchor ≤ m)(p:m ≤ c) : PadRank R m c (R.y m+(R.draws.S.scale c-R.draws.S.scale m)+(c-m:ℕ)):=by
    refine ⟨fun i a b=> (R.age m i v a).trans ?_, le_add_of_nonneg_left ?_⟩; · linarith only [scales R.draws.S b,Nat.cast_nonneg (α:=ℝ) (c-m)]
    linarith [scales R.draws.S p,R.depth m v]
lemma PadRank.pos (h:PadRank R m c Z)(p:Escort R m c η):1≤Z:= (R.depth m p.ham).trans (h.year m le_rfl p.lane)
lemma PadRank.zone (h:PadRank R m c Z)(p:m ≤ i)(g:j≤ c) : PadRank R i j Z:= ⟨fun _ x z=> h.year _ (p.trans x) (z.trans g),(Nat.cast_le.mpr (show j-i≤c-m by omega)).trans h.lengthS⟩

def BulkCert (G:Gauge)(k e u i r:ℕ)(E W C:Credit):Prop:= ∀ R:Realm G (e+1) E,Dormitory R k u W → ∀ m c η N Z, Escort R m c η → PadRank R m c Z→ c≤N→∀(P:Era G ℝ) (A:ℝ),Auth k P →0≤ A →Saturation e 0 u P.2 (η c) A→ Fruit 0 (η m) u ((cruises R.draws R.paid N k c m P).2 i r) (C.buy Z*A)
lemma BulkCert.more (p:BulkCert G k e u i r E W C)(h:∀ x:ℝ,1≤x→ C.buy x ≤ D.buy x):BulkCert G k e u i r E W D:=fun R t m c η N Z p' q u P A x v w=> (p R t m c η N Z p' q u P A x v w).more (mul_le_mul_of_nonneg_right (h _ (q.pos p')) v)
lemma BulkOver (p:k+i<r):BulkCert G k e u i r E W C:=by
   intro R t m c η N Z p' q u P A x v w; rw [(cruising R.draws R.hG R.green p'.lane u x).coverN i r p]; refine Fruit.zero.more (mul_nonneg (zero_le_one.trans (C.purchase (q.pos p'))) v)

lemma delta_tick (C:Credit)(_p:1≤x)(_e:A≥0)(f:m<c): A+((c-(m+1):ℕ):ℝ)*(C.buy x*A)+C.buy x*A=A+(c-m:ℕ)*(C.buy x*A):=by
    have h:c-(m+1)+1=c-m:=by omega
    rw [←h]; push_cast; ring
lemma value_tick (C:Credit)(S:Schedule)(p:1≤x)(e:A≥0)(f:m<c)(r:ℕ){X:ℝ}(hp:X≤ C.buy x*A): lowRep S m r*(A+((c-(m+1):ℕ):ℝ)*(C.buy x*A))+X≤ A+(c-m:ℕ)*(C.buy x*A):=by
   have h : lowRep S m r ≤ 1:=by unfold lowRep; split; exact le_rfl; exact Real.exp_le_one_iff.mpr (by linarith [PathCost.arc_nn S m])
   have ht:= zero_le_one.trans (C.purchase p); exact (add_le_add (mul_le_of_le_one_left (by positivity) h) hp).trans_eq (delta_tick _ p e f)
def TickB (C:Credit):= Credit.unit.plus (Credit.leanC.prodC C)
lemma full_tick (C:Credit)(p:1≤x)(e:A≥0)(h: (b:ℝ)≤x) : A+(b:ℝ)*(C.buy x*A) ≤ (TickB C).buy x*A:=by
   rw [←mul_assoc]; refine (le_trans ?_ (mul_le_mul_of_nonneg_right (Credit.fuel Credit.unit (Credit.leanC.prodC C) p) e)); rw [Credit.products,Credit.unit_cost,Credit.lean_cost,add_mul,one_mul]; exact add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (zero_le_one.trans (C.purchase p))) e) _

lemma valueBulk (p:i≤e)(w:r≤k+i)(h:∀ i' j,lowerGrade i' j i r →BulkCert G k e u i' j E W C): ∃ K:Credit,BulkCert G k e u i r E W K:=by
   let L:= ticketL G e k i r u E W; let X:=L.prodC C
   refine ⟨TickB X,fun R t m c η N Z g f q P A x v z=>?_⟩; let F j:= cruises R.draws R.paid N k c j P; have hz:= f.pos g
   suffices H:∀ j≤c,m≤ j → Fruit 0 (η j) u ((F j).2 i r) (A+(c-j:ℕ)*(X.buy Z*A)) by exact (H m g.lane le_rfl).more (full_tick X hz v f.lengthS)
   intro n hn; induction hn using Nat.decreasingInduction with
   | self=> intro b; unfold F; rw [cruises_top,Nat.sub_self,Nat.cast_zero,zero_mul,add_zero]; exact z i p r (Nat.zero_le _)
   | of_succ b he ih=>
      intro a; let B:=F (b+1); have hb:m≤ b+1:=by omega
      have H:= g.he b a he.le; have hp:Auth k B:= cruising R.draws R.hG R.green he q x; have heq:=g.ham.trans a
      let K:=C.buy Z*A; let θ:= thinLevel R.draws b (η b); have hy:= zero_le_one.trans (C.purchase hz); have hk:0≤K:=mul_nonneg hy v
      have hx l j (v':lowerGrade l j i r): Fruit 0 θ u (B.2 l j) K:= (h l j v' R t (b+1) c η N Z (g.clip hb he le_rfl) (f.zone hb le_rfl) q P A x v z).shave (g.frost a he) (g.stern b a he)
      unfold F; rw [cruises_sub _ _ _ _ _ he]; apply (amen R t heq (he.trans_le q) p (by omega) B hp H (g.hp b a he.le) ((ih hb).shave (g.frost a he) (g.stern b a he)) hk hx).more; apply value_tick X R.draws.S hz v he; unfold X; rw [Credit.products,mul_assoc]; exact mul_le_mul_of_nonneg_right (L.elder (R.depth b heq) (f.year _ a he.le)) hk
lemma bulkCert (G:Gauge)(k e u:ℕ)(E W:Credit): ∃ C:Credit,∀ i≤e,∀ j,BulkCert G k e u i j E W C:=by
    apply seasonsPaid (fun i j C=> BulkCert G k e u i j E W C) k e _ (fun i j v _=> BulkOver v) (fun _ _ _ _ h q=>q.more h); intro i v r W h; by_cases hp:r≤k+i; exact valueBulk v hp h; exact ⟨W,BulkOver (by omega)⟩
end YM.WilsonCoeffUV.Mer
