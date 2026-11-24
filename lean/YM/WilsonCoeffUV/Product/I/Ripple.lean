import YM.WilsonCoeffUV.Product.I.Decay
/-!
# Perturbation price through I-decay
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
def Flush (e u:ℕ)(η:ℝ)(V:Era G ℝ)(A:ℝ): Prop:=0≤A ∧ Saturation e 0 u V.2 η A
structure Fringed (k e u:ℕ)(η:ℝ)(A δ:ℝ)(X Y:Era G ℝ): Prop where
    inkV : Auth k X
    pen : Auth k Y
    crest : 0≤δ
    heapS : ∀ i r, i≤e → YieldP 0 η u A δ (X.2 i r) (Y.2 i r)
variable {P Q:Era G ℝ}
lemma Fringed.rate (q:Fringed k e u t A δ P Q)(h:δ ≤ x): Fringed k e u t A x P Q:=⟨q.inkV,q.pen,q.crest.trans h,fun i r p=> by have H:= q.heapS i r p; exact ⟨H.wax,H.wane,H.toll.more (mul_le_mul_of_nonneg_left h H.nn)⟩⟩
lemma Fringed.pay (q:Fringed k e u t A δ P Q)(h:A ≤ x): Fringed k e u t x δ P Q:=⟨q.inkV,q.pen,q.crest,fun i r p=> (q.heapS i r p).step h q.crest⟩
lemma Fringed.same (p:Flush e u t P A)(q:Auth k P)(h:0 ≤ δ): Fringed k e u t A δ P P:=⟨q,q,h,fun i j v=> YieldP.same (p.2 i v j (Nat.zero_le _)) h⟩
lemma Fringed.nn (q:Fringed k e u t A δ P Q):0≤ A:= (q.heapS 0 0 (Nat.zero_le _)).nn
lemma Fringed.f_l (q:Fringed k e u t A δ P Q) : Flush e u t P A:=⟨q.nn,fun i p j _=> (q.heapS i j p).wax⟩
lemma Fringed.f_r (q:Fringed k e u t A δ P Q) : Flush e u t Q A:=⟨q.nn,fun i p j _=> (q.heapS i j p).wane⟩

def Ripples (G:Gauge)(k e u i r:ℕ) (E W C:Credit): Prop:= ∀ R:Realm G (e+1) E, Dormitory R k u W → ∀ m c η b N M A δ Z,Escort R m c η → PadRank R m c Z→ c≤b→ b≤N→ b≤M→ R.tempC c b≤ δ→ ∀ P Q:Era G ℝ,Fringed k e u (η c) A δ P Q →
    Fruit 0 (η m) u ((cruises R.draws R.paid N k c m P - cruises R.draws R.paid M k c m Q).2 i r) (C.buy Z*A*δ)
lemma Ripples.more (h:Ripples G k e u i r E W C)(q:∀ y:ℝ,1≤y → C.buy y≤ D.buy y): Ripples G k e u i r E W D:= fun R p m c η b N M A δ Z v ht hv ha hb hp X Y z=> (h R p m c η b N M A δ Z v ht hv ha hb hp X Y z).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (q _ (ht.pos v)) z.nn) z.crest)
lemma overL (p:k+i < r) : Ripples G k e u i r E W C:=by
    intro R h m c η b N M A δ Z q H v y w x P Q hp
    rw [((cruising R.draws R.hG R.green q.lane (v.trans y) hp.inkV).sub (cruising R.draws R.hG R.green q.lane (v.trans w) hp.pen)).coverN i r p]; exact Fruit.zero.more (mul_nonneg (mul_nonneg (zero_le_one.trans (C.purchase (H.pos q))) hp.nn) hp.crest)
lemma coreRip (p:i≤e)(z:r≤ k+i)(h:∀ j l,lowerGrade j l i r →Ripples G k e u j l E W C): ∃ V:Credit,Ripples G k e u i r E W V:=by
    obtain ⟨V,H⟩:=bulkCert G k e u E W; let L:= ticketL G e k i r u E W; let X:= ticketU G e k i r u E W; let M:= doubling E; let T':= (X.prodC V).prodC M; let B:=L.prodC C; let U:= B.plus T'
    refine ⟨TickB U,fun R t m c η b N N' A δ Z q H' v y w x P Q hp=>?_⟩
    have ht:= hp.f_l; have hq:= hp.f_r; let F l:= cruises R.draws R.paid N k c l P; let J l:= cruises R.draws R.paid N' k c l Q
    let O:=A*δ; have hO:0≤ O:=mul_nonneg hp.nn hp.crest; let a l:= O+(c-l:ℕ)*(U.buy Z*O); have hz:= H'.pos q
    suffices Hy:∀ l≤c,m≤ l → Fruit 0 (η l) u (((F l)-(J l)).2 i r) (a l) by exact (Hy m q.lane le_rfl).more ((full_tick U hz hO H'.lengthS).trans_eq (Eq.symm (mul_assoc ..)))
    intro l hl; induction hl using Nat.decreasingInduction with
    | self=> intro x; unfold a F J; rw [cruises_top,cruises_top,Nat.sub_self,Nat.cast_zero,zero_mul,add_zero]; exact (hp.heapS _ _ p).toll
    | of_succ l g ih=>
       intro d; have hy:= H'.year l d g.le; have hb:m≤ l+1:=by omega
       have hh:= q.clip hb g le_rfl; have hc:= H'.zone hb (le_refl c); have hv:= q.frost d g; have ha:= q.he l d g.le; have hθ:= q.stern l d g; let Y:= F (l+1); let W':= J (l+1); let n a := verseI (V:=ℝ) R.draws R.paid l a k
       have hY:Auth k Y:= cruising R.draws R.hG R.green g (v.trans y) hp.inkV; have hP:Auth k W':= cruising R.draws R.hG R.green g (v.trans w) hp.pen; let θ:=thinLevel R.draws l (η l)
       have hi:=q.ham.trans d; have hui:= R.depth l hi
       have hK: Fruit 0 (η l) u ((n N Y-n N W').2 i r) (lowRep R.draws.S l r*(a (l+1))+ R.cash L l*(C.buy Z*O)):=by
          let Y':=Y-W'; have hh j i' (b':lowerGrade j i' i r): Fruit 0 θ u (Y'.2 j i') (C.buy Z*O):= by unfold O; rw [←mul_assoc]; exact (h j i' b' R t (l+1) c η b N N' A δ Z hh hc v y w x P Q hp).shave hv hθ
          rw [show n N Y-_=n N Y' from Eq.symm (verse_lin _ R.hG (lt_of_lt_of_le (lt_of_lt_of_le g v) y) R.green hY hP)]
          exact amen R t hi ((g.trans_le v).trans_le y) p (by omega) Y' (hY.sub hP) ha (q.hp l d g.le) ((ih hb).shave hv hθ) (mul_nonneg (zero_le_one.trans (C.purchase hz)) hO) hh
       have htq : δWarm R l b ≤ M.buy Z*δ:=mul_le_mul (M.elder hui hy) ((PathCost.narrow R.draws.S g.le b).trans x) (trail_pos ..).le (zero_le_one.trans (M.purchase hz))
       let Y':=n N W'-n N' W'
       let V':=V.buy Z*A; have hV:0≤ V':=mul_nonneg (zero_le_one.trans (V.purchase hz)) hp.nn
       have hX: Fruit 0 (η l) u (Y'.2 i r) (R.cash X l*V'* δWarm R l b):= (urgent R t hi (g.trans_le v) y w p (by omega) W' W' ha (q.hp l d g.le) hV (fun i r e'=> YieldP.same ((H i (e'.trans p) r R t (l+1) c η N' Z hh hc (v.trans w) Q A hp.pen hp.nn hp.f_r.2).shave hv hθ) (mul_nonneg (zero_le_one.trans (M.purchase hui)) (trail_pos ..).le))).toll
       rw [show F l-J l=n N Y-n N W'+Y' by unfold F J Y' W' Y; rw [cruises_sub R.draws _ _ k P g, cruises_sub R.draws _ _ k Q g]; unfold n; abel]
       apply (hK.plus hX ha).more; rw [add_assoc]; apply value_tick U R.draws.S hz hO g
       have hπ:=mul_nonneg (zero_le_one.trans (C.purchase hz)) hO
       refine le_trans (add_le_add (show _ ≤ B.buy Z*O from ?_) (show _ ≤ T'.buy Z*O from ?_)) ?_
       · rw [Credit.products,mul_assoc]; exact mul_le_mul_of_nonneg_right (L.elder hui hy) hπ
       · apply (mul_le_mul (b:=X.buy Z*V') (mul_le_mul_of_nonneg_right (X.elder hui hy) hV) htq (mul_nonneg (zero_le_one.trans (M.purchase hui)) (trail_pos ..).le) (mul_nonneg (zero_le_one.trans (X.purchase hz)) hV)).trans_eq; unfold T'; rw [Credit.products,Credit.products]; unfold V' O; ring
       rw [←add_mul]; exact mul_le_mul_of_nonneg_right (Credit.fuel _ _ hz) hO
lemma rippleBill (G:Gauge)(k e u:ℕ)(E W:Credit): ∃ C:Credit,∀ i≤e,∀ j,Ripples G k e u i j E W C:=by
   apply seasonsPaid (fun i j C=> Ripples G k e u i j E W C) k e _ (fun i j v _=> overL v) (fun _ _ _ _ h q=>q.more h); intro i v r W h; by_cases hp:r≤k+i; exact coreRip v hp h; exact ⟨W,overL (by omega)⟩

theorem waveSeen (G:Gauge)(k e u:ℕ)(E W:Credit): ∃ C:Credit,∀ (R:Realm G (e+1) E),Dormitory R k u W →∀ m c η b N M A δ Z, Escort R m c η → PadRank R m c Z→ c≤b→ b≤N→ b≤M→ R.tempC c b≤ δ →∀ P Q:Era G ℝ,Fringed k e u (η c) A δ P Q→ Fringed k e u (η m) (C.buy Z*A) δ (cruises R.draws R.paid N k c m P) (cruises R.draws R.paid M k c m Q):=by
   obtain ⟨C,h⟩:= rippleBill G k e u E W; obtain ⟨V,f⟩:= bulkCert G k e u E W
   refine ⟨C.plus V,fun R t m c η b N M A δ Z u p q y w z X Y H=>⟨cruising R.draws R.hG R.green u.lane (q.trans y) H.inkV,cruising R.draws R.hG R.green u.lane (q.trans w) H.pen,H.crest,fun i r he=>?_⟩⟩
   have hp:=p.pos u; have hX:= mul_le_mul_of_nonneg_right (Credit.thickened (V:=V) C hp) H.nn
   exact ⟨(f i he r R t m c η N Z u p (q.trans y) X A H.inkV H.nn H.f_l.2).more hX,(f i he r R t m c η M Z u p (q.trans w) Y A H.pen H.nn H.f_r.2).more hX,(h i he r R t m c η b N M A δ Z u p q y w z X Y H).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.thickens V hp) H.nn) H.crest)⟩
end YM.WilsonCoeffUV.Mer
