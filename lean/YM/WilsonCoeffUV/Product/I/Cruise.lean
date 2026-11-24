import YM.WilsonCoeffUV.Product.I.Price
/-!
# Cruising shelf bill uniformity
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
section
variable [NormedAddCommGroup V][NormedSpace ℝ V]
noncomputable def cruises (A:Levels G)(Ñ:ChartRatio G)(N k c m:ℕ)(P: Era G V): Era G V:= if h:m<c then verseI A Ñ m N k (cruises A Ñ N k c (m+1) P) else P
termination_by c-m
lemma cruises_sub {c:ℕ}(A:Levels G)(Ñ:ChartRatio G)(N k:ℕ) (P:Era G V)(p:m<c) : cruises A Ñ N k c m P=verseI A Ñ m N k (cruises A Ñ N k c (m+1) P):=by rw [cruises,dif_pos p]
lemma cruises_top (A:Levels G)(Ñ:ChartRatio G)(N k c:ℕ)(P:Era G V): cruises A Ñ N k c c P=P:=by rw [cruises,dif_neg (lt_irrefl c)]
lemma cruising [CompleteSpace V] (A:Levels G){Ñ:ChartRatio G}{P:Era G V}{c m:ℕ}(g:G.Simple)(p:LocalRatio Ñ)(q:m≤ c)(h:c≤ N)(z:Auth k P): Auth k (cruises A Ñ N k c m P):=by
    induction q using Nat.decreasingInduction with
    | self=> rw [cruises_top]; exact z
    | of_succ i he ih=> rw [cruises_sub _ _ _ _ _ he]; exact Auth.verse A (he.trans_le h) g p ih
end
open Ore
variable {E W V' U' C:Credit}{u e k j c b:ℕ}{x t δ:ℝ}
structure Escort {e:ℕ}{E:Credit}(R:Realm G e E)(m c:ℕ)(η:ℕ→ℝ): Prop where
   ham : R.anchor≤m
   lane:m≤c
   he i:m ≤ i → i≤ c → 0≤η i
   hp i:m ≤ i → i≤ c →η i≤1
   stern i:m ≤ i → i<c → thinLevel R.draws i (η i) ≤ η (i+1)
variable {R:Realm G e E}{η:ℕ→ℝ}
lemma Escort.clip (q:Escort R m c η)(p:m≤ i)(u:i≤j)(w:j≤ c): Escort R i j η:=⟨q.ham.trans p,u,fun k v e=>q.he k (p.trans v) (e.trans w),fun k v e=> q.hp k (p.trans v) (e.trans w),fun k v e=> q.stern k (p.trans v) (e.trans_le w)⟩
lemma Escort.frost (q:Escort R m c η)(v:m ≤ i)(p:i<c): 0 ≤ thinLevel R.draws i (η i):= div_nonneg (q.he i v p.le) (by positivity)
abbrev Saturation (e r u:ℕ)(P:Bookend ℝ G)(η A:ℝ):Prop:=∀ i≤e,∀ j≥r,Fruit 0 η u (P i j) A
abbrev BeamCost (G:Gauge)(k e u i r:ℕ) (E W C:Credit): Prop:=∀ (R:Realm G (e+1) E), Dormitory R k u W →∀ m c η, Escort R m c η→∀ N,PureM R N c k m i r u e C η
where PureM (R:Realm G (e+1) E)(N c k m i r u e':ℕ)(C:Credit)(η:ℕ→ℝ): Prop:= ∀ P:Era G ℝ,∀ A:ℝ,Auth k P→ c≤ N→ 0≤A→Saturation e' 1 u P.2 (η c) A →0<r→ Fruit 0 (η m) u ((cruises R.draws R.paid N k c m P).2 i r) (R.cash C m* R.tempC m c*A)
lemma BeamCost.more (q:BeamCost G k e u i r E W V')(p:∀ y:ℝ,1≤y → V'.buy y≤ U'.buy y): BeamCost G k e u i r E W U':=by
    intro R h m c η f N P A hv hp ht he hu; exact (q R h m c η f N P A hv hp ht he hu).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (p _ (R.depth _ f.ham)) (trail_pos ..).le) ht)
lemma beamMega (q:k+i<r): BeamCost G k e u i r E W V':=by
    intro R h m c η f N P A hp p he hv u; rw [(cruising R.draws R.hG R.green f.lane p hp).coverN i r q]; refine Fruit.zero.more (mul_nonneg (mul_nonneg (zero_le_one.trans (V'.purchase (R.depth _ f.ham))) (trail_pos ..).le) he)
lemma beamStep (t:i≤e)(p:r≤k+i)(h:∀ i' j,lowerGrade i' j i r→ BeamCost G k e u i' j E W V'): ∃ C:Credit,BeamCost G k e u i r E W C:=by
    let T:= ticketL G e k i r u E W; let U:= jumped E V'; let C:= T.prodC U
    refine ⟨C.behind,fun R hR m c η f N P A hv hp ht he hu=>?_⟩; let F i:=cruises R.draws R.paid N k c i P; have hx:=R.depth m f.ham
    suffices H:∀ b≤c,m≤b→ Fruit 0 (η b) u ((F b).2 i r) (C.tower Credit.liftA (R.y b)*R.tempC b c*A) by exact (H m f.lane le_rfl).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.donation C _ _ _ hx) (trail_pos ..).le) ht)
    intro b Hb; induction Hb using Nat.decreasingInduction with
    | self=> intro a; unfold F; rw [cruises_top]; exact (he i t r hu).more (purchase_border C R (f.ham.trans a) ht)
    | of_succ b z ih=>
        intro a; have ha:=f.ham.trans a; let q:= thinLevel R.draws b (η b); have heq:0≤q:= f.frost a z
        have hb:m≤b+1:=a.trans (by omega); let X:= F (b+1); let Y:=axeR X; let Z:= R.cash U b*R.tempC b c*A; have hy:= f.he b a z.le; have hY:= cruising R.draws R.hG R.green z hp hv
        have hQ:0≤Z:=by unfold Z; exact mul_nonneg (mul_nonneg (zero_le_one.trans (U.purchase (R.depth _ ha))) (trail_pos ..).le) ht
        have hf j l (v:0<l): Y.2 j l= X.2 j l:=by simp only [Y,axeR,lop,if_neg (show l≠0 by omega)]
        have hm j l (v:lowerGrade j l i r): Fruit 0 q u (Y.2 j l) Z:=by
           cases l with
           | zero=> rw [show Y.2 j 0=0 by simp only [Y,axeR,lop,↓reduceIte]]; exact Fruit.zero.more hQ
           | succ l=>
             rw [hf _ _ (by omega)]; exact ((h _ _ v R hR (b+1) c η (f.clip hb z le_rfl) N P A hv hp ht he (by omega)).shave heq (f.stern b a z)).more (mul_le_mul_of_nonneg_right (lift_money R ha V' c) ht)
        let B:=C.tower Credit.liftA (R.y (b+1))*R.tempC (b+1) c*A; have hz: Fruit 0 q u (Y.2 i r) B:=by rw [hf i r hu]; exact (ih hb).shave heq (f.stern b a z)
        unfold F; rw [cruises_sub _ _ _ _ _ z, zinc_eye R.draws (z.trans_le hp) hY R.hG R.green hu]; apply (amen R hR ha (z.trans_le hp) t (by omega) Y hY.axe hy (f.hp b a z.le) hz hQ hm).more; rw [lowRep,if_neg (by omega)]; refine le_trans (le_of_eq (show _+_= _ from congr_arg (fun y=>Real.exp (-PathCost.arc R.draws.S b /2)*B+y) (show R.cash T b* Z= R.cash C b*R.tempC b c*A by unfold C cash Z; rw [Credit.products]; unfold cash; ring
         ))) (aging C R ha c A ht)
theorem beamGo (G:Gauge)(k e u:ℕ)(E W:Credit) : ∃ C:Credit,∀ i≤e,∀ r, BeamCost G k e u i r E W C:=by
   refine seasonsPaid (fun i j C=> BeamCost G k e u i j E W C) k e ?_ (fun i j v _=> beamMega v) (fun _ _ _ _ h q=>q.more h)
   intro i v r W h; by_cases hp:r≤k+i; exact beamStep v hp h; exact ⟨W,beamMega (by omega)⟩
end YM.WilsonCoeffUV.Mer
