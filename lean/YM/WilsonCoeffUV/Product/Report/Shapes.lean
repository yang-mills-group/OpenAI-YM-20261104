import YM.WilsonCoeffUV.Product.Report.Geometry
/-!
# Reader shapes and Λ-anchors
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b m M N:ℕ}{H:Hol G}{F:Frame G h}{T:SectionData F}{E W Q:Credit}{p:h<D}
def paceT (S:Schedule)(m i:ℕ):ℝ:= S.a i/S.a m
lemma pace_pos (S:Schedule)(m i:ℕ): 0< paceT S m i:= div_pos (S.a_pos _) (S.a_pos _)
lemma pace_step (S:Schedule)(m i:ℕ): paceT S m (i+1)*(S.block i).val=paceT S m i:=by rw [paceT, S.a_step,paceT]; field_simp
lemma pace_self (S:Schedule)(m:ℕ): paceT S m m=1:=div_self (S.a_pos _).ne'
lemma pace_le (S:Schedule)(p:m≤ i): paceT S m i≤1:= (div_le_one (S.a_pos _)).mpr (S.strictAnti.antitone p)
lemma pace_ge (S:Schedule)(v:i≤m): 1≤ paceT S m i:= (one_le_div (S.a_pos _)).mpr (S.strictAnti.antitone v)
lemma pace_rep (S:Schedule)(m i:ℕ): paceT S m i= Real.exp (-(S.scale i-S.scale m)):= by simp [paceT,Schedule.scale,Real.exp_log (S.a_pos i),Real.exp_neg,Real.exp_add,div_eq_mul_inv,mul_comm,Real.exp_log (S.a_pos m)]

def FirstCharge (A : Levels G) (Ñ: ChartRatio G)(T:SectionData F)(p:h<D)(φ:Rarity D)(m i N:ℕ)(y:ℝ)(X:Verse F) : Era G Lounge:= pupil h (polarP A Ñ T p N m i X) φ (paceT A.S m i) y
lemma tokenPaid (L:Theatre H T p e E W)(φ:Rarity D)(X:Verse F)(y:ℝ)(v:L.V.anchor≤ i)(t:i≤N): Auth h (FirstCharge L.V.draws L.V.paid T p φ m i N y X):=placed _ _ (tournure L X v t) _ _
lemma priceReset (L:Theatre H T p e E W)(φ:Rarity D)(X:Verse F)(y:ℝ)(v:L.V.anchor≤ m)(t:m≤ i)(q:i<N):
     let S:=L.V.draws; let Ñ:= L.V.paid; verseI S Ñ i N h (FirstCharge S Ñ T p φ m (i+1) N y X)= FirstCharge S Ñ T p φ m i N y X:=by
    intro S Ñ
    unfold FirstCharge; rw [journey _ _ S L.V.hG L.V.green (tournure L X (by omega) q) _ (pace_pos ..) q,summerUp L X v t q,pace_step]

section
variable [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
lemma cruisePlus {X Y:Era G V}(A:Levels G){Ñ:ChartRatio G}(v:b≤ m)(g:G.Simple)(t:LocalRatio Ñ)(q:m≤ N)(p:Auth k X)(x:Auth k Y): cruises A Ñ N k m b (X-Y)=cruises A Ñ N k m b X-cruises A Ñ N k m b Y:=by
    induction v using Nat.decreasingInduction with
    | self=> rw [cruises_top,cruises_top,cruises_top]
    | of_succ b v ih=> rw [cruises_sub _ _ _ _ _ v,cruises_sub _ _ _ _ X v,cruises_sub _ _ _ _ Y v,ih]; exact verse_lin A g (v.trans_le q) t (cruising A g t v q p) (cruising A g t v q x)
lemma cruiseT [NormedAddCommGroup U][NormedSpace ℝ U][CompleteSpace U](T: V→L[ℝ]U){X:Era G V}(A:Levels G){Ñ:ChartRatio G}(v:b≤ m)(g:G.Simple)(t:LocalRatio Ñ)(q:m≤ N)(p:Auth k X):
    tuftV T (cruises A Ñ N k m b X)=cruises A Ñ N k m b (tuftV T X):= by
    induction v using Nat.decreasingInduction with
    | self=> rw [cruises_top,cruises_top]
    | of_succ b v ih=> rw [cruises_sub _ _ _ _ X v,cruises_sub _ _ _ _ _ v, ply_verse A (v.trans_le q) g t (cruising A g t v q p),ih]
omit [CompleteSpace V] in
lemma cruisesMore (A:Levels G)(Ñ:ChartRatio G)(P:Era G V)(v:m≤ b)(t:b≤ i) : cruises A Ñ N k i m P= cruises A Ñ N k b m (cruises A Ñ N k i b P):=by
    induction v using Nat.decreasingInduction with
    | self=> rw [cruises_top A Ñ N k b (cruises ..)]
    | of_succ d h ih=> rw [cruises_sub _ _ _ _ _ (h.trans_le t), cruises_sub _ _ _ _ (cruises _ _ _ _ _ _ P) h, ih]
omit [CompleteSpace V] in
lemma cruiseStep (A:Levels G)(Ñ:ChartRatio G)(P:Era G V)(v:m≤ i): cruises A Ñ N k i m (verseI A Ñ i N k P) = cruises A Ñ N k (i+1) m P:=by rw [cruisesMore A Ñ P v (show i≤ i+1 by omega),cruises_sub _ _ _ _ P (show i< i+1 by omega),cruises_top]
end
lemma woadChart (i:CellR)(X Y:Era G Lounge):locale i (agateV X Y)=agateV (locale i X) (locale i Y):=by
   have hp : (century i).toLinearMap= (nestC i).toLinearMap:= rfl; exact Prod.ext (funext fun _n=>woad_ply _ _ (nestC i)) (woad_ply _ _ (nestC i))
lemma agateHome {X Y:Era G Lounge}(p:Auth i X)(q:Auth j Y):Auth (i+j) (agateV X Y):= Auth.woadB p q nestC (fun _ _ h=> ContinuousMap.ext h)
lemma PortalLong (n:ℕ)(X:Fin (n+1)→ Era G Lounge)(U:Fin (n+1)→ℕ)(p:∀ i,Auth (U i) (X i)):Auth (∑ i,U i) (MassP G Lounge n X):=by
   induction n with
   | zero=> rw [Fin.sum_univ_succ,Fintype.sum_empty,add_zero]; exact p 0
   | succ n ih=> rw [Fin.sum_univ_succ, MassP]; exact agateHome (p 0) (ih (Fin.tail X) (Fin.tail U) (fun i=> p i.succ))
lemma PortalHome (n:ℕ)(X:Fin (n+1)→ Era G Lounge)(i:CellR) : locale i (MassP G Lounge n X)=MassP G ℝ n (fun b=>locale i (X b)):=by
    induction n with
    | zero=> rfl
    | succ n ih=> rw [MassP, woadChart, ih]; rfl
lemma woadNull (P:Pal ℝ U): woad P 0=0∧woad 0 P=0:=by
   constructor <;> (funext i j; unfold woad; rw [Finset.sum_apply]; apply Finset.sum_eq_zero; intro x _; unfold knitS; rw [Finset.sum_eq_zero]; · exact swirl_exact Blue.Smooth.zero); all_goals intro _ _; ext1 i; simp [webT]
lemma GapZero {n':ℕ}(P:Fin (n'+1) → Era G ℝ)(v:Fin (n'+1))(t:P v=0): MassP G ℝ n' P=0:=by
   induction n' with
   | zero=> rw [Fin.eq_zero v] at t; exact t
   | succ n ih=>
     revert t; refine Fin.cases (fun t=>?_) (fun i t=>?_) v
     · rw [MassP,t]; exact Prod.ext (funext fun _ => (woadNull _).2) (woadNull _).2
     rw [MassP,ih (Fin.tail P) i t]; exact Prod.ext (funext fun _ => (woadNull _).1) (woadNull _).1
lemma verseZero (A:Levels G){Ñ:ChartRatio G} (p:m<N)(v:G.Simple)(h:LocalRatio Ñ): verseI A Ñ m N k (0:Era G ℝ)=0:=by simpa using verse_sum A (Ñ:=Ñ) (P:=fun _:Unit=>0) (k:=k) v p h (S:=∅) (by simp) (fun _=>1)
lemma deltaZero {n':ℕ}(P: Fin (n'+1)→ Era G ℝ)(u:Fin (n'+1))(t:P u=0)(A:Levels G){Ñ:ChartRatio G}(q:LocalRatio Ñ)(v:m<N)(g:G.Simple)(V: Fin (n'+1)→ℕ): DeltaGap A Ñ m N P V=0:=by
   unfold DeltaGap startK; rw [GapZero P u t,verseZero A v g q, GapZero _ u (by rw [t,verseZero A v g q]),sub_self]
end YM.WilsonCoeffUV.Mer
