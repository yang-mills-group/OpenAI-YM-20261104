import YM.WilsonCoeffUV.Product.Report.Capture
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Soft stop with marked price envelopes
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
variable {b b' v u m M N a:ℕ}{H:Hol G} {x δ Z y:ℝ} {E W V' W':Credit}{R:Realm G (e+1) E}
variable {c':ℕ}{Q:Fin (a+1)→SealR G}

noncomputable def spools (A:Levels G)(Ñ:ChartRatio G)(N k h m:ℕ) :ℕ→TowerS G D→ TowerS G D
  | 0,X=> X
  | i+1,X=> spools A Ñ N k h m i (Spout A Ñ N (m+i) h k X)
lemma spoolEnd (p:m+i≤N){A:Levels G}{Ñ:ChartRatio G}(g:G.Simple)(u:LocalRatio Ñ){X:TowerS G D}(v:On k X): On k (spools A Ñ N k h m i X):=by
   induction i generalizing X with
   | zero=> exact v
   | succ i ih=> exact ih (by omega) (ShedG A Ñ (by omega) g u v le_rfl)
lemma spool_sub (p:m+i≤N){A:Levels G}{Ñ:ChartRatio G}(g:G.Simple)(u:LocalRatio Ñ){X Y:TowerS G D}(v:On k X)(y:On k Y): spools A Ñ N k h m i (X-Y)=spools A Ñ N k h m i X-spools A Ñ N k h m i Y:=by
   induction i generalizing X Y with
   | zero=> rfl
   | succ i ih=> have hp:m+i<N:=by omega
                 simp only [spools]; rw [Shed_sub _ _ hp g u v y]; exact ih (by omega) (ShedG _ _ hp g u v le_rfl) (ShedG _ _ hp g u y le_rfl)
variable {F:Frame G h}{T:SectionData F}{p:h<D}
lemma spooled (L:Theatre H T p e E W)(X:Verse F)(t:L.V.anchor ≤ m)(v:h≤k)(g:m+i ≤ N): spools L.V.draws L.V.paid N k h m i (Shrine (L.lore N (m+i)) X)= Shrine (L.lore N m) (street L.V.draws L.V.paid T p N m i X):=by
    induction i generalizing X with
    | zero=> rw [street_nil]; rfl
    | succ i ih=>
       let Y:= L.lore N (m+i+1); have hh: m+i+1=m+(i+1):=by omega
       have he:Shimmer Y:= (production L (show m+i+1≤N by omega) (by omega)).1
       let A:=L.V.draws; let B:= spools (D:=D) A L.V.paid N k h m i; have hu:m+i<N:=by omega
       rw [←Street_steal]; change B (Spout A L.V.paid N (m+i) h k (Shrine Y X))=_; rw [emptied A L.V.paid L.V.hG L.V.green hu (leaseN L (t.trans (by omega)) hu) _ he v]; exact ih _ (by omega)
lemma Street_plus (A:Levels G)(Ñ:ChartRatio G)(N m i j:ℕ)(V:Verse F): street A Ñ T p N m i (street A Ñ T p N (m+i) j V)=street A Ñ T p N m (i+j) V:=by
    induction j generalizing V with
    | zero=> rw [street_nil]; rfl
    | succ j ih=> rw [←Street_steal,ih,show m+i+j=m+(i+j) by omega,Street_steal,Nat.add_succ]; rfl
lemma Street_refund (L:Theatre H T p e E W)(X:Verse F)(v:L.V.anchor ≤ m)(p':m+i+j≤ N):
    steep L.V.draws L.V.paid T p N m (i+j) (street L.V.draws L.V.paid T p N m i X) = steep L.V.draws L.V.paid T p N (m+i) j X := by
     apply street_up (i:=i+j) (N:=N) L v (by omega); rw [Street_up L _ v (by omega),← Street_plus, Street_up L _ (v.trans (by omega)) p']

lemma TallOracle {K:Credit} {w:Rails h k u e}(L:Torch H T p w E W K) (q:L.L.V.anchor≤m)(c:m+i≤N)(X:TowerS G D)(x: On k X):
   let A:= L.L.V.draws; let Ñ:=L.L.V.paid; opal F (spools A Ñ N k h m i X) = street A Ñ T p N m i (tallyV A Ñ T p N k (m+i) m X):=by
    intro A Ñ
    let B:= m+i; let R:= tallyV A Ñ T p N k B m X; let P:=L.L.lore N B; let V:= queries A Ñ T p N k B m; let Q:=Silt P X; have hp:= (production L.L c (by omega)).1; have ht:= sifted P hp x w.hk
    have he (j:ℕ)(t:j≤ i): spools A Ñ N k h m j (V j X)=V 0 X:=by
        induction j with
        | zero=> rfl
        | succ j ih=>
           rw [spools, show Spout A Ñ N (m+j) h k (V (j+1) X)=V j X from tired L q (Nat.add_le_add_left t m) c Q ht.1 ht.2]; exact ih (by omega)
    let K:= Shrine P R; have hK:On k K:= Shrine_on P hp R w.hk
    have hZ:= he i le_rfl
    have hU: opal F (V 0 X)=0:= by
       unfold V queries burden boot; simp only [Finset.range_zero,Finset.sum_empty,Shrine_zero,sub_zero]; exact (nursing L q (Nat.le_add_right ..) c ht.1 ht.2).2
    rw [show V i X=X-K from release L.L X rfl,spool_sub c L.L.V.hG L.L.V.green x hK] at hZ
    let Y:= L.L.lore N m
    have hf:= L.L.V.hG; have hd:=L.L.V.green
    rw [←hZ, On.read_sub F (spoolEnd c hf hd x) (spoolEnd c hf hd hK),show spools A Ñ N k h m i K=Shrine Y (street A Ñ T p N m i R) from spooled L.L R q w.hk c,Shrine_read _ _ (production L.L (by omega) q).1] at hU; exact sub_eq_zero.mp hU

def AutumnDay (A:Levels G)(Ñ:ChartRatio G)(F: Wilt Q)(X:Herit Q)(m b N:ℕ)(D:ℕ) : TowerS G D:= tuftV (HourFace dayMeasure D) (LodeStar A Ñ F X m b N (paceT A.S m b))
lemma GatesC (P:HorizonP H R W V' Q)(F:Wilt Q)(X:Herit Q)(q:R.anchor ≤ b)(v:b≤m)(g:m≤N)(t:capP Q≤ k): On k (AutumnDay R.draws R.paid F X m b N D):= by apply Auth_on; exact (Auth.tall ((cruising R.draws R.hG R.green (v.trans g) le_rfl (Hearth_enter P F X (q.trans (v.trans g)) le_rfl)).tuft _) t)
lemma importation (H:Hol G)(Q:Fin (a+1)→ SealR G)(E W V W' L:Credit)(e u D:ℕ): ∃ C:Credit,∀ (R:Realm G (e+1) E), HorizonP H R W V Q → SpringD R (capP Q) u (capP Q+2) W' → Dormitory R (capP Q) u L → ∀ m b c N M (F:Wilt Q)(X Y: Herit Q)(A B:Fin (a+1)→ℝ)(Z δ:ℝ), R.anchor ≤ b → b≤m → m≤ c→ c≤ N → c≤ M → PadRank R b m Z → Bough Q F (paceT R.draws.S m b) Z B → R.tempC m c≤ δ → Sitting Q A e δ X Y → ∀ i≤ e,∀ j:ℕ, let f n U:= AutumnDay R.draws R.paid F U m b n D; YieldP 0 1 u (C.buy Z* ∏ i,B i*A i) δ ((f N X).2 i j) ((f M Y).2 i j):=by
   obtain ⟨C,h⟩:= Captures H Q E W V W' L e u; refine ⟨C,fun R H' v t m b c N M F X Y A B Z δ hv hm hb hn hM hz hy hδ l i u' j=>?_⟩; intro f
   let η:= paceT R.draws.S m b; let I n U:= LodeStar R.draws R.paid F U m b n η; let T:=I N X; let Q':= I M Y; have hh (o):= (h R H' v t m c b N M F X Y A B Z η δ o hv hm hb hn hM hz hy hδ l).heapS i j u'
   refine ⟨MintD dayMeasure D (T.2 i j) (fun i=> (hh i).wax),MintD dayMeasure D (Q'.2 i j) (fun i=>(hh i).wane),?_⟩; have he : (f N X).2 i j -(f M Y).2 i j =fun b=> HourFace dayMeasure D ((T-Q').2 i j b):= funext fun b=> (map_sub (HourFace dayMeasure D) (T.2 i j b) (Q'.2 i j b)).symm; rw [he]; exact MintD dayMeasure D ((T-Q').2 i j) (fun i=> (hh i).toll)

-- finite Wilson formal report to soft stop

def Reports (A:Levels G)(Ñ:ChartRatio G)(T':SectionData F)(p:h<D)(Φ:Wilt Q)(X:Herit Q)(m b c N k:ℕ): Verse F:= (paceT A.S m b)^h • steep A Ñ T' p N c (m-c) (opal F (spools A Ñ N k h c (b-c) (AutumnDay A Ñ Φ X m b N D)))
lemma tall_report {U':Credit} {w: Rails h k u e}(L:Torch H T p w E W U') (P:HorizonP H L.L.V W V' Q)(X:Herit Q)(F':Wilt Q)(q:L.L.V.anchor≤ c')(t:c' ≤ b)(x:b ≤ m)(g:m≤N)(v:capP Q≤ k):
    let A:=L.L.V.draws; let Ñ:=L.L.V.paid; Reports A Ñ T p F' X m b c' N k= (paceT A.S m b)^h • steep A Ñ T p N b (m-b) (tallyV A Ñ T p N k b c' (AutumnDay A Ñ F' X m b N D)):=by
    intro A Ñ; have hp:= TallOracle (N:=N) (i:=b-c') L q (by omega) _ (GatesC (D:=D) P F' X (q.trans t) x g v); have hh:c'+(b-c')=b:=by omega
    dsimp only at hp; rw [hh] at hp; unfold Reports; rw [show opal _ (spools A Ñ N k h c' (b-c') (AutumnDay A Ñ F' X m b N D))=street A Ñ T p N c' (b-c') (tallyV A Ñ T p N k b c' (AutumnDay A Ñ F' X m b N D)) from hp, show m-c'= b-c'+(m-b) by omega, Street_refund L.L _ q (by omega),hh]
end YM.WilsonCoeffUV.Mer
