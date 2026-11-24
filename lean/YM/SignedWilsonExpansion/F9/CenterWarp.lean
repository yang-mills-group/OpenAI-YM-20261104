import YM.SignedWilsonExpansion.F9.Spiro
/-! # All operands travel to the inversion center, after evaluating the F9 corners -/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r p u n :ℕ}
variable {P Q:Era G ℝ}
structure Center (A:Levels G)(m c:ℕ)(x:ℕ→ Cover): Prop where
    era (i:ℕ): m ≤ i → i<c → x (i+1)= (A.S.block i).val • x i
variable {x:ℕ→Cover}
lemma Center.trimH (f:Center A m c x)(p:m≤v)(q:b≤ c): Center A v b x:=⟨fun _ u t=> f.era _ (p.trans u) (t.trans_le q)⟩
lemma moveT (x y:Cover)(P:Era G ℝ): shifted P (x+y)=shifted (shifted P y) x:=by
    refine Prod.ext (funext fun n=>funext fun i=>funext fun j=> ?_) (funext fun i=>funext fun j=>?_)
    · change revolve (wrap n (x+y)) _= _; rw [map_add]; exact rollCup ..
    exact rollCup ..
lemma moveM (x:Cover)(p:Auth k P)(q:Auth i Q): agateV (shifted P x) (shifted Q x)=shifted (agateV P Q) x:=by
    apply flash_recover ((p.shifted x).manor (q.shifted x)) ((p.manor q).shifted x); intro n; rw [flashAgate (p.shifted x) (q.shifted x)]; have hz {P:Era G ℝ}{e}(p:Auth e P):flash ((shifted P x).1 n)=Blue.loom (spear (jog (wrap n x))) (flash (P.1 n)):= translate_value n _ _ (p.span _)
    rw [hz p,hz q,hz (p.manor q),flashAgate p q,map_mul]
lemma move_sumP (P:Fin (n+1)→Era G ℝ)(p:∀ i,Auth k (P i))(d:Cover): shifted (MassP G ℝ n P) d=MassP G ℝ n (fun i=>shifted (P i) d):=by
    induction n with
    | zero=> rfl
    | succ n ih=> rw [MassP,MassP,← moveM d (p 0) (MassP_auth (Fin.tail P) (fun i=> p i.succ)), ih (Fin.tail P) (fun i=> p i.succ)]; rfl
lemma Center.cruise (f:Center A m c x)(u:m ≤ c)(p:G.Simple)(q:LocalRatio Ñ)(b:c≤N)(hp:Auth k P) :
    cruises A Ñ N k c m (shifted P (x c))=shifted (cruises A Ñ N k c m P) (x m):=by
    induction u using Nat.decreasingInduction with
    | self=> rw [cruises_top,cruises_top]
    | of_succ i t ih=> rw [cruises_sub _ _ _ _ (shifted ..) t,cruises_sub _ _ _ _ P t,ih (f.trimH (Nat.le_succ i) le_rfl), f.era i le_rfl t,outing A (t.trans_le b) p q (cruising A p q t b hp)]
lemma immovable (P: Era G ℝ)(x:Cover): dew (shifted P x)=dew P:=by ext1 i; rw [dew_coeff,dew_coeff]; change P.2 i 0 _=P.2 i 0 _; exact congr_arg (P.2 i 0) (Subsingleton.elim ..)
lemma Center.still (f:Center A m c x)(u:m≤c)(p:G.Simple)(q:LocalRatio Ñ)(b:c≤N)(w:Fin (n+1)→Cover)(P:Fin (n+1)→Era G ℝ)(hP:∀ i,Auth k (P i)):
     FadeRaw A Ñ N ((n+1)*k) m c (embark P (fun i=> x c+w i))=FadeRaw A Ñ N ((n+1)*k) m c (embark P w):=by
    unfold FadeRaw embark; simp_rw [moveT]; rw [← move_sumP _ (fun i=>(hP i).shifted (w i)), f.cruise u p q b (MassP_auth _ (fun i=>(hP i).shifted (w i))), immovable]
end YM.WilsonCoeffUV.Mer.Xa
