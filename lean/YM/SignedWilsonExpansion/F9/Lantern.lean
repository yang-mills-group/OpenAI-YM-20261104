import YM.SignedWilsonExpansion.F9.Jetty
/-!
# Conditional coverage is multilinear on ledger operations -- every comparison on margin/mask
   executed under new column names AND same power pull.
-/
set_option autoImplicit false
set_option maxHeartbeats 730000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r p u n :ℕ}
variable {B Q D Z X Y η t a:ℝ}{E W U:Credit} {x y: Cost}
section
variable (W:Finset J)(P:J→ Era G ℝ)
lemma cruises_gather (v:m≤ c)(p:G.Simple)(q:LocalRatio Ñ)(w:c≤N)(hP:∀ i∈W,Auth k (P i)):
    cruises A Ñ N k c m (∑ i∈ W,P i)=∑ i∈ W,cruises A Ñ N k c m (P i):=by
    induction v using Nat.decreasingInduction with
    | self=> simp_rw [cruises_top]
    | of_succ i b ih=> rw [cruises_sub A Ñ N k (∑ i∈W,P i) b,ih]; refine (Eq.trans (show _=∑ j∈ W,verseI A Ñ i N k (cruises A Ñ N k c (i+1) (P j)) from ?_) (Finset.sum_congr rfl fun j _=> (cruises_sub _ _ _ _ (P j) b).symm)); simpa only [one_smul] using verse_sum A p (b.trans_le w) q (S:=W) (fun i h=> cruising A p q b w (hP i h)) (fun i=>1)
lemma shifted_gather (o:Cover): shifted (∑ i∈ W,P i) o=∑ i∈ W, shifted (P i) o:=by
    unfold shifted; refine Prod.ext (funext fun n=>funext fun i=>funext fun r=>funext fun x=> ?_) (funext fun i=>funext fun r=>funext fun x=>?_);
    all_goals simp only [Prod.fst_sum,Prod.snd_sum,skewV,revolve,Finset.sum_apply]
end
lemma shift_order (x:Cost)(P:Era G ℝ)(o:Cover) : trim x (shifted P o)= shifted (trim x P) o:=by
    unfold trim shifted; refine Prod.ext (funext fun n=>funext fun i=>funext fun r=>funext fun x=>?_) (funext fun i=>funext fun r=>funext fun x=>?_); all_goals simp only [affix,revolve,skewV,Finset.sum_apply,Pi.smul_apply]
lemma trim_lib (c:ℝ)(x:Cost)(P:Era G ℝ) : trim (c • x) P= c • trim x P:=by
    have h(U:Type)(P: Pal ℝ U) : affix (c • x) P=c • affix x P:= by funext i; rw [Pi.smul_apply]; simp_rw [affix,Finset.smul_sum,map_smul, smul_assoc]
    exact Prod.ext (funext fun n=>h _ _) (h _ _)
lemma trim_lot (S:Finset J)(f:J→ Cost)(P:Era G ℝ): trim (∑ i∈ S,f i) P= ∑ i∈ S,trim (f i) P:= by unfold trim; refine Prod.ext (funext fun n=> ?_) (?_); all_goals simp only [Prod.fst_sum, Prod.snd_sum,Finset.sum_apply,addend]

variable {P R L T':Era G ℝ}{K:ℝ}
lemma flash_recover (v:Auth k P)(h:Auth i R)(q:∀ n, flash (P.1 n)=flash (R.1 n)): P=R:=Auth.ext v h (funext fun n=> by_flash (v.span n) (h.span n) (v.pale _) (h.pale _) (q n))
lemma flashAgate (v:Auth k P)(h:Auth i R)(n:Side): flash ((agateV P R).1 n) = flash (P.1 n)*flash (R.1 n):= woadap _ _ (finite_shell (v.span n)) (finite_shell (h.span n))
lemma agate_swap (v:Auth k P)(h:Auth i R): agateV P R=agateV R P:= flash_recover (v.manor h) (h.manor v) (fun n=>by rw [flashAgate v h,flashAgate h v,mul_comm])
lemma agate_add (v:Auth k P)(p:Auth i R)(h:Auth i T') : agateV P (R+T')=agateV P R+agateV P T':=by
    apply eq_add_of_sub_eq; rw [←pairingP,add_sub_cancel_right]
lemma agate_sum (S:Finset J)(Q:J→Era G ℝ)(v:Auth k P)(p:∀ i∈ S, Auth l (Q i)) : agateV P (∑ i∈ S,Q i)=∑ i∈S, agateV P (Q i):=by
    induction S using Finset.induction_on with
    | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact Prod.ext (funext fun _=>(woadNull _).1) (woadNull _).1
    | @insert i S g ih=> let w:=fun i (h:i∈S)=> p i (Finset.mem_insert_of_mem h); rw [Finset.sum_insert g,Finset.sum_insert g, agate_add v (p i (Finset.mem_insert_self ..)) (Auth.sum w), ih w]
lemma agate_meters (v:Auth k P)(p:Auth i R)(x y:Cost): agateV (trim x P) (trim y R)=trim (x*y) (agateV P R):=by
    apply flash_recover ((trim_auth x v).manor (trim_auth y p)) (trim_auth _ (v.manor p)); intro n; let X:= P.1 n; let Y:=R.1 n; rw [flashAgate (trim_auth x v) (trim_auth y p) n]; change flash (affix x X)*flash (affix y Y)=flash (affix (x*y) (woad X Y)); rw [sponsor X _ (v.span _), sponsor Y _ (p.span _),sponsor (woad X Y) (x*y) (show shellK (k+i) (woad X Y) from ((v.manor p).span _)),map_mul,show flash (woad X Y)= _ from flashAgate v p n]; unfold X Y; ring
lemma MassP_auth (P:Fin (n+1)→Era G ℝ)(q:∀ i, Auth k (P i)):Auth ((n+1)*k) (MassP G ℝ n P):=by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,Nat.cast_id] using manCo P (fun _=>k) q
lemma agate_left (S:Finset J)(P:J→Era G ℝ)(p:∀ i∈ S,Auth k (P i))(v:Auth l L): agateV (∑ i∈S,P i) L=∑ i∈S,agateV (P i) L:=by rw [agate_swap (Auth.sum p) v,agate_sum S P v p]; exact Finset.sum_congr rfl (fun i hi=> agate_swap v (p i hi))
section slate
variable [Fintype J]
variable (Yp:Fin (n+1)→J→ Era G ℝ)
-- sequence splitting for parent counts
def splitList (n): (Fin (n+1)→ J) ≃ J× (Fin n→ J) where
  toFun x:=(x 0, Fin.tail x)
  invFun x:=Fin.cons x.1 x.2
  left_inv x:=funext fun i=> Fin.cases (by simp) (fun i=>by simp [Fin.tail]) i
  right_inv x:= by simp
lemma fullList {A:Type*}[AddCommMonoid A] (f: (Fin (n+1)→ J)→ A): (∑ x,f x)=∑ i:J,∑ p:Fin n→J, f (Fin.cons i p):=by
    rw [← Equiv.sum_comp (splitList (J:=J) n).symm f, Fintype.sum_prod_type]; rfl
lemma massHeaders (q:∀ i j,Auth k (Yp i j)): MassP G ℝ n (fun j=> ∑ i,Yp j i)=∑ f: Fin (n+1) → J, MassP G ℝ n (fun i=> Yp i (f i)):=by
    induction n with
    | zero=> rw [fullList]; simp only [MassP, Fintype.sum_unique,Fin.cons_zero]
    | succ n ih=>
       let f:=Fin.tail Yp; let S(p:Fin (n+1)→ J):=MassP G ℝ n fun i=>f i (p i); let Y(x:Fin (n+1+1) → J):= MassP G ℝ (n+1) (fun i=> Yp i (x i)); change agateV (∑ i:J,Yp 0 i) (MassP G ℝ n (fun i=>∑ j:J,f i j))=∑ i,Y i; rw [ih f (fun i j=>q i.succ j)]; change agateV (∑ i:J,Yp 0 i) (∑ p:Fin (n+1)→ J,S p)=_
       have hh p:Auth ((n+1)*k) (S p):= MassP_auth _ fun i=> q i.succ (p i)
       rw [agate_left Finset.univ _ (fun i h=>q 0 i) (Auth.sum (fun i (_:i∈Finset.univ)=>hh i)), fullList Y]; apply Finset.sum_congr rfl; intro x _; rw [agate_sum _ S (q 0 x) (fun i _=>hh i)]; apply Finset.sum_congr rfl; intro i _; unfold Y; rw [MassP,Fin.cons_zero]; congr -- fix
omit [Fintype J] in
lemma massClocks (y: Fin (n+1)→Cost)(Yp:Fin (n+1)→Era G ℝ)(q:∀ i,Auth k (Yp i)): MassP G ℝ n (fun i=>trim (y i) (Yp i))=trim (∏ i,y i) (MassP G ℝ n Yp):=by
   induction n with
   | zero=> rw [Fin.prod_univ_succ,Fintype.prod_empty,mul_one]; rfl
   | succ n ih=> rw [Fin.prod_univ_succ, MassP, show (Fin.tail fun i=>trim (y i) (Yp i))=(fun i=>trim (Fin.tail y i) (Fin.tail Yp i)) from rfl, ih (Fin.tail y) (Fin.tail Yp) (fun i=> q i.succ), MassP]; exact agate_meters (q 0) (MassP_auth _ (fun i=> q i.succ)) _ _ -- annotated
lemma scaling_H (K:Fin (n+1)→Cover)(y:Fin (n+1)→J→Cost)(p:∀ i j,Auth k (Yp i j)): embark (fun i=>∑ j:J,trim (y i j) (Yp i j)) K= ∑ f: Fin (n+1) → J,trim (∏ i,y i (f i)) (embark (fun i=>Yp i (f i)) K):=by
   unfold embark; simp_rw [shifted_gather,← shift_order]; rw [massHeaders (fun i j=> trim (y i j) (shifted (Yp i j) (K i))) (fun i j=> trim_auth _ ((p i j).shifted _))]; exact Finset.sum_congr rfl (fun i _=> massClocks _ _ (fun j=>(p j (i j)).shifted (K j))) -- check implicit J
-- covers linear claim under EACH clock independent of root.W
lemma seasonH (K:Fin (n+1)→Cover)(y:Fin (n+1)→J→ Cost)(g:G.Simple)(q:LocalRatio Ñ)(u:m ≤ c)(v:c≤N) (p:∀ i j,Auth k (Yp i j)):
     FadeRaw A Ñ N ((n+1)*k) m c (embark (fun i=>∑ j:J,trim (y i j) (Yp i j)) K)= ∑ f: Fin (n+1) → J, (∏ i, toward A Ñ N m c (y i (f i))) * FadeRaw A Ñ N ((n+1)*k) m c (embark (fun i=>Yp i (f i)) K):=by
   let F(x:Fin (n+1)→J):= embark (fun i=>Yp i (x i)) K; let b(x:Fin (n+1)→ J):=(∏ i,y i (x i)); have hv f:Auth ((n+1)*k) (F f):= MassP_auth _ (fun j=>(p j _).shifted _)
   unfold FadeRaw; rw [scaling_H Yp K y p, cruises_gather (W:=Finset.univ) (P:=fun f=>trim (b f) (F f)) u g q v (fun f _=> trim_auth (b f) (hv f)), dew_sum]; apply Finset.sum_congr rfl; intro f _; rw [calendarX (P:=F f) g q u v (b f) (hv f),dew_flat,←map_prod (toward A Ñ N m c)]
end slate
end YM.WilsonCoeffUV.Mer.Xa
