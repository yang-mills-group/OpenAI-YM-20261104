import YM.WilsonCoeffUV.Product.Connected.Charges
/-!
# First-join polynomial UV gains from separation
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{U V α β ι:Type*}{r h D j m e i i' j' l k u a:ℕ}{A B C s:ℝ}{G:Gauge}
variable {p q:ProfileW}{D' t η K M s S δ:ℝ}
variable {b:ℕ}
lemma SplitHill.union (x:SplitHill p q η K D') {z}(y:SplitHill p z η K D'): SplitHill p (q⊓z) η K D':=by
   refine ⟨x.lipP,?_,x.globe,x.toll,x.nonneg,x.year,x.edge,?_,?_⟩
   · intro i j; change min (q i) (z i) ≤ min (q j) (z j)+Bank.terrain.gap j i; rw [← min_add_add_right]; exact le_min ((min_le_left ..).trans (x.lipQ ..)) ((min_le_right ..).trans (y.lipQ ..))
   · intro i; change _ ≤ K+↑(min (q i) (z i)); rw [Nat.cast_min,add_min]; exact le_min (x.rate _) (y.rate _)
   intro a b; change _ ≤ _+(↑(min (q b) (z b)):ℝ); rw [Nat.cast_min,add_min]; exact le_min (x.gap ..) (y.gap ..)

section
variable {V:Type*}[NormedRing V][NormedAlgebra ℝ V]
noncomputable def MassP (G:Gauge)(V:Type*)[NormedRing V][NormedAlgebra ℝ V]: (n:ℕ) → (Fin (n+1)→ Era G V)→Era G V
 | 0,X=> X 0
 | n+1,X=> agateV (X 0) (MassP _ _ n (Fin.tail X))
lemma manCo {n:ℕ}(P: Fin (n+1)→ Era G ℝ)(T:Fin (n+1)→ ℕ)(p:∀ i,Auth (T i) (P i)):Auth (∑ i,T i) (MassP G ℝ n P):=by
    induction n with
    | zero=> rw [Fin.sum_univ_succ,Fintype.sum_empty,add_zero]; exact p 0
    | succ n ih=>rw [Fin.sum_univ_succ]; exact (p 0).manor (ih (Fin.tail P) (Fin.tail T) (fun i=>p i.succ))
end

noncomputable def nuP (x:ℝ): (n:ℕ)→ (Fin (n+1)→ℝ) → ℝ
 | 0,p=> p 0
 | n+1,p=> x*p 0*nuP x n (Fin.tail p)
lemma loadRep (x:ℝ)(n:ℕ)(P:Fin (n+1)→ℝ): nuP x n P=x^n * ∏ i,P i:=by
   induction n with
   | zero=> rw [Fin.prod_univ_succ,Fintype.prod_empty,mul_one,pow_zero,one_mul]; rfl
   | succ n ih=> rw [Fin.prod_univ_succ,nuP,ih]; unfold Fin.tail; ring
lemma loadN (x:ℝ)(n:ℕ)(P:Fin (n+1)→ℝ)(p:0≤ x)(q:∀ i,0≤P i):0≤nuP x n P:=by rw [loadRep]; exact mul_nonneg (pow_nonneg p _) (Finset.prod_nonneg fun i _=>q i)
lemma pedig (n:ℕ)(T:Fin (n+1)→ Era G ℝ)(V:Fin (n+1)→ Era G ℝ)(h:Fin (n+1)→ ℕ)(X:Fin (n+1)→ℝ)(p':ProfileW)(t:∑ i,h i≤k)(g:∀ i,Auth (h i) (T i))(q:∀ i,Auth (h i) (V i))(x:∀ i,PaidMer e u p' (T i) (V i) (X i) δ)(hv:0≤δ): PaidMer e u p' (MassP G ℝ n T) (MassP G ℝ n V) (nuP (coinMat k e) n X) δ:=by
   induction n with
   | zero=> exact x 0
   | succ n ih=>
      have hp:= manCo (Fin.tail T) _ (fun i=>g i.succ); have hh:=manCo (Fin.tail V) _ (fun i=>q i.succ)
      rw [Fin.sum_univ_succ] at t; exact procureT (g 0) (q 0) hp hh (x 0) (ih _ _ (Fin.tail h) (Fin.tail X) (by simpa only [Fin.tail] using (show (∑ i:Fin (n+1),h i.succ)≤ k from by omega)) (fun i=>g i.succ) (fun i=>q i.succ) (fun i=>x i.succ)) hv t
lemma valueP (n:ℕ)(T V:Fin (n+1)→ Era G ℝ)(h:Fin (n+1)→ℕ)(X: Fin (n+1)→ℝ)(t:∑ i,h i≤k)(p:∀ i,Fringed (h i) e u η (X i) δ (T i) (V i))(hv:0≤η): Fringed (∑ i,h i) e u η (nuP (coinMat k e) n X) δ (MassP G ℝ n T) (MassP G ℝ n V):=by
   induction n with
   | zero=> rw [Fin.sum_univ_succ,Fintype.sum_empty,add_zero]; exact p 0
   | succ n ih=> rw [Fin.sum_univ_succ] at t ⊢; exact fringedMat (p 0) (ih (Fin.tail T) (Fin.tail V) (Fin.tail h) (Fin.tail X) (by simpa only [Fin.tail] using (show (∑ i:Fin (n+1),h i.succ)≤ k from by omega)) (fun i=>p i.succ)) hv t

-- Good seam order assignment
lemma closingW (n:ℕ) (X:ProfileW)(W:Fin (n+1)→ProfileW)(p:∀ i,SplitHill X (W i) η K D'):∃ q,SplitHill X q η K D' ∧ ∀ i,q≤ W i:=by
   induction n with
   | zero=> exact ⟨W 0,p 0,Fin.forall_fin_one.mpr le_rfl⟩
   | succ n ih=>
      obtain ⟨V,v,e⟩:= ih (Fin.tail W) (fun i=> p i.succ); exact ⟨W 0 ⊓ V,(p 0).union v,fun i=> Fin.cases inf_le_left (fun i=> inf_le_right.trans (e i)) i⟩
lemma mate (P Q R: Pal ℝ U): woad P (Q-R)=woad P Q-woad P R:=by
   funext i j; unfold woad; simp only [Finset.sum_apply,Pi.sub_apply,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i hi=>?_; unfold knitS; rw [← swirl_mo, ← Finset.sum_sub_distrib]; apply congr_arg _; refine Finset.sum_congr rfl (fun w hw=> funext fun x=>?_); unfold webT; simp only [dif_pos (Finset.mem_antidiagonal.mp hw),Pi.sub_apply,mul_sub]
lemma pairingP (P Q R: Era G ℝ): agateV P (Q-R)=agateV P Q-agateV P R:=Prod.ext (funext fun _n=>mate ..) (mate ..)
abbrev startK (A:Levels G)(Ñ:ChartRatio G)(m N k:ℕ)(P:Era G ℝ):=verseI A Ñ m N k P
abbrev DeltaGap (A:Levels G)(Ñ:ChartRatio G)(m N:ℕ){n}(P:Fin (n+1)→Era G ℝ)(h:Fin (n+1)→ℕ): Era G ℝ:= startK A Ñ m N (∑ i,h i) (MassP G ℝ n P)-MassP G ℝ n (fun i=>startK A Ñ m N (h i) (P i))
variable {n':ℕ}
lemma scrape (A:Levels G)(Ñ:ChartRatio G)(m N:ℕ)(P:Fin (n'+1+1)→Era G ℝ) (v:Fin (n'+1+1)→ ℕ):
   let Q:=Fin.tail P; let h:=Fin.tail v; let X:= startK A Ñ m N (v 0) (P 0); DeltaGap A Ñ m N P v= JoinGap A Ñ m N (v 0) (∑ i,h i) (P 0) (MassP G ℝ n' Q)+agateV X (DeltaGap A Ñ m N Q h):=by
   intro Q h X; let S a:= startK A Ñ m N a; let Y:= fun i=> S (h i) (Q i); let F:=MassP G ℝ n' Q
   unfold DeltaGap; rw [pairingP,Fin.sum_univ_succ, MassP, MassP]; unfold JoinGap; abel
lemma Fringed.nullV {x:ℝ}(p:0≤δ)(h:0≤x): Fringed k e u η x δ (0:Era G ℝ) 0:=by
   have ht: Auth k (0:Era G ℝ):=by let S:Unit→ Era G ℝ:= fun _=>0; simpa using Auth.sum (P:=S) (S:=∅) (by simp)
   exact ⟨ht,ht,p,fun i j _=> YieldP.zero.step h p⟩
variable {E W':Credit}{R: Realm G (e+1) E}{m b' N N':ℕ}
lemma drifted (n:ℕ)(T V: Fin (n+1)→ Era G ℝ)(h:Fin (n+1)→ℕ)(X:Fin (n+1)→ℝ)(P:Fin (n+1)→ ProfileW)
   (_z:1≤K)(_hD:0<D')(hr:∑ i,h i ≤ k)(g:0≤η)(w:∀ i j,i≠j→ SplitHill (P i) (P j) η K D')
   (q:SpringD R k u b W')(t:R.anchor≤m)(p:m<b')(he:b'≤ N)(hv:b'≤ N')
   (hx:δWarm R m b'≤δ)(hg:∀ i,Auth (h i) (T i))(hf:∀ i, Auth (h i) (V i))
   (hp:∀ i,PaidMer e (u+b) (heirP R.draws m (P i)) (T i) (V i) (X i) δ)
   (hy:∀ i, Fringed (h i) e u η (X i) δ (verseI R.draws R.paid m N (h i) (T i)) (verseI R.draws R.paid m N' (h i) (V i))):
   Fringed (∑ i,h i) e u η ((n:ℝ)*R.cash (priceWG G e k u b E W') m*pearlB u b K D'*nuP (coinMat k e +1) n X) δ (DeltaGap R.draws R.paid m N T h) (DeltaGap R.draws R.paid m N' V h) :=by
   induction n with
   | zero=>
      unfold DeltaGap; rw [Fin.sum_univ_succ,Fintype.sum_empty,add_zero]; simp only [MassP,sub_self,Nat.cast_zero,zero_mul]; exact Fringed.nullV (hy 0).crest le_rfl
   | succ n ih=>
    let K':= coinMat k e; let P':=Fin.tail P; let D:= R.cash (priceWG G e k u b E W') m; let A:= Fin.tail h; let F:= Fin.tail V; let Q:= Fin.tail T; let S:= ∑ i,A i; let Y:= Fin.tail X; let M:=pearlB u b K D'; let C:=nuP (K'+1) n Y
    have hS: h 0+ S≤k:= by rw [Fin.sum_univ_succ] at hr; exact hr
    have hh:S≤ k:=by omega
    have hz:=ih Q F A Y P' hh (fun i j p=> w _ _ (fun H=>p (Fin.succ_inj.mp H))) (fun i=>hg i.succ) (fun i=>hf i.succ) (fun i=> hp i.succ) (fun i=>hy i.succ)
    obtain ⟨V',H,t'⟩:= closingW n (P 0) P' fun j=> w _ _ (Ne.symm (Fin.succ_ne_zero j))
    let Q':=MassP G ℝ n Q; let F':=MassP G ℝ n F; have ha: Auth S Q':= manCo Q A fun i=>hg _; have hB: Auth S F':= manCo F A fun i=>hf _
    have hd:= (hy 0).crest
    have hy':PaidMer e (u+b) (heirP R.draws m V') Q' F' (nuP K' n Y) δ:= pedig n Q F A Y _ hh (fun i=> hg i.succ) (fun i=>hf i.succ) (fun i=> (hp i.succ).grade (fun x=>t' i _) le_rfl) hd
    have ht:= enterShore q t p he hv _ _ _ _ (hg 0) (hf 0) ha hB H hS hx (hp 0) hy'
    rw [scrape,scrape]; apply ((ht.plus (fringedMat (hy 0) hz g hS) g).tall (Nat.le_of_eq (Fin.sum_univ_succ h).symm)).pay
    rw [nuP]; let B:= X 0; have hu:0≤C:= loadN _ _ _ (by linarith [show 0≤K' from coinMat_nn ..]) (fun i=> (hy i.succ).nn); have hC: nuP K' n Y≤ C:= by unfold C; rw [loadRep,loadRep]; refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (coinMat_nn ..) ?_ n) (Finset.prod_nonneg fun i _=> (hy i.succ).nn); linarith
    change D*(M*(B*nuP K' n Y))+K'*B*((n:ℝ)*D*M*C) ≤ (n+1:ℕ)*D*M*((K'+1)*B*C)
    have hD:0≤D:= zero_le_one.trans (Credit.purchase _ (R.depth m t)); have hB:0≤B:= (hy 0).nn; have hM:0≤ M:=pearl_paid H
    calc
     _ ≤ D*(M*(B*C))+K'*B*((n:ℝ)*D*M*C):= by gcongr
     _ ≤ _ := by push_cast; nlinarith only [show 0≤(n:ℝ)*B*D*M*C by positivity,show 0≤K'*B*D*M*C by have he:0≤K':=coinMat_nn ..; positivity]
end YM.WilsonCoeffUV.Mer
