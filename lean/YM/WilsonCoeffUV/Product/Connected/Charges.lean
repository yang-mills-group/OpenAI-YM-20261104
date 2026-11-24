import YM.WilsonCoeffUV.Product.Connected.Post
/-!
# Whole-product currency
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
def weavePair (U:Type*)(i j:ℕ): ((Fin (i+j) → U)) ≃ (Fin i→ U) × (Fin j→ U) where
    toFun x:= (x∘ Fin.castAdd j,x∘ Fin.natAdd i)
    invFun x:= Fin.append x.1 x.2
    right_inv:= fun ⟨x,y⟩=> Prod.ext (funext fun i=>by simp) (funext fun i=>by simp)
    left_inv:= fun x=>Fin.append_castAdd_natAdd
lemma webCred (P:Ten ℝ U i)(Q:Ten ℝ U j)(s:(Fin i→U)→ ℝ)(t:(Fin j→U)→ ℝ)(w:(Fin r→U)→ ℝ)(p:0≤ w)(v:i+j=r)(h:∀ x, w x ≤ s (x ∘ Fin.cast v ∘ Fin.castAdd j) * t (x ∘ Fin.cast v ∘ Fin.natAdd i))(f:Award P s A)(g:Award Q t B): Award (webT P Q r) w (A*B):=by
    subst r; let W:= weavePair U i j; let V:=fun x=> (s (W x).1 *‖P (W x).1‖)*(t (W x).2*‖Q (W x).2‖)
    refine budget_minor (cap_walk V _ W.symm (fun _=>by unfold V; rw [W.apply_symm_apply]) (prod_cap f g.C (fun _=>g))) (fun i=>mul_nonneg (p i) (norm_nonneg _)) ?_
    intro x; refine (mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)).trans_eq ?_; unfold webT; rw [dif_pos rfl,norm_mul]; change (s (W x).1*t (W x).2)*(‖P (W x).1‖*‖Q (W x).2‖)=_; unfold V; ring
structure PledgeG (s:U→ℝ)(A δ:ℝ)(P Q:U→ℝ) : Prop where
   leftT : Award P s A
   rightT :Award Q s A
   times : Award (P-Q) s (A*δ)
lemma oceanT (P P':Ten ℝ U i)(Q Q': Ten ℝ U j)(s:(Fin i→U)→ ℝ)(t:(Fin j→U)→ ℝ)(w:(Fin r→U)→ ℝ)(p:0≤w)(v:i+j=r)(h:∀ x,w x ≤ s (x ∘ Fin.cast v ∘ Fin.castAdd j)*t (x∘ Fin.cast v ∘ Fin.natAdd i))(f:PledgeG s A δ P P')(g:PledgeG t B δ Q Q'): PledgeG w (2*A*B) δ (webT P Q r) (webT P' Q' r):=by
   have hx : A*B≤ 2*A*B:= le_trans (le_mul_of_one_le_left (mul_nonneg f.leftT.C g.leftT.C) (show (1:ℝ)≤2 by norm_num)) (le_of_eq (mul_assoc ..).symm)
   refine ⟨(webCred _ _ _ _ _ p v h f.leftT g.leftT).more hx,(webCred _ _ _ _ _ p v h f.rightT g.rightT).more hx,?_⟩
   rw [show webT P Q r-webT P' Q' r= webT (P-P') Q' r + webT P (Q-Q') r from ?_]; exact (((webCred _ _ _ _ _ p v h f.times g.rightT).plus (webCred _ _ _ _ _ p v h f.leftT g.times) p).more (le_of_eq (by ring)))
   subst r; funext x; unfold webT; simp only [Pi.sub_apply, Pi.add_apply, ↓reduceDIte]; rw [sub_mul,mul_sub]; abel
variable {W X: ProfileW}
lemma crestRoot (W:ProfileW)(x:dock Cover α r)(t:i+j=r): Ridge W x ≤ Ridge W (x ∘ Fin.cast t ∘ Fin.castAdd j)+ Ridge W (x ∘Fin.cast t ∘Fin.natAdd i):=by
    subst r; let T:= weavePair (Cloth α) i j; change _ ≤ Ridge W (T x).1+Ridge W (T x).2; refine Ridge.cap (fun v=> Fin.addCases ?_ ?_ v)
    · exact fun i=> (Ridge.host W (T x).1 i).trans (Nat.le_add_right ..)
    exact fun i=>(Ridge.host W (T x).2 i).trans (Nat.le_add_left ..)
lemma PromX.woadT (P P':Ten ℝ (Cloth α) i)(Q Q':Ten ℝ (Cloth α) j)(z:i+j=r)(p:PromX W u A δ P P')(q:PromX W u B δ Q Q'): PromX W u (2*A*B) δ (webT P Q r) (webT P' Q' r):=by
    have H:= oceanT P P' Q Q' (quoteT W u) (quoteT W u) (quoteT W u) (fun i=>zero_le_one.trans (quoteT_pos i ..)) z (fun i=> (autumn_mono zero_le_one u (crestRoot W i z)).trans (autumn_tax zero_le_one ..)) ⟨p.paid,p.feud,p.dropR⟩ ⟨q.paid,q.feud,q.dropR⟩
    exact ⟨H.leftT,H.rightT,H.times⟩
lemma FrondT (P P':Ten ℝ (Cloth α) i)(Q Q':Ten ℝ (Cloth α) j)(z:i+j=r)(h:0≤η)(p: YieldP 0 η u A δ P P')(q: YieldP 0 η u B δ Q Q'): YieldP 0 η u (2*A*B) δ (webT P Q r) (webT P' Q' r):=by
    have H:= oceanT P P' Q Q' (hedge 0 η u) (hedge 0 η u) (hedge 0 η u) (hedge_nn h) z (fun i=>(autumn_mono h u (webT_tread Bank.terrain 0 z i)).trans (autumn_tax h ..)) ⟨p.wax,p.wane,p.toll⟩ ⟨q.wax,q.wane,q.toll⟩
    exact ⟨H.leftT,H.rightT,H.times⟩
lemma swirl_mo (P Q: Ten ℝ U r): swirl (P-Q)= swirl P-swirl Q:=by funext x; simp only [swirl, Finset.sum_apply, Pi.smul_apply,Pi.sub_apply, Finset.sum_sub_distrib,smul_sub]
lemma PromX.swivels {P Q:Ten ℝ (Cloth α) i}(p:PromX W u A δ P Q): PromX W u A δ (swirl P) (swirl Q):=⟨p.paid.swirl,p.feud.swirl, by rw [←swirl_mo]; exact p.dropR.swirl⟩
lemma Whirling {P Q: Ten ℝ (Cloth α) i}(p:YieldP 0 η u A δ P Q)(v:0≤η): YieldP 0 η u A δ (swirl P) (swirl Q):=⟨p.wax.swirl v,p.wane.swirl v,by rw [←swirl_mo]; exact p.toll.swirl v⟩
def coinMat (k e:ℕ):ℝ:= (((e+1)*(k+e+1))*2:ℕ)
lemma coinMat_nn (k e:ℕ):0≤coinMat k e:=by unfold coinMat; positivity
lemma coinMat_pay (p:i≤e)(v:r≤k+e)(h:0≤A)(q:0≤B): ∑ _ ∈ Finset.antidiagonal i, ∑ _ ∈ Finset.antidiagonal r, 2*A*B ≤ coinMat k e*A*B:=by
    unfold coinMat; simp_rw [Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul]; push_cast; calc
     _ = ((i+1)*(r+1)*2)*A*B:=by ring
     _ ≤ _ := by gcongr; exact_mod_cast v
lemma procureT {P P' Q Q': Era G ℝ}(f:Auth i P)(f':Auth i P')(g:Auth j Q)(g':Auth j Q')(p:PaidMer e u W P P' A δ)(q:PaidMer e u W Q Q' B δ)(he:0≤δ)(hz:i+j≤k): PaidMer e u W (agateV P Q) (agateV P' Q') (coinMat k e*A*B) δ:=by
    intro n r t; have h:0≤A:= (p 0 0 (Nat.zero_le _)).paid.C; have hh:0≤ B:= (q 0 0 (Nat.zero_le _)).paid.C
    by_cases hp:r≤k+e
    · let S:= Finset.antidiagonal n; let T:= Finset.antidiagonal r; let C:= 2*A*B
      have he' j (hv:j∈S): PromX W u (∑ _∈T,C) δ (knitS (P.2 j.1) (Q.2 j.2) r) (knitS (P'.2 j.1) (Q'.2 j.2) r) :=by
          have hx:=Finset.mem_antidiagonal.mp hv; unfold knitS; exact (PromX.gather (S:=T) (fun i hi=> PromX.woadT _ _ _ _ (Finset.mem_antidiagonal.mp hi) (p _ _ (by omega)) (q _ _ (by omega)))).swivels
      simp_rw [agateV,woad,Finset.sum_apply]; exact (PromX.gather he').stepX (coinMat_pay t hp h hh) he
    rw [(f.manor g).coverN n r (by omega), (f'.manor g').coverN n r (by omega)]; exact PromX.zero.stepX (mul_nonneg (mul_nonneg (coinMat_nn ..) h) hh) he
lemma fringedMat {P P' Q Q': Era G ℝ}(p:Fringed i e u η A δ P P')(q:Fringed j e u η B δ Q Q')(he:0≤η)(hz:i+j≤k): Fringed (i+j) e u η (coinMat k e*A*B) δ (agateV P Q) (agateV P' Q'):=by
    have d:=p.inkV.manor q.inkV; have b:=p.pen.manor q.pen; refine ⟨d,b,p.crest,fun n r t=>?_⟩
    by_cases hp:r≤k+e
    · let S:= Finset.antidiagonal n; let T:= Finset.antidiagonal r; let C:= 2*A*B
      have he' j (hv:j∈ S): YieldP 0 η u (∑ _∈T,C) δ (knitS (P.2 j.1) (Q.2 j.2) r) (knitS (P'.2 j.1) (Q'.2 j.2) r):=by
          have hx:= Finset.mem_antidiagonal.mp hv; unfold knitS; exact Whirling (YieldP.sum (S:=T) (fun i hi=> FrondT _ _ _ _ (Finset.mem_antidiagonal.mp hi) he (p.heapS _ _ (by omega)) (q.heapS _ _ (by omega))) he) he
      simp_rw [agateV,woad,Finset.sum_apply]; exact (YieldP.sum he' he).step (coinMat_pay t hp p.nn q.nn) p.crest
    rw [d.coverN n r (by omega), b.coverN n r (by omega)]; exact YieldP.zero.step (mul_nonneg (mul_nonneg (coinMat_nn ..) p.nn) q.nn) p.crest
lemma Fringed.plus {P Q Y X: Era G ℝ}(p:Fringed i e u η A δ P Q)(v:Fringed i e u η B δ Y X)(h:0≤η): Fringed i e u η (A+B) δ (P+Y) (Q+X) :=⟨p.inkV.add v.inkV,p.pen.add v.pen,p.crest,fun i r he=> (p.heapS i r he).plus (v.heapS i r he) h⟩
lemma Fringed.tall {P Q:Era G ℝ}(p:Fringed i e u η A δ P Q)(v:i≤k): Fringed k e u η A δ P Q:= ⟨p.inkV.tall v,p.pen.tall v,p.crest,p.heapS⟩
lemma PaidMer.grade {P Q: Era G ℝ}(p:PaidMer e u W P Q A δ)(q:X ≤ W)(h:i ≤ u): PaidMer e i X P Q A δ:= by
   have hp {r:ℕ}{P: ChamberTen G ℝ r}{T:ℝ}(p: Rent W u P T): Rent X i P T:= Award.less p (fun x=> (pow_le_pow_right₀ (show (1:ℝ)≤1+(1:ℝ)*(Ridge X x) from le_add_of_nonneg_right (by positivity)) h).trans (quote_less X W q x)) (fun i=> zero_le_one.trans (quoteT_pos i ..))
   intro a j v; have h:=p a j v; exact ⟨hp h.paid,hp h.feud,hp h.dropR⟩
end YM.WilsonCoeffUV.Mer
