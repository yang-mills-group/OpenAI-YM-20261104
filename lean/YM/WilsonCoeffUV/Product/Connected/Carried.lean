import YM.WilsonCoeffUV.Product.Connected.OneStep
/-!
# Uniform rough prices carried in fields and positions
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
variable {u:ℕ}{p:ProfileW}
variable {δ η:ℝ}
structure PromX (p:ProfileW)(u:ℕ)(A δ:ℝ)(P Q:Ten ℝ (Cloth α) i): Prop where
    paid : Rent p u P A
    feud : Rent p u Q A
    dropR : Rent p u (P-Q) (A*δ)
variable {P Q Y W:Ten ℝ (Cloth α) i}
lemma PromX.stepX (h:PromX p u A δ P Q)(v:A≤B)(p':0≤δ): PromX p u B δ P Q:=⟨h.paid.more v,h.feud.more v,h.dropR.more (mul_le_mul_of_nonneg_right v p')⟩
lemma PromX.zero : PromX p u 0 δ (0:Ten ℝ (Cloth α) i) 0:=⟨Award.zero,Award.zero,by rw [sub_zero,zero_mul]; exact Award.zero⟩
lemma PromX.add(p':PromX p u A δ P Q)(v: PromX p u B δ Y W): PromX p u (A+B) δ (P+Y) (Q+W):=by
    have hx x:0≤ quoteT p u (x:dock Cover α i):=zero_le_one.trans (quoteT_pos x p u)
    refine ⟨p'.paid.plus v.paid hx,p'.feud.plus v.feud hx,?_⟩; rw [add_sub_add_comm,add_mul]; exact p'.dropR.plus v.dropR hx
lemma PromX.μ (h:PromX p u A δ P Q)(c:ℝ): PromX p u (‖c‖*A) δ (c•P) (c•Q):= ⟨h.paid.μ _,h.feud.μ _,by rw [←smul_sub,mul_assoc]; exact h.dropR.μ _⟩
lemma PromX.gather {P Q: U→ Ten ℝ (Cloth α) i}{S:Finset U}{w:U→ℝ}(h:∀ i∈ S,PromX p u (w i) δ (P i) (Q i)): PromX p u (∑ i∈ S,w i) δ (∑ i∈S,P i) (∑ i∈S,Q i):=by
   classical
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact PromX.zero
   | @insert i S e ih=> rw [Finset.sum_insert e,Finset.sum_insert e,Finset.sum_insert e]; exact (h _ (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma PromX.raft1 {P Q:Gen ℝ (Cloth α)}{G H: ropes Cover α α}(v:PromX p u A δ (P (i+2)) (Q (i+2)))(h:Ballast s B δ G H)(hx:0<s): PromX p u (2*B*fareV i*A) δ (rime G P i) (rime H Q i):=by
   have hv:= rimeX G P hx h.oneP v.paid; have ht:=rimeX H Q hx h.otherP v.feud; have he:= hv.take; have hh: B*fareV i*A ≤ 2*B*fareV i*A:= by have hu:= he.C; nlinarith
   refine ⟨he.more hh,ht.take.more hh,?_⟩; unfold rime; rw [← hv.minus ht,show rain G P i-rain H Q i=rain G (P-Q) i+rain (G-H) Q i from ?_]; apply ((RentX.plus (rimeX G (P-Q) hx h.oneP v.dropR) (rimeX (G-H) Q hx h.between v.feud)).take).more; exact le_of_eq (by ring)
   funext x y; simp only [rain_spell, Pi.sub_apply,Pi.add_apply, Matrix.sub_apply,mul_sub,sub_mul,smul_sub,sub_smul]; abel
lemma PromX.raft2 {P Q X Y:Gen ℝ (Cloth α)}{G H: ropes Cover α α}[Fintype α](v:PromX p u A δ (P (j+1)) (Q (j+1)))(x:PairA s C δ (X (i+1)) (Y (i+1)))(h:Ballast s B δ G H)(hx:0<s)(l:AngleSea p)(hz:i+j=r) : PromX p u (3*pegPrice i j*(A*((B*tender α s u)*(C*piped α i s u)))) δ (ruins (swivel (rill G X P r i j))) (ruins (swivel (rill H Y Q r i j))):=by
   subst r; have hv:= (torrid l G X P x.pose h.oneP v.paid hx rfl).crew; have ht:= (torrid l H Y Q x.vale h.otherP v.feud hx rfl).crew; let T:= pegPrice i j; let R:= tender α s u; let V:=piped α i s u; let L:=A*((B*R)*(C*V))
   have he:=hv.take; have hh: T* L≤3*T*L:=by have hu:0≤T*L:= he.C; nlinarith
   refine ⟨he.more hh,ht.take.more hh,?_⟩
   rw [← hv.minus ht, show swivel _-_= swivel (rill G X P (i+j) i j-rill H Y Q (i+j) i j) from ?_]
   · have h0:= torrid l (G-H) X P x.pose h.between v.paid hx rfl; have h1:=torrid l H (X-Y) P x.visit h.otherP v.paid hx rfl; have h2:=torrid l H Y (P-Q) x.vale h.otherP v.dropR hx rfl
     rw [show rill G X P (i+j) i j-rill H Y Q (i+j) i j=_ from ?_]; apply (((h0.plus h1).plus h2).crew.take).more; exact le_of_eq (by ring)
     funext x y; simp only [rill_spell,Pi.sub_apply, Matrix.sub_apply, Pi.add_apply, sub_mul,mul_sub,sub_smul,smul_sub]; abel
   funext x y; simp only [swivel, Pi.sub_apply, Pi.smul_apply,Finset.sum_apply, Finset.sum_sub_distrib,smul_sub]

lemma loreRent [Fintype β](w:AngleSea p)(x:Rent p u P A) (v:0<s){G H:ropes Cover α β}(q:Ballast s B δ G H): RentX p u (gloss G P-gloss H P) ((i:ℝ)*((B*tender β s u)^i*A)*δ):=by
   let K (j:ℕ)(k: Fin i):= if k.val< j then G else H
   let C:=(B*tender β s u)^i*A*δ
   have hh:∀ j ≤ i,RentX p u (ribbon (K j) P-ribbon (fun _=> H) P) (j*C):=by
       intro j; induction j with
       | zero=> intro _; rw [show K 0=(fun _=>H) from funext fun k=>if_neg (Nat.not_lt_zero _),sub_self,Nat.cast_zero,zero_mul]; exact Award.zero
       | succ j ih=>
         intro t; let v':Fin i:= ⟨j,t⟩; let M:=Function.update (K j) v' (G-H); let U (k:Fin i):= if k=v' then δ else 1
         have Hx k:dragCup Bank.terrain s (B*U k) (M k):=by
            unfold U M; by_cases h:k=v'; rw [h,if_pos rfl,Function.update_self]; exact q.between
            rw [if_neg h,Function.update_of_ne h,mul_one]; unfold K; split; exact q.oneP; exact q.otherP
         have hp:= ribbonRent M P v w _ Hx x; have hU k: B*U k*tender β s u=B*tender β s u*U k:= mul_right_comm ..
         simp_rw [hU,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hp; rw [show ∏ i,U i=δ from ?_] at hp
         · rw [mul_right_comm,←mul_pow] at hp
           rw [show ribbon (K (j+1)) P=ribbon M P+ ribbon (K j) P from ?_,add_sub_assoc,Nat.cast_succ,add_mul,one_mul,add_comm (↑j*C) C]; exact hp.plus (ih (by omega))
           rw [show K (j+1)= Function.update (K j) v' G from ?_]
           · funext x y; let a i (g:ropes Cover α β): ℝ:=g (y i) (x i)
             let T:= K j; let L:= Function.update (K j) v' G; let S:= Finset.univ.erase v'
             have ht:(∏ j,a j (L j))=(∏ j,a j (M j))+(∏ j,a j (T j)):=by
                rw [← Finset.mul_prod_erase _ (fun j=> a j (L j)) (Finset.mem_univ v'),← Finset.mul_prod_erase _ (fun j=> a j (M j)) (Finset.mem_univ v'),← Finset.mul_prod_erase _ (fun j=> a j (T j)) (Finset.mem_univ v')]
                rw [show (∏ j∈S,a j (L j))=∏ j∈S,a j (T j) from Finset.prod_congr rfl (fun j hj=>congr_arg (a j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 ..)),show (∏ j∈S,a j (M j))=∏ j∈S,a j (T j) from Finset.prod_congr rfl (fun j hj=>congr_arg (a j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 ..)),←add_mul]; congr 1; unfold L M; rw [Function.update_self, Function.update_self, show T v'= H from if_neg (lt_irrefl j)]; unfold a; rw [Matrix.sub_apply]; abel
             change (∏ j,a j (L j)) • P y= _; rw [ht,add_smul]; rfl
           funext k; by_cases h:k=v'; · rw [h,Function.update_self]; exact if_pos (Nat.lt_succ_self j)
           rw [Function.update_of_ne h]; unfold K; simp only [show k.val<j+1 ↔ k.val<j from by have he:k.val≠j:=fun H=>h (Fin.ext H); omega]
         rw [Finset.prod_eq_single v' (fun k _ g=>if_neg g) (by simp)]; exact if_pos rfl
   specialize hh i le_rfl; rw [show K i=(fun _=> G) from funext fun k=> if_pos k.isLt] at hh; rw [mul_assoc]; exact hh
lemma glossRent [Fintype β](w:AngleSea p){G:ropes Cover α β}(p':dragCup Bank.terrain s B G)(e:Rent p u P A)(t:0<s): RentX p u (gloss G P) ((B*tender β s u)^i*A):=by
    have he:= ribbonRent (fun _:Fin i=>G) _ t w _ (fun _=>p') e; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at he; exact he
lemma PromX.rafts [Fintype β](w:AngleSea p)(v:PromX p u A δ P Q)(t:0<s){G H:ropes Cover α β}(q:Ballast s B δ G H): PromX p u ((i+1:ℕ)*((B*tender β s u)^i*A)) δ (reflectCut G P) (reflectCut H Q):=by
    rw [show reflectCut G P= ruins (gloss G P) from funext fun x=>climb_cut ..,show reflectCut H Q=ruins (gloss H Q) from funext fun x=> climb_cut ..]; have hv:= glossRent w q.oneP v.paid t; have hp:=glossRent w q.otherP v.feud t; have hh:=hv.take.C
    have he: (B*tender β s u)^i*A≤(i+1:ℕ)*((B*tender β s u)^i*A):=le_mul_of_one_le_left hh (by exact_mod_cast Nat.le_add_left ..)
    refine ⟨hv.take.more he,hp.take.more he,?_⟩; rw [← hv.minus hp,show gloss G P-gloss H Q= gloss G P-gloss H P+gloss H (P-Q) from ?_]; exact (((loreRent w v.paid t q).plus (glossRent w q.otherP v.dropR t)).take.more (le_of_eq (by push_cast; ring)))
    funext x y; simp only [gloss,ribbon, Pi.sub_apply, Pi.add_apply, smul_sub]; abel
end YM.WilsonCoeffUV.Mer
