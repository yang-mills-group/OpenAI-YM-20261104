import YM.WilsonCoeffUV.Stable.WickTariff
/-! # Post rates for linked lipschitz. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open Soil
open scoped Topology BigOperators
variable {L:Side}{U α β V W ι : Type*}{i k r u j l:ℕ} {A B C D s σ η δ a b: ℝ} {o:Cover}
lemma finance_pick {s:ι→ℝ}(p:SumBudget s A){f:U→ι}(g:Injective f): SumBudget (s ∘ f) A:= ⟨fun _=>p.1 _,p.2.1.comp_injective g,(tsum_comp_le_tsum_of_inj p.2.1 p.1 g).trans p.2.2⟩
variable [NormedAddCommGroup V]
lemma Fruit.gleanP {P:Ten V (Cloth (α⊕β)) r}(h:Fruit o η u P A): Fruit o η u (scoop P) A:=by
    let f (x:dock Cover β r):dock Cover (α⊕β) r:=pierR ∘ x
    have he: Injective f:= by intro i j h; ext1 v; have ht:=congr_fun h v; simp only [f,Function.comp_apply,pierR,Prod.mk.injEq,Sum.inr.injEq] at ht; exact Prod.ext ht.1 ht.2
    have hg: (fun i:dock Cover β r=> hedge o η u i*‖scoop P i‖)= (fun i:dock Cover (α⊕β) r=>hedge o η u i * ‖P i‖) ∘ f:= by
        ext1 i; unfold Function.comp hedge autumn tread; simp only [stud,scoop,f]; congr 4
    unfold Fruit Award; rw [hg]; exact finance_pick h he

structure YieldP (p: Cover)(η:ℝ)(u:ℕ) (A δ:ℝ)(P Q: Ten V (Cloth α) r): Prop where
   wax: Fruit p η u P A
   wane: Fruit p η u Q A
   toll: Fruit p η u (P-Q) (A*δ)
variable {P Q R T: Ten V (Cloth α) r}
lemma YieldP.nn(p: YieldP o η u A δ P Q):0≤A:= p.wax.C
lemma YieldP.step (h:YieldP o η u A δ P Q)(g:A≤B)(p:0≤δ): YieldP o η u B δ P Q:=⟨h.wax.more g,h.wane.more g,h.toll.more (mul_le_mul_of_nonneg_right g p)⟩
lemma YieldP.same (h: Fruit o η u P A)(p:0≤δ): YieldP o η u A δ P P:= ⟨h,h,by rw [sub_self]; exact Fruit.zero.more (mul_nonneg h.C p)⟩
lemma YieldP.shrink (h:YieldP o η u A δ P Q)(p:0≤σ)(e:σ≤η): YieldP o σ u A δ P Q:= ⟨h.wax.shave p e,h.wane.shave p e,h.toll.shave p e⟩
lemma YieldP.zero : YieldP o η u 0 δ (0: Ten V (Cloth α) r) 0:=⟨Fruit.zero,Fruit.zero,by rw [sub_zero,zero_mul]; exact Fruit.zero⟩
lemma YieldP.plus (h: YieldP o η u A δ P Q)(g:YieldP o η u B δ R T)(p:0≤η): YieldP o η u (A+B) δ (P+R) (Q+T):=⟨h.wax.plus g.wax p,h.wane.plus g.wane p,by rw [add_sub_add_comm,add_mul]; exact h.toll.plus g.toll p⟩
lemma YieldP.sum {S:Finset ι}{P Q:ι→ Ten V (Cloth α) r}{A:ι→ℝ}(h:∀ i∈ S,YieldP o η u (A i) δ (P i) (Q i))(p:0≤η): YieldP o η u (∑ i∈ S,A i) δ (∑ i∈S,P i) (∑ i∈S,Q i):=⟨Fruit.sum (fun i hi=>(h i hi).wax) p,Fruit.sum (fun i hi=>(h i hi).wane) p,by rw [Finset.sum_mul,←Finset.sum_sub_distrib]; exact Fruit.sum (fun i hi=>(h i hi).toll) p⟩
lemma YieldP.gleanP {P Q: Ten V (Cloth (α⊕β)) r}(h:YieldP o η u A δ P Q): YieldP o η u A δ (scoop P) (scoop Q):=⟨h.wax.gleanP,h.wane.gleanP,h.toll.gleanP⟩
lemma YieldP.travel {w:Site L}(p:0≤η)(h:η≤1)(hx:YieldP (L.val • o+ lift w) (η/L.val) u A δ P Q): YieldP o η u (9^u*A) δ (turnTen (panel L α).symm P) (turnTen (panel L α).symm Q):=⟨hx.wax.panel p h,hx.wane.panel p h,by rw [mul_assoc]; exact hx.toll.panel p h⟩
variable [NormedSpace ℝ V]
lemma YieldP.μ(h:YieldP o η u A δ P Q)(c:ℝ): YieldP o η u (|c| * A) δ (c•P) (c•Q):=⟨h.wax.μ c,h.wane.μ c,by rw [←smul_sub,mul_assoc]; exact h.toll.μ c⟩
lemma YieldP.mag (h:YieldP o η u A δ P Q)(p:twain B δ a b)(v:0≤η):YieldP o η u (2*A*B) δ (a•P) (b•Q):=by
   have ht:B*A≤2*A*B:= by have he:=mul_nonneg h.nn p.nn; nlinarith
   refine ⟨(h.wax.μ a).more ((mul_le_mul_of_nonneg_right p.main h.nn).trans ht), (h.wane.μ b).more ((mul_le_mul_of_nonneg_right p.side h.nn).trans ht), ?_⟩
   rw [show a•P-b•Q=(a-b)•P+b•(P-Q) by rw [sub_smul,smul_sub]; abel]; exact ((h.wax.μ _).plus (h.toll.μ _) v).more ((add_le_add (mul_le_mul_of_nonneg_right p.gap h.nn) (mul_le_mul_of_nonneg_right p.side h.toll.C)).trans_eq (by ring))
lemma glue_fin [Fintype β](h:0<s){G: ropes Cover α β}(p:dragCup Bank.terrain s B G)(Y:Fruit o η u P A)(he:0≤η)(hu:η≤1): Ragtop o η u (gloss G P) ((B*tender β s u)^r*A):= by
   have hg:= ribbon_finance h (fun _:Fin r=> G) _ (fun _=>p) Y he hu; rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin] at hg; exact hg
private lemma varnish_cost [Fintype β](h:0<s){G H:ropes Cover α β}(p:Ballast s B δ G H)(Y:Fruit o η u P A)(he:0≤η)(hu:η≤1) : Ragtop o η u (gloss G P-gloss H P) (r*((B*tender β s u)^r*A)*δ):=by
   let Q (i:ℕ)(j:Fin r):= if j.val< i then G else H
   let K:=(B*tender β s u)^r*A*δ
   have hh:∀ i≤r,Ragtop o η u (ribbon (Q i) P-gloss H P) (i*K):=by
       intro i; induction i with
       | zero=> intro _; rw [show Q 0=(fun _=>H) from funext fun i=>if_neg (Nat.not_lt_zero _),show ribbon _ _ - _=0 from sub_self (gloss H P),Nat.cast_zero,zero_mul]; exact Award.zero
       | succ i ih=>
         intro h'; let v: Fin r:=⟨i,h'⟩; let M:=Function.update (Q i) v (G-H); let U (j:Fin r):= if j=v then δ else 1
         have Hx j:dragCup Bank.terrain s (B*U j) (M j):= by
            unfold U M; by_cases g:j=v; · rw [g,if_pos rfl,Function.update_self]; exact p.between
            rw [if_neg g,Function.update_of_ne g,mul_one]; unfold Q; split; exact p.oneP
            exact p.otherP
         have hp:= ribbon_finance h M _ Hx Y he hu
         have hU j: B*U j*tender β s u=(B*tender β s u)*U j:=mul_right_comm ..
         simp_rw [hU,Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin] at hp
         rw [show ∏ i,U i=δ from ?_ ] at hp
         · have hy:Ragtop o η u (ribbon M P) K:= by unfold K; rw [mul_right_comm,mul_pow]; exact hp
           have hz: Q (i+1)=Function.update (Q i) v G:= by
               funext j; by_cases hx:j=v; · rw [hx,Function.update_self]; exact if_pos (Nat.lt_succ_self i)
               rw [Function.update_of_ne hx]; unfold Q; simp only [show j.val< i+1↔j.val< i from by have he:j.val≠i:=fun h=>hx (Fin.ext h); omega]
           rw [show ribbon (Q (i+1)) P=ribbon M P+ribbon (Q i) P from ?_,add_sub_assoc,Nat.cast_succ,add_mul,one_mul,add_comm _ K]; exact hy.plus (ih (by omega)) he
           rw [hz]; funext x y; unfold ribbon; let a j (g:ropes Cover α β):ℝ:= g (y j) (x j)
           have hk : (∏ j, a j (Function.update (Q i) v G j))= (∏ j, a j (M j))+(∏ j,a j (Q i j)):= by
              let u:=Q i; let L:=Function.update u v G; let S:=Finset.univ.erase v
              rw [← Finset.mul_prod_erase _ (fun j=> a j (L j)) (Finset.mem_univ v),← Finset.mul_prod_erase _ (fun j=> a j (M j)) (Finset.mem_univ v),← Finset.mul_prod_erase _ (fun j=> a j (u j)) (Finset.mem_univ v)]
              change a v (L v)*(∏ j∈S,a j (L j))=a v (M v)*(∏ j∈S,a j (M j))+a v (u v)*(∏ j∈S,a j (u j))
              rw [show (∏ j∈S,a j (L j))= ∏ j∈S,a j (u j) from Finset.prod_congr rfl (fun j hj=> congr_arg (a j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 ..)),show (∏ j∈S,a j (M j))= ∏ j∈S,a j (u j) from Finset.prod_congr rfl fun j hj=>congr_arg (a j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 ..),←add_mul]; congr 1; unfold L M; rw [Function.update_self,Function.update_self,show u v=H from if_neg (lt_irrefl _)]; unfold a; rw [Matrix.sub_apply]; abel
           rw [show _ = _ from hk,add_smul]; rfl
         rw [Finset.prod_eq_single v (fun b _ g=>if_neg g) (by simp)]; exact if_pos rfl
   specialize hh r le_rfl; rw [show Q r=(fun _=>G) from funext fun i=> if_pos i.isLt] at hh; rw [mul_assoc]; exact hh
variable [CompleteSpace V]
lemma prism_purchase [Fintype β] {G H:ropes Cover α β}(p:0<s)(h:Ballast s B δ G H)(Y: YieldP o η u A δ P Q)(he:0≤η)(hu:η≤1): YieldP o η u ((r+1:ℕ)*((B*tender β s u)^r*A)) δ (reflectCut G P) (reflectCut H Q):=by
   rw [show reflectCut G P=ruins (gloss G P) from funext fun x=> climb_cut .., show reflectCut H Q=ruins (gloss H Q) from funext fun x=> climb_cut ..]
   have hx:= glue_fin p h.oneP Y.wax he hu; have ht:=glue_fin p h.otherP Y.wane he hu
   have hh : (B*tender β s u)^r*A≤(r+1:ℕ)*((B*tender β s u)^r*A):= le_mul_of_one_le_left (mul_nonneg (pow_nonneg (mul_nonneg h.nn (tender_nn p ..)) _) Y.nn) (by exact_mod_cast Nat.le_add_left 1 _)
   refine ⟨(hx.collectR he).more hh,(ht.collectR he).more hh,?_⟩; rw [← hx.collect_minus ht he,show gloss G P-gloss H Q= (gloss G P-gloss H P)+gloss H (P-Q) from ?_]; exact (((varnish_cost p h Y.wax he hu).plus (glue_fin p h.otherP Y.toll he hu) he).epochT (le_of_eq (by push_cast; ring))).collectR he
   unfold gloss; funext x y; simp only [ribbon,Pi.sub_apply,Pi.add_apply,smul_sub]; abel
lemma YieldP.rimeX {P Q:Gen V (Cloth α)} (Y:YieldP o η u A δ (P (r+2)) (Q (r+2)))(p:0≤η)(G H:ropes Cover α α)(hb:0≤B)(hx:0≤ B*δ)(g:∀ i j,‖G i j‖≤B)(h:∀ i j,‖H i j‖≤B)(he:∀ i j,‖(G-H) i j‖≤ B*δ): YieldP o η u (2*B*A*fareV r) δ (rime G P r) (rime H Q r):=by
   have H0:= ragRain g hb Y.wax p; have H1:=ragRain h hb Y.wane p
   have hh: (1/2:ℝ)*B*(r+1:ℕ)*(r+2:ℕ)*A≤2*B*A*fareV r:=by
         have ha:=Y.nn; calc
          _ = B*A*fareV r:=by unfold fareV; ring
          _ ≤ _ := by have he:0≤ fareV r:=by unfold fareV; positivity
                      gcongr; linarith
   refine ⟨(H0.collectR p).more hh,(H1.collectR p).more hh,?_⟩; rw [rime,rime,← H0.collect_minus H1 p, show rain G P r-rain H Q r= rain G (P-Q) r+ rain (G-H) Q r from ?_]; exact (((ragRain g (P:=P-Q) hb Y.toll p).plus (ragRain he hx Y.wane p) p).epochT (le_of_eq (by unfold fareV; ring))).collectR p
   funext x y; simp only [rain_spell, Pi.sub_apply,Pi.add_apply, Matrix.sub_apply,mul_sub,sub_mul,smul_sub,sub_smul]; abel
lemma YieldP.tap [Fintype α]{P Q:Gen ℝ (Cloth α)}{U T: Gen V (Cloth α)}{G H:ropes Cover α α}(p:0<s) (y: PairA s A δ (P (i+1)) (Q (i+1)))(z:YieldP o η u C δ (U (k+1)) (T (k+1)))(g:Ballast s B δ G H)(e:i+k=r)(he:0≤η)(hv:η≤1) : YieldP o η u (3*pegPrice i k*(C*(B*tender α s u*(A*piped α i s u)))) δ (ruins (swivel (rill G P U r i k))) (ruins (swivel (rill H Q T r i k))):=by
   subst r; have hp := (ragRill p g.oneP y.pose z.wax rfl he hv).spun he; have hx:= (ragRill p g.otherP y.vale z.wane rfl he hv).spun he
   have hy : pegPrice i k*(C*(B*tender α s u*(A*piped α i s u))) ≤ 3*pegPrice i k*(C*(B*tender α s u*(A*piped α i s u))) := by
          have hb:=g.nn; have ha:=y.nn; have hC:= z.nn; have hh:=tender_nn p α u; have ht:=piped_nn (β:=α) i p u; have h0:0≤pegPrice i k:=by unfold pegPrice; positivity
          gcongr; linarith
   refine ⟨(hp.collectR he).more hy,(hx.collectR he).more hy,?_⟩; rw [← hp.collect_minus hx he]
   have H0:= ragRill p g.between y.pose z.wax rfl he hv
   have H1:= ragRill p g.otherP y.vale (Q:=U-T) z.toll rfl he hv
   have H2:= ragRill p g.otherP (P:=P-Q) y.visit z.wax rfl he hv
   let F:= rill G P U (i+k) i k; let W:=rill H Q T (i+k) i k
   rw [show swivel F - swivel W= swivel (F-W) from ?_,show F-W= _ from ?v]; exact (((((H0.plus H1 he).plus H2 he).spun he).collectR he).more (le_of_eq (by unfold pegPrice; ring)))
   case v=>
      unfold F W; funext x y; simp only [rill_spell, Pi.sub_apply,Pi.add_apply, Matrix.sub_apply,mul_sub,sub_mul,smul_sub,sub_smul]; abel
   funext x y; simp only [swivel,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_sub_distrib,smul_sub]
end YM.WilsonCoeffUV.Shard
