import YM.OPE.Compatible.Stamen.Sample
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
abbrev Bunch (I:Type):= Root I×Root I
def peacock (I:Type)(r:ℕ):Bunch I× Page I r ≃ Page I (r+2) where
     toFun u:= usher u.1.1 _ (usher u.1.2 r u.2)
     invFun u:= ((u 0,mort u 0),melt u)
     left_inv:=by rintro ⟨⟨x,y⟩,u⟩; simp only[usher,melt,mort,Fin.cons_zero,Fin.tail_cons]
     right_inv:=by intro i; simp only [usher,melt,mort,Fin.cons_self_tail]
def duco (A:RowB I)(p:Script I (r+2))(a:Bunch I): Script I r:= fun i=>tunnel A.val p (peacock I r (a,i))
lemma paia (v:Page I r)(A:RowB I)(p:Script I (r+2)): pad A.val p v=∑' a:Bunch I, duco A p a v:=by
      let F:= Sack.rope melt (tunnel A.val p); unfold pad Sack.rope; let f:=fun i:Page I (r+2)=> if melt i=v then tunnel A.val p i else 0; let g(x:Bunch I):=peacock I r (x,v); have ht:Injective g:=fun ⦃x y⦄ h=> (Prod.mk.inj ((peacock I r).injective h)).1
      change (∑' i,f i)=_; symm; rw [show (fun a:Bunch I=> duco A p a v)= f∘g from ?_]; apply ht.tsum_eq; intro i h; have hp: melt i=v:=by by_contra hc; exact h (if_neg hc)
      refine ⟨((peacock I r).symm i).1,?_⟩; unfold g; rw [← hp,show melt i= ((peacock I r).symm i).2 from rfl]; exact (peacock I r).apply_symm_apply _
      ext1 x; refine (show f (g x)= duco A p x v from ?_).symm -- rw under comp?
      simp only [g,f,duco,peacock,usher,melt,mort,Fin.tail_cons,if_true,Equiv.coe_fn_mk]
lemma duoW (x:Bunch I)(v:Page I r)(p:Script I (r+2))(A:RowB I): duco A p x v = A.val x.1.2 x.2.2 (x.2.1-x.1.1)*toque (toque p x.1) x.2 v:=by simp [duco,peacock,toque,usher,tunnel,poke,mort]; ring
lemma tollDu (A:RowB I)(p:Script I (r+2))(h:soot m p C): Summable fun t:Bunch I × Page I r=> figure m t.2 * ‖duco A p t.1 t.2‖:=by
       let z(i:Page I (r+2)):= figure m i*‖p i‖; let q:Bunch I× Page I r → Page I (r+2):= peacock I r; let f(t:Bunch I×Page I r):= duco A p t.1 t.2; have hp:Summable (z ∘ q):= (peacock I r).summable_iff.mpr h.2.1; refine (hp.mul_right A.fare).of_norm_bounded ?_; rintro ⟨v,i⟩; rw [Real.norm_of_nonneg (mul_nonneg (figure_pos i).le (norm_nonneg _)),duco,tunnel,norm_mul]; let k:=q (v,i); have ht: figure m i≤ figure m k:= (usherPrice v.2 i).trans (usherPrice v.1 (usher v.2 _ i))
       exact (mul_le_mul ht (mul_le_mul_of_nonneg_left (A.lease ..) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (figure_pos k).le).trans_eq (mul_assoc ..).symm
lemma prop_pad (p:Script I (r+2))(h:p.sorted)(A:RowB I): (pad A.val p).sorted:=by
       intro i; ext1 v; change pad A.val p (v ∘ i)=_; simp_rw [paia]; apply tsum_congr; intro a; rw [duoW,duoW]; apply congr_arg; exact congr_fun (touchS _ _ (touchS _ _ h) i) v
variable [Fintype I]
omit [Fintype I] in lemma boundDu {v:Fin r→fieldX (Palette I)}(h:Glob v (fun _=>0))(p:Script (Palette I) (r+2))(hp:soot m p C)(A:RowB (Palette I)):
     wholeX (pad A.val p) v= ∑' a:Bunch (Palette I), wholeX (duco A p a) v:=by
         let g(x:Bunch (Palette I) × Page (Palette I) r):=duco A p x.1 x.2*wordX v x.2; choose c hc H using h; have hh(x): ‖g x‖≤(∏ i,c i)*(figure m x.2*‖duco A p x.1 x.2‖):=by
                   unfold g; rw [norm_mul]; refine (mul_le_mul_of_nonneg_left (wordXbill (k:=fun _=>0) hc H (show ∑ _ :Fin r,(0:ℕ)≤m by simp) x.2) (norm_nonneg _)).trans_eq ?_; ring
         have he: Summable g:= ((tollDu A p hp).mul_left _).of_norm_bounded hh; unfold wholeX; rw [← he.tsum_prod, ← Equiv.tsum_eq (Equiv.prodComm ..)]; erw [(show Summable (g ∘ Equiv.prodComm (Page (Palette I) r) _) from (Equiv.prodComm ..).summable_iff.mpr he).tsum_prod] -- rw patterns eups
         apply tsum_congr; intro i; rw [paia,← tsum_mul_right];rfl
lemma beacon (p:Script (Palette I) (r+2))(hp:soot m p C)(hh:p.abides)(A: RowB (Palette I)): (pad A.val p).abides:=by
      intro i n w s; let X:=update w i (cliff s); let a(j):=unfoldX (X j); rw [bridgeX]; change wholeX _ a= _; rw [boundDu (fun j=>quietZ _) p hp]; change (∑' k:Bunch (Palette I), wholeX (duco A p k) a)=0; rw [show (fun k:Bunch (Palette I)=> wholeX (duco A p k) a)= fun _=>0 from ?_]; simp; ext1 k; let f:= toque (toque p k.1) k.2; let B:= A.val k.1.2 k.2.2 (k.2.1-k.1.1)
      rw [show duco A p k=B • f from funext fun i=>duoW ..]; rw [← (bridgeX X), score_scaled]; rw [veilX (toque p k.1) (owns p k.1 hp) (veilX p hp hh k.1) k.2 i n w s]; ring
end YM.OPE.Silt.Phere
