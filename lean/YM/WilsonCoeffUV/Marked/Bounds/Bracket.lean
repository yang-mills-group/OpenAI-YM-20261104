import YM.WilsonCoeffUV.Marked.Bounds.SpanPrice
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric
open scoped Topology BigOperators
variable {c f:Side}{ι α U β V t:Type}{J K I S T:Finset ι}{p:ι→U}{d:Bank.Distance U}{D k:ι→ℕ}{h' i j i' j' a e r h N n m l:ℕ}{G:Gauge}{σ τ u A B C:ℝ}
variable {w s:Gear G→ℝ}

lemma tuneDr {M:(I:Gear G) → ZL D S e I → ropes Cover (Helms I) (Helms I)}(h:J.Nonempty)(hp:i' ≤ e)(p:∀ I t, dragCup Bank.terrain I.s I.D (M I t)) (u:∀ I,0≤ w I)(t:∀ I,w I<s I)(v:∀ I,s I<I.s) {Y:(I:Gear G) →ZL D S e I→ Gen (Pen D J) (Cloth (Helms I))} (g: QuestB s (fun I t=> Y I t (j+1)) J)(he:r=i+j) : QuestB w (fun I t=> ruins (swivel (rill (M I t) (t.L.P.rays h' i') (Y I t) r i j))) J:=by
   obtain ⟨d,H⟩:= g; obtain ⟨k,W⟩:= Satin.flywheel h' i' (i+1) (e+1) 0 (by omega) s v (fun I=> (u I).trans (t I).le)
   refine ⟨d+k,fun I=>?_⟩; obtain ⟨A,hA,H⟩:=H I; obtain ⟨B,hB,L⟩:= W I; let U:=sealM i j; have hf:0≤ U:=by unfold U sealM; positivity;
   let V:= tiePay (Helms I) 2 (s I-w I); have hg:0≤V:=tie_non (sub_pos.mpr (t I)); have hw:= zero_le_one.trans I.bill_nn; refine ⟨U*I.D*A*B*V,by positivity,fun x=>?_⟩
   have hZ:= Wrest (Grapple.spin (grassyFlow (P:= x.L.P.rays h' i') (Q:= Y I x) ((p I x).mono (v I).le) (L x.L).pose (H x) ((u I).trans (t I).le))) (t I) (u I) h
   rw [he]; apply hZ.more; apply le_of_eq; unfold U V sealM largus; rw [pow_add]; ring

variable [DecidableEq ι]
lemma tuneBron {Y:(I:Gear G) → ZL D S e I→ Gen (Pen D K) (Cloth (Helms I))}{Z:(I:Gear G)→ ZL D S e I→ Gen (Pen D (J\K)) (Cloth (Helms I))}(m: K⊆ J)(q:QuestB s (fun I t=> Y I t (i+1)) K)(x:QuestB s (fun I t=> Z I t (j+1)) (J\K))(g:J.Nonempty)(p:∀ I,0≤w I)(u:∀ I,w I<s I)(v:∀ I,s I<I.s){l}(h:i+j=l):QuestB w (fun I t=> ruins (swivel (lakeL t.L.P.payMat m (Y I t) (Z I t) l i j))) J:=by
   subst l; obtain ⟨d,h⟩:=q; obtain ⟨c,x⟩:=x; refine ⟨d+c,fun I=>?_⟩; obtain ⟨A,hA,H⟩:= h I; obtain ⟨B,hB,L⟩:=x I; let U:=sealM i j; let V:= tiePay (Helms I) 2 (s I-w I); have hg:0≤V:=tie_non (sub_pos.mpr (u I)); have hf:0≤ U:=by unfold U sealM; positivity
   have hw:= zero_le_one.trans I.bill_nn; refine ⟨U*I.D*A*B*V,by positivity,fun t=>?_⟩; apply (Wrest (Grapple.spin (grassyLeaf (P:=Y I t) (Q:=Z I t) m ((pm_rate t.L).oneP.mono (v I).le) (H t) (L t) ((p I).trans (u I).le))) (u I) (p I) g).more; unfold U V; have he: K.card+(J\K).card=J.card:=by rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card m
   conv_rhs=> rw [← he,pow_add,pow_add];
   exact le_of_eq (by ring)

lemma choirZ (D :ι→ℕ)(G:Gauge)(S:Finset ι)(j i e r:ℕ)(p:i≤e)(h:J⊆ S)(v:Gear G→ℝ)(W:∀ I,v I<I.s)(u:∀ I,0≤v I) : QuestB v (fun I (t:ZL D S e I)=> t.quietT J j i r) J:=by
   induction j using Nat.strong_induction_on generalizing i r v J with
   | h j ih=>
      by_cases w:J=∅; · subst J; simp_rw [ZL.silent]; exact QuestB.zero
      have g:J.Nonempty:=Finset.nonempty_iff_ne_empty.mpr w
      cases j with
      | zero=>
         refine ⟨0,fun I=>?_⟩; let A:= tiePay (Pick I) r (I.s-v I); let B:= Real.exp (8*I.s); have hf:0≤ A:=tie_non (sub_pos.mpr (W I)); have hv:B≥ 0:= (Real.exp_pos _).le; have hh:= zero_le_one.trans I.bill_nn; have he:0≤I.s:=(u I).trans (W I).le
         refine ⟨I.D^r*A*B,by positivity,fun t=>?_⟩; let Q:=upperP I t.L; let Z:=tiles I.patch.L ((t.K J).2 i) r; have ht: t.quietT J 0 i r=ruins (gloss Q Z):=by unfold ZL.quietT Humour; rw [Temple]; exact funext fun x=> climb_cut Q _
         dsimp only; rw [ht]; apply (Wrest (motionNp (F:=Z) (votes I t.L).oneP (plankB I.patch t.places t.token J ((t.K J).2 i r) ((t.live J h i p r).shave I.room) he) he) (W I) (u I) g).more; rw [pow_zero,mul_one]; exact le_of_eq (by unfold A B Pick; change I.D^r*(_*Real.exp _)*tiePay (Pick I) r (I.s-v I)=_; unfold Pick; ring)
      | succ j=>
         have He (I:Gear G)(x: ZL D S e I): x.quietT J (j+1) i r=((j+1:ℕ):ℝ)⁻¹ • (rime x.L.P.payMat (x.quietT J j i) + Soil.paintC x.L.P.payMat x.L.P.rays (x.quietT J) j i + Soil.paintC x.L.P.payMat.transpose x.L.P.rays (x.quietT J) j i+ SubC x.L.P.payMat x.quietT j i J) r:=congr_fun (warmUp ..) _
         let s I:=v I+(Gear.s I-v I)/2; have ht I:s I<I.s:=by unfold s; linarith [W I];
         have hv I:v I<s I:=by unfold s; linarith [W I];
         let H K (q:K⊆ S) i' j' (x:i'≤ i) (f:j'≤j) (r:ℕ):=ih j' (by omega) i' r (x.trans p) q s ht (fun I=>(u I).trans (hv I).le)
         have hx (Q:(I:Gear G)→ZL D S e I→ ropes Cover (Helms I) (Helms I)) (p':∀ I t,dragCup Bank.terrain I.s I.D (Q I t)) : QuestB v (fun I t=> Soil.paintC (Q I t) t.L.P.rays (t.quietT J) j i r) J:=by
            unfold Soil.paintC rondel; simp_rw [Finset.sum_apply]; apply QuestB.sum; intro a ha; apply QuestB.sum; intro b hb; apply QuestB.sum; intro z hz; have he:=Finset.mem_antidiagonal.mp ha; have ht':= Finset.mem_antidiagonal.mp hb; exact tuneDr g (by omega) p' u hv ht (Y:=fun I t=> t.quietT J a.2 b.2) (H J h b.2 a.2 (by omega) (by omega) (z.2+1)) (Eq.symm (Finset.mem_antidiagonal.mp hz))
         have hU:QuestB v (fun I (t:ZL D S e I)=> SubC t.L.P.payMat t.quietT j i J r) J:=by
            unfold SubC; simp_rw [Finset.sum_apply]; apply QuestB.sum; intro K y; have hl:= Finset.mem_powerset.mp y; simp_rw [dif_pos hl,Sewing,Finset.sum_apply,overture];
            apply QuestB.sum; intro a ha; have hm:=Finset.mem_antidiagonal.mp ha; apply QuestB.sum; intro b hb; have hn:=Finset.mem_antidiagonal.mp hb; apply QuestB.sum; intro z hz; apply tuneBron (Y:=fun I t=>t.quietT K a.1 b.1) (Z:=fun I t=>t.quietT (J\K) a.2 b.2) hl _ _ g u hv ht (Finset.mem_antidiagonal.mp hz)
            · exact H K (hl.trans h) _ _ (by omega) (by omega) _
            exact H _ (Finset.sdiff_subset.trans h) _ _ (by omega) (by omega) _
         have hZ := ((tuneBr (Z:=fun I t=> t.quietT J j i) g u hv (s:=s) (fun I=>(ht I).le) (H J h i j le_rfl le_rfl (r+2))).plus (hx _ (fun I t=>(pm_rate t.L).oneP))).plus (hx _ (fun I t=>(BankT (pm_rate t.L)).oneP))
         simp_rw [He]; exact (hZ.plus hU).μ _
end YM.WilsonCoeffUV.Wheel.Mark
