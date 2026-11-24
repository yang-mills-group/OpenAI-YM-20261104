import YM.WilsonCoeffUV.Root.Gain.Deterministic
/-!
# Post norms for compressed two cans. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open scoped Topology BigOperators
variable {n L:Side}{U α β V ι E : Type*}{k r l j:ℕ} {A B C D X Y σ η s t δ : ℝ} {d:Distance U}{w:U}{p:Cover}
section
variable [NormedAddCommGroup V] {P Q R T: Ten V (U×α) r}
structure Shelf (d:Distance U)(p:U) (s A δ:ℝ) (P Q: Ten V (U×α) r): Prop where
   wax: Cork d p s A P
   wane: Cork d p s A Q
   toll: Cork d p s (A*δ) (P-Q)
lemma Shelf.nn (h:Shelf d w s A δ P Q): 0≤A:= h.wax.1
lemma Shelf.step (h:Shelf d w s A δ P Q)(g:A≤B)(p:0≤δ): Shelf d w s B δ P Q:=⟨h.wax.cost g,h.wane.cost g,h.toll.cost (mul_le_mul_of_nonneg_right g p)⟩
lemma Shelf.encore (h:Cork d w s A P)(p:0≤δ): Shelf d w s A δ P P:= ⟨h,h,by rw [sub_self]; exact Cork.zero.cost (mul_nonneg h.1 p)⟩
lemma Shelf.shrink (h:Shelf d w s A δ P Q)(p:t≤s) : Shelf d w t A δ P Q:=⟨h.wax.mono p,h.wane.mono p,h.toll.mono p⟩
lemma Shelf.zero : Shelf d w s 0 δ (0: Ten V (U×α) r) 0:=⟨Cork.zero,Cork.zero,by rw [sub_zero,zero_mul]; exact Cork.zero⟩
lemma Shelf.add (h:Shelf d w s A δ P Q)(g:Shelf d w s B δ R T): Shelf d w s (A+B) δ (P+R) (Q+T):=⟨h.wax.add g.wax,h.wane.add g.wane,by rw [add_sub_add_comm,add_mul]; exact h.toll.add g.toll⟩
lemma Shelf.sum {S:Finset ι}{P Q:ι→ Ten V (U×α) r}{A:ι→ℝ}(h:∀ i∈ S,Shelf d w s (A i) δ (P i) (Q i)): Shelf d w s (∑ i∈ S,A i) δ (∑ i∈S,P i) (∑ i∈S,Q i):=⟨Cork.sum (fun i p=>(h i p).wax),Cork.sum (fun i p=>(h i p).wane),by rw [Finset.sum_mul,←Finset.sum_sub_distrib]; exact Cork.sum (fun i p=>(h i p).toll)⟩
lemma Shelf.gulp {P Q: Ten V (U×(α⊕β)) r}(h:Shelf d w s A δ P Q): Shelf d w s A δ (scoop P) (scoop Q):=⟨cork_scoop h.wax,cork_scoop h.wane,cork_scoop h.toll⟩
variable [NormedSpace ℝ V]
lemma Shelf.μ (h:Shelf d w s A δ P Q)(u:ℝ): Shelf d w s (|u| * A) δ (u•P) (u•Q):=⟨h.wax.μ u,h.wane.μ u,by rw [←smul_sub,mul_assoc]; exact h.toll.μ u⟩
lemma Shelf.mag (h:Shelf d w s A δ P Q)(p:twain B δ t σ):Shelf d w s (2*A*B) δ (t•P) (σ•Q):=by
   have ht:B*A≤2*A*B:= by have he:=mul_nonneg h.nn p.nn; nlinarith
   refine ⟨(h.wax.μ t).cost ((mul_le_mul_of_nonneg_right p.main h.nn).trans ht), (h.wane.μ σ).cost ((mul_le_mul_of_nonneg_right p.side h.nn).trans ht), ?_⟩
   rw [show t•P-σ•Q=(t-σ)•P+σ•(P-Q) by rw [sub_smul,smul_sub]; abel]; exact ((h.wax.μ _).add (h.toll.μ _)).cost ((add_le_add (mul_le_mul_of_nonneg_right p.gap h.nn) (mul_le_mul_of_nonneg_right p.side h.toll.1)).trans_eq (by ring))
-- lens. r=0 no issue here (stricter budget)
omit [NormedSpace ℝ V] in lemma Shelf.portal {P Q:Ten V (Cloth α) r}{b:Site L}(h:Shelf Bank.terrain (lift b) s A δ P Q)(u:t/L.val≤ s)(g:0≤t): Shelf Bank.terrain 0 t (A*Real.exp (8*t)) δ (turnTen (panel L α).symm P) (turnTen (panel L α).symm Q) := ⟨((h.shrink u).wax.cipher g),((h.shrink u).wane.cipher g),by rw [mul_right_comm]; exact ((h.shrink u).toll.cipher g)⟩
lemma tie_nn [Fintype α](h:0<s)(r:ℕ):0≤ tiePay α r s:=by
   cases r; unfold tiePay; positivity
   exact pow_nonneg (boardPay_nn (by positivity)) _
variable [Fintype α][CompleteSpace V]
lemma Shelf.prismLens {P Q:Gen V (Cloth α)}{M N:ropes Cover α β}(p:Shelf Bank.terrain 0 s A δ (P r) (Q r))(h:Ballast s B δ M N)(he:t<s)(ht:0≤t): Shelf Bank.terrain 0 t ((r+1:ℕ)*B^r*A*tiePay α r (s-t)) δ (prism M P r) (prism N Q r):= by
    have hw:=tie_nn (α:=α) (sub_pos.mpr he) r; have hb:=h.nn; have ha:=p.nn
    have hv : B^r*A*tiePay α r (s-t)≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show B^r≤(r+1:ℕ)*B^r from le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.le_add_left 1 _)) ha) hw
    refine ⟨(solo_cast h.oneP p.wax ht he).cost hv,(solo_cast h.otherP p.wane ht he).cost hv,(solo_gap h.otherP h.oneP h.between p.wane p.wax p.toll ht he).cost ?_⟩; exact le_of_eq (by cases r <;> push_cast <;> ring)
lemma Shelf.rimming {P Q:Gen V (Cloth α)}{M N:ropes Cover α α}(p:Shelf Bank.terrain 0 s A δ (P (r+2)) (Q (r+2)))(h:Ballast s B δ M N)(he:t<s)(ht:0≤t):Shelf Bank.terrain 0 t (2*B*A*fareV r*tiePay α 2 (s-t)) δ (rime M P r) (rime N Q r):=by
   have hw:= tie_nn (α:=α) (sub_pos.mpr he) 2; have hb:= h.nn; have ha:=p.nn; have hv:0≤fareV r:=by unfold fareV; positivity
   have hx : B*A*fareV r*tiePay α 2 (s-t)≤2*B*A*fareV r*tiePay α 2 (s-t):=by gcongr; linarith
   have hF:= solorain_bill h.oneP p.wax (ht.trans he.le); have hQ:=solorain_bill h.otherP p.wane (ht.trans he.le)
   refine ⟨(hF.meter he ht).cost hx,(hQ.meter he ht).cost hx,?_⟩; rw [rime,rime,← Peb.minus hF hQ (lt_of_le_of_lt ht he)]; apply ((solorain_gap h.oneP h.between (P:=P) (Q:=Q) p.toll p.wane (ht.trans he.le)).meter he ht).cost; exact le_of_eq (by unfold fareV; ring)
lemma Shelf.rondelTap {P Q:Gen ℝ (Cloth α)}{U T:Gen V (Cloth α)}{M N:ropes Cover α α}(p: PairA s A δ (P (l+1)) (Q (l+1)))(hx:Shelf Bank.terrain 0 s C δ (U (k+1)) (T (k+1)))(h:Ballast s B δ M N)(he:t<s)(ht:0≤t)(hh:l+k=r): Shelf Bank.terrain 0 t (3*pegPrice l k*B*A*C*tiePay α 2 (s-t)) δ (ruins (swivel (rill M P U r l k))) (ruins (swivel (rill N Q T r l k))):=by
    have hw:=tie_nn (α:=α) (sub_pos.mpr he) 2; have hb:= h.nn; have ha:=p.nn; have hc:=hx.nn; have hv:0≤pegPrice l k:= by unfold pegPrice; positivity
    have hp : pegPrice l k*B*A*C*tiePay α 2 (s-t) ≤ 3*pegPrice l k*B*A*C*tiePay α 2 (s-t):=by gcongr; linarith
    have hF:=soloswivel_cup (solorill_bill h.oneP p.pose hx.wax (ht.trans he.le) hh); have hG:=soloswivel_cup (solorill_bill h.otherP p.vale hx.wane (ht.trans he.le) hh)
    refine ⟨(hF.meter he ht).cost hp,(hG.meter he ht).cost hp,?_⟩; rw [←Peb.minus hF hG (lt_of_le_of_lt ht he)]; apply ((soloswivel_gap (solorill_gap h.otherP h.between p.pose hx.wax hx.toll p.vale p.visit (ht.trans he.le) hh)).meter he ht).cost; exact le_of_eq (by unfold pegPrice; ring)
end
end YM.WilsonCoeffUV.Soil
