import YM.WilsonCoeffUV.Winding.Vacuum
/-!
# Native rooted winding error. Nonperiodic fibers above moving degrees
remain **uncanonical** outside 4d<n; no claim to track an unbounded choice
of lifted origin across an alias in a mixed join. Supply folded torus
moments on the whole output.
-/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel.Mark Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type}{G:Gauge}{D:ι→ℕ}{i j k r e a:ℕ}{s A B t q :ℝ}
variable {J I S:Finset ι}{p:ι→Cover}{x:ι}
lemma cardFire {v:dock Cover α r}{y:dock Cover β k}(h:x ∈ J)(i): Bank.terrain.gap (p x) (y i).1≤billow Bank.terrain p J v y:= leg_le Bank.terrain (visitN p J v y) (.inl (.inl ⟨x,h⟩)) (.inr i)
lemma studyW {d:Bank.Distance U}{p:ι→U}{x:ι}{v:dock U α r}{y:dock U β k}(h:x∈J): brims d (p x) v y ≤ billow d p J v y :=by
   apply reachL; rintro (i|i)
   · refine Fin.cases ⟨.inl (.inl ⟨x,h⟩),rfl⟩ (fun i=>⟨.inl (.inr i),rfl⟩) i
   exact ⟨.inr i,rfl⟩
lemma foyer_fold (p:ι→Cover)(S:Finset ι)(x:dock Cover β r): foyer (wrap n ∘ p) S (slideC n x)=wrap n ∘ (foyer p S x):= funext fun i=>by cases i<;>rfl
lemma exact_syn (p:ι→Cover)(S:Finset ι)(x:dock Cover β r)(v:4*Syn Bank.terrain p S x<n.val): Syn (tor n) (wrap n ∘ p) S (slideC n x)=Syn Bank.terrain p S x:=by unfold Syn; rw [foyer_fold]; exact exact_course v
lemma linger (p:ι→Cover)(a:x∈J)(y:dock Cover α k)(z:dock Cover β r)(h:4*Syn Bank.terrain p J y < n.val)(q:unfoldAt (p x) (slideC n z)=z):
   billow Bank.terrain p J y z ≤ 2*billow (tor n) (wrap n ∘ p) J (slideC n y) (slideC n z) :=by
    apply league_cash _ (a:=p x); rintro (i|i)
    · let b:=foyer p J y i; have he : Bank.terrain.gap (p x) b≤ Syn Bank.terrain p J y:=leg_le Bank.terrain (foyer p J y) (.inl ⟨x,a⟩) i
      rw [← exact_syn p J y h] at he; exact he.trans (synret ..)
    have ht:= near_change (p x) (slideC n z) i; rw [q] at ht; exact ht.le.trans (leg_le (tor n) (visitN (wrap n∘ p) J (slideC n y) (slideC n z)) (.inl (.inl ⟨x,a⟩)) (.inr i))

variable [NormedAddCommGroup V]
structure MarkU (p:ι→Cover)(J:Finset ι)(Q: Ten V (Co n α) r)(F:Ten V (Cloth α) r)(s A:ℝ):Prop where
    access : Wig Bank.terrain p s A J F
    bill : Wig (tor n) (wrap n ∘ p) s A J Q
    gulf : Wound Q F n (slideC n) (Syn Bank.terrain p J) s A
variable {P Q:Ten V (Co n α) r}{F Z:Ten V (Cloth α) r}
lemma MarkU.more (h:MarkU p J P F s A)(v:A≤ B):MarkU p J P F s B:=⟨h.access.more v,h.bill.more v,h.gulf.more v⟩
lemma MarkU.mono (h:MarkU p J P F s A)(v:t≤s):MarkU p J P F t A:=⟨h.access.shave v,h.bill.shave v,h.gulf.mono v⟩
lemma MarkU.μ [NormedSpace ℝ V](h:MarkU p J P F s A)(v:ℝ):MarkU p J (v•P) (v•F) s (‖v‖*A):=⟨h.access.μ _,h.bill.μ _,h.gulf.μ _⟩
lemma MarkU.zero:MarkU p J (0:Ten V (Co n α) r) 0 s 0:=⟨Wig.zero,Wig.zero,Wound.zero⟩
lemma MarkU.add (h:MarkU p J P F s A)(v:MarkU p J Q Z s B): MarkU p J (P+Q) (F+Z) s (A+B):=⟨h.access.plus v.access,h.bill.plus v.bill,h.gulf.add v.gulf⟩
lemma MarkU.sum {g:Finset X}{P:X→Ten V (Co n α) r}{F:X→Ten V (Cloth α) r}{Z:X→ℝ}(h:∀ i∈g,MarkU p J (P i) (F i) s (Z i)): MarkU p J (∑ i∈ g,P i) (∑ i∈g,F i) s (∑ i∈g,Z i):=by
   classical
   induction g using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact MarkU.zero
   | @insert i g hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
structure MarkC (p:ι→Cover)(J:Finset ι)(Q:canal (Site n) α β V k r)(F:canal Cover α β V k r)(s A:ℝ):Prop where
    access : Grapple Bank.terrain p s A J F
    bill : Grapple (tor n) (wrap n ∘ p) s A J Q
    gulf : Wound (uncurry Q) (uncurry F) n (Prod.map (slideC n) (slideC n)) (uncurry (billow Bank.terrain p J)) s A

lemma campY [Fintype α]{F:canal (Site n) α β V k r}{p:ι→Site n}(h:Grapple (tor n) p s A J F)(v:x∈J)(q:t<s)(u:0≤t):
    Wig (tor n) p t (A*tiePay α k (s-t)) J (refuge F) :=by
    cases k with
    | zero=> refine ⟨by rw [tiePay,pow_zero,mul_one]; exact h.1, fun i=>?_⟩; rw [refuge,Fintype.sum_unique,tiePay,pow_zero,mul_one]; apply (h.2 _ _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (neg_le_neg q.le) (by positivity)).trans (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (synret ..)) (neg_nonpos.mpr u)))) h.1)
    | succ k=>
        refine ⟨mul_nonneg h.1 (tie_non (sub_pos.mpr q)),fun z=>?_⟩; let D:=Syn (tor n) p J z; let a:=t; let E:=(s-t)/(k+1:ℕ); have he:0<E:= div_pos (sub_pos.mpr q) (by positivity)
        have hh(i:dock (Site n) α (k+1)): ‖F z i‖ ≤ A*Real.exp (-t*D)*sail E (tor n) (p x) i:=by
            apply (h.2 z i).trans; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (sail_cut (synret _ p J z i) u q (by omega) (p x) _ (fun j=>leg_le (tor n) (visitN p J z i) (.inl (.inl ⟨_,v⟩)) (.inr j))) h.1
        change ‖∑ i,F z i‖ ≤_; apply (norm_sum_le ..).trans; apply le_trans (Finset.sum_le_sum (fun i _=> hh i)); rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (train_native he _ _) (mul_nonneg h.1 (by positivity))).trans_eq (mul_right_comm ..)

variable [Fintype α][CompleteSpace V]
lemma MarkC.camp {F:canal Cover α β V k r}{Q:canal (Site n) α β V k r}(h:MarkC p J Q F s A)(v:J.Nonempty)(q:0<s): MarkU p J (refuge Q) (ruins F) (s/32) (priceM α k s*A):=by
    obtain ⟨x,hx⟩:= v; classical
    have he: s/32<s:=by linarith
    have hb:0≤s/32:=by positivity
    let b:= boardPay α (Winding.tailC k (s/4))^k; let c:=tiePay α k (s-s/32)
    have ha:=h.access.1; have hv:0≤ b:=pow_nonneg (boardPay_nn (tail_good _ (by positivity))) _; have hg: 0≤ c:=tie_non (sub_pos.mpr he)
    have hh:A*tiePay α k (s-s/32)≤ priceM α k s*A:=by change A*c≤(c+2*b)*A; nlinarith
    refine ⟨(Wrest h.access he hb ⟨_,hx⟩).more hh,(campY h.bill hx he hb).more hh,⟨(mul_nonneg ha hg).trans hh,fun z u=>?_⟩⟩
    have hP:Peb Bank.terrain (p x) s A F:=⟨ha,fun i j=> (h.access.2 i j).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (studyW hx)) (neg_nonpos.mpr q.le))) ha)⟩
    unfold refuge ruins
    apply le_trans (broker (p x) (F z) (Q (slideC n z)) (billow Bank.terrain p J z) q ha (hP.cache q le_rfl z).2.1.of_norm ?_); · apply mul_le_mul_of_nonneg_right _ (catch_hot ..); change (A+A)*b≤(c+2*b)*A; nlinarith
    intro W y _; refine ⟨cardFire hx, fun v=>?_, (norm_sub_le ..).trans ((add_le_add ?_ ((h.access.2 z y).trans (mul_le_mul_of_nonneg_left (catch_width (by linarith) _) ha))).trans_eq (add_mul ..).symm)⟩
    · unfold W; rw [if_pos (unfoldReady (fun i=> vn (cardFire (p:=p) hx i) v))]; exact h.gulf.local_w (z,y) v
    unfold W; split
    next v=> exact (h.bill.2 ..).trans (mul_le_mul_of_nonneg_left (spliceHit s _ _ (linger p hx z y u v) q.le) ha)
    rw [norm_zero]; exact mul_nonneg ha (catch_hot ..)
end YM.WilsonCoeffUV.Winding
