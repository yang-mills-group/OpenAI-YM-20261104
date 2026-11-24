import YM.WilsonCoeffUV.Marked.Step.Evaluation
/-!
# Multi-root native width and rescaling

`Wig`: exponential of full span, pointwise at every marker, used through
arbitrarily many steps. Don't claim same-width tree ℓ1 merging. At render
scale spend final ε width for outgoing rooted path weights (see endpoint).
 -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric
open scoped Topology BigOperators
variable {c f:Side}{ι α U β V t:Type}{J K I S T:Finset ι}{z:Finset U}{D k:ι→ℕ}{i j e r h N n m l:ℕ}{G:Gauge}{σ τ u A B C:ℝ}

abbrev foyer (p:ι→U)(S:Finset ι)(x:dock U α r) : S ⊕ Fin r → U:= Sum.elim (fun i:S=>p i.val) (Prod.fst ∘ x)
abbrev visitN (p:ι→U)(S:Finset ι)(x:dock U α r)(y:dock U β i): (S⊕ Fin r) ⊕ Fin i → U:= Sum.elim (foyer p S x) (Prod.fst ∘ y)
def Syn (d:Bank.Distance U)(p:ι→U)(S:Finset ι)(x:dock U α r):ℕ:= league d (foyer p S x)
def billow (d:Bank.Distance U)(p:ι→U)(S:Finset ι)(x:dock U α r)(y:dock U β i):ℕ:= league d (visitN p S x y)
section
variable [NormedAddCommGroup V]{p:ι→U} {d:Bank.Distance U}
def Wig (d:Bank.Distance U)(p:ι→U)(σ A:ℝ)(S:Finset ι)(X:Ten V (U×α) i):Prop:=0≤A ∧ ∀ x,‖X x‖≤ A*Real.exp (-σ*Syn d p S x)
variable {P Q:Ten V (U×α) i}
lemma Wig.more (w: Wig d p σ A S P)(h:A ≤ B): Wig d p σ B S P:=⟨w.1.trans h,fun x=>(w.2 x).trans (mul_le_mul_of_nonneg_right h (by positivity))⟩
lemma Wig.shave (w: Wig d p σ A S P)(h:τ ≤ σ): Wig d p τ A S P:=⟨w.1,fun x=>(w.2 x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg h) (by positivity))) w.1)⟩
lemma Wig.zero : Wig d p σ 0 S (0:Ten V (U×α) i) :=by simp [Wig]
lemma Wig.plus (w:Wig d p σ A S P)(u:Wig d p σ B S Q): Wig d p σ (A+B) S (P+Q):=⟨add_nonneg w.1 u.1,fun x=>(norm_add_le ..).trans ((add_le_add (w.2 x) (u.2 x)).trans_eq (by ring))⟩
lemma Wig.μ [NormedSpace ℝ V](w:Wig d p σ A S P)(a:ℝ): Wig d p σ (‖a‖*A) S (a•P):=⟨mul_nonneg (norm_nonneg _) w.1, fun x=> (norm_smul a (P x)).le.trans ((mul_le_mul_of_nonneg_left (w.2 x) (norm_nonneg _)).trans_eq (by ring))⟩
lemma Wig.sum {P:t→Ten V (U×α) i}{Z:Finset t}{w:t→ℝ}(h:∀ i∈Z,Wig d p σ (w i) S (P i)): Wig d p σ (∑ i∈Z,w i) S (∑ i∈Z,P i):=by
    classical
    induction Z using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Wig.zero
    | @insert i Z h' ih=>
        rw [Finset.sum_insert h',Finset.sum_insert h']; exact (h _ (Finset.mem_insert_self ..)).plus (ih (fun i hi=>h _ (Finset.mem_insert_of_mem hi)))
lemma Wig.to_cork (w: Wig d p σ A S P)(v:0≤σ){u}(h:u∈S) : Cork d (p u) σ A P:=by
    refine ⟨w.1,fun x=> (w.2 x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (show tread d (p u) x≤ Syn d p S x from ?_)) (neg_nonpos.mpr v))) w.1)⟩
    refine league_le d _ fun a b=> ?_; let f : Fin (i+1)→ S⊕ Fin i := Fin.cases (.inl ⟨u,h⟩) Sum.inr
    have ht j:stud (p u) x j=foyer p S x (f j):=Fin.cases rfl (fun _=>rfl) j
    rw [ht,ht]; exact leg_le ..

def Grapple (d:Bank.Distance U)(p:ι→U)(σ A:ℝ)(S:Finset ι)(F:canal U α β V i j): Prop:=0≤ A ∧∀ x y, ‖F x y‖≤ A*Real.exp (-σ*billow d p S x y)
omit [NormedAddCommGroup V] in
lemma synret (d:Bank.Distance U)(p:ι→U)(S:Finset ι)(x:dock U α i)(y:dock U β j): Syn d p S x ≤ billow d p S x y:= league_le d _ fun i j=> leg_le d (visitN p S x y) (Sum.inl i) (Sum.inl j)
lemma Grapple.spin [NormedSpace ℝ V]{F:canal U α α V 2 i}(w:Grapple d p σ A S F): Grapple d p σ A S (swivel F):= by
    let I:= Equiv.Perm (Fin i); let C:ℝ:=Fintype.card I; have hc:0<C:=by unfold C; positivity
    refine ⟨w.1,fun x y=>?_⟩
    let Z:=A*Real.exp (-σ*billow d p S x y); let g (i:I) := F (x∘ i) y; have h (i:I): ‖g i‖≤ Z:=by
       let W:= ((Equiv.refl S).sumCongr i).sumCongr (Equiv.refl (Fin 2)); have he: visitN p S (x ∘ i) y = visitN p S x y ∘ W:= funext fun v=>by cases v with | inr i=> rfl | inl i=> cases i<;>rfl
       refine (w.2 (x ∘ i) y).trans_eq ?_; unfold Z billow; rw [he,league_equiv]
    change ‖C⁻¹ • ((∑ i:I,(fun x y=> F (x ∘i) y)) x y)‖≤ Z; simp_rw [Finset.sum_apply]; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> h i))) (by positivity)).trans; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hc.ne']
end
-- array packing by arbitrary Copy. wAddr labels S passive; root proof
lemma foreStretch (P:Patch)(w:ι→Cover)(s:ι→Site P.L)(S:Finset ι)(x:dock Cover (Co P.L β) r): P.L.val*Syn Bank.terrain w S x ≤ Syn Bank.terrain (fun i=> P.L.val • w i + lift (s i)) S (panel P.L β ∘ x)+8*P.L.val:=by
    let u : ↑S⊕ Fin r → Cloth (Co P.L Unit) := Sum.elim (fun i:S=> (w i.val,s i.val,())) (fun i:Fin r=> ((x i).1,(x i).2.1,())); let v:= Fintype.equivFin (↑S⊕ Fin r); let p:=cover_pack (L:=P.L) (u ∘ v.symm)
    have ha : foyer w S x= Prod.fst ∘ u:= funext fun i=>by cases i<;>rfl
    have ht : foyer (fun i=> P.L.val • w i+lift (s i)) S (panel P.L β ∘ x)=Prod.fst ∘(panel P.L Unit ∘ u):= funext fun i=>by cases i<;>rfl
    unfold Syn; rw [ha, ht,← league_equiv Bank.terrain _ v.symm,← league_equiv Bank.terrain (Prod.fst ∘ (panel P.L Unit ∘ u)) v.symm]; exact p
lemma plankB [NormedAddCommGroup V](P:Patch)(w:ι→Cover)(s:ι→Site P.L)(S:Finset ι)(x: Ten V (Cloth β) r)(h:Wig Bank.terrain (fun i=> P.L.val • w i+ lift (s i)) (σ/P.L.val) A S x)(v:0≤σ): Wig Bank.terrain w σ (A*Real.exp (8*σ)) S (turnTen (panel P.L β).symm x):= by
   refine ⟨mul_nonneg h.1 (by positivity),fun y=> (h.2 (panel P.L β ∘ y)).trans ?_⟩; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (spentL P.L (foreStretch P w s S y) v) h.1

lemma Wrest [Fintype α][NormedAddCommGroup V]{F:canal Cover α β V i j}{p:ι→Cover}{S:Finset ι}(h: Grapple Bank.terrain p σ A S F)(v:τ<σ)(u:0≤τ)(q:S.Nonempty): Wig Bank.terrain p τ (A*tiePay α i (σ-τ)) S (ruins F):=by
    refine ⟨mul_nonneg h.1 ?_,fun x=>?_⟩
    · cases i with
      | zero=> rw [tiePay,pow_zero]; exact zero_le_one
      | succ i=> exact pow_nonneg (boardPay_nn (div_pos (sub_pos.mpr v) (by positivity))) _
    by_cases a:i=0
    · subst i; simp only [ruins,tsum_fintype,Fintype.sum_unique, tiePay,pow_zero,mul_one]; refine (h.2 x _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (neg_le_neg v.le) (by positivity)).trans (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (synret _ _ S x _)) (neg_nonpos.mpr u)))) h.1)
    let n:= Syn Bank.terrain p S x; let c:=(σ-τ)/i; have hc: 0<c:=div_pos (sub_pos.mpr v) (by exact_mod_cast Nat.pos_of_ne_zero a)
    obtain ⟨k,hk⟩:= q; let w:= p k; let g:=A*Real.exp (-τ*n); have hg:0≤g:= mul_nonneg h.1 (by positivity); have H:SumBudget (fun y=>‖F x y‖) (g*tiePay α i (σ-τ)):= by
        refine budget_minor (cap_scale (train_pay hc w i) hg) (fun _=>norm_nonneg _) (fun y=>?_ )
        apply (h.2 x y).trans
        change _≤A*Real.exp (-τ*_) * sail _ _ _ _; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (sail_cut (synret Bank.terrain p S x y) u v (Nat.pos_of_ne_zero a) (p k) _ (fun i=> leg_le Bank.terrain (visitN p S x y) (.inl (.inl ⟨k,hk⟩)) (.inr i))) h.1
    exact (norm_tsum_le_tsum_norm H.2.1).trans (H.2.2.trans_eq (mul_right_comm ..))
end YM.WilsonCoeffUV.Wheel.Mark
