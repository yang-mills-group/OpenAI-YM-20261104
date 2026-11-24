import YM.Pert.Attach.Links

/-! The forced cap of exact mergers. Withdraw one forced fugacity before charging the forest. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Attach
open Function Lattice Wilson MeasureTheory RG Finset Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {A:Activities G n} {X:Corrections G n} {R:Activities G n}
    {P:BudgetPoint}
local notation "B!" => attach A X P.threshold R
set_option quotPrecheck false

lemma forced (HA:A.ForcedFamily P) (H:Prepared P.threshold X) : (B!).ForcedFamily P := by
   have hT (i:ℕ) (x:Site n→G.El) (U) : ((B!).forced i).extraTest (Lattice.gauge x U) ↔ ((B!).forced i).extraTest U := by
      change (∀ j∈(parts A X i).toLeft, _) ↔ _; simp_rw [HA.symtest]; rfl
   have hM i : MeasurableSet {U | ((B!).forced i).extraTest U} := by
      change MeasurableSet {U | ∀ j∈(parts A X i).toLeft, _}
      simp only [Set.setOf_forall]
      exact MeasurableSet.biInter (Set.to_countable _) fun j _=>HA.meas_test j
   have hD (i:ℕ) : UsesFinal P.threshold ((B!).forced i).support ((B!).forced i).extraTest := by
      show UsesFinal P.threshold ((B!).forced i).support _ ; intro U V ha hf
      exact propext ⟨fun k j hj=>(Work.H03.reads_larger (sub_cover_old A X hj) (HA.reads_test _) _ _ ha hf) ▸ k j hj,
        fun k j hj=>(Work.H03.reads_larger (sub_cover_old A X hj) (HA.reads_test _) _ _ ha hf).symm ▸ k j hj ⟩
   refine ⟨fun i g U=>?_,hT,fun i=>?_,hM,fun i=>?_,hD,fun i U hi=>?_⟩
   · let T := page A X i
     have hu := Work.H03.eligible_gauge P.threshold T g U (hT i g U)
     change entry A X _ _ _ = entry A X _ _ U; unfold entry
     dsimp only [T] at hu; simp only [hu]; split_ifs
     · refine prod_congr rfl fun l _=>?_
       cases l with
       | inl j => exact HA.sym _ _ _
       | inr j => exact H.sym _ _ _
     rfl
   · change Measurable fun U=>entry A X _ _ U; unfold entry
     refine Measurable.ite (Work.H03.eligible_measurable _ _ (hM _)) (Finset.measurable_fun_prod (parts A X i) fun j _ =>?_) measurable_const
     cases j with
     | inl j=> exact HA.meas _
     | inr j=> exact H.meas _
   · intro U V ha hf
     have ht := Work.H03.eligible_reads _ _ (hD i) _ _ ha hf
     change entry _ _ _ _ _ = entry _ _ _ _ _; unfold entry
     change (if ((B!).forced i).eligible _ U then _ else _)=(if ((B!).forced i).eligible _ V then _ else _)
     rw [ht]; split_ifs
     · refine prod_congr rfl fun l hl=>?_
       have hx : UsesFinal P.threshold (X.area A l) (fun U=>weight A X U l) :=
         l.rec (fun j=>HA.reads _) (fun j=>H.deps _)
       exact Work.H03.reads_larger (q:=((B!).forced i).support) (fun _ hk=>mem_biUnion.mpr ⟨l,hl,hk⟩) hx _ _ ha hf
     rfl
   by_contra! he; exact hi (if_neg he)

structure Prices (A : Activities G n) (X:Corrections G n) (P:BudgetPoint) (q γ : ℝ) : Prop where
   margin : 0≤γ ∧ 1≤q ∧ ((P.B+P.B+1:ℕ):ℝ)^4*γ ≤ 1
   toll : ∃ f : Old→ℝ, (∀ i U, q*‖A.K i U‖ ≤ f (.inl i)) ∧ (∀ j U, ‖X.value j U‖ ≤ f (.inr j)) ∧
       Ac.Hit (X.area A) P.B f (P.supportExponent+1) γ

lemma bound (A:Activities G n) (X:Corrections G n) (R:Activities G n) (P:BudgetPoint) {q γ : ℝ}
    (h:Prices A X P q γ) : (attach A X P.threshold R).KBound P ((Real.exp γ-1)/q) := by
   obtain ⟨f,hf,hg,hb⟩:=h.toll
   have h0 (j:Old) : 0 ≤ f j := j.rec (fun i=>(mul_nonneg (zero_le_one.trans h.margin.2.1) (norm_nonneg _)).trans (hf _ 1))
     (fun k=>(norm_nonneg _).trans (hg _ 1))
   have h1 (U:Config G n) (j:Old) : ‖weight A X U j‖ ≤ f j :=
     j.rec (fun i=>(le_mul_of_one_le_left (norm_nonneg _) h.margin.2.1).trans (hf _ U)) (fun i=>hg _ U)
   let b i := (∏ j∈parts A X i,f j)/q
   refine ⟨b,fun i => ⟨by apply div_nonneg (Finset.prod_nonneg fun _ _ =>h0 _) (zero_le_one.trans h.margin.2.1),fun U=>?_⟩,fun x=>?_⟩
   · change ‖entry _ _ _ _ U‖ ≤ b i; unfold entry; split_ifs
     · obtain ⟨j,hj⟩:= (decoding A X i).2.2.1; rw [norm_prod]
       unfold b; refine (le_div_iff₀' (zero_lt_one.trans_le h.margin.2.1)).2 ?_
       rw [← mul_prod_erase (parts A X i) (fun l => ‖weight A X U l‖) (mem_toLeft.mp hj), ← mul_prod_erase (parts A X i) f (mem_toLeft.mp hj), ←mul_assoc]
       apply mul_le_mul (hf j U) (prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>h1 ..)) (prod_nonneg fun _ _=>norm_nonneg _) (h0 _)
     rw [norm_zero]; exact div_nonneg (prod_nonneg fun _ _=>h0 _) (zero_le_one.trans h.margin.2.1)
   have he := budget_scale (inv_nonneg.mpr (zero_le_one.trans h.margin.2.1)) <| budget_pull (parts A X) (parts_inj A X) <|
      Ac.forest (X.area A) P.B P.exponent_pos.le h0 hb h.margin.2.2 h.margin.1 x
   rw [div_eq_inv_mul]; convert he using 2 with i
   unfold Ac.roots; rw [ite_and,if_pos (show Ac.Spark (X.area A) (parts A X i) from (decoding A X i).2.1)]
   change (if x∈full _ _ _ then _ else _) = _; split_ifs
   · unfold BudgetPoint.mass b; dsimp [attach,page,full]; ring
   · contradiction
   · contradiction
   rw [mul_zero]
end YM.Pert.Attach
