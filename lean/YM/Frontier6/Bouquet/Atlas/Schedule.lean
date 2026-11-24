import YM.Frontier6.Bouquet.Audit.Journeys

/-! Dimension bills for a single burst. Compare the same Leg* widths.
 Even singleton leaf child keeps its width until the parent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Audit Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q:Ensemble}{i:P}
lemma ledgerD (P: Ensemble)(d:Slot→ℕ): ∑ p:P,p.val.arityD d=∑ i∈P.Along,d i :=by rw [Along,sum_biUnion P.pairwise]; exact Finset.sum_coe_sort P.choose (fun p=>p.arityD d)
lemma ledgerF (P:Ensemble):∑ p:P,dim (normal p.val)=dim (fiber P):=by
   have he:=fiber_dim P; have hh:=rank_split P;
   calc
      _ = _ := rfl
      _ = dim (fiber P) := by
         have ht:∑ p:P,(4+dim (normal p.val))=4*P.Along.card:=by rw [← hh,Finset.mul_sum]; refine sum_congr rfl (fun p _=>?_); rw [normal_rank]; have he:= p.val.card_pos; omega
         rw [Finset.sum_add_distrib, Finset.sum_const, card_univ, Fintype.card_coe,nsmul_eq_mul] at ht; simp only [Nat.cast_id] at ht; omega
lemma ledger_sum (P:Ensemble)(d:Slot→ℕ):∑ p:P, Audit.difference p.val d=(dim (fiber P):ℝ) - ((∑ i∈ P.Along,d i: ℕ):ℝ):=by unfold Audit.difference; rw [Finset.sum_sub_distrib,← Nat.cast_sum,← Nat.cast_sum,ledgerD,ledgerF]
section
variable (h:Burst i Q) (d:Slot→ℕ)
include h
lemma total_difference : ((∑ j:Q, Audit.difference j.val d)+(dim (Margin P Q):ℝ))=∑ j:P,Audit.difference j.val d:=by simp_rw [ledger_sum,ref_slots h.le]; have hz: (dim (fiber Q):ℝ)+(dim (Margin P Q):ℝ)=dim (fiber P):=(by exact_mod_cast (attendance (plan_sub h.le)|>.dim_eq)); linarith only [hz] -- line colon
lemma registry : (∑ j∈ dialogues h.le i, Audit.difference j.val d)+(dim (Margin P Q):ℝ)=Audit.difference i.val d:=by
   let f(p:P):=Audit.difference p.val d; let g(p:Q):= Audit.difference p.val d; let F(p:P):=∑ j∈dialogues h.le p,g j
   have hh:(∑ p,F p)=∑ j:Q,g j:=Finset.sum_fiberwise Finset.univ (assign h.le) g; let D:= Finset.univ.erase i; have hr:(∑ p∈D,F p)=∑ p∈D,f p:= by refine Finset.sum_congr rfl (fun j hj=> ?_); unfold F; rw [h.bedrooms (Finset.ne_of_mem_erase hj),Finset.sum_singleton]; rfl
   have he:=total_difference h d; change (∑ j:Q,g j)+_=∑ j:P,f j at he; rw [← hh,← add_sum_erase Finset.univ F (mem_univ i),← add_sum_erase Finset.univ f (mem_univ i),hr] at he; change F i+_=f i; linarith only [he]
lemma star_bills (r:P→ℝ)(hp:∀ i:P,0<r i): stars d P r= stars d Q (r ∘ assign h.le)*(r i) ^ dim (Margin P Q):=by
    let f(j:P):=(r j)^(Audit.difference j.val d); let g(j:Q):=(r (assign h.le j))^(Audit.difference j.val d);
    let F(p:P):=∏ j∈ dialogues h.le p,g j; have ht(p)(hv:p≠i):F p=f p:=by unfold F; rw [h.bedrooms hv, Finset.prod_singleton]; unfold g f; rw [h.remembered hv]; rfl
    have hy:(∏ p,F p)=∏ j,g j:= Finset.prod_fiberwise Finset.univ (assign h.le) g; have hr :f i= F i*(r i)^dim (Margin P Q):=by unfold f; rw [← registry h d, Real.rpow_add (hp i),Real.rpow_natCast, Real.rpow_sum_of_pos (hp i)]; unfold F; congr 1; refine prod_congr rfl (fun p hx=>?_); unfold g; rw [(members ..).mp hx] -- rpow_sum?
    change (∏ p, f p)= (∏ p,g p) * (r i)^_; rw [← hy,←mul_prod_erase Finset.univ F (mem_univ i),← mul_prod_erase Finset.univ f (mem_univ i), Finset.prod_congr (s₁:=Finset.univ.erase i) (f:=f) rfl (fun j hj=> (ht j (Finset.ne_of_mem_erase hj)).symm),hr]; ring
end
end YM.Frontier6.Bouquet.Atelier
