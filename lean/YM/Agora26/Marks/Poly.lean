import YM.Push.GRID_APPROXIMATION.Bounds

/-! Simple finite price calculus for moments of multiple actual observables.
Difference slots remain designated under every expansion (no bound at volume cost
or assumption of convergence for the product with no error slots). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe.Vista26.Moment
open MeasureTheory Finset Function RG
open scoped Topology BigOperators Classical
variable {I X : Type} [DecidableEq I] [MeasurableSpace X] (μ:Measure X)[IsFiniteMeasure μ]
variable (A B : I → X → ℂ)(c : I → ℂ){ε M:ℝ}

def write (i:I)(t:Bool):X→ℂ:= if t then A i - B i else fun x=> A i x-c i
abbrev mix (b:I→Bool)(i:I):X→ℂ := if b i then A i else B i
def pick (F:I→X→ℂ)(q:Finset I) (x:X):ℂ := ∏ i∈q,F i x

lemma multi_error (hA:∀ i,Envelope (A i))(hB:∀ i,Envelope (B i))(hM:0≤ M)(hmm:∀ i, ‖c i‖≤M)(hε:0≤ε)
    (hw:∀ (q:Finset I)(t:I→Bool), (∃ i∈q,t i=true) → ‖∫ x,pick (fun i=>write A B c i (t i)) q x ∂μ‖ ≤ ε)
    (p:Finset I)(q:Finset I)(b t:I→Bool)(hd:Disjoint p q)(hh:∃ i∈q,t i=true) :
    ‖∫ x,pick (mix A B b) p x * pick (fun i=>write A B c i (t i)) q x ∂μ‖ ≤ ε*(2+M)^p.card:=by
  let F:=mix A B b
  let W (t:I→Bool) i:= write A B c i (t i)
  have hF (i):Envelope (F i):=by unfold F mix; split; exact hA _; exact hB _
  have hW(t)(i): Envelope (W t i):=by
     unfold W write; split; exact (hA i).subC (hB i); exact (hA i).subC (Envelope.constC _)
  change ‖∫ x,pick F p x*pick (W t) q x ∂μ‖ ≤ _
  induction p using Finset.induction_on generalizing q t with
  | empty=> simpa [pick] using hw q t hh
  | insert i p hi ih=>
     have hd':Disjoint p q:= Finset.disjoint_left.mpr (fun a ha=>Finset.disjoint_left.mp hd (mem_insert_of_mem ha))
     have hiq:i∉q:= Finset.disjoint_left.mp hd (mem_insert_self i p)
     have hi':Disjoint p (insert i q) := Finset.disjoint_right.mpr (fun a ha=> (mem_insert.mp ha).elim (fun hx=>hx ▸ hi) (fun hx=>Finset.disjoint_right.mp hd' hx))
     let G(x:X):=pick F p x*pick (W t) q x
     have hG:Envelope G:=(Envelope.prodC p F (fun i _=>hF i)).mulC (Envelope.prodC q _ (fun i _=>hW t i))
     let w (u:Bool): X→ℂ:= write A B c i u
     have hw₀(u):Envelope (fun x=> w u x * G x):=(hW (fun _=>u) i).mulC hG
     let val(u:Bool):ℂ:= ∫ x,w u x*G x ∂μ
     let D:= ε*(2+M)^p.card
     have hD:0 ≤ D:=by unfold D; positivity
     have cost(u): ‖val u‖ ≤ D:=by
        let t':= Function.update t i u
        have hh':∃ j∈insert i q,t' j=true:=by
           obtain ⟨l,hl,h⟩:=hh; exact ⟨l,mem_insert_of_mem hl,(Function.update_of_ne (ne_of_mem_of_not_mem hl hiq) ..).trans h⟩
        have he := ih (insert i q) t' hi' hh'
        suffices hf:(fun x=>pick F p x * pick (W t') (insert i q) x)=fun x=>w u x * G x by rw [hf] at he; exact he
        funext x; unfold G pick; rw [Finset.prod_insert hiq]
        have hV : (∏ j∈q,W t' j x)=∏ j∈q,W t j x:= Finset.prod_congr rfl fun j hj=> by unfold W t'; rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hiq) ..]
        rw [hV]; unfold W w t'; rw [Function.update_self,mul_left_comm]
     have costC: ‖∫ x, c i*G x ∂μ‖ ≤ M*D:=by
        rw [integral_const_mul,norm_mul]; exact mul_le_mul (hmm _) (ih q t hd' hh) (norm_nonneg _) hM
     have hI : Integrable (fun x=>w false x*G x+c i*G x) μ:= ((hw₀ false).integrableC μ).add (((Envelope.constC _).mulC hG).integrableC μ)
     have hP: ‖∫ x,w false x*G x+c i*G x ∂μ‖ ≤ D+M*D:=by rw [integral_add ((hw₀ false).integrableC μ) (((Envelope.constC _).mulC hG).integrableC μ)]; exact (norm_add_le ..).trans (add_le_add (cost false) costC)
     have hscale: ε*(2+M)^(insert i p).card=D*(2+M):=by rw [Finset.card_insert_of_notMem hi,pow_succ]; unfold D;ring
     by_cases hbi:b i=true
     · have h:(fun x=>pick F (insert i p) x*pick (W t) q x)=fun x=>w false x*G x+c i*G x:=by
          funext x; unfold G pick; rw [prod_insert hi,mul_assoc]; change F i x*_=_; rw [show F i=A i from if_pos hbi]; change _= (A i x-c i)*_+_; ring
       rw [show (∫ x, pick F (insert i p) x*pick (W t) q x ∂μ)=(∫ x,w false x*G x+c i*G x ∂μ) from congr_arg (fun f:X→ℂ=>∫ x,f x ∂μ) h,hscale]; exact hP.trans (by linarith)
     have h:(fun x=>pick F (insert i p) x*pick (W t) q x)=fun x=> (w false x*G x+c i*G x)-w true x*G x:= by
        funext x; unfold G pick; rw [prod_insert hi,mul_assoc]; change F i x*_=_; rw [show F i=B i from if_neg hbi]; change _= ( (A i x-c i)*_+_) -(A i x-B i x)*_;ring
     rw [show (∫ x, pick F (insert i p) x*pick (W t) q x ∂μ)=(∫ x,(w false x*G x+c i*G x)-w true x*G x ∂μ) from congr_arg (fun f:X→ℂ=>∫ x,f x ∂μ) h,hscale,integral_sub hI ((hw₀ true).integrableC μ)]
     exact ((norm_sub_le ..).trans (add_le_add hP (cost true))).trans_eq (by ring)

lemma replacement (hA:∀ i,Envelope (A i))(hB:∀ i,Envelope (B i))(hM:0≤ M)(hmm:∀ i, ‖c i‖≤M)(hε:0≤ε)
    (hw:∀ (q:Finset I)(t:I→Bool), (∃ i∈q,t i=true) → ‖∫ x,pick (fun i=>write A B c i (t i)) q x ∂μ‖ ≤ ε)
    (P:Finset I) : ‖(∫ x,pick A P x ∂μ)-(∫ x,pick B P x ∂μ)‖ ≤ P.card*ε*(2+M)^P.card :=by
   let U(q:Finset I):= mix A B (fun i=>decide (i∈q))
   have he(s)(k):Envelope (U s k):=by unfold U mix; split; exact hA _; exact hB _
   suffices h:∀ q:Finset I,q⊆P → ‖(∫ x,pick (U q) P x ∂μ) -(∫ x,pick B P x ∂μ)‖ ≤ q.card*ε*(2+M)^P.card by
      have hy : pick (U P) P=pick A P:=by funext x; unfold pick; apply prod_congr rfl; intro i hi; unfold U mix; simp only [decide_eq_true hi,↓reduceIte]
      exact hy ▸ h P (Subset.rfl)
   intro q; induction q using Finset.induction_on with
   | empty=> intros; have hx : U ∅ = B:=by funext i;simp [U,mix]
             rw [hx]; simp
   | insert i q hi ih=>
     intro hq; have hIP:= hq (mem_insert_self i _); let r:=P.erase i
     have hP:insert i r=P:=insert_erase hIP; have hr:i∉r:=Finset.notMem_erase i P
     have hq' : q⊆P:=by intro k hk; exact hq (mem_insert_of_mem hk)
     have hd:Disjoint r ({i}:Finset I):=Finset.disjoint_singleton_right.mpr hr
     let D:=ε*(2+M)^P.card; let u':Finset I→ℂ:=fun q=>∫ x,pick (U q) P x ∂μ
     have hE:= multi_error μ A B c hA hB hM hmm hε hw r {i} (fun j=>decide (j∈q)) (fun _=>true) hd ⟨i,mem_singleton_self _,rfl⟩
     let F(k:Finset I):=U k
     have h : (fun x=> pick (F (insert i q)) P x-pick (F q) P x)= fun x=>pick (F q) r x * pick (fun j=>write A B c j true) ({i}:Finset I) x:=by
        funext x; conv_lhs=> rw [← hP]; -- may rewrite r=P.erase i inside? `r` opaque
        unfold pick; rw [prod_insert hr,prod_insert hr]; simp only [prod_singleton]
        have hx:(∏ j∈r,F (insert i q) j x)=∏ j∈r,F q j x:= Finset.prod_congr rfl (fun j hj=>by
           have he:j≠i:=ne_of_mem_of_not_mem hj hr; simp [F,U,mix,he])
        rw [hx,show F (insert i q) i=A i from (by simp [F,U,mix]), show F q i=B i from (by simp [F,U,mix,hi])]; change _= _*(A i x-B i x); ring
     have hv:‖u' (insert i q)-u' q‖ ≤ D:=by
        have hg(s):Integrable (pick (U s) P) μ:=(Envelope.prodC P _ (fun i _=>he _ i)).integrableC μ
        unfold u'; rw [← integral_sub (hg _) (hg _)]; change ‖∫ x,(pick (F (insert i q)) P x - pick (F q) P x) ∂μ‖ ≤ _; rw [h]; refine hE.trans (mul_le_mul_of_nonneg_left ?_ hε); exact pow_le_pow_right₀ (by linarith) (by unfold r; exact card_le_card (erase_subset ..))
     let v:=∫ x,pick B P x ∂μ
     change ‖u' _-v‖ ≤ _; rw [show u' (insert i q)-v=(u' (insert i q)-u' q)+(u' q-v) by ring]; apply ((norm_add_le ..).trans (add_le_add hv (ih hq'))).trans_eq; rw [card_insert_of_notMem hi]; unfold D; push_cast; ring
end YM.OPE.Strobe.Vista26.Moment

