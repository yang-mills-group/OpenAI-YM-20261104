import YM.Frontier6.Bouquet.Core.Major

/-! Root recurrence with full test budgets at every vertex, before taking
 the regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R:Ensemble} (i:P)(d:Slot→ℕ)(s:ℝ)
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
    (x:Seats P)(H:Patron S P Y)(f:Full (fiber P))
lemma reconfirm (he:Payroll i.val K d s A T)(hh:Welcomes H x f)(hv:∀ w:i.val.Horizon d, Welcomes (key K H i x w) x (atBook i d s w f)) : marble K A T i x H f= -(∑ w:i.val.Horizon d,pollen K A T i x (key K H i x w) (atBook i d s w f)):=by
    obtain ⟨p,Q,h,hX,hp⟩ : ∃ (p:Pod)(Q:Ensemble)(h:Free (only p) Q), P=merge h ∧ i.val=p:= ⟨_, _, except_free P i.property, except_eq P i.property,rfl⟩
    subst P; obtain rfl:i=germL h (default:only p):=Subtype.ext hp; exact lifted K A T d s h default he hh hv
-- more linear regularizer accounting
lemma Appointed.same_sum {V:Type*}{A':V→ Patron S P Y} (u:Finset V)(he:∀ i∈u,Appointed K A T x (A' i) f) : Appointed K A T x (∑ i∈u,A' i) f:=by induction u using Finset.induction_on with
    | empty=>simp only [Finset.sum_empty]; exact Appointed.trivial (Y:=Y) K A T x f -- extra args? 
    | @insert i u hh ih=>rw [Finset.sum_insert hh]; exact (he _ (mem_insert_self ..)).sameplus (ih fun j hj=> he _ (mem_insert_of_mem hj))
lemma select_sames {V:Type*}{A': V→ Patron S P Y}(u:Finset V)(t:Finset (Down P))(he:∀ i∈u,Appointed K A T x (A' i) f): select K A T t x (∑ i∈u,A' i) f=∑ i∈u, select K A T t x (A' i) f:=by
    induction u using Finset.induction_on with
    | empty=> simp [select, branch,essay,ink_noop]
    | @insert i u hh ih=> have ht j (hj:j∈u):= he j (mem_insert_of_mem hj); rw [Finset.sum_insert hh, Finset.sum_insert hh, select_sameplus t (he _ (mem_insert_self ..)) (Appointed.same_sum K A T x f u ht),ih ht]
lemma rec_response (hm:Appointed K A T x (main K H i d x) f)(hD:∀ w:i.val.Horizon d, Appointed K A T x (key K H i x w) f) : pollen K A T i x H f= pollen K A T i x (main K H i d x) f+∑ w:i.val.Horizon d,pollen K A T i x (key K H i x w) f:=by
   unfold pollen; rw [← select_sames K A T x f Finset.univ _ (fun w _=> hD w),← select_sameplus _ hm (Appointed.same_sum K A T x f Finset.univ (fun w _=> hD w)),frontage K i d x H]
lemma select_subtract (u:Finset (Down P))(g:Full (fiber P))(he: Appointed K A T x H f)(hf:Appointed K A T x H g): select K A T u x H (f-g)= select K A T u x H f-select K A T u x H g:=by rw [sub_eq_add_neg f, ← neg_one_smul ℂ g, select_plus K A T x H _ _ u he (hf.scal _), select_scal, neg_one_smul ℂ,sub_eq_add_neg]
structure Partakes (K:Final C F S)(d:Slot→ℕ)(i:P)(s:ℝ)(x:Seats P)(H:Patron S P Y)(f:Full (fiber P)): Prop where
    willing : Welcomes H x f
    readyBack : Welcomes (main K H i d x) x f
    readyKey : ∀ w:i.val.Horizon d, Welcomes (key K H i x w) x f
    readyLedger : ∀ w:i.val.Horizon d, Welcomes (key K H i x w) x (atBook i d s w f)
lemma seesaw (ha:Payroll i.val K d s A T)(he:Partakes K d i s x H f): regulator K A T x H f= pollen K A T i x (main K H i d x) f+ ∑ w:i.val.Horizon d,pollen K A T i x (key K H i x w) (overBook i d s w f):=by
    rw [splitting K A T i,reconfirm K A T i d s x H f ha he.willing he.readyLedger];
    have hz(w:i.val.Horizon d): Appointed K A T x (key K H i x w) f:= Welcomes.appointed K A T _ _ _ (he.readyKey w)
    have hy(w:i.val.Horizon d): pollen K A T i x (key K H i x w) (overBook i d s w f)=pollen K A T i x (key K H i x w) f - pollen K A T i x (key K H i x w) (atBook i d s w f):= select_subtract K A T x _ f (proper P i.val) _ (hz w) (Welcomes.appointed K A T _ _ _ (he.readyLedger w))
    rw [rec_response K A T i d x H f (Welcomes.appointed K A T _ _ _ he.readyBack) hz]; simp_rw [hy,sum_sub_distrib]; abel
end YM.Frontier6.Bouquet
