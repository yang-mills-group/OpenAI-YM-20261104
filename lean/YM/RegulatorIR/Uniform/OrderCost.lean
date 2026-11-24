import YM.RegulatorIR.Uniform.Periodic
import YM.RegulatorIR.Diagram.Linear

/-! Uniform coefficient bills starting on the cover only. At any demand,
every larger moment for this lemma is a separate finite demand. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function Budget Diagram Budget.Layer Budget.Packet Budget.Tuple Budget.Tariff Finset
open scoped Topology BigOperators Classical ENNReal
variable {W:Type}{I J:W→Type}{L:Meter W}
namespace Workday
variable {K : (w:W)→Layer (I w) (I w)} {A : (w:W)→Tariff (I w)} {u b:ℕ}
lemma with_heat {T:(w:W)→ Ranked (I w)} (h:Workday L A (fun w=>T w (u+2)))(hh:Beam L A K): Workday L A (fun w=>heating (K w) (T w) u):= ((h.loop_budget hh).robust).csmul _
lemma with_match {T S:(w:W)→ Ranked (I w)} (r p q:ℕ) (hh: Beam L A K) (h: Workday L A (fun w=>T w (p+1)))(hs:Workday L A (fun w=> S w (q+1))): Workday L A (fun w=>matchTwo (K w) (T w) (S w) r (p,q)):=by
 by_cases he : p+q=r
 · subst r; simp only [matchTwo, ↓reduceDIte]; exact ((h.knot_budget hs hh).robust).csmul _
 simp_rw [matchTwo,dif_neg he]; exact zeroQ
lemma hot {e:ℕ}{V:(w:W)→Orders (I w)}(h:∀ p≤e,∀ r,Workday L A (fun w=>V w p r))(H:Beam L A K)(flag:Bool) (k p r:ℕ)(hh:p≤e) :
     Workday L A (fun w=> logHeat (K w) (V w) flag k p r):= by
 induction k using Nat.strong_induction_on generalizing p r with
 | _ k ih=>
    cases k with
    | zero =>
      simp_rw [logHeat_first]; by_cases ht:r=0∧ flag=false
      · simp_rw [if_pos ht]; exact zeroQ
      simp_rw [if_neg ht]; exact h p hh r
    | succ k =>
      simp_rw [logHeat_next]; by_cases ht:r=0 ∧ flag=false
      · simp_rw [if_pos ht];exact zeroQ
      simp_rw [if_neg ht]; apply csmul ; apply Workday.add (with_heat (ih k (by omega) _ _ hh) H); apply csmul
      unfold drift carry force; apply Workday.sum
      rintro ⟨i,j⟩ hz; have he:= Finset.mem_antidiagonal.mp hz; change i+j=k at he
      apply Workday.sum
      rintro ⟨t,u⟩ hq; have hf:= Finset.mem_antidiagonal.mp hq; change t+u=p at hf
      apply Workday.sum; rintro ⟨s,v⟩ _
      exact Workday.with_match r s v H (ih i (by omega) t _ (by omega)) (ih j (by omega) u _ (by omega))
end Workday

variable {X Y:Type} {P:ℝ}
lemma heating_deck (D:Deck P X Y)(K:Layer X X)(T:Ranked X)(r) (h:Layer.Sym D D K)(hh:D.Ready (T (r+2))) : D.Ready (heating K T r):= D.ready_smul _ (D.symm_ready (loop_ready hh h))
lemma matching_deck (D:Deck P X Y)(K:Layer X X)(T S:Ranked X)(p q r) (h:Layer.Sym D D K) (ht:D.Ready (T (p+1)))(hh:D.Ready (S (q+1))) : D.Ready (matchTwo K T S r (p,q)) := by
 by_cases hz:p+q=r
 · subst r; rw [matchTwo,dif_pos (show (p,q).1+(p,q).2=p+q from rfl)]; exact D.ready_smul _ (D.symm_ready (Packet.knot_ready D ht hh h))
 rw [matchTwo,dif_neg hz]; exact D.ready_zero
lemma heat_uses {e:ℕ}(D:Deck P X Y)(K:Layer X X)(T:Orders X)(h:Layer.Sym D D K)(hh:∀ p ≤ e, ∀ r,D.Ready (T p r))(f:Bool) (k p r:ℕ)(ht:p≤e): D.Ready (logHeat K T f k p r):= by
 induction k using Nat.strong_induction_on generalizing p r with
 | _ k ih=>
    cases k with
    | zero => rw [logHeat_first]; split; exact D.ready_zero; exact hh p ht r
    | succ k=>
      rw [logHeat_next]; split; exact D.ready_zero
      apply D.ready_smul; apply D.ready_add (heating_deck D K _ _ h (ih k (by omega) p _ ht)); apply D.ready_smul
      unfold drift carry force; apply D.ready_sum ;rintro ⟨i,j⟩ hq;have hv:= Finset.mem_antidiagonal.mp hq;change i+j=k at hv; apply D.ready_sum ;rintro ⟨a,b⟩ he;have hz:= Finset.mem_antidiagonal.mp he; change a+b=p at hz; apply D.ready_sum; rintro ⟨l,x⟩ hx; exact matching_deck D K _ _ l x r h (ih i (by omega) a _ (by omega)) (ih j (by omega) b _ (by omega))

namespace BudgetMore
-- linear folding wrapped in family form (avoid repeating sum costs)
lemma work_sum {X:Type}{A:Post I J}{u r:ℕ}{f:X→(w:W)→Packet (I w) r}(s:Finset X)(h:∀ i∈s, Workday L (A.cone u) (f i)) (w:W): (A.deck w).deckSum (∑ i∈s,f i w)=∑ i∈s,(A.deck w).deckSum (f i w):=by
 classical
 cases isEmpty_or_nonempty (Subtype (·∈ s)) with
 | inl hz=>rw [show s=∅ from ?_]; simp_rw [sum_empty,(A.deck w).desk_zero]; exact Finset.eq_empty_of_forall_notMem fun x hx=> hz.false ⟨x,hx⟩
 | inr ne=>
    let d := A.deck w
    rw [← Finset.sum_attach s (f:=fun i=>f i w), ← Finset.sum_attach s (f:=fun i=>(A.deck w).deckSum (f i w))]
    choose F hF H using fun i:s=> h i.val i.property
    apply d.desk_sum (s.attach) (fun i _=> H i w); intro i _; exact (hF i).cost w
end BudgetMore
end YM.RegulatorIR.Uniform
