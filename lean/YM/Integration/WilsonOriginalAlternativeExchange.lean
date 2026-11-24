import YM.Integration.WilsonOriginalAlternativeExtraction

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeExchange
open Finset Function Marker WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable {V:Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem split_root (F:V→Port→ℂ) (c:V→Port) (v:V) (s:Finset V) (t:Port) :
    (∏j∈s,F j (Function.update c v t j)) =
      (if v∈s then F v t else 1) * ∏j∈s.erase v,F j (c j) := by
  have rest:(∏j∈s.erase v,F j (Function.update c v t j))=∏j∈s.erase v,F j (c j):=by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  by_cases resident:v∈s
  · rw [if_pos resident,←Finset.mul_prod_erase s (fun j=>F j (Function.update c v t j)) resident,
      Function.update_self,rest]
  · rw [Finset.erase_eq_of_notMem resident] at rest
    simpa only [if_neg resident,Finset.erase_eq_of_notMem resident,one_mul] using rest

omit [Fintype V] in
private theorem picked (R:Census V) (p:Poly R) (C:V→ℂ) (c:V→Port) (v:V)
    (a b s:R.Mode) (hab:Poly.merges a b s) (hv:v∈s.val) :
    let term (t:Port):=
      ((∏j∈a.val,retain (Function.update c v t j))*p.part a) *
       ∏j∈b.val,entry C (j,Function.update c v t j)
    term 2=term 0-term 1 := by
  dsimp only
  simp_rw [split_root (fun _ t=>retain t) c v a.val,
    split_root (fun j t=>entry C (j,t)) c v b.val]
  by_cases ha:v∈a.val
  · have hb:v∉b.val:=Finset.disjoint_left.mp hab.1 ha
    simp [ha,hb,retain]
  · have hb:v∈b.val:=(Finset.mem_union.mp (hab.2.symm ▸ hv)).resolve_left ha
    simp [ha,hb,entry]

/-- One signed port withdraws the entire original conditional at this root while
holding every other port fixed, including resident disjoint owners in the same word. -/
theorem original (R:Census V) (p:Poly R) (C:V→ℂ) (c:V→Port) (v:V) (s:R.Mode)
    (active:v∈s.val) :
    (read R (Function.update c v 2) (stamped R p C)).part s =
    (read R (Function.update c v 0) (stamped R p C)).part s -
    (read R (Function.update c v 1) (stamped R p C)).part s := by
  have word_part (h:V→ℂ) (b:R.Mode):(word R h).part b=∏ j∈b.val,h j:=rfl
  simp only [full,Poly.part_mul,Multi.dilation_part,word_part]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab:Poly.merges a b s
  · simp only [if_pos hab]
    exact picked R p C c v a b s hab active
  · simp [hab]

end YM.Integration.WilsonOriginalAlternativeExchange
