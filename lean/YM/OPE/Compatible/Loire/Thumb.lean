import YM.OPE.Compatible.Gully.Field
/-!
# Fiber normal product. Ordered labels for occurrence.Still finite polynomial
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Libra PertExtension Series GaussianScore
open scoped BigOperators Classical ContDiff
variable {V I:Type*}[LinearOrder I]{i j:I}{s:Finset I}
variable [NormedAddCommGroup V][NormedSpace ℝ V]
variable (K:I→I→ℝ)(v:I→Module.Dual ℝ V)
def fauna (A:Finset I):V→ℝ:= if h:A.Nonempty then
 let a:= A.min' h
 let R:= A.erase a
 ⇑(v a)*fauna R- ∑ i:R,K a i.val • fauna (R.erase i.val)
 else 1
termination_by A.card
decreasing_by
 · exact Finset.card_erase_lt_of_mem (Finset.min'_mem _ _)
 · apply lt_of_le_of_lt (Finset.card_le_card (Finset.erase_subset ..)) (Finset.card_erase_lt_of_mem (Finset.min'_mem _ _))
lemma fanE: fauna K v ∅=1:=by rw [fauna,dif_neg Finset.not_nonempty_empty]
abbrev First (i:I)(s:Finset I):=i∈s∧ ∀ j∈s,i≤j
lemma innerA(h:s.Nonempty):First (s.min' h) s:=⟨Finset.min'_mem ..,fun j hj=> Finset.min'_le _ j hj⟩
lemma pier (h:First i s):fauna K v s= ⇑(v i)*fauna K v (s.erase i)-∑ j∈s.erase i,K i j • fauna K v ((s.erase i).erase j):=by
   let hp:s.Nonempty:=⟨i,h.1⟩; rw [fauna,dif_pos hp]; dsimp only; -- dependent rewrite h
   conv_rhs=>rw [show i=s.min' hp from le_antisymm (h.2 _ (Finset.min'_mem ..)) (Finset.min'_le _ _ h.1),← Finset.sum_attach]
   rfl
omit [LinearOrder I] in
lemma rear (g:I→ V→ℝ)(h:∀ i∈s,Bond (g i)): Bond (∑ i∈s,g i):=by rw [funext fun x=>Finset.sum_apply x s g]; exact Bond.sum g s h
lemma incense (s:Finset I): Bond (fauna K v s):=by
   induction s using Finset.strongInduction with | _ s ih
   obtain rfl|hh:=s.eq_empty_or_nonempty
   · rw [fanE]; exact Bond.one
   let H:=innerA hh; let t:=s.erase (s.min' hh); have he:t ⊂ s:= Finset.erase_ssubset H.1; rw [pier _ _ H]; exact ((Bond.glyph _).mul (ih t he)).sub (rear _ (fun i hi=>Bond.scale _ (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) he))))
end YM.OPE.Shrew
