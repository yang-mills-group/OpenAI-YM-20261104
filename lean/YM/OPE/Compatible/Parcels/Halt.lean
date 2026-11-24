import YM.OPE.Compatible.Parcels.Grav
/-!
# Integer Taylor below horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG
open scoped Topology BigOperators Classical
variable {I: Type*}[Fintype I][DecidableEq I]{Y:Type*}[AddCommGroup Y]
-- axis multiset through <D
def trail (I:Type*) [Fintype I][DecidableEq I] : ℕ→Finset (Multiset I)
| 0=>∅
| d+1=> insert 0 ((Finset.univ:Finset I).biUnion fun a=> (trail I d).image (Multiset.cons a))
lemma trailed (x:Multiset I)(d:ℕ): x∈trail I d ↔ x.card<d:=by
    induction d generalizing x with
    | zero=>simp [trail]
    | succ d ih=>
       rw [trail,Finset.mem_insert, Finset.mem_biUnion]; constructor
       · rintro (rfl|⟨i,-,hx⟩); simp
         obtain ⟨v,hv,rfl⟩:= Finset.mem_image.mp hx; rw [ih] at hv; simpa using hv
       intro h; by_cases H:x=0; exact Or.inl H
       obtain ⟨a,ha⟩:= Multiset.exists_mem_of_ne_zero H; refine Or.inr ⟨a,Finset.mem_univ _,Finset.mem_image.mpr ⟨x.erase a, (ih (x.erase a)).2 ?_,Multiset.cons_erase ha⟩⟩; rw [← Multiset.cons_erase ha] at h; simpa using h
omit [Fintype I] in
lemma mapped (f:Shift I→Y)(l:List I): dvol (Multiset.toList (l:Multiset I)) f=dvol l f:= rotate_perm f ((Multiset.coe_eq_coe ..).mp (by simp))
variable [Module ℝ Y]
omit [Fintype I] in
lemma slot_run (f:Shift I→ℝ)(v:Y)(l:List I)(x:Shift I): dvol l (fun i=>f i • v) x=dvol l f x • v:=by induction l generalizing x with
   | nil=>rfl
   | cons i l ih=>rw [dvol,dvol]; unfold numDiff; rw [ih,ih,sub_smul]
omit [Fintype I] [Module ℝ Y] in
lemma run_add (f g:Shift I→Y)(l:List I)(x:Shift I): dvol l (f+g) x=dvol l f x+dvol l g x:=by induction l generalizing x with
   | nil=>rfl
   | cons i l ih=> rw [dvol,dvol,dvol]; unfold numDiff; rw [ih,ih]; abel
omit [Fintype I] [Module ℝ Y] in
lemma run_sub (f g:Shift I→Y)(l:List I)(x:Shift I): dvol l (f-g) x=dvol l f x-dvol l g x:=by
    have he:= run_add (f-g) g l x; rw [sub_add_cancel] at he; abel_nf at *; rw [he]; abel
omit [Fintype I] [Module ℝ Y] in
lemma run_set {J:Type*}(A:Finset J)(f:J→ Shift I→Y)(l:List I)(x:Shift I): dvol l (∑ j∈A,f j) x=∑ j∈A,dvol l (f j) x:=by
    induction A using Finset.induction_on with
    | empty=>rw [Finset.sum_empty,dvol_zero,Finset.sum_empty];rfl
    | insert i a hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,run_add,ih]
def sketch (d:ℕ)(f:Shift I→Y): Shift I→Y:= ∑ i∈trail I d, (fun x:Shift I=> pine i x • dvol i.toList f 0)
lemma sketch_hits (l:List I)(f:Shift I→Y) {d:ℕ} (h:l.length<d): dvol l (sketch d f) 0=dvol l f 0:=by
   rw [sketch,run_set, Finset.sum_eq_single (l:Multiset I), slot_run,known,if_pos rfl,one_smul,mapped]; swap
   · exact fun H=> (H ((trailed _ d).2 (by simpa using h))).elim
   intro i hi hj; rw [slot_run,known, if_neg (Ne.symm hj),zero_smul]
lemma sketch_fizz (l:List I)(f:Shift I→Y)(x:Shift I) {d:ℕ}(h:d≤ l.length): dvol l (sketch d f) x=0:=by rw [sketch,run_set]; apply Finset.sum_eq_zero; intro i hi; rw [slot_run,overrun i l (((trailed i d).1 hi).trans_le h)]; simp
end YM.OPE.Flume
