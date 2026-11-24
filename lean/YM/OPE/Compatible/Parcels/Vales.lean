import YM.OPE.Compatible.Parcels.Lakes
/-!
# Polynomial tolerances. Lifts for finite marks with coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG
open scoped Topology Classical BigOperators
variable {I J K:Type*}[Fintype I]
def notch (x:I→ℤ):=1+size x
def poise (m:ℕ)(x:Shift I):ℝ:= (notch x:ℝ)^m
lemma notch_one (x:Shift I):1 ≤ notch x:= Nat.le_add_right ..
lemma poise_one (m:ℕ) : 1 ≤ poise (I:=I) m:= fun i=>one_le_pow₀ (show (1:ℝ)≤(notch i:ℝ) by exact_mod_cast notch_one i)
lemma notch_add (x y:Shift I) : notch (x+y) ≤ notch x*notch y:=by
    unfold notch; nlinarith only [size_add x y]
lemma poise_cumul (x y:Shift I)(d:ℕ) : poise d (x+y) ≤ poise d x*poise d y:=by
   unfold poise; rw [← mul_pow,← Nat.cast_mul]; gcongr; apply notch_add
section step
variable [DecidableEq I]
def stint (i:I): Shift I:= Pi.single i 1
lemma backing (x:Shift I)(i:I)(hx:x i≠0): ∃ y:Shift I,size x=size y+1∧ (x=y+stint i ∨ x=y-stint i):=by
    rcases lt_or_gt_of_ne hx with hx|hx
    · refine ⟨x+stint i, ?_, Or.inr (by abel)⟩; unfold size; nth_rw 1 [← Finset.add_sum_erase _ (fun k=> (x k).natAbs) (Finset.mem_univ i)]; rw [← Finset.add_sum_erase _ (fun k=> ((x+stint i) k).natAbs) (Finset.mem_univ i)]
      have he : ∀ j∈(Finset.univ.erase i), ((x+stint i) j).natAbs=(x j).natAbs := fun j hj=> by simp [stint,Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
      rw [Finset.sum_congr rfl he]; change _+_=(x i+stint i i).natAbs+_+_; rw [show stint i i=1 by simp [stint]]; omega
    refine ⟨x-stint i,?_,Or.inl (by abel)⟩; unfold size; nth_rw 1 [← Finset.add_sum_erase _ (fun k=> (x k).natAbs) (Finset.mem_univ i)]; rw [← Finset.add_sum_erase _ (fun k=> ((x-stint i) k).natAbs) (Finset.mem_univ i)]; have he : ∀ j∈(Finset.univ.erase i), ((x-stint i) j).natAbs=(x j).natAbs := fun j hj=> by simp [stint,Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
    rw [Finset.sum_congr rfl he]; change _+_=(x i-stint i i).natAbs+_+_; rw [show stint i i=1 by simp [stint]]; omega
lemma stride (x:Shift I) (h:x≠0): ∃ i:I,∃ y:Shift I,size x=size y+1∧ (x=y+stint i ∨ x=y-stint i):=by
    have he : ∃ i:I,x i≠0:=not_forall.mp (fun hh=> h (funext hh)); obtain ⟨i,hi⟩:=he; exact ⟨i,backing x i hi⟩
-- diff. use list
variable {Y:Type*}[AddCommGroup Y]
def numDiff (i:I)(f:Shift I→Y) :Shift I→Y:=fun x=> f (x+stint i)-f x
def dvol :List I → (Shift I→Y) → Shift I→Y
| [],f=>f
| k::l,f=>numDiff k (dvol l f)
omit [Fintype I]
lemma rotate (i j:I)(f:Shift I→Y): numDiff i (numDiff j f)=numDiff j (numDiff i f):=by ext1 x; unfold numDiff; rw [add_right_comm x]; abel
lemma rotate_tail (l:List I)(i:I)(f:Shift I→Y): numDiff i (dvol l f)=dvol l (numDiff i f) := by
    induction l with
    | nil=>rfl
    | cons j l ih=>rw [dvol,dvol,rotate,ih]
lemma rotate_perm {l m:List I}(f:Shift I→Y)(h:l.Perm m): dvol l f=dvol m f:=by
    induction h with
    | nil=>rfl
    | cons a b ih=> rw [dvol,dvol,ih]
    | swap a b l=> exact rotate b a (dvol l f)
    | trans _ _ a b=> exact a.trans b
end step
end YM.OPE.Flume
