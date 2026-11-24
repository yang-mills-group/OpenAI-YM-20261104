import YM.SchemeConversionRG11.FirstW.Kernel.Yard
/-! Forward differences (pre-physics normalization); flexible periodic and cover arrays. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Lattice Function
open scoped BigOperators
variable {X E F : Type*} [AddCommGroup X] [One X] [AddCommGroup E] [AddCommGroup F]

def up (i : Axis) (f : Four X→E) : Four X→E := fun x=> f (x+step i)-f x
def combine : List Axis → (Four X → E) → Four X → E
  | [], f => f
  | i::d,f => up i (combine d f)
lemma append_op (α β : List Axis) (f : Four X→E) : combine (α++β) f = combine α (combine β f) := by
  induction α with
  | nil => rfl
  | cons a b ih => simp only [List.cons_append,combine,ih]
lemma combine_up (α : List Axis) (i : Axis) (f : Four X→E) : combine α (up i f) = up i (combine α f) := by
  induction α with
  | nil=>rfl
  | cons a α ih=>
    rw [combine,ih,combine]; funext x; unfold up; rw [add_right_comm x]; abel
lemma perm_row {l l' : List Axis} (h : l.Perm l') (f : Four X→E) : combine l f=combine l' f := by
  induction h with
  | nil=>rfl
  | cons _ _ ih => simp only [combine,ih]
  | swap x y α => exact combine_up [y] _ (combine α f)
  | trans _ _ i j=> exact i.trans j
lemma combine_add (α : List Axis) (f g : Four X→E) : combine α (f+g)=combine α f+combine α g := by
  induction α with
  | nil=> rfl
  | cons a l ih=> rw [combine,ih]; funext x; dsimp [combine,up];abel
lemma combine_sub (α : List Axis) (f g : Four X→E) : combine α (f-g)=combine α f-combine α g := by
  induction α with
  | nil=> rfl
  | cons a l ih=> rw [combine,ih]; funext x; dsimp [combine,up];abel
lemma combine_smul {R : Type*} [Monoid R] [DistribMulAction R E] (r : R) (α : List Axis) (f : Four X→E) : combine α (r • f) = r • combine α f := by
  induction α with
  | nil=> rfl
  | cons a l ih=> rw [combine,ih]; funext x; simp [combine,up, smul_sub]
lemma combine_zero (α : List Axis) : combine α (0:Four X→E)=0 := by
  induction α with
  | nil=> rfl
  | cons a l ih=> rw [combine,ih]; ext1 x; simp [up]
lemma sum_combine (α : List Axis) {K : Type*} (s : Finset K) (f : K→Four X→E) : combine α (∑ k∈s, f k)=∑ k∈s,combine α (f k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [combine_zero]
  | insert a s h ih=> rw [Finset.sum_insert h,Finset.sum_insert h,combine_add,ih]
lemma combine_map (α : List Axis) (L : E→+F) (f : Four X→E) : combine α (L ∘ f) = L ∘ combine α f := by
  induction α with
  | nil=> rfl
  | cons a l ih => rw [combine,ih]; ext1 x; simp only [up,comp_def,combine,map_sub]
lemma combine_shift (α : List Axis) (f : Four X→E) (z : Four X) : combine α (fun x=> f (x+z))=fun x=>combine α f (x+z) := by
  induction α with
  | nil=> rfl
  | cons a l ih => rw [combine, ih]; ext1 x; exact congrArg (fun v => combine _ f v- _) (add_right_comm _ _ _)
lemma combine_wrap (α : List Axis) (n : Side) (f : Site n→E) : combine α (f ∘ wrap n) = combine α f ∘ wrap n := by
  induction α with
  | nil=>rfl
  | cons a α ih=> rw [combine, ih]; ext1 x; simp only [comp_def,map_add, wrap_step,combine,up]
lemma sum_transpose {n : Side} (f g : Site n→ℝ) (i : Axis) : (∑ x, up i f x * g x) = (-1:ℝ) * (∑ x:Site n,f x* up i g (x-step i)) := by
  let h := Equiv.addRight (- (step i : Site n))
  have hh := Equiv.sum_comp h (fun x=> f (x+step i)*g x)
  simp only [up, sub_mul,mul_sub, Finset.sum_sub_distrib, sub_add_cancel]
  rw [← hh]
  change (∑ x:Site n,f (x + -step i + step i) * g (x + -step i)) - _ = _
  simp only [neg_add_cancel_right]; simp_rw [sub_eq_add_neg]; ring

def offsetD (D : List Axis) : Cover := ((D.map (fun i=> (step i : Cover))).sum)
lemma offsetD_cons (i : Axis) (a : List Axis) : offsetD (i::a)=step i+offsetD a := by rw [offsetD,List.map_cons,List.sum_cons];rfl
lemma offsetD_append (α β : List Axis):offsetD (α++β)=offsetD α+offsetD β:= by unfold offsetD; rw [List.map_append,List.sum_append]
lemma combine_transpose {n : Side} (f g : Site n→ℝ) (α : List Axis) : ∑ x,combine α f x * g x = (-1)^α.length * ∑ x:Site n,f x * combine α g (x-wrap n (offsetD α)) := by
  induction α generalizing g with
  | nil => simp [combine,offsetD]
  | cons i α ih=>
    rw [combine,sum_transpose]
    let u:=fun x=> up i g (x-step i)
    rw [show (∑ x,combine _ f x * _)=_ from ih u]
    have he : ∀ x, combine α u x= up i (combine α g) (x-step i) := fun x => by simp_rw [u,sub_eq_add_neg, combine_shift,combine_up]
    rw [offsetD_cons,map_add,wrap_step]; simp_rw [he,combine, sub_sub, add_comm (step i : Site n)]
    rw [List.length_cons,pow_succ]; ring
end YM.RG11.FirstW
