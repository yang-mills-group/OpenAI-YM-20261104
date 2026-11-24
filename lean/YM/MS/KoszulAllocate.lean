import YM.MS.KoszulEdges

/-!
# List allocation of legs to two vertices in the shuffle product

Version on any comm ring, with sign determined by input list order. Consumers in momentum shape estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset
variable {A R I : Type*} [CommRing R]
abbrev Legs (A : Type*) := List A
inductive Split {A : Type*} : Legs A → Legs A → Legs A → Prop where
| nil : Split [] [] []
| left {a l r w} : Split (A:=A) l r w → Split (a::l) r (a::w)
| right {a l r w} : Split (A:=A) l r w → Split l (a::r) (a::w)
attribute [grind .] Split.left Split.right
variable (p : Sector A)

abbrev Shared (A R : Type*) := Legs A → Legs A → R

def scatter (p : Sector A) : Legs A→ Shared A R→ R
  | [], f=> f [] []
  | i::w,f=> scatter p w (fun l r=> f (i::l) r+cross (p i) (degree p l)*f l (i::r))
@[simp] lemma scatter_nil (f : Shared A R) : scatter p [] f=f [] [] := rfl
lemma scatter_cons (i) (w:Legs A) (f:Shared A R) : scatter p (i::w) f=scatter p w (fun l r=> f (i::l) r+cross (p i) (degree p l)*f l (i::r)):=rfl
private lemma distribute_add (w:Legs A) (f g:Shared A R): scatter p w (fun l r=> f l r+ g l r)= scatter p w f+ scatter p w g:= by
   induction w generalizing f g with
   | nil=>rfl
   | cons a w IH=> simp only [scatter_cons,← IH,mul_add]; congr! 3; abel
private lemma distribute_smul (w:Legs A) (c:R) (f:Shared A R): scatter p w (fun l r=> c*f l r)= c*scatter p w f:= by
   induction w generalizing f with
   | nil=>rfl
   | cons a w IH=> rw [scatter_cons, scatter_cons (f:=f),← IH]; congr! 2; funext; ring

def allocate (w:Legs A): Shared A R→ₗ[R] R where
   toFun := scatter p w
   map_add' _ _:= distribute_add ..
   map_smul' _ _:= distribute_smul ..

lemma scatter_congr (w : Legs A) (f g:Shared A R) (h: ∀ l r, Split l r w → f l r=g l r) : scatter p w f=scatter p w g := by
   induction w generalizing f g with
   | nil=>exact h _ _ .nil
   | cons a w IH=>
       rw [scatter_cons,scatter_cons]; refine IH _ _ (fun l r hv=>?_)
       rw [h (a::l) r hv.left,h _ _ hv.right]
lemma scattered (F G : Raw A R) (w : Legs A) : product p F G w = scatter p w (fun l r=> F l*G r):= by
   induction w generalizing F G with
   | nil => simp
   | cons a w IH=>
       rw [D_eval a (product p F G), D_product,Pi.add_apply,IH,IH,scatter_cons,← distribute_add]; simp only [at_sign, at_D, mul_assoc]
lemma split_perm {l r w:Legs A} (h:Split l r w): (l++r).Perm w := by
   induction h with
   | nil=>rfl
   | left h IH=> exact IH.cons _
   | right h IH=> exact (List.perm_middle ..).trans (IH.cons _)
lemma split_comm {l r w:Legs A} (h:Split l r w): Split r l w:= by induction h with | nil=>exact .nil | left h IH=>exact IH.right | right h IH=>exact IH.left
lemma split_sum {G:Type*} [AddCommMonoid G] (r:A→G) {l k w:Legs A} (h:Split l k w) : (l.map r).sum+(k.map r).sum=(w.map r).sum := by simpa using ((split_perm h).map r).sum_eq
lemma split_length {l k w:Legs A} (h:Split l k w): l.length+k.length=w.length := by simpa using (split_perm h).length_eq
end YM.MS.Koszul
