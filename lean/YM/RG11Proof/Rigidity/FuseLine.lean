import YM.RG11Proof.Rigidity.Palette

/-!
# Collapse of summed color panels along scalar Wick lines
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell.Free Function
open scoped BigOperators Classical

namespace palette
variable {C A Q : Type*} [Fintype C]

abbrev Pair (Q : Type*) := Q×Q
def byColor (hit : Q → C → A) (i : Pair Q) : Dye C A := (hit i.1,hit i.2)
def deck (hit : Q → C → A) (L : List (Pair Q)) := palette (R:=ℝ) (L.map (byColor hit))
@[simp] lemma deck_nil (hit : Q → C → A) (f) : deck hit [] f=f [] := rfl
lemma deck_bind (hit : Q→C→A) (p : Pair Q) (L : List (Pair Q)) (f : List A → ℝ) :
    deck hit (p::L) f=∑ s, deck hit L (fun r=> f (hit p.1 s :: hit p.2 s:: r)) := rfl
abbrev Swap (u : List A→ℝ) := ∀ {L t},List.Perm L t → u L=u t

lemma deck_perm (hit : Q→C→A) (u : List A→ℝ) (H : Swap u) {L t : List (Pair Q)} (hw : List.Perm L t) :
    deck hit L u=deck hit t u := by
  induction hw generalizing u with
  | nil => rfl
  | cons a h ih => simp_rw [deck_bind]; exact Finset.sum_congr rfl fun i _=> ih (u:=fun r=>u _) (fun h=> H (List.Perm.cons _ (.cons _ h)))
  | swap a b L =>
    simp_rw [deck_bind]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
    congr 1; funext r; apply H
    exact List.Perm.append_right r (List.perm_append_comm (l₁:=[_,_]) (l₂:=[_,_]))
  | trans h g h1 h2 => exact (h1 _ H).trans (h2 _ H)
lemma swap_after (g : List A→ℝ) (H : Swap g) (a b : A) : Swap (fun u=>g (a::b::u)) := fun h=>H (List.Perm.cons _ (.cons _ h))

local notation "Σ₀" => Finset.sum

lemma pulls_sum_outer {I : Type*} (s : Finset I) (L : List A) (f : I → A → List A→ℝ) :
    (∑ i∈s,pulls L (f i))=pulls L (fun a l=>∑ i∈s,f i a l) := Finset.sum_comm

/-- Sum over all panels, pay a levy on *one chosen endpoint*, and read a
symmetric cost on the rest. An earlier color (fixed at one endpoint outside
the packet) now exits through the partner. -/
lemma fuses [DecidableEq C] (hit : Q → C → A) (E : A → A → ℝ) (B : Q → Q → ℝ)
    (h : ∀ i j d c, E (hit i d) (hit j c)= if d=c then B i j else 0)
    (L : List (Pair Q)) (i : Q) (d : C) (m : List A→ℝ) (hm : Swap m) :
    deck hit L (fun p=> pulls p (fun a r=> E (hit i d) a * m r)) =
    pulls L (fun q l=>
      B i q.1 * deck hit l (fun r=> m (hit q.2 d::r))+ B i q.2*deck hit l (fun r=>m (hit q.1 d::r))) := by
  classical
  induction L generalizing m with
  | nil => rw [deck_nil,pulls_nil,pulls_nil]
  | cons a L ih =>
    rw [deck_bind,pulls_cons]; simp_rw [pulls_cons]
    have hk (l) (u v : List A→ℝ) : deck hit l (fun r=>u r+v r)=deck hit l u+deck hit l v := add (L:=l.map (byColor hit)) u v
    have hk' (l) (u : List A→ℝ) t : deck hit l (fun r=>t*u r)=t*deck hit l u := mul (L:=l.map (byColor hit)) u t
    simp_rw [hk,h,hk',Finset.sum_add_distrib]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    rw [← add_assoc]; congr 1
    simp_rw [show ∀ x, deck hit L (fun r=> pulls r (fun b v=> E (hit i d) b * m (hit a.1 x :: hit a.2 x :: v))) =_ from fun x : C=> ih _ (swap_after m hm _ _), deck_bind, Finset.mul_sum,← Finset.sum_add_distrib]
    rw [pulls_sum_outer]; apply pulls_congr; intro j
    refine Finset.sum_congr rfl fun c _=> ?_
    have hx (q:A) (l) : m (hit a.1 c :: hit a.2 c :: q :: l)=m (q :: hit a.1 c :: hit a.2 c :: l):= hm (((List.Perm.swap _ _ l).cons _).trans (.swap _ _ _))
    simp_rw [hx]

end palette
end YM.RG11.Rigidity
