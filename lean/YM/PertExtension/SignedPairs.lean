import YM.Space.Index
import Mathlib

/-!
Symmetry combinatorics for the symmetric square of 2-form slots in four
dimensions. Finitary rigidity lemma: an endomorphism killed on the
orthogonal unit and skew on the remaining span with signed permutation
equivariance. The bilinear form here can use conjugating test partners if
they are fixed real-underlying variations.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 400000
namespace YM.PertExtension.SignedPair
open Set Function Filter
open scoped BigOperators

private def edge (i : Fin 6): Axis×Axis :=
  ![((0,1) : Axis×Axis), (0,2),(0,3),(1,2),(1,3),(2,3)] i
lemma positivePairs (i:Fin 6) : (edge i).1<(edge i).2 := by fin_cases i <;> decide
lemma enumerate (a b : Axis)(ha:a<b):∃ i,edge i=(a,b):= by
  fin_cases a <;> fin_cases b <;> simp [Axis] at ha
  all_goals decide

abbrev E := Axis × Axis
abbrev W := Fin 6 × Fin 6
private def tint (a : Axis)(u : W): Bool := if a=(edge u.1).1 then !((a==(edge u.1).2) ^^ (a==(edge u.2).1) ^^ (a==(edge u.2).2)) else ((a==(edge u.1).2) ^^ (a==(edge u.2).1) ^^ (a==(edge u.2).2))

def interchange (a b x:Axis):= if x=a then b else if x=b then a else x
def invert_edge (a b:Axis)(e:E) : E := (interchange a b e.1,interchange a b e.2)
def converts (a b:Axis)(e f:E)(x:Bool): Prop := invert_edge a b e=(if x then Prod.swap f else f)
def convertsPair (a b:Axis)(u v:W)(s x y:Bool): Prop := let v:= if s then Prod.swap v else v; converts a b (edge u.1) (edge v.1) x ∧ converts a b (edge u.2) (edge v.2) y
def decRelation (a b:Axis)(u v:W)(s x y:Bool): Bool :=
 ((invert_edge a b (edge u.1)) == if x then Prod.swap (edge (if s then Prod.swap v else v).1) else edge (if s then Prod.swap v else v).1) &&
 ((invert_edge a b (edge u.2)) == if y then Prod.swap (edge (if s then Prod.swap v else v).2) else edge (if s then Prod.swap v else v).2)

set_option pp.universes false in
lemma finite_search (i j k l : Fin 6) :
    (∃ a,tint a (i,j) ≠ tint a (k,l)) ∨
    (∃ a b : Axis,∃ s x y:Bool, decRelation a b (i,j) (k,l) s x y) ∨
    (i=j ∧ k=l ∧ (edge i).1 ≠ (edge k).2 ∧ (edge i).2 ≠ (edge k).1):= by
  -- test pure enumeration using constructive fin instances
  revert i j k l
  decide +kernel

def push (s : Axis≃Axis) (e:E) : E := (s e.1,s e.2)
def orbitAlt {V : Type*}[AddCommGroup V][Module ℝ V] (q:E→E→V)(u:W):= q (edge u.1) (edge u.2)

lemma intersection (u v:W) : (∃ a,tint a u≠tint a v) ∨
   ∃ (s : Equiv.Perm Axis) (x y : Bool)(w : W), (w=v ∨ w=v.swap) ∧
        (push s (edge u.1)=(if x then Prod.swap (edge w.1) else edge w.1)) ∧
        (push s (edge u.2)=(if y then Prod.swap (edge w.2) else edge w.2)) ∧
        (push s (edge w.1)=(if x then Prod.swap (edge u.1) else edge u.1)) ∧
        (push s (edge w.2)=(if y then Prod.swap (edge u.2) else edge u.2)):= by
   rcases u with ⟨i,j⟩;rcases v with ⟨k,l⟩
   obtain h|h|⟨rfl,rfl,ht,hv⟩:=finite_search i j k l;exact Or.inl h
   · right; obtain ⟨a,b,s,x,y,h⟩:=h
     let p:=Equiv.swap a b
     let w:= if s then Prod.swap (k,l) else (k,l)
     have H : (push p (edge i)=(if x then Prod.swap (edge w.1) else edge w.1)) ∧
        (push p (edge j)=(if y then Prod.swap (edge w.2) else edge w.2)) := by
       simpa [w,decRelation, Bool.and_eq_true, beq_iff_eq, interchange, invert_edge, p,push,Equiv.swap_apply_def] using! h
     have he z : p (p z)=z:=Equiv.swap_apply_self ..
     refine ⟨p,x,y,w, (by cases s <;> simp [w]),H.1,H.2,?_,?_⟩ 
     · have hh := congr_arg (push p) H.1
       cases x <;> simp only [ite_false,ite_true,push,Prod.swap,Prod.mk.injEq,he] at hh ⊢ <;>grind
     have hh:= congr_arg (push p) H.2
     cases y <;> simp only [ite_false,ite_true,push,Prod.swap,Prod.mk.injEq,he] at hh ⊢ <;> grind
   right
   let s:=Equiv.swap (edge i).1 (edge k).1*Equiv.swap (edge i).2 (edge k).2
   have hi:=(positivePairs i).ne
   have hk:= (positivePairs k).ne
   have h₁ : push s (edge i)=edge k := by
      apply Prod.ext <;> simp [push,s,Equiv.swap_apply_of_ne_of_ne,Equiv.Perm.mul_apply,ht,hi,ht.symm,hk.symm]
   have h₂ :push s (edge k)=edge i := by
      apply Prod.ext <;> simp [push,s,Equiv.swap_apply_of_ne_of_ne,Equiv.Perm.mul_apply,hv,hv.symm,hk,hi.symm]
   exact ⟨s,false,false,(k,k),Or.inl rfl,h₁,h₁,h₂,h₂⟩

def sign (a i:Axis) : ℝ := if a=i then -1 else 1
private lemma xor_value (p q: Bool) : (if p ^^ q then -1 else (1:ℝ)) = (if p then -1 else 1)*(if q then -1 else 1):=by cases p<;>cases q <;> norm_num
lemma tint_eq (a : Axis)(u:W) : (if tint a u then (-1:ℝ) else 1) = sign a (edge u.1).1 * sign a (edge u.1).2 *(sign a (edge u.2).1 * sign a (edge u.2).2) := by
  unfold tint sign
  set e:=edge u.1
  set f:=edge u.2
  generalize e₁ : e.1=x at *
  generalize e₂ : e.2=y at *
  generalize f₁ : f.1=x' at *
  generalize f₂ : f.2=y' at *
  simp_rw [beq_eq_decide]
  clear e₁ e₂ f₁ f₂ e f u
  fin_cases a <;> fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;> norm_num [Axis]

variable {V:Type*}[AddCommGroup V][Module ℝ V]

theorem signs_force (q:E→E→V)(L:Module.End ℝ V)(A: LinearMap.BilinForm ℝ V)(units:Set V)
    (spans: (⊤:Submodule ℝ V) ≤ Submodule.span ℝ (Set.range (orbitAlt q) ∪ units))
    (H₁: ∀ x y, q (Prod.swap x) y= -q x y)
    (H₂: ∀ x y,q x (Prod.swap y)= -q x y)
    (H₃: ∀ x y, q x y=q y x)
    (round: ∀ s:Equiv.Perm Axis, ∀ x y u v, A (L (q (push s x) (push s y))) (q (push s u) (push s v))=A (L (q x y)) (q u v))
    (signs: ∀ (a:Axis) (x y u v : E), A (L (q x y)) (q u v)=
         ((sign a x.1*sign a x.2)*(sign a y.1*sign a y.2))*((sign a u.1*sign a u.2)*(sign a v.1*sign a v.2))*A (L (q x y)) (q u v))
    (skew : ∀ x y,A (L x) y= -A (L y) x)
    (unitKill : ∀ x∈units,L x=0)
    (det : ∀ x,A x x=0 → x=0) : L=0 := by
  have ht : ∀ x : W,∀ y:W,A (L (orbitAlt q x)) (orbitAlt q y)=0:=by
    intro u v; obtain h|⟨s,p,q',w,hw,hu₁,hu₂,hv₁,hv₂⟩:=intersection u v
    · obtain ⟨a,hm⟩:=h
      have hk:=signs a (edge u.1) (edge u.2) (edge v.1) (edge v.2)
      dsimp only [orbitAlt]
      rw [←tint_eq a u, ← tint_eq a v] at hk
      cases h₁:tint a u<;>cases h₂:tint a v<;> simp [h₁,h₂] at hm hk<;>change A _ _=0 <;>linarith
    specialize round s (edge u.1) (edge u.2) (edge w.1) (edge w.2)
    have he : q (edge w.1) (edge w.2)=orbitAlt q v:=by
      rcases hw with rfl|rfl; rfl
      exact H₃ _ _
    rw [hu₁,hu₂,hv₁,hv₂] at round
    cases p <;> cases q' <;> simp only [ite_true,ite_false,Bool.false_eq_true,H₁, H₂,neg_neg,map_neg,LinearMap.neg_apply] at round
    all_goals
              change A (L (q _ _)) _ = _
              rw [he,skew] at round; change A (L (q _ _)) (orbitAlt q _)=0;linarith
  suffices h: ∀ x y : V,A (L x) y=0 by
    exact LinearMap.ext fun x=>det _ (h x _)
  have hw x: x∈Submodule.span ℝ (Set.range (orbitAlt q) ∪ units):=spans (Submodule.mem_top (x:=x))
  have he v y : A (L (orbitAlt q v)) y=0 := by
    induction hw y using Submodule.span_induction with
    | mem y hy=>
      obtain ⟨y,rfl⟩|h:=hy;exact ht ..
      rw [skew,unitKill _ h,map_zero];simp
    | zero=>simp
    | add _ _ _ _ hx hy=> simp [hx,hy]
    | smul c x h hx=>simp [hx]
  intro x y; rw [skew,neg_eq_zero]
  induction hw x using Submodule.span_induction with
  | mem u hu=>
    obtain ⟨u,rfl⟩|h:=hu;rw [skew,he,neg_zero]
    rw [skew,unitKill _ h,map_zero];simp
  | zero=>simp
  | add _ _ _ _ hx hy=> simp [hx,hy]
  | smul _ _ _ hx=> simp [hx]
end YM.PertExtension.SignedPair
