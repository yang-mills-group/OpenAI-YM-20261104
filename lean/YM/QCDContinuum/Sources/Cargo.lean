import YM.Marker.Console
/-! # Adapt the marker ring in Marker/Console to even-Grassmann contents.
A type synonym separating the hard exclusion convolution from pointwise multiply.
Square-zero counted only at evaluation in this ring; labels remain distinct in
the financing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Marker
open Function Finset
open scoped BigOperators Topology ENNReal
variable {V:Type*}[DecidableEq V]{R:Census V}
-- type synonym hide pointwise multiplication instance.
def Cargo (R : Census V)(A : Type*) := R.Mode → A
namespace Cargo
variable {A : Type*}
def part (f : Cargo R A) : R.Mode → A := f
def inject (f : R.Mode → A) : Cargo R A := f

section add
variable [AddCommGroup A]
instance : AddCommGroup (Cargo R A) := inferInstanceAs (AddCommGroup (R.Mode → A))
instance instModule (k:Type*) [Ring k][Module k A]: Module k (Cargo R A) := inferInstanceAs (Module k (R.Mode → A))

omit [AddCommGroup A] in
@[ext] theorem ext {f g : Cargo R A} (h : ∀ v, part f v=part g v) : f=g := funext h

/-- from scalar & tag. -/
def send (x : R.Mode) (v : A) := inject (Pi.single x v)

@[simp] lemma part_plus (f g : Cargo R A) (x : R.Mode) : (f+g).part x= f.part x+g.part x := rfl
@[simp] lemma part_nil (x : R.Mode) : (0 : Cargo R A).part x=0 := rfl
@[simp] lemma part_neg (f : Cargo R A) (x : R.Mode) : (-f).part x= -f.part x := rfl
@[simp] lemma part_smul {k:Type*}[Ring k][Module k A](r : k) (f : Cargo R A) (x : R.Mode) : (r • f).part x=r • f.part x := rfl
@[simp] lemma part_send (x y : R.Mode) (v : A) : (send x v).part y=if y=x then v else 0 := Pi.single_apply _ _ _
@[simp] lemma send_zero (x : R.Mode) : send x (0:A)=0 := by ext i; simp

lemma part_sum {M} (S : Finset M) (f : M → Cargo R A) (x : R.Mode) : (∑ i∈S,f i).part x=∑ i∈S,(f i).part x := by
  let g : Cargo R A →+ A := { toFun := fun b => b.part x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum g ..

lemma studs (b : Cargo R A) : (∑ i,send i (b.part i))=b := by ext; simp [part_sum]
end add
variable [CommRing A]

def prod (p q : Cargo R A) : Cargo R A := inject fun z => ∑ x, ∑ y, if Poly.merges x y z then part p x*part q y else 0

lemma product (p q : Cargo R A) (x : R.Mode) : (prod p q).part x=∑ i, ∑ j, if Poly.merges i j x then p.part i*q.part j else 0 := rfl

lemma prod_commutative (a b : Cargo R A) : prod a b=prod b a := by
  ext u; change (∑ x, ∑ y, if Poly.merges x y u then _ else _)=∑ x, ∑ y, if Poly.merges x y u then _ else _
  rw [sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp only [Poly.wind j i u]; split <;> simp [mul_comm]

lemma on_left (a b c : Cargo R A) : prod (a+b) c=prod a c+prod b c := by
  ext i
  simp only [part_plus,product]
  rw [← sum_add_distrib]; refine sum_congr rfl fun j _ => ?_
  rw [← sum_add_distrib]; refine sum_congr rfl fun k _ => ?_
  split <;> simp [*,add_mul]

lemma on_vac (a : Cargo R A) : prod (send R.quiet 1) a=a := by
  ext i; rw [product, sum_eq_single R.quiet]
  · simp
  · intro b _ hb; simp [hb]
  simp

lemma no_one (a : Cargo R A) : prod a 0=0 := by
  ext i
  suffices ∑ x, ∑ y, (if Poly.merges x y i then a.part x*(0 : Cargo R A).part y else 0)=0 from this
  simp

lemma cart (x y z : R.Mode) (i j : A) : (prod (send x i) (send y j)).part z=
    if Poly.merges x y z then i*j else 0 := by
  change (∑ a : R.Mode, ∑ b : R.Mode, if Poly.merges a b z then (send x i).part a*(send y j).part b else 0)=_
  rw [sum_eq_single x]
  · rw [sum_eq_single y]; simp
    · intro b _ hb; simp [hb]
    simp
  · intro b _ hb; simp [hb]
  simp

lemma atom_left (a b c d : R.Mode) (i j k : A) :
    (prod (prod (send a i) (send b j)) (send c k)).part d=
      if ∃ x, Poly.merges a b x ∧ Poly.merges x c d then i*j*k else 0 := by
  change (∑ x, ∑ y, if Poly.merges x y d then (prod _ _).part x * (send c k).part y else 0)=_
  split_ifs with h
  · obtain ⟨x,hx,h⟩ := h
    rw [sum_eq_single x, sum_eq_single c]; simp only [if_pos h,cart, if_pos hx,part_send,↓reduceIte]
    · intro b _ hb; simp [hb]
    · simp
    · intro y _ hy
      have ht : ¬ Poly.merges a b y := fun H => hy (Subtype.ext (H.2.symm.trans hx.2))
      simp [cart,ht]
    simp
  refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
  by_cases hh : y=c
  · subst y
    rw [cart]; split_ifs with he hz; exact False.elim (h ⟨_,hz,he⟩)
    all_goals simp
  simp [hh]

lemma atom_assoc (a b c : R.Mode) (i j k:A) : prod (prod (send a i) (send b j)) (send c k)=prod (send a i) (prod (send b j) (send c k)) := by
  rw [prod_commutative (send a i) (prod (send b j) (send c k))]; ext x; simp only [atom_left,Poly.three a b c]; split <;> ac_rfl

lemma prod_sum {M} (S : Finset M) (X : M → Cargo R A) (a : Cargo R A) : prod (∑ i∈S,X i) a=∑ i∈S,prod (X i) a := by
  let B : Cargo R A →+ Cargo R A := { toFun := fun i => prod i a, map_zero' := prod_commutative _ a |>.trans (no_one a), map_add' := fun x y => on_left x y a }
  exact map_sum B ..
lemma prod_sum' {M} (a : Cargo R A) (S : Finset M) (X : M → Cargo R A) : prod a (∑ i∈S,X i)=∑ i∈S,prod a (X i) := by
  rw [prod_commutative a, prod_sum]; exact sum_congr rfl fun i _ => prod_commutative (X i) a

instance : CommRing (Cargo R A) :=
  { (inferInstance : AddCommGroup (Cargo R A)) with
    mul := prod
    one := send R.quiet 1
    mul_comm := prod_commutative
    mul_one := fun a => (prod_commutative ..).trans (on_vac a)
    one_mul := on_vac
    right_distrib := on_left
    left_distrib := fun a b c => by change prod a (b+c)=prod a b+prod a c; simp_rw [prod_commutative a, on_left]
    mul_assoc := fun a b c => by
      change prod (prod a b) c=prod a (prod b c)
      rw [← studs a,← studs b, ← studs c]
      simp_rw [prod_sum,prod_sum',prod_sum,atom_assoc]
      exact sum_congr rfl fun i _ => Finset.sum_comm
    zero_mul := fun a => (prod_commutative ..).trans (no_one a)
    mul_zero := no_one }

end Cargo
end YM.Marker
