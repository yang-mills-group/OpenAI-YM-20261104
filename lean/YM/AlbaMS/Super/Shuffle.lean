import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
/-!
# Super-commuting symbols with arbitrarily labeled generators

Represent coefficients by ordered words. Reading coefficient (x::y) means
applying *left* derivative D_x then all in y. Later modules bundle these as
actual graded polynomials, accounting for finite ranks and locality through
support predicates. Here R is even. No generator finiteness requirement.
No use of Grassmann-integration intuition for expected keys; all the BV signs
will be established coefficientwise. Keep the kinetic and mark-source
variables out of this algebra for now, but ghost/antifield signs appear
at the level of `ρ : ι→Bool` where `true` is odd.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R W : Type*} [CommRing R] {E : Type*} [AddCommGroup E]

-- sign involution. use Neg operations on E directly so comm identities cheap.
def sting [Neg W] (p : Bool) (x : W) : W := if p then -x else x
@[simp] lemma sting_false [Neg W] (x : W) : sting false x=x := rfl
@[simp] lemma sting_true [Neg W] (x : W) : sting true x=-x := rfl
@[simp] lemma sting_zero (p : Bool) : sting p (0:E)=0:= by cases p <;> simp
lemma sting_add (p : Bool) (x y : E) : sting p (x+y)=sting p x+sting p y:= by cases p <;> simp [add_comm]
@[simp] lemma sting_neg (p : Bool) (x : E) : sting p (-x)=-sting p x:= by cases p <;> rfl
lemma sting_comm (p q:Bool) (x:E) : sting p (sting q x)=sting q (sting p x):= by cases p <;> cases q <;> rfl
@[simp] lemma sting_sting (p q:Bool) (x:E) : sting p (sting q x)=sting (xor p q) x:= by cases p <;> cases q <;> simp
lemma sting_mul (p:Bool) (x y:R) : sting p (x*y)=sting p x*y:=by cases p <;> simp
lemma mul_sting (p:Bool) (x y:R) : x*sting p y=sting p (x*y):=by cases p <;> simp
-- interchange sting as function application
lemma sting_apply (p:Bool) (x:W→ E) (i:W) : (sting p x) i=sting p (x i):=by cases p <;> rfl
lemma sting_smul [Module R E] (p:Bool) (c:R) (x:E) : sting p (c • x)= c • sting p x:=by cases p <;> simp

abbrev Book (ι R : Type*) := List ι → R
def band (ρ : ι→Bool) : List ι→Bool
 | []=> false
 | x::l=> xor (ρ x) (band ρ l)
@[simp] lemma band_nil (ρ : ι→Bool) : band ρ []=false:=rfl
@[simp] lemma band_cons (ρ : ι→Bool) (x : ι)(l : List ι): band ρ (x::l)=xor (ρ x) (band ρ l):=rfl
lemma band_append (ρ : ι→Bool) (l m : List ι) : band ρ (l++m)=xor (band ρ l) (band ρ m) := by induction l with|nil=>simp|cons x l ih=> simp [ih]

def detach (x : ι)(F : Book ι W): Book ι W := fun l=> F (x::l)
variable (ρ : ι→ Bool) (p q : Bool) (l : List ι) (x y : ι) (F G H : Book ι R)
omit [CommRing R] in
@[simp] lemma detach_apply : detach x F l=F (x::l):=rfl
@[simp] lemma detach_add : detach x (F+G)=detach x F+detach x G:=rfl
@[simp] lemma detach_zero : detach x (0:Book ι R)=0:=rfl
@[simp] lemma detach_neg : detach x (-F)=-detach x F:=rfl
lemma detach_smul (c:R): detach x (c • F)= c • detach x F:=rfl
lemma detach_sting : detach x (sting p F)=sting p (detach x F):=by cases p <;> rfl

def tilt (p : Bool) (F : Book ι R) : Book ι R := fun l=> sting (p && band ρ l) (F l)
@[simp] lemma tilt_zero : tilt ρ p (0:Book ι R) = 0:=funext fun _=> sting_zero _
@[simp] lemma tilt_false : tilt ρ false F = F:=rfl
@[simp] lemma tilt_add : tilt ρ p (F+G) = tilt ρ p F + tilt ρ p G := funext fun _=> sting_add _ _ _
@[simp] lemma tilt_neg : tilt ρ p (-F) = -tilt ρ p F:=funext fun _=> sting_neg _ _
lemma tilt_smul (c:R): tilt ρ p (c • F) = c • tilt ρ p F:=funext fun _=> sting_smul _ c (F _)
lemma tilt_sting : tilt ρ p (sting q F)=sting q (tilt ρ p F):=by cases q <;> simp
lemma detach_tilt : detach x (tilt ρ p F) = sting (p && ρ x) (tilt ρ p (detach x F)):=by
  ext l; simp only [detach_apply,tilt,sting_apply,band_cons]; generalize p=b; cases b <;> cases ρ x <;> cases band ρ l <;> simp
lemma tilt_comm : tilt ρ p (tilt ρ q F)=tilt ρ q (tilt ρ p F):= funext fun _=> sting_comm _ _ _
@[simp] lemma tilt_nil : tilt ρ p F []= F []:=by cases p <;> rfl

def weave (l : List ι) (F G : Book ι R) : R := match l with
 | []=> F []*G []
 | x::s=> weave s (detach x F) G+ weave s (tilt ρ (ρ x) F) (detach x G)
def deal : Book ι R:= fun l=> weave ρ l F G
@[simp] lemma deal_nil : deal ρ F G []=F []*G []:=rfl
lemma deal_cons : deal ρ F G (x::l) = deal ρ (detach x F) G l + deal ρ (tilt ρ (ρ x) F) (detach x G) l:=rfl
lemma detach_deal : detach x (deal ρ F G)=deal ρ (detach x F) G+deal ρ (tilt ρ (ρ x) F) (detach x G):=rfl
@[simp] lemma deal_add_left : deal ρ (F+G) H=deal ρ F H + deal ρ G H:=by
  ext l; induction l generalizing F G H with
  | nil=> simp [add_mul]
  | cons i l ih=> simp only [deal_cons, Pi.add_apply,detach_add,tilt_add, ih]; abel
@[simp] lemma deal_add_right : deal ρ F (G+H)= deal ρ F G+deal ρ F H:=by
  ext l; induction l generalizing F G H with
  | nil=> simp [mul_add]
  | cons i l ih=> simp only [deal_cons,Pi.add_apply,detach_add,ih]; abel
@[simp] lemma deal_zero_left : deal ρ 0 F=0:= by have h:= deal_add_left ρ 0 0 F; rw [zero_add, ← sub_eq_iff_eq_add,sub_self] at h; exact h.symm
@[simp] lemma deal_zero_right : deal ρ F 0=0:= by have h:= deal_add_right ρ F 0 0; rw [zero_add, ← sub_eq_iff_eq_add,sub_self] at h; exact h.symm
@[simp] lemma deal_neg_left : deal ρ (-F) G = -deal ρ F G := eq_neg_of_add_eq_zero_left (by rw [← deal_add_left, neg_add_cancel, deal_zero_left])
@[simp] lemma deal_neg_right : deal ρ F (-G) = -deal ρ F G := eq_neg_of_add_eq_zero_left (by rw [← deal_add_right, neg_add_cancel, deal_zero_right])
lemma deal_sting_left : deal ρ (sting p F) G = sting p (deal ρ F G):= by cases p <;> simp
lemma deal_sting_right : deal ρ F (sting p G) = sting p (deal ρ F G):= by cases p <;> simp
lemma deal_smul_left (c:R) : deal ρ (c • F) G = c • deal ρ F G:=by
  ext l; induction l generalizing F G with | nil=> simp [mul_assoc]|cons i l ih=> simp only [deal_cons, detach_smul, tilt_smul, Pi.smul_apply, ih,smul_add]
lemma deal_smul_right (c:R) : deal ρ F (c • G)=c • deal ρ F G:=by
  ext l; induction l generalizing F G with | nil=> simp [mul_left_comm]|cons i l ih=> simp only [deal_cons, detach_smul, Pi.smul_apply, ih,smul_add]
@[simp] lemma tilt_deal : tilt ρ p (deal ρ F G)=deal ρ (tilt ρ p F) (tilt ρ p G):= by
  ext l; induction l generalizing F G with
  | nil=> simp
  | cons x l ih=>
    change detach x (tilt ρ p (deal ρ F G)) l=detach x (deal ρ (tilt ρ p F) (tilt ρ p G)) l
    rw [detach_tilt,detach_deal,detach_deal,detach_tilt,detach_tilt,tilt_add,deal_sting_left,deal_sting_right,← tilt_comm ρ p (ρ x),sting_add]
    simp only [Pi.add_apply,sting_apply, ih]
lemma deal_assoc : deal ρ (deal ρ F G) H = deal ρ F (deal ρ G H) := by
  ext l; induction l generalizing F G H with
  | nil=> simp [mul_assoc]
  | cons x l ih=> simp only [deal_cons,detach_deal,tilt_deal,deal_add_left,deal_add_right,Pi.add_apply,ih, add_assoc]

end YM.MSBar.Bric
