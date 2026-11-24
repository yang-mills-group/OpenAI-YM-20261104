import YM.AlbaMS.Super.Shuffle
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
Symmetric polynomials/formal super series. Not the commuting power series
ring. No reliance on characteristic except where specified (for BV/descendants
we'll use over the reals and with a rank cap). build K-algebra. Function
readout with left derivative convention at each letter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R E : Type*} [CommRing R] {ρ : ι→Bool} (p q : Bool)
variable {F G : Book ι R} (l : List ι) (x y : ι)

-- no rank restriction baked in
def Concord (ρ : ι→ Bool) (F : Book ι R) : Prop := ∀ a l i j,F (a++i::j::l)=sting (ρ i && ρ j) (F (a++j::i::l))
namespace Concord
variable (H : Concord ρ F)
lemma zero : Concord ρ (0:Book ι R):= fun _ _ _ _=> (sting_zero _).symm
lemma add {F G:Book ι R} (h : Concord ρ F)(H: Concord ρ G): Concord ρ (F+G):= fun a l i j=> by simp only [Pi.add_apply,sting_add]; exact congr_arg₂ (·+·) (h ..) (H ..)
lemma scaleR {F:Book ι R}(h:Concord ρ F)(c:R): Concord ρ (c • F):= fun a l i j=> by
  simp only [Pi.smul_apply,smul_eq_mul,← mul_sting]; exact congr_arg (fun x=> c*x) (h ..)
lemma neg {F:Book ι R}(h:Concord ρ F): Concord ρ (-F):=fun a l i j=> by simp only [Pi.neg_apply,sting_neg];exact congr_arg Neg.neg (h ..)
lemma stinged (h:Concord ρ F): Concord ρ (sting p F):=by cases p; exact h;exact h.neg
lemma det (h:Concord ρ F): Concord ρ (detach x F):= fun a l=> h (x::a) l
lemma top (h:Concord ρ F): detach x (detach y F)=sting (ρ y && ρ x) (detach y (detach x F)):= funext fun l=> by rw [sting_apply];exact h [] _ _ _
lemma tilted (h:Concord ρ F): Concord ρ (tilt ρ p F) := by
  intro a l i j; unfold tilt; rw [sting_comm (ρ i && ρ j)]
  rw [h a l i j,show band ρ (a++i::j::l)=band ρ (a++j::i::l) from ?_]
  simp only [band_append,band_cons]; cases ρ i <;> cases ρ j <;> cases band ρ a <;> cases band ρ l <;> rfl
lemma dealt (h:Concord ρ F)(H:Concord ρ G): Concord ρ (deal ρ F G) := by
  intro a l i j; induction a generalizing F G with
  | nil=>
    simp only [List.nil_append];
    have hu : detach j (detach i (deal ρ F G)) = sting (ρ i && ρ j) (detach i (detach j (deal ρ F G))):=by
      simp only [detach_deal,detach_add,detach_tilt]
      rw [h.top j i,H.top j i,tilt_comm ρ (ρ j) (ρ i)];simp only [deal_sting_left,deal_sting_right]
      cases ρ i <;> cases ρ j <;> simp only [Bool.and_self, Bool.and_false,Bool.false_and, sting_false,sting_true] <;> abel
    simpa only [sting_apply,detach_apply] using congr_fun hu l
  | cons x a ih=>
    simp only [List.cons_append,deal_cons,sting_add];exact congr_arg₂ (·+·) (ih (h.det x) H) (ih (h.tilted _) (H.det x))
end Concord

def peace (c : R) : Book ι R
| []=>c
| _::_=>0
lemma peaceful (c : R) : Concord ρ (peace c):= by intro a l i j; cases a <;> exact (sting_zero _).symm
lemma peace_equal (c : R) : tilt ρ p (peace c)=peace c := by ext l; cases l; exact tilt_nil ..; exact sting_zero _
lemma deal_peace (F : Book ι R)(c : R) : deal ρ (peace c) F=c • F:=by
  ext l; induction l generalizing F with | nil=> rfl|cons x l ih=> rw [deal_cons,peace_equal,show detach x (peace c)=0 from rfl, deal_zero_left,ih]; exact zero_add _
lemma peace_deal (F : Book ι R)(c : R): deal ρ F (peace c)=c • F:=by
  ext l; induction l generalizing F with|nil=>exact mul_comm ..|cons x l ih=>rw [deal_cons,show detach x (peace c)=0 from rfl,deal_zero_right,ih]; exact add_zero _

def vestry (ρ : ι→Bool)(R : Type*) [CommRing R] : Submodule R (Book ι R) where
  carrier F:= Concord ρ F
  zero_mem':= Concord.zero
  add_mem' := Concord.add
  smul_mem' c _ h:= Concord.scaleR h c
abbrev Coil (ρ : ι→Bool) (R : Type*) [CommRing R] := ↥(vestry ρ R)

namespace Coil
variable (F G H : Coil ρ R)
instance : FunLike (Coil ρ R) (List ι) R := ⟨Subtype.val,Subtype.coe_injective⟩
@[ext] lemma ext (h : ∀ i,F i=G i) : F=G := Subtype.ext (funext h)
lemma trusted : Concord ρ (⇑F) := F.2
instance : Mul (Coil ρ R) := ⟨fun F G=> ⟨deal ρ F G,F.trusted.dealt G.trusted⟩⟩
@[simp] lemma zero_apply (l : List ι) : (0:Coil ρ R) l=0:=rfl
@[simp] lemma plus_read : (F+G) l = F l+ G l:=rfl
@[simp] lemma neg_read : (-F) l = -(F l):=rfl
@[simp] lemma sub_read : (F-G) l= F l-G l:=rfl
@[simp] lemma smul_read (c:R): (c • F) l=c*F l:=rfl
lemma form : ⇑(F*G)=deal ρ F G:=rfl
def put (ρ : ι→Bool) (c:R): Coil ρ R:=⟨peace c,peaceful _⟩
@[simp] lemma put_add (c d:R) : put ρ (c+d)=put ρ c+put ρ d:= ext _ _ (fun l=> by cases l; rfl;exact (zero_add (0:R)).symm)
@[simp] lemma put_zero : put ρ (0:R)=0:= ext _ _ (fun l=> by cases l <;> rfl)
lemma put_smul_left (c:R): put ρ c * F= c • F:= Subtype.ext (deal_peace ..)
lemma put_smul_right (c:R): F* put ρ c=c • F:= Subtype.ext (peace_deal ..)

instance : Ring (Coil ρ R) where
  one:= put ρ 1
  natCast n:= put ρ (n:R)
  intCast n:= put ρ (n:R)
  natCast_zero := by change put ρ ((0:ℕ):R) = 0; simp
  natCast_succ n := by change put ρ ((n+1:ℕ):R)=_; rw [Nat.cast_add,Nat.cast_one, put_add];rfl
  intCast_ofNat n:= by change put ρ (((n:ℤ)):R)=put ρ _; simp
  intCast_negSucc n:= by
    change put ρ ((Int.negSucc n:R))= -put ρ _; rw [eq_neg_iff_add_eq_zero,← put_add]; simp
  left_distrib F G H:= Subtype.ext (deal_add_right ..)
  right_distrib F G H:= Subtype.ext (deal_add_left ..)
  zero_mul F:= Subtype.ext (deal_zero_left ..)
  mul_zero F:= Subtype.ext (deal_zero_right ..)
  mul_assoc F G H:= Subtype.ext (deal_assoc ..)
  one_mul a:= (put_smul_left ..).trans (one_smul ..)
  mul_one a:= (put_smul_right ..).trans (one_smul ..)
instance : Algebra R (Coil ρ R) where
  algebraMap:= { toFun:= put ρ, map_mul':= fun c d=>by
                   rw [put_smul_left]; exact ext _ _ fun i=> by cases i; rfl; exact (mul_zero c).symm
                 map_add':=put_add, map_zero':=put_zero,map_one':= rfl }
  commutes' c F:= (put_smul_left ..).trans (put_smul_right ..).symm
  smul_def' c F := (put_smul_left F c).symm
end Coil
end YM.MSBar.Bric
