import YM.MSbar.Super.Bell

/-!
# Derivations and free charge variation

Ordinary fields and antifields. Use derivations on the left in product rules.
Develop the parity-charged derivative generally, compute the structural
commutator relation, and keep `Mask` for both operators and lines even though
one carries opposite paired momenta (in uses).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function Finset
open scoped BigOperators
variable {α β : Type*} {p : α → Bool}
abbrev Drive (α : Type*) := α → Term α
def Coach (p : α → Bool) (d : Bool) (T : Drive α) : Prop := ∀ x,Grade p ((p x).xor d) (T x)
def Train (p : α → Bool) (T : Drive α) : Prop := ∀ x,Ordered p (T x)

variable {f g : Term α} {d r s : Bool} {T : Drive α} {C S : Mask α}
variable [Fintype α]
/-- The coefficient multiplies the left derivative on its left. -/
def ride (p : α → Bool) (T : Drive α) (f : Term α) := ∑ x : α, mix p (T x) (peel x f)
lemma ride_add (p : α → Bool) (T : Drive α) (f g : Term α) : ride p T (f+g)=ride p T f+ride p T g := by simp only [ride,peel_add,mix_add_last,sum_add_distrib]
lemma ride_add_drive (p : α → Bool) (S T : Drive α) (f : Term α) : ride p (S+T) f=ride p S f+ride p T f := by simp only [ride,Pi.add_apply,mix_add_first,sum_add_distrib]
lemma ride_sub (p : α → Bool) (T : Drive α) (f g : Term α) : ride p T (f-g)=ride p T f-ride p T g := by simp only [ride,peel_sub,mix_sub_last,sum_sub_distrib]
lemma ride_neg (p : α → Bool) (T : Drive α) (f : Term α) : ride p T (-f)= -ride p T f := by simp only [ride,peel_neg,mix_neg_last,sum_neg_distrib]
lemma ride_smul (p : α → Bool) (T : Drive α) (f : Term α) (c : ℂ) : ride p T (c • f)=c • ride p T f := by simp only [ride,peel_smul,mix_smul_last,smul_sum]
lemma ride_sum (p : α → Bool) (T : Drive α) (f : β → Term α) (s : Finset β) : ride p T (∑ b∈s,f b)=∑ b∈s,ride p T (f b) := map_sum (AddMonoidHom.mk' (ride p T) (ride_add p T)) ..

lemma Grade.ride (F : Grade p r f) (H : Coach p d T) : Grade p (d.xor r) (ride p T f) := by
  apply Grade.sum; intro x _; convert (H x).mix (F.peel x) using 1; cases p x <;> cases r <;> cases d <;> rfl
lemma Ordered.ride (F : Ordered p f) (H : Coach p d T) (G : Train p T) : Ordered p (ride p T f) := Ordered.sum fun x _ => (G x).mix (F.peel x) (H x)
lemma Grade.ride_mix (F : Grade p r f) (H : Coach p d T) (g : Term α) : Super.ride p T (Super.mix p f g)=Super.mix p (Super.ride p T f) g+twist d r • Super.mix p f (Super.ride p T g) := by
  simp only [Super.ride,mix_sum_first,mix_sum_last,smul_sum,← sum_add_distrib]
  apply sum_congr rfl; intro x hx
  rw [F.peel_mix g,mix_add_last,mix_smul_last,grade_mix_assoc (H x) (F.peel x)]
  congr 1; rw [←grade_mix_assoc (H x) F,grade_mix_comm (H x) F,mix_smul_first,grade_mix_assoc F (H x),smul_smul,twist_xor,←mul_assoc,twist_mm,one_mul]
lemma peel_ride (F : Ordered p f) (H : Coach p d T) (x : α) : peel x (ride p T f)=ride p (fun a => peel x (T a)) f+twist (p x) d • ride p T (peel x f) := by
  simp only [ride,peel_sum,smul_sum,←sum_add_distrib]; apply sum_congr rfl; intro y hy
  rw [(H y).peel_mix (peel y f),F.exchange y x,mix_smul_last,smul_smul,twist_xor',twist_comm (p y)]; congr 2
  rw [mul_right_comm,twist_mm,one_mul]

@[simp] lemma ride_letter [DecidableEq α] (p : α → Bool) (T : Drive α) (x) : ride p T (letter x)=T x := by
  unfold ride; rw [sum_eq_single x] <;> simp +contextual [peel_letter]

variable [DecidableEq α]
def tether (S : Mask α) : Drive α := fun x => ∑ y : α, S x y • letter y
lemma tether_nil (x : α) : tether S x []=0 := by simp [tether]
lemma tether_peel (x y : α) : peel y (tether S x)=S x y • scalar 1 := by
  unfold tether; rw [peel_sum,sum_eq_single y]; rw [peel_smul,peel_letter_self]
  · intro z _ h; simp [peel_smul,peel_letter, Ne.symm h]
  · simp
lemma Access.coach (H : Access p d S) : Coach p d (tether S) := by
  intro x; apply Grade.sum; intro y _; by_cases he : S x y=0
  · simp [he]
  · rw [← H x y he]; apply Grade.smul; simp
lemma tether_train (p : α → Bool) (S : Mask α) : Train p (tether S) := fun _ => Ordered.sum fun y _ => (ordered_letter y).smul _

/-- Taylor recursion for the linear drive, in the exact sign convention of the kernels. -/
lemma drift_nil (p : α → Bool) (S : Mask α) (f : Term α) : ride p (tether S) f []=0 := by simp [tether_nil,ride]
def row (S : Mask α) (x : α) (f : Term α) := ∑ a : α, S a x • peel a f
lemma drift_peel (F : Ordered p f) (H : Access p d S) (x : α) :
    peel x (ride p (tether S) f)=row S x f+twist (p x) d • ride p (tether S) (peel x f) := by
  rw [peel_ride F H.coach]; congr 1; simp only [ride,row,tether_peel,mix_smul_first,unit_mix]

/-- Constant pairing mask, commuted with the drift. -/
def pushMask (p : α → Bool) (d : Bool) (S C : Mask α) : Mask α := fun x y => (∑ z,S x z * C z y)+(∑ z,twist (p x) d * S y z*C x z)

lemma bell_ride (F : Ordered p f) (H : Access p d S) {b} (G : Access p b C) :
    bell C (ride p (tether S) f)=twist b d • ride p (tether S) (bell C f)+bell (pushMask p d S C) f := by
  have H1 : ∀ x y,bellMask C x y (ride p (tether S) f)=twist b d • ride p (tether S) (bellMask C x y f)+
     ((∑ a : α,(S a x*C x y/2) • peel y (peel a f))+(∑ a : α,(twist (p x) d*S a y*C x y / 2) • peel a (peel x f))) := by
    intro x y; by_cases h : C x y=0
    · simp [h,bellMask,ride]
    · rw [← G x y h]; simp only [bellMask,drift_peel F H,drift_peel (F.peel x) H,peel_add,peel_smul,row,peel_sum,
              ride_smul,smul_add,smul_sum,smul_smul,twist_xor];
      simp only [mul_comm (C x y / 2) _, ← mul_div_assoc]
      abel
  unfold bell
  simp_rw [H1]; simp only [smul_sum,sum_add_distrib,ride_sum,bellMask,pushMask,add_div,sum_div,sum_smul,add_smul]
  congr 1; congr 1
  · conv_lhs => rhs; ext x; rw [sum_comm]
    rw [sum_comm]; apply sum_congr rfl; intro x hx; exact sum_comm
  · apply sum_congr rfl; intro x hx; exact sum_comm
end YM.MSBar.Super
