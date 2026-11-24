import YM.MSbar.Super.Mix

/-!
# Wick and BV contractions on finite modes

One mask for any pairing (Hermitian conditions separate). Use left derivatives,
so that `bellMask x y` uses `peel y` **after** `peel x`, and that with spin in
`cross` agrees exactly with `Kernel.tad` and `Kernel.join` signs under testing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function Finset
open scoped BigOperators
variable {α β : Type*} {p : α → Bool}
abbrev Mask (α : Type*) := α → α → ℂ
def Access (p : α → Bool) (d : Bool) (C : Mask α) := ∀ x y,C x y ≠ 0 → (p x).xor (p y)=d
def Exchange (p : α → Bool) (C : Mask α) := ∀ x y,C x y=twist (p x) (p y)*C y x
variable {C : Mask α} {r s d : Bool} {f g : Term α}
lemma xor_three (a b c : Bool) : a.xor (b.xor c)=b.xor (a.xor c) := by cases a <;> cases b <;> cases c <;> rfl

variable [Fintype α]
def bellMask (C : Mask α) (x y : α) (f : Term α) : Term α := (C x y / 2) • peel y (peel x f)
def bell (C : Mask α) (f : Term α) : Term α := ∑ x : α, ∑ y : α, bellMask C x y f
/-- Full cross (no halves). -/
def crossMask (p : α → Bool) (C : Mask α) (x y : α) (f g : Term α) := C x y • mix p (spin p (p y) (peel x f)) (peel y g)
def cross (p : α → Bool) (C : Mask α) (f g : Term α) : Term α := ∑ x : α,∑ y : α,crossMask p C x y f g
omit [Fintype α] in
lemma Grade.flash (F : Grade p r f) (g : Term α) (x y : α) : crossMask p C x y f g = (twist (p y) ((p x).xor r) * C x y) • Super.mix p (Super.peel x f) (Super.peel y g) := by
  rw [crossMask,spin_eq p _ (F.peel x),mix_smul_first,smul_smul,mul_comm]

lemma bell_add (C : Mask α) (f g : Term α) : bell C (f+g)=bell C f+bell C g := by simp only [bell,bellMask,peel_add,smul_add,sum_add_distrib]
lemma bell_sub (C : Mask α) (f g : Term α) : bell C (f-g)=bell C f-bell C g := by simp only [bell,bellMask,peel_sub,smul_sub,sum_sub_distrib]
lemma bell_add_mask (C D : Mask α) (f : Term α) : bell (C+D) f=bell C f+bell D f := by simp only [bell,bellMask,Pi.add_apply,add_div,add_smul,sum_add_distrib]
lemma bell_sub_mask (C D : Mask α) (f : Term α) : bell (C-D) f=bell C f-bell D f := by simp only [bell,bellMask,Pi.sub_apply,sub_div,sub_smul,sum_sub_distrib]
lemma bell_smul (C : Mask α) (f : Term α) (c : ℂ) : bell C (c • f)=c • bell C f := by simp only [bell,bellMask,peel_smul,smul_sum]; simp_rw [smul_comm (_ / _) c]
lemma bell_neg (C : Mask α) (f : Term α) : bell C (-f)= -bell C f := by simpa using bell_smul C f (-1)
lemma bell_neg_mask (C : Mask α) (f : Term α) : bell (-C) f= -bell C f := by simp only [bell,bellMask,Pi.neg_apply,neg_div,neg_smul,sum_neg_distrib]
lemma bell_sum (C : Mask α) (f : β→Term α) (s : Finset β) : bell C (∑ b∈s,f b)=∑ b∈s,bell C (f b) := map_sum (AddMonoidHom.mk' (bell C) (bell_add C)) ..
omit [Fintype α] in
lemma spin_smul (p : α → Bool) (f : Term α) (b) (c : ℂ) : spin p b (c • f)=c • spin p b f := by ext; simp [spin,mul_left_comm]
omit [Fintype α] in
lemma spin_add (p : α → Bool) (f g : Term α) (b) : spin p b (f+g)=spin p b f+spin p b g := by ext; simp [spin,mul_add]
lemma cross_add_first (p : α → Bool) (C : Mask α) (f g h : Term α) : cross p C (f+g) h=cross p C f h+cross p C g h := by
  simp only [cross,crossMask,peel_add,spin_add,mix_add_first,smul_add,sum_add_distrib]
lemma cross_add_last (p : α → Bool) (C : Mask α) (f g h : Term α) : cross p C f (g+h)=cross p C f g+cross p C f h := by
  simp only [cross,crossMask,peel_add,mix_add_last,smul_add,sum_add_distrib]
lemma cross_sub_first (p : α → Bool) (C : Mask α) (f g h : Term α) : cross p C (f-g) h=cross p C f h-cross p C g h := map_sub (AddMonoidHom.mk' (cross p C · h) (fun _ _ => cross_add_first ..)) ..
lemma cross_sub_last (p : α → Bool) (C : Mask α) (f g h : Term α) : cross p C f (g-h)=cross p C f g-cross p C f h := map_sub (AddMonoidHom.mk' (cross p C f) (cross_add_last p C f)) ..
lemma cross_add_mask (p : α → Bool) (C D : Mask α) (f g : Term α) : cross p (C+D) f g=cross p C f g+cross p D f g := by simp only [cross,crossMask,Pi.add_apply,add_smul,sum_add_distrib]
lemma cross_sub_mask (p : α → Bool) (C D : Mask α) (f g : Term α) : cross p (C-D) f g=cross p C f g-cross p D f g := by simp only [cross,crossMask,Pi.sub_apply,sub_smul,sum_sub_distrib]
lemma cross_neg_mask (p : α → Bool) (C : Mask α) (f g : Term α) : cross p (-C) f g= -cross p C f g := by simp only [cross,crossMask,Pi.neg_apply,neg_smul,sum_neg_distrib]
lemma cross_smul_first (p : α → Bool) (C : Mask α) (f g : Term α) (c : ℂ) : cross p C (c • f) g=c • cross p C f g := by
  simp only [cross,crossMask,peel_smul,spin_smul,mix_smul_first,smul_sum]; simp_rw [smul_comm (C _ _) c]
lemma cross_smul_last (p : α → Bool) (C : Mask α) (f g : Term α) (c : ℂ) : cross p C f (c • g)=c • cross p C f g := by
  simp only [cross,crossMask,peel_smul,mix_smul_last,smul_sum]; simp_rw [smul_comm (C _ _) c]
@[simp] lemma bell_zero (C : Mask α) : bell C 0=0 := by simp [bell,bellMask]
@[simp] lemma cross_zero_first (p : α → Bool) (C : Mask α) (f : Term α) : cross p C 0 f=0 := by simpa using cross_smul_first p C f f 0
@[simp] lemma cross_zero_last (p : α → Bool) (C : Mask α) (f : Term α) : cross p C f 0=0 := by simpa using cross_smul_last p C f f 0
lemma cross_sum_first (p : α → Bool) (C : Mask α) (f : β → Term α) (g : Term α) (s : Finset β) : cross p C (∑ b∈s,f b) g = ∑ b∈s,cross p C (f b) g := map_sum (AddMonoidHom.mk' (cross p C · g) (fun _ _ => cross_add_first ..)) ..
lemma cross_sum_last (p : α → Bool) (C : Mask α) (f : Term α) (g : β → Term α) (s : Finset β) : cross p C f (∑ b∈s,g b)=∑ b∈s,cross p C f (g b) := map_sum (AddMonoidHom.mk' (cross p C f) (cross_add_last p C f)) ..
lemma Grade.bell (F : Grade p r f) (H : Access p d C) : Grade p (d.xor r) (bell C f) := by
  apply Grade.sum; intro x hx; apply Grade.sum; intro y hy; unfold bellMask
  by_cases e : C x y=0
  · simp [e]
  · rw [← H x y e,Bool.xor_comm (p x),Bool.xor_assoc]; exact (((F.peel x).peel y).smul _)
lemma Grade.cross (F : Grade p r f) (G : Grade p s g) (H : Access p d C) : Grade p (d.xor (r.xor s)) (cross p C f g) := by
  apply Grade.sum; intro x hx; apply Grade.sum; intro y hy; rw [F.flash g]
  by_cases e : C x y=0
  · simp [e]
  · rw [← H x y e,Bool.xor_assoc,xor_three (p y),← Bool.xor_assoc]; exact (((F.peel x).mix (G.peel y)).smul _)
lemma Ordered.bell (F : Ordered p f) (C : Mask α) : Ordered p (bell C f) := Ordered.sum (fun x _ => Ordered.sum fun y _ => ((F.peel x).peel y).smul _)
lemma Ordered.cross (F : Ordered p f) (G : Ordered p g) (H : Grade p r f) (C : Mask α) : Ordered p (cross p C f g) := by
  apply Ordered.sum; intro x hx; apply Ordered.sum; intro y hy; rw [H.flash g]; exact (((F.peel x).mix (G.peel y) (H.peel x)).smul _)

omit [Fintype α] in
private lemma petal (H : Access p d C) (E : Exchange p C) (F : Grade p r f) (g : Term α) (x y) :
    bellMask C x y (mix p f g)= mix p (bellMask C x y f) g + twist d r • mix p f (bellMask C x y g) +
        ((1/2:ℂ) • crossMask p C x y f g + (1/2:ℂ) • crossMask p C y x f g) := by
  by_cases h : C x y=0
  · have hy : C y x=0 := by rw [E y x,h,mul_zero]
    simp [bellMask,crossMask,h,hy]
  rw [← H x y h]; simp only [bellMask,mix_smul_first,mix_smul_last,F.peel_mix _,peel_add,peel_smul,(F.peel x).peel_mix _,F.flash g,E y x]
  cases p x <;> cases p y <;> cases r <;> (simp; ext1; simp; ring)

lemma Grade.bell_mix (F : Grade p r f) (H : Access p d C) (E : Exchange p C) (g : Term α) :
    Super.bell C (Super.mix p f g)=Super.mix p (Super.bell C f) g+twist d r • Super.mix p f (Super.bell C g)+Super.cross p C f g := by
  unfold Super.bell; simp_rw [petal H E F g,mix_sum_first,mix_sum_last,sum_add_distrib, ← smul_sum]
  rw [sum_comm (f:=fun x y => crossMask p C y x f g)]
  unfold Super.cross; rw [← add_smul]; norm_num

lemma peel_bell (F : Ordered p f) (H : Access p d C) (x : α) : peel x (bell C f)=twist (p x) d • bell C (peel x f) := by
  simp only [bell,bellMask,peel_sum,smul_sum]; apply sum_congr rfl; intro y _; apply sum_congr rfl; intro z _
  by_cases e : C y z=0
  · simp [e]
  · rw [← H y z e,peel_smul,(F.peel y).exchange z x,F.exchange y x,peel_smul,twist_xor']
    simp only [smul_smul,twist_comm (p x) (p z),twist_comm (p x) (p y)]; congr 1; ac_rfl
lemma bell_bell (F : Ordered p f) {B : Mask α} {c} (G : Access p c B) (H : Access p d C) : bell C (bell B f)=twist d c • bell B (bell C f) := by
  change (∑ x,∑ y,bellMask C x y (bell B f))=_ • bell _ (∑ x,∑ y, bellMask C x y f)
  simp only [bell_sum,bellMask,smul_sum]; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _
  by_cases h : C x y=0
  · simp [h]
  · rw [←H x y h,peel_bell F G,peel_smul,peel_bell (F.peel x) G,bell_smul B,twist_xor,smul_smul,smul_smul,smul_smul]; congr 1; ring
@[simp] lemma bell_nilpotent (F : Ordered p f) (H : Access p true C) : bell C (bell C f)=0 := by
  have h : bell C (bell C f)= -bell C (bell C f) := by simpa using bell_bell F H H
  ext L; simp only [Pi.zero_apply]; have hx := congrFun h L; simp only [Pi.neg_apply] at hx; linear_combination hx / 2
end YM.MSBar.Super
