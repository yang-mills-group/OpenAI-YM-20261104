import YM.MSbar.Super.Term

/-!
# Shuffle product

Establish the skin rule for left derivatives on Term. Give both sign-automorphism
and homogeneous sign formulations. As needed build associative graded commutative
calculus. Lemmas are stated also in mixed grades to avoid lifting sign hypotheses in
bracket transformations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function Finset
open scoped BigOperators
variable {α β : Type*} (p : α → Bool)
def spin (b : Bool) (f : Term α) : Term α := fun L => twist b (parity p L)*f L
@[simp] lemma spin_false (f : Term α) : spin p false f=f := by ext; simp [spin]
lemma spin_eq {r : Bool} {f : Term α} (b : Bool) (h : Grade p r f) : spin p b f = twist b r • f := by
  ext L; by_cases e : parity p L=r
  · simp [spin,e]
  · simp [spin,h L e]

def mix (f g : Term α) : Term α := fun L => divide p L fun A B => f A*g B
@[simp] lemma mix_nil (f g : Term α) : mix p f g []=f [] * g [] := rfl
lemma peel_mix (x) (f g : Term α) : peel x (mix p f g)=mix p (peel x f) g+mix p (spin p (p x) f) (peel x g) := by
  ext L; simp only [Pi.add_apply,peel_apply,spin,mix,divide,mul_assoc]
lemma mix_add_first (f g h : Term α) : mix p (f+g) h = mix p f h + mix p g h := by
  ext L; simp only [Pi.add_apply,mix,add_mul,divide_add]
lemma mix_add_last (f g h : Term α) : mix p f (g+h) = mix p f g + mix p f h := by
  ext L; simp only [Pi.add_apply,mix,mul_add,divide_add]
lemma mix_smul_first (f g : Term α) (c : ℂ) : mix p (c • f) g = c • mix p f g := by
  ext L; simp only [Pi.smul_apply,smul_eq_mul,mix,mul_assoc,divide_factor]
lemma mix_smul_last (f g : Term α) (c : ℂ) : mix p f (c • g) = c • mix p f g := by
  ext L; simp only [Pi.smul_apply,smul_eq_mul,mix,mul_left_comm (f _) c,divide_factor]
@[simp] lemma mix_first_zero (f : Term α) : mix p 0 f=0 := by simpa using mix_smul_first p f f 0
@[simp] lemma mix_last_zero (f : Term α) : mix p f 0=0 := by simpa using mix_smul_last p f f 0
lemma mix_sum_first (f : β→Term α) (g : Term α) (s : Finset β) : mix p (∑ b∈s,f b) g=∑ b∈s,mix p (f b) g :=
  map_sum (AddMonoidHom.mk' (mix p · g) (fun _ _ => mix_add_first ..)) ..
lemma mix_sum_last (f : Term α) (g : β → Term α) (s : Finset β) : mix p f (∑ b∈s,g b)=∑ b∈s,mix p f (g b) :=
  map_sum (AddMonoidHom.mk' (mix p f) (mix_add_last p f)) ..
lemma mix_sub_first (f g h : Term α) : mix p (f-g) h=mix p f h-mix p g h :=
  map_sub (AddMonoidHom.mk' (mix p · h) (fun _ _ => mix_add_first ..)) ..
lemma mix_sub_last (f g h : Term α) : mix p f (g-h)=mix p f g-mix p f h :=
  map_sub (AddMonoidHom.mk' (mix p f) (mix_add_last p f)) ..
lemma mix_neg_first (f g : Term α) : mix p (-f) g= -mix p f g := by simpa using mix_smul_first p f g (-1)
lemma mix_neg_last (f g : Term α) : mix p f (-g)= -mix p f g := by simpa using mix_smul_last p f g (-1)

variable {p} {f g h : Term α} {r s t : Bool}
lemma Grade.peel_mix (H : Grade p r f) (g : Term α) (x : α) : Super.peel x (mix p f g)=mix p (Super.peel x f) g + twist (p x) r • mix p f (Super.peel x g) := by
  rw [Super.peel_mix,spin_eq p _ H,mix_smul_first]
lemma Grade.mix (F : Grade p r f) (G : Grade p s g) : Grade p (r.xor s) (mix p f g) := by
  intro L e
  refine (divide_congr p (g:=fun _ _ =>0) ?_).trans (divide_zero ..)
  intro A B Q; by_contra he; obtain ⟨ha,hb⟩ := mul_ne_zero_iff.mp he
  apply e; rw [← parity_perm Q,parity_append,F.degree ha,G.degree hb]
lemma grade_mix_assoc (F : Grade p r f) (G : Grade p s g) (h : Term α) : mix p (mix p f g) h=mix p f (mix p g h) := by
  ext L
  induction L generalizing r s f g h with
  | nil => exact mul_assoc ..
  | cons x L ih =>
    rw [←peel_apply x (mix p (mix p f g) h), ←peel_apply x (mix p f (mix p g h))]
    rw [(F.mix G).peel_mix h,F.peel_mix g,mix_add_first,mix_smul_first,F.peel_mix (mix p g h),G.peel_mix h,
      mix_add_last,mix_smul_last]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,twist_xor',mul_assoc,mul_add]
    rw [ih (F.peel x) G h,ih F (G.peel x) h,ih F G (peel x h)]
    abel
lemma twist_rev (a b c : Bool) : twist (a.xor b) c = twist b c * twist c a := by rw [twist_xor,twist_comm c a,mul_comm]
lemma grade_mix_comm (F : Grade p r f) (G : Grade p s g) : mix p f g=twist r s • mix p g f := by
  ext L
  induction L generalizing r s f g with
  | nil =>
    by_cases e : r=false
    · simp [e,mul_comm]
    · simp [F [] (Ne.symm e)]
  | cons x L ih =>
    rw [←peel_apply x (mix p f g),←peel_apply x (twist r s • mix p g f)]
    rw [peel_smul,F.peel_mix g,G.peel_mix f]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add]; rw [ih (F.peel x) G,ih F (G.peel x)]
    -- IH already applied smuls may be printed as values
    simp only [Pi.smul_apply,smul_eq_mul,twist_xor, twist_xor', twist_comm r (p x)]
    rw [add_comm]; congr 1
    · rw [← mul_assoc,←mul_assoc,twist_mm,one_mul]
    · ring


/-- The head swaps, using left derivatives. Only the first grade needs to be fixed. -/
private lemma peel_mix2 {x y : α} (H : Grade p r f) (F : Ordered p f) (G : Ordered p g) : peel y (peel x (mix p f g))=twist (p x) (p y) • peel x (peel y (mix p f g)) := by
  rw [H.peel_mix g x, H.peel_mix g y]; simp only [peel_add,peel_smul,(H.peel x).peel_mix _ y,(H.peel y).peel_mix _ x,H.peel_mix]
  rw [F.exchange x y,G.exchange x y,mix_smul_first,mix_smul_last]
  simp only [smul_add,smul_smul,twist_xor',twist_comm (p y) (p x)]
  rw [← mul_assoc (twist (p x) (p y)) (twist (p x) (p y)),twist_mm,one_mul]
  rw [show twist (p x) r * (twist (p y) r * twist (p x) (p y)) = twist (p x) (p y) * (twist (p y) r * twist (p x) r) by ac_rfl]; abel

lemma Ordered.mix (F : Ordered p f) (G : Ordered p g) (H : Grade p r f) : Ordered p (mix p f g) := by
  intro A x y L; induction A generalizing r f g with
  | nil => exact congrFun (peel_mix2 H F G) L
  | cons a A ih =>
    change Super.peel a (Super.mix p f g) (A++_:: _:: L) = twist .. * Super.peel a (Super.mix p f g) (A++ _::_::L)
    rw [H.peel_mix]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; rw [ih (F.peel _) G (H.peel _),ih F (G.peel _) H]; ring

lemma mix_scalar_first (p : α → Bool) (c : ℂ) (f : Term α) : mix p (scalar c) f=c • f := by
  ext L; induction L generalizing f with
  | nil => rfl
  | cons x L ih =>
    rw [←peel_apply x (mix p (scalar c) f), ← peel_apply x (c • f)]
    rw [grade_scalar c |>.peel_mix f,peel_smul,peel_scalar]; simpa only [twist_false',one_smul,mix_first_zero,zero_add] using ih (peel x f)
lemma mix_scalar_last (p : α → Bool) (f : Term α) (c : ℂ) : mix p f (scalar c)=c • f := by
  ext L; induction L generalizing f with
  | nil => exact mul_comm ..
  | cons x L ih =>
    rw [←peel_apply x (mix p f (scalar c)), ← peel_apply x (c • f)]
    rw [peel_mix,peel_smul,peel_scalar]; simpa only [mix_last_zero,add_zero] using ih (peel x f)
@[simp] lemma unit_mix (p : α → Bool) (f : Term α) : mix p (scalar 1) f=f := by simp [mix_scalar_first]
@[simp] lemma mix_unit (p : α → Bool) (f : Term α) : mix p f (scalar 1)=f := by simp [mix_scalar_last]
end YM.MSBar.Super
