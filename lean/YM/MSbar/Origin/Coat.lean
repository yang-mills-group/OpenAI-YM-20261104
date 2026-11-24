import YM.MSbar.Origin.Canon

/-!
# Exponent protecting field variations

Candidate master theorem for nonlinear algebra in `α` fields on whole `β`
alphabet. The exponent `B₀ + ∑e ...` and FP may then be used in site or
continuum finite form. Require purity of the original classical objects before
packing; antifields in gauge-fixing or canonical rescalings are incorporated in
later forms of comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Origin.Canon
open Function Set Filter Topology Super Finset
open scoped BigOperators
variable {α β γ : Type*} {p : β→Bool} (K : Canon α β p)
def Stand (f : Term β) := ∀ x:α,peel (K.anti x) f=0
variable {f g : Term β}
variable {K} in
section
lemma Stand.zero : K.Stand (0 : Term β) := fun _ => rfl
lemma Stand.scalar (c : ℂ) : K.Stand (scalar c) := fun _ => rfl
lemma Stand.add (h : K.Stand f) (H : K.Stand g) : K.Stand (f+g) := by intro a; rw [peel_add,h,H,add_zero]
lemma Stand.neg (h : K.Stand f) : K.Stand (-f) := by intro a; rw [peel_neg,h,neg_zero]
lemma Stand.sub (h : K.Stand f) (H : K.Stand g) : K.Stand (f-g) := by rw [sub_eq_add_neg]; exact h.add H.neg
lemma Stand.smul (h : K.Stand f) (c : ℂ) : K.Stand (c • f) := by intro a; rw [peel_smul,h,smul_zero]
lemma Stand.sum {f : γ→Term β} {s : Finset γ} (h : ∀ a∈s,K.Stand (f a)) : K.Stand (∑ a∈s,f a) := by intro a; rw [peel_sum]; exact Finset.sum_eq_zero fun i e => h i e a
lemma Stand.letter [DecidableEq β] (a : α) : K.Stand (Super.letter (K.leaf a)) := by intro b; rw [peel_letter,if_neg (K.anti_ne b a)]
lemma Stand.mix (h : K.Stand f) (H : K.Stand g) : K.Stand (Super.mix p f g) := by intro a; simp only [peel_mix,h a,H a,mix_first_zero,mix_last_zero,add_zero]
end
variable [DecidableEq β] [Fintype α]

def dress (T : α → Term β) (S : Term β) := S+ ∑ a,K.dye a • mix p (letter (K.anti a)) (T a)
def guide (T : α → Term β) (f : Term β) := ∑ a,mix p (T a) (peel (K.leaf a) f)
lemma dress_grade {T : α→Term β} {S : Term β} (H : Grade p false S) (G : ∀ a,Grade p (p (K.anti a)) (T a)) : Grade p false (K.dress T S) := H.add (Grade.sum fun i _ => Grade.smul (by simpa using (grade_letter (K.anti i)).mix (G i)) _)
lemma dress_order {T : α→ Term β} {S : Term β} (H : Ordered p S) (G : ∀ a,Ordered p (T a)) : Ordered p (K.dress T S) := H.add (Ordered.sum fun i _ => ((ordered_letter _).mix (G i) (grade_letter _)).smul _)
lemma dress_peel {T : α→Term β} {S : Term β} (h : K.Stand S) (H : ∀ a,K.Stand (T a)) (a) : peel (K.anti a) (K.dress T S)= K.dye a • T a := by
  classical
  simp only [dress, peel_add, h a, peel_sum,peel_mix,peel_smul,H _ _, mix_last_zero, add_zero, zero_add]; rw [sum_eq_single a]
  · simp
  · intro b _ hb; simp [peel_letter,Ne.symm hb]; -- ok
  simp
variable {T : α→Term β} {S : Term β}
omit [DecidableEq β] [Fintype α] in
private lemma interchange (F : Grade p false f) (a : α) : mix p (peel (K.anti a) f) (peel (K.leaf a) f)=mix p (peel (K.leaf a) f) (peel (K.anti a) f) := by
  rw [grade_mix_comm (F.peel _) (F.peel _),Bool.xor_false,Bool.xor_false,twist_comm,K.twist_neutral,one_smul]
omit [Fintype α] in
private lemma par (F : ∀ a, Grade p (p (K.anti a)) (T a)) (a b : α) :
    mix p (T a) (peel (K.leaf a) (K.dye b • mix p (letter (K.anti b)) (T b))) = - mix p (letter (K.anti b)) (mix p (T a) (peel (K.leaf a) (T b))) := by
  rw [peel_smul,(grade_letter _).peel_mix,peel_letter,if_neg (K.leaf_ne a b),mix_first_zero,zero_add,mix_smul_last,mix_smul_last, ← grade_mix_assoc (F a) (grade_letter _),grade_mix_comm (F a) (grade_letter _),mix_smul_first, grade_mix_assoc (grade_letter _) (F a),smul_smul,smul_smul];
  rw [mul_rotate,K.transfer, neg_one_smul]
lemma guide_dress (F : ∀ a,Grade p (p (K.anti a)) (T a)) : K.guide T (K.dress T S)=K.guide T S - ∑ a,mix p (letter (K.anti a)) (K.guide T (T a)) := by
  simp only [guide,dress, peel_add,mix_add_last, sum_add_distrib, peel_sum,mix_sum_last, K.par F, sum_neg_distrib, sub_eq_add_neg]; congr 2; exact sum_comm
variable [DecidableEq α] [Fintype β]
lemma classical_master (F : Grade p false S) (P : K.Stand S) (G : ∀ a,Grade p (p (K.anti a)) (T a)) (E : ∀ a,K.Stand (T a)) :
    (1/2:ℂ) • cross p K.ties (K.dress T S) (K.dress T S)= K.guide T S -∑ a,mix p (letter (K.anti a)) (K.guide T (T a)) := by
  rw [←K.guide_dress G,K.evenPair (K.dress_grade F G)]; simp_rw [← K.interchange (K.dress_grade F G), K.dress_peel P E, mix_smul_first,smul_smul, K.dye_symm,one_smul]; unfold guide; module
lemma classical_derivative (F : Grade p false S) (P : K.Stand S) (G : ∀ a,Grade p (p (K.anti a)) (T a)) (E : ∀ a,K.Stand (T a)) (H : K.Stand f) : cross p K.ties (K.dress T S) f = K.guide T f := by
  simp_rw [K.evenPair (K.dress_grade F G), K.dress_peel P E,H _,mix_last_zero, mix_smul_first,smul_zero,smul_smul, K.dye_symm, one_smul, sum_const_zero, zero_add]; rfl
lemma classical_trace (F : Ordered p S) (P : K.Stand S) (G : ∀ a,Ordered p (T a)) (E : ∀ a,K.Stand (T a)) : bell K.ties (K.dress T S)=∑ a,peel (K.leaf a) (T a) := by
  simp only [K.bell_tie (K.dress_order F G),K.dress_peel P E,peel_smul,smul_smul,K.dye_symm,one_smul]
variable {K} in
omit [DecidableEq β] in
lemma Stand.bell (F : Ordered p f) (G : K.Stand f) : bell K.ties f=0 := by simp only [K.bell_tie F,G _,peel_zero,smul_zero,sum_const_zero]
variable {K} in
omit [DecidableEq β] in
lemma Stand.cross (F : Grade p false f) (G : K.Stand f) (H : K.Stand g) : cross p K.ties f g=0 := by simp only [K.evenPair F,G _,H _,mix_first_zero,mix_last_zero,smul_zero,sum_const_zero,add_zero]
end YM.MSBar.Origin.Canon
