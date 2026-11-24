import YM.MSbar.Super.Pipe

/-!
# Canonical antifield pairings and real sites

Generic for a finite alphabet. Unit volume conventions here use
unit measuring weight in these coordinates. Signs as in the logarithmic perturbation
form, exponent and left graded derivatives. `Stand` means contains no antifield dependence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Origin
open Function Set Filter Topology Super Finset
open scoped BigOperators
variable {α β γ : Type*}

structure Canon (α β : Type*) (p : β → Bool) where
  pair : α ⊕ α ≃ β
  shift (a : α) : p (pair (.inr a))=(p (pair (.inl a))).xor true
namespace Canon
variable {p : β → Bool} (K : Canon α β p)
abbrev leaf (a : α) := K.pair (.inl a)
abbrev anti (a : α) := K.pair (.inr a)
abbrev hue (a : α) := p (K.leaf a)
theorem flips (a : α) : p (K.anti a) = (p (K.leaf a)).xor true := K.shift a
lemma instances (v : β) : (∃ a,v=K.leaf a) ∨ ∃ a, v=K.anti a := by obtain ⟨v,rfl⟩ := K.pair.surjective v; cases v with | inl a => exact Or.inl ⟨a,rfl⟩ | inr a => exact Or.inr ⟨a,rfl⟩
lemma twist_neutral (a : α) : twist (p (K.leaf a)) (p (K.anti a))=1 := by rw [K.flips]; cases p (K.leaf a) <;> simp
lemma leaf_ne (a b : α) : K.leaf a≠K.anti b := K.pair.injective.ne (by simp)
lemma anti_ne (a b : α) : K.anti a≠K.leaf b := (K.leaf_ne b a).symm
@[simp] lemma leaf_eq (a b : α) : K.leaf a=K.leaf b ↔ a=b := by simp [leaf]
@[simp] lemma anti_eq (a b : α) : K.anti a=K.anti b ↔ a=b := by simp [anti]

/-- `δ` sign is positive on even fields, negative on odd fields. -/
def dye (a : α) : ℂ := twist (p (K.leaf a)) true
lemma dye_symm (a : α) : K.dye a*K.dye a=1 := twist_mm ..
lemma transfer (a b : α) : twist (p (K.leaf a)) (p (K.anti b))*twist (p (K.anti a)) (p (K.anti b))*K.dye b= -1 := by simp only [K.flips, dye]; cases p (K.leaf a) <;> cases p (K.leaf b) <;> simp
variable [DecidableEq α]
def maskpart : α ⊕ α → α ⊕ α → ℂ
 | .inl a,.inr b | .inr a,.inl b => if a=b then K.dye a else 0
 | _,_ => 0

def ties : Mask β := fun a b => K.maskpart (K.pair.symm a) (K.pair.symm b)
@[simp] lemma ties_leaves (a b : α) : K.ties (K.leaf a) (K.leaf b)=0 := by simp [ties,leaf,maskpart]
@[simp] lemma ties_anti (a b : α) : K.ties (K.anti a) (K.anti b)=0 := by simp [ties,anti,maskpart]
@[simp] lemma ties_sway (a b : α) : K.ties (K.leaf a) (K.anti b) = if a=b then K.dye a else 0 := by simp [ties,leaf,anti,maskpart]
@[simp] lemma ties_stay (a b : α) : K.ties (K.anti a) (K.leaf b) = if b=a then K.dye b else 0 := by by_cases e : b=a <;> simp [ties,leaf,anti,e,Ne.symm,maskpart]
lemma exchange : Exchange p K.ties := by
  have he (a) : twist (p (K.anti a)) (p (K.leaf a))=1 := by rw [twist_comm,K.twist_neutral]
  intro x y; rcases K.instances x with ⟨a,rfl⟩ | ⟨a,rfl⟩ <;> rcases K.instances y with ⟨b,rfl⟩ | ⟨b,rfl⟩ <;> by_cases e : a=b <;> simp [e,K.twist_neutral,he,Ne.symm]
lemma access : Access p true K.ties := by
  intro x y; rcases K.instances x with ⟨a,rfl⟩ | ⟨a,rfl⟩ <;> rcases K.instances y with ⟨b,rfl⟩ | ⟨b,rfl⟩ <;> by_cases e : a=b <;> simp [K.flips,e,Ne.symm]

variable [Fintype α] [Fintype β]
omit [DecidableEq α] in
lemma eitherSum [AddCommMonoid γ] (f : β → γ) : (∑ b,f b)=(∑ a,f (K.leaf a))+(∑ a,f (K.anti a)) := by rw [← Equiv.sum_comp K.pair, Fintype.sum_sum_type]
lemma bell_tie {f : Term β} (h : Ordered p f) : bell K.ties f=∑ a,K.dye a • peel (K.leaf a) (peel (K.anti a) f) := by
  unfold bell; simp_rw [K.eitherSum,bellMask, ties_leaves,ties_anti,ties_sway,ties_stay]
  simp only [ite_div, ite_smul, zero_div, zero_smul,sum_const_zero, sum_ite_eq,sum_ite_eq',Finset.mem_univ,↓reduceIte, add_zero,zero_add,←sum_add_distrib,h.exchange (K.leaf _) (K.anti _),K.twist_neutral, one_smul]
  apply sum_congr rfl; intro a _; linear_combination (norm:=module)
omit [Fintype α] [Fintype β] in
lemma evenPairStep (f g : Term β) (h : Grade p false f) (a : α) :
    crossMask p K.ties (K.leaf a) (K.anti a) f g=
    K.dye a • mix p (peel (K.leaf a) f) (peel (K.anti a) g) ∧
    crossMask p K.ties (K.anti a) (K.leaf a) f g=
    K.dye a • mix p (peel (K.anti a) f) (peel (K.leaf a) g) := by rw [h.flash,h.flash]; simp only [Bool.xor_false,twist_comm (p (K.anti a)),K.twist_neutral,one_mul,K.ties_sway,K.ties_stay]; simp
lemma evenPair {f : Term β} (F : Grade p false f) (g : Term β) : cross p K.ties f g= (∑ a,K.dye a • mix p (peel (K.leaf a) f) (peel (K.anti a) g)) +(∑ a,K.dye a • mix p (peel (K.anti a) f) (peel (K.leaf a) g)) := by
  unfold cross; simp_rw [K.eitherSum];
  have hj a : (∑ x,crossMask p K.ties (K.leaf a) (K.anti x) f g)=K.dye a • mix p (peel (K.leaf a) f) (peel (K.anti a) g) := by rw [sum_eq_single a]; exact (K.evenPairStep f g F a).1; simp +contextual [crossMask,Ne.symm]; simp
  have hu a : (∑ x,crossMask p K.ties (K.anti a) (K.leaf x) f g)=K.dye a • mix p (peel (K.anti a) f) (peel (K.leaf a) g) := by rw [sum_eq_single a]; exact (K.evenPairStep f g F a).2; simp +contextual [crossMask]; simp
  simp_rw [hj,hu]; simp [crossMask]
end Canon
end YM.MSBar.Origin
