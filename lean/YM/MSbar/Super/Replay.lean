import YM.MSbar.Super.Drift

/-!
# Replaying a list polynomial on a changed alphabet

Apply pinned linear substitution, including to interpreted Grassmann series. No dependency
on term leg bounds. Use row convention for `a` (start alphabet) expanded from the `b` legs.
Not assumed invertible, as it'll be used across lattice sites & over-covered alias samples too.
Target alphabet can actually be infinite for use as real momentum kernels. Grade and ordering
applicable throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function Finset
open scoped BigOperators
variable {α β γ : Type*} {p : α → Bool} {q : β → Bool}

abbrev Slots (α β : Type*) := α → β → ℂ
def Slots.Avoid (p : α → Bool) (q : β → Bool) (u : Slots α β) := ∀ a b,u a b≠0 → p a=q b

section
variable [Fintype α] (u : Slots α β)
def rehearse (u : Slots α β) (L : List β) (f : Term α) : ℂ :=
   List.recOn L (motive:=fun _ => Term α → ℂ) (fun f => f []) (fun b _ ih f => ∑ a,u a b * ih (peel a f)) f

@[simp] lemma rehearse_nil (f : Term α) : rehearse u [] f=f [] := rfl
lemma rehearse_cons (b : β) (L : List β) (f : Term α) : rehearse u (b::L) f=∑ a,u a b*rehearse u L (peel a f) := rfl
lemma rehearse_add (f g : Term α) (L : List β) : rehearse u L (f+g)=rehearse u L f+rehearse u L g := by induction L generalizing f g <;> simp_all [rehearse_cons,peel_add,mul_add,sum_add_distrib]
lemma rehearse_smul (f : Term α) (L : List β) (c : ℂ) : rehearse u L (c • f)=c • rehearse u L f := by induction L generalizing f <;> simp_all [rehearse_cons,peel_smul,mul_left_comm _ c,mul_sum]

def replay (u : Slots α β) : Term α →ₗ[ℂ] Term β where
  toFun f := fun L => rehearse u L f
  map_add' f g := funext fun L => rehearse_add u f g L
  map_smul' c f := funext fun L => rehearse_smul u f L c
@[simp] lemma replay_nil (f : Term α) : replay u f []= f [] := rfl
lemma replay_cons (f : Term α) (b) (L) : replay u f (b::L)=∑ a,u a b * replay u (peel a f) L := rehearse_cons ..
lemma peel_replay (f : Term α) (b : β) : peel b (replay u f)=∑ a,u a b • replay u (peel a f) := by funext L; simp only [Finset.sum_apply,Pi.smul_apply, peel_apply,smul_eq_mul]; exact replay_cons ..
lemma replay_reindex (f : Term α) (φ : γ → β) (L : List γ) : replay u f (L.map φ)=replay (fun a b => u a (φ b)) f L := by induction L generalizing f <;> simp_all only [List.map_nil,List.map_cons,replay_cons,replay_nil]
lemma replay_factor (f : Term α) (g : β→ℂ) (L : List β) : replay (fun a b => g b*u a b) f L=(L.map g).prod*replay u f L := by
  induction L generalizing f <;> (simp_all only [List.map_nil,List.prod_nil,List.map_cons,List.prod_cons,replay_nil,replay_cons,one_mul]); rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
@[simp] lemma replay_scalar (c : ℂ) : replay u (scalar c)=scalar c := by funext L; cases L <;> simp [replay_cons, scalar]

variable {u} {f g : Term α}
lemma Grade.replay (r : Bool) (h : Grade p r f) (T : Slots.Avoid p q u) : Grade q r (replay u f) := by
  intro L e; induction L generalizing f r with
  | nil => exact h [] e
  | cons b L ih =>
      rw [replay_cons]; apply sum_eq_zero; intro a _; by_cases he : u a b=0
      · rw [he,zero_mul]
      · rw [ih ((p a).xor r) (h.peel a),mul_zero]; intro j; apply e; rw [parity_cons,j, T _ _ he]; simp
lemma Ordered.replay (h : Ordered p f) (T : Slots.Avoid p q u) : Ordered q (replay u f) := by
  intro L x y A; induction L generalizing f with
  | nil =>
      simp only [List.nil_append];
      simp_rw [replay_cons]
      simp only [mul_sum]; rw [sum_comm]
      apply sum_congr rfl; intro a ha; apply sum_congr rfl; intro b hb
      by_cases e : u b x=0 <;> by_cases H : u a y=0
      any_goals solve | simp_all only [mul_zero, zero_mul]
      rw [← T _ _ e, ← T _ _ H,h.exchange b a,map_smul]; simp only [Pi.smul_apply,smul_eq_mul]; ring
  | cons x L ih =>
      simp only [List.cons_append,replay_cons, mul_sum]; apply sum_congr rfl; intro a ha; rw [ih (h.peel a)]; ring
lemma replay_spin (d : Bool) (f : Term α) (T : Slots.Avoid p q u) : replay u (spin p d f)=spin q d (replay u f) := by
  have hp (p : α→Bool) (x) (f : Term α) : peel x (spin p d f)=twist d (p x) • spin p d (peel x f) := by
    funext L; simp only [peel_apply,spin,parity_cons,twist_xor',mul_assoc,Pi.smul_apply,smul_eq_mul]
  funext L; induction L generalizing f with
  | nil => rfl
  | cons b L ih =>
    rw [replay_cons]; simp only [hp,map_smul, Pi.smul_apply, smul_eq_mul, ih, spin, replay_cons, parity_cons, twist_xor',mul_sum]; apply sum_congr rfl; intro a ha; by_cases e : u a b=0
    · rw [e, zero_mul, zero_mul,mul_zero]
    · rw [T _ _ e]; ring
lemma replay_mix (f g : Term α) (T : Slots.Avoid p q u) : replay u (mix p f g)=mix q (replay u f) (replay u g) := by
  funext L; induction L generalizing f g with
  | nil => rfl
  | cons b L ih =>
    rw [←peel_apply b (mix q (replay u f) (replay u g)) L]
    rw [replay_cons, peel_mix, peel_replay, peel_replay]; simp only [peel_mix, map_add,mix_sum_first,mix_sum_last,Pi.add_apply,mul_add,sum_add_distrib,Finset.sum_apply, mix_smul_first,mix_smul_last,Pi.smul_apply,smul_eq_mul]; congr 1
    · apply sum_congr rfl; intro a _; exact congrArg (u a b* ·) (ih ..)
    · apply sum_congr rfl; intro a ha; by_cases e : u a b=0
      · rw [e, zero_mul, zero_mul]
      rw [T _ _ e, ←replay_spin _ _ T, ← ih]
end
end YM.MSBar.Super
