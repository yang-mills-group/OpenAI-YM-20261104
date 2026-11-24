import YM.MSbar.Super.Replay
import YM.MSbar.Super.Point

/-!
# Substitute operators in the formal field alphabet

Both moment and covariant substitution. Use to go from sites to plate and
compare the same kernel operations, avoiding choosing an exact BZ spectrum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function Finset
open scoped BigOperators
variable {α β γ : Type*} {p : α → Bool} {q : β → Bool}
section
variable [Fintype α] (u : Slots α β)
lemma peel_eq_term (f g : Term β) (e : f []=g []) (h : ∀ b,peel b f=peel b g) : f=g := by funext L; cases L with | nil => exact e | cons x L => exact congrFun (h x) L
variable [Fintype β]
def slotsBridge (u : Slots α β) (v : Slots β γ) : Slots α γ := fun a c => ∑ b,u a b*v b c
lemma replay_comp (v : Slots β γ) (f : Term α) : replay (slotsBridge u v) f=replay v (replay u f) := by
  funext L; induction L generalizing f with
  | nil => rfl
  | cons a L ih =>
    simp only [replay_cons, ih, peel_replay, map_sum,map_smul, Finset.sum_apply, Pi.smul_apply,mul_sum,slotsBridge,sum_mul,smul_eq_mul]; rw [sum_comm]
    apply sum_congr rfl; intro b _; apply sum_congr rfl; intro x _; ring

section
variable [DecidableEq α] [DecidableEq β]
lemma replay_letter (a : α) : replay u (letter a)=∑ b,u a b • letter b := by
  apply peel_eq_term _ _ (by simp); intro b; rw [peel_replay,sum_eq_single a,peel_letter_self,replay_scalar,peel_sum,sum_eq_single b, peel_smul,peel_letter_self]
  · simp +contextual [peel_smul,peel_letter,Ne.symm]
  · simp
  · simp +contextual [peel_letter]
  simp
lemma replay_tether (S : Mask α) (a : α) : replay u (tether S a)=∑ b,slotsBridge S u a b • letter b := by
  simp only [tether,map_sum,map_smul,replay_letter,smul_sum,smul_smul,slotsBridge,sum_smul]; rw [sum_comm]
end

def slotsPipe (u : Slots α β) (D : Mask β) : Mask α := fun x y => ∑ a : β,∑ b : β,u x a*u y b*D a b
lemma replay_bell (D : Mask β) (f : Term α) : replay u (bell (slotsPipe u D) f)=bell D (replay u f) := by
  simp only [bell,bellMask,map_sum,map_smul,peel_replay,peel_sum,peel_smul,sum_smul,smul_sum,smul_smul,slotsPipe,sum_div]
  funext L; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; -- reorganize 4 sums by lemma
  -- l x y a b; r a b x y
  conv_lhs => rhs; ext x; rw [sum_comm]; rhs; ext a; rw [sum_comm]
  rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_comm]; apply sum_congr rfl; intro b _; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring

variable {u}
omit [Fintype α] in
lemma Access.pipe {d : Bool} {D : Mask β} (J : Slots.Avoid p q u) (H : Access q d D) : Access p d (slotsPipe u D) := by
  intro x y h; by_contra hn; apply h; apply sum_eq_zero; intro a _; apply sum_eq_zero; intro b _
  by_cases e : D a b=0 <;> by_cases s : u x a=0 <;> by_cases t : u y b=0
  any_goals solve | simp_all only [mul_zero, zero_mul]
  exact (hn (by rw [J _ _ s,J _ _ t,H _ _ e])).elim
omit [Fintype α] in
lemma Exchange.pipe {D : Mask β} (J : Slots.Avoid p q u) (E : Exchange q D) : Exchange p (slotsPipe u D) := by
  intro x y; unfold slotsPipe; rw [sum_comm]; simp only [mul_sum]; apply sum_congr rfl; intro b _; apply sum_congr rfl; intro a _
  by_cases e : u x a=0 <;> by_cases h : u y b=0
  any_goals solve | simp_all only [mul_zero,zero_mul]
  rw [E, J _ _ e,J _ _ h]; ring
lemma replay_cross {d r : Bool} {D : Mask β} {f : Term α} (F : Grade p r f) (g : Term α)
    (J : Slots.Avoid p q u) (H : Access q d D) (E : Exchange q D) : replay u (cross p (slotsPipe u D) f g)=cross q D (replay u f) (replay u g) := by
  have h := congrArg (replay u) (F.bell_mix (H.pipe J) (E.pipe J) g)
  simp only [replay_mix _ _ J,map_add,map_smul,replay_bell] at h
  rw [(F.replay r J).bell_mix H E] at h; exact add_left_cancel h.symm

lemma replay_ride (J : Slots.Avoid p q u) {B : Drive α} {T : Drive β} (E : ∀ a,replay u (B a)=∑ b,u a b • T b) (f : Term α) : replay u (ride p B f)=ride q T (replay u f) := by
  simp only [ride,map_sum,replay_mix _ _ J,E,mix_sum_first,mix_smul_first, peel_replay, mix_sum_last,mix_smul_last]; rw [sum_comm]
lemma replay_drift [DecidableEq α] [DecidableEq β] (J : Slots.Avoid p q u) {S : Mask α} {R : Mask β} (e : slotsBridge S u=slotsBridge u R) (f : Term α) : replay u (ride p (tether S) f)=ride q (tether R) (replay u f) := by
  apply replay_ride J _ f; intro a; rw [replay_tether,e]; unfold tether slotsBridge; simp only [sum_smul,smul_sum,smul_smul]; rw [sum_comm]
end
end YM.MSBar.Super
