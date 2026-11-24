import YM.FormalBulk08.Chapel.Ago

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Lattice Laurent Rift Gorge Function Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {A V E: Type*}[Fintype A][AddCommGroup E][Module ℝ E]

lemma step_nearer (w : Wand A)(h:w≠0): ∃ i:A, size (w-buzz i)+1=size w ∨ size (w+buzz i)+1=size w := by
    obtain ⟨i,hi⟩:=Function.ne_iff.mp h;change w i≠0 at hi; use i; let I:=(Finset.univ: Finset A).erase i
    have hh (a:Wand A): size a=(a i).natAbs+∑ j∈I,(a j).natAbs := (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rcases lt_or_gt_of_ne hi with he|he
    · right; rw [hh,hh w,show (∑ j∈I,((w+buzz i) j).natAbs)= _ from (show _ = ∑ j∈I,(w j).natAbs from Finset.sum_congr rfl fun j hj=> by simp [buzz,Finset.ne_of_mem_erase hj]),Pi.add_apply, show buzz i i=1 by simp [buzz]]; omega
    left; rw [hh,hh w,show (∑ j∈I,((w-buzz i) j).natAbs)=∑ j∈I,(w j).natAbs from Finset.sum_congr rfl fun j hj=> by simp [buzz,Finset.ne_of_mem_erase hj],Pi.sub_apply, show buzz i i=1 by simp [buzz]]; omega
-- polym budget operator
variable (B : E→ℝ→ Prop) (plus : ∀ x y a b,B x a→B y b→ B (x+y) (a+b)) (minus : ∀ x a,B x a→B (-x) a) (tilt : ∀ x a b, B x a→a ≤ b→ B x b) (base:B 0 0)
    (C : ℝ)(hc:0≤C)
include plus minus base
omit [Module ℝ E] tilt hc in
lemma one_path (U:Wand A→E)(L:ℕ)(w : Wand A)(he:size w ≤ L)(hz:U 0=0)(H:∀ i x,size x ≤ L →size (x+buzz i)≤L →B (booth U i x) C): B (U w) (size w*C) := by
    generalize hi:size w=k; rw [hi] at he; induction k using Nat.strong_induction_on generalizing w with
    | _ k h'=>
      by_cases ht:w=0
      · subst w; rw [hz, ←hi]; simp only [size, Pi.zero_apply, Int.natAbs_zero,Finset.sum_const_zero,Nat.cast_zero,zero_mul]; exact base
      obtain ⟨a,h|h⟩:= step_nearer w ht
      · let x:=w-buzz a; have hx:x+buzz a=w:=sub_add_cancel ..
        have hy:size x+1=k:= h.trans hi; have hd:= H a x (by omega) (by rw [hx,hi];exact he)
        have hp:= plus _ _ _ _ hd (h' (size x) (by omega) x (by omega) rfl)
        unfold booth at hp;rw [sub_add_cancel,hx] at hp; rw [←hy]; push_cast;rw [add_mul,one_mul,add_comm];exact hp
      let x:=w+buzz a; have hy:size x+1=k:=h.trans hi; have hd:=H a w (by rw [hi];exact he) (show size x≤L by omega)
      have hp:= plus _ _ _ _ (minus _ _ hd) (h' (size x) (by omega) x (by omega) rfl)
      unfold booth at hp; rw [neg_sub,show (w+_)=x from rfl,sub_add_cancel] at hp; rw [←hy];push_cast;rw [add_mul,one_mul,add_comm]; exact hp
-- mean value with Taylor remainder
include tilt hc
lemma sharp (U:Wand A→E)(d L:ℕ)(p:Wand A)(hp:size p≤L)(h:∀ l:List A,l.length=d→∀ q,size q≤L →B (gang U l q) C): B (U p-party d U p) (L^d*C):= by
    induction d generalizing U p with
    | zero=> rw [party,trim_nil,Finset.sum_empty,sub_zero,pow_zero,one_mul]; exact h [] rfl p hp
    | succ d ih=>
       let F : Wand A→ E:=U-party (d+1) U
       have hz:F 0=0:=by simp [F,party_corner (Nat.zero_lt_succ d)]
       have he (i:A) (x:Wand A): booth F i x=booth U i x-party d (booth U i) x:= by rw [←party_game d U i]; unfold booth F;simp only [Pi.sub_apply];abel
       have hs (i:A)(x:Wand A)(hx:size x≤L): B (booth F i x) (L^d*C):= by
           rw [he]; apply ih (booth U i) x hx
           intro l hl q hq; rw [gang_booth]; exact h (i::l) (by simp [hl]) q hq
       have hx:=one_path B plus minus base (L^d*C) F L p hp hz (fun i x hx _=>hs i x hx)
       apply tilt _ _ _ hx; rw [pow_succ',mul_assoc]
       exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (by positivity)
-- especially
variable {η : ℝ}{m : ℕ}
omit plus minus tilt base in
lemma climb_sharp {U: Wand A→Tile V m} (d : ℕ) (w:Wand A)(D: Reach V)(a:V) (H : ∀ l: List A,l.length=d→∀ x,size x≤size w → Knoxville D η a (gang U l x) C):
    Knoxville D η a (U w-party d U w) ((↑(size w) : ℝ)^d*C):= by
    apply sharp (Knoxville D η a) (fun x y b c hx hy=>hx.add hy) _ (fun x b t hx e=> hx.mono e) (Knox_zeros a) C hc U d _ w le_rfl H
    intro x b hx; simpa only [neg_one_smul,abs_neg,abs_one, one_mul] using hx.smul (-1)
end YM.FormalBulk08.Chapel
