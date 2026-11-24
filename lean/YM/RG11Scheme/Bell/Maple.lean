import YM.RG11Scheme.Bell.Slices

/-! Surjective onto polynomial charges without leaving native polynomial gauge. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Bell
open Function Set Filter Lattice Stencil Stencil.Point Stencil.Shot Mesh
open scoped Classical Topology BigOperators
variable {E:Type}[AddCommGroup E][Module ℝ E] {f q:Cover→ E} {A D:List Axis} {p:ℕ}
local notation "τ" => (0:Axis)
local notation "t'" => (step τ:Cover)
omit [Module ℝ E] in
lemma stop_eq (i:Axis)(x:Cover): stoptime f i x=go [i,i] f (x-step i) := by simp only [stoptime,onwards,starting,sub_add_cancel];abel
omit [Module ℝ E] in
lemma pine_eq (i:Axis): go D (stoptime f i)=stoptime (go D f) i:= by
   induction D with
   | nil=>exact rfl
   | cons a D IH=> funext x;rw [onwards, IH];unfold stoptime; simp only [onwards]; rw [add_right_comm x (step a),show x+step a-step i=x-step i+step a by abel];abel
lemma vigor (A:List Axis)(q:Cover→ E): quake (go A q)=go A (quake q):= by
   have he (q:Cover→E): quake q=∑ i:Axis, stoptime q i := funext fun x=>by unfold quake; rw [Finset.sum_apply]; rfl
   rw [he,he]; change _=ladder A (∑ _,_); rw [map_sum]; exact Finset.sum_congr rfl fun i _=>pine_eq i |>.symm
omit [Module ℝ E] in
lemma dried {x:ℤ}(h:∀ p,p τ=x→f p=0) {D:List Axis} (ht:τ∉D) : ∀ p,p τ=x → go D f p=0:= by
   induction D with
   | nil=>exact h
   | cons a D IH=> intro p hp; rw [onwards]; simp only [List.mem_cons,not_or] at ht;rw [IH ht.2 _ ((step_up p a (Ne.symm ht.1)).trans hp), IH ht.2 p hp, sub_self]
lemma tangency (h₁:∀ x,x τ=0 → q x=0)(h₂:∀ x,x τ=1 → q x=0)(hq:quake q∈hill E p) (h:D.length>p) (hi:τ∉ D): go D q=0 := inhabit _ ((vigor D q).trans (hq _ h)) (dried h₁ hi) (dried h₂ hi)
theorem membrane (h₁:∀ x,x τ=0 → q x=0)(h₂:∀ x,x τ=1 → q x=0)(hq:quake q∈hill E p) : q∈ hill E (p+2) := by
   intro D hd; generalize he: D.count τ=j
   induction j using Nat.strong_induction_on generalizing D with
   | h j IH =>
      by_cases hi:τ∉D
      · exact tangency h₁ h₂ hq (by omega) hi
      push Not at hi
      let C:=D.erase τ; have hc:= List.perm_cons_erase hi; have hC : C.length+1=D.length:= hc.length_eq.symm
      by_cases ha:τ∉C
      · rw [shuffle D (τ::C) q hc]; funext x; rw [onwards,tangency h₁ h₂ hq (by omega : C.length>p) ha]; exact sub_self _
      push Not at ha; let T:=C.erase τ
      have ht : D.Perm (τ::τ::T) := hc.trans (List.Perm.cons τ (List.perm_cons_erase ha))
      have hp : D.length=T.length+2 := ht.length_eq
      have H : quake (go T q)=0 := (vigor T q).trans (hq _ (by omega))
      have hf (k:Axis)(hk:k∈Finset.univ.erase τ): go (k::k::T) q=0 := by
         apply IH _ _ (k::k::T) (show p+2 < T.length+1+1 by omega) rfl
         have hb := (List.perm_iff_count.mp ht τ)
         simp [Finset.ne_of_mem_erase hk] at hb ⊢; omega
      rw [shuffle _ _ _ ht]; funext x; have hy:= congrFun H (x+t')
      have off : offwalk (go T q) (x+t')=0 := by
          apply Finset.sum_eq_zero; intro i he; rw [stop_eq,←go_concat]; exact congrFun (hf i he) (x+t'-step i)
      rw [garden, off,zero_add,stop_eq,add_sub_cancel_right,←go_concat] at hy; exact hy
lemma solve (h:f∈hill E p) : ∃ q:Cover→E,q∈hill E (p+2) ∧ quake q=f := by obtain ⟨q,e,A,B⟩ := globe f; exact ⟨q,membrane A B (e.symm ▸ h),e⟩
end YM.RG11Scheme.Bell
