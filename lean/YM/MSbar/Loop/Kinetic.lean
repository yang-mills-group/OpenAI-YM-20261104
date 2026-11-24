import YM.MSbar.Loop.Discrete

/-! Uniform rows for linear BRST transform and motion. Keeps momentum. `active` output support I,
put marks among external (use X=0 on all their rows for now). d tracks sign of transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Finsupp Super Finset
open scoped BigOperators Classical
variable {C M: Type*} [AddCommGroup M] {p:C→Bit} {I:Finset C} {f g:Amps C M}
abbrev Row (C M:Type*) := C→C→M→ℂ
def Kinetic (p:C→Bit) (I:Finset C)(k:Bit)(R:Row C M):Prop:= ∀ x i,i∈I→∀ m,R x i m ≠0→ p x+k=p i
variable (p I) (A : Row C M) {B:Line C M} {k:Bit}
def linear (a: Wave C M) : Finsupp (Wave C M) ℂ:= ∑ i∈I,Finsupp.single (i,a.2) (A a.1 i a.2)
lemma linear_eval (a b:C)(s t:M): linear I A (a,s) (b,t)= if s=t∧b∈I then A a b s else 0:=by
    unfold linear;rw [Finsupp.finsetSum_apply]; by_cases h:b∈I
    · rw [Finset.sum_eq_single b] <;> simp_all [Finsupp.single_apply]
    rw [if_neg (fun hh=> h hh.2)]; exact Finset.sum_eq_zero fun i hi=> by grind [Finsupp.single_apply]
variable {I p A}
def rotate (hA: Kinetic p I k A) : Transport (lift (M:=M) p) k:= {
    coeff := linear I A
    parity := by
       rintro ⟨a,s⟩ ⟨b,t⟩ hv; rw [Finsupp.mem_support_iff,linear_eval] at hv; split_ifs at hv with hx
       · exact (hA _ b hx.2 s hv).symm
       exact (hv rfl).elim
}
lemma row_here (hA:Kinetic p I k A)(v:Field C M)(b:C)(s:M): (rotate hA).row (b,s) f v= ∑ i ∈ I, A b i s*f ((i,s)::v):= by
    rw [Transport.cost,Finset.sum_apply]
    let L := Finsupp.linearCombination ℂ (fun i : Wave C M=> f (i::v))
    change L (_)= _ -- defeq?
    change L (∑ i∈I,Finsupp.single (i,s) (A b i s))=_; rw [map_sum]; unfold L;simp only [Finsupp.linearCombination_single,smul_eq_mul]
lemma rotate_at (m:M) (hf:∀ s:Field C M, m+channel s≠0→ f s=0)(hA:Kinetic p I k A)(l:Field C M) (hv:m+channel l≠0): (rotate hA).lift f l=0:=by
    induction l generalizing f m with
    | nil => exact (rotate hA).base
    | cons a l ih =>
      rcases a with ⟨b,s⟩; change field (b,s) ((rotate hA).lift f) l=_
      rw [channel_cons,← add_assoc] at hv; have hh(i:C):f ((i,s)::l)=0:=hf _ (by rw [channel_cons,←add_assoc]; exact hv)
      rw [Transport.leg, Pi.add_apply,row_here, Finset.sum_eq_zero (fun i _=> by simp [hh i]),Pi.smul_apply,ih _ (f:=field (b,s) f) ?_ hv,smul_zero,zero_add]
      intro u H; exact hf ((b,s)::u) (by rw [channel_cons,← add_assoc];exact H)
lemma Quiet.rotation (hf:Quiet f)(hA:Kinetic p I k A): Quiet ((rotate hA).lift f):= fun u hu=> rotate_at 0 (fun x hx=> hf x (by simpa using hx)) hA _ (by simpa)
-- Supporting generalized above residual

end YM.MSbar.Loops
