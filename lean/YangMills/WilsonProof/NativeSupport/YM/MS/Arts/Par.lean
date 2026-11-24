import YM.MS.Arts.Par
import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.NatD
import YM.MS.Properties
/-! # Canonical indices for real orthogonal continuation -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open Momentum
variable {m n i:ℕ}
lemma nowhere (h:m≤n)(i:L m)(j:Apart m n): rises h i ≠ aside h j:= fun he=>by have ht:=congr_arg Fin.val he; change i.val= Zed m + _ at ht; have hz:= i.isLt; omega
lemma rangeA (i:L n)(h:m≤n): (∃ j,rises h j=i) ∨ (∃ j,aside h j=i):= by
    by_cases hh:i.val< Zed m; · exact Or.inl ⟨⟨i.val,hh⟩,Fin.ext rfl⟩
    refine Or.inr ⟨⟨i.val-Zed m,?_⟩,Fin.ext ?_⟩; · have he:= op h; have ht:=i.isLt; omega
    change Zed m+(i.val-Zed m)=i.val; omega

def equivS (h:m≤n): L m ⊕ Apart m n ≃ L n:= Equiv.ofBijective (Sum.elim (rises h) (aside h)) (by
   constructor; · intro i j he; rcases i with i|i <;> rcases j with j|j; exact congr_arg _ ((rises h).injective he); exact (nowhere h i j he).elim; exact (nowhere h j i he.symm).elim; exact congr_arg _ ((aside h).injective he)
   intro i; rcases rangeA i h with ⟨j,hh⟩ | ⟨j,hh⟩; exact ⟨.inl j,hh⟩; exact ⟨.inr j,hh⟩)
variable {A B D R:Type}[Fintype A][Fintype B][Fintype D]
open Classical in
@[simp] lemma cut_sum [AddCommMonoid R](h:m≤n)(f:L n→R): (∑ i:L n,f i)=(∑ i:L m,f (rises h i)) +∑ i:Apart m n,f (aside h i):= by rw [← Equiv.sum_comp (equivS h) f,Fintype.sum_sum_type]; rfl
attribute [-simp] cut_sum
-- linear maps for embeddings in general
variable [DecidableEq A][DecidableEq B][DecidableEq D]
lemma standardP (f:Momentum A): (∑ i:A,f i • spray i)=f:= by ext i; simp [spray,Pi.single_apply,Finset.sum_apply,mul_ite]
omit [DecidableEq A] [Fintype B] in
lemma sends (f:A↪B)(x:Momentum A)(i:B) : sendB f x i= ∑ j:A, x j* (spray (f j) i):= by simp [sendB,_root_.sum_apply]
omit [DecidableEq A] [Fintype B] in
lemma lasts (f:A↪B)(x:Momentum A)(i:A): sendB f x (f i)=x i:= by rw [sends]; classical simp [spray,Pi.single_apply,mul_ite] -- simp inj
omit [DecidableEq A] [Fintype B] in
lemma offt (f:A↪B)(x:Momentum A)(i:B)(h:∀ j,f j≠i) : sendB f x i=0:= by simp_rw [sends]; classical simp [spray, Ne.symm (h _)] -- h or orientation
omit [Fintype B] in
lemma send_spray (f:A↪B)(i:A): sendB f (spray i)= spray (f i):=by ext j; rw [sends,Finset.sum_eq_single i (fun b hb ht=>?_)]; simp [spray]; simp; simp [spray,ht]
omit [Fintype D] in
lemma sons (f:A↪B)(g:B↪D)(x: Momentum A): sendB g (sendB f x)=sendB (f.trans g) x:= by nth_rw 1 2 [← standardP x]; simp_rw [map_sum,map_smul,send_spray]; rfl
@[simp] lemma rides_link (h:m≤n)(ht:i≤m): (rises ht).trans (rises h)=rises (le_trans ht h):= by ext; rfl
end YM.MS.Arts
