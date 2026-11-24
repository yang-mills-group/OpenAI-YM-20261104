import YM.Contacts.Pulse.Rebase
import Mathlib.Algebra.MvPolynomial.PDeriv
/-! # Symmetric measured arcs (r log coordinates). -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Set Filter Finset RG MvPolynomial
open scoped Classical BigOperators Topology NNReal
variable {ι κ α β : Type*}
variable (F G:Field ι α) (b:ℝ)

def Poem (F:Field ι α):Prop := ∀ p: Equiv.Perm ι, ∀ x, F (x∘p)= F x
def reorder (e:ι≃κ) (F:Field ι α) : Field κ α := fun x=>F (x∘e)
namespace Poem
variable {F G}
lemma empty : Poem (fun _:ι→α=>0):= fun _ _=>rfl
lemma add (h:Poem F)(hg:Poem G): Poem (F+G):= fun p x=> congr_arg₂ (·+·) (h p x) (hg p x)
lemma scale (h: Poem F)(b:ℝ): Poem (b • F):= fun p x=>congr_arg (b*·) (h p x)
lemma minus (h:Poem F): Poem (-F):=fun p x=>congr_arg (fun x:ℝ=>-x) (h p x)
lemma renew (h:Poem F)(e:ι≃κ): Poem (reorder e F):= by
  intro p x; unfold reorder; rw [← h ((e.trans p).trans e.symm) (x∘e)]; apply congr_arg; ext1 i; simp
lemma sum {f:β→Field ι α} (t:Finset β) (h:∀ i∈t, Poem (f i)): Poem (∑ i∈t,f i) := fun p x=> by simp only [Finset.sum_apply]; exact Finset.sum_congr rfl fun j hj=> h j hj p x
end Poem

section pen
variable [Fintype ι][Fintype κ]
def printRun (F:Field ι α) : Field ι α := ( (Fintype.card (Equiv.Perm ι):ℝ)⁻¹ ) • ∑ p:Equiv.Perm ι, reorder p F
lemma print_even : Poem (printRun F):= by
  intro p x; simp only [printRun,Finset.sum_apply,Pi.smul_apply]; apply congr_arg; conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft p)]
  apply sum_congr rfl; intro i _; unfold reorder; apply congr_arg; ext1 t; rfl
lemma print_mirror {e : Equiv.Perm α}(h : Mirrored e F): Mirrored e (printRun F):= by
  intro x; simp only [printRun,Pi.smul_apply,Finset.sum_apply]; apply congr_arg; exact sum_congr rfl fun i _=>h _
lemma Rooted.aggregate {l:Range α}{f:β→Field ι α}{c:β→ℝ}(s:Finset β)(h:∀ i∈s, Rooted l (f i) (c i)) : Rooted l (∑ i∈s, f i) (∑ i∈s,c i):= by
  refine ⟨sum_nonneg fun i hi=>(h i hi).cash, fun i x=>?_⟩
  simp_rw [Finset.sum_apply]; exact budget_collect (fun _=> show 0≤ l.bill _ from (by positivity)) (fun i hi=>(h i hi).row ..)
variable {F b}
lemma Rooted.renew {c}{l:Range α}(h:Rooted l F c)(e:ι≃κ): Rooted l (reorder e F) c:=h.rotate e
lemma Rooted.even {l:Range α}{b}(h:Rooted l F b) : Rooted l (printRun F) b:= by
   apply Rooted.weaken ((Rooted.aggregate univ (fun (p:Equiv.Perm ι) _=> h.rotate p)).smul ((Fintype.card (Equiv.Perm ι):ℝ)⁻¹)) (fun _=>le_rfl) ?_ -- reorder
   simp
lemma Shadow.aggregate {l:Range α} (p:α→ β){X:Type*}{f:X→Field ι α}{g:X→Field ι β}(s:Finset X){t:X→ℝ} (h:∀ i∈s,Rooted l (f i) (t i))(hp:∀ i∈s, Shadow p (f i) (g i)): Shadow p (∑ i∈s,f i) (∑ i∈s,g i) := by
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact Shadow.empty (ι:=ι) p
  | @insert i u hi ih=>
    let hu := Rooted.aggregate u (fun j hj=> h j (mem_insert_of_mem hj))
    rw [sum_insert hi,sum_insert hi]; exact (hp i (mem_insert_self ..)).add (ih (fun j hj=> h j (mem_insert_of_mem hj)) (fun j hj=> hp j (mem_insert_of_mem hj))) (h i (mem_insert_self ..)) hu
lemma Shadow.even {p:α→ β}{l:Range α}{H:Field ι β}(hp:Shadow p F H)(h:Rooted l F b): Shadow p (printRun F) (printRun H):= by
  apply Shadow.scale; exact Shadow.aggregate p _ (fun i _=> h.renew i) (fun i _=> hp.replace (e:=i.symm))

variable [Fintype α]
abbrev Plate (α:Type*) := MvPolynomial α ℝ
def verse (F:Field ι α) : Plate α := ∑ x:ι→α, C (F x)*(∏ i:ι,X (x i))
lemma verse_add (F G:Field ι α): verse (F+G)=verse F+verse G:= by simp [verse,add_mul,sum_add_distrib]
lemma verse_scale (F:Field ι α)(b:ℝ) : verse (b • F)= C b * verse F:= by simp only [verse,Pi.smul_apply,smul_eq_mul,map_mul,mul_assoc,mul_sum]
lemma verse_scale' (F:Field ι α)(b:ℝ) : verse (b • F)= b • verse F:= by rw [verse_scale, C_mul']
lemma verse_sum (f:β→Field ι α)(s:Finset β) : verse (∑ i∈s,f i)= ∑ i∈s, verse (f i):= by simp only [verse,Finset.sum_apply,map_sum,sum_mul]; rw [sum_comm]
lemma verse_renew (F:Field ι α)(e:ι≃κ): verse (reorder e F)=verse F:= by
  unfold verse; rw [←Equiv.sum_comp (Equiv.arrowCongr e (Equiv.refl _))]; apply sum_congr rfl; intro x _; rw [show reorder e F ((Equiv.arrowCongr e (Equiv.refl _)) x)=F x from ?_];
  · apply congr_arg; rw [← Equiv.prod_comp e]; simp
  unfold reorder; congr; ext1 i; simp
lemma verse_print (F:Field ι α): verse (printRun F)=verse F:= by
  unfold printRun; rw [verse_scale',verse_sum]; simp_rw [verse_renew,sum_const,card_univ];
  rw [←Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α:=Equiv.Perm ι)),one_smul]
@[simp] lemma verse_quiet : verse (ι:=ι) (0:Field ι α)=0 := by simp [verse]
end pen
end YM.Pulse
