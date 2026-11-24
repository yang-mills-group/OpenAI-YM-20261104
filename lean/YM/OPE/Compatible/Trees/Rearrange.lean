import YM.OPE.Compatible.Kernel
import YM.OPE.Compatible.Trees.Order
import YM.OPE.Shape

/-!
# Cut slots and their tests
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Cov
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V : Type} [PartialOrder V] [OrderBot V] [Fintype V]
variable (E : Origin V) (P : Finset V) (v : V)

def forks : (glen E P v) ⊕ (shore E P v) ≃ (brim E P : Finset V) := Equiv.ofBijective (beside
  (fun x : glen E P v => ⟨x.val,(Finset.mem_filter.mp x.2).1⟩)
  (fun x : shore E P v => ⟨x.val,(Finset.mem_filter.mp x.2).1⟩)) (by
    refine ⟨beside_distinct.mpr ⟨fun i j e => Subtype.ext (congr_arg (Subtype.val (p:= fun x => x ∈ brim E P)) e),
      fun i j e => Subtype.ext (congr_arg (Subtype.val (p:= fun x => x ∈ brim E P)) e),fun i j e => ?_⟩,fun i => ?_⟩
    · have he : i.val = j.val := congr_arg Subtype.val e
      exact (Finset.mem_filter.mp j.2).2 (he ▸ (Finset.mem_filter.mp i.2).2)
    by_cases h : v ≤ i.val
    · exact ⟨.inl ⟨_,Finset.mem_filter.mpr ⟨i.2,h⟩⟩,rfl⟩
    exact ⟨.inr ⟨_,Finset.mem_filter.mpr ⟨i.2,h⟩⟩,rfl⟩)

def trails (hP : Crown P) (h : v∈ rest P) : Unit ⊕ shore E P v ≃ (brim E (trim P v) : Finset V) :=
  let hw := (rest_mem P).mp h
  Equiv.ofBijective (beside
    (sole (⟨v,(frontier_trim E P hP hw.1 hw.2).mpr (Or.inl rfl)⟩ : ↑(brim E (Arboreal.trim P v))))
    (fun i : shore E P v => ⟨i.val,(frontier_trim E P hP hw.1 hw.2).mpr (Or.inr (Finset.mem_filter.mp i.2))⟩)) (by
      refine ⟨beside_distinct.mpr ⟨injective_of_subsingleton _,fun i j e =>
        Subtype.ext (congr_arg (Subtype.val (p:=fun x => x∈brim E (Arboreal.trim P v))) e),fun i j e => ?_⟩,fun i => ?_⟩
      · have he : v = j.val := congr_arg Subtype.val e
        exact (Finset.mem_filter.mp j.2).2 he.le
      rcases (frontier_trim E P hP hw.1 hw.2).mp i.2 with hv|ht
      · exact ⟨.inl (),Subtype.ext hv.symm⟩
      exact ⟨.inr ⟨_,Finset.mem_filter.mpr ht⟩,rfl⟩)

def picked {V B : Type*} (P : Finset V) (p : V → B) : P → B := p ∘ Subtype.val
@[simp] lemma forked {B:Type*} (p:V→ B) : picked (brim E P) p ∘ (forks E P v) =
    beside (picked (glen E P v) p) (picked (shore E P v) p) := funext fun i => by cases i<;> rfl
lemma trailed {B:Type*} (p:V→B) (hP:Crown P) (h:v∈rest P) :
    picked (brim E (trim P v)) p ∘ (trails E P v hP h) = beside (sole (p v)) (picked (shore E P v) p) :=
  funext fun i => by cases i<;> rfl
lemma shore_ne {u : V} (h : u∈shore E P v) : u≠v :=
  fun e => (Finset.mem_filter.mp h).2 e.ge
lemma unpicked {B:Type*} (p:V→B) (a:B) : picked (shore E P v) (update p v a) = picked (shore E P v) p :=
  funext fun i => update_of_ne (shore_ne E P v i.2) _ _

section
variable {G:Gauge} {L:Register G} (S T:Table L)
variable {I J K W:Type} [Fintype I] [Fintype J] [Fintype K] [Fintype W]
lemma swivel (ht:T.Symmetric) (e : I⊕J ≃ K)
    (x:I→ E4)(y:J→ E4)(z:K→ E4)(o:W→ E4) (p:I→ S.Tag)(q:J→ S.Tag)(s:K→ S.Tag)(w:W→ S.Tag)
    (he : z ∘ e=beside x y) (hv : s ∘ e=beside p q) (hz:Injective (beside z o)) :
    kernel T (beside z o) (beside s w) = kernel T (beside x (beside y o)) (beside p (beside q w)) := by
  let F := (Equiv.sumAssoc I J W).symm.trans (Equiv.sumCongr e (Equiv.refl W))
  have hh {Y:Type} (a:I→Y)(b:J→Y)(u:K→Y)(v:W→Y)(h : u ∘ e = beside a b) :
      beside a (beside b v) = beside u v ∘ F := funext fun j => by
        rcases j with i | i|i
        exact (congr_fun h (.inl i)).symm
        exact (congr_fun h (.inr i)).symm
        rfl
  rw [hh x y z o he,hh p q s w hv,kernel_order _ _ _ hz]; exact ht
end

variable {G:Gauge} {L:Register G} {S T:Table L} {J:Type} [Fintype J]
lemma from_brim (hT:T.Symmetric) (x:V→ E4)(p:V→ S.Tag)(y:J→E4)(q:J→ S.Tag)
    (hx : Injective (beside (picked (brim E P) x) y)) :
    kernel T (beside (picked (brim E P) x) y) (beside (picked (brim E P) p) q) = kernel T
      (beside (picked (glen E P v) x) (beside (picked (shore E P v) x) y))
      (beside (picked (glen E P v) p) (beside (picked (shore E P v) p) q)) :=
  swivel S T hT (forks E P v) _ _ _ _ _ _ _ _ (forked ..) (forked ..) hx
lemma passing (hT:T.Symmetric) (x:V→ E4)(p:V→ S.Tag)(a:S.Tag)(y:J→E4)(q:J→ S.Tag) (hP:Crown P) (hv:v∈rest P)
    (hx : Injective (beside (picked (brim E (Arboreal.trim P v)) x) y)) :
    kernel T (beside (sole (x v)) (beside (picked (shore E P v) x) y))
        (beside (sole a) (beside (picked (shore E P v) p) q)) =
      kernel T (beside (picked (brim E (Arboreal.trim P v)) x) y)
        (beside (picked (brim E (Arboreal.trim P v)) (update p v a)) q) := by
  refine Eq.symm (swivel S T hT (trails E P v hP hv) _ _ _ _ _ _ _ _ (trailed ..) ?_ hx)
  rw [trailed .., update_self, unpicked]

lemma glen_sum {A:Type*} [AddCommMonoid A] (f:V→A) :
    (∑ i:brim E P,f i.val) = (∑ i:glen E P v, f i.val)+∑ i:shore E P v,f i.val := by
  rw [← Equiv.sum_comp (forks E P v) (fun i => f i.val), Fintype.sum_sum_type]; rfl
lemma trim_sum {A:Type*} [AddCommMonoid A] (f:V→A) (hP:Crown P) (h:v∈rest P) :
    (∑ i:brim E (Arboreal.trim P v), f i.val)= f v + ∑ i:shore E P v, f i.val := by
  rw [← Equiv.sum_comp (trails E P v hP h) (fun i => f i.val),
    Fintype.sum_sum_type, Fintype.sum_unique]; rfl
end YM.OPE.Arboreal
