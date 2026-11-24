import YM.QuadraticLocal.Sunrise.Crowns
/-!
# Fusing marker alphabets with overlaps & arbitrary capacity

The map is on the *full* powerset of primitive impulses. When input
marks can belong to conflicting slots (locations at the same Slot but
not the same source etc), or are larger monomials than primitives,
push all their effects into the combined actual Poly. This construction
automatically kills the relevant products and respects all scale factors.
No equalities conditional on choosing a fork in the kernel needed. Coupling
table is transported separately by applying `Fiber`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.TableMap
open Function Finset Marker Multi QuadraticLocal.Sunrise Focus Comparison.RG02
open Cumulants
open scoped BigOperators Classical
variable {V W : Type} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
variable {R : Census V} {S : Census W}
set_option quotPrecheck false
local notation "P"=> Poly
local notation "D"=> Focus.census V
local notation "ι"=> Finset V
variable (A: V→Poly S)
local notation "A₀"=> (D).Mode

def lint : Poly (Focus.census V)→ₗ[ℂ] Poly S where
   toFun p := ∑ i:Finset V,(p.part (Focus.onto i)) • (∏ j∈i,A j)
   map_add' a b:=by simp only [Poly.part_plus,add_smul,sum_add_distrib]
   map_smul' c a:= by simp only [Poly.part_smul,mul_smul, Finset.smul_sum]; rfl
local notation "L"=> lint A
omit [Fintype W] in
lemma passed (i:Finset V)(a:ℂ) : lint A (Poly.send (Focus.onto i) a) = a • ∏ j∈i,A j := by change (∑ j:Finset V, (Poly.send (Focus.onto i) a).part (Focus.onto j) • (∏ i∈j,A i))=_; simp [Focus.onto,ite_smul]
variable (h:∀ v,A v*A v=0)
include h
lemma killed {i j: Finset V} (hp:¬ Disjoint i j) : (∏ t∈i,A t)*(∏ t∈j,A t)=0:= by obtain ⟨v,hv,Hv⟩:= not_disjoint_iff.mp hp; rw [← mul_prod_erase i A hv,← mul_prod_erase j A Hv,mul_mul_mul_comm,h,zero_mul]
lemma worship (i j:(Focus.census V).Mode)(a b:ℂ) : lint A (Poly.send i a* Poly.send j b)=lint A (Poly.send i a)*lint A (Poly.send j b):= by
   change L (Poly.send (Focus.onto i.val) a* Poly.send (Focus.onto j.val) b)= L (Poly.send (Focus.onto i.val) a)* L (Poly.send (Focus.onto j.val) b); by_cases hi:Disjoint i.val j.val
   · rw [send_prod (a:=a) (z:=Focus.onto (i.val∪j.val)) ⟨hi,rfl⟩] -- needs z explicit
     simp only [passed, prod_union hi]; rw [smul_mul_smul_comm]
   rw [send_noProd (fun hv=> hi hv.choose_spec.1), map_zero, passed,passed, smul_mul_smul_comm]; rw [killed A h hi]; rw [smul_zero]
def mapC : Poly (Focus.census V)→ₐ[ℂ] Poly S:= by
 refine AlgHom.ofLinearMap (lint A) ?_ ?_
 · rw [show (1:Poly (Focus.census V))=Poly.send (Focus.onto ∅) 1 from rfl,passed, one_smul, Finset.prod_empty]
 intro i j; rw [← Poly.studs i, ← Poly.studs j]; simp_rw [sum_mul, Finset.mul_sum,map_sum,worship A h, Finset.sum_mul, Finset.mul_sum]
-- V rank.Focus. expose maps.value & Warranty of φ over all.
local notation "Λ"=> TableMap.mapC A h
lemma pushes (p: Poly (Focus.census V)) : mapC A h p= ∑ i:Finset V,(p.part (Focus.onto i)) • (∏ j∈i,A j):=rfl
lemma primitive (i:V)(a:ℂ) : Λ (Poly.send (Focus.detailI i).val a)= a • A i:= by change lint A (Poly.send (Focus.detailI i).val a)=_; simpa using passed A ({i}:Finset V) a -- ok
lemma unmarked (p:Poly (Focus.census V)): (mapC A h p).part S.quiet=p.part (Focus.census V|>.quiet):= by
 let f i:ℂ:= (A i).part S.quiet; have he i:f i=0:= by apply mul_self_eq_zero.mp; exact Eq.trans (Poly.quiet_mul _ _).symm ( (congr_arg (fun p:Poly S=>p.part S.quiet) (h i))) -- maybe name
 rw [pushes,Poly.part_sum,Finset.sum_eq_single_of_mem (∅:Finset V) (mem_univ _)]; · rw [Finset.prod_empty,Poly.part_smul,Poly.one_part,if_pos rfl,mul_one]; rfl
 intro i hi h; rw [Poly.part_smul]; obtain ⟨x,hx⟩:= Finset.nonempty_iff_ne_empty.mpr h; rw [← Finset.mul_prod_erase _ _ hx, Poly.quiet_mul]; exact (by change _* (f x*_)=_; rw [he x, zero_mul, mul_zero])
-- for slot.W dissolution λ.R issue
end YM.QuadraticLocal.TableMap
