import YM.Integration.WilsonLongContactPriorFlags

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLongContactFlagPartition
open Finset
open scoped BigOperators Classical

variable {ι α:Type} [DecidableEq ι] [DecidableEq α] (X:ι→Finset α)

def Covers (D:Finset α) (p:Finset ι):Prop :=
  (p:Set ι).Pairwise (fun i j=>Disjoint (X i) (X j)) ∧ p.biUnion X=D

def admitted (L:Finset ι) (D:Finset α):Finset (Finset ι):=
  L.powerset.filter (Covers X D)

omit [DecidableEq ι] in
theorem member {L:Finset ι} {D:Finset α} {p:Finset ι}:
    p∈admitted X L D ↔ p⊆L ∧ Covers X D p:=by simp [admitted]

private theorem removed {D:Finset α} {p:Finset ι} (ok:Covers X D p) {i:ι} (hi:i∈p):
    Covers X (D\X i) (p.erase i):=by
  classical
  refine ⟨ok.1.mono (Finset.erase_subset i p),?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨distinct,inside⟩:=Finset.mem_erase.mp hj
    refine Finset.mem_sdiff.mpr ⟨ok.2 ▸ Finset.mem_biUnion.mpr ⟨j,inside,hx⟩,?_⟩
    exact Finset.disjoint_left.mp (ok.1 inside hi distinct) hx
  · intro hx
    obtain ⟨has,away⟩:=Finset.mem_sdiff.mp hx
    rw [←ok.2] at has
    obtain ⟨j,hj,atj⟩:=Finset.mem_biUnion.mp has
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_erase.mpr ⟨fun e=>away (e ▸ atj),hj⟩,atj⟩

variable (c:ι→ℝ)
def sum (L:Finset ι) (D:Finset α):ℝ:=∑p∈admitted X L D,∏i∈p,c i

private theorem after (nonneg:∀i,0≤c i) (L:Finset ι) (D:Finset α) (i:ι):
    (∑ p∈admitted X L D,if i∈p then ∏j∈p,c j else 0)≤
      c i*sum X c (L.erase i) (D\X i):=by
  classical
  let good:=(admitted X L D).filter (fun p=>i∈p)
  let prior:=fun p:Finset ι=>p.erase i
  let wt (p:Finset ι):=∏j∈p,c j
  have inj:Set.InjOn prior good:=by
    intro p hp q hq same
    have ep:i∈p:=(Finset.mem_filter.mp hp).2
    have eq:i∈q:=(Finset.mem_filter.mp hq).2
    rw [←Finset.insert_erase ep,←Finset.insert_erase eq]
    exact congrArg (insert i) same
  have sub:good.image prior⊆admitted X (L.erase i) (D\X i):=by
    intro r hr
    obtain ⟨p,own,rfl⟩:=Finset.mem_image.mp hr
    obtain ⟨hp,incl⟩:=Finset.mem_filter.mp own
    obtain ⟨down,ok⟩:=(member X).mp hp
    exact (member X).mpr ⟨Finset.erase_subset_erase i down,removed X ok incl⟩
  calc (∑p∈admitted X L D,if i∈p then ∏j∈p,c j else 0)=∑p∈good,wt p:= (Finset.sum_filter ..).symm
       _=∑p∈good,c i*wt (prior p):=Finset.sum_congr rfl (fun p hp=>(Finset.mul_prod_erase p c (Finset.mem_filter.mp hp).2).symm)
       _=c i*∑p∈good.image prior,wt p:=by rw [Finset.sum_image inj,Finset.mul_sum]
       _≤_:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg sub (fun p _ _=>Finset.prod_nonneg fun j _=>nonneg j)) (nonneg i)

/-- The root is chosen solely from the flags still to be covered. Different candidate
inventories may overlap; disjointness is imposed only within each one submitted family. -/
theorem rooted (nonempty:∀i,(X i).Nonempty) (nonneg:∀i,0≤c i) (η:ℝ) (small:η≤1)
    (income:∀(x:α)(L:Finset ι),∑i∈L.filter (fun i=>x∈X i), c i≤η)
    (D:Finset α) (L:Finset ι):sum X c L D ≤ (if D.Nonempty then η else 1):=by
  classical
  induction D using Finset.strongInductionOn generalizing L with
  | _ D ih =>
    by_cases live:D.Nonempty
    · obtain ⟨x,hx⟩:=(show D.Nonempty from live)
      let idx:=L.filter (fun i=>x∈X i)
      have fac (p:Finset ι):0≤∏i∈p,c i:=Finset.prod_nonneg fun i _=>nonneg i
      have first:sum X c L D≤∑i∈idx,∑p∈admitted X L D,if i∈p then ∏j∈p,c j else 0:=by
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨sub,ok⟩:=(member X).mp hp
        have hx':x∈p.biUnion X:=ok.2.symm ▸ hx
        obtain ⟨i,hi,belongs⟩:=Finset.mem_biUnion.mp hx'
        have hin:i∈idx:=Finset.mem_filter.mpr ⟨sub hi,belongs⟩
        apply (Finset.single_le_sum (f:=fun i=>if i∈p then ∏j∈p,c j else 0)
          (fun a _=>by split; exact fac p; exact le_rfl) hin) |> le_trans ?_
        simp [hi]
      rw [if_pos live]
      refine first.trans ((Finset.sum_le_sum (fun i own=>?_)).trans (income x L))
      have xi:x∈X i:=(Finset.mem_filter.mp own).2
      have strict:D\X i⊂D:=Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,fun same=>
        (Finset.mem_sdiff.mp (same.symm ▸ hx)).2 xi⟩
      have next:sum X c (L.erase i) (D\X i)≤1:=
        (ih (D\X i) strict (L.erase i)).trans (by split <;> first | exact small | exact le_rfl)
      exact (after X c nonneg L D i).trans (by simpa using mul_le_mul_of_nonneg_left next (nonneg i))
    · have zero:D=∅:=Finset.not_nonempty_iff_eq_empty.mp live
      subst D
      have empty:admitted X L ∅={∅}:=by
        ext p
        rw [member,Finset.mem_singleton]
        constructor
        · intro ⟨_,ok⟩
          exact Finset.eq_empty_iff_forall_notMem.mpr fun i hi=>by
            obtain ⟨x,hx⟩:=nonempty i
            have bad:x∈(∅:Finset α):=ok.2 ▸ Finset.mem_biUnion.mpr ⟨i,hi,hx⟩
            exact Finset.notMem_empty x bad
        · rintro rfl; simp [Covers]
      simp [sum,empty]

end YM.Integration.WilsonLongContactFlagPartition
