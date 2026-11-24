import YM.Integration.WilsonReceivedDepositedOrbitalMode

/-! Resolving the fixed physical face of a joint thermal board leaves all
thermal labels. Multiplication there is the original subset convolution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalColumns
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open WilsonCoeffUV.Wheel.Mark
open WilsonReceivedDepositedOrbitalMode (face)
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V]{r:ℕ}
local notation "J" => Stock.census V

def row (x:Grade (J) r)(s:Finset V):Poly (indices r):=
  Poly.inject fun u=>x.part (Join.pair (face s) u)

private theorem mates {A:Type}[AddCommMonoid A] (s:Finset V)(f:Finset V→Finset V→A):
    (∑j:(J).Mode,∑k:(J).Mode,if Poly.merges j k (face s) then f j.val k.val else 0)=
    ∑j∈s.powerset,f j (s\j):=by
  classical
  have inner (j:(J).Mode):
      (∑k:(J).Mode,if Poly.merges j k (face s) then f j.val k.val else 0)=
      if j.val⊆s then f j.val (s\j.val) else 0:=by
    by_cases h:j.val⊆s
    · rw [if_pos h,Finset.sum_eq_single (face (s\j.val))]
      · rw [if_pos (show Poly.merges j (face (s\j.val)) (face s) from
          ⟨Finset.disjoint_left.mpr (fun _ hj hk=>(mem_sdiff.mp hk).2 hj),Finset.union_sdiff_of_subset h⟩)]
        rfl
      · intro k _ ne
        apply if_neg
        rintro ⟨dis,same⟩
        apply ne
        apply Subtype.ext
        change k.val=s\j.val
        rw [show s=j.val∪k.val from same.symm,Finset.union_sdiff_left]
        exact (Finset.sdiff_eq_self_of_disjoint dis.symm).symm
      · simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro k _
      apply if_neg
      intro he
      apply h
      rw [show s=j.val∪k.val from he.2.symm]
      exact subset_union_left
  simp_rw [inner];rw [←Finset.sum_filter]
  refine Finset.sum_bij (fun j _=>j.val) ?_ ?_ ?_ (fun _ _=>rfl)
  · intro j hj;exact mem_powerset.mpr (mem_filter.mp hj).2
  · intro i _ j _ h;exact Subtype.ext h
  · intro j hj;exact ⟨face j,mem_filter.mpr ⟨mem_univ _,mem_powerset.mp hj⟩,rfl⟩

theorem product (x y:Grade (J) r):row (x*y)=shells (row x) (row y):=by
  funext s
  have specific:(∑j:(J).Mode,∑k:(J).Mode,if Poly.merges j k (face s) then row x j.val*row y k.val else 0)=
      shells (row x) (row y) s:=mates s (fun j k=>row x j*row y k)
  rw [←specific]
  apply Marker.Poly.ext
  intro t
  change (x*y).part (Join.pair (face s) t)=_
  rw [Join.pair_product]
  simp_rw [Poly.part_sum]
  refine Finset.sum_congr rfl fun j _=>?_
  rw [Finset.sum_comm (s:=univ (α:=Index r)) (t:=univ (α:=(J).Mode))]
  refine Finset.sum_congr rfl fun k _=>?_
  by_cases h:Poly.merges j k (face s)
  · simp only [h,if_true,true_and,Poly.part_mul]
    rfl
  · simp [h]

theorem ext {x y:Grade (J) r}(h:row x=row y):x=y:=by
  apply Join.both_parts
  intro s t
  exact congrArg (fun z:Poly (indices r)=>z.part t) (congrFun h s.val)

theorem zero (s:Finset V):row (0:Grade (J) r) s=0:=rfl

theorem one (s:Finset V):row (1:Grade (J) r) s=if s=∅ then 1 else 0:=by
  apply Marker.Poly.ext
  intro t
  change (1:Grade (J) r).part (Join.pair (face s) t)=_
  rw [Join.one_pair]
  by_cases h:s=∅
  · subst s;simp [show face (∅:Finset V)=(J).quiet from rfl,Poly.one_part]
  · have no:face s≠(J).quiet:=fun he=>h (congrArg Subtype.val he)
    simp [h,no]

end YM.Integration.WilsonReceivedDepositedOrbitalColumns
end
