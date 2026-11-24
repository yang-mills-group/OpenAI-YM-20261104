import YM.Integration.WilsonLongContactFlagPartition

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorGasSum
open Lattice Wilson RG Marker Finset Merge
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {Γ:Census V}
  (A:Activities G n) (P:BudgetPoint) (w:V→ℝ) (f:ℕ→Poly Γ)
local notation "X" => fun i=>(A.forced i).inventory
local notation "Y" => fun i=>(A.forced i).support

theorem original (hw:∀v,0<w v) (U:Config G n) (η:ℝ) (small:η≤1)
    (income:∀(x:Site n)(L:Finset ℕ),∑i∈Ac.buds Y L {x},Poly.price w (f i)≤η):
    Summable (fun s=>Poly.price w (Photo.fronts A f U P s)) ∧ Summable (Photo.fronts A f U P) ∧
    (∑'s,Poly.price w (Photo.fronts A f U P s)) ≤ (if (flags P.threshold U).Nonempty then η else 1) ∧
    Poly.price w (∑'s,Photo.fronts A f U P s) ≤ (if (flags P.threshold U).Nonempty then η else 1):=by
  classical
  let D:=flags P.threshold U
  let h:=fun i=>Poly.price w (f i)
  let bills:=fun s:Finset ℕ=>Poly.price w (Photo.fronts A f U P s)
  have pos (i):0≤h i:=Poly.nonnegative hw _
  have cap (x:Site n) (pool:Finset ℕ):∑i∈pool.filter (fun i=>x∈(A.forced i).inventory),h i≤η:=by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t:=Ac.buds Y pool {x}) ?_ (fun i _ _=>pos i)).trans (income x pool)
    intro i hi
    obtain ⟨ini,point⟩:=Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨ini,⟨x,Finset.mem_singleton_self _,(A.forced i).inventory_sup point⟩⟩
  have fee (range:Finset (Finset ℕ)):∑s∈range,bills s≤ (if D.Nonempty then η else 1):=by
    let pool:=range.biUnion id
    let good:=range.filter (A.admissible P U)
    have correct:good⊆WilsonLongContactFlagPartition.admitted X pool D:=by
      intro p hp
      obtain ⟨inside,legal⟩:=Finset.mem_filter.mp hp
      refine (WilsonLongContactFlagPartition.member X).mpr ⟨fun i hi=>Finset.mem_biUnion.mpr ⟨p,inside,hi⟩,?_,legal.2⟩
      intro i hi j hj hij
      exact (legal.1 hi hj hij).mono (A.forced i).inventory_sup (A.forced j).inventory_sup
    refine le_trans ?_ (WilsonLongContactFlagPartition.rooted X h (fun i=>(A.forced i).inventory_ne)
      pos η small cap D pool)
    change _≤∑p∈WilsonLongContactFlagPartition.admitted X pool D,∏i∈p,h i
    refine le_trans (b:=∑p∈good,∏i∈p,h i) ?_
      (Finset.sum_le_sum_of_subset_of_nonneg correct (fun p _ _=>Finset.prod_nonneg fun i _=>pos i))
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro s _
    by_cases legal:A.admissible P U s
    · simpa only [bills,Photo.fronts,if_pos legal,h] using Poly.multiple hw s f
    simp only [bills,Photo.fronts,if_neg legal,Poly.zero_price,le_refl]
  have sum:Summable bills:=summable_of_sum_le (fun s=>Poly.nonnegative hw _) fee
  have total:=sum.tsum_le_of_sum_le fee
  have taken:=Poly.budgeted hw sum (fun s=>le_refl (bills s))
  exact ⟨sum,taken.1,total,taken.2.trans total⟩

/-- In a flag-free field the exact-cover rule allows only the empty family. -/
theorem cold (U:Config G n) (none:flags P.threshold U=∅):
    ∑'s,Photo.fronts A f U P s=1:=by
  classical
  rw [tsum_eq_single (∅:Finset ℕ)]
  · have legal:A.admissible P U ∅:=by simp [Activities.admissible,none]
    simp [Photo.fronts,legal]
  intro s distinct
  have bad:¬A.admissible P U s:=by
    intro ok
    obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr distinct
    obtain ⟨x,hx⟩:=(A.forced i).inventory_ne
    have encounter:x∈flags P.threshold U:=ok.2 ▸ Finset.mem_biUnion.mpr ⟨i,hi,hx⟩
    simp [none] at encounter
  simp [Photo.fronts,bad]

end YM.Integration.WilsonLongContactPriorGasSum
