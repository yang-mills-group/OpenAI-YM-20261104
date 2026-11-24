import YM.Integration.WilsonLongContactPriorGasSum

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorGasRooted
open Lattice RG Wilson Marker Merge
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {Γ:Census V}

/-- Choose the same rough site for every configuration contributing at a given held field. -/
def root (P:BudgetPoint) (U:Config G n) (rough:(flags P.threshold U).Nonempty):Site n :=
  Classical.choose rough

theorem unique (A:Activities G n) (P:BudgetPoint) (U:Config G n) (rough:(flags P.threshold U).Nonempty)
    (s:Finset ℕ) (h:A.admissible P U s):
    ∃!i:ℕ,i∈s ∧ root P U rough∈(A.forced i).inventory:=by
  classical
  let x:=root P U rough
  have hx:x∈flags P.threshold U:=Classical.choose_spec rough
  rw [←h.2] at hx
  obtain ⟨i,hi,seen⟩:=Finset.mem_biUnion.mp hx
  refine ⟨i,⟨hi,seen⟩,?_⟩
  rintro j ⟨hj,hxj⟩
  by_contra different
  exact Finset.disjoint_left.mp (h.1 hj hi different) ((A.forced j).inventory_sup hxj)
    ((A.forced i).inventory_sup seen)

theorem signed (A:Activities G n) (P:BudgetPoint) (U:Config G n) (rough:(flags P.threshold U).Nonempty)
    (f:ℕ→Poly Γ) (s:Finset ℕ):
    Photo.fronts A f U P s=∑_i∈s.filter (fun i=>root P U rough∈(A.forced i).inventory),Photo.fronts A f U P s:=by
  classical
  by_cases live:A.admissible P U s
  · obtain ⟨i,hi,only⟩:=unique A P U rough s live
    have single:s.filter (fun j=>root P U rough∈(A.forced j).inventory)={i}:=by
      ext j
      simp only [Finset.mem_filter,Finset.mem_singleton]
      exact ⟨only j,fun h=>h ▸ hi⟩
    rw [single,Finset.sum_singleton]
  · simp [Photo.fronts,live]

end YM.Integration.WilsonLongContactPriorGasRooted
