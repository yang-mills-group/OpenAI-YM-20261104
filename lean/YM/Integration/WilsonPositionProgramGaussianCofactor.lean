import YM.Comparison.RG02.Cumulants.Cloud

/-! The signed conditional cofactor of a changed driver on its genuine Gaussian law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianCofactor
open Function Finset Marker Multi Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Extra.Trajectories (connected)
open scoped BigOperators Classical
variable {V A:Type} [DecidableEq V] [Fintype V] {R:Census V}
  [CommSemiring A] [Algebra ℂ A] (f:A→ₗ[ℂ]ℂ) (p:V→A) (s:R.Mode) (i:V)

def companion : A :=
  let den:=inverseMass (outer s.val {i} (moments R f p))
  ∑ a:R.Mode,∑ b:R.Mode, if Poly.merges a b s ∧ a.val⊆s.val ∧ i∈a.val then
    den.part b • (∏j∈a.val.erase i,p j) else 0

theorem probed (normalized:f 1=1)(live:i∈s.val)(delta:A):
    (connected (moments R f (update p i delta))).part s =
      f (delta * companion f p s i):=by
  classical
  rw [← quotient_singleton s i _ ((moments_quiet _ _).trans normalized) live,
    quotient, invariant_denominator, Poly.part_mul]
  simp only [companion,mul_sum,map_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [root_part]
  by_cases h:Poly.merges a b s
  · by_cases ha:a.val⊆s.val
    · by_cases hi:i∈a.val
      · simp [h,ha,hi,moment_with_root f p i hi,mul_comm]
      · simp [h,ha,hi]
    · simp [h,ha]
  · simp [h]

theorem centered (normalized:f 1=1)(live:i∈s.val)(other:∃j∈s.val,j≠i):
    f (companion f p s i)=0:=by
  classical
  obtain ⟨j,hj,ne⟩:=other
  have split:FactorsAt f (update p i (1:A)) s {i}:=by
    intro a _
    have unit:(∏ k∈a.val∩{i},update p i (1:A) k)=1:=by
      apply prod_eq_one
      intro k hk
      have eq:k=i:=mem_singleton.mp (mem_inter.mp hk).2
      simp [eq]
    rw [←prod_inter_mul_prod_sdiff a.val {i} (update p i (1:A)),unit,one_mul,normalized,one_mul]
  have zero:=cumulant_split (⇑f) (update p i (1:A)) s normalized
    (U:={i}) ⟨i,by simp [live]⟩ ⟨j,by simp [hj,ne]⟩ split
  rw [probed f p s i normalized live,one_mul] at zero
  exact zero

end YM.Integration.WilsonPositionProgramGaussianCofactor
end
