import YM.Integration.WilsonSeparatedPrefixMovingUnformedSector

/-! Convert the actual strictly later connecting dates to the inclusive native
paid calendar. A same-date entry contributes to the unformed branch. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingTriangle
open Finset
open scoped BigOperators Classical

theorem row (N m d:ℕ)(v:d < N-m)(f:ℕ→ℝ)(zero:f d=0):
    ∑z∈range (N-(m+d+1)),f (d+1+z)=∑j∈(range (N-m)).filter (fun j=>d≤j),f j:=by
  have cover:(range (N-m)).filter (fun j=>d≤j)=insert d ((range (N-m)).filter (fun j=>d<j)):=by
    ext j
    simp only [mem_insert,mem_filter,mem_range]
    omega
  rw [cover,sum_insert (by simp),zero,zero_add]
  apply sum_bij (fun z _=>d+1+z)
  · intro z hz
    simp only [mem_range] at hz
    simp only [mem_filter,mem_range];omega
  · intro i _ j _ h
    omega
  · intro j hj
    simp only [mem_filter,mem_range] at hj
    exact ⟨j-(d+1),mem_range.mpr (by omega),by omega⟩
  · intros;rfl

end YM.Integration.WilsonSeparatedPrefixMovingTriangle
