import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFieldDegreeAllocations
namespace IssuedBridge.PostedLastDegreeExclusion
open scoped BigOperators Classical
noncomputable section
theorem original {n k : ℕ} (F : (Fin n → Fin (k+2)) → ℂ)
    (vanish : ∀ ν, (∃ i, (ν i).val = k+1) → F ν = 0) :
    ∑ ν, F ν = ∑ τ : Fin n → Fin (k+1), F (fun i => (τ i).castSucc) := by
  classical
  let small := Finset.univ.filter (fun ν : Fin n → Fin (k+2) => ∀ i, (ν i).val < k+1)
  have retained : ∑ ν ∈ small, F ν = ∑ ν, F ν := by
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro ν _ absent
    have someTop : ¬ ∀ i, (ν i).val < k+1 := fun h => absent (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    obtain ⟨i, hi⟩ := not_forall.mp someTop
    have upper := (ν i).isLt
    exact vanish ν ⟨i, by omega⟩
  rw [← retained]
  symm
  apply Finset.sum_bij (fun τ _ i => (τ i).castSucc)
  · intro τ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i => (τ i).isLt⟩
  · intro τ _ σ _ same
    funext i
    exact Fin.ext (congrArg (fun z : Fin (k+2) => z.val) (congrFun same i))
  · intro ν hν
    have late := (Finset.mem_filter.mp hν).2
    refine ⟨fun i => ⟨(ν i).val,late i⟩, Finset.mem_univ _, ?_⟩
    funext i
    exact Fin.ext rfl
  · intro _ _
    rfl
end
end IssuedBridge.PostedLastDegreeExclusion
