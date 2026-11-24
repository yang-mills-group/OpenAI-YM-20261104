import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Ends

/-! Minimal low-sector consequence of the ancestral Ends argument, specialized
before the quadratic case. This adapter preserves the original strict d < 4
statement and uses the unchanged Maxwell shell/BottomOnly definitions. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat
open Set Function Filter Tensor Analysis MeasureTheory Maxwell Maxwell.Free
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
variable {G : Gauge} {d : ℕ}

private lemma splits_one (p : Slot G →₀ ℕ) (hp : p ≠ 0) :
    ∃ i q, p = q + Finsupp.single i 1 := by
  classical
  obtain ⟨i,h⟩ : p.support.Nonempty := by simpa using hp
  have ht : Finsupp.single i 1 ≤ p := by
    intro x
    by_cases he : x = i
    · subst x
      rw [Finsupp.single_eq_same]
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
    simp [Ne.symm he]
  exact ⟨i,p-Finsupp.single i 1,(tsub_add_cancel_of_le ht).symm⟩

lemma underground (h : G.Simple) (hd : d < 4) :
    shellSector G d = BottomOnly G := by
  apply le_antisymm _ unit_fits
  classical
  intro p hP
  obtain ⟨H,W⟩ := sector.mp hP
  rw [← paints_self W]
  rw [lowerCap,MvPolynomial.restrictSupport_eq_span] at H
  refine Submodule.span_induction
    (p := fun p _ => moyenne G p ∈ BottomOnly G) ?_ ?_ ?_ ?_ H
  · rintro p ⟨x,hx,rfl⟩
    change degree x ≤ d at hx
    by_cases ht : x = 0
    · subst x
      change moyenne G 1 ∈ BottomOnly G
      rw [paints_self (fun u => map_one _)]
      exact unit_mem G
    obtain ⟨i,p,rfl⟩ := splits_one _ ht
    rw [weight_next] at hx
    by_cases ht : p = 0
    · subst p
      simp only [zero_add]
      change moyenne G (X i) ∈ BottomOnly G
      rw [← symbol_coordinate, solo _ h]
      exact Submodule.zero_mem _
    obtain ⟨j,p,rfl⟩ := splits_one _ ht
    rw [weight_next] at hx
    omega
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  intro t y _ hy
  rw [map_smul]
  exact Submodule.smul_mem _ _ hy
end YM.XSpace.Compat
end
