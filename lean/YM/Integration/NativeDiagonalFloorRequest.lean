import YM.R2I.Campaign.Clock

/-! Diagonal pre-block floors for countably many fixed demands.  The original
floor is retained at every profile index.  A fixed additional demand is paid
on its tail, and the original deep/monotone profile map carries that tail to
both adjacent physical-step indices.  This supplies only eventual floor
domination; it does not turn a global-floor premise into a local one. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeDiagonalFloorRequest
open Filter RG

def diagonalFloor (base : ℕ → ℕ) (D : ℕ → ℕ → ℕ) (i : ℕ) : ℕ :=
  max (base i) ((Finset.range (i + 1)).sup fun n => D n i)

theorem base_le (base : ℕ → ℕ) (D : ℕ → ℕ → ℕ) :
    base ≤ diagonalFloor base D := by
  intro i
  exact le_max_left _ _

theorem demand_le (base : ℕ → ℕ) (D : ℕ → ℕ → ℕ) {n i : ℕ}
    (h : n ≤ i) : D n i ≤ diagonalFloor base D i := by
  exact (Finset.le_sup (f := fun q => D q i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le h))).trans (le_max_right _ _)

theorem profile_eventually (base : ℕ → ℕ) (D : ℕ → ℕ → ℕ) (n : ℕ) :
    ∀ᶠ i : ℕ in atTop, D n i ≤ diagonalFloor base D i :=
  (eventually_ge_atTop n).mono fun _ hi => demand_le base D hi

/-- One common first physical stage pays both neighbors for this fixed
demand, before any later error tolerance, output, or test is chosen. -/
theorem pair_eventually {G : Gauge} (base : ℕ → ℕ) (D : ℕ → ℕ → ℕ)
    (A : Levels G) (n : ℕ) :
    ∃ first : ℕ, ∀ m, first ≤ m →
      D n (A.clock.J m) ≤ diagonalFloor base D (A.clock.J m) ∧
      D n (A.clock.J (m + 1)) ≤ diagonalFloor base D (A.clock.J (m + 1)) := by
  have hn : ∀ᶠ m : ℕ in atTop, n ≤ A.clock.J m :=
    A.fits.deep.eventually (eventually_ge_atTop n)
  obtain ⟨first, hfirst⟩ := eventually_atTop.1 hn
  refine ⟨first, ?_⟩
  intro m hm
  exact ⟨demand_le base D (hfirst m hm),
    demand_le base D ((hfirst m hm).trans (A.fits.mono (Nat.le_succ m)))⟩

end YM.Integration.NativeDiagonalFloorRequest
end
