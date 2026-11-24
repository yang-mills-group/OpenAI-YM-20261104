import YM.Integration.FVA1Physical.Wilson.InheritedPrice

/-! The geometry for inherited Wilson histories on the actual run.
For any finite segment, all sufficiently large admitted periods work at once
for every choice of forest. This only discharges geometry, not the dependence
of the price constants on the periodic volume. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Filter Lattice RG Tree RGComparison.Core16 RGComparison.Core16.Descent
open scoped Classical

variable {G : Gauge} (a : Levels G)

/-- At fixed scale the block patch is independent of period, whereas
the admitted torus sides tend to infinity. -/
theorem eventually_large (m : ℕ) :
    ∀ᶠ p : ℕ in atTop, Bid.Larger (G := G) (a.clock.op m p) := by
  let b := max (100 * Pressure.macroR (a.clock.op m 0).patch) 2
  filter_upwards [a.S.period_strict.tendsto_atTop.eventually_ge_atTop b] with p hp
  have hside (j : ℕ) : (a.S.period p).val ≤ (a.S.side j p).val :=
    Nat.le_mul_of_pos_right _ (a.S.denominator j).property
  refine ⟨(a.blocks m p).branches, ?_, ?_⟩
  · exact ((le_max_left _ _).trans hp).trans (hside (m+1))
  · exact (by decide : 1 < 2).trans_le (((le_max_right _ _).trans hp).trans (hside m))

/-- Room at every level is simultaneously valid for all forests on all
sufficiently large periods, with no additional choice of physical trajectory. -/
theorem traversal_admitted {m N : ℕ} (hm : m ≤ N) :
    ∀ᶠ p : ℕ in atTop, ∀ (T : Slices a p), (traversal T hm).Room G := by
  induction hm using Nat.decreasingInduction with
  | self =>
    exact .of_forall fun p T => by rw [traversal_self]; trivial
  | of_succ m hm ih =>
    filter_upwards [eventually_large a m, ih] with p hp hT
    intro T
    rw [traversal_push T hm]
    exact ⟨hp,hT T⟩

end YM.Integration.FVA1Physical.Wilson

