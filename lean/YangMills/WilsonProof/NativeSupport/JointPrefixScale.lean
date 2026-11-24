import YangMills.WilsonProof.NativeSupport.OriginalGrowth
/-! Multiply the linear tariffs on the actual schedule. The accumulated
loss is a power of its total block scale. The quadratic and newborn
expenses form an additive error on that same full inlet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice Wilson RG RGComparison.Core16 PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}

theorem prefix_monotone {A:Levels G} {p:ℕ} (T:Slices A p) {t j N:ℕ} (tj:t ≤ j) (jn:j ≤ N) :
    scale (traversal T jn) ≤ scale (traversal T (tj.trans jn)) := by
  induction tj using Nat.decreasingInduction with
  | self => rfl
  | of_succ k hk ih =>
    rw [traversal_push T (hk.trans_le jn),scale]
    exact ih.trans (Nat.le_mul_of_pos_left _ (A.clock.op k p).ratio.count.property)

end YM.Integration.InletSusceptibility.Packet
