import YangMills.WilsonProof.NativeSupport.NearBonds
import YM.RGComparison.Core16.Trajectory

set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Finset Lattice RG Wilson Tree RGComparison.Core16
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletBondRemainder
open scoped Classical BigOperators

variable {G : Gauge} {A : Levels G} {p N t : ℕ}

theorem interior_cap (T : Slices A p) (h : t ≤ N) :
    ∀ q : sites _ (traversal T h), lag (traversal T h) q < (traversal T h).depth →
      cap (traversal T h) q = A.clock.kernel.penalty * 2 := by
  induction h using Nat.decreasingInduction with
  | self =>
    rw [traversal_self]
    intro q hq
    exact (Nat.not_lt_zero _ hq).elim
  | of_succ t ht ih =>
    rw [traversal_push T ht]
    intro q hq
    rcases q with b | b
    · rfl
    · exact ih b (Nat.lt_of_succ_lt_succ hq)

theorem actual_near (T : Slices A p) (h : t ≤ N) (β v : ℕ → ℝ)
    {φ : Config G (A.S.side N p) → ℝ} (test : Continuous φ) (symm : GaugeInvariant φ)
    {S : ℝ} (bill : ∀ U, |φ U| ≤ S) (r : ℝ) {m : ℕ} (o : Fin m → Site (A.S.side N p)) (R : ℕ) :
    let d := traversal T h
    ∑ q ∈ window o R d ∩ interior d, |picture d β v 1 φ r q| ≤
      ((N-t) * (m * ((2*R+1)^4 * 4)) : ℕ) * (A.clock.kernel.penalty * 2 * (2*S)) := by
  intro d
  have cap' : ∀ q ∈ interior d, cap d q ≤ A.clock.kernel.penalty * 2 :=
    fun q hq => (interior_cap T h q (mem_filter.mp hq).2.2).le
  simpa only [d, traversal_depth] using
    near_bonds d (traversal_ok T h) β v 1 test symm bill
      (mul_nonneg A.clock.kernel.penalty_pos.le zero_le_two) cap' r o R

end YM.Integration.InletSusceptibility
