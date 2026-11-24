import YM.Integration.WilsonOlderFreshHybridScar
import YM.Integration.WilsonOlderFreshTerminalProgramme

/-! Hear the nonbare K-planted programme on its earlier weak date, with every
rank entering the original normalized transfer and one charge for all its first joins. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOlderFreshHybridClock
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Topology BigOperators Classical
variable {G : Gauge} {a h D k u e : ℕ}

open WilsonOriginalPublicTwoTopJoined (Hearing)
open WilsonMarkedIndependentNormalizedElection (deck normalized)

def flat (X : Era G ℝ) (q : ℕ) (g : ℝ) : ℝ :=
  WilsonOlderFreshTerminalProgramme.series q g (fun j => X.2 j 0 Fin.elim0)

theorem component {P Q : Era G ℝ} {A δ : ℝ} (fund : Fringed k e u 1 A δ P Q)
    {j : ℕ} (kept : j ≤ e) :
    ‖P.2 j 0 Fin.elim0 - Q.2 j 0 Fin.elim0‖ ≤ A*δ := by
  have pay := (fund.heapS j 0 kept).toll
  have one := pay.2.1.sum_le_tsum ({Fin.elim0} : Finset (dock Cover _ 0))
    (fun i _ => pay.1 i)
  rw [sum_singleton] at one
  exact (le_mul_of_one_le_left (norm_nonneg _) (autumn_pos (by norm_num : (0:ℝ)≤1) _ _)).trans
    (one.trans pay.2.2)

theorem priced {P Q : Era G ℝ} {A δ : ℝ} (fund : Fringed k e u 1 A δ P Q)
    {q:ℕ} (kept : q ≤ e) (g : ℝ) :
    ‖flat P q g - flat Q q g‖ ≤ (∑j ∈ range (q+1), |g|^j)*(A*δ) :=by
  unfold flat WilsonOlderFreshTerminalProgramme.series
  rw [←sum_sub_distrib, sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro i hi
  rw [←mul_sub, norm_mul, Real.norm_eq_abs, abs_pow]
  exact mul_le_mul_of_nonneg_left (component fund (by have hh:=mem_range.mp hi; omega)) (by positivity)

end YM.Integration.WilsonOlderFreshHybridClock
end
