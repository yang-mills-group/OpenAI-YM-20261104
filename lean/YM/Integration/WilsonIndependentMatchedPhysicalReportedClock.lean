import YM.Integration.WilsonIndependentSpoutMasterClockFees
import YM.Integration.WilsonIndependentSpoutMasterReport
import YM.Integration.WilsonIndependentMatchedPhysicalCash

/-! Reverting an actual signed absolute error on the older stopped scalar to
the nominated reporting date using that cutoff's true kinetic reset.  The
fee is selected before the cutoffs and is independent of the later depth. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalReportedClock
open Filter Function Finset Matrix Lattice RG Wilson PhysicalNext PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank.PathCost PowerSeries
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentSpoutMasterClockFees (Paid)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped BigOperators Classical
variable {G:Gauge}{j e:ℕ}{C:Credit}(R:Run G)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O

def bill (q:ℕ)(c M:ℝ):ℝ:=∑r∈range (q+1),((r+1:ℕ):ℝ)*(M*c)

theorem coefficient (fees:Paid R j e C)(host m N:ℕ)(early:j ≤ host)(older:host ≤ m)(live:m ≤ N)
    (A:Cost)(M:ℝ)(nn:0 ≤ M)(heard:∀i ≤ e,‖coeff i A‖ ≤ M)(i:ℕ)(ie:i ≤ e):
    ‖coeff i (report L O N m host A)‖ ≤ ((i+1:ℕ):ℝ)*(M*C.buy (Compar R.family.S (zz L) host m)):=by
  unfold report
  rw [reelQuote]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑_s∈range (i+1), M*C.buy (Compar R.family.S (zz L) host m):=by
      apply sum_le_sum
      intro s hs
      have si:s ≤ i:=Nat.le_of_lt_succ (mem_range.mp hs)
      have curr:=(fees host m N N (i-s) s early older live le_rfl (by omega) (si.trans ie)).main
      rw [norm_mul]
      exact mul_le_mul (heard s (si.trans ie)) curr (norm_nonneg _) nn
    _ = _:=by simp

theorem reserve (fees:Paid R j e C)(host m N:ℕ)(early:j ≤ host)(older:host ≤ m)(live:m ≤ N)
    (A:Cost)(M:ℝ)(nn:0 ≤ M)(heard:∀i ≤ e,‖coeff i A‖ ≤ M)(q:ℕ)(qe:q ≤ e):
    belt q (embed (report L O N m host A)) ≤ bill q (C.buy (Compar R.family.S (zz L) host m)) M:=by
  unfold WilsonPhysicalMarkedDefect.RawProduct.belt bill
  apply sum_le_sum
  intro r hr
  have rr:=coefficient R fees host m N early older live A M nn heard r
    ((Nat.le_of_lt_succ (mem_range.mp hr)).trans qe)
  simpa [embed,PowerSeries.coeff_map] using rr

end YM.Integration.WilsonIndependentMatchedPhysicalReportedClock
