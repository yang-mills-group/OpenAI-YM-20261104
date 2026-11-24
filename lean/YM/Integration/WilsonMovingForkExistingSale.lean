import YM.Integration.WilsonMovingForkEnrolledDensity
import YM.Integration.WilsonMovingForkChronologicalSale

/-! Consume the original sale on its actual Filed witnesses. Its two
declarations are the only dates that must coincide with the optical print. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkExistingSale
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity QuadraticLocal.Sunrise Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonMovingForkChronologicalTable (density)
open WilsonMovingForkPrintedFile (Program allSlots)
open WilsonMovingForkChronologicalSale (Mounted)
open WilsonThermometerUnitFilingFlatTelescope (feeAt)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple){m j k N per:ℕ}(hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G (R.family.side i per))
  {φ:ℕ→ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m≤j)(ahead:Mentor.Forecast D R.rolls Q φ books)
  {n K:ℕ}{d:Fin n→ℕ}(prog:Program R d K)(w:∀a,R.family.label (d a))(pins:Fin n→Site (R.family.side K per))
  (rows:∀i,Config G (R.family.side i per)→Poly (Stock.census (Fin n))){S S':Fin n→ℝ}{a a':ℕ}
  (upper:WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a
    (rows (j+1+1)))(lower:WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books base ahead S' a'
    (rows (j+1)))

theorem original {u v b p size:ℕ}{η:ℝ}(uv:u≤v)(vb:v≤b)(vj:v≤j+1)(cut:j+2≤K)(kn:K≤N)
    (old:Mounted prog N per w pins (j+1))(fresh:Mounted prog N per w pins (j+2))
    (before:rows (j+1)=density prog N per w pins (j+1))(after_:rows (j+2)=density prog N per w pins (j+2))
    (granted:WilsonReceivedChronologicalTwoFlatSale.Sale R simple hk D Q π Γ Ψ books base ahead rows upper lower
      u b (allSlots n) p size η):
    let s:=allSlots n
    ‖feeAt R N per v (WilsonMovingForkPrintedFile.row prog N per w pins) (j+1)‖≤
      (WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*(2:ℝ)^p*WilsonOriginalCensusFiledHousing.fare s size)*
        (regulatorRun R.family N per b)^p:=by
  intro s
  have actual:=WilsonMovingForkCensusIncidence.dated R (N:=N) (per:=per) vj (by omega) s rows
    (WilsonMovingForkPrintedFile.row prog N per w pins)
    (before ▸ WilsonMovingForkChronologicalSale.integrable prog N per w pins (by omega) kn old)
    (after_ ▸ WilsonMovingForkChronologicalSale.integrable prog N per w pins cut kn fresh)
    (by rw [before];exact WilsonMovingForkChronologicalTable.full ..)
    (by rw [after_];exact WilsonMovingForkChronologicalTable.full ..)
  rw [←actual]
  exact WilsonReceivedChronologicalTwoFlatSale.paid R simple hk D Q π Γ Ψ books base ahead rows upper lower
    granted uv vb

end YM.Integration.WilsonMovingForkExistingSale
