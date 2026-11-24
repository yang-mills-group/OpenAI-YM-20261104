import YM.Integration.WilsonReceivedChronologicalFixedDay
import YM.Integration.WilsonIndependentCollarDatedTeachers
/-! Reuse the unmarked source and the angular room of the fixed observation day at both material filings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedQuiet
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Embroider WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse
open WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse WilsonOriginalCollarElection
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds
open FundedMarkedPathSelection WilsonIndependentCollarAddressedSource Comparison.Density.Transport Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal QuadraticLocal.Mentor
open scoped Classical BigOperators Topology

open WilsonOriginalCensusFiledAttendance (QuietAt)
open WilsonIndependentCollarDatedTeachers (At)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonVacuumPreResetDatedDeposit (Issued)
open QuadraticLocal Rebirth QuadraticLocal.Poetry WilsonCoeffUV.Bank WilsonCoeffUV
open WilsonOriginalOpticalSchedule (prepared)
open QuadraticLocal.Sunrise
variable {G:Gauge}{simple:G.Simple}{R:Run G}{n q p k m N j:ℕ}
  {s:WilsonOriginalAllOrderCourse.Schedule G}{school:Syl.School k}
  (day:Day (prepared s) R simple school m N)

theorem original {Z:ℕ → SeriesA G}{price:Credit}(quiet:QuietAt day price Z)(base:m ≤ j)(live:j+1<N):
    Read R N m (Burn.horizon k) Z day.π day.Γ ∧
      (∃σ fee:ℝ,Issued R N (j+2) (Burn.horizon k) (Z (j+2)) σ fee) ∧
      Legal (Step.tape (Burn.horizon k+2)) (day.π (j+2)) ∧ Legal (Step.tape (Burn.horizon k+2)) (day.π (j+1)):=by
  obtain ⟨σ,_,_,funded⟩:=quiet.1 (j+2) (by omega) (by omega)
  exact ⟨quiet.2.2.1,⟨σ,_,funded⟩,quiet.2.2.2 (j+1) (by omega) live,quiet.2.2.2 j base (by omega)⟩

theorem teacher (per:ℕ){V:Realm G (q+1) Credit.leanC}{dims grades:Fin n→ℕ}{S:Type}[Fintype S]
    {δ:ℝ}{tube:LinkTube G}{pieces physical:ℕ}{pole:Bool→ℕ}{span:S→ℕ}{lag:S→Bool→ℕ}
    (teacher:At s R simple V dims grades (Burn.horizon k) p δ tube pieces physical pole span lag j)
    (anchor:V.anchor ≤ j+1)(base:m ≤ j)(live:j+1<N):
    let χ:=R.alloy.B.a.clock.hatBeta (j+1)
    let ℓ:=Poetry.Agenda.seed (WilsonOriginalCensusPhysicalAttendance.roots (prepared s) R simple) MintClock.splits
      (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
    let U:=day.Ψ per (j+1)
    0<ℓ ∧ Real.exp (ℓ⁻¹^2)≤χ ∧ (U.p.supportExponent+2)*((U.p.B:ℝ)⁻¹)≤ℓ/2 ∧
      (Real.sqrt U.beta)⁻¹≤1/2 ∧ U.p.B=Nat.ceil ((Real.log χ)^2) ∧ U.p.supportExponent+2≤102:=by
  obtain ⟨pos,heat,distance,_,chill,housing,exponent,_⟩:=
    (teacher anchor).2 m N per k day.π day.Γ (day.Ψ per) (day.seen per).1 (by omega) live.le
  exact ⟨pos,heat,distance,chill,housing,exponent⟩

end YM.Integration.WilsonReceivedChronologicalFixedQuiet
end
