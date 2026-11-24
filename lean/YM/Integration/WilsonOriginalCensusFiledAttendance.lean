import YM.Integration.WilsonOriginalCensusJoinedAttendance
import YM.Integration.WilsonOriginalCensusAttendanceVacuum

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledAttendance
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
universe u
variable {G:Gauge}{a:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
  {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}{U:Type}[Fintype U]


open Marker Multi QuadraticLocal QuadraticLocal.Earn

open WilsonOriginalCensusDatedSchools (Paired)
open WilsonOriginalCensusMeasuredStation (CreditAt)
open WilsonCoeffUV.Bank.Carp

open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance
open WilsonOriginalCensusAttendanceStation WilsonOriginalCensusPublicationClock

open Function Filter Finset Lattice RG RG.Supply Org PhysicalNext.Repeat Legato
open Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth QuadraticLocal.Sunrise.Aviary
open AllOrder.Transit AllOrder.Transit.WheelP
open WilsonOlderFreshGraphAward WilsonThermometerDeclaredSeeds
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetDepositedGeometric WilsonOriginalOccupiedForestIntegral
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation
open WilsonMarkedIndependentPhysicalIntake
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetDatedDeposit (Issued)
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe
open AllOrder.Floe.Step.PlanV FVA1Physical.TwoReset
open WilsonVacuumPreResetDatedCourse (coin)
open Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonOriginalOccupiedForestIntegral (numerator)
open Next.SectorChange MeasureTheory

/-- The actual unmarked datum at every date and all angular forest reads on
the same enrolled trajectory, with finite native width and numerical fee. -/
def QuietAt {vac m N:ℕ}{school:Syl.School vac}{course:WilsonOriginalAllOrderCourse.Schedule G}
    (day:Day course R simple school m N)(price:Credit)(Z:ℕ → SeriesA G) : Prop :=
    (∀i,m ≤ i → i ≤ N → ∃σ:ℝ,0 < σ ∧ σ⁻¹ ≤ zz (levels R) i ∧
        Issued R N i (Burn.horizon vac) (Z i) σ
          (price.buy (zz (levels R) i)+zz (levels R) i*(levels R).clock.loopCap i)) ∧
    Prescription R (fun i=>bank (Z i)) (coin R N) N m (Burn.horizon vac) ∧
    Read R N m (Burn.horizon vac) Z day.π day.Γ ∧
    ∀i,m ≤ i → i < N → Legal (Step.tape (Burn.horizon vac+2)) (day.π (i+1))

/-- The true vacuum and ordered angular boards precede all physical periods.
Their two marked posts, named compact comparator and the period estimate are
issued together on the same original path and grade schedule. -/
theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    (n:ℕ)(front:Fin n)(k D:Fin n → ℕ)(κ:(j:Fin n) → Knob (D j))(pt:Fin n → Chamber)
    (caps:Fin n → ℝ)(nonneg:∀j,0 ≤ caps j)(hk:∀v,k v < D v)(q p₀:ℕ)(ask:Demand q p₀ k)
    (P:ℕ)(tube:LinkTube G)(pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):
    let L:=R.family.path.levels
    let all:Finset (Fin n):=univ
    let θ:=Burn.horizon ask.vac
    ∃ book:WilsonOriginalCensusPhysicalAttendance.Room (prepared s) R simple,
    ∃price:Credit,∃B:ℝ,1 ≤ B ∧ ∀ᶠ first:ℕ in atTop,∃V:Realm G (q+1) Credit.leanC,∃draw:V.draws=L,
      V.paid=R.metals.O ∧ V.anchor=first ∧ ∀A:ℕ,∃C:ℝ,0 ≤ C ∧ ∀δ:ℝ,0 < δ → ∀ᶠ m:ℕ in atTop,
      ∃ board:(N:ℕ) → m ≤ N → Day (prepared s) R simple ask.school m N,
      (∀N:ℕ,∀(valid:m ≤ N),∃Z:ℕ → SeriesA G, QuietAt (board N valid) price Z) ∧
      (∀j ≥ m,WilsonIndependentCollarDatedTeachers.At s R simple V D k θ P δ tube pieces physical p span lag j ∧
        WilsonIndependentCollarDatedTeachers.At s R simple V D k θ P δ tube pieces physical p span lag (j+1)) ∧
      ∀(_hm:V.anchor ≤ m)(days:ℕ),
        L.S.scale (m+days)-L.S.scale m ≤ (A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
        let dates:=↥(Ico m (m+days))
        ∀(diameter:dates → ℕ)(amount:dates → Hot (Stock.census (Fin n)) → ℝ),
        (∀j t,0 < amount j t) → ∀ᶠ per:ℕ in atTop,∀N:ℕ,∀ (valid:m+days ≤ N),m+1 ≤ N →
        let H:=Real.sqrt (R.family.path.β N per (m+1))
        let rate:=H^δ*B^all.card
        let day:=board N (by omega)
        (∀j,∀ (young:m ≤ j), ∀ (reached:j+3 ≤ m+days),
          ∃ openers:Open R simple k ask.school.pieces (ask.school.order+1) ask.load j ∧
            Open R simple k ask.school.pieces (ask.school.order+1) ask.load (j+1),
          WilsonOriginalCensusAttendancePair.Sold (K:=m+days) (D:=D) (V:=V) (draw:=draw)
            (rate:=rate) (δ:=δ) book ask day.π day.Γ day.hk day.lessons (day.Ψ per) young
            (by omega) openers) ∧
        (∀j:dates,∀t:Hot (Stock.census (Fin n)),
          CreditAt R κ pt k caps j.val (m+days) q per (diameter j) (amount j t)) ∧
        ∀v:(l:Fin n) → R.family.label (k l),
          let g:=regulatorRun R.family N per (m+days)
          let scale:=L.S.a m/L.S.a (m+days)
          let d:=∑j:all,k j
          ∑z:(j:all) → Choice R k j,(∏j:all,WilsonIndependentCollarOriginalDose.weight R k N per
            (m+days) v j (z j) g scale)*rate ≤
              (∏j:all,WilsonIndependentCollarOriginalDose.axisFee R k v j)*C^d*H^((2*A+1)*d)*rate :=by
  intro L all θ
  obtain ⟨book,B,one,elected⟩:=WilsonOriginalCensusJoinedAttendance.original paid
    n front k D κ pt caps nonneg hk q p₀ ask P tube pieces physical p span lag
  obtain ⟨price,timetable⟩:=WilsonOriginalCensusAttendanceVacuum.original paid paths book ask.vac
  refine ⟨book,price,B,one,?_⟩
  filter_upwards [elected] with first chosen
  obtain ⟨V,draw,chart,anchor,original⟩:=chosen
  refine ⟨V,draw,chart,anchor,?_⟩
  intro A
  obtain ⟨C,cn,scheduled⟩:=original A
  refine ⟨C,cn,?_⟩
  intro δ positive
  filter_upwards [scheduled δ positive,timetable] with m admitted banked
  obtain ⟨board,teachers,sold⟩:=admitted
  refine ⟨board,?_,teachers,sold⟩
  intro N valid
  obtain ⟨Z,issued,reset,read⟩:=banked N valid
  exact ⟨Z,issued,reset,read ask.school (board N valid)⟩

end YM.Integration.WilsonOriginalCensusFiledAttendance
end
