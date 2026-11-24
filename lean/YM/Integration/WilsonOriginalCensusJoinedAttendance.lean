import YM.Integration.WilsonOriginalCensusAttendanceStation
import YM.Integration.WilsonOriginalCensusMeasuredCourse

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCensusJoinedAttendance
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

/-- The school's two complete original received posts and their numerical
credit use the same period floor, Wilson course and independent coefficient
program. Each cutoff's physical timetable is fixed before every period. -/
theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n:ℕ)(front:Fin n)(k D:Fin n → ℕ)(κ:(j:Fin n) → Knob (D j))(pt:Fin n → Chamber)
    (caps:Fin n → ℝ)(nonneg:∀j,0 ≤ caps j)(hk:∀v,k v < D v)(q p₀:ℕ)(ask:Demand q p₀ k)
    (P:ℕ)(tube:LinkTube G)(pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):
    let L:=R.family.path.levels
    let all:Finset (Fin n):=univ
    let θ:=Burn.horizon ask.vac
    ∃ book:WilsonOriginalCensusPhysicalAttendance.Room (prepared s) R simple,
    ∃B:ℝ,1 ≤ B ∧ ∀ᶠ first:ℕ in atTop,∃V:Realm G (q+1) Credit.leanC,∃draw:V.draws=L,
      V.paid=R.metals.O ∧ V.anchor=first ∧ ∀A:ℕ,∃C:ℝ,0 ≤ C ∧ ∀δ:ℝ,0 < δ → ∀ᶠ m:ℕ in atTop,
      ∃ board:(N:ℕ) → m ≤ N → Day (prepared s) R simple ask.school m N,
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
  obtain ⟨⟨book⟩,physicalSeats⟩:=WilsonOriginalCensusPhysicalAttendance.original paid
  obtain ⟨B,one,issued⟩:=WilsonOriginalCensusMeasuredCourse.original paid n front k D κ pt caps
    nonneg hk q θ P ask.fit ask.common tube pieces physical p span lag
  refine ⟨book,B,one,?_⟩
  filter_upwards [issued] with first start
  obtain ⟨V,draw,chart,anchor,scheduled⟩:=start
  refine ⟨V,draw,chart,anchor,?_⟩
  intro A
  obtain ⟨C,cn,offer⟩:=scheduled A
  refine ⟨C,cn,?_⟩
  intro δ under
  filter_upwards [offer δ under,physicalSeats ask.vac ask.school ask.deep,
    WilsonOriginalCensusPublicationClock.both R simple k ask.school.pieces (ask.school.order+1) ask.load]
    with m dated desks opening
  let board (N:ℕ)(band:m ≤ N):=Classical.choice (choose_day desks band)
  refine ⟨board,dated.1,?_⟩
  intro hm days window dates diameter amount pos
  filter_upwards [dated.2 hm days window diameter amount pos] with per sold
  intro N valid live H rate day
  obtain ⟨_,pair,credit,dose⟩:=sold N valid live
  refine ⟨?_,credit,dose⟩
  intro j young reached
  have ready:=opening j young
  refine ⟨ready,?_⟩
  exact WilsonOriginalCensusAttendancePair.original book ask day.π day.Γ day.hk day.lessons (day.Ψ per)
    (day.seen per) young (by omega) ready (pair j young reached)

end YM.Integration.WilsonOriginalCensusJoinedAttendance
end
