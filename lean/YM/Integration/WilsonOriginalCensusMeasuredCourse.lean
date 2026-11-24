import YM.Integration.WilsonOriginalCensusDatedSchools
import YM.Integration.WilsonOriginalCensusMeasuredCalendar

/-! The one original school elects both dated materials and the finite-roster numerical winding price on the same physical period tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusMeasuredCourse
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
theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n:ℕ)(front:Fin n)(k D:Fin n→ℕ)(κ:(j:Fin n)→Knob (D j))(pt:Fin n→Chamber)
    (caps:Fin n→ℝ)(nonneg:∀j,0 ≤ caps j)(hk:∀v,k v<D v)(q θ P:ℕ)(ht:1≤θ)(room:n≤θ)
    (tube:LinkTube G)(pieces physical:ℕ)(p:Bool→ℕ)(span:U→ℕ)(lag:U→Bool→ℕ):
    let L:=R.family.path.levels
    let roots:=WilsonOlderFreshGraphSchool.roots (menu (teacher (prepared s))) simple R.metals.p R.metals.K
    let all:Finset (Fin n):=univ
    ∃B:ℝ,1≤B ∧ ∀ᶠ first:ℕ in atTop,∃V:Realm G (q+1) Credit.leanC,∃draw:V.draws=L,
      V.paid=R.metals.O ∧ V.anchor=first ∧ ∀A:ℕ,∃C:ℝ,0≤C ∧ ∀δ:ℝ,0<δ → ∀ᶠ m:ℕ in atTop,
      (∀j≥m,WilsonIndependentCollarDatedTeachers.At s R simple V D k θ P δ tube pieces physical p span lag j ∧
        WilsonIndependentCollarDatedTeachers.At s R simple V D k θ P δ tube pieces physical p span lag (j+1)) ∧
      ∀(_hm:V.anchor ≤ m)(days:ℕ),
        L.S.scale (m+days)-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
        let dates:=↥(Ico m (m+days))
        ∀(diameter:dates→ℕ)(amount:dates→Hot (Stock.census (Fin n))→ℝ),
        (∀j t,0<amount j t) → ∀ᶠ per:ℕ in atTop,∀N:ℕ,m+days≤N → m+1≤N →
        let H:=Real.sqrt (R.family.path.β N per (m+1))
        let rate:=H^δ*B^all.card
        (∀j,m ≤ j → j+2 ≤ m+days → Submitted R V draw D k N (m+days) j rate δ
          (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+1)))) ∧
        (∀j,m ≤ j → j+3 ≤ m+days →
          Paired R V draw D k N (m+days) j rate δ
            (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+2)))
            (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+1)))) ∧
        (∀j:dates,∀t:Hot (Stock.census (Fin n)),
          CreditAt R κ pt k caps j.val (m+days) q per (diameter j) (amount j t)) ∧
        ∀v:(l:Fin n)→R.family.label (k l),
          let g:=regulatorRun R.family N per (m+days)
          let scale:=L.S.a m/L.S.a (m+days)
          let d:=∑j:all,k j
          ∑z:(j:all)→Choice R k j,(∏j:all,WilsonIndependentCollarOriginalDose.weight R k N per
            (m+days) v j (z j) g scale)*rate ≤
              (∏j:all,WilsonIndependentCollarOriginalDose.axisFee R k v j)*C^d*H^((2*A+1)*d)*rate :=by
  intro L roots all
  let salary:ℕ→Gear G→ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  have wage:FundedMarkedCoverRows.prices salary R.kit:=paid.billsPaid.1
  have winding:=WilsonOriginalCensusMeasuredCalendar.original (q:=q) R κ pt simple paid.quiet salary wage k caps nonneg
  obtain ⟨B,one,dated⟩:=WilsonOriginalCensusDatedSchools.original paid n front k D hk q θ P ht room tube pieces physical p span lag
  refine ⟨B,one,?_⟩
  filter_upwards [dated] with first selected
  obtain ⟨V,draw,stamp,center,offered⟩:=selected
  refine ⟨V,draw,stamp,center,?_⟩
  intro A
  obtain ⟨C,cn,school⟩:=offered A
  refine ⟨C,cn,?_⟩
  intro δ under
  filter_upwards [school δ under,winding] with m purchased issued
  refine ⟨purchased.1,?_⟩
  intro anchor days span dates diameter amount pos
  have window:=issued (m+days) (fun _=>V)
    (fun j=>anchor.trans (Finset.mem_Ico.mp j.property).1) (fun _=>draw) (fun _=>stamp) diameter amount pos
  filter_upwards [window] with per funded
  intro N valid live H rate
  obtain ⟨one,two,dose⟩:=purchased.2 anchor days N per valid live span
  exact ⟨one,two,funded,dose⟩

end YM.Integration.WilsonOriginalCensusMeasuredCourse
end
