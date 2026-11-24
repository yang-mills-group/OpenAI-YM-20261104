import YM.Integration.WilsonOriginalCensusFaceSchools
import YM.Integration.WilsonIndependentCollarDatedAddressed

/-! Both material receipts are elected along the original measured optical collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusDatedSchools
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

/-- The two reports and their actual lower and upper books on the one original school. -/
def Paired {G:Gauge}{n q:ℕ}(R:Run G)(V:Realm G (q+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (D k:Fin n→ℕ)(N K j:ℕ)(rate δ upperWidth lowerWidth:ℝ):Prop:=
  ∃(upper:Submitted R V draw D k N K (j+1) rate δ upperWidth)
    (lower:Submitted R V draw D k N K j rate δ lowerWidth),
    ∀(cells:Digits V.draws (Fin n))(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(seed:(v:Fin n)→Choice R k v)
      (per:ℕ)(y:Fin n → Cover)(t:Case D)(deep:∀s:Hot (Stock.census (Fin n)),0 < mass k s.val.val),
      type_of% (WilsonOriginalCensusFaceSchools.original upper lower cells κ pt seed per y t deep)

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n:ℕ)(front:Fin n)(k D:Fin n→ℕ)(hk:∀v,k v<D v)(q θ P:ℕ)(ht:1≤θ)(room:n≤θ)
    (tube:LinkTube G)(pieces physical:ℕ)(p:Bool→ℕ)(span:U→ℕ)(lag:U→Bool→ℕ):
    let L:=R.family.path.levels
    let roots:=WilsonOlderFreshGraphSchool.roots (menu (teacher (prepared s))) simple R.metals.p R.metals.K
    let all:Finset (Fin n):=univ
    ∃B:ℝ,1≤B ∧ ∀ᶠ first:ℕ in atTop,∃V:Realm G (q+1) Credit.leanC,∃draw:V.draws=L,
      V.paid=R.metals.O ∧ V.anchor=first ∧ ∀A:ℕ,∃C:ℝ,0≤C ∧ ∀δ:ℝ,0<δ → ∀ᶠ m:ℕ in atTop,
      (∀j≥m,WilsonIndependentCollarDatedTeachers.At s R simple V D k θ P δ tube pieces physical p span lag j ∧
        WilsonIndependentCollarDatedTeachers.At s R simple V D k θ P δ tube pieces physical p span lag (j+1)) ∧
      ∀(_hm:V.anchor ≤ m)(days N per:ℕ),m+days≤N → m+1≤N →
        L.S.scale (m+days)-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
        let H:=Real.sqrt (R.family.path.β N per (m+1))
        let rate:=H^δ*B^all.card
        (∀j,m ≤ j → j+2 ≤ m+days → Submitted R V draw D k N (m+days) j rate δ
          (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+1)))) ∧
        (∀j,m ≤ j → j+3 ≤ m+days →
          Paired R V draw D k N (m+days) j rate δ
            (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+2)))
            (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+1)))) ∧
        ∀v:(l:Fin n)→R.family.label (k l),
          let g:=regulatorRun R.family N per (m+days)
          let scale:=L.S.a m/L.S.a (m+days)
          let d:=∑j:all,k j
          ∑z:(j:all)→Choice R k j,(∏j:all,WilsonIndependentCollarOriginalDose.weight R k N per
            (m+days) v j (z j) g scale)*rate ≤
              (∏j:all,WilsonIndependentCollarOriginalDose.axisFee R k v j)*C^d*H^((2*A+1)*d)*rate :=by
  intro L roots all
  obtain ⟨B,bpos,dates⟩:=WilsonIndependentCollarDatedAddressed.original paid n front k D hk q θ P ht room
    tube pieces physical p span lag
  refine ⟨B,bpos,?_⟩
  filter_upwards [dates] with start selected
  obtain ⟨V,draw,chart,anchor,scheduled⟩:=selected
  refine ⟨V,draw,chart,anchor,?_⟩
  intro A
  obtain ⟨C,cn,planned⟩:=scheduled A
  refine ⟨C,cn,?_⟩
  intro δ ds
  filter_upwards [planned δ ds] with m atDate
  refine ⟨atDate.1,?_⟩
  intro hm days N per first next range H rate
  obtain ⟨single,pair,fee⟩:=atDate.2 hm days N per first next range
  refine ⟨single,?_,fee⟩
  intro j live up
  obtain ⟨upper,lower⟩:=pair j live up
  exact ⟨upper,lower,fun cells κ pt seed per y t deep=>
    WilsonOriginalCensusFaceSchools.original upper lower cells κ pt seed per y t deep⟩

end YM.Integration.WilsonOriginalCensusDatedSchools
end
