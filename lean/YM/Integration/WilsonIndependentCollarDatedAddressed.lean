import YM.Integration.WilsonIndependentCollarAddressedSource
import YM.Integration.WilsonIndependentCollarMaterialIntensity

/-! The optical Wilson election supplies the actual two teacher openings and
the independently seeded nonbare census at every interior date, with the
original finite-cutoff doses outside by multilinearity. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarDatedAddressed
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
          Submitted R V draw D k N (m+days) (j+1) rate δ (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+2))) ∧
          Submitted R V draw D k N (m+days) j rate δ (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+1)))) ∧
        ∀v:(l:Fin n)→R.family.label (k l),
          let g:=regulatorRun R.family N per (m+days)
          let scale:=L.S.a m/L.S.a (m+days)
          let d:=∑j:all,k j
          ∑z:(j:all)→Choice R k j,(∏j:all,WilsonIndependentCollarOriginalDose.weight R k N per
            (m+days) v j (z j) g scale)*rate ≤
              (∏j:all,WilsonIndependentCollarOriginalDose.axisFee R k v j)*C^d*H^((2*A+1)*d)*rate:=by
  intro L roots all
  obtain ⟨B,bpos,issued⟩:=WilsonIndependentCollarOriginalWages.original paid n k D hk q n (mass k univ)
  refine ⟨B,bpos,?_⟩
  filter_upwards [issued] with first receipt
  obtain ⟨V,draw,chart,_year,anchor,closed,tickets,app,hired⟩:=receipt
  refine ⟨V,draw,chart,anchor,?_⟩
  intro A
  obtain ⟨C,non,dates⟩:=hired all front (mem_univ _) A
  refine ⟨C,non,?_⟩
  intro δ ds
  obtain ⟨floor,windows⟩:=eventually_atTop.mp
    (WilsonIndependentCollarDatedTeachers.original paid V app θ P ht room δ ds tube pieces physical p span lag)
  filter_upwards [dates δ ds,eventually_ge_atTop floor] with m pay big
  refine ⟨fun j hj=>windows j (big.trans hj),?_⟩
  intro hm days N per cap cut gap H rate
  have rate0:0≤rate:=mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg (zero_le_one.trans bpos) _)
  have source:=pay hm days N per cap cut gap
  have print (j:ℕ)(hj:m ≤ j)(up:j+2 ≤ m+days):Submitted R V draw D k N (m+days) j rate δ
      (Poetry.Agenda.seed roots MintClock.splits θ (L.clock.J (j+1))):=by
    have hi:V.anchor ≤ j+1:=by omega
    have wallet:=source (j+2) (m+days-(j+2)) (by omega) (by omega) (show V.anchor ≤ j+2 by omega)
    exact WilsonIndependentCollarAddressedSource.print R V D k N (m+days) j hi draw chart closed tickets
      (((windows j (big.trans hj)).1 hi).1) rate0 (Poetry.Agenda.stem ..) cap up
      (fun κ pt cells z=>(wallet.1 κ pt cells z).1)

  exact ⟨print,fun j hj up=>⟨print (j+1) (by omega) up,print j hj (by omega)⟩,(source m 0 le_rfl (by omega) hm).2⟩

end YM.Integration.WilsonIndependentCollarDatedAddressed
end
