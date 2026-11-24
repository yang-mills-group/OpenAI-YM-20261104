import YM.Integration.WilsonAddressedPublicFirstCharge
import YM.Integration.WilsonReceivedChronologicalFixedSale
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstDay
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical



open WilsonOriginalFullRosterCouplingClock (work)
open WilsonOriginalCensusFundedAttendance (Demand)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonOriginalCensusPhysicalAttendance (roots tab Room)
open WilsonReceivedChronologicalPanelClock (debitDepth fare)
open WilsonOriginalOccupiedWindow WilsonOriginalOccupiedCorridor WilsonOriginalJointTrialHearing
variable {G:Gauge}{R:Run G}{simple:G.Simple}{semester:WilsonOriginalAllOrderCourse.Schedule G}
variable {n q₀ p₀:ℕ}{grades:Fin n→ℕ}(ask:Demand q₀ p₀ grades)(room:Room semester R simple)
variable {o N per j b u K:ℕ}(day:Day semester R simple ask.school o N)(base:o ≤ j)
local notation "marks" => Stock.census (Fin n)
local notation "D₀" => roots semester R simple
local notation "Q₀" => tab semester R simple
local notation "Ψ" => day.Ψ per
local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "rk" => (∑v:Fin n,grades v)+1
variable {U L:Fin n→ℝ}{l:ℕ}
variable (rows:∀i:ℕ,Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))
variable (highRow : Config G (R.family.side (j+1+1) per)→Marker.Poly (Stock.census (Fin n)))
variable (lowRow : Config G (R.family.side (j+1) per)→Marker.Poly (Stock.census (Fin n)))
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R day.hk (roots semester R simple) (tab semester R simple) day.π day.Γ (day.Ψ per)
  room.books (Nat.le_succ_of_le base) room.ahead U (((∑v,grades v)+1+5)*Fintype.card (Fin n)) highRow)
variable (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R day.hk (roots semester R simple) (tab semester R simple) day.π day.Γ (day.Ψ per)
  room.books base room.ahead L l lowRow)
local notation "home" => (upper.post.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "g" t:max => regulatorRun R.family N per t

theorem original (upperAt : highRow=rows (j+1+1))(lowerAt : lowRow=rows (j+1))
    (s:(marks).Mode)(charge:Fin n→ℕ)(P cost p target precision rentOrder size:ℕ)
    (C tol η:ℝ)(c₂:2 ≤ C)(tp:0<tol)(ep:0<η)
    (late:(eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask charge P cost p target
      C tol η c₂ tp ep)).choose ≤ b)
    (fixed:WilsonSingleHardRadius.first R simple ≤ o)(ou:o ≤ u)(ub:u ≤ b)(bj:b ≤ j)(live:j+1<K)(kN:K ≤ N)
    (geometric:R.family.S.a b/R.family.S.a K ≤ (R.family.path.levels.clock.hatBeta b)^cost)
    (np:0<n)(uu:∀v,0 ≤ U v)(ll:∀v,0 ≤ L v)
    (gu:upper.grades=grades)(gl:lower.grades=grades)(printed:upper.order=ask.order)
    (stock:upper.shelf=ask.shelf)(seats:upper.seats=ask.school.pieces)
    (calendar:WilsonOriginalSparseCensusEdge.Calendar R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
      room.ahead highRow lowRow upper lower charge rentOrder 1 ((H^precision)⁻¹) C)
    (seen:∀t:Hot (marks),t.val.val⊆s.val → WilsonOriginalSparseCensusEdge.Face R day.hk D₀ Q₀ day.π day.Γ
      Ψ room.books base room.ahead highRow lowRow upper lower t (calendar.front t)
      charge calendar.tube target ((H^precision)⁻¹))
    (cash:work n P (fare grades charge) (rk)+1+(WilsonOriginalFullRosterCouplingClock.wallet
      (fare grades charge)).pole+1 ≤ rentOrder)
    (jet:work n P (fare grades charge) (rk)+1+1 ≤ precision)(regular:work n P (fare grades charge) (rk)+2 ≤ p)
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    (Z:Support (R.family.side b per))(center:Site (R.family.side b per))(held:center∈Z)
    (homes:∀v∈s.val,sites R (home) (by omega:b ≤ j+1) v∈Z)(roof:coverNumber (Ψ b).p.B Z ≤ size) :
  (∃highFiled : WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R day.hk D₀ Q₀ day.π day.Γ
        Ψ room.books (Nat.le_succ_of_le base) room.ahead U (((∑v,grades v)+1+5)*Fintype.card (Fin n)) (rows (j+1+1)),
     ∃lowFiled : WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
        room.ahead L l (rows (j+1)), HEq highFiled upper ∧ HEq lowFiled lower ∧
       WilsonReceivedChronologicalTwoFlatSale.Sale R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
        room.ahead rows highFiled lowFiled u b s P size η) ∧
  ∀v:ℕ, u≤v → (fv:v≤b) →
    WilsonReceivedChronologicalLastFlat.Ticket (N:=N) R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books
      room.ahead rows j u b v s P size η ∧
    ‖WilsonOriginalJointTrialHearing.read R N per (1:Config G (R.family.side v per))
        ((fv.trans bj).trans (Nat.le_add_right j 2)) highRow s-
      WilsonOriginalJointTrialHearing.read R N per (1:Config G (R.family.side v per))
        ((fv.trans bj).trans (Nat.le_succ _)) lowRow s‖ ≤
      WilsonReceivedChronologicalLastFlat.wage s P size η * (g b)^P := by
  subst highRow
  subst lowRow
  obtain ⟨sale,hears⟩:=WilsonReceivedChronologicalFixedSale.original ask room day base rows upper lower s
    charge P cost p target precision rentOrder size C tol η c₂ tp ep late fixed ou ub bj live kN geometric
    np uu ll gu gl printed stock seats calendar seen cash jet regular support section_ group Z center held homes roof
  have actual:=WilsonAddressedPublicFirstCharge.original R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
    room.ahead rows upper lower sale (Nat.le_succ_of_le bj)
  exact ⟨⟨upper,lower,HEq.rfl,HEq.rfl,sale⟩,fun v uv vb=>⟨(hears v uv vb).1,actual.2.2 v uv vb⟩⟩

end YM.Integration.WilsonAddressedPublicFirstDay
end
