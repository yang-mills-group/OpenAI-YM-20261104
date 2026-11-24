import YM.Integration.WilsonReceivedChronologicalLastFlat
import YM.Integration.WilsonReceivedChronologicalFixedSchool
import YM.Integration.WilsonReceivedChronologicalPhysicalJets
/-! The two genuine flat receivers of a paid, dated mixed material on the fixed old Wilson law. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedSale
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
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R day.hk (roots semester R simple) (tab semester R simple) day.π day.Γ (day.Ψ per)
  room.books (Nat.le_succ_of_le base) room.ahead U (((∑v,grades v)+1+5)*Fintype.card (Fin n)) (rows (j+1+1)))
variable (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R day.hk (roots semester R simple) (tab semester R simple) day.π day.Γ (day.Ψ per)
  room.books base room.ahead L l (rows (j+1)))
local notation "home" => (upper.post.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "g" t:max => regulatorRun R.family N per t

theorem original (s:(marks).Mode)(charge:Fin n→ℕ)(P cost p target precision rentOrder size:ℕ)
    (C tol η:ℝ)(c₂:2 ≤ C)(tp:0<tol)(ep:0<η)
    (late:(eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask charge P cost p target
      C tol η c₂ tp ep)).choose ≤ b)
    (fixed:WilsonSingleHardRadius.first R simple ≤ o)(ou:o ≤ u)(ub:u ≤ b)(bj:b ≤ j)(live:j+1<K)(kN:K ≤ N)
    (geometric:R.family.S.a b/R.family.S.a K ≤ (R.family.path.levels.clock.hatBeta b)^cost)
    (np:0<n)(uu:∀v,0 ≤ U v)(ll:∀v,0 ≤ L v)
    (gu:upper.grades=grades)(gl:lower.grades=grades)(printed:upper.order=ask.order)
    (stock:upper.shelf=ask.shelf)(seats:upper.seats=ask.school.pieces)
    (calendar:WilsonOriginalSparseCensusEdge.Calendar R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
      room.ahead (rows (j+1+1)) (rows (j+1)) upper lower charge rentOrder 1 ((H^precision)⁻¹) C)
    (seen:∀t:Hot (marks),t.val.val⊆s.val → WilsonOriginalSparseCensusEdge.Face R day.hk D₀ Q₀ day.π day.Γ
      Ψ room.books base room.ahead (rows (j+1+1)) (rows (j+1)) upper lower t (calendar.front t)
      charge calendar.tube target ((H^precision)⁻¹))
    (cash:work n P (fare grades charge) (rk)+1+(WilsonOriginalFullRosterCouplingClock.wallet
      (fare grades charge)).pole+1 ≤ rentOrder)
    (jet:work n P (fare grades charge) (rk)+1+1 ≤ precision)(regular:work n P (fare grades charge) (rk)+2 ≤ p)
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    (Z:Support (R.family.side b per))(center:Site (R.family.side b per))(held:center∈Z)
    (homes:∀v∈s.val,sites R (home) (by omega:b ≤ j+1) v∈Z)(roof:coverNumber (Ψ b).p.B Z ≤ size):
    WilsonReceivedChronologicalTwoFlatSale.Sale R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
      room.ahead rows upper lower u b s P size η ∧
    ∀v:ℕ,u ≤ v → v ≤ b →
      WilsonReceivedChronologicalLastFlat.Ticket (N:=N) R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books
        room.ahead rows j u b v s P size η ∧
      ‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side v per)) rows (j+1) s‖ ≤
        WilsonReceivedChronologicalLastFlat.wage s P size η*(g b)^P:=by
  have employees:=upper.post.capacity.trans seats
  have floor:o ≤ b:=ou.trans ub
  have hot:j+1<N:=lt_of_lt_of_le live kN
  have plan:= (eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask charge P cost p target
      C tol η c₂ tp ep)).choose_spec b late
  obtain ⟨paid,hard,allOpt,spans⟩:=plan.2 j bj
  have span:=(spans (per:=per) live kN geometric).2.2
  have votes:=(day.seen per).1
  have reg:(Ψ b).p.supportExponent=100:=by
    rw [(votes.1.walk b floor (by omega)).truep.point]
    exact support b
  have jets:=WilsonReceivedChronologicalPhysicalJets.original R simple ask hard N per hot precision _ jet
  have positive:0 ≤ g (j+1+1):=(ActualRunKernelPackets.regulator_pos R N per _ hot).le
  have grant:=jets.trans (le_mul_of_one_le_left (pow_nonneg positive _) (one_le_two.trans c₂))
  have count:∀t:(marks).Mode,t.val.card ≤ n:=fun t=>by simpa only [Fintype.card_fin] using Finset.card_le_univ t.val
  have sale:WilsonReceivedChronologicalTwoFlatSale.Sale R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
      room.ahead rows upper lower u b s P size η:=
    .issued votes hot room.way room.pass room.month room.hospital room.warm uu ll calendar seen c₂ le_rfl
      floor (by omega) (by omega) kN n cost (fare grades charge) (rk) (count s)
      (by simpa only [gu,gl,max_self,Fintype.card_fin,debitDepth] using
        WilsonReceivedChronologicalPanelClock.priced (grades:=grades) charge s)
      (by simp only [gu,gl,max_self,le_refl]) geometric paid.coupling cash rfl grant (support _) p tp regular paid.failed
      (by simpa only [gu,gl,Fintype.card_fin] using paid.station) section_ group room.ticket (by exact paid.mature.trans (by omega))
      paid.failure (by omega) ou ub (fixed.trans ou) (by simpa only [stock] using hard.shelf)
      (by simpa only [employees] using ask.load.count) hard.one (by simpa only [employees] using hard.many)
      hard.wide hard.neighbor paid.mature p₀ (by simpa only [seats] using hard.seats)
      (by simpa only [printed] using ask.load.deep) ask.load.aged (by norm_num:0<(1:ℝ)) (hard.rent N per hot)
      (by simpa only [employees,printed] using hard.fee) np hard.group count hard.cap Z center held homes 1
      ((cost:ℝ)/Real.log 3) ep (div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) roof reg
      paid.zero (by simpa only [debitDepth,Fintype.card_fin] using allOpt s) span
  refine ⟨sale,?_⟩
  intro v uv vb
  exact ⟨Or.inl ⟨uv,vb,⟨base,U,L,_,l,upper,lower,sale⟩⟩,
    WilsonReceivedChronologicalTwoFlatSale.paid R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
      room.ahead rows upper lower sale uv vb⟩

end YM.Integration.WilsonReceivedChronologicalFixedSale
end
