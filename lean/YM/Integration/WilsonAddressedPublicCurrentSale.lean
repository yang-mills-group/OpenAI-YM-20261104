import YM.Integration.WilsonReceivedChronologicalFixedSale
import YM.Integration.WilsonOriginalFullRosterSparseHearing

/-! Price the final dated edge directly on its identity group field. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.WilsonAddressedPublicCurrentSale
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

theorem original (s:(marks).Mode)(charge:Fin n→ℕ)(P cost p target precision rentOrder:ℕ)
    (C tol η:ℝ)(c₂:2 ≤ C)(tp:0<tol)(ep:0<η)
    (late:(eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask charge P cost p target
      C tol η c₂ tp ep)).choose ≤ j)
    (live:j+1<K)(kN:K ≤ N)
    (geometric:R.family.S.a (j+1)/R.family.S.a K ≤ (R.family.path.levels.clock.hatBeta (j+1))^cost)
    (uu:∀v,0 ≤ U v)(ll:∀v,0 ≤ L v)
    (gu:upper.grades=grades)(gl:lower.grades=grades)
    (calendar:WilsonOriginalSparseCensusEdge.Calendar R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
      room.ahead (rows (j+1+1)) (rows (j+1)) upper lower charge rentOrder 1 ((H^precision)⁻¹) C)
    (seen:∀t:Hot (marks),t.val.val⊆s.val → WilsonOriginalSparseCensusEdge.Face R day.hk D₀ Q₀ day.π day.Γ
      Ψ room.books base room.ahead (rows (j+1+1)) (rows (j+1)) upper lower t (calendar.front t)
      charge calendar.tube target ((H^precision)⁻¹))
    (cash:work n P (fare grades charge) (rk)+1+(WilsonOriginalFullRosterCouplingClock.wallet
      (fare grades charge)).pole+1 ≤ rentOrder)
    (jet:work n P (fare grades charge) (rk)+1+1 ≤ precision)(regular:work n P (fare grades charge) (rk)+2 ≤ p)
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G):
    WilsonReceivedChronologicalLastFlat.Here (N:=N) R simple day.hk D₀ Q₀ day.π day.Γ Ψ
      room.books room.ahead rows j s P ∧
    ‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side (j+1) per)) rows (j+1) s‖ ≤
        WilsonOriginalOrdinaryFaceOrder.constant s s.val.card*(g (j+1))^P:=by
  have previous:=(eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask charge P cost p target
    C tol η c₂ tp ep)).choose_spec j late
  have current:=(eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask charge P cost p target
    C tol η c₂ tp ep)).choose_spec (j+1) (late.trans (Nat.le_succ j))
  have reg:=(previous.2 j le_rfl).1
  have hard:=(previous.2 j le_rfl).2.1
  have wallet:= (current.2 (j+1) le_rfl).1
  have hot:j+1<N:=lt_of_lt_of_le live kN
  let crop:=WilsonOriginalMountedRegularFare.crop
    (work n P (fare grades charge) (rk)+1+(WilsonOriginalFullRosterCouplingClock.wallet (fare grades charge)).pole+
      (WilsonOriginalFullRosterCouplingClock.raw (rk)).pole) (g (j+1))
  have votes:=(day.seen per).1
  let read:=WilsonOriginalSparseCensusEdge.original (h:=crop) R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
    room.ahead (rows (j+1+1)) (rows (j+1)) upper lower charge target votes hot room.way room.pass room.month
    room.hospital calendar uu ll seen
  have earned:=WilsonOriginalFullRosterSparseHearing.original (h:=crop) R simple day.hk D₀ Q₀ day.π day.Γ Ψ
    room.books base room.ahead rows upper lower votes hot room.way room.pass room.month room.hospital room.warm
    uu ll calendar seen (by simpa only [gu,gl,Fintype.card_fin] using reg.station) section_ group room.ticket
    p tp (reg.mature.trans (Nat.le_succ j)) reg.failure (base.trans (Nat.le_succ j)) le_rfl current.1
    (1:Config G (R.family.side (j+1) per)) (UVNext.CouplingReset.flags_one (Ψ (j+1)).p)
  have jets:=WilsonReceivedChronologicalPhysicalJets.original R simple ask hard N per hot precision _ jet
  have positive:0 ≤ g (j+1+1):=(ActualRunKernelPackets.regulator_pos R N per _ hot).le
  have rate:=jets.trans (le_mul_of_one_le_left (pow_nonneg positive _) (one_le_two.trans c₂))
  have count:s.val.card≤n:=by simpa only [Fintype.card_fin] using Finset.card_le_univ s.val
  have sale:WilsonReceivedChronologicalInstallment.Sale R simple day.hk D₀ Q₀ day.π day.Γ Ψ room.books base
      room.ahead rows upper lower (le_refl (j+1)) s P (1:Config G (R.family.side (j+1) per)):=
    .issued votes hot room.way room.pass room.month room.hospital room.warm uu ll read c₂ le_rfl
      (base.trans (Nat.le_succ j)) (by omega) kN n cost (fare grades charge) (rk) count
      (by simpa only [gu,gl,max_self,Fintype.card_fin,debitDepth] using
        WilsonReceivedChronologicalPanelClock.priced (grades:=grades) charge s)
      (by simp only [gu,gl,max_self,le_refl]) geometric wallet.coupling cash rfl rate (support _) p tp regular
      wallet.failed (by simp [WilsonOriginalDecoderSpring.bill,G.chord_one]) earned
  exact ⟨⟨base,U,L,_,_,upper,lower,sale⟩,WilsonReceivedChronologicalCurrentFlat.original R simple day.hk D₀ Q₀
    day.π day.Γ Ψ room.books base room.ahead rows upper lower s P sale⟩

end YM.Integration.WilsonAddressedPublicCurrentSale
end
