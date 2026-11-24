import YM.Integration.WilsonAddressedPublicFirstRanks
import YM.Integration.WilsonReceivedChronologicalFixedEarner
import YM.Integration.WilsonOriginalCensusCanonicalFirstEdgePayer

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstClock
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open WilsonThermometerDeclaredSeeds WilsonReceivedChronologicalFixedReserve
open WilsonReceivedChronologicalFixedEarner (programme)
open WilsonOriginalCensusPublicationClock (Load Open)
open WilsonOriginalCensusCanonicalRows (ceiling)
open ActualRunAdmissionScales
open scoped Topology Classical BigOperators

theorem original {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}(d:Fin n→ℕ)(P cost:ℕ)
    (tol η:ℝ)(tp:0<tol)(ep:0<η):
    let S:=terms d (fun _=>0) P
    let ask:=programme d (fun _=>0) P
    let C:=max ((2:ℝ)^(ask.order+ask.shelf+1)) ((2:ℝ)^(ask.order+ask.shelf+1))
    ∃c₂:2≤C,ask.order=S.order ∧ S.order≤Burn.horizon ask.vac+1 ∧
      ∃load:Load ask.vac S.order S.order ask.shelf S.rent d ask.school.pieces (ask.school.order+1),
        ∀ᶠ b:ℕ in atTop,
          (eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask (fun _:Fin n=>4) P
            cost S.precision S.target C tol η c₂ tp ep)).choose≤b ∧
          ∀j≥b,Open R simple d ask.school.pieces (ask.school.order+1) load j ∧
            Open R simple d ask.school.pieces (ask.school.order+1) load (j+1) ∧
            S.order≤R.alloy.B.a.clock.J (j+1) ∧
            WilsonReceivedMeasuredStampPrice.opening R simple (S.rent+1) S.order ask.vac load.deep load.aged
              (by norm_num:0<(1:ℝ))≤j+1 ∧
            (eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose≤j+1 ∧
            R.alloy.B.a.clock.hatBeta (j+2)≤(R.alloy.B.a.clock.hatBeta (j+1))^2 ∧
            (eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop
              (max 1 (ceiling R d 1)))).choose≤j+1:=by
  intro S ask C
  obtain ⟨c,ord,fit,load,dates⟩:=WilsonReceivedChronologicalFixedReserve.original d (fun _=>0) P R simple cost tol η tp ep
  have same:ask.order=S.order:=ord
  have c₂:2≤C:=by simpa only [C,max_self,same] using c
  let sale:=WilsonReceivedChronologicalPanelClock.original R simple ask (fun _:Fin n=>4) P cost S.precision
    S.target C tol η c₂ tp ep
  let census:=((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (max 1 (ceiling R d 1)))
  refine ⟨c₂,same,fit,load,?_⟩
  filter_upwards [dates,eventually_ge_atTop (eventually_atTop.mp sale).choose,
    eventually_ge_atTop (eventually_atTop.mp census).choose] with b station paid armed
  refine ⟨paid,?_⟩
  intro j born
  obtain ⟨left,right,width,ready,opening,scale⟩:=station.2 j born
  exact ⟨left,right,width,ready,opening,scale,armed.trans (Nat.le_succ_of_le born)⟩

end YM.Integration.WilsonAddressedPublicFirstClock
end
