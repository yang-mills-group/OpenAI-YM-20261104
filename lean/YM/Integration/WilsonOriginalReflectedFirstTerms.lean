import YM.Integration.WilsonAddressedPublicFirstRoseTerms

/-! First-date prices on the very same arbitrary finite physical roster and positive panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalReflectedFirstTerms
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

variable {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}(d:Fin n → ℕ)(P cost:ℕ)
  (tol η:ℝ)(tp:0<tol)(ep:0<η)
set_option quotPrecheck false
local notation "ask₀" => programme d (fun _=>0) P
local notation "paid₀" => terms d (fun _=>0) P
local notation "C₀" => max ((2:ℝ)^((ask₀).order+(ask₀).shelf+1)) ((2:ℝ)^((ask₀).order+(ask₀).shelf+1))

/-- Original first-edge dockets on the same order as the already enrolled interior. -/
structure At (b j:ℕ) : Prop where
  fit : (ask₀).order ≤ Burn.horizon (ask₀).vac+1
  high : Open R simple d (ask₀).school.pieces ((ask₀).school.order+1) (ask₀).load (j+1)
  low : Open R simple d (ask₀).school.pieces ((ask₀).school.order+1) (ask₀).load j
  stage : (ask₀).order ≤ R.alloy.B.a.clock.J (j+1)
  stamped : WilsonReceivedMeasuredStampPrice.opening R simple ((paid₀).rent+1) (ask₀).order (ask₀).vac
    (ask₀).load.deep (ask₀).load.aged (by norm_num:0<(1:ℝ)) ≤ j+1
  income : (eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1
  sold : (eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop
    (max 1 (ceiling R d 1)))).choose ≤ j+1
  two : 2 ≤ (C₀)
  flat : (eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple (ask₀) (fun _=>4) P
    cost (paid₀).precision (paid₀).target (C₀) tol η two tp ep)).choose ≤ b

theorem original :
    ∀ᶠ b:ℕ in atTop,∀j≥b,At R simple d P cost tol η tp ep b j:=by
  let ask:=ask₀
  let S:=paid₀
  obtain ⟨two,same,fit,load,posted⟩:=WilsonAddressedPublicFirstClock.original R simple d P cost tol η tp ep
  let stock:=eventually_atTop.mp (WilsonOriginalCensusPublicationClock.original R simple d
    ask.school.pieces (ask.school.order+1) ask.load)
  let stamp:=WilsonReceivedMeasuredStampPrice.opening R simple (S.rent+1) ask.order ask.vac ask.load.deep ask.load.aged
    (by norm_num:0<(1:ℝ))
  filter_upwards [posted,eventually_ge_atTop stock.choose,eventually_ge_atTop stamp] with b ready financed active
  intro j bj
  obtain ⟨_left,_right,stage,_retained,income,_growth,sold⟩:=ready.2 j bj
  exact ⟨same.le.trans fit,stock.choose_spec _ (financed.trans (Nat.le_succ_of_le bj)),
    stock.choose_spec _ (financed.trans bj),same.le.trans stage,active.trans (Nat.le_succ_of_le bj),
    income,sold,two,ready.1⟩

/-- A single order pays all declared grades with this physical roster. -/
def order (R:Run G){n:ℕ}(d:Fin n → ℕ)(target:ℕ):ℕ:=max target (WilsonOriginalStarSceneWords.maximum R d)

theorem ranked_before (target:ℕ):WilsonAddressedPublicFirstOrigin.ceiling R d≤
    (terms d (fun _=>0) (order R d target+1)).order:=
  (WilsonAddressedPublicFirstActivation.before R d).trans ((Nat.le_succ_of_le (le_max_right _ _)).trans
    (WilsonAddressedPublicFirstActivation.rank_budget ..))

end YM.Integration.WilsonOriginalReflectedFirstTerms
end
