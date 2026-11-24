import YM.Integration.WilsonReceivedChronologicalPanelClock
import YM.Integration.WilsonOriginalOneArmMaterialGrant
/-! Choose the paid mixed programme's native salaries and ranks before the physical period and cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedReserve
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



open WilsonOriginalFullRosterCouplingClock (work wallet)
open WilsonOriginalCensusFundedAttendance (quote)
open WilsonReceivedChronologicalPanelClock (fare)
open WilsonOriginalCensusPublicationClock (Load Open)
variable {G:Gauge}{n:ℕ}(grades power:Fin n→ℕ)(P:ℕ)

def charges (v:Fin n):ℕ:=2*(power v+4)
local notation "fees" => charges power
local notation "w₀" => work n P (fare grades (fees)) ((∑v:Fin n,grades v)+1)

structure Terms (grades power:Fin n→ℕ)(P:ℕ) where
  rent : ℕ
  precision : ℕ
  target : ℕ
  order : ℕ
  cash : work n P (fare grades (charges power)) ((∑v,grades v)+1)+1+
    (wallet (fare grades (charges power))).pole+1 ≤ rent+1
  marked : work n P (fare grades (charges power)) ((∑v,grades v)+1)+1+1 ≤ precision
  failed : work n P (fare grades (charges power)) ((∑v,grades v)+1)+2 ≤ precision
  enough : 2*(precision+1) ≤ target
  deep : 2*(rent+1)+8 ≤ order
  ceiling : 3*WilsonOriginalFullRosterBookedHearing.roof grades grades (charges power) target ≤ order

def terms:Terms grades power P:=
  let p:=w₀+2
  let r:=w₀+1+(wallet (fare grades (fees))).pole
  let t:=2*(p+1)
  let q:=max (2*(r+1)+8) (3*WilsonOriginalFullRosterBookedHearing.roof grades grades (fees) t)
  ⟨r,p,t,q,le_rfl,le_rfl,le_rfl,le_rfl,le_max_left ..,le_max_right ..⟩

theorem original (R:Run G)(simple:G.Simple)(cost:ℕ)(tol η:ℝ)(tp:0<tol)(ep:0<η):
    let menu:=terms grades power P
    let ask:=quote menu.order menu.rent grades
    let C:ℝ:=2^(menu.order+ask.shelf+1)
    ∃c₂:2 ≤ C,ask.order=menu.order ∧ menu.order ≤ Burn.horizon ask.vac+1 ∧
    ∃demand:Load ask.vac menu.order menu.order ask.shelf menu.rent grades ask.school.pieces (ask.school.order+1),
      ∀ᶠ b:ℕ in atTop,
        (eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask (charges power)
          P cost menu.precision menu.target C tol η c₂ tp ep)).choose ≤ b ∧
        ∀j ≥ b,(Open R simple grades ask.school.pieces (ask.school.order+1) demand j) ∧
          (Open R simple grades ask.school.pieces (ask.school.order+1) demand (j+1)) ∧
          menu.order ≤ R.alloy.B.a.clock.J (j+1) ∧
          WilsonReceivedMeasuredStampPrice.opening R simple (menu.rent+1) menu.order ask.vac demand.deep demand.aged
            (by norm_num:0<(1:ℝ)) ≤ j+1 ∧
          (eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1 ∧
          R.alloy.B.a.clock.hatBeta (j+2) ≤ (R.alloy.B.a.clock.hatBeta (j+1))^2:=by
  intro M ask C
  have c₂:2 ≤ C:=by
    simpa only [C,pow_one] using pow_le_pow_right₀ (by norm_num:1≤(2:ℝ)) (by omega:1 ≤ M.order+ask.shelf+1)
  have same:ask.order=M.order:=max_eq_left M.deep
  have enrolled:M.order≤Burn.horizon ask.vac+1:=by
    change M.order≤Burn.horizon (n+max M.order (2*(M.rent+1)+8)+(∑v,grades v)+M.rent+4)+1
    simp only [Burn.horizon]
    omega
  have demand:Load ask.vac M.order M.order ask.shelf M.rent grades ask.school.pieces (ask.school.order+1):=by
    simpa only [same] using ask.load
  refine ⟨c₂,same,enrolled,demand,?_⟩
  have halls:=WilsonOriginalCensusPublicationClock.original R simple grades ask.school.pieces (ask.school.order+1) demand
  let seated:=(eventually_atTop.mp halls).choose
  let bought:=WilsonReceivedChronologicalPanelClock.original R simple ask (charges power) P cost M.precision M.target C tol η c₂ tp ep
  have ages:=R.alloy.B.a.fits.deep.eventually_ge_atTop M.order
  filter_upwards [eventually_ge_atTop (eventually_atTop.mp bought).choose,eventually_ge_atTop seated,
    eventually_ge_atTop (eventually_atTop.mp ages).choose,
    eventually_ge_atTop (WilsonReceivedMeasuredStampPrice.opening R simple (M.rent+1) M.order ask.vac demand.deep demand.aged
      (by norm_num:0<(1:ℝ))),eventually_ge_atTop (eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose]
    with b gate tutors occupied ready era
  refine ⟨gate,?_⟩
  intro j later
  have clock:=(eventually_atTop.mp bought).choose_spec b gate
  obtain ⟨_,τ,_,_⟩:=clock.2 j later
  have four:=(eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose_spec (j+1) τ.wide
  have step:=(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec (j+1) τ.neighbor
  have cap:2≤R.alloy.B.a.clock.hatBeta (j+1):=le_trans (by norm_num:2≤(20:ℝ)) four
  exact ⟨(eventually_atTop.mp halls).choose_spec j (tutors.trans later),
    (eventually_atTop.mp halls).choose_spec (j+1) (by omega),(eventually_atTop.mp ages).choose_spec _ (by omega),
    by omega,by omega,step.trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_right cap (by linarith))⟩

end YM.Integration.WilsonReceivedChronologicalFixedReserve
end
