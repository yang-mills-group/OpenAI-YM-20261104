import YM.Integration.WilsonThermometerRegisteredRestrictedWithdrawal
import YM.Integration.WilsonThermometerAncestralLastWallet

import YM.Integration.WilsonThermometerRegisteredInheritedAperture
import YM.Integration.WilsonThermometerAncestralWallet

/-! Recover the full angular aperture from the genuine source paid above the close
window on the precise received post reached by that source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredDatedAperture
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

open OPE.Therm Pert.Asymptotics WilsonReceivedFirstTrace WilsonPositionThermometerGradedSource WilsonThermometerCourseHearing

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m t N per k:ℕ}
  (top:t<N) (o:Positions (Fin 3) (R.family.side N per))
local notation "faces" itr:max => WilsonThermometerCourseHearing.offered R A simple itr o
local notation "arr" j:max jt:max => WilsonReceivedCloseHistory.history (N:=N) R WilsonThermometerCourseHearing.disks (faces top) j jt

theorem same (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {j:ℕ} (jt:j≤t) :
    arr j jt = faces (jt.trans_lt top) :=by
  induction jt using Nat.decreasingInduction with
  | self =>exact WilsonReceivedCloseHistory.head (N:=N) R WilsonThermometerCourseHearing.disks (faces top)
  | of_succ l lt hyp =>
    rw [←WilsonReceivedCloseHistory.adjacent (N:=N) R WilsonThermometerCourseHearing.disks (faces top) lt,hyp]
    exact WilsonThermometerTestedReturn.push R A simple (show l+1<N by omega) o refs

variable (hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (tab:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ→ℕ} (books:Mentor.Offices.Books D R.rolls tab φ) (ahead:Mentor.Forecast D R.rolls tab φ books)
  (order shelf seats:ℕ)
local notation "ages" => (fun v:Fin 3=>(grade v).val)
local notation "post" j:max mj:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D tab π Γ Ψ books
  ahead WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats j mj y
variable (W:Registration (m:=m) (N:=N) (k:=k) R D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks shelf seats)
  (mt:m≤t)
local notation "B" => budgetR R
local notation "roof" j:max => ∏ l∈Ico j t,(B l)^2*(B (l+1))^7
local notation "g" => regulatorRun R.family N per


open Primitives.GCC.Anchor Extra.Trajectories Comparison.RG02 Comparison.RG02.Order WilsonThermometerAncestralTrace WilsonFiniteOrdinaryInverse WilsonThermometerCenteredAlgebra
open private wage from YM.Integration.WilsonThermometerAncestralLastWallet
local notation "J" => Stock.census (Fin 3)

open private stages from YM.Integration.WilsonThermometerAncestralWallet

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex)
    (q l degree i:ℕ) {price:ℝ} (cap:0 ≤ price) (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N)
    (mi:m ≤ i) (both:i+2 ≤ t) (close:PaceR.Close R degree price i t)
    (booked:(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple degree seats q l cap)).choose ≤ i)
    (weak:(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose ≤ i)
    (start:(g t)^l ≤ Poly.toll inlet.w full)
    (L:post i mi (faces (show i<N by omega)))
    (reached:Reached R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted (q+2) 1 mi (show i ≤ t by omega) L):
    (g (i+1))^(l+2) ≤ Poly.toll L.w full:=by
  obtain ⟨d,one,small,wage⟩:=WilsonThermometerRegisteredInheritedAperture.original R simple A top o hk D tab π Γ Ψ books
    ahead order shelf seats W mt inlet counted (q+2) 1 refs mi (by omega) L reached
  have stage:∀j∈Ico i t,2 ≤ B j:=by
    obtain ⟨_,_,tr,_,_,_⟩:=reached
    exact stages R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted tr
  have wallet:Poly.toll L.w full=Poly.toll inlet.w full/d^3:=by
    rw [show L.w=(fun v=>inlet.w v/d) from funext wage];simp [Poly.toll,full,prod_div_distrib]
  have clock:=(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose_spec i weak N per
  have totalFee:0 ≤ ∑j∈Ico i t,(g (j+2))^(q+2):=by
    apply sum_nonneg;intro j hj
    have h:=mem_Ico.mp hj;exact pow_nonneg (clock (j+2) (by omega) (by omega)).1.le _
  have now:=(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple degree seats q l cap)).choose_spec i
    booked t N per i le_rfl (by omega) top close d 0 0 0 (Poly.toll inlet.w full) (Poly.toll L.w full) 0
    one small le_rfl (zero_le_one.trans (budget_pos R)) (Nat.zero_le _) le_rfl (pow_nonneg (clock t (by omega) top.le).1.le _)
    le_rfl (by simpa only [zero_add] using totalFee) stage start wallet
  exact now.2

end YM.Integration.WilsonThermometerRegisteredCenteredDatedAperture
