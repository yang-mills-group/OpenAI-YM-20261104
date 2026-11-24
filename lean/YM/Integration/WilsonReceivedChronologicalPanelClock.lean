import YM.Integration.WilsonReceivedChronologicalSaleClock
import YM.Integration.WilsonReceivedChronologicalDates
/-! One before-cutoff clock pays every occupied mask and the whole optical age count. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalPanelClock
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


open WilsonOriginalFullRosterCouplingClock (work wallet raw)
open WilsonOriginalCensusFundedAttendance (Demand)
variable {G:Gauge}(R:Run G)(simple:G.Simple)
variable {n q p₀:ℕ}{grades:Fin n→ℕ}
local notation "stage" l:max => R.alloy.B.a.clock.J l


open WilsonReceivedChronologicalSaleClock (Regular Compulsory)
local notation "faces" => Stock.census (Fin n)
def debitDepth {n:ℕ}(grades:Fin n→ℕ):ℕ:=((∑v,grades v)+1+5)*n
def fare {n:ℕ}(grades charges:Fin n→ℕ):ℕ:=
  (Finset.univ:Finset ((Stock.census (Fin n)).Mode)).sup
    (WilsonOriginalCensusPostedWages.debit (debitDepth grades) charges)

theorem priced (charges:Fin n→ℕ)(s:(faces).Mode):
    WilsonOriginalCensusPostedWages.debit (debitDepth grades) charges s ≤ fare grades charges:=by
  exact Finset.le_sup (Finset.mem_univ s)

local notation "roof" c:max t:max => WilsonOriginalFullRosterBookedHearing.roof grades grades c t
local notation "rank" => (∑v:Fin n,grades v)+1
local notation "res" => (WilsonSingleHardRadius.first R simple)

theorem original (ask:Demand q p₀ grades)(charge:Fin n→ℕ)(P cost p target:ℕ)
    (C tol η:ℝ)(c₂:2 ≤ C)(tp:0<tol)(ep:0<η):
    let f:=fare grades charge
    let d:=rank
    let E:ℝ:=(cost:ℝ)/Real.log 3
    let E0:0 ≤ E:=div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    ∀ᶠ b:ℕ in atTop,res ≤ b ∧ ∀j ≥ b,
      Regular R simple n cost P f d p (roof charge target) C c₂ tol tp b j ∧
      Compulsory R simple ask b j ∧
      (∀s:(faces).Mode,(eventually_atTop.mp (WilsonOriginalOccupiedOpticalRate.original R simple n 1
        (2*s.val.card+(debitDepth grades+∑v∈s.val,charge v)) P E E0 η ep)).choose ≤ (j+1)-1) ∧
      ∀{K N per:ℕ},j+1<K → K ≤ N →
        R.family.S.a b/R.family.S.a K ≤ (R.family.path.levels.clock.hatBeta b)^cost →
        let g:=Pert.Asymptotics.regulatorRun R.family N per b
        0<g ∧ 3*g ≤ 1 ∧ (((j+1)-b:ℕ):ℝ) ≤ E*(1+Real.log (R.family.path.levels.clock.hatBeta (j+1)))^1:=by
  intro f d E E0
  have allFaces:∀ᶠ b:ℕ in atTop,∀s:(faces).Mode,(eventually_atTop.mp
      (WilsonOriginalOccupiedOpticalRate.original R simple n 1
        (2*s.val.card+(debitDepth grades+∑v∈s.val,charge v)) P E E0 η ep)).choose ≤ b:=by
    exact Filter.eventually_all.2 (fun _=>eventually_ge_atTop _)
  obtain ⟨first,dated⟩:=WilsonReceivedChronologicalDates.stages R simple cost
  filter_upwards [WilsonReceivedChronologicalSaleClock.regular R simple n cost P f d p (roof charge target)
    C c₂ tol tp, WilsonReceivedChronologicalSaleClock.compulsory R simple ask,allFaces,
    eventually_ge_atTop res,eventually_ge_atTop first] with b regular hard paid fixed arrived
  refine ⟨fixed,?_⟩
  intro j bj
  refine ⟨regular j bj,hard j bj,fun s=>by simpa only [Nat.add_one_sub_one] using (paid s).trans bj,?_⟩
  intro K N per live active aperture
  have top:b+(K-b)=K:=Nat.add_sub_of_le (by omega)
  have batch:=dated (b:=b) (L:=K-b) (N:=N) (per:=per) arrived (by simpa only [top] using active)
    (by simpa only [top] using aperture) {j} (by simpa using Nat.le_succ_of_le bj)
    (by simpa only [top,Finset.mem_singleton,forall_eq] using live)
  exact ⟨batch.1.1,batch.1.2.1,batch.2 j (by simp)⟩

end YM.Integration.WilsonReceivedChronologicalPanelClock
end
