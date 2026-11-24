import YM.Integration.WilsonThermometerAncestralNumbers
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralLastWallet
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
open WilsonThermometerAncestralTrace
local notation "place" j:max => WilsonReceivedFirstTrace.Position (m:=m) (N:=N) (per:=per) R hk D tab π Γ Ψ books ahead
  WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats j
local notation "edge" e:max j:max U:max L:max => WilsonReceivedFirstTrace.Adjacent R hk D tab π Γ Ψ books ahead
  WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats W
  e 1 j U L


open WilsonThermometerCenteredAlgebra WilsonThermometerAncestralRoster
local notation "B" => budgetR R
local notation "g" => regulatorRun R.family N per
local notation "headroom" mj:max L:max => Oak.expenseReal R hk D tab π Γ books mj
  (L).op (L).lesson ahead order shelf

private theorem wage {j:ℕ} {mj:m≤j}
    {leftRead rightRead:Wallet WilsonThermometerCourseHearing.disks → Config G (R.family.side (j+1) per) → Poly (Stock.census (Fin 3))}
    (a:post j mj leftRead) (b:post j mj rightRead) (eq:leftRead=rightRead) (same:HEq a b) : a.w=b.w := by
  cases eq
  rw [eq_of_heq same]

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {i:ℕ} (mi:m ≤ i) (it:i<t)
    (atCut:post i mi (faces (it.trans top))) (found:Reached R simple A top o hk D tab π Γ Ψ
      books ahead order shelf seats W mt inlet counted (q+2) 1 mi it.le atCut)
    (degree l:ℕ) {price:ℝ} (cap:0 ≤ price)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (days:((t-i:ℕ):ℝ) ≤ price*(Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta i)))^degree)
    (weak:(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose ≤ i)
    (booked:(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple (degree+1) seats q l cap)).choose ≤ i)
    (oldRent:inlet.rent ≤ (g t)^(q+2)) (start:(g t)^l ≤ Poly.toll inlet.w full) :
    (g (i+1))^(l+2) ≤ Poly.toll atCut.w full :=by
  obtain ⟨f,_,⟨Z,hZ,atZ,_,_⟩,edges⟩:=WilsonThermometerAncestralLedger.original R simple A top o hk D tab π Γ Ψ
    books ahead order shelf seats W mt inlet counted q refs mi it.le atCut found degree l cap slow days weak booked oldRent start
  obtain ⟨U,L,_,hL,_,_,fieldAt,_,wallet⟩:=edges i le_rfl it
  have eq:Z=L:=Option.some.inj (hZ.symm.trans hL)
  subst Z
  rw [wage R hk D tab π Γ Ψ books ahead order shelf seats atCut L.post fieldAt.symm atZ]
  exact wallet

end YM.Integration.WilsonThermometerAncestralLastWallet
