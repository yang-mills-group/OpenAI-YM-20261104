import YM.Integration.WilsonThermometerRegisteredRestrictedWithdrawal
import YM.Integration.WilsonThermometerAncestralLastWallet

/-! A physical proper-face withdrawal can use the actual individual radii of the enrolled entrance. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredInheritedAperture
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

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ) (ε:ℝ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {j:ℕ} (mj:m ≤ j) (jt:j ≤ t)
    (L:post j mj (faces (jt.trans_lt top)))
    (reached:Reached R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted q ε mj jt L):
    ∃d:ℝ,1≤d ∧ d≤roof j ∧ ∀v,L.w v=inlet.w v/d:=by
  obtain ⟨P,c,chain,samePost,_,_⟩:=reached
  obtain ⟨_,d,one,cap,perName⟩:=chain.trail.wallet
  have exactRead:=WilsonThermometerAncestralTrace.same R simple A top o refs jt
  have wages:=wage R hk D tab π Γ Ψ books ahead order shelf seats L P exactRead.symm samePost
  exact ⟨d,one,cap,fun v=>by rw [wages];exact perName v⟩

theorem capped (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex) (q:ℕ) (ε:ℝ)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) {j:ℕ} (mj:m ≤ j) (jt:j ≤ t)
    (L:post j mj (faces (jt.trans_lt top)))
    (reached:Reached R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted q ε mj jt L)
    (lim:∀v,inlet.w v≤1) (gpos:0<g (j+1)) (gsmall:g (j+1)≤1):
    let weights:=fun v=>g (j+1)*L.w v
    (∀v,0<weights v ∧ weights v≤1) ∧ ∀s:(J).Mode,WilsonThermometerRegisteredProperScale.restoration weights s≤4 ∧
      ∀Q:Poly J,WilsonThermometerRegisteredRestrictedWithdrawal.restoration weights s Q≤
        2*(1+∑a:(J).Mode with Disjoint s.val a.val,‖(inverseMass Q).part a‖):=by
  intro weights
  obtain ⟨d,one,_,perName⟩:=original R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt inlet counted q ε refs mj jt L reached
  have fields(v):0<weights v ∧ weights v≤1:=by
    have small:L.w v≤1:=by
      rw [perName v];exact (div_le_iff₀ (zero_lt_one.trans_le one)).mpr (by simpa only [one_mul] using (lim v).trans one)
    exact ⟨mul_pos gpos (L.salary.positive v),mul_le_one₀ gsmall (L.salary.positive v).le small⟩
  have toll(s:(J).Mode):0≤Poly.toll weights s ∧ Poly.toll weights s≤1:=by
    refine ⟨Finset.prod_nonneg fun v _=>(fields v).1.le,?_⟩
    exact Finset.prod_le_one (fun v _=>(fields v).1.le) (fun v _=>(fields v).2)
  refine ⟨fields,fun s=>⟨?_,?_⟩⟩
  · unfold WilsonThermometerRegisteredProperScale.restoration
    linarith only [(toll s).2]
  · intro Q
    have hit:=WilsonThermometerRegisteredRestrictedWithdrawal.charge weights s (fun v=>(fields v).1) Q
    let P:=fun a:(J).Mode=>‖(inverseMass Q).part a‖
    have each(a:(J).Mode):Poly.toll weights a*P a≤P a:=mul_le_of_le_one_left (norm_nonneg _) (toll a).2
    have cut:=Finset.sum_le_sum (s:=Finset.univ.filter (fun a:(J).Mode=>Disjoint s.val a.val)) (fun a _=>each a)
    have small:Poly.toll weights s*(∑a:(J).Mode with Disjoint s.val a.val,Poly.toll weights a*‖(inverseMass Q).part a‖)≤
        ∑a:(J).Mode with Disjoint s.val a.val,Poly.toll weights a*‖(inverseMass Q).part a‖:=mul_le_of_le_one_left (Finset.sum_nonneg (fun a _=>mul_nonneg (toll a).1 (norm_nonneg ((inverseMass Q).part a)))) (toll s).2
    simp only [P] at cut
    unfold WilsonThermometerRegisteredRestrictedWithdrawal.restoration
    linarith only [hit,small,cut]

end YM.Integration.WilsonThermometerRegisteredInheritedAperture
