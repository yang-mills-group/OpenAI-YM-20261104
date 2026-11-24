import YM.Integration.WilsonThermometerAncestralTrace
import YM.Integration.WilsonThermometerAncestralCopies
import YM.Integration.WilsonThermometerAncestralRent
import YM.Integration.WilsonThermometerAncestralCalendar
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralLongLaunch
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

variable {G:Gauge} (R:Run G) (simple:G.Simple)
def Funded (r:ℕ) (η:ℝ) (j:ℕ):Prop:=
  ∀(t N per:ℕ),j ≤ t → t<N → ∀{M e:ℝ},e ≤ 1 →
    let g:=regulatorRun R.family N per
    M ≤ g t^(r+5) → M+∑l∈Ico j t,e*g (l+2)^(r+5) ≤ η*g j^(r+2)

include simple in
theorem funded (r:ℕ) {η:ℝ} (positive:0<η) : ∀ᶠ j:ℕ in atTop,Funded R r η j:=by
  let b:ℝ:=G.slopeConstant*Real.log (3:ℝ)
  have pb:0<b:=mul_pos (G.slopeConstant_pos simple) (Real.log_pos (by norm_num))
  let K:ℝ:=2^(r+5)+8*2^(r+1)/b
  have K0:0 ≤ K:=by dsimp only [K];positivity
  filter_upwards [WilsonThermometerAncestralCalendar.weak R simple,
    WilsonDyadicReportingPrice.reserve (C:=R.family) simple R.makes K 0 η K0 positive] with j weak ready
  intro t N per jt cut M e charge g face
  obtain ⟨pos,unit⟩:=weak N per j le_rfl (jt.trans cut.le)
  have rented:=WilsonThermometerAncestralRent.original R simple jt cut per (r+1)
  have cutoff: g t ≤ 2*g j:=WilsonLocalCompactRichPortUnits.compared R simple jt cut.le per
  have front:=pow_le_pow_left₀ (weak N per t jt cut.le).1.le cutoff (r+5)
  have fit:g j^(r+5) ≤ g j^(r+3):=pow_le_pow_of_le_one pos.le unit (by omega)
  have sum:(∑l∈Ico j t,e*g (l+2)^(r+5)) ≤ ∑l∈Ico j t,g (l+2)^(r+5):=by
    refine sum_le_sum fun l hl=>?_ 
    exact mul_le_of_le_one_left (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) charge
  have pay:K*g j ≤ η:=by simpa only [Real.rpow_zero,mul_one] using ready per N (jt.trans cut.le)
  have upper:M ≤ (2:ℝ)^(r+5)*(g j)^(r+3):=by
    rw [mul_pow] at front
    exact face.trans (front.trans (mul_le_mul_of_nonneg_left fit (by positivity)))
  calc
    _ ≤ 2^(r+5)*g j^(r+3)+(8*2^(r+1)/b)*g j^(r+3):=add_le_add upper (sum.trans rented)
    _ = K*g j*g j^(r+2):=by dsimp only [K];rw [show r+3=(r+2)+1 by omega,pow_succ];ring
    _ ≤ _:=mul_le_mul_of_nonneg_right pay (pow_nonneg pos.le _)

variable (A:Group R.family 6) {m t N per k:ℕ}
  (top:t<N) (o:Positions (Fin 3) (R.family.side N per))
local notation "faces" itr:max => WilsonThermometerCourseHearing.offered R A simple itr o
local notation "arr" j:max jt:max => WilsonReceivedCloseHistory.history (N:=N) R WilsonThermometerCourseHearing.disks (faces top) j jt

variable (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (tab:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ → ℕ} (books:Mentor.Offices.Books D R.rolls tab φ) (ahead:Mentor.Forecast D R.rolls tab φ books)
  (order shelf seats:ℕ)
local notation "ages" => (fun v:Fin 3=>(grade v).val)
local notation "post" j:max mj:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D tab π Γ Ψ books
  ahead WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats j mj y
variable (W:Registration (m:=m) (N:=N) (k:=k) R D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks shelf seats)
  (mt:m ≤ t)
open WilsonOriginalCopiedHistory FVA1Physical.TwoReset
open WilsonReceivedFirstTrace
local notation "J₃" => Stock.census (Fin 3)
local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "teacher" j:max mj:max P:max => Oak.student (i:=j) (n:=per) R hk D tab π Γ books mj
  (P).op (P).lesson ahead WilsonThermometerCourseHearing.disks (P).model order (P).voter
local notation "store" P:max c:max cut:max => WilsonReceivedFirstTrace.install R hk D tab π Γ Ψ books ahead
  WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats W P c cut

/-- The entire dated library descends on one source. Its regular error is funded even on
    an unbounded fine interval. The original marker wage is recorded with its actual divisor. -/
theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N) (path:PlanV.Path D R.alloy tab (Burn.horizon k) N m π Γ)
    (pass:Pass D tab R.alloy R.kit) (month:Scholar.Month R.rolls D tab R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (packed:order+shelf ≤ Burn.horizon k+2) (r:ℕ) {ε η:ℝ}
    (deep:2*(r+5)+8 ≤ order) (aged:(r+5)+3 ≤ 3*k+2) (ep:0<ε) (unit:ε ≤ 1) {j:ℕ}
    (late:WilsonReceivedMeasuredStampPrice.opening R W.simple (r+5) order k deep aged ep ≤ j+1)
    (small:∀l,j ≤ l → l ≤ N → 0<regulatorRun R.family N per l ∧ regulatorRun R.family N per l ≤ 1)
    (paid:Funded R r η j) (start:inlet.rent ≤ (regulatorRun R.family N per t)^(r+5))
    (mj:m ≤ j) (jt:j ≤ t) :
    ∃L:post j mj (faces (jt.trans_lt top)), WilsonThermometerAncestralTrace.Reached R simple A top o hk D tab π Γ Ψ books ahead
      order shelf seats W mt inlet counted (r+5) ε mj jt L ∧ L.rent ≤ η*(regulatorRun R.family N per j)^(r+2) ∧
      (∃d:ℝ,1 ≤ d ∧ d ≤ ∏l∈Ico j t,(budgetR R l)^2*(budgetR R (l+1))^7 ∧ ∀v,L.w v=inlet.w v/d) ∧
      ∀(x:Wallet WilsonThermometerCourseHearing.disks)
        (upper:WilsonOriginalCopiedHistory.Values G (J₃) (R.family.side t per)),
        (∀(grid:Side)(div:(R.family.side t per).val ∣ grid.val)(d:ℕ),d ≤ order → ∀z,
          upper grid div d z=peek div (teacher t mt inlet) ages (π (t+1)) tape₀ x d z) →
        ∀(grid:Side)(div:(R.family.side j per).val ∣ grid.val)(d:ℕ),d ≤ order → ∀field,
        (WilsonOriginalCoveredEvolution.run R top π Γ (Burn.horizon k+2) order ages upper) j jt grid div d field=
          peek div (teacher j mj L) ages (π (j+1)) tape₀ x d field :=by
  obtain ⟨L,reached,rent,wages⟩:=WilsonThermometerAncestralTrace.original R simple A top o hk D tab π Γ Ψ books ahead
    order shelf seats W mt inlet counted refs path pass month fits packed (r+5) deep aged ep unit late small mj jt
  refine ⟨L,reached,rent.trans (paid t N per jt top unit start),wages,?_⟩
  intro x upper fields
  exact WilsonThermometerAncestralCopies.original R simple A top o hk D tab π Γ Ψ books ahead order shelf seats W mt
    inlet counted refs mj jt L (r+5) ε reached pass month fits x upper fields

end YM.Integration.WilsonThermometerAncestralLongLaunch
