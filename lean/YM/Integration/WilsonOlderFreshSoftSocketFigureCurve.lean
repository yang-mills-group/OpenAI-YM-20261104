import YM.Integration.WilsonOlderFreshSoftSocketFigureRoom
import YM.Integration.WilsonOlderFreshSoftSocketFitted

/-! Both independent soft readings and the original finite physical source on one realm and issued vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketFigureCurve
open Function Filter Finset Lattice Laurent Bloch Precision Wilson RG Source Labels Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Winding WilsonCoeffUV.Soil WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PertExtension NativeCurvatureTensor
open OriginalMarkedSourceComet WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftTrialCharge (power bill wages)
open WilsonOriginalPublicTrialInput (vector)
open scoped Classical BigOperators Topology
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Iron
open QuadraticLocal QuadraticLocal.Mentor
open WilsonIndependentCollarRootedWidth
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {crop:Campaign R} {W:Campaign.Pillars R crop}

open WilsonOlderFreshSoftRoseCourse (grade seat Hearing)
open WilsonOlderFreshSoftTrialCharge (power bill)


open WilsonOlderFreshSoftRoseMarket (Probe row scaled)
open WilsonOlderFreshSoftRoseSecant (deficit actual)
open WilsonNeutralOffsetCutoff (named)
open WilsonThermometerAlignedCells (atOrigin)

variable (R) (A₀:WilsonPositionThermometerCapStation.Group R.family 6)
local notation "Faces" => Finset (Fin 3)
local notation "Sites" N:max per:max => Site (R.family.side N per)


open WilsonOriginalPublicFixedCourse (sites digits home)
open WilsonOlderFreshSoftRoseMesh (filed table fare)
open WilsonMaxwellThermometerNominatedSecant (bill)

open WilsonOlderFreshSoftRoseNodes (TestAt enrolled Covered)
open WilsonOlderFreshSoftTrialCut (source)
open WilsonOlderFreshSoftMoment (mixed)

open WilsonOlderFreshSoftRoseIncome (Stock)
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation
open WilsonVacuumPreResetDatedDeposit (Issued)
open PertExtension.Series WilsonCoeffUV.Blue.Cameo
open WilsonOriginalAllOrderCourse
open WilsonOriginalOccupiedForestIntegral
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonVacuumPreResetDatedCourse
open WilsonReportingAbsoluteInletForecastBooks
open WilsonOlderFreshSoftSocketFitted (residual)
open WilsonOlderFreshSoftSocketOptical (fixed)
open WilsonOlderFreshSoftSocketCensus (fee)
open WilsonOriginalPublicTrialInput (fitted)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonIndependentCollarCensusCourse
open Filter

def Bought (D:Fin 3→ℕ)(p target start v N per K:ℕ)(V:Realm G (p+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(A δ:ℝ):Prop:=
  ∀(t:Faces),t.Nonempty→∀(j:Fin 3→ℕ),(∀i,start≤j i)→∀(c w₀:ℕ),v≤w₀→w₀≤c→
    ∀(ck:c≤K)(live:K<N),v+1≤K→2≤R.family.path.levels.clock.hatBeta K→
    R.family.S.scale K-R.family.S.scale v≤A*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1)))→
    ∀(A₀:WilsonPositionThermometerCapStation.Group R.family 6)(order:ℕ)(η:ℝ)(M:Fin 3→ℝ)
      (before:∀i,j i≤K)(reg:Indexed R grade j order η M (filed R A₀)),0≤η→(∀i,0≤M i)→
    ∀(income m C D₁ D₂:Fin 3→ℝ)(y:Sites N per×Sites N per)(trial:TestAt D t),
    let probe:=enrolled R D V draw N per c (ck.trans live.le) y t trial
    let x:=regulatorRun R.family N per K
    let θ:=regulatorRun R.family N per v
    let s:=Real.log x⁻¹
    let w:=fitted R grade j K order η M (filed R A₀) before reg N per
    (∀i,0≤ income i)→(∀i,M i≤C i*Real.exp ((2*m i)*s))→
    (∀i,Real.log (R.family.S.a K/R.family.S.a (j i))⁻¹≤D₁ i*s)→
    (∀i,income i≤Real.exp ((grade i:ℝ)*D₂ i*s))→
    (∏z:t,income (seat t z))*‖residual R p D V t draw N per K c w₀ v probe w‖≤
      (WilsonOlderFreshSoftTrialCharge.bill R grade (seat t) C*Real.exp (power R grade (seat t) m η D₁ D₂*s))*
        (fee R (grade ∘ seat t) univ*(θ^target*(‖probe.test‖*(fixed R (D ∘ seat t)
          (grade ∘ seat t) p univ*x⁻¹^δ))))

variable {R}
local notation "L_" => R.family.path.levels

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room (prepared s) R simple)
    (D:Fin 3→ℕ)(fit:∀i,grade i<D i)(vac p target B:ℕ)(enough:p+1≤Burn.horizon vac)(cropSize:7+target+2≤p)
    (A τ δ:ℝ)(A0:0≤A)(τ0:0<τ)(δ0:0<δ):
    ∃(P:Credit)(course survey:ℕ),∀ᶠv:ℕ in atTop,∃(V:Realm G (p+1) Credit.leanC)
      (draw:V.draws=R.family.path.levels),V.paid=R.metals.O ∧ V.y=zz L_ ∧ V.anchor=v ∧
      Covered R D p v course V draw A τ ∧ (∀t:Faces,t.Nonempty→Stock R D p v course V draw A τ t) ∧
      ∀N:ℕ,v≤N→∃Z:ℕ→SeriesA G,
        (∀j,v≤j→j≤N→∃σ:ℝ,0<σ ∧ σ⁻¹≤zz L_ j ∧ Issued R N j (Burn.horizon vac) (Z j) σ
          (P.buy (zz L_ j)+zz L_ j*(L_).clock.loopCap j)) ∧
        ∀(school:Syl.School vac)(day:Day (prepared s) R simple school v N),
          Agrees R N v (Burn.horizon vac) Z day.π day.Γ ∧
          ∀per K,v≤K→K≤N→R.family.S.a v/R.family.S.a K≤(L_).clock.hatBeta v^B→
            Bought R D p target survey v N per K V draw A δ:=by
  obtain ⟨P,calendar⟩:=WilsonOlderFreshSoftSocketDay.original u paid paths room vac p target B enough cropSize
  obtain ⟨course,realm⟩:=WilsonOlderFreshSoftSocketFigureRoom.original R paid D fit p A τ A0 τ0
  obtain ⟨survey,purchase⟩:=WilsonOlderFreshSoftSocketFitted.original R simple (WilsonOlderFreshSoftRoseMarket.physical paid)
    D p target A δ A0 δ0
  refine ⟨P,course,survey,?_⟩
  filter_upwards [calendar,realm,eventually_ge_atTop survey] with v bank lab late
  obtain ⟨V,draw,scheme,heat,anchor,shelf,both,tables⟩:=lab
  refine ⟨V,draw,scheme,heat,anchor,both,tables,?_⟩
  intro N vN
  obtain ⟨Z,issued,opened⟩:=bank N vN
  refine ⟨Z,issued,?_⟩
  intro school day
  obtain ⟨same,sales⟩:=opened school day
  refine ⟨same,?_⟩
  intro per K vk KN ratio t nonblank j beforeJ c w₀ vw wc ck live away warm span A₀ order η M before regs η0 M0 income m C D₁ D₂ y trial
  exact purchase t nonblank v late j beforeJ (fun i=>(paid.support (j i)).le) N per K c w₀
    (vw.trans wc) ck live away warm span (sales per v K le_rfl vk KN ratio) V draw scheme heat anchor.le (shelf t)
    (enrolled R D V draw N per c (ck.trans live.le) y t trial) order η M (filed R A₀) before regs η0 M0 income m C D₁ D₂

end YM.Integration.WilsonOlderFreshSoftSocketFigureCurve
end
