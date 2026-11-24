import YM.Integration.WilsonOlderFreshSoftSocketStationPanelStops
import YM.Integration.WilsonOlderFreshSoftRoseMarket

/-! The native charged coefficient is applied once on both infrared hearings. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2600000
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationPanelAmplitude
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

open WilsonOlderFreshSoftRoseMarket (row Probe)
open WilsonOlderFreshSoftRoseCourse (grade seat)
open WilsonOlderFreshSoftCoveredRead (cost)
open WilsonOlderFreshSoftFigureReading (reading)
open WilsonOlderFreshSoftSocketStationPanelCapital (roster)
open WilsonPositionProgramReportedField (entire)
open WilsonReceivedChronologicalHeldEntrance (coords)
open WilsonOriginalPublicFigureIncome (height)
open WilsonMeasuredPublicEntrancePanel (Panel)
open ActualRunPhysicalPages
open PhysicalNext.Repeat.Legato RG16 RG16.Literal Labels Source
open WilsonOlderFreshSoftRoseMarket (scaled)
open WilsonOlderFreshSoftSocketStationPanelStops (printed)
open WilsonOriginalPublicTrialFigure (weight amount)
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
local notation "F" i:max => R.family.labels.level (d i)
omit [LinearOrder I] in
theorem weights (g:ℝ)(x:∀i,(F i).Coeff)(a:I→ℂ)(b:∀i,(F i).Index):
    weight R d g (fun i=>a i • x i) b=(∏i,a i)*weight R d g x b:=by
  unfold WilsonOriginalPublicTrialFigure.weight
  rw [←prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  change (a i*x i (b i))*_=a i*(x i (b i)*_)
  ring

variable (D:Fin 3→ℕ){e:ℕ}(V:Realm G (e+1) Credit.leanC)(s:Finset (Fin 3))
    (N K c w v:ℕ)(p:Probe D V s)(g:ℝ)(x:∀i,(R.family.labels.level (grade i)).Coeff)
    (q:ℕ)(θ:ℝ)(early:Bool)
theorem hearing (a:Fin 3→ℂ):
    row (R:=R) D V s N K c w v p g (fun i=>a i • x i) q θ early=
      (∏i:s,a i)*row (R:=R) D V s N K c w v p g x q θ early:=by
  cases early <;> simp only [row,Bool.false_eq_true,if_false,if_true,WilsonOlderFreshSoftCoveredRead.cost,
    WilsonOlderFreshSoftFigureReading.reading]
  all_goals
    rw [mul_sum]
    apply sum_congr rfl
    intro b _
    let ds:=grade ∘ WilsonOlderFreshSoftRoseCourse.seat s
    let raw:(i:s)→(R.family.labels.level (ds i)).Coeff:=fun i=>x (WilsonOlderFreshSoftRoseCourse.seat s i)
    have line:=weights R ds g raw (fun i:s=>a (WilsonOlderFreshSoftRoseCourse.seat s i)) b
    exact (congrArg (fun z:ℂ=>z*_) line).trans (mul_assoc ..)

variable {f n per req pow step:ℕ}{B:ℝ}(cut:f+n≤N)
    (P:Panel R grade N per f (f+n) (Nat.le_add_right f n) cut req pow step B)
theorem restored (r:ℝ):
    (∏i∈s,(r:ℂ)^grade i)*row (R:=R) D V s N (f+n) c w v p g (printed R cut P) q θ early=
      scaled s (fun i=>(r/R.family.S.a (f+n))^grade i)
        (row (R:=R) D V s N (f+n) c w v p g (fun i=>entire R (grade i) (f+n) (N,per) (coords R grade cut P i)) q θ early):=by
  let x:=fun i=>entire R (grade i) (f+n) (N,per) (coords R grade cut P i)
  let a:Fin 3→ℂ:=fun i=>(((R.family.S.a (f+n)):ℂ)^grade i)⁻¹
  have funding:printed R cut P=fun i=>a i • x i:=by
    funext i b
    simp only [printed,x,a,WilsonPositionProgramReportedField.entire,gMap,Frame.scaled_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [funding,hearing,←mul_assoc,scaled]
  congr 1
  rw [←Finset.prod_coe_sort s (fun i=>(r:ℂ)^grade i),←prod_mul_distrib]
  simp only [Complex.ofReal_prod,Complex.ofReal_pow,Complex.ofReal_div,WilsonOlderFreshSoftRoseCourse.seat,a]
  apply prod_congr rfl
  intro i _
  exact (div_pow (r:ℂ) (R.family.S.a (f+n):ℂ) (grade (i:s))).symm

end YM.Integration.WilsonOlderFreshSoftSocketStationPanelAmplitude
end
