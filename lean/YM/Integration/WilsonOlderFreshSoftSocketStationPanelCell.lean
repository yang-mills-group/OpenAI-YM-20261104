import YM.Integration.WilsonOlderFreshSoftSocketStationPanelWindow
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelAmplitude
import YM.Integration.WilsonOriginalObservedRoseProbeRead
import YM.Integration.WilsonMeasuredPublicEntranceCellWords
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelPower
import YM.Integration.WilsonOlderFreshSoftRoseMarket

/-! A single original reporting date buys every proper or complete deposited face before both numerical regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2600000
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationPanelCell
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
open WilsonOlderFreshSoftSocketStationPanelStops (printed)
open WilsonOlderFreshSoftSocketStationPanelPower (loss debt)
open WilsonOlderFreshSoftSocketStationCalendar (date)
variable {G:Gauge}(R:Run G)
local notation "L" => R.family.path.levels
local notation "H" k:max => R.family.path.levels.clock.hatBeta k
local notation "Faces" => {t:Finset (Fin 3)//t.Nonempty}

open RG16 RG16.Literal Extra.Histories Extra.Trajectories Extra.Multi Source
open WilsonMeasuredPublicEntranceCellWords (physical)
open WilsonMovingForkHeterogeneousCut (Filed)
open ActualRunPhysicalPages Pert.Asymptotics Extraction Labels
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonOriginalObservedRoseProbeRead (quota)
open WilsonReceivedChronologicalHeldEntrance (coords)
open WilsonPositionProgramReportedField (entire)
open WilsonOlderFreshSoftSocketTotal (figure)
open WilsonOlderFreshSoftRoseMarket (scaled)

/-- The actual pre-existing upper Wilson density heard at its earlier flat field. -/
def observed {N per f n req pow step:ℕ}{B:ℝ}(cut:f+n≤N)
    (P:Panel R grade N per f (f+n) (Nat.le_add_right f n) cut req pow step B)
    (s:(Stock.census (Fin 3)).Mode)(u:ℕ)(old:u≤f+n):ℂ:=
  WilsonThermometerUnitFilingCoarse.reading R (N:=N)
    (credit R.family N per 0 (physical R grade P.names P.turn P.loc s) (f+n) cut) u old

variable (D:Fin 3→ℕ){e N per f n req pow step:ℕ}{B:ℝ}
variable (V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
variable (cut:f+n≤N)(P:Panel R grade N per f (f+n) (Nat.le_add_right f n) cut req pow step B)
variable (file:Filed R grade (f+n))
variable (station:P.slot=file.station)(axes:P.axis=file.A N per)
variable (s:(Stock.census (Fin 3)).Mode)(κ:(i:Fin 3)→Knob (D i))(pt:Fin 3→Chamber)
variable (route:Digits R.family.path.levels (Fin 3))(home:Fin 3→ Cover)(test:Case D)(q:ℕ)(θ r:ℝ)

/-- The scalar from the original full N quiet at the paid independent stop, with its measured normalizations. -/
def terminal (R:Run G)(D:Fin 3→ℕ){e N per f n req pow step:ℕ}{B:ℝ}
    (V:Realm G (e+1) Credit.leanC)(level:V.draws=R.family.path.levels)(cut:f+n≤N)
    (P:Panel R grade N per f (f+n) (Nat.le_add_right f n) cut req pow step B)
    (s:(Stock.census (Fin 3)).Mode)(κ:(i:Fin 3)→Knob (D i))(pt:Fin 3→Chamber)
    (trace:Digits R.family.path.levels (Fin 3))(home:Fin 3→ Cover)(test:Case D)(q:ℕ)(θ r:ℝ)(c w v:ℕ):ℂ:=
  let branch:=touch (fun i:s.val=>test i.val) (univ:Finset s.val)
  let probe:=WilsonOriginalObservedRoseProbeRead.filed R D s.val κ pt
    (fun j (i:s.val)=>trace j i.val) (fun i:s.val=>home i.val) V level branch
  (quota branch:ℂ)*scaled s.val (fun i=>(r/R.family.S.a (f+n))^grade i)
    (row (R:=R) D V s.val N (f+n) c w v probe (regulatorRun R.family N per (f+n))
       (fun i=>entire R (grade i) (f+n) (N,per) (coords R grade cut P i)) q θ true)

include paid station axes in
theorem joined (simple:G.Simple)(ratio:LocalRatio R.metals.O){c w v u:ℕ}
    (vc:v≤c)(ck:c≤f+n)(old:u≤f+n)(fee income:ℝ)
    (issued:‖observed R cut P s u old-
       figure R grade κ pt N per (f+n) c v route s.val (votes R grade (N:=N) (per:=per) file P.names P.turn) home (touch test s.val) q θ‖≤fee)
    (window:∀p:Probe D V s.val,let g:=regulatorRun R.family N per (f+n)
       let x:=printed R cut P
       ‖row (R:=R) D V s.val N (f+n) c w v p g x q θ false-row (R:=R) D V s.val N (f+n) c w v p g x q θ true‖ ≤ income):
    ‖(∏i∈s.val,(r:ℂ)^grade i)*observed R cut P s u old-
      terminal R D V draw cut P s κ pt route home test q θ r c w v‖≤
      ‖∏i∈s.val,(r:ℂ)^grade i‖*(fee+
        quota (touch (fun i:s.val=>test i.val) (univ:Finset s.val))*income):=by
  classical
  let branch:=touch (fun i:s.val=>test i.val) (univ:Finset s.val)
  let probe:=WilsonOriginalObservedRoseProbeRead.filed R D s.val κ pt
    (fun j (i:s.val)=>route j i.val) (fun i:s.val=>home i.val) V draw branch
  let g:=regulatorRun R.family N per (f+n)
  let x:=printed R cut P
  let a:=∏i∈s.val,(r:ℂ)^grade i
  let val (early:Bool):=row (R:=R) D V s.val N (f+n) c w v probe g x q θ early
  have input:(fun i=>entire R (grade i) (f+n) (N,per) ((votes R grade (N:=N) (per:=per) file P.names P.turn) i))=x:=by
    funext i
    unfold x printed WilsonOriginalObservedRoseCorrectedWords.votes coords
    rw [←station,←axes]
    rfl
  have mark:=WilsonOriginalObservedRoseProbeRead.original R D s.val κ pt N per (f+n) c v
    (votes R grade (N:=N) (per:=per) file P.names P.turn) q θ V draw paid simple ratio vc ck cut route home test w
  dsimp only at mark
  rw [input] at mark
  change _=(quota branch:ℂ)*val false at mark
  rw [mark] at issued
  have bill:‖val false-val true‖ ≤ income:=window probe
  have comp:‖(quota branch:ℂ)*val false-(quota branch:ℂ)*val true‖≤quota branch*income:=by
    rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (WilsonOriginalObservedRoseProbeRead.positive branch).le]
    exact mul_le_mul_of_nonneg_left bill (WilsonOriginalObservedRoseProbeRead.positive branch).le
  have joined:‖observed R cut P s u old-(quota branch:ℂ)*val true‖≤fee+quota branch*income:=
    calc
      _=‖(observed R cut P s u old-(quota branch:ℂ)*val false)+
          ((quota branch:ℂ)*val false-(quota branch:ℂ)*val true)‖:=by congr 1;ring
      _≤_ := (norm_add_le _ _).trans (add_le_add issued comp)
  have price:=WilsonOlderFreshSoftSocketStationPanelAmplitude.restored R D V s.val N c w v probe g q θ true cut P r
  change a*val true=_ at price
  have land:a*((quota branch:ℂ)*val true)=terminal R D V draw cut P s κ pt route home test q θ r c w v:=by
    unfold terminal
    change _=(quota branch:ℂ)*_
    rw [←price]
    ring
  change ‖a*observed R cut P s u old-_‖≤‖a‖*_
  rw [←land,←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left joined (norm_nonneg _)

end YM.Integration.WilsonOlderFreshSoftSocketStationPanelCell
end
