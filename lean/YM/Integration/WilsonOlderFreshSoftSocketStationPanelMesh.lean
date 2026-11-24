import YM.Integration.WilsonOlderFreshSoftSocketStationPanelHearing
import YM.Integration.WilsonOlderFreshSoftSocketStationScan
import YM.Integration.WilsonMaxwellThermometerNominatedSecant
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelCell
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
namespace YM.Integration.WilsonOlderFreshSoftSocketStationPanelMesh
open Function Filter Finset Lattice Laurent Bloch Precision Wilson RG Source Labels Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Winding WilsonCoeffUV.Soil WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PertExtension NativeCurvatureTensor
open OriginalMarkedSourceComet WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftTrialCharge (power wages)
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

open WilsonOlderFreshSoftSocketStationPanelCell (observed terminal)
open WilsonOlderFreshSoftSocketStationScan (Support)
open WilsonMaxwellThermometerNominatedSecant (bill faceKey)
open WilsonThermometerAlignedCells (atOrigin)
open MeasureTheory
local notation "FC" => Finset (Fin 3)

def mode (s:FC):(Stock.census (Fin 3)).Mode:=⟨s,mem_univ _⟩

private theorem inactive (a b:FC→ℂ):bill a b ∅=0:=by
  unfold WilsonMaxwellThermometerNominatedSecant.bill
  apply Finset.sum_eq_zero
  intro i _
  have used:(faceKey i).Nonempty:=by fin_cases i <;> decide
  exact if_neg used.ne_empty.symm

structure Entry (R:Run G)(D:Fin 3→ℕ){N per f n:ℕ}(req pow step:ℕ)(B:ℝ)(cut:f+n≤N)
    (file:Filed R grade (f+n))(y:Site (R.family.side f per) × Site (R.family.side f per)) where
  panel:Panel R grade N per f (f+n) (Nat.le_add_right f n) cut req pow step B
  site:panel.loc=atOrigin y
  station:panel.slot=file.station
  axes:panel.axis=file.A N per
  knobs:(i:Fin 3)→Knob (D i)
  phase:Fin 3→Chamber
  route:Digits R.family.path.levels (Fin 3)
  home:Fin 3→ Cover
  test:Case D

variable {D:Fin 3→ℕ}{e N per f n req pow step:ℕ}{B:ℝ}
variable (V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
variable (cut:f+n≤N)(file:Filed R grade (f+n))(r:ℝ)(φ:YM.Test 3)
local notation "Valid" => Support R f per r φ
local notation "μ" => WilsonThermometerAlignedCells.mass (R:=R) r (f,per) φ
variable (E:(y:Valid)→Entry R D req pow step B cut file y.val)
variable {c w v u:ℕ}(old:u≤f+n)(q:ℕ)(θ:ℝ)

def high (R:Run G){D:Fin 3→ℕ}{N per f n req pow step:ℕ}{B:ℝ}
    (cut:f+n≤N)(file:Filed R grade (f+n))(r:ℝ)(φ:YM.Test 3)
    (E:(y:Support R f per r φ)→Entry R D req pow step B cut file y.val) {u:ℕ}(old:u≤f+n)(y:Support R f per r φ)(s:FC):ℂ:=(∏i∈s,(r:ℂ)^grade i)*observed R cut (E y).panel (mode s) u old

def low (R:Run G){D:Fin 3→ℕ}{e N per f n req pow step c w v:ℕ}{B:ℝ}
    (V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (cut:f+n≤N)(file:Filed R grade (f+n))(r:ℝ)(φ:YM.Test 3)
    (E:(y:Support R f per r φ)→Entry R D req pow step B cut file y.val) (q:ℕ)(θ:ℝ)(y:Support R f per r φ)(s:FC):ℂ:=terminal R D V draw cut (E y).panel (mode s) (E y).knobs (E y).phase
  (E y).route (E y).home (E y).test q θ r c w v

def price (R:Run G){D:Fin 3→ℕ}{N per f n req pow step:ℕ}{B:ℝ}
    (cut:f+n≤N)(file:Filed R grade (f+n))(r:ℝ)(φ:YM.Test 3)
    (E:(y:Support R f per r φ)→Entry R D req pow step B cut file y.val) (y:Support R f per r φ)(s:FC)(fee:Support R f per r φ→FC→ℝ)(m:ℝ):ℝ:=
  ‖∏i∈s,(r:ℂ)^grade i‖*(fee y s+quota (touch (fun i:s=>(E y).test i.val) (univ:Finset s))*m)

theorem earned (R:Run G){D:Fin 3→ℕ}{e N per f n req pow step:ℕ}{B:ℝ}
    (V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
    (cut:f+n≤N)(file:Filed R grade (f+n))(r:ℝ)(φ:YM.Test 3)
    (E:(y:Support R f per r φ)→Entry R D req pow step B cut file y.val)
    {c w v u:ℕ}(old:u≤f+n)(q:ℕ)(θ:ℝ) (simple:G.Simple)(vc:v≤c)(ck:c≤f+n)(fee:Support R f per r φ→FC→ℝ)(total:ℝ)
    (born:∀(y:Support R f per r φ)(s:FC),s.Nonempty →
      ‖observed R cut (E y).panel (mode s) u old-
        figure R grade (E y).knobs (E y).phase N per (f+n) c v (E y).route s
          (votes R grade (N:=N) (per:=per) file (E y).panel.names (E y).panel.turn) (E y).home (touch (E y).test s) q θ‖≤fee y s)
    (book:∀(y:Support R f per r φ)(s:FC),s.Nonempty →∀p:Probe D V s,
      let g:=regulatorRun R.family N per (f+n)
      let x:=printed R cut (E y).panel
      ‖row (R:=R) D V s N (f+n) c w v p g x q θ false-row (R:=R) D V s N (f+n) c w v p g x q θ true‖≤total):
    let seen:=high R cut file r φ E old
    let ending:=low R (c:=c) (w:=w) (v:=v) V draw cut file r φ E q θ
    let expense y:=∑s:FC,‖bill (seen y) (ending y) s‖*price R cut file r φ E y s fee total
    ‖∑y:Support R f per r φ,WilsonThermometerAlignedCells.mass (R:=R) r (f,per) φ y.val*(WilsonPositionThermometerConnected.value (seen y)-WilsonPositionThermometerConnected.value (ending y))‖≤
      ∑y:Support R f per r φ,‖WilsonThermometerAlignedCells.mass (R:=R) r (f,per) φ y.val‖*expense y:=by
  classical
  intro seen ending expense
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro y _
  rw [norm_mul,WilsonMaxwellThermometerNominatedSecant.signed]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro s _
  rw [norm_mul]
  by_cases hs:s.Nonempty
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact WilsonOlderFreshSoftSocketStationPanelCell.joined R D V draw paid cut (E y).panel file
      (E y).station (E y).axes (mode s) (E y).knobs (E y).phase (E y).route (E y).home (E y).test q θ r
      simple (RunFormalChain.fromRun R).receipt vc ck old (fee y s) total (born y s hs) (book y s hs)
  · have blank:s=∅:=Finset.not_nonempty_iff_eq_empty.mp hs
    rw [blank,inactive,norm_zero,zero_mul,zero_mul]

theorem position (t y:Valid→ℂ)(C:ℝ)(pos:0≤C)
    (band:∀o:Valid,‖t o-y o‖≤C):
    ‖∑o:Valid,μ o.val*(t o-y o)‖≤(∫z:Points 3,‖φ z‖)*C:=by
  apply (norm_sum_le ..).trans
  calc
    _≤∑o:Valid,‖μ o.val‖*C:=by apply sum_le_sum;intro o _;rw[norm_mul];exact mul_le_mul_of_nonneg_left (band o) (norm_nonneg _)
    _=(∑o:Valid,‖μ o.val‖)*C:=(sum_mul ..).symm
    _≤_:=mul_le_mul_of_nonneg_right (WilsonOlderFreshSoftSocketStationScan.variation R (f:=f) (per:=per) r φ) pos

end YM.Integration.WilsonOlderFreshSoftSocketStationPanelMesh
end
