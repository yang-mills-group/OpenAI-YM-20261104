import YM.Integration.WilsonOlderFreshSoftSocketStationMixedPage
import YM.Integration.WilsonOlderFreshSoftSocketStationDosedCells
import YM.Integration.WilsonOlderFreshSoftSocketStationSettlement
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 30000
set_option quotPrecheck false
namespace YM.Integration.WilsonOlderFreshSoftSocketStationScan
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats ticket)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonOlderFreshSoftSocketRestored (degree stopped coin)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshHybridClock (flat)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonOriginalStarSceneWords (pole)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding ActualRunPhysicalPages Pert.Asymptotics
open scoped Classical BigOperators

open WilsonOlderFreshSoftFigures (seed stencil)
open WilsonOlderFreshSoftSocketRestored (stopped)
open WilsonOlderFreshSoftSocketMeasuredCash (seats packet)
open WilsonPositionProgramReportedField (entire)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketTotal (figure)
open WilsonOlderFreshSoftFigureReading (reading)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshHybridClock (flat)

open WilsonOriginalTwoFlatRoseCapturedDigits (Rolled)
open WilsonOlderFreshSoftRoseCourse (grade seat)
open WilsonOlderFreshSoftRoseNodes (enrolled TestAt anchor)
open WilsonOlderFreshSoftRoseMarket (Probe row)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonReceivedChronologicalMaterialSites (footprint)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonThermometerAlignedCells (atOrigin)
open ActualRunPhysicalPages
open WilsonCoeffUV.Bank.Realm Pert.Asymptotics Extraction

open Marker QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Rebirth
open WilsonOriginalTwoFlatRoseFixedFiles (site cells)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonOriginalTwoFlatRoseHousedDigits (Joined marks)
open WilsonOriginalTwoFlatRosePublishedFigure (test)
open WilsonOriginalTwoFlatRoseMerFigure (restoration)
open QuadraticLocal.Affinity Push.AbsoluteSums
local notation "FC" => Finset (Fin 3)
local notation "J" => Stock.census (Fin 3)

open WilsonOriginalPublicTrialInput (vector fitted)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonOlderFreshSoftRoseMesh (filed table)
open WilsonOlderFreshSoftSocketStationDose (stamp outside)
open WilsonOriginalTwoFlatIRFlatMarked (seat)
open WilsonOriginalTwoFlatRoseFiledVisit (published)

open WilsonOlderFreshSoftSocketStationSettlement (Book put)
open WilsonOlderFreshSoftSocketStationSample (Sampled)
open WilsonOlderFreshSoftSocketStationSale (overhead)
open WilsonOlderFreshSoftSocketStationSingleton (reserve)
open WilsonOlderFreshSoftSocketStationCenter (cost amount)
open WilsonOlderFreshSoftSocketStationInverse (total)
open WilsonOlderFreshSoftSocketStationDosedCells (residual)
open WilsonPositionThermometerConnected (value)
open MeasureTheory
abbrev Support {G:Gauge}(R:Run G)(f per:ℕ)(r:ℝ)(φ:YM.Test 3) :=
  {y:Site (R.family.side f per) × Site (R.family.side f per) //
    WilsonThermometerAlignedCells.mass (R:=R) r (f,per) φ y ≠ 0}

variable {G:Gauge}(R:Run G)(D:Fin 3→ℕ)(A₀:WilsonPositionThermometerCapStation.Group R.family 6)
    {q p f n N per c i:ℕ}(V:Realm G (q+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (W:Realm G (p+1) Credit.leanC)(hub:W.draws=R.family.path.levels)(sv:V.paid=R.metals.O)(sw:W.paid=R.metals.O)
    (live:f+n<N)(ck:c≤f+n)(r η:ℝ)(φ:YM.Test 3)
    (order:ℕ)(M:Fin 3→ℝ)(reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀))(kK:A₀.station.k≤f+n)
local notation "top" => (f+n)
local notation "fine" => (Nat.le_add_right f n).trans live.le
local notation "μ" => WilsonThermometerAlignedCells.mass (R:=R) r (f,per) φ
local notation "Jumps" => (Site (R.family.side f per)×Site (R.family.side f per))
local notation "Valid" => Support R f per r φ
local notation "land" y:max => put R (per:=per) (fine) (y).val
local notation "bank" => filed R A₀
local notation "measured" => fitted R grade (fun _=>A₀.station.k) top order η M bank (fun _=>kK) reg N per
local notation "reading" => vector R grade (fun _=>A₀.station.k) top order η M bank (fun _=>kK) reg N per
local notation "x" => regulatorRun R.family N per top
local notation "θ" => regulatorRun R.family N per (i+1)
local notation "pay" => (fun a:Fin 3=>(r/R.family.S.a top)^(grade a))
local notation "costed" => (fun _=>(WilsonReceivedChronologicalSocket.lit (V:=Fin 3)))
variable (κ:Support R f per r φ →(a:Fin 3)→Knob (D a))(pt:Support R f per r φ →Fin 3→Chamber)(t:Support R f per r φ →Case D)(cash:Support R f per r φ →Fin 3→ℂ)
    (money:∀(y:Support R f per r φ)(a:Fin 3),cash y a ≠ 0)
    (bound:∀(y:Support R f per r φ)(s:FC),‖WilsonOriginalTwoFlatRosePublishedFigure.profile D s (t y)‖ ≤ 1)
local notation "probes" y:max => (fun z s=>enrolled R D W hub N per c (ck.trans live.le) z s
      (test D s (κ y) (pt y) (t y) (bound y s)))
local notation "shown" y:max s:max stop:max => WilsonOriginalTwoFlatRoseFiledVisit.published R D (i:=i) V draw (κ y) (pt y) (t y)
    (atOrigin (y).val) live.le ck costed measured (cash y) (WilsonOriginalTwoFlatIRFlatMarked.seat s) (bound y s) stop p θ

local notation "exposed" y:max w:max early:max => table R D W N per top c w (i+1) (probes y) x reading pay p θ early (land y)

theorem variation: (∑y:Valid,‖μ y.val‖)≤ ∫z:Points 3,‖φ z‖:=by
  apply le_trans _ (WilsonThermometerAlignedCells.variation (R:=R) r (f,per) φ)
  let inclusion:Valid↪Jumps:=⟨Subtype.val,Subtype.val_injective⟩
  have reindex:(∑y:Valid,‖μ y.val‖)=∑z∈(univ:Finset Valid).map inclusion,‖μ z‖:=by
    rw [sum_map]
    rfl
  rw [reindex]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>norm_nonneg _)

include live in
theorem cost_nonnegative (C:Fin 3→ℝ)(B:ℝ)(power:ℕ):
    0≤cost R C B*x^power:=by
  have gpos:=ActualRunKernelPackets.regulator_pos R N per top live.le
  have f0:0 ≤ total R C:=sum_nonneg fun _ _=>abs_nonneg _
  have A0:0 ≤ WilsonOlderFreshSoftSocketStationCenter.amount R C B:=by unfold WilsonOlderFreshSoftSocketStationCenter.amount;linarith [abs_nonneg B]
  change 0 ≤ total R C*(7*(WilsonOlderFreshSoftSocketStationCenter.amount R C B+2*(WilsonOlderFreshSoftSocketStationCenter.amount R C B)^2))*x^power
  positivity

include money sv sw in
theorem original (target width:ℕ)(ξ δ:ℝ)(m C:Fin 3→ℝ)(w:ℕ)
    (_funded:Sampled R D p target order width ξ η δ m C A₀ r M reg (i+1) N per top c w W hub kK ck live)
    (sale:Book R A₀ (per:=per) r φ (fine))
    (_issued:∀(y:Valid)(s:FC),s.Nonempty→(sale y).table s=shown y s w):
    let H:=overhead R width ξ η δ m
    let B:=reserve R D p H C
    ‖∑y:Valid,μ y.val*residual (sale y) (outside r grade (cash y)) (exposed y w true)‖≤
      (∑y:Valid,‖μ y.val‖*(‖stamp (outside r grade (cash y)) univ‖*WilsonOriginalTwoFlatRoseCellSum.cost (sale y)))+
        (∫z:Points 3,‖φ z‖)*(cost R C B*x^target):=by
  intro H B
  exact WilsonOlderFreshSoftSocketStationDosedCells.collected sale (fun y=>outside r grade (cash y))
    (fun y=>μ y.val) (fun y:Valid=>exposed y w false) (fun y:Valid=>exposed y w true)
    (variation R (f:=f) (per:=per) r φ) (cost_nonnegative R (per:=per) live C B target)
    (fun y s active=>by
      rw [_issued y s active]
      exact WilsonOlderFreshSoftSocketStationMixedPage.original R D A₀ V draw (κ y) (pt y) (t y)
        (atOrigin y.val) live ck r η order M reg kK (cash y) (money y) (bound y) W hub sv sw s active w θ)
    (fun y=>_funded (fun _ s=>test D s (κ y) (pt y) (t y) (bound y s)) (land y))

end YM.Integration.WilsonOlderFreshSoftSocketStationScan
