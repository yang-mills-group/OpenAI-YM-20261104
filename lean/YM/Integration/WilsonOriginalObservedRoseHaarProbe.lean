import YM.Integration.WilsonOriginalObservedRoseHaarOrbit
import YM.Integration.WilsonIndependentSpoutHaarHistory
/-! The same enrolled, finite, normalized relative probe run on the Haar chart, with the whole original upper occupied word and both of its true admission receipts. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalObservedRoseHaarProbe
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
local notation "FC" => Finset (Fin 3)

variable {G:Gauge}(R:Run G){e:ℕ}(D:Fin 3→ℕ)(V:Realm G (e+1) Credit.leanC)
  (s:FC)(N K c v:ℕ)(probe:Probe D V s)(g:ℝ)
  (x:∀i,(R.family.labels.level (grade i)).Coeff)(q:ℕ)(θ:ℝ)
local notation "dates" => grade ∘ seat s
local notation "ports" => D ∘ seat s
local notation "yard" => V.draws
local notation "bare" => XSpace.Bare.chart G
local notation "S" => (univ:Finset s)
local notation "amount" => WilsonCoeffUV.Wheel.Mark.mass (dates) S

def source (O:ChartRatio G):=
  WilsonOlderFreshSoftTrialCut.source R (ports) (dates) N K c (yard) O probe.coeff probe.phase
    probe.digit probe.root S probe.test

def priced:ℂ:=WilsonOlderFreshSoftFigureReading.reading R (dates) g (fun i=>x (seat s i))
  (fun idx=>cruises (yard) (bare) N (amount) c v (source R D V s N K c probe (bare) idx)) q θ

theorem original (ink:V.paid=R.metals.O)(late:ℕ):
    row (R:=R) D V s N K c late v probe g x q θ false=priced R D V s N K c v probe g x q θ:=by
  have old:LocalRatio V.paid:=ink.symm ▸ (RunFormalChain.fromRun R).receipt
  have changeWord (b):
      cruises (yard) V.paid N (amount) c v (source R D V s N K c probe V.paid b)=
      cruises (yard) (bare) N (amount) c v (source R D V s N K c probe (bare) b):=
    WilsonOriginalObservedRoseHaarOrbit.original old (XSpace.Bare.chart_ratio G) (yard) (dates)
      (stencil R (ports) (dates) b probe.coeff probe.phase) N probe.digit c K v probe.root S probe.test
  unfold WilsonOlderFreshSoftRoseMarket.row priced
  simp only [Bool.false_eq_true,↓reduceIte]
  change WilsonOlderFreshSoftFigureReading.reading R (dates) g _ (fun b=>cruises (yard) V.paid N (amount) c v
    (source R D V s N K c probe V.paid b)) q θ=_
  rw [show (fun b=>cruises (yard) V.paid N (amount) c v (source R D V s N K c probe V.paid b))=
    (fun b=>cruises (yard) (bare) N (amount) c v (source R D V s N K c probe (bare) b)) from funext changeWord]

theorem admitted (simple:G.Simple)(ck:c≤K)(kn:K≤N):
    ∀b:(i:s)→(R.family.labels.level ((dates) i)).Index,
      let X:=stencil R (ports) (dates) b probe.coeff probe.phase
      Wellness (dates) X ∧ (∀y:s→ Cover,Auth (amount) (tuftV probe.test (levelsO (X y) S))) ∧
      Auth (amount) (source R D V s N K c probe (bare) b):=by
  intro b X
  have high:Wellness (dates) X:=((WilsonOlderFreshSoftFigures.original R (ports) (dates) 0 (w:=1) zero_lt_one).choose_spec.2 b probe.coeff probe.phase).1
  have capture:=WilsonReceivedFixedDigitHistory.sound (yard) (bare) (dates) N probe.digit simple
    (XSpace.Bare.chart_ratio G) X high (K-c) c (by omega)
  exact ⟨high,fun y=>(placedO _ (high.level' y) S).tuft probe.test,(placedO _ (capture.level' probe.root) S).tuft probe.test⟩

end YM.Integration.WilsonOriginalObservedRoseHaarProbe
end
