import YM.Integration.WilsonIndependentSpoutHaarHistory
import YM.Integration.WilsonOriginalObservedRoseProbeRead
/-! The full marked finite itinerary of an arbitrary originally posted word on two normalized local Haar charts. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalObservedRoseHaarOrbit
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

open WilsonReceivedFixedDigitHistory (Digits itinerary)
open WilsonReceivedFixedDigitIntake (next)
open WilsonOlderFreshSoftOrdinary (material)
variable {G:Gauge}{U V:ChartRatio G}(first:LocalRatio U)(second:LocalRatio V)(L:Levels G)
variable {I:Type}[DecidableEq I]{D:I→ℕ}(k:I→ℕ)

include first second in
theorem log (m N:ℕ)(X:family G D):logO L U m N X k=logO L V m N X k:=by
  apply congrArg (fun Z:family G D=>reverseO Z)
  funext S
  exact WilsonIndependentSpoutHaarHistory.marked first second L m N (WilsonCoeffUV.Wheel.Mark.mass k S) (levelsO X S)

include first second in
theorem posted (m N:ℕ)(X:Outerm G D)(cell:I→Site (loose L m).L):
    WilsonReceivedFixedDigitIntake.next L U m N k X cell=WilsonReceivedFixedDigitIntake.next L V m N k X cell:=by
  funext y
  exact log first second L k m N _

include first second in
theorem history (N:ℕ)(cells:Digits L I)(days m:ℕ)(X:Outerm G D):
    itinerary L U k N cells days m X=itinerary L V k N cells days m X:=by
  induction days generalizing m with
  | zero=>rfl
  | succ age ih=>simp only [itinerary,ih,posted first second]

include first second in
theorem source (X:Outerm G D)(N:ℕ)(cells:Digits L I)(c K:ℕ)(roots:I→ Cover)
    (S:Finset I)(test:Pen D S→L[ℝ]ℝ):
    material D k L U X N cells c K roots S test=material D k L V X N cells c K roots S test:=by
  simp only [material,history first second]

include first second in
theorem original (X:Outerm G D)(N:ℕ)(cells:Digits L I)(c K v:ℕ)(roots:I→ Cover)
    (S:Finset I)(test:Pen D S→L[ℝ]ℝ):
    cruises L U N (WilsonCoeffUV.Wheel.Mark.mass k S) c v (material D k L U X N cells c K roots S test)=
    cruises L V N (WilsonCoeffUV.Wheel.Mark.mass k S) c v (material D k L V X N cells c K roots S test):=by
  rw [source first second L k,WilsonIndependentSpoutHaarHistory.original first second]

end YM.Integration.WilsonOriginalObservedRoseHaarOrbit
end
