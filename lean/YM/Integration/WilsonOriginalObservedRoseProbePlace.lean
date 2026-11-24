import YM.Integration.WilsonOriginalObservedRoseProbeRead
import YM.Integration.WilsonOriginalTwoFlatRoseCapturedDigits
/-! Physical enrollment of each normalized probe on the purchased original lattice cylinder, with its true mass, coupling and all older proper coordinates. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalObservedRoseProbePlace
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
variable {G:Gauge}(R:Run G)(D:Fin 3→ℕ)(s:FC)(κ:(a:Fin 3)→Knob (D a))(pt:Fin 3→Chamber)
    (A:Case D){e f K N per c v:ℕ}(V:Realm G (e+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
    (o:Fin 3→Site (R.family.side f per))(fk:f≤K)(kn:K≤N)(vc:v+1≤c)(ck:c≤K)
local notation "P" => pin R fk o
local notation "X" => pin R (fk.trans kn) o
local notation "raw" => ((X) 1,(X) 2)
local notation "tape" => WilsonReceivedChronologicalMaterialSites.digits R (P)
local notation "root" => WilsonIndependentCollarOrdinaryCruise.address R.family.path.levels (tape) (c-(v+1)) (v+1)
  (footprint R (P) (vc.trans ck))

open WilsonOriginalObservedRoseProbeRead (quota normalizedProbe affordable)
open WilsonOriginalTwoFlatRosePublishedFigure (profile)

def ticket:TestAt D s where
  coeff:=fun i=>κ i.val
  phase:=fun i=>pt i.val
  test:=normalizedProbe (profile D s A)
  bound:=affordable _

private theorem same {left right:Probe D V s}(knobs:left.coeff=right.coeff)(phase:left.phase=right.phase)
    (digits:left.digit=right.digit)(roots:left.root=right.root)(test:left.test=right.test):left=right:=by
  cases left
  cases right
  congr

include draw in
theorem fields (center:(X) 0=0)(rooms:Rolled R o fk kn vc ck):
    WilsonOriginalObservedRoseProbeRead.filed R D s κ pt
      (fun j (i:s)=>(tape) j i.val) (fun i:s=>(root) i.val) V draw (profile D s A)=
    enrolled R D V draw N per c (ck.trans kn) (raw) s (ticket D s κ pt A):=by
  have node:atOrigin (raw)=(X):=by funext i;fin_cases i <;> simp [atOrigin,center]
  obtain ⟨digits,placed⟩:=rooms
  apply same D s V
  · rfl
  · rfl
  · change (draw.symm ▸ fun j (i:s)=>(tape) j i.val)=
      (draw.symm ▸ fun j (i:s)=>WilsonOriginalPublicFixedCourse.digits R (N:=N) per (atOrigin (raw)) j (seat s i))
    rw [node,digits]
    rfl
  · change (fun i:s=>(root) i.val)=(fun i:s=>WilsonOriginalPublicFixedCourse.home R (N:=N) per c (ck.trans kn)
      (atOrigin (raw)) (anchor s) (seat s i))
    rw [node,placed (anchor s)]
    rfl
  · rfl

include draw paid in
theorem original (simple:G.Simple)(center:(X) 0=0)(rooms:Rolled R o fk kn vc ck)
    (w:(i:Fin 3)→R.family.label (grade i))(late p:ℕ)(θ:ℝ):
    figure R grade κ pt N per K c (v+1) (tape) s w (root) (touch A s) p θ=
      (quota (profile D s A):ℂ)*row (R:=R) D V s N K c late (v+1)
        (enrolled R D V draw N per c (ck.trans kn) (raw) s (ticket D s κ pt A))
        (regulatorRun R.family N per K) (fun i=>entire R (grade i) K (N,per) (w i)) p θ false:=by
  have eqn:=WilsonOriginalObservedRoseProbeRead.original R D s κ pt N per K c (v+1) w p θ V draw paid
    simple (RunFormalChain.fromRun R).receipt vc ck kn (tape) (root) A late
  change _=(quota (profile D s A):ℂ)*row (R:=R) D V s N K c late (v+1)
    (WilsonOriginalObservedRoseProbeRead.filed R D s κ pt (fun j (i:s)=>(tape) j i.val) (fun i:s=>(root) i.val)
      V draw (profile D s A)) _ _ p θ false at eqn
  rw [fields R D s κ pt A V draw o fk kn vc ck center rooms] at eqn
  exact eqn

end YM.Integration.WilsonOriginalObservedRoseProbePlace
end
