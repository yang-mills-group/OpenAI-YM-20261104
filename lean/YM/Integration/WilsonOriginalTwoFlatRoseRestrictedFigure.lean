import YM.Integration.WilsonOriginalTwoFlatRoseRestrictedStart
import YM.Integration.WilsonOlderFreshSoftSocketRose

/-! Use the previously registered finite public vectors at their own weights.
The full three-name programme evaluated on a proper face has the same finite
angular and scalar response as the independently published restricted roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseRestrictedFigure
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
variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I]
  (R:Run G)(D d:I→ℕ)(S:Finset I)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
  (N per K c v:ℕ)(sites:Digits R.family.path.levels I)(y:I→ Cover)(A:Case D)

omit [Fintype I] in
private theorem here (b:Columns R (fun j:S=>d j.val)):
    (fun j:S=>seats R d S b j.val)=b:=by
  funext j
  exact dif_pos j.property

theorem column (simple:G.Simple)(ratio:LocalRatio R.metals.O)(ck:c≤K)(live:K≤N)
    (b:Columns R (fun j:S=>d j.val)):
    WilsonOlderFreshSoftSocketRestored.stopped R d N K c v sites y S (touch A S) (stencil R D d (seats R d S b) κ pt)=
    WilsonOlderFreshSoftSocketRestored.stopped R (fun a:S=>d a.val) N K c v (fun m (a:S)=>sites m a.val) (fun a:S=>y a.val) univ
      (touch (fun a:S=>A a.val) univ)
      (stencil R (fun a:S=>D a.val) (fun a:S=>d a.val) b (fun a:S=>κ a.val) (fun a:S=>pt a.val)):=by
  let X:=seed R D d (seats R d S b) κ pt
  let DD:=fun i:S=>D i.val
  let dd:=fun i:S=>d i.val
  have smaller:independent (fun i:S=>X i.val)=stencil R DD dd b (fun i:S=>κ i.val) (fun i:S=>pt i.val):=by
    change stencil R DD dd (fun j:S=>seats R d S b j.val) _ _=_
    rw [here]
  have full:=((WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one).choose_spec.2 (seats R d S b) κ pt).1
  have proper:=((WilsonOlderFreshSoftFigures.original R DD dd 0 (w:=1) zero_lt_one).choose_spec.2 b
    (fun i:S=>κ i.val) (fun i:S=>pt i.val)).1
  have ranks (i:I) (m:WilsonMeasuredPointBareWords.Term R (d i) ((seats R d S b) i)):
      (X i m).rank≤d i+(X i m).head:=Nat.le_add_left _ _
  have filed:=WilsonOriginalTwoFlatRoseRestrictedStart.filed X S A ranks R.family.path.levels R.metals.O
    simple ratio N c (K-c) (by omega) sites y full (smaller.symm ▸ proper)
  rw [smaller] at filed
  unfold WilsonOlderFreshSoftSocketRestored.stopped
  rw [show mass dd (univ:Finset S)=mass d S from sum_coe_sort S _]
  exact congrArg (cruises R.family.path.levels R.metals.O N (mass d S) c v) filed

theorem original (simple:G.Simple)(ratio:LocalRatio R.metals.O)(ck:c≤K)(live:K≤N)
    (w:(i:I)→R.family.label (d i))(p:ℕ)(θ:ℝ):
    WilsonOlderFreshSoftSocketTotal.figure R d κ pt N per K c v sites S w y (touch A S) p θ=
    WilsonOlderFreshSoftFigureReading.reading R (fun i:S=>d i.val) (regulatorRun R.family N per K)
      (fun i:S=>entire R (d i.val) K (N,per) (w i.val))
      (fun b=>WilsonOlderFreshSoftSocketRestored.stopped R (fun a:S=>d a.val) N K c v (fun m (a:S)=>sites m a.val) (fun a:S=>y a.val) univ
        (touch (fun a:S=>A a.val) univ)
        (stencil R (fun a:S=>D a.val) (fun a:S=>d a.val) b (fun a:S=>κ a.val) (fun a:S=>pt a.val))) p θ:=by
  classical
  unfold WilsonOlderFreshSoftSocketTotal.figure WilsonOlderFreshSoftFigureReading.reading
  apply sum_congr rfl
  intro b _
  rw [column R D d S κ pt N K c v sites y A simple ratio ck live b]
  rfl

end YM.Integration.WilsonOriginalTwoFlatRoseRestrictedFigure
