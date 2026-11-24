import YM.Integration.WilsonOriginalTwoFlatRosePublishedFigure
import YM.Integration.WilsonOriginalObservedRosePrintedTail
import YM.Integration.WilsonOlderFreshSoftSocketTest

/-! The independent finite subword filed on the actual chosen digits and occupied locations. Its unit probe and its full physical return are co-issued. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalObservedRoseProbeRead
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
variable (N per K c v:ℕ)(digits:Digits R.family.path.levels s)(roots:s→ Cover)
variable (w:(i:Fin 3)→R.family.label (grade i))(p:ℕ)(θ:ℝ)

def quota {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](test:E→L[ℝ]ℝ):ℝ:=max 1 ‖test‖
theorem positive {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](test:E→L[ℝ]ℝ):0<quota test:=
  zero_lt_one.trans_le (le_max_left _ _)
def normalizedProbe {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](test:E→L[ℝ]ℝ):E→L[ℝ]ℝ:=
  (quota test)⁻¹ • test
theorem affordable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](test:E→L[ℝ]ℝ):‖normalizedProbe test‖≤1:=by
  rw [normalizedProbe,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (positive test))]
  calc (quota test)⁻¹*‖test‖≤(quota test)⁻¹*quota test:=
         mul_le_mul_of_nonneg_left (le_max_right ..) (inv_nonneg.mpr (positive test).le)
       _=1:=inv_mul_cancel₀ (positive test).ne'

def valueAt (test:Pen (D ∘ seat s) (univ:Finset s)→L[ℝ]ℝ):ℂ:=
  WilsonOlderFreshSoftFigureReading.reading R (grade ∘ seat s) (regulatorRun R.family N per K)
    (fun i:s=>entire R (grade i.val) K (N,per) (w i.val))
    (fun idx=>stopped R (grade ∘ seat s) N K c v digits roots univ test
      (stencil R (D ∘ seat s) (grade ∘ seat s) idx (fun j:s=>κ j.val) (fun j:s=>pt j.val))) p θ

private theorem linear (simple:G.Simple)(ratio:LocalRatio R.metals.O)(vc:v≤c)(ck:c≤K)(kn:K≤N)
    (test:Pen (D ∘ seat s) (univ:Finset s)→L[ℝ]ℝ)(t:ℝ):
    valueAt R D s κ pt N per K c v digits roots w p θ (t • test)=
      (t:ℂ)*valueAt R D s κ pt N per K c v digits roots w p θ test:=by
  unfold valueAt WilsonOlderFreshSoftFigureReading.reading
  rw [mul_sum]
  apply sum_congr rfl
  intro idx _
  let d₀:=grade ∘ seat s
  let D₀:=D ∘ seat s
  let κ₀:=(fun j:s=>κ j.val)
  let pt₀:=(fun j:s=>pt j.val)
  let field:=stencil R D₀ d₀ idx κ₀ pt₀
  have income:=((WilsonOlderFreshSoftFigures.original R D₀ d₀ 0 (w:=1) zero_lt_one).choose_spec.2 idx κ₀ pt₀).1
  have lin:=WilsonOlderFreshSoftSocketTest.linear R D₀ d₀ univ N K c v simple ratio vc ck kn digits roots field income test t
  have amount:flat (stopped R d₀ N K c v digits roots univ (t • test) field) p θ=
      t*flat (stopped R d₀ N K c v digits roots univ test field) p θ:=by
    change WilsonOlderFreshSoftSocketTotal.listen p θ _=t*(WilsonOlderFreshSoftSocketTotal.listen p θ _)
    rw [lin,map_smul]
    rfl
  rw [amount,Complex.ofReal_mul]
  ring

open WilsonCoeffUV.Bank.Realm
private theorem moved {α:Type*}(F:α→Type*){u v:α}(same:u=v)(x:F v):
    cast (congrArg F same) (same.symm ▸ x)=x:=by cases same;rfl

def filed {e:ℕ}(V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (test:Pen (D ∘ seat s) (univ:Finset s)→L[ℝ]ℝ):Probe D V s where
  coeff:=fun i=>κ i.val
  phase:=fun i=>pt i.val
  digit:=draw.symm ▸ digits
  root:=roots
  test:=normalizedProbe test
  bound:=affordable test

private theorem chart (L:Levels G)(O:ChartRatio G)(draw:L=R.family.path.levels)(paid:O=R.metals.O)
    (trace:Digits L s)(test:Pen (D ∘ seat s) (univ:Finset s)→L[ℝ]ℝ):
    WilsonOlderFreshSoftFigureReading.reading R (grade ∘ seat s) (regulatorRun R.family N per K)
      (fun i:s=>entire R (grade i.val) K (N,per) (w i.val))
      (fun idx=>cruises L O N (mass (grade ∘ seat s) univ) c v
        (WilsonOlderFreshSoftTrialCut.source R (D ∘ seat s) (grade ∘ seat s) N K c L O
          (fun i:s=>κ i.val) (fun i:s=>pt i.val) trace roots univ test idx)) p θ=
      valueAt R D s κ pt N per K c v (cast (congrArg (fun l=>Digits l s) draw) trace) roots w p θ test:=by
  subst L O
  rfl

theorem original {e:ℕ}(V:Realm G (e+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
    (simple:G.Simple)(ratio:LocalRatio R.metals.O)(vc:v≤c)(ck:c≤K)(kn:K≤N)
    (sites:Digits R.family.path.levels (Fin 3))(y:Fin 3→ Cover)(A:Case D)(late:ℕ):
    let test:=touch (fun i:s=>A i.val) (univ:Finset s)
    let probe:=filed R D s κ pt (fun j (i:s)=>sites j i.val) (fun i:s=>y i.val) V draw test
    let gK:=regulatorRun R.family N per K
    let inputs:=fun i=>entire R (grade i) K (N,per) (w i)
    figure R grade κ pt N per K c v sites s w y (touch A s) p θ=
      (quota test:ℂ)*row (R:=R) D V s N K c late v probe gK inputs p θ false:=by
  intro test probe gK inputs
  let trace:Digits R.family.path.levels s:=fun j i=>sites j i.val
  let home:s→ Cover:=fun i=>y i.val
  let heard:=valueAt R D s κ pt N per K c v trace home w p θ
  have restricted:figure R grade κ pt N per K c v sites s w y (touch A s) p θ=heard test:=
    WilsonOriginalTwoFlatRoseRestrictedFigure.original R D grade s κ pt N per K c v sites y A simple ratio ck kn w p θ
  have unit:row (R:=R) D V s N K c late v probe gK inputs p θ false=heard (normalizedProbe test):=by
    have level:=chart R D s κ pt N per K c v home w p θ V.draws V.paid draw paid probe.digit (normalizedProbe test)
    have same:cast (congrArg (fun l=>Digits l s) draw) probe.digit=trace:=moved (fun l:Levels G=>Digits l s) draw trace
    rw [same] at level
    exact level
  have payment:=linear R D s κ pt N per K c v trace home w p θ simple ratio vc ck kn test (quota test)⁻¹
  rw [restricted,unit]
  change heard test=(quota test:ℂ)*heard ((quota test)⁻¹ • test)
  change heard ((quota test)⁻¹ • test)=((quota test)⁻¹:ℝ)*heard test at payment
  rw [payment,←mul_assoc]
  rw [←Complex.ofReal_mul,mul_inv_cancel₀ (positive test).ne',Complex.ofReal_one,one_mul]

end YM.Integration.WilsonOriginalObservedRoseProbeRead
end
