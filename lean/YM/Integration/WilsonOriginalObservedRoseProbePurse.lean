import YM.Integration.WilsonOriginalObservedRoseProbeRead
import YM.Integration.WilsonIndependentCollarLowerMass
/-! The single cash amount of the native subword probe on the three actual source tensors. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalObservedRoseProbePurse
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

open WilsonOriginalObservedRoseProbeRead (quota)
variable {D:Fin 3→ℕ}(s:FC)(A:Case D)

theorem original (caps:Fin 3→ℝ)(rate:Fin 3→ℕ)(z:ℝ)(one:1≤z)
    (earned:∀i,‖A i‖≤caps i*z^rate i) :
    quota (touch (fun i:s=>A i.val) (univ:Finset s))≤
      (∏i∈s,max 1 (caps i))*z^(∑i∈s,rate i):=by
  let cost:=fun i:Fin 3=>max 1 (caps i)*z^rate i
  have head (i:Fin 3):1≤cost i:=one_le_mul_of_one_le_of_one_le (le_max_left ..) (one_le_pow₀ one)
  have unit:1≤∏i∈s,cost i:=Finset.one_le_prod (fun i _=>head i)
  have bound (i:Fin 3):‖A i‖≤cost i:=(earned i).trans
    (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (zero_le_one.trans one) _))
  have stock:‖touch (fun i:s=>A i.val) (univ:Finset s)‖≤∏i∈s,cost i:=calc
    _≤∏i:s,‖A i.val‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
      intro v
      rw [hit_leaf,mul_comm]
      exact (v.le_opNorm _).trans (mul_le_mul_of_nonneg_left (folio_norm (fun i:s=>A i.val)) (norm_nonneg _))
    _≤∏i:s,cost i.val:=Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>bound i.val)
    _=∏i∈s,cost i:=Finset.prod_coe_sort s cost
  calc WilsonOriginalObservedRoseProbeRead.quota (touch (fun i:s=>A i.val) (univ:Finset s))≤∏i∈s,cost i:=max_le unit stock
       _=_:=by simp only [cost,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

end YM.Integration.WilsonOriginalObservedRoseProbePurse
end
