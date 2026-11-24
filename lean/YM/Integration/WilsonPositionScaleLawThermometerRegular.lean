import YM.Integration.WilsonPositionScaleLawThermometerChart

/-! Integrability of the same original three-point thermometer on every actual
positive measuring length follows from the physical spectator's smooth hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerRegular
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionThermometerReading (sample leg)
open WilsonPositionThermometerConnected (value)
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(L:ℝ→tower S)

private theorem slot {r:ℝ}(hr:0<r)(s:Badge):ContinuousOn (fun x=>sample F L r x s) (conf 3):=by
  let w:Fin 3→S.Tag:=fun i=>⟨6,L r 6 (leg R.family s i)⟩
  change ContinuousOn (fun x=>S.useAt (spectator F none) (r • x) w) (conf 3)
  exact (S.class_smooth _ (spectate F none).smooth w).continuousOn.comp
    (continuous_const_smul r).continuousOn (fun _ hx=>Work.A05.smul_conf hr hx)

theorem original {r:ℝ}(hr:0<r):ContinuousOn (fun x=>value (sample F L r x)) (conf 3):=by
  have c:=slot F L hr
  exact ((c univ).sub ((((c {0,1}).mul (c {2})).add ((c {0,2}).mul (c {1}))).add ((c {1,2}).mul (c {0})))).add
    (continuousOn_const.mul (((c {0}).mul (c {1})).mul (c {2})))

end YM.Integration.WilsonPositionScaleLawThermometerRegular
end
