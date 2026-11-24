import YM.Integration.WilsonObservedChiralFreeFiledRose

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonObservedChiralFreeFiledThermometer
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register MS MS.Land
open WilsonMaxwellThermometerOriginal (lower)
open WilsonMaxwellThermometerFaces (connected)
open WilsonMaxwellThermometerCommonTangent (payout separate)
open WilsonPositionProgramTrialPublicJointPivotEvidence (independent)
variable {G:Gauge}(Z:WilsonPrescription G)

theorem inputs (G:Gauge):Rose.tag G = Graph3.trip (Rose.toll G)
    (up (by decide:4≤6) (lower G)) (up (by decide:4≤6) (lower G)) := by
  funext i
  fin_cases i <;> rfl
theorem original (simple:G.Simple)(T:Change G 6):
    (Rose.test Z.criterion).applyTo (fun x=>connected x (fun i=>stand T (Rose.tag G i)))=0 := by
  rw [inputs G]
  exact WilsonObservedChiralFreeFiledRose.original Z simple T (Rose.toll G)
theorem issued {simple:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {S:Prescription (Press.portDeck G)}{dial:Bool}(H:Main.Match Z simple M S dial)(ν:ℝ)(T:Change G 6):
    independent Z M H ν 6 (Rose.test Z.criterion) 0 0 (fun i=>stand T (Rose.tag G i))=0 :=
  (WilsonObservedChiralFreeIndependentRose.original Z M H ν _ _).trans (original Z simple T)

end YM.Integration.WilsonObservedChiralFreeFiledThermometer
