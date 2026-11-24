import YM.Integration.WilsonObservedChiralFreeIndependentRose
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotForecast

/-! The entire constant independent position row as a tested Maxwell connected form. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotRoseGround
open WilsonPositionProgramTrialPublicJointPivotTarget (row)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonMaxwellThermometerCommonTangent (payout)
open Function Set Finset PowerSeries Spec Table Extraction PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionProgramTrialPublicJointPivotEvidence (independent)
open WilsonPositionProgramTrialPublicJointPivotSeries (cash whole signed)
open WilsonMaxwellThermometerFaces (connected faces)
open scoped Classical Topology BigOperators
variable {G:Gauge}(Z:WilsonPrescription G){simple:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z simple M σ b)(ν:ℝ)


theorem amount (q:ℕ)(f:PowerSeries ℂ): cash q 0 f=constantCoeff f := by
  simp [cash,zero_pow_eq,coeff_zero_eq_constantCoeff_apply]

theorem chosen (q:ℕ)(p:Fin 3→Sec G 6) :
    row Z M H ν 0 q 0 p = independent Z M H ν 6 (Rose.test Z.criterion) 0 0 p := by
  change (Rose.test Z.criterion).applyTo (fun x=>cash q 0 (signed (Jury.fxt (response Z M ν 0) x) p)) =
    (Rose.test Z.criterion).applyTo (fun x=>cash 0 0 (signed (Jury.fxt (Measure.start Z.scheme Z.criterion 6) x) p))
  rw [WilsonPositionScaleLawThermometerChart.response,WilsonPositionScaleLawThermometerOrigin.clock Z M H ν,Facets.team_one]
  simp only [amount]

theorem original (q:ℕ)(p:Fin 3→Sec G 6) :
    row Z M H ν 0 q 0 p = (Rose.test Z.criterion).applyTo (fun x=>connected x p) :=
  (chosen Z M H ν q p).trans (WilsonObservedChiralFreeIndependentRose.original Z M H ν _ p)

theorem raised (q:ℕ)(u:Sec G 6)(v w:Sec G 4) :
    row Z M H ν 0 q 0 (Graph3.trip u (up (by decide:4≤6) v) (up (by decide:4≤6) w)) =
      payout Z.criterion u v w := original Z M H ν q _
end YM.Integration.WilsonPositionProgramTrialPublicJointPivotRoseGround
