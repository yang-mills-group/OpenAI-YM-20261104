import YM.Integration.WilsonObservedChiralFreeIndependentRose
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotRestriction

/-! The Maxwell ground on the submitted filtered change and its two lower restrictions. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonObservedChiralFreeFiledRose
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register MS MS.Land
open WilsonMaxwellThermometerOriginal (lower)
open WilsonMaxwellThermometerFaces (connected)
open WilsonMaxwellThermometerCommonTangent (payout separate)
open WilsonPositionProgramTrialPublicJointPivotEvidence (independent)
variable {G:Gauge}(Z:WilsonPrescription G)

def reading (T:Change G 6)(u:Sec G 6):ℂ :=
  (Rose.test Z.criterion).applyTo (fun x=>connected x (fun i=>
    stand T (Graph3.trip u (up (by decide:4≤6) (lower G)) (up (by decide:4≤6) (lower G)) i)))

theorem original (simple:G.Simple)(T:Change G 6)(u:Sec G 6):
    reading Z T u=0 := by
  let A:=stand T
  let B:=stand (WilsonPositionProgramTrialPublicJointPivotRestriction.lower (by decide:4≤6) T)
  have lift:stand T (up (by decide:4≤6) (lower G))=up (by decide:4≤6) (B (lower G)) :=
    (WilsonPositionProgramTrialPublicJointPivotRestriction.original (by decide:4≤6) T (lower G)).symm
  have eqn:(fun i=>A (Graph3.trip u (up (by decide:4≤6) (lower G)) (up (by decide:4≤6) (lower G)) i))=
      Graph3.trip (A u) (up (by decide:4≤6) (B (lower G))) (up (by decide:4≤6) (B (lower G))) := by
    funext i
    fin_cases i
    · rfl
    · exact lift
    · exact lift
  have equiv:WilsonMaxwellThermometerCommonTangent.Equivariant B := by
    intro rot x
    simp only [B,stood_ori]
  unfold reading
  rw [show (fun i=>stand T (Graph3.trip u (up (by decide:4≤6) (lower G)) (up (by decide:4≤6) (lower G)) i))=_ from eqn]
  exact separate Z.criterion simple (A u) B B equiv equiv

theorem issued {simple:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {S:Prescription (Press.portDeck G)}{dial:Bool}(H:Main.Match Z simple M S dial)(ν:ℝ)(T:Change G 6)(u:Sec G 6):
    independent Z M H ν 6 (Rose.test Z.criterion) 0 0 (fun i=>stand T
      (Graph3.trip u (up (by decide:4≤6) (lower G)) (up (by decide:4≤6) (lower G)) i))=0 :=
  (WilsonObservedChiralFreeIndependentRose.original Z M H ν _ _).trans (original Z simple T u)

end YM.Integration.WilsonObservedChiralFreeFiledRose
