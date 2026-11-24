import YM.Integration.WilsonThermometerCourseHearing

/-! Advance the complete original three-marker offer. The same marked
density, including every scalar probe, re-enters with a paid regular rent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerTestedReturn
open Finset Filter Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure OriginalForcedAddresses MergeProof MergeProof.East
open IterationFour Push.AbsoluteSums.Animals Extra.Trajectories FVA1
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonThermometerCourseIntake WilsonThermometerCourseHearing
open scoped Classical BigOperators Topology
local notation "J" => Stock.census (Fin 3)

private def adjust (x : Wallet disks) : Poly J →ₗ[ℂ] Poly J where
  toFun a := Poly.inject (fun s => (∏ v ∈ s.val,(x v).val)*a.part s)
  map_add' a b := by ext s; exact mul_add _ _ _
  map_smul' c a := by ext s; exact mul_left_comm _ _ _

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {N i per m k : ℕ} (live : i+1 < N) (o : Positions (Fin 3) (R.family.side N per))

theorem push (ref : ∀ t : Fin 3, R.family.ref (grade t) ≤ N) :
    (fun x : Wallet disks => LocalComparison.actualPush R.family N per (i+1) (offered R A simple live o x)) =
      offered R A simple (Nat.lt_of_succ_lt live) o := by
  have value := step R A simple live o
  have paid := WilsonPositionThermometerDepositedFaces.paid R simple N per A.station
    (fun j : Fin 3 => index A (grade j)) (vector A univ) o ref live
  funext x W
  let L := ((adjust x).toContinuousLinearMap).restrictScalars ℝ
  have ker := StepData.push_slice (R.family.path.levels.transition_mass (i+1) per
    (R.family.path.β N per (i+2))) W _ paid
  change _ = L (incoming R A simple live.le o W)
  rw [←value]
  change (∫ U, _ ∂prior G _) = L (∫ U, _ ∂prior G _)
  apply Eq.trans _ (L.integral_comp_comm ker)
  apply integral_congr_ae
  filter_upwards with U
  exact (map_smul L _ (incoming R A simple live o U)).symm

end YM.Integration.WilsonThermometerTestedReturn
end
