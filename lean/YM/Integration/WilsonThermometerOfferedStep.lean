import YM.Integration.WilsonThermometerCourseHearing

/-! Every ambient test of the genuine three-field source commutes with its original Wilson step. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerOfferedStep
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology

local notation "I" => Fin 3

open WilsonThermometerCourseHearing WilsonPositionThermometerGradedReading LocalComparison ActualPolynomialContraction MergeProof.Accent
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {j N per : ℕ} (live : j+1 < N) (o : Positions (Fin 3) (R.family.side N per))
local notation "J" => Stock.census (Fin 3)
local notation "coarse" => R.family.side (j+1) per
local notation "fine" => R.family.side ((j+1)+1) per
local notation "next" => Nat.lt_of_succ_lt live
local notation "S" => R.family.path.levels.clock.op (j+1) per
local notation "β" => R.family.path.β N per ((j+1)+1)

theorem original (ref : ∀ t : Fin 3, R.family.ref (grade t) ≤ N) :
    (fun x : Wallet disks => actualPush R.family N per (j+1) (offered R A simple live o x)) =
      offered R A simple (next) o := by
  let old := incoming R A simple live o
  have paid : Integrable old (prior G (fine)) :=
    WilsonPositionThermometerDepositedFaces.paid R simple N per A.station
      (fun t => index A (grade t)) (vector A Finset.univ) o ref live
  funext x F
  let tested := offered R A simple live o x
  have htest : Integrable tested (prior G (fine)) := by
    apply integrable_pi_iff.mpr
    intro t
    exact ((Poly.get t).integrable_comp paid).const_mul (∏ v ∈ t.val, (x v).val)
  have mass := R.family.path.levels.transition_mass (j+1) per (β)
  have push := WilsonThermometerCourseIntake.step R A simple live o
  ext s
  let z := ∏ v ∈ s.val, (x v).val
  have entry : (fun B => (tested B).part s) = z • (fun B => (old B).part s) := rfl
  have left := congrFun (push_get mass htest s) F
  have right := congrFun (push_get mass paid s) F
  have scalar := congrFun ((S).push_smul (fun B => (old B).part s) (β) z ((Poly.get s).integrable_comp paid)) F
  have genuine := congrArg (fun D : Config G (coarse) → Poly J => (D F).part s) push
  exact left.trans ((congrFun (congrArg ((S).push (β)) entry) F).trans
    (scalar.trans (congrArg (z*·) (right.symm.trans genuine))))

end YM.Integration.WilsonThermometerOfferedStep
end
