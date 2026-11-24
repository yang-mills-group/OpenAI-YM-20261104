import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedSource
import YM.Integration.WilsonIndependentMatchedPhysicalPeer

/-! Evaluation of the registered quadratic source at its actual finite temperature. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedReading
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h hi D k u e : ℕ}
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC


open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialPublicJointCapFiling (sectionAt)
open WilsonSurveyedEquationFrameStability (course)

open WilsonPositionProgramTrialPublicJointCapArrival (high own linear)


open PowerSeries Matrix WilsonCoeffUV.Bank.Carp

open WilsonPositionProgramTrialStationHome (age)
open WilsonPositionProgramTrialAccrued (home)
open WilsonPositionProgramTrialPublicJointGroundBirth (accrued)

open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramTrialPublicJointGroundPortfolio (amount)
open WilsonOriginalPublicNodalDeployedVote (vector)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPositionProgramReportedField (entire)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open PhysicalNext.Repeat.Legato Extra.Histories Pert.Asymptotics

open WilsonPositionProgramTrialPublicJointGroundHead (picked)
open WilsonIndependentMatchedPhysicalPeer (reading)

theorem scale (q:ℕ)(g s:ℝ)(b:Blue.Cost):reading q g (C s*b)=s*reading q g b:=by
  simp only [WilsonIndependentMatchedPhysicalPeer.reading,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,coeff_C_mul,Finset.mul_sum,mul_left_comm]

theorem estimate (q:ℕ)(degree:2 ≤ q)(g:ℝ)(positive:0 ≤ g)(inside:g ≤ 1)(b:Blue.Cost)(a E A:ℝ)
    (zero:∀j:ℕ,j<2 → coeff j b=0)(head:‖coeff 2 b-a‖ ≤ E)
    (paid:∀j:ℕ,j ≤ q → ‖coeff j b‖ ≤ A):
    ‖reading q g b-g^2*a‖ ≤ g^2*(E+((q-2:ℕ):ℝ)*g*A):=by
  let tail:=∑j∈Finset.range (q-2),g^(3+j)*coeff (3+j) b
  have split:reading q g b=g^2*coeff 2 b+tail:=by
    change (∑i∈Finset.range (q+1),g^i • (coeff i:Blue.Cost →ₗ[ℝ] ℝ)) b=_
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
    rw [show q+1=3+(q-2) by omega,Finset.sum_range_add]
    simp [Finset.sum_range_succ,zero 0 (by decide),zero 1 (by decide),tail]
  have cost:‖tail‖ ≤ ((q-2:ℕ):ℝ)*(g^2*(g*A)):=by
    calc
      ‖tail‖ ≤ ∑j∈Finset.range (q-2),‖g^(3+j)*coeff (3+j) b‖:=norm_sum_le ..
      _ ≤ ∑_j∈Finset.range (q-2),g^2*(g*A):=by
        refine Finset.sum_le_sum fun j member=>?_
        have short:=Finset.mem_range.mp member
        have power:g^(3+j) ≤ g^3:=by
          rw [pow_add]
          exact mul_le_of_le_one_right (pow_nonneg positive _) (pow_le_one₀ positive inside)
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg positive _)]
        calc
          _ ≤ g^3*A:=mul_le_mul power (paid (3+j) (by omega)) (norm_nonneg _) (pow_nonneg positive _)
          _ = _:=by ring
      _ = _:=by simp
  rw [split,show g^2*coeff 2 b+tail-g^2*a=g^2*(coeff 2 b-a)+tail by ring]
  calc
    _ ≤ ‖g^2*(coeff 2 b-a)‖+‖tail‖:=norm_add_le ..
    _ ≤ g^2*E+((q-2:ℕ):ℝ)*(g^2*(g*A)):=by
      refine add_le_add ?_ cost
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg g)]
      exact mul_le_mul_of_nonneg_left head (sq_nonneg g)
    _ = _:=by ring

end YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedReading
