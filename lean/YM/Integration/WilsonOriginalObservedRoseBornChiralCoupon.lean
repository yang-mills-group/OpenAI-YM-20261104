import YM.Integration.WilsonOriginalObservedRoseBornChiralRegister
import YM.Integration.WilsonOriginalObservedRoseBornChiralUnaryCash
/-! One registered court, the measured input, and its surveyed replacement at the actual shared fresh cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralCoupon
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix cancel)
open WilsonPositionProgramTrialPublicJointSourceStable (seen)
open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical Topology

open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialReverseLens (received)
variable {G:Gauge}{n k u e h D₀:ℕ}(R:Run G)(W:Initialize G)
variable (d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "C" => Credit.leanC

open WilsonIndependentMatchedPhysicalSector (stamp Courts)
open WilsonOriginalObservedRoseBornChiralPeer (input)

open WilsonIndependentMatchedFreshInverseIncome (age)
open WilsonIndependentMatchedProxyIncome (cost)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonOriginalObservedRoseBornChiralTender (plan size)
open WilsonPositionProgramTrialHomeDose (scaled)

def coin {d:ℕ}(F:Labels.Frame G d)(e:ℕ)(base rate:Credit)(tick span:ℝ)(A:Alma F→ℝ):ℝ:=
  (Fintype.card (Alma F):ℝ)*base.buy tick*(rate.buy span*plan e A+size F e)

theorem costed {d:ℕ}{F:Labels.Frame G d}(e:ℕ)(c:Verse F):0≤cost e c:=
  Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _

theorem single {d:ℕ}{F:Labels.Frame G d}(e:ℕ)(base rate:Credit)(tick span:ℝ)(A:Alma F→ℝ)(nn:∀i,0≤A i)
    (b c x:Verse F)(fuel:ℝ)(issued:fuel=charge e c A)
    (bills:cost e x ≤ ((Fintype.card (Alma F):ℝ)*base.buy tick*cost e b)*size F e)
    (paid:fuel ≤ rate.buy span*((Fintype.card (Alma F):ℝ)*base.buy tick*cost e b)*plan e A):
    ‖fuel‖+‖cost e x‖ ≤ ‖coin F e base rate tick span A‖*cost e b:=by
  have zero:0≤fuel:=issued.symm ▸ Finset.sum_nonneg (fun i _=>WilsonIndependentMatchedFiledIncome.nonneg (nn i) (c i) e)
  rw [Real.norm_of_nonneg zero,Real.norm_of_nonneg (costed e x)]
  apply (add_le_add paid bills).trans
  calc
    _=coin F e base rate tick span A*cost e b:=by unfold coin; ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (le_abs_self _) (costed e b)

end YM.Integration.WilsonOriginalObservedRoseBornChiralCoupon
