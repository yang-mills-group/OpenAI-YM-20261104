import YM.Integration.WilsonPositionProgramTrialPublicJointGroundPortfolio
import YM.Integration.WilsonOriginalObservedRoseBornPairDose
import YM.Integration.WilsonOriginalPublicNodalDeployedVote

/-! All thermal pole restorations on one native previously commissioned signed physical arm. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundVoted
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

theorem priced {F:Frame G h}(g:ℝ)(v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(a:Alma F):
    amount (vector F g v) p a=(g^(valence F a))⁻¹ * amount v p a:=by
  by_cases held:rankS a.val.2=0
  · simp only [amount,if_pos held,vector]
    simpa only [valence,Complex.real_smul,smul_eq_mul,mul_comm] using
      p.map_smul ((g^(valence F a))⁻¹) (v (sheet F a))
  · simp [amount,held]

theorem restored (simple:G.Simple)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:h≤k)(q:ℕ)(g:ℝ)(live:g≠0)(v:(R.family.labels.level h).Coeff)
    (p:ℂ →L[ℝ] ℝ)(i:Alma (R.family.labels.level h)):
    let F:=R.family.labels.level h
    let I:=plate T fit
    let B:=relativeF L O N m (K-m)
    g^q * coeff q (accrued R fit m K N k (Shrine I (written F (vector F g v) p)) i)=
      ∑a,if valence F a ≤ q then g^(q-valence F a)*amount v p a*
        coeff (q-valence F a) (B^(valence F a)*accrued R fit m K N k (vein I a) i) else 0:=by
  intro F I B
  rw [WilsonPositionProgramTrialPublicJointGroundPortfolio.original R simple fit m K N k before upper
    T sound pop capacity q _ p i,Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _=>?_
  split
  · rename_i room
    rw [priced]
    have cancel:g^q*(g^(valence F a))⁻¹=g^(q-valence F a):=by
      calc
        _=g^(q-valence F a+valence F a)*(g^(valence F a))⁻¹:=by rw [Nat.sub_add_cancel room]
        _=_:=by rw [pow_add,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ live),mul_one]
    change g^q*( ((g^(valence F a))⁻¹ * _) * _)=_
    rw [←mul_assoc,←mul_assoc,cancel]
  · exact mul_zero _

def bid {n:ℕ}(d:Fin n→ℕ){K:ℕ}(N per:ℕ)(file:Filed R d K)
    (Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r:ℝ)(t:ℂ)(i:Fin n):
    (R.family.labels.level (d i)).Coeff:=fun b=>
  (((R.family.S.a K/r)^(d i):ℝ):ℂ)*t*((entire R (d i) K (N,per)
    (votes R d (N:=N) (per:=per) file Y turn i)) b)

theorem chosen {n:ℕ}(d:Fin n→ℕ){K f:ℕ}(N per:ℕ)(file:Filed R d K)
    (Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r:ℝ)(t:ℂ)(i:Fin n)
    (A:Arm R (d i) N per f K)(placed:A.w=(file.A N per i).symm
      (fitted R (d i) (file.station i) N per (Y i)))(oriented:(A.s,A.b)=turn i):
    amounts R (d i) K N per r t (coords R A)=vector (R.family.labels.level (d i))
      (regulatorRun R.family N per K) (bid R d N per file Y turn r t i):=
  WilsonOriginalObservedRoseBornPairDose.arm R d file Y turn r t i A placed oriented

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundVoted
