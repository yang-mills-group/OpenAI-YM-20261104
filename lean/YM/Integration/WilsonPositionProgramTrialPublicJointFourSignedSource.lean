import YM.Integration.WilsonPositionProgramTrialPublicJointFourActivePaid
import YM.Integration.WilsonPositionProgramTrialPublicJointGroundSigned

/-! On the original active output the public Laurent pole is common and removable. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedSource
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
def strip {F:Frame G 4}(v:F.Coeff):F.Coeff:=fun a=>if a=0 then 0 else v a

theorem amountStrip {F:Frame G 4}(v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(a:Alma F):
    amount (strip v) p a=if sheet F a=0 then 0 else amount v p a:=by
  by_cases zero:sheet F a=0 <;> simp [strip,amount,zero]

theorem rank {F:Frame G 4}(simple:G.Simple)(a:Alma F)(active:sheet F a ≠ 0):valence F a=2:=
  congrArg Prod.snd (WilsonPositionProgramTrialPublicJointFourLive.grades F simple le_rfl a active).1

theorem raw (simple:G.Simple)(v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    (fit:4<D)(rails:Rails 4 k u e)(enough:4 ≤ k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData (R.family.labels.level 4)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T):
    ∀ᶠj:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N → ∀g:ℝ,g ≠ 0 →
      ∀(v:(R.family.labels.level 4).Coeff)(p:ℂ →L[ℝ] ℝ)(i:Alma (R.family.labels.level 4)),
      sheet (R.family.labels.level 4) i ≠ 0 →
      let F:=R.family.labels.level 4
      let I:=plate T fit
      C (g^2) * accrued R fit m K N k (Shrine I (written F (vector F g v) p)) i =
        accrued R fit m K N k (Shrine I (written F (strip v) p)) i:=by
  filter_upwards [WilsonPositionProgramTrialPublicJointScalarReport.original R simple v₀ funded (by decide)
    fit rails enough capacity T sound pop] with j quiet
  intro m K N late before top g live v p i active F I
  rw [WilsonPositionProgramTrialPublicJointGroundPortfolio.issued R simple fit m K N k before top T sound pop enough,
    WilsonPositionProgramTrialPublicJointGroundPortfolio.issued R simple fit m K N k before top T sound pop enough,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _=>?_
  by_cases zero:sheet F a=0
  · have cancelled:=quiet m K N late before top a i zero active
    simp only [cancelled,mul_zero]
  · have two:=rank simple a zero
    rw [WilsonPositionProgramTrialPublicJointGroundVoted.priced,amountStrip,if_neg zero,two,map_mul]
    have cancels:PowerSeries.C (R:=ℝ) (g^2)*PowerSeries.C ((g^2)⁻¹) = 1:=by
      rw [←map_mul,mul_inv_cancel₀ (pow_ne_zero _ live),map_one]
    generalize PowerSeries.C (amount v p a)=d
    generalize (relativeF L O N m (K-m))^2*accrued R fit m K N k (vein (plate T fit) a) i=E
    calc
      _=PowerSeries.X^2*((PowerSeries.C (g^2)*PowerSeries.C ((g^2)⁻¹))*d*E):=by ring
      _=_:=by rw [cancels,one_mul]

theorem starts (simple:G.Simple)(fit:4<D)(m K N k:ℕ)(before:m ≤ K)(top:K ≤ N)
    (T:SectionData (R.family.labels.level 4)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:4 ≤ k)(v:(R.family.labels.level 4).Coeff)(p:ℂ →L[ℝ] ℝ)
    (i:Alma (R.family.labels.level 4))(q:ℕ)(low:q<2):
    coeff q (accrued R fit m K N k (Shrine (plate T fit) (written _ (strip v) p)) i)=0:=by
  rw [WilsonPositionProgramTrialPublicJointGroundPortfolio.original R simple fit m K N k before top T sound pop capacity]
  apply Finset.sum_eq_zero
  intro a _
  by_cases unit:sheet (R.family.labels.level 4) a=0
  · rw [amountStrip,if_pos unit]
    split <;> simp
  · rw [rank simple a unit,if_neg (by omega)]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedSource
