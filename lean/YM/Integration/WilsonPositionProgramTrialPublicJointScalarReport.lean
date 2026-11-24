import YM.Integration.WilsonPositionProgramTrialPublicJointScalarProjection
import YM.Integration.WilsonPositionProgramTrialPublicJointGroundBirth

/-! The nonunit reporter of a scalar insertion on the true earlier prior. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointScalarReport
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
theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (size:h≤6)(fit:h<D)(rails:Rails h k u e)(four:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T):
    ∀ᶠj:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N →
      ∀a i:Alma (R.family.labels.level h),sheet (R.family.labels.level h) a=0 →
        sheet (R.family.labels.level h) i≠0 →
        accrued R fit m K N k (vein (plate T fit) a) i=0:=by
  let F:=R.family.labels.level h
  have valid:LocalRatio O:=(RunFormalChain.fromRun R).receipt
  filter_upwards [WilsonPositionProgramTrialPublicJointCapGroundFare.course R simple v funded fit rails capacity] with j court
  obtain ⟨l,a,_,_,levels,reals,_,start⟩:=court
  intro m K N late before live x i unit positive
  let P:=spools L O N k h m (K-m) (vein (plate T fit) x)
  have cancelled:opal F P i=0:=WilsonPositionProgramTrialPublicJointScalarProjection.original L O simple valid
    N k m (K-m) (by omega) four rails.hk T fit sound pop x i unit positive
  apply PowerSeries.ext
  intro q
  have wick:=WilsonPhysicalSixWickRows.nonunit l.L size simple (before.trans live) (start.le.trans late) i positive
    (fun j=>coeff q (opal F P j))
  rw [levels,reals] at wick
  unfold accrued matrix
  simp only [map_sum,map_smul,smul_eq_mul,map_zero]
  exact wick.trans ((congrArg (coeff q) cancelled).trans (map_zero _))

end YM.Integration.WilsonPositionProgramTrialPublicJointScalarReport
