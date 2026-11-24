import YM.Integration.WilsonPositionProgramTrialPublicJointSourceParityCourse

/-! The genuine native first report of an arbitrary full moving input at horizons up to five is the ground response to its moving coefficient, also at the unit. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceParityCash
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

theorem even (simple:G.Simple)(cap:h≤5)(F:Frame G h)(a:Alma F):(valence F a)%2=0:=by
  have hw:=WilsonPhysicalSixWickRows.arity F a
  have whole:=weigh_cap F a
  have sz:weave F a≤weight F a:=Nat.le_add_right ..
  have prohibited:valence F a≠1:=WilsonMaxwellThermometerWardColors.arity simple F (sheet F a)
  omega

theorem axis (simple:G.Simple)(fit:h<D)(cap:h≤5)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:h≤k)(a i:Alma (R.family.labels.level h))(q:ℕ)(odd:q%2=1):
    coeff q (accrued R fit m K N k (vein (plate T fit) a) i)=0:=by
  have valid:LocalRatio O:=(RunFormalChain.fromRun R).receipt
  unfold accrued matrix
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  have cancel:=WilsonPositionProgramTrialPublicJointSourceParityCourse.original L O simple valid N k h m
    (K-m) (by omega) T fit sound pop capacity a j q (by
      have p:=even simple cap (R.family.labels.level h) a
      have t:=even simple cap (R.family.labels.level h) j
      omega)
  rw [map_smul,cancel,smul_zero]

theorem matrixRow (simple:G.Simple)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:h≤k)(c:Verse (R.family.labels.level h))(i:Alma (R.family.labels.level h)):
    accrued R fit m K N k (Shrine (plate T fit) c) i=
      ∑a,reel (relativeF L O N m (K-m)) (c a)*accrued R fit m K N k (vein (plate T fit) a) i:=by
  let I:=plate T fit
  have solid:Shimmer I:=freshly T H fit sound pop
  have names (a:Alma (R.family.labels.level h)):On k (vein I a):=
    hailed I solid a ((valence_cap ..).trans capacity)
  have valid:LocalRatio O:=(RunFormalChain.fromRun R).receipt
  unfold Shrine
  rw [WilsonPositionProgramTrialPublicJointGroundPortfolio.summed R simple fit m K N k before upper _
    (fun a=>(names a).stem _) i]
  exact Finset.sum_congr rfl fun a _=>WilsonPositionProgramTrialPublicJointGroundSuspension.read R simple valid
    fit m K N k before upper _ (names a) _ i

theorem zeroth (B f:Cost):constantCoeff (reel B f)=constantCoeff f:=by
  nth_rw 1 [f.eq_X_mul_shift_add_const]
  simp [reel_X,reel_C]

theorem tangent (B f:Cost)(unit:constantCoeff B=1):coeff 1 (reel B f)=coeff 1 f:=by
  nth_rw 1 [f.eq_X_mul_shift_add_const]
  simp [reel_X,reel_C,coeff_one_mul,zeroth,unit]

def row {F:Frame G h}(s:ℕ)(c:Verse F):Verse F:=fun i=>PowerSeries.C (coeff s (c i))

theorem original (simple:G.Simple)(fit:h<D)(cap:h≤5)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:h≤k)(c:Verse (R.family.labels.level h))(i:Alma (R.family.labels.level h)):
    coeff 1 (accrued R fit m K N k (Shrine (plate T fit) c) i)=
      coeff 0 (accrued R fit m K N k (Shrine (plate T fit) (row 1 c)) i):=by
  have unit:constantCoeff (relativeF L O N m (K-m))=1:=
    angularF simple (RunFormalChain.fromRun R).receipt (by omega)
  rw [matrixRow R simple fit m K N k before upper T sound pop capacity c i,
    matrixRow R simple fit m K N k before upper T sound pop capacity (row 1 c) i,
    map_sum,map_sum]
  refine Finset.sum_congr rfl fun a _=>?_
  have vanish:=axis R simple fit cap m K N k before upper T sound pop capacity a i 1 (by decide)
  simp [coeff_one_mul,vanish,tangent _ _ unit,row,coeff_zero_eq_constantCoeff_apply,reel_C]

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceParityCash
