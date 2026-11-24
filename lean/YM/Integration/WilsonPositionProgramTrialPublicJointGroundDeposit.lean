import YM.Integration.WilsonPositionProgramTrialPublicJointGroundSuspension
import YM.Integration.RunFormalChain

/-! A single physically suspended and pole-restored rank channel, on its original vacuum. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundDeposit
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

theorem common {F:Frame G h}(I:Island F D)(f:Cost)(c:Verse F):
    Shrine I (fun j=>f*c j)=Stem f (Shrine I c):=by
  apply Prod.ext
  · funext n
    simp only [Shrine,Stem,Prod.fst_sum,Finset.sum_apply,affix_sum,affix_mul]
  · simp only [Shrine,Stem,Prod.snd_sum,affix_sum,affix_mul]

theorem restored (simple:G.Simple)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:h≤k)(r q:ℕ)(t:ℝ)(openT:t≠0)(c:Verse (R.family.labels.level h))
    (i:Alma (R.family.labels.level h)):
    t^r*coeff (q+r) (accrued R fit m K N k
      (Shrine (plate T fit) (fun j=>(PowerSeries.C (t^r)⁻¹*PowerSeries.X^r)*c j)) i)=
      coeff q ((relativeF L O N m (K-m))^r*accrued R fit m K N k (Shrine (plate T fit) c) i):=by
  let valid:LocalRatio O:=(RunFormalChain.fromRun R).receipt
  have primary:Shimmer (plate T fit):=freshly T H fit sound pop
  have entered:On k (Shrine (plate T fit) c):=Shrine_on _ primary c capacity
  rw [common,WilsonPositionProgramTrialPublicJointGroundSuspension.clear R simple valid fit m K N k before upper _
    entered (t^r)⁻¹ r q i]
  rw [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ openT),one_mul]

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (size:h ≤ 6)(fit:h<D)(rails:Rails h k u e)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T):
    ∃(C:Credit)(A:Alma (R.family.labels.level h)→ℝ),(∀i,0 ≤ A i) ∧
      ∀ᶠj:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N → ∀(c:Verse (R.family.labels.level h))
        (i:Alma (R.family.labels.level h)),2 ≤ valence (R.family.labels.level h) i →
        h ≤ 2*valence (R.family.labels.level h) i → ∀(r:ℕ)(t:ℝ),t≠0 →
        ‖t^r*coeff r (accrued R fit m K N k
          (Shrine (plate T fit) (fun j=>(PowerSeries.C (t^r)⁻¹*PowerSeries.X^r)*c j)) i)-coeff 0 (c i)‖ ≤
          C.buy (age L m K)*trailC (L).S m K*charge e c A:=by
  obtain ⟨C,A,an,paid⟩:=WilsonPositionProgramTrialPublicJointGroundBirth.original R simple v funded size
    fit rails capacity T sound pop
  refine ⟨C,A,an,?_⟩
  filter_upwards [paid] with j bought
  intro m K N late before upper c i active full r t openT
  have field:=restored R simple fit m K N k before upper T sound pop rails.hk r 0 t openT c i
  have unit:constantCoeff (relativeF L O N m (K-m))=1:=
    angularF simple (RunFormalChain.fromRun R).receipt (by omega)
  simp only [Nat.zero_add,coeff_zero_eq_constantCoeff_apply,map_mul,map_pow,unit,one_pow,one_mul] at field
  rw [field,←coeff_zero_eq_constantCoeff_apply]
  exact bought m K N late before upper c i active full

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundDeposit
