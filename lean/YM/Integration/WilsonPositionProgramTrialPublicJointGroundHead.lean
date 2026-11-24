import YM.Integration.WilsonPositionProgramTrialPublicJointGroundVoted
import YM.Integration.WilsonPositionProgramTrialPublicJointScalarReport

/-! The fully restored rank principal and the signed earlier positive-valence feed. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundHead
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

def picked {F:Frame G h}(v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(l:ℕ):Verse F:=
  fun a=>PowerSeries.C (if valence F a=l then amount v p a else 0)

theorem principal (simple:G.Simple)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:h≤k)(q:ℕ)(v:(R.family.labels.level h).Coeff)(p:ℂ →L[ℝ] ℝ)
    (i:Alma (R.family.labels.level h)):
    let F:=R.family.labels.level h
    let I:=plate T fit
    coeff 0 (accrued R fit m K N k (Shrine I (picked v p q)) i)=
      ∑a,if valence F a=q then amount v p a*coeff 0 (accrued R fit m K N k (vein I a) i) else 0:=by
  intro F I
  rw [WilsonPositionProgramTrialPublicJointSourceParityCash.matrixRow R simple fit m K N k before upper T
    sound pop capacity, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [F,I]
  by_cases z:valence (R.family.labels.level h) a=q <;>
    simp [picked,reel_C,PowerSeries.coeff_zero_eq_constantCoeff_apply,z]

theorem original (simple:G.Simple)(v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    (size:h≤6)(fit:h<D)(rails:Rails h k u e)(four:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T):
    ∀ᶠj:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N → ∀q:ℕ,0<q → ∀g:ℝ,g≠0 →
      ∀(v:(R.family.labels.level h).Coeff)(p:ℂ →L[ℝ] ℝ)(i:Alma (R.family.labels.level h)),
      sheet (R.family.labels.level h) i≠0 →
      let F:=R.family.labels.level h
      let I:=plate T fit
      let B:=relativeF L O N m (K-m)
      g^q*coeff q (accrued R fit m K N k (Shrine I (written F (vector F g v) p)) i)=
        coeff 0 (accrued R fit m K N k (Shrine I (picked v p q)) i)+
        ∑a,if 0<valence F a ∧ valence F a<q then g^(q-valence F a)*amount v p a*
          coeff (q-valence F a) (B^(valence F a)*accrued R fit m K N k (vein I a) i) else 0:=by
  filter_upwards [WilsonPositionProgramTrialPublicJointScalarReport.original R simple v₀ funded
    size fit rails four capacity T sound pop] with j unit
  intro m K N late before upper q hq g hg v p i active F I B
  have hb:constantCoeff B=1:=angularF simple (RunFormalChain.fromRun R).receipt (by omega)
  rw [WilsonPositionProgramTrialPublicJointGroundVoted.restored R simple fit m K N k before upper T sound pop
    rails.hk q g hg v p i,principal R simple fit m K N k before upper T sound pop rails.hk q v p i,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  change (if valence F a≤q then g^(q-valence F a)*amount v p a*
      coeff (q-valence F a) (B^(valence F a)*accrued R fit m K N k (vein I a) i) else 0)=
    (if valence F a=q then amount v p a*coeff 0 (accrued R fit m K N k (vein I a) i) else 0)+
    (if 0<valence F a ∧ valence F a<q then g^(q-valence F a)*amount v p a*
      coeff (q-valence F a) (B^(valence F a)*accrued R fit m K N k (vein I a) i) else 0)
  by_cases zero:valence F a=0
  · have sheetZero:sheet F a=0:=by
      by_contra miss
      exact (Nat.ne_of_gt (F.factors_pos (sheet F a) miss)) zero
    have cancel:accrued R fit m K N k (vein I a) i=0:=unit m K N late before upper a i sheetZero active
    rw [cancel]
    simp [zero,Nat.ne_of_lt hq]
  by_cases same:valence F a=q
  · simp [same,hb,PowerSeries.coeff_zero_eq_constantCoeff_apply]
  by_cases earlier:valence F a<q
  · simp [same,earlier,(Nat.zero_lt_of_ne_zero zero),Nat.le_of_lt earlier]
  · have high:q<valence F a:=by omega
    simp [same,earlier,Nat.not_le_of_gt high]

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundHead
