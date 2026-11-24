import YM.Integration.WilsonPositionProgramTrialPublicJointGroundDeposit
import YM.Integration.WilsonOriginalPhysicalFruitVerse

/-! The original physical finite vote is a signed sum of heterogeneous heat suspensions. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundPortfolio
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
variable {ι:Type*}[Fintype ι]

theorem combined (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N k h m j:ℕ)(before:m+j≤N)(P:ι→TowerS G D)(openLaw:∀a,On k (P a)):
    spools A O' N k h m j (∑a,P a)=∑a,spools A O' N k h m j (P a):=by
  induction j generalizing P with
  | zero => rfl
  | succ j ih =>
    have here:m+j<N:=by omega
    have step:Spout A O' N (m+j) h k (∑a,P a)=∑a,Spout A O' N (m+j) h k (P a):=by
      simpa only [one_smul] using Shed_add A O' (h:=h) here simple valid (fun _:ι=>(1:ℝ)) openLaw
    change spools A O' N k h m j (Spout A O' N (m+j) h k (∑a,P a))=_
    rw [step,ih (by omega) _ (fun a=>ShedG A O' (h:=h) here simple valid (openLaw a) le_rfl)]
    rfl

theorem booked (F:Frame G h)(P:ι→TowerS G D)(openLaw:∀a,On k (P a)):
    opal F (∑a,P a)=∑a,opal F (P a):=by
  funext i
  ext1 z
  simp only [Finset.sum_apply,map_sum,opal,coeff_mk,Prod.snd_sum]
  exact glean_pool F i univ (fun a _=>solo_stretch (openLaw a))

theorem summed (simple:G.Simple)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (P:ι→TowerS G D)(openLaw:∀a,On k (P a))(i:Alma (R.family.labels.level h)):
    accrued R fit m K N k (∑a,P a) i=∑a,accrued R fit m K N k (P a) i:=by
  have valid:LocalRatio O:=(RunFormalChain.fromRun R).receipt
  have ages:m+(K-m)≤N:=by omega
  unfold accrued
  rw [combined L O simple valid N k h m (K-m) ages P openLaw,
    booked _ _ (fun a=>spoolEnd ages simple valid (openLaw a))]
  unfold matrix
  simp only [Finset.sum_apply,Finset.smul_sum]
  exact Finset.sum_comm

def amount {F:Frame G h}(v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(a:Alma F):ℝ:=
  if rankS a.val.2=0 then p (v (sheet F a)) else 0

theorem intrinsic {F:Frame G h}(v:F.Coeff)(p:ℂ →L[ℝ] ℝ)(a:Alma F):
    written F v p a=C (amount v p a)*PowerSeries.X^(valence F a):=by
  by_cases b:rankS a.val.2=0
  · simp only [WilsonOriginalPhysicalFruitVerse.written,amount,if_pos b,monomial_eq_C_mul_X_pow]
  · simp [WilsonOriginalPhysicalFruitVerse.written,amount,b]

theorem issued (simple:G.Simple)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:h≤k)(v:(R.family.labels.level h).Coeff)(p:ℂ →L[ℝ] ℝ)(i:Alma (R.family.labels.level h)):
    let I:=plate T fit
    let B:=relativeF L O N m (K-m)
    accrued R fit m K N k (Shrine I (written (R.family.labels.level h) v p)) i=
      ∑a,(PowerSeries.X^(valence (R.family.labels.level h) a))*
        (C (amount v p a)*(B^(valence (R.family.labels.level h) a)*accrued R fit m K N k (vein I a) i)):=by
  intro I B
  have solid:Shimmer I:=freshly T H fit sound pop
  have names (a:Alma (R.family.labels.level h)):On k (vein I a):=
    hailed I solid a ((valence_cap ..).trans capacity)
  have valid:LocalRatio O:=(RunFormalChain.fromRun R).receipt
  unfold Shrine
  rw [summed R simple fit m K N k before upper _ (fun a=>(names a).stem _) i]
  refine Finset.sum_congr rfl fun a _=>?_
  rw [WilsonPositionProgramTrialPublicJointGroundSuspension.read R simple valid fit m K N k before upper _ (names a)]
  rw [intrinsic,map_mul,map_pow,reel_C,reel_X,mul_pow]
  change (C _*(B^_*PowerSeries.X^_))*_=_ 
  ring

theorem original (simple:G.Simple)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (capacity:h≤k)(q:ℕ)(v:(R.family.labels.level h).Coeff)(p:ℂ →L[ℝ] ℝ)(i:Alma (R.family.labels.level h)):
    let I:=plate T fit
    let B:=relativeF L O N m (K-m)
    coeff q (accrued R fit m K N k (Shrine I (written (R.family.labels.level h) v p)) i)=
      ∑a,if valence (R.family.labels.level h) a ≤ q then
        amount v p a*coeff (q-valence (R.family.labels.level h) a)
          (B^(valence (R.family.labels.level h) a)*accrued R fit m K N k (vein I a) i) else 0:=by
  intro I B
  rw [issued R simple fit m K N k before upper T sound pop capacity v p i,map_sum]
  refine Finset.sum_congr rfl fun a _=>?_
  rw [PowerSeries.coeff_X_pow_mul']
  split <;> simp_all [I,B]

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundPortfolio
