import YM.Integration.WilsonPositionProgramTrialPublicJointGroundHead

/-! The original restored quadratic and cubic angular rows, retaining their signed lower feed. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundSigned
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
def lower {F:Frame G h}(q:ℕ)(g:ℝ)(v:F.Coeff)(p:ℂ→L[ℝ]ℝ)(B:Blue.Cost)(E:Alma F→Blue.Cost):ℝ:=
  ∑a,if 0<valence F a ∧ valence F a<q then g^(q-valence F a)*amount v p a*
    coeff (q-valence F a) (B^(valence F a)*E a) else 0

theorem quadratic {F:Frame G h}(simple:G.Simple)(g:ℝ)(v:F.Coeff)(p:ℂ→L[ℝ]ℝ)
    (B:Blue.Cost)(E:Alma F→Blue.Cost):lower 2 g v p B E=0:=by
  apply Finset.sum_eq_zero
  intro a _
  have one:valence F a≠1:=WilsonMaxwellThermometerWardColors.arity simple F (sheet F a)
  simp only [if_neg (show ¬(0<valence F a ∧ valence F a<2) by omega)]

theorem cubic {F:Frame G h}(simple:G.Simple)(g:ℝ)(v:F.Coeff)(p:ℂ→L[ℝ]ℝ)
    (B:Blue.Cost)(E:Alma F→Blue.Cost):
    lower 3 g v p B E= g*∑a,if valence F a=2 then amount v p a*coeff 1 (B^2*E a) else 0:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have one:valence F a≠1:=WilsonMaxwellThermometerWardColors.arity simple F (sheet F a)
  by_cases two:valence F a=2
  · simp [two,mul_assoc]
  · have none:¬(0<valence F a ∧ valence F a<3):=by omega
    simp [none,two]

theorem original (simple:G.Simple)(v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    (size:h≤6)(fit:h<D)(rails:Rails h k u e)(four:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T):
    ∃(C:Credit)(A:Alma (R.family.labels.level h)→ℝ),(∀i,0≤A i) ∧
    ∀ᶠj:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N → ∀q:ℕ,2≤q → h≤2*q → ∀g:ℝ,g≠0 →
      ∀(v:(R.family.labels.level h).Coeff)(p:ℂ →L[ℝ] ℝ)(i:Alma (R.family.labels.level h)),
      valence (R.family.labels.level h) i=q →
      let F:=R.family.labels.level h
      let I:=plate T fit
      let B:=relativeF L O N m (K-m)
      ‖g^q*coeff q (accrued R fit m K N k (Shrine I (written F (vector F g v) p)) i)-
          lower q g v p B (fun a=>accrued R fit m K N k (vein I a) i)-amount v p i‖≤
        C.buy (WilsonPositionProgramTrialStationHome.age L m K)*trailC (L).S m K*
          WilsonIndependentMatchedFiledIncome.charge e (picked v p q) A:=by
  obtain ⟨C,A,nonneg,front⟩:=WilsonPositionProgramTrialPublicJointGroundBirth.original R simple v₀ funded
    size fit rails capacity T sound pop
  refine ⟨C,A,nonneg,?_⟩
  filter_upwards [front,WilsonPositionProgramTrialPublicJointGroundHead.original R simple v₀ funded
    size fit rails four capacity T sound pop] with j salary identity
  intro m K N late before upper q positive full g hg v p i hit F I B
  have active:sheet F i≠0:=by
    intro unit
    have z:valence F i=0:=by rw [valence,unit,F.zero_degree]
    have hitF:valence F i=q:=hit
    omega
  have split:=identity m K N late before upper q (by omega) g hg v p i active
  have bill:=salary m K N late before upper (picked v p q) i (by omega) (by omega)
  have atI:coeff 0 (picked v p q i)=amount v p i:=by simp [picked,hit]
  rw [←atI]
  change ‖_ - lower q g v p B _ - coeff 0 (picked v p q i)‖≤_
  change _=coeff 0 (accrued R fit m K N k (Shrine I (picked v p q)) i)+lower q g v p B _ at split
  rw [split,add_sub_cancel_right]
  exact bill

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundSigned
