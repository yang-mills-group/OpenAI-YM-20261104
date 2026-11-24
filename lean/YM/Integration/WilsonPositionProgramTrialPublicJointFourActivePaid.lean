import YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveTile

/-! Uniform original older-cutoff price for the full accrued nonunit rows. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourActivePaid
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
open WilsonPositionProgramTrialPublicJointGroundBirth (accrued mounted)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:4<D)(rails:Rails 4 k u e)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData (R.family.labels.level 4)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T):
    ∃(C:Credit)(A:Alma (R.family.labels.level 4)→ℝ),(∀i,0 ≤ A i) ∧
      ∀ᶠj:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N → ∀c:Verse (R.family.labels.level 4),
        ∀q ≤ e,∀i:Alma (R.family.labels.level 4),sheet (R.family.labels.level 4) i ≠ 0 →
        ‖coeff q (accrued R fit m K N k (Shrine (plate T fit) c) i)‖ ≤ C.buy (age L m K)*charge e c A:=by
  let Q:=sectionSeal (R.family.localSection 4) fit
  obtain ⟨C,buy⟩:=WilsonPositionProgramTrialPublicJointFourActiveTile.original (hol G)
    (R.family.localSection 4) fit rails CC CC CC CC simple
  obtain ⟨A,an,paid⟩:=WilsonIndependentMatchedFiledIncome.original T fit H sound pop rails.hk e u
  refine ⟨C,A,an,?_⟩
  filter_upwards [WilsonPositionProgramTrialPublicJointCapGroundFare.course R simple v funded fit rails capacity] with j court
  obtain ⟨l,a,same,_,levels,reals,clock,start⟩:=court
  intro m K N late before top c q depth i active
  have mark:=paid c
  let X:=WilsonIndependentMatchedKernelResidual.diagonal l a same m (K-m) N (start.le.trans late)
    (by omega) (Shrine (plate T fit) c) mark.1 (charge e c A) mark.2.1 mark.2.2
  have fx:X.ax=L:=levels
  have fm:X.m=m:=rfl
  have date:X.ceilC=K:=Nat.add_sub_of_le before
  have cash:=buy X q depth i active
  have house:=mounted R fit rails CC CC CC CC m K N X fx reals fm date rfl
  have ages:X.Age=age L m K:=(WilsonPositionProgramTrialStationHome.dates (Q:=Q) X L m K fx clock fm date).2
  change ‖coeff q (home Q X i)‖ ≤ _ at cash
  have ret:=congrArg (fun b:Verse (R.family.labels.level 4)=>‖coeff q (b i)‖) house
  rw [ages] at cash
  exact ret.le.trans cash

end YM.Integration.WilsonPositionProgramTrialPublicJointFourActivePaid
