import YM.Integration.WilsonPositionProgramTrialPublicJointGroundField

/-! The leading physical angular coordinate of one actual filed group field on the
old unmarked prior, at a cutoff and dose supplied after the registered course. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundBirth
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
def accrued (fit:h<D)(m K N k:ℕ)(P:TowerS G D):Verse (R.family.labels.level h):=
  matrix (Wray L O (R.family.localSection h) fit N m)
    (opal (R.family.labels.level h) (spools L O N k h m (K-m) P))

theorem mounted (fit:h<D)(rails:Rails h k u e)(E U V B:Credit)(m K N:ℕ)
    (X:CutsP (hol G) (R.family.localSection h) fit rails E U B V)
    (levels:X.ax=L)(ratio:X.tx=O)(start:X.m=m)(stop:X.ceilC=K)(prior:X.N=N):
    accrued R fit m K N k X.pt=home (sectionSeal (R.family.localSection h) fit) X:=by
  have length:X.i=K-m:=by rw [←start,←stop];exact (Nat.add_sub_cancel_left X.m X.i).symm
  change matrix _ (opal _ (spools _ _ _ _ _ _ _ _))=matrix _ (opal _ (spools _ _ _ _ _ _ _ _))
  rw [levels,ratio,start,prior,length]
  rfl

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (size:h ≤ 6)(fit:h<D)(rails:Rails h k u e)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData (R.family.labels.level h)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T):
    ∃(C:Credit)(A:Alma (R.family.labels.level h)→ℝ),(∀i,0 ≤ A i) ∧
      ∀ᶠj:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N → ∀(c:Verse (R.family.labels.level h))
        (i:Alma (R.family.labels.level h)),2 ≤ valence (R.family.labels.level h) i →
        h ≤ 2*valence (R.family.labels.level h) i →
        ‖coeff 0 (accrued R fit m K N k (Shrine (plate T fit) c) i)-coeff 0 (c i)‖ ≤
          C.buy (age L m K)*trailC (L).S m K*charge e c A:=by
  let Q:=sectionSeal (R.family.localSection h) fit
  obtain ⟨C,buy⟩:=WilsonPositionProgramTrialPublicJointGroundField.purchase (H:=hol G) Q rails CC CC CC CC CC size
  obtain ⟨A,an,paid⟩:=WilsonIndependentMatchedFiledIncome.original T fit H sound pop rails.hk e u
  refine ⟨C,A,an,?_⟩
  filter_upwards [WilsonPositionProgramTrialPublicJointCapGroundFare.course R simple v funded fit rails capacity] with j court
  obtain ⟨l,a,same,levelsWest,levels,reals,clock,start⟩:=court
  intro m K N late before live c i active full
  have mark:=paid c
  let X:=WilsonIndependentMatchedKernelResidual.diagonal l a same m (K-m) N (start.le.trans late)
    (by omega) (Shrine (plate T fit) c) mark.1 (charge e c A) mark.2.1 mark.2.2
  have fx:X.ax=L:=levels
  have fo:X.tx=O:=reals
  have fm:X.m=m:=rfl
  have fn:X.N=N:=rfl
  have date:X.ceilC=K:=Nat.add_sub_of_le before
  have west:Weston X.L.L CC:=levelsWest
  have rhs:=buy X west (plate T fit) c (freshly T H fit sound pop) rfl i active full
  have household:=mounted R fit rails CC CC CC CC m K N X fx fo fm date fn
  have ages: X.Age=age L m K:=(WilsonPositionProgramTrialStationHome.dates (Q:=Q) X L m K fx clock fm date).2
  have rate:X.ρ=trailC (L).S m K:=by change trailC X.ax.S X.m X.ceilC=_;rw [fx,fm,date]
  have cost:X.fuel=charge e c A:=rfl
  change ‖coeff 0 (home Q X i)-coeff 0 (c i)‖ ≤ _ at rhs
  have tariff:C.buy X.Age*X.ρ*X.fuel=C.buy (age L m K)*trailC (L).S m K*charge e c A:=by
    rw [ages,rate,cost]
  have sameAmount:=congrArg (fun b:Verse (R.family.labels.level h)=>‖coeff 0 (b i)-coeff 0 (c i)‖) household
  exact sameAmount.le.trans (rhs.trans tariff.le)

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundBirth
