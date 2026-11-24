import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedWage
import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedReading

/-! The signed numerical relative response on all original nonconstant grade-four rows. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedResponse
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
open WilsonIndependentMatchedPhysicalPeer (reading)

open WilsonPositionProgramTrialPublicJointFourSignedSource (strip)
open WilsonPositionProgramTrialPublicJointFourSignedWage (fieldSize wage)

theorem original (simple:G.Simple)(v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    (fit:4<D)(rails:Rails 4 k u e)(enough:4 ≤ k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData (R.family.labels.level 4)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T):
    ∃(C P:Credit)(A B:ℝ),0 ≤ A ∧ 0 ≤ B ∧
    ∀ᶠj:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N → ∀q:ℕ,2 ≤ q → q ≤ e →
    ∀g t:ℝ,g ≠ 0 → 0 ≤ t → t ≤ 1 → ∀(v:(R.family.labels.level 4).Coeff)(p:ℂ →L[ℝ] ℝ)
      (i:Alma (R.family.labels.level 4)),sheet (R.family.labels.level 4) i ≠ 0 →
      let F:=R.family.labels.level 4
      let b:=accrued R fit m K N k (Shrine (plate T fit) (written F (vector F g v) p)) i
      let multiplier:=(t/g)^2
      ‖reading q t b-multiplier*amount v p i‖ ≤ multiplier*(C.buy (age L m K)*trailC (L).S m K*A+
        ((q-2:ℕ):ℝ)*t*P.buy (age L m K)*B)*fieldSize v p:=by
  obtain ⟨C,X,hx,ground⟩:=WilsonPositionProgramTrialPublicJointGroundSigned.original R simple v₀ funded
    (by decide) fit rails enough capacity T sound pop
  obtain ⟨P,Y,hy,high⟩:=WilsonPositionProgramTrialPublicJointFourActivePaid.original R simple v₀ funded
    fit rails capacity T sound pop
  let A:=wage e X 1
  let B:=wage e Y (PowerSeries.X^2)
  refine ⟨C,P,A,B,Finset.sum_nonneg (fun a _=>WilsonIndependentMatchedFiledIncome.nonneg (hx a) _ e),
    Finset.sum_nonneg (fun a _=>WilsonIndependentMatchedFiledIncome.nonneg (hy a) _ e),?_⟩
  filter_upwards [ground,high,WilsonPositionProgramTrialPublicJointFourSignedSource.raw R simple v₀ funded fit rails
    enough capacity T sound pop,WilsonPositionProgramTrialPublicJointCapGroundFare.course R simple v₀ funded fit rails capacity] with j receipt paid embodied room
  intro m K N late before top q floor depth g t real hot small v p i nonunit F b factor
  let pure:=accrued R fit m K N k (Shrine (plate T fit) (written F (strip v) p)) i
  obtain ⟨l,_,_,_,levels,_,clock,start⟩:=room
  let window:WindowS G (e+1) CC:=⟨l.L.V,m,K-m,N,N,K,start.le.trans late,by omega,top,top⟩
  have warm:1 ≤ age L m K:=by
    have w:=window.warm
    change 1 ≤ l.L.V.y m+(l.L.V.draws.S.scale (m+(K-m))-l.L.V.draws.S.scale m)+((K-m:ℕ):ℝ) at w
    simpa only [age,WilsonPositionProgramTrialStationHome.elapsed,levels,clock,Nat.add_sub_of_le before] using w
  have agree:PowerSeries.C (g^2)*b=pure:=embodied m K N late before top g real v p i nonunit
  have clocked:g^2*reading q t b=reading q t pure:=by
    rw [←agree,WilsonPositionProgramTrialPublicJointFourSignedReading.scale]
  have back:g^2*coeff 2 b=coeff 2 pure:=by rw [←agree,coeff_C_mul]
  have tr:=receipt m K N late before top 2 (by decide) (by decide) g real v p i
    (WilsonPositionProgramTrialPublicJointFourSignedSource.rank simple i nonunit)
  dsimp only at tr
  rw [WilsonPositionProgramTrialPublicJointGroundSigned.quadratic simple,sub_zero] at tr
  have mrate:0 ≤ C.buy (age L m K)*trailC (L).S m K:=
    mul_nonneg (zero_le_one.trans (C.purchase warm)) (trail_pos ..).le
  have head:‖coeff 2 pure-amount v p i‖ ≤ C.buy (age L m K)*trailC (L).S m K*A*fieldSize v p:=by
    rw [←back]
    exact tr.trans ((mul_le_mul_of_nonneg_left
      (WilsonPositionProgramTrialPublicJointFourSignedWage.original simple e X hx v p).1 mrate).trans_eq
      (by ring))
  have posP:0 ≤ P.buy (age L m K):=zero_le_one.trans (P.purchase warm)
  have tariff l (hl:l ≤ q):‖coeff l pure‖ ≤ P.buy (age L m K)*B*fieldSize v p:=by
    have price:=paid m K N late before top (written F (strip v) p) l (hl.trans depth) i nonunit
    exact price.trans ((mul_le_mul_of_nonneg_left
      (WilsonPositionProgramTrialPublicJointFourSignedWage.original simple e Y hy v p).2 posP).trans_eq
      (by ring))
  have estimate:=WilsonPositionProgramTrialPublicJointFourSignedReading.estimate q floor t hot small pure
    (amount v p i) _ _ (WilsonPositionProgramTrialPublicJointFourSignedSource.starts R simple fit m K N k
      before top T sound pop enough v p i) head tariff
  rw [←clocked] at estimate
  have hp:0<g^2:=sq_pos_of_ne_zero real
  have exchange:g^2*factor=t^2:=by dsimp [factor];field_simp
  apply le_of_mul_le_mul_left (by
    calc
      g^2*‖reading q t b-factor*amount v p i‖=‖g^2*(reading q t b-factor*amount v p i)‖:=by
        rw [norm_mul,Real.norm_of_nonneg hp.le]
      _=‖g^2*reading q t b-t^2*amount v p i‖:=by rw [mul_sub,←mul_assoc,exchange]
      _ ≤ _:=estimate
      _=g^2*(factor*(C.buy (age L m K)*trailC (L).S m K*A+
          ((q-2:ℕ):ℝ)*t*P.buy (age L m K)*B)*fieldSize v p):=by rw [←exchange];ring) hp

end YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedResponse
