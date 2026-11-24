import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedResponse
import YM.Integration.WilsonSeparatedPrefixMovingFrozenAge

/-! The signed measured field on a common optical interval at its own physical coupling. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedCollar
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
    (T:SectionData (R.family.labels.level 4)){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (width η:ℝ)(wide:0≤width)(gain:0<η)(margin:2*η ≤ 1):
    ∃M:ℝ,0 ≤ M ∧ ∀ᶠ j:ℕ in atTop,∀ m K N per:ℕ,j ≤ m → m ≤ K → K ≤ N →
    let t:=regulatorRun R.family N per m
    let g:=regulatorRun R.family N per K
    0 < t → t ≤ 1 → g ≠ 0 → (L).S.a m/(L).S.a K ≤ t^(-width) →
    (L).S.a K/(L).S.a m ≤ t^(8*η) →
    ∀q:ℕ,2 ≤ q → q ≤ e → ∀(v:(R.family.labels.level 4).Coeff)(p:ℂ →L[ℝ] ℝ)
      (i:Alma (R.family.labels.level 4)),sheet (R.family.labels.level 4) i ≠ 0 →
      let F:=R.family.labels.level 4
      let b:=accrued R fit m K N k (Shrine (plate T fit) (written F (vector F g v) p)) i
      ‖reading q t b-(t/g)^2*amount v p i‖ ≤ (t/g)^2*M*t^η*fieldSize v p:=by
  obtain ⟨C,P,A,B,ha,hb,heard⟩:=WilsonPositionProgramTrialPublicJointFourSignedResponse.original R simple v₀ funded
    fit rails enough capacity T sound pop
  obtain ⟨jC,hC⟩:=Filter.eventually_atTop.mp (WilsonSeparatedPrefixMovingFrozenAge.credits R simple C width η wide gain)
  obtain ⟨jP,hP⟩:=Filter.eventually_atTop.mp (WilsonSeparatedPrefixMovingFrozenAge.credits R simple P width η wide gain)
  refine ⟨A+e*B,by positivity,?_⟩
  filter_upwards [heard,eventually_ge_atTop jC,eventually_ge_atTop jP,
    WilsonPositionProgramTrialPublicJointCapGroundFare.course R simple v₀ funded fit rails capacity] with j receipt ctop ptop room
  intro m K N per late before top t g hot small real thick thin q floor depth v p i nonunit F b
  obtain ⟨l,_,_,_,levels,_,clock,start⟩:=room
  let window:WindowS G (e+1) CC:=⟨l.L.V,m,K-m,N,N,K,start.le.trans late,by omega,top,top⟩
  have warm:1 ≤ age L m K:=by
    have w:=window.warm
    change 1 ≤ l.L.V.y m+(l.L.V.draws.S.scale (m+(K-m))-l.L.V.draws.S.scale m)+((K-m:ℕ):ℝ) at w
    simpa only [age,WilsonPositionProgramTrialStationHome.elapsed,levels,clock,Nat.add_sub_of_le before] using w
  have c:C.buy (age L m K) ≤ t^(-η):=(le_abs_self _).trans (hC m (ctop.trans late) K N per before top thick _ warm le_rfl)
  have pp:P.buy (age L m K) ≤ t^(-η):=(le_abs_self _).trans (hP m (ptop.trans late) K N per before top thick _ warm le_rfl)
  have saved:trailC (L).S m K ≤ t^(2*η):=by
    rw [trail_ratio]
    calc
      _ ≤ (t^(8*η))^((4:ℝ)⁻¹):=Real.rpow_le_rpow (div_pos ((L).S.a_pos _) ((L).S.a_pos _)).le thin (by norm_num)
      _=t^(2*η):=by rw [←Real.rpow_mul hot.le];congr 1;ring
  have first:C.buy (age L m K)*trailC (L).S m K ≤ t^η:=calc
    _ ≤ t^(-η)*t^(2*η):=mul_le_mul c saved (Real.exp_pos _).le (Real.rpow_nonneg hot.le _)
    _=t^η:=by rw [←Real.rpow_add hot];congr 1;ring
  have other:t*P.buy (age L m K) ≤ t^η:=calc
    _ ≤ t*t^(-η):=mul_le_mul_of_nonneg_left pp hot.le
    _=t^(1-η):=by rw [sub_eq_add_neg,Real.rpow_add hot,Real.rpow_one]
    _≤t^η:=Real.rpow_le_rpow_of_exponent_ge hot small (by linarith only [margin])
  have qbound:((q-2:ℕ):ℝ) ≤ (e:ℝ):=by exact_mod_cast (show q-2 ≤ e by omega)
  have tail:((q-2:ℕ):ℝ)*t*P.buy (age L m K) ≤ (e:ℝ)*t^η:=by
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left other (by positivity)).trans
      (mul_le_mul_of_nonneg_right qbound (Real.rpow_nonneg hot.le _))
  have size:0 ≤ fieldSize v p:=Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  calc
    _ ≤ _:=receipt m K N late before top q floor depth g t real hot.le small v p i nonunit
    _ ≤ (t/g)^2*((t^η)*A+((e:ℝ)*t^η)*B)*fieldSize v p:=by
      apply mul_le_mul_of_nonneg_right _ size
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact add_le_add (mul_le_mul_of_nonneg_right first ha) (mul_le_mul_of_nonneg_right tail hb)
    _=_:=by ring

end YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedCollar
