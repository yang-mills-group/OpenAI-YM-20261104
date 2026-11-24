import YM.Integration.WilsonIndependentConditionedBankStableCost
import YM.Integration.WilsonIndependentConditionedGramShellLifetime

/-! The invoice for the four measured preparations, with all raw source charges paid on the reported board. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankAward
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFiledSemester (Tested)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

open WilsonIndependentConditionedBankCorner (Bill input)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentFittedPivotCash (view)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentConditionedBankPublicGram (response)
open WilsonPositionProgramTrialHomeDose (publicDose)

open WilsonIndependentConditionedBankFour (Enrolled)
open WilsonIndependentConditionedBankMatrix (sample protocol)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentConditionedBankPublicGram (residual)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentFittedMixedCash (embed)
open WilsonOlderFreshSoftCoverScalar (clock)

open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedGramCampus (Paid)
open WilsonIndependentConditionedGramPrices (profile)
open WilsonPhysicalMarkedDefect.RawProduct (belt positive)
open WilsonSeparatedPrefixMovingCalendar (epoch)

open WilsonIndependentConditionedBankReport (salary panel debit)

open WilsonIndependentConditionedBankApplied (field gram)

def fare (R:Run G)(Q:J→SealR G)(C₁ C₂:J→Credit)(rate:Credit)(coins:Prices)
    (u b host m K q:ℕ)(inverse ζ:ℝ)(H B:J→ℝ)(t z:ℝ)(φ:(s:J)→Rarity (Q s).D)(y:ℝ):ℝ:=
  let S:=roof (wage (k:=k) (e:=e) R Q coins u b host m K ζ (fun _=>1) (fun _=>1) B t z)*
    (1+H 0)*(1+H 1)
  let cf:=fun s=>|field R (Q s) (C₁ s) (C₂ s) host m K q 1 1| * H s
  WilsonIndependentConditionedBankStableCost.gross q S inverse (cf 0) (cf 1) |gram (e:=e) R Q rate host K q φ B y|

theorem original (R:Run G)(Q:J→SealR G)(C₁ C₂:J→Credit)(rate:Credit)(coins:Prices)
    (u b host m K q:ℕ)(cut:m ≤ K)(inverse g ζ η:ℝ)(nn:0 ≤ inverse)
    (gain:0 ≤ ζ)(quarter:ζ ≤ 1/4)(_paid:0 ≤ η)(room:2*η ≤ ζ/4)
    (a A H B:J→ℝ)(inlet:∀s,0 ≤ A s)(source:∀s,|a s| * A s ≤ H s*(paceT R.family.path.levels.S m K)^(-η))
    (t z:ℝ)(φ:(s:J)→Rarity (Q s).D)(y:ℝ):
    let δ:=paceT R.family.path.levels.S m K;let n:=(Q 0).h+(Q 1).h
    let S:=roof (wage (k:=k) (e:=e) R Q coins u b host m K ζ a A B t z)
    let cf:=fun s=>salary R (Q s) (C₁ s) (C₂ s) host m K q (a s) (A s)
    debit q g (S*δ^ζ) inverse (cf 0) (cf 1) (panel (e:=e) R Q rate host m K q φ B y)
      ≤ fare (k:=k) (e:=e) R Q C₁ C₂ rate coins u b host m K q inverse ζ H B t z φ y*
        (δ^(3*ζ/4)+|g|^(q+1)*(δ^(2*n+1))⁻¹):=by
  intro δ n S cf
  let U:=roof (wage (k:=k) (e:=e) R Q coins u b host m K ζ (fun _=>1) (fun _=>1) B t z)
  let before:=U*(1+H 0)*(1+H 1)
  let costs:=fun s=>|field R (Q s) (C₁ s) (C₂ s) host m K q 1 1| * H s
  let v:=gram (e:=e) R Q rate host K q φ B y
  have dp:0<δ:=div_pos (R.family.path.levels.S.a_pos _) (R.family.path.levels.S.a_pos _)
  have dc:δ ≤ 1:=(div_le_one (R.family.path.levels.S.a_pos _)).2 (R.family.path.levels.S.strictAnti.antitone cut)
  have pos (s:J):0 ≤ |a s| * A s:=mul_nonneg (abs_nonneg _) (inlet s)
  have Hpos (s:J):0 ≤ H s:=nonneg_of_mul_nonneg_left ((pos s).trans (source s)) (Real.rpow_pos_of_pos dp _)
  have op:0 ≤ S:=le_max_left ..
  have up:0 ≤ U:=le_max_left ..
  have bpos:0 ≤ before:=mul_nonneg (mul_nonneg up (by linarith only [Hpos 0])) (by linarith only [Hpos 1])
  have shel:= (WilsonIndependentConditionedGramShellLifetime.original R Q coins k e u b host m K
    ζ η δ a A B H t z dp dc gain room pos source).2
  have single:S*δ^ζ ≤ before*δ^(3*ζ/4):=by
    calc S*δ^ζ = δ^ζ*S :=mul_comm ..
         _ ≤ δ^(3*ζ/4)*U*(1+H 0)*(1+H 1):=shel
         _ = _ := by dsimp only [before];ring
  have norm (s:J):|cf s| ≤ costs s*((δ^(Q s).h)⁻¹*δ^(-η)):=by
    let v₀:=field R (Q s) (C₁ s) (C₂ s) host m K q 1 1
    have eq:cf s=v₀*(|a s| * A s)*(δ^(Q s).h)⁻¹:=by
      dsimp only [cf,salary,v₀,field,δ];simp only [abs_one,mul_one];ring
    rw [eq,abs_mul,abs_mul,abs_of_nonneg (pos s),abs_of_pos (inv_pos.mpr (pow_pos dp _))]
    calc
      _ ≤ |v₀| * (H s*δ^(-η))*(δ^(Q s).h)⁻¹:=by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (source s) (abs_nonneg _)) (by positivity)
      _ = _ :=by dsimp only [costs,v₀];ring
  have pp:panel (e:=e) R Q rate host m K q φ B y=v*(δ^n)⁻¹:=by dsimp only [WilsonIndependentConditionedBankReport.panel,v,WilsonIndependentConditionedBankApplied.gram,δ,n];ring
  have pbound:|panel (e:=e) R Q rate host m K q φ B y| ≤ |v| * (δ^n)⁻¹:=by
    rw [pp,abs_mul,abs_of_pos (inv_pos.mpr (pow_pos dp _))]
  have cp (s:J):0 ≤ costs s:=mul_nonneg (abs_nonneg _) (Hpos s)
  exact WilsonIndependentConditionedBankStableCost.original δ g (3*ζ/4) η q (Q 0).h (Q 1).h
    before inverse (costs 0) (costs 1) |v| _ _ _ _ dp dc (by positivity) (by linarith only [room,quarter]) 
    (mul_nonneg op (Real.rpow_nonneg dp.le _)) nn bpos (cp 0) (cp 1) (abs_nonneg _)
    single (norm 0) (norm 1) pbound

end YM.Integration.WilsonIndependentConditionedBankAward
