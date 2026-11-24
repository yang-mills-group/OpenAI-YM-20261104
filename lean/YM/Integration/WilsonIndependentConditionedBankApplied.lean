import YM.Integration.WilsonIndependentConditionedBankReport
import YM.Integration.WilsonIndependentConditionedBankOptics

/-! Apply the optical bracket to the original dated salaries in the actual reported pair. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankApplied
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

def field (R:Run G)(Q:SealR G)(old young:Credit)(host m K q:ℕ)(a A:ℝ):ℝ:=
  (Fintype.card (Alma Q.F):ℝ)*((q+1:ℕ):ℝ)*
    (old.buy (age R host m)*(young.buy (age R m K)*(|a| * A)))

def gram (R:Run G)(Q:J→SealR G)(rate:Credit)(host K q:ℕ)(φ:(s:J)→Rarity (Q s).D)(B:J→ℝ)(y:ℝ):ℝ:=
  let A:=R.family.path.levels
  ((q+1:ℕ):ℝ)*(rate.buy (zz A host+2*(A.S.scale K-A.S.scale host))*
    (coinMat ((Q 0).h+(Q 1).h) e*profile (φ 0) y (B 0)*profile (φ 1) y (B 1)))

def gross (q:ℕ)(F i A B G:ℝ):ℝ:=
  max (((q+1:ℕ):ℝ)*F*i)
    (2*((q+1:ℕ):ℝ)*F*(|A|+|B|)+3*|G| * |A| * |B|)

private theorem absolute (q:ℕ)(g F i a b G:ℝ)(pay:0 ≤ F):
    debit q g F i a b G ≤ debit q g F i |a| |b| G:=by
  let t:=|g|^(q+1)
  have nt:0 ≤ t:=pow_nonneg (abs_nonneg _) _
  have terms:|G| *a*b ≤ |G| * |a| * |b|:=by
    calc
      _ ≤ |(|G| *a*b)|:=le_abs_self _
      _=_:=by simp [abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add_right
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self a) (le_abs_self b)) (mul_nonneg (by norm_num) nt)) i)
    (mul_nonneg (by positivity) pay)) (mul_le_mul_of_nonneg_left terms (mul_nonneg (by norm_num) nt))

theorem original (R:Run G)(Q:J→SealR G)(C₁ C₂:J→Credit)(rate:Credit)
    (host m K q:ℕ)(cut:m ≤ K)(S inverse g ζ:ℝ)(paid:0 ≤ S)(gain:0 ≤ ζ)
    (a A B:J→ℝ)(φ:(s:J)→Rarity (Q s).D)(y:ℝ):
    let δ:=paceT R.family.path.levels.S m K; let H:=(Q 0).h+(Q 1).h
    let A₀:=fun s=>field R (Q s) (C₁ s) (C₂ s) host m K q (a s) (A s)
    let G₀:=gram (e:=e) R Q rate host K q φ B y
    let E:=debit q g (S*δ^ζ) inverse
      (salary R (Q 0) (C₁ 0) (C₂ 0) host m K q (a 0) (A 0))
      (salary R (Q 1) (C₁ 1) (C₂ 1) host m K q (a 1) (A 1))
      (panel (e:=e) R Q rate host m K q φ B y)
    E ≤ gross q S inverse (A₀ 0) (A₀ 1) G₀*(δ^ζ+|g|^(q+1)*(δ^(2*H))⁻¹):=by
  intro δ H A₀ G₀ E
  have dp:0<δ:=div_pos (R.family.path.levels.S.a_pos _) (R.family.path.levels.S.a_pos _)
  have dc:δ ≤ 1:=(div_le_one (R.family.path.levels.S.a_pos _)).2 (R.family.path.levels.S.strictAnti.antitone cut)
  let cf:=fun s=>salary R (Q s) (C₁ s) (C₂ s) host m K q (a s) (A s)
  let G:=panel (e:=e) R Q rate host m K q φ B y
  have f (s:J):|cf s|=|A₀ s| *(δ^(Q s).h)⁻¹:=by
    have eq:cf s=A₀ s*(δ^(Q s).h)⁻¹:=by dsimp only [cf,A₀,δ,salary,field];ring
    rw [eq,abs_mul,abs_of_pos (inv_pos.mpr (pow_pos dp _))]
  have normG:G=G₀*(δ^H)⁻¹:=by dsimp only [G,G₀,WilsonIndependentConditionedBankReport.panel,gram,δ,H];ring
  let ns:ℝ:=((q+1:ℕ):ℝ); let t:=|g|^(q+1)
  let low:=ns*S*inverse
  let high:=2*ns*S*(|A₀ 0|+|A₀ 1|)+3*|G₀| * |A₀ 0| * |A₀ 1|
  have nt:0 ≤ t:=pow_nonneg (abs_nonneg _) _
  have price:=WilsonIndependentConditionedBankOptics.gross (Q 0).h (Q 1).h δ ζ ns t S inverse
    |A₀ 0| |A₀ 1| G₀ dp dc gain (by dsimp [ns];positivity) nt paid (abs_nonneg _) (abs_nonneg _)
  have step:E ≤ debit q g (S*δ^ζ) inverse |cf 0| |cf 1| G:=
    absolute q g (S*δ^ζ) inverse (cf 0) (cf 1) G (mul_nonneg paid (Real.rpow_nonneg dp.le _))
  rw [f,f,normG] at step
  apply step.trans <| price.trans ?_
  change low*δ^ζ+t*(δ^(2*H))⁻¹*high ≤ max low high*(δ^ζ+t*(δ^(2*H))⁻¹)
  calc
    _ ≤ max low high*δ^ζ+t*(δ^(2*H))⁻¹*max low high:=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.rpow_nonneg dp.le _))
        (mul_le_mul_of_nonneg_left (le_max_right ..) (mul_nonneg nt (inv_nonneg.mpr (pow_nonneg dp.le _))))
    _= _:=by ring

end YM.Integration.WilsonIndependentConditionedBankApplied
