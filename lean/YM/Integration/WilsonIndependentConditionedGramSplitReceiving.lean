import YM.Integration.WilsonIndependentConditionedGramSplitPooled
import YM.Integration.WilsonIndependentConditionedGramShellRoster

/-! The priced ordinary conditional debit at the actual independent two-slot
receiver, with the amplitudes of its two original physical arms kept separate. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramSplitReceiving
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
variable {G:Gauge}{e k u u₀:ℕ}
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
open WilsonIndependentConditionedGramPrices (profile)
open WilsonPhysicalMarkedDefect.RawProduct (belt positive)
open WilsonSeparatedPrefixMovingCalendar (epoch)

open WilsonIndependentConditionedBankReport (salary panel debit)

open WilsonIndependentConditionedBankApplied (field gram)

open GapsContact Climb PhysicalNext Extraction Table Spec Trace.Pilot Trace.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonIndependentConditionedGramSplitPooled (marked)
open WilsonIndependentConditionedGramRawHome (fixed)
open WilsonIndependentConditionedGramSplitAward (homeLow homeHigh)
variable {R₀:Run G}{o:Extraction.Order}{RTable:Table R₀.family.book}
    (F:Final R₀.family o RTable){l:Ultrafilter (ℕ×ℕ)}{ℋ:(Bel R₀.family.book).Hierarchy}
    {Z:Trace.Terrace.Arch R₀.family}{I:Type}[Fintype I]
local notation "Bf" => R₀.family.path.levels.clock.hatBeta

theorem original {D T:ℕ}{d:I→Fin (D+1)}{limit:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<limit})→Book F (l:=l) ℋ Z D T s.val)(ρ:I→{s:ℝ // 0<s ∧ s<limit})
    (phys:(i:I)→{s:ℝ // 0<s ∧ s<limit}→Bool→RTable.Field (d i).val)(M:I→ℝ)(E:I→ℕ)
    (sale:Paid F D T d books phys M E ρ (reporter F books ρ))
    (flag:J→Bool)(θ:ℝ)(small:θ ≤ 1)(α:J→ℂ)(doseP:∀i,‖α i‖ ≤ 1)
    (choose:J→I)(c:J→ℝ)(colour:∀s,0 ≤ c s)
    {R:Run G}{Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}{V:Realm G (e+1) C}
    {coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}{ι:J→Type*}
    {P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{b host m K N:ℕ}
    (Y:Assigned R Q own V coins j port ι P A u b host m K N)
    (early:j ≤ host)(older:host ≤ m)(cut:m ≤ K)(ageV:V.y=zz R.family.path.levels)(pick:(s:J)→ι s)
    (C₁ C₂:J→Credit)(rate:Credit)(q:ℕ)(inverse g ζ η:ℝ)(nn:0 ≤ inverse)
    (gain:0 ≤ ζ)(quarter:ζ ≤ 1/4)(eta:0 ≤ η)(room:2*η ≤ ζ/4)
    (a B:J→ℝ)(t z:ℝ)(φ:(s:J)→Rarity (Q s).D)(y:ℝ)
    (source:∀s,|a s| *A s (pick s) ≤
      (marked F books ρ phys (flag s) θ (α s) (choose s)*c s)*(paceT R.family.path.levels.S m K)^(-η)):
    let δ:=paceT R.family.path.levels.S m K;let n:=(Q 0).h+(Q 1).h
    let f:=reporter F books ρ
    let Y₀:=fun s=>Y.cuts s (pick s)
    let cap:=fun s=>M (choose s)*fixed R₀ (d (choose s)).val*c s
    let E₀:=E (choose 0);let E₁:=E (choose 1)
    let shell:=WilsonIndependentConditionedPairProbes.charge Q own C C C C V Y₀ coins u b host m K ζ a B t z
    let cf:=fun s=>salary R (Q s) (C₁ s) (C₂ s) host m K q (a s) (A s (pick s))
    let U:=roof (wage (k:=k) (e:=e) R Q coins u b host m K ζ (fun _=>1) (fun _=>1) B t z)
    let Fprice:=fun s=>|field R (Q s) (C₁ s) (C₂ s) host m K q 1 1|
    let Gprice:=|gram (e:=e) R Q rate host K q φ B y|
    debit q g (roof shell) inverse (cf 0) (cf 1) (panel (e:=e) R Q rate host m K q φ B y) ≤
      (homeLow q U inverse cap*(Bf f)^(E₀+E₁))*δ^(3*ζ/4) +
      (homeHigh q U Fprice cap Gprice*(Bf f)^(E₀+E₁+max E₀ E₁))*(|g|^(q+1)*(δ^(2*n+1))⁻¹):=by
  intro δ n f Y₀ cap E₀ E₁ shell cf U Fprice Gprice
  let raw:=fun s=>marked F books ρ phys (flag s) θ (α s) (choose s)*c s
  have inlet (s:J):0 ≤ A s (pick s):=by rw [←Y.price s (pick s)];exact (Y₀ s).hf
  have dp:0<δ:=pace_pos ..
  have exactFee:=(WilsonIndependentConditionedBankShellPrice.original Y early older ageV pick ζ a B t z).2
  have earned:=WilsonIndependentConditionedGramSplitAward.original (k:=k) (e:=e) R Q C₁ C₂ rate coins
    u b host m K q cut inverse g ζ η nn gain quarter eta room a (fun s=>A s (pick s)) raw B inlet source t z φ y
  have recorded:=WilsonIndependentConditionedGramSplitPooled.on_book F books ρ phys M E sale flag θ small α
    doseP choose c colour q U inverse Gprice Fprice (le_max_left ..) nn (abs_nonneg _) (fun _=>abs_nonneg _)
  change roof shell=_ at exactFee
  rw [exactFee]
  refine earned.trans (add_le_add (mul_le_mul_of_nonneg_right recorded.1 (Real.rpow_nonneg dp.le _))
    (mul_le_mul_of_nonneg_right recorded.2 (by positivity)))

end YM.Integration.WilsonIndependentConditionedGramSplitReceiving
