import YM.Integration.WilsonIndependentConditionedEarlierOpening
import YM.Integration.WilsonIndependentConditionedBankRulerQuartet
import YM.Integration.WilsonIndependentConditionedBankRulerPayment

/-! The same opening pays each actual tested thermal row on the finite family of signed preparations. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRulerTill
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


open WilsonIndependentConditionedActualBudget (Pay ages)
open WilsonIndependentConditionedActualCredit (badge gramAge)
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentConditionedBankApplied (field gram)
open WilsonIndependentConditionedGramPrices (profile)
open WilsonIndependentMatchedRosterReception (perSite)
open WilsonIndependentMatchedProxyIncome (tariff)
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterSlots (degree)
open WilsonInvariantActionPosition (berth)
open Real

open WilsonIndependentConditionedBankAward (fare)
open WilsonIndependentConditionedBankStableCost (gross)
open WilsonIndependentConditionedActualWages (unitWage stripped quote gramWage)

open WilsonIndependentConditionedGramSplitAward (homeLow homeHigh)
open WilsonIndependentConditionedGramRawHome (fixed)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)

open WilsonIndependentConditionedActualSplit (inverse)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open GapsContact Climb PhysicalNext Extraction Table Spec Trace.Pilot Trace.Physical PhysMS
variable {R:Run G}{ord:Extraction.Order}{S:Table R.family.book}(F:Final R.family ord S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{Z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I]


open WilsonIndependentConditionedEarlierSplit (Heard)
open WilsonIndependentConditionedGramSpatialHost (date)
open WilsonIndependentConditionedEarlierRoom (Room)

open WilsonIndependentConditionedBankRulerQuartet (due)
open Pert.Asymptotics

theorem original [Nonempty I](simple:G.Simple)(bliss:Bliss F l Z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {D T:ℕ}(d:I→Fin (D+1))(h:ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H Z D T s.val)
    (cap:(J→Bool×Bool)→J→ℝ)(pc:∀p s,0≤cap p s)(Q:J→SealR G)(C₁ C₂:J→Credit)
    (rate L M:Credit)(coins:Prices)(E:J→ℕ)(u b A q spatial width target:ℕ)(ζ constant:ℝ)(pos:0<ζ)
    (low:(target:ℝ)+1+((2*(E 0+E 1):ℕ):ℝ) ≤ ((2*A:ℕ):ℝ)*(3*ζ/4))
    (high:(target:ℝ)+1+((2*(E 0+E 1+max (E 0) (E 1)+(2*T+11+2*h)*(2*((Q 0).h+(Q 1).h)+1)):ℕ):ℝ) ≤
      ((q+1:ℕ):ℝ)-((2*(A+1):ℕ):ℝ)*(2*((Q 0).h+(Q 1).h)+1:ℕ)):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer Z h r) → (∃i,(ρ i).val=r) →
      let m:=date R simple r; let f:=reporter F books ρ; let K:=berth R A f
      ∀j≤f,∀(t z:ℝ)(B:J→ℝ),
      let bound:=constant*(1+r/R.family.S.a m)^spatial*(R.family.path.levels.clock.monitor j)^width
      |t⁻¹|≤bound → |z|≤bound → (∀s,|B s|≤bound) →
        ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ),(∀s,radiusH (φ s) 1 y≤z) →
        ∀N per,K≤N→∀p:J→Bool×Bool,
          due R Q C₁ C₂ rate L M coins k e u b f m m K q ζ B t z y (regulatorRun R.family N per K)
            E (cap p) φ ≤ (1+8^(q+1))*(thermal R f)^target:=by
  classical
  let U:=2*T+11+2*h
  let H₀:=2*((Q 0).h+(Q 1).h)+1
  have money:∀p:J→Bool×Bool, _ := fun p=>WilsonIndependentConditionedEarlierOpening.original
    (k:=k) (e:=e) F simple bliss slow d h books (cap p) (pc p) Q C₁ C₂ rate L M coins u b A q spatial width
    ζ constant (ε:=1) (by norm_num)
  have booked:=Filter.eventually_all.mpr money
  have window:=WilsonIndependentConditionedGramSpatialCourse.original F simple bliss slow D T h A 0 d
    (ε:=1) (by norm_num) books
  obtain ⟨floor,grant⟩:=eventually_atTop.mp (WilsonIndependentConditionedBankRulerPayment.original
    R simple slow A U q H₀ (E 0+E 1) (E 0+E 1+max (E 0) (E 1)) target 1 (3*ζ/4) 8
    (by positivity) (by norm_num) low high)
  filter_upwards [booked,window,(WilsonIndependentConditionedGramSpatialHost.late R simple).eventually_ge_atTop floor]
    with r paid found live
  intro ρ room center m f K j oj t z B bound clear box amps φ y radii N per top p
  have page:WilsonIndependentConditionedGramSpatialCourse.Page R r m f K A U 0 1:=(found ρ room center).1
  have fresh:=paid p ρ room center j oj t z B clear box amps
  have gauge:=WilsonOriginalPublicRelativeGramKineticMesh.original_gauge R simple f K N per page.higher.le top
  have fare:=grant f (live.trans page.before) r m 0 1 page _ _ _ fresh.1 (fresh.2 φ y radii) gauge
  unfold due
  dsimp only
  simpa only [H₀,paceT,inverse,Real.rpow_natCast] using fare

end YM.Integration.WilsonIndependentConditionedBankRulerTill
