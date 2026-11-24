import YM.Integration.WilsonIndependentConditionedActualSplit
import YM.Integration.WilsonOriginalTwoFlatPublicMixedSpan

/-! Pull the true pair's fee opening back to the ordered family of nominated radii on its one public course. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedActualOpening
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

theorem before [Nonempty I](simple:G.Simple)(bliss:Bliss F l Z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {D T:ℕ}(d:I→Fin (D+1))(h:ℕ){limit:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<limit})→Book F (l:=l) H Z D T s.val)
    {P:ℕ→Prop}(started:∀ᶠ f:ℕ in atTop,P f):
    ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<limit},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer Z h r) →
      (∃i,(ρ i).val=r) → P (reporter F books ρ):=by
  obtain ⟨f₀,all⟩:=eventually_atTop.mp started
  filter_upwards [WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books,
    (gt_mem_nhds (R.family.S.a_pos f₀)).filter_mono nhdsWithin_le_nhds] with r dates small ρ housed near
  have mesh:R.family.S.a (reporter F books ρ) ≤ r:=(dates ρ housed near).1
  exact all _ (R.family.S.strictAnti.le_iff_ge.mp (mesh.trans small.le))

theorem original (simple:G.Simple)(bliss:Bliss F l Z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {D T:ℕ}(d:I→Fin (D+1))(h:ℕ){limit:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<limit})→Book F (l:=l) H Z D T s.val)
    (pick:J→I)(M:I→ℝ)(c:J→ℝ)(mass:∀s,0 ≤ M (pick s))(coin:∀s,0 ≤ c s)
    (Q:J→SealR G)(C₁ C₂:J→Credit)(rate L M':Credit)(coins:Prices)(u b A q:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ)
    {ε:ℝ}(ep:0<ε):
    ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<limit},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer Z h r) →
      (∃i,(ρ i).val=r) →
      let f:=reporter F books ρ
      let K:=berth R A f
      let cap:=fun s=>M (pick s)*fixed R (d (pick s)).val*c s
      let U:=roof (wage (k:=k) (e:=e) R Q coins u b f f K ζ (fun _=>1) (fun _=>1) B t z)
      let cells:=fun s=>|field R (Q s) (C₁ s) (C₂ s) f f K q 1 1|
      homeLow q U (inverse R L M' f) cap ≤ (thermal R f)^(-ε) ∧
        ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ),(∀s,radiusH (φ s) 1 y ≤ z) →
          homeHigh q U cells cap |gram (e:=e) R Q rate f K q φ B y| ≤ (thermal R f)^(-ε):=by
  letI : Nonempty I:=⟨pick 0⟩
  exact before F simple bliss slow d h books (WilsonIndependentConditionedActualSplit.original
    (k:=k) (e:=e) R simple slow pick d M c mass coin Q C₁ C₂ rate L M' coins u b A q ζ B t z ep)

end YM.Integration.WilsonIndependentConditionedActualOpening
