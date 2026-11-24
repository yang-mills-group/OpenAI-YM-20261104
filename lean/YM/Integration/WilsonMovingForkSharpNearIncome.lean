import YM.Integration.WilsonMovingForkSharpExteriorIncome
import YM.Integration.WilsonMovingForkSharpPortfolioAnnulus
import YM.Integration.WilsonIndependentSpoutMasterCoordinates
import YM.Integration.WilsonSeparatedPrefixMovingPinnedPhysical
import YM.Integration.WilsonMovingForkSharpNumericalLedger
import YM.Integration.WilsonMovingForkSharpThermalSplit

noncomputable section
namespace YM.Integration.WilsonMovingForkSharpNearIncome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named)
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{h D k n height seats:ℕ}{H:Hol G}{F:Labels.Frame G h}{T:SectionData F}{p:h<D}

open MeasureTheory
open scoped SchwartzMap ContDiff
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointExpansion (coefficient angle)
open WilsonSeparatedPrefixMovingJointIntegral (signedRow)
open WilsonSeparatedPrefixMovingJointRows (bill)
open WilsonSeparatedPrefixMovingJointAddress (move)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonMovingForkSharpMaster (Paid)
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingTested44 (inner ranks)
open WilsonSeparatedPrefixMovingRelativeMaster (Landed)
open WilsonCoeffUV.Mer.Patrol (BayV)
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (old count)
open RegulatorIR RegulatorIR.Ledger
variable {D' j extra:ℕ}
open WilsonMovingForkSharpUniform (Earned)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
open WilsonSeparatedPrefixMovingPinnedPupil (Clear frontPrice)
open WilsonSeparatedPrefixMovingPinnedRaw (raw)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonMovingForkSharpBudget (allowance)
open WilsonMovingForkSharpAxisWave (tested)
open WilsonSeparatedPrefixMovingPinned44 (Tariff)
open WilsonSeparatedPrefixMovingPinnedRuler (tab)

open WilsonMovingForkSharpNumericalLedger (inputs assembled annulus)
open WilsonMovingForkSharpGramLedger (film)
open WilsonIndependentFittedPivotCash (measured)
open WilsonSeparatedPrefixMovingJointSpectrum (transformed)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonMovingForkSharpAxisWindow (wage)
open WilsonMovingForkSharpGramCap (cap)
open WilsonMovingForkSharpGramUniform (fare)
open WilsonMovingForkSharpPortfolioAnnulus (limits)
open WilsonMovingForkSharpExteriorIncome (axis_paid nonnegative)
def center (arms:Fin (n+1)→SealR G)(j:(s:Fin (n+1))→Alma (arms s).F):Herit arms:=
  fun s=>axis (arms s) (j s)
def charge (arms:Fin (n+1)→SealR G)(X:Herit arms)(q:ℕ):ℝ:=
  ∏s,fee (arms s) q (X s)

theorem nonneg (arms:Fin (n+1)→SealR G)(X:Herit arms)(q:ℕ):0 ≤ charge arms X q:=
  Finset.prod_nonneg (fun s _=>nonnegative (arms s) q (X s))

theorem wallet (arms:Fin (n+1)→SealR G)(X:Herit arms)(q:ℕ)(B:Fin (n+1)→ℝ):
    (∏s,B s*fee (arms s) q (X s))=charge arms X q*(∏s,B s):=by
  rw [Finset.prod_mul_distrib]
  exact mul_comm _ _

theorem captured (arms:Fin (n+1)→SealR G)(X:Herit arms)(q:ℕ)(B:Fin (n+1)→ℝ)
    (j:(s:Fin (n+1))→Alma (arms s).F)(capt:Credit)(room:ℝ):
    max 0 (capt.buy room*∏s,B s*fee (arms s) q (X s))=
      charge arms X q*max 0 (capt.buy room*∏s,B s*fee (arms s) q (center arms j s)):=by
  simp only [center,axis_paid,mul_one,wallet]
  rw [show capt.buy room*(charge arms X q*∏s,B s)=charge arms X q*(capt.buy room*∏s,B s) by ring,
      mul_max_of_nonneg _ _ (nonneg arms X q),mul_zero]

theorem front (R:Realm G (e+1) C)(arms:Fin (n+1)→SealR G)(Q:SealR G)(X:Herit arms)
    (j:(s:Fin (n+1))→Alma (arms s).F)(Z:Q.Rider)(first shape chron middle:Credit)
    (target older t b m:ℕ)(r nearGap farGap DF:ℝ)(B:Fin (n+1)→ℝ):
    frontPrice R arms Q X Z first shape chron middle target older t b m r nearGap farGap DF B=
      charge arms X e*frontPrice R arms Q (center arms j) Z first shape chron middle target older t b m r nearGap farGap DF B:=by
  have port (u:ℕ):(∏s,coupon (arms s) (X s) e u r (B s))=
      charge arms X e*∏s,coupon (arms s) (center arms j s) e u r (B s):=by
    unfold charge
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro s _
    simp only [WilsonSeparatedPrefixMovingWages.coupon,center,axis_paid]
    ring
  simp only [WilsonSeparatedPrefixMovingPinnedPupil.frontPrice,WilsonSeparatedPrefixMovingUnformedSector.invoice,
    WilsonIndependentMovingRosterInvoice.charge,WilsonIndependentMovingRosterBirth.charge,port,
    center,axis_paid,mul_one,wallet]
  ring
end YM.Integration.WilsonMovingForkSharpNearIncome
