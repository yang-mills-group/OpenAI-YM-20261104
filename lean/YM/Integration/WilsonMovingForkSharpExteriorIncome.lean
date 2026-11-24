import YM.Integration.WilsonMovingForkSharpPortfolioAnnulus
import YM.Integration.WilsonIndependentSpoutMasterCoordinates
import YM.Integration.WilsonSeparatedPrefixMovingPinnedPhysical
import YM.Integration.WilsonMovingForkSharpNumericalLedger
import YM.Integration.WilsonMovingForkSharpThermalSplit

noncomputable section
namespace YM.Integration.WilsonMovingForkSharpExteriorIncome
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
theorem axis_paid (Q:SealR G)(q:ℕ)(j:Alma Q.F):fee Q q (axis Q j)=1:=by
  classical
  have row (i:Alma Q.F):(∑k:Fin (q+1),‖PowerSeries.coeff k.val (axis Q j i)‖)=if i=j then 1 else 0:=by
    by_cases same:i=j
    · simp [axis,same,Fin.sum_univ_succ,PowerSeries.coeff_one]
    · simp [axis,same]
  unfold WilsonSeparatedPrefixMovingOwnDate.fee
  simp only [row]
  simp
theorem nonnegative (Q:SealR G)(q:ℕ)(X:Q.Rider):0 ≤ fee Q q X:=by
  unfold WilsonSeparatedPrefixMovingOwnDate.fee
  positivity

theorem front (R:Realm G (e+1) C)(arms:Fin (n+1)→SealR G)(Q:SealR G)(X:Herit arms)(Z:Q.Rider)(j:Alma Q.F)
    (first shape chron middle:Credit)(target older t b m:ℕ)(r nearGap farGap DF:ℝ)(B:Fin (n+1)→ℝ):
    frontPrice R arms Q X Z first shape chron middle target older t b m r nearGap farGap DF B=
      fee Q e Z*frontPrice R arms Q X (axis Q j) first shape chron middle target older t b m r nearGap farGap DF B:=by
  simp only [WilsonSeparatedPrefixMovingPinnedPupil.frontPrice,WilsonSeparatedPrefixMovingUnformedSector.invoice,
    WilsonIndependentMovingRosterInvoice.charge,WilsonSeparatedPrefixMovingWages.coupon,axis_paid]
  ring

theorem held (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)(φ:Rarity D)(χ:Rarity Q.D)(Z:Q.Rider)(j:Alma Q.F)
    (y gap r:ℝ)(older:ℕ):
    bill Y Q C₀ C₁ C₂ φ χ Z y gap r older=fee Q e Z*bill Y Q C₀ C₁ C₂ φ χ (axis Q j) y gap r older:=by
  simp only [WilsonSeparatedPrefixMovingJointRows.bill,WilsonSeparatedPrefixMovingWages.coupon,axis_paid]
  ring

theorem axisWage (h:ℕ)(Q:SealR G)(Z:Q.Rider)(j:Alma Q.F)(e u target:ℕ)(r gap U V:ℝ):
    wage (h:=h) Q Z e u target r gap U V=fee Q e Z*wage (h:=h) Q (axis Q j) e u target r gap U V:=by
  simp only [WilsonMovingForkSharpAxisWindow.wage,axis_paid]
  ring

theorem stable (Y:CutsP H T p v C C C C)(Q:SealR G)(Z:Q.Rider)(j:Alma Q.F)(ledger pay thermal:Credit)
    (older u':ℕ)(r gap:ℝ):
    allowance Y Q Z ledger pay thermal older u' r gap=fee Q e Z*allowance Y Q (axis Q j) ledger pay thermal older u' r gap:=by
  unfold WilsonMovingForkSharpBudget.allowance
  rw [axisWage h Q Z j,abs_mul,abs_of_nonneg (nonnegative Q e Z)]
  ring

theorem gramCap (H:Hol G)(A B:SealR G)(e u target:ℕ)(C₁ C₂:Credit)(X:B.Rider)(j:Alma B.F)(Z r gap:ℝ):
    cap H A B e u target C₁ C₂ X Z r gap=fee B e X*cap H A B e u target C₁ C₂ (axis B j) Z r gap:=by
  simp only [WilsonMovingForkSharpGramCap.cap,WilsonMovingForkSharpAxisWindow.wage,axis_paid]
  ring
theorem thermal (Y:CutsP H T p v C C C C)(Q:SealR G)(q u' target:ℕ)(C₁ C₂ pay τ:Credit)(φ:Rarity D)(χ:Rarity Q.D)
    (hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)(X:Q.Rider)(j:Alma Q.F)(older depth:ℕ)(r gap:ℝ)(S:𝓢(Euclid,ℂ)):
    limits Y Q q u' target C₁ C₂ pay τ φ χ hφ hχ X older depth r gap S=
      fee Q q X*limits Y Q q u' target C₁ C₂ pay τ φ χ hφ hχ (axis Q j) older depth r gap S:=by
  unfold WilsonMovingForkSharpPortfolioAnnulus.limits WilsonMovingForkSharpGramUniform.fare
  rw [gramCap H _ Q q u' target C₁ C₂ X j,abs_mul,abs_of_nonneg (nonnegative Q q X)]
  ring
theorem ruler (m price a b:ℝ)(positive:0≤price):tab m (price*a) (price*b)=price*tab m a b:=by
  simp only [WilsonSeparatedPrefixMovingPinnedRuler.tab,abs_mul,abs_of_nonneg positive]
  ring
end YM.Integration.WilsonMovingForkSharpExteriorIncome
