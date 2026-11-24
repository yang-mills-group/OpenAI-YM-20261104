import YM.Integration.WilsonMovingForkSharpNumericalLedger
import YM.Integration.WilsonMovingForkSharpGramUniform
import YM.Integration.WilsonMovingForkSharpCoordinate

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpPortfolioAnnulus
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


open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open WilsonMovingForkSharpMaster (Paid)
open scoped ContDiff
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingJointRows (bill page)
open WilsonMovingForkSharpIncome (gain)
open MeasureTheory
open scoped SchwartzMap
open WilsonSeparatedPrefixMovingJointExpansion (coefficient)
open WilsonSeparatedPrefixMovingJointIntegral (signedRow multiplier growth)
open WilsonMovingForkSharpProjected (amp incoming paired axisRow)
open WilsonMovingForkSharpReportClock (atFar)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentMatchedFittedSeat (dose)

open WilsonIndependentMatchedReportedProxy (sectionSeal passport)
open WilsonIndependentMatchedPivotSeat (axis)
open WilsonMovingForkSharpGramBirth (pair)
open WilsonSeparatedPrefixMovingUnformedSector (invoice)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonMovingForkSharpAxisWindow (top wage)
open WilsonMovingForkSharpAxisCash (panel)
open WilsonMovingForkSharpGramLedger (page film)
open WilsonMovingForkSharpAxisWave (tested)
open WilsonIndependentFittedPivotCash (measured)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonMovingForkSharpNumericalLedger (inputs annulus)
open WilsonMovingForkSharpGramUniform (fare)
open WilsonMovingForkSharpAxisCash (mass)
private theorem belt_embed (q:ℕ)(f:PowerSeries ℝ):belt q (embed f)=∑j∈Finset.range (q+1),‖PowerSeries.coeff j f‖:=by
  simp [WilsonPhysicalMarkedDefect.RawProduct.belt,embed,PowerSeries.coeff_map]
private theorem ledger {I:Type*}[Fintype I](d a:I→PowerSeries ℝ)(q:ℕ)(b:ℝ)
    (seen:∀i j,j≤q → ‖PowerSeries.coeff j (a i)‖ ≤ b):
    ∑i,belt q (embed (d i))*belt q (embed (a i)) ≤ mass d q*((q+1:ℕ)*b):=by
  classical
  rw [mass,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [belt_embed,belt_embed]
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  calc _ ≤ ∑_j∈Finset.range (q+1),b:=Finset.sum_le_sum fun j hj=>seen i j (by simpa using hj)
       _=_:=by simp
def limits (Y:CutsP H T p v C C C C)(Q:SealR G)(e u' target:ℕ)(C₁ C₂ pay thermal:Credit)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (X:Q.Rider)(older depth:ℕ)(r gap:ℝ)(S:𝓢(Euclid,ℂ)):ℝ:=
  let Z:=epoch Y.vesselsC older Y.ceilC
  let W:=fare H (sectionSeal T p) Q e u' target C₁ C₂ X (epoch Y.vesselsC older Y.m) r gap φ χ hφ hχ S
  ((Fintype.card (Alma F):ℝ)*(depth+1:ℕ)*(thermal.buy Z*(pay.buy Z*Y.fuel)))*((depth+1:ℕ)*W)
theorem original (p:h<D)(T:SectionData F)(v:Rails h k (u+a) e)(Q:SealR G)(u' target:ℕ):
    let toll:=Q.h+h+(u'+target+2)
    ∃C₁ C₂ pay thermal:Credit,∀Y:CutsP H T p v C C C C,
      SpringD Y.vesselsC (h+Q.h) u' toll C → Dormitory Y.vesselsC (h+Q.h) u' C → PassportC H Y.vesselsC Q C C →
      ∀m older:ℕ,Y.vesselsC.anchor ≤ older → older ≤ Y.m → Y.ceilC ≤ m → m ≤ Y.N →
      ∀(φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
        (X:Q.Rider)(o:CellR)(y gap r:ℝ),0<gap → ClearDay φ χ gap → φ.radius+|y|+1 ≤ r → χ.radius+|y|+1 ≤ r →
      ∀(S:𝓢(Euclid,ℂ)),(∀n:ℕ,Integrable fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖) →
      ∀(x:Verse F),x=(paceT Y.ax.S m Y.ceilC)^h • steep Y.ax Y.tx T p Y.N Y.ceilC (m-Y.ceilC) Y.tileP →
      ∀ depth ≤ e,∀ w:Fin 0→YForest G,
        annulus Y Q φ χ X y o m older depth x w S ≤ limits Y Q e u' target C₁ C₂ pay thermal φ χ hφ hχ X older depth r gap S:=by
  intro toll
  obtain ⟨C₁,C₂,prepaid⟩:=WilsonMovingForkSharpGramUniform.original (H:=H) (k:=k) p T Q e u' target
  obtain ⟨pay,thermal,charged⟩:=WilsonMovingForkSharpCoordinate.original (H:=H) p T v
  refine ⟨C₁,C₂,pay,thermal,?_⟩
  intro Y spring dorm ticket m older live ear past upper φ χ hφ hχ X o y gap r pos clear nr fr S stock x filed depth hdepth w
  let W:=fare H (sectionSeal T p) Q e u' target C₁ C₂ X (epoch Y.vesselsC older Y.m) r gap φ χ hφ hχ S
  have each:=prepaid Y spring dorm ticket older live ear φ χ hφ hχ X o y gap r pos clear nr fr S stock
  have hW:0≤W:=by
    apply mul_nonneg (mul_nonneg (abs_nonneg _) (WilsonSeparatedPrefixMovingSpectralSalary.positive ..))
    apply integral_nonneg
    intro ξ
    positivity
  have ports:=ledger (inputs Y x m older) (film Y Q φ χ X y o older w S) depth W
    (fun j i hi=>each j i (hi.trans hdepth) w)
  exact ports.trans (mul_le_mul_of_nonneg_right (charged Y m older live ear past upper x filed depth hdepth)
    (mul_nonneg (Nat.cast_nonneg _) hW))
end YM.Integration.WilsonMovingForkSharpPortfolioAnnulus
