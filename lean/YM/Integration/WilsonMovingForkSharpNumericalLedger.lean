import YM.Integration.WilsonMovingForkSharpSpectralLedger
import YM.Integration.WilsonMovingForkSharpGrades
import YM.Integration.WilsonMovingForkSharpCash

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpNumericalLedger
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
def inputs (Y:CutsP H T p v C C C C)(x:Verse F)(m older:ℕ)(j:Alma F):PowerSeries ℝ:=
  clock Y.ax Y.tx Y.N Y.m older (atFar Y m x j)
def assembled (Y:CutsP H T p v C C C C)(Q:SealR G)(φ:Rarity D)(χ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(m older depth:ℕ)(x:Verse F)(g:ℝ)(w:Fin 0→YForest G)(S:𝓢(Euclid,ℂ)):ℂ:=
  ∑j,measured depth g (inputs Y x m older j)*measured depth g (film Y Q φ χ X y o older w S j)
def annulus (Y:CutsP H T p v C C C C)(Q:SealR G)(φ:Rarity D)(χ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(m older depth:ℕ)(x:Verse F)(w:Fin 0→YForest G)(S:𝓢(Euclid,ℂ)):ℝ:=
  ∑j,belt depth (embed (inputs Y x m older j))*belt depth (embed (film Y Q φ χ X y o older w S j))

theorem original (Y:CutsP H T p v C C C C)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q C C)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (X:Q.Rider)(y:ℝ)(o:CellR)(m older depth:ℕ)(ear:older ≤ Y.m)(x:Verse F)(w:Fin 0→YForest G)(S:𝓢(Euclid,ℂ))
    (stock:∀n:ℕ,Integrable fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖)(g:ℝ)(small:|g| ≤ 1)(raw:ℕ→ℝ):
    let written:=fun q=>(∫ξ:Euclid,WilsonMovingForkSharpAxisWave.tested Y Q φ χ X y o m older q x w S true ξ)
    ‖(measured depth g (PowerSeries.mk raw)-assembled Y Q φ χ X y o m older depth x g w S)-
      measured depth g (PowerSeries.mk (fun q=>raw q-written q))‖ ≤
      2*|g|^(depth+1)*annulus Y Q φ χ X y o m older depth x w S:=by
  intro written
  let d:=inputs Y x m older
  let pane:=film Y Q φ χ X y o older w S
  let ev:=measured depth g
  have got:PowerSeries.mk raw-∑j,d j*pane j=PowerSeries.mk (fun q=>raw q-written q):=by
    ext q
    simp only [map_sub,PowerSeries.coeff_mk]
    exact congrArg (fun z:ℝ=>raw q-z) (WilsonMovingForkSharpSpectralLedger.original Y Q ticket φ χ hφ hχ X y o m older q ear x w S stock).symm
  change ‖(ev (PowerSeries.mk raw)-∑j,ev (d j)*ev (pane j))-ev _‖ ≤
    2*|g|^(depth+1)*∑j,belt depth (embed (d j))*belt depth (embed (pane j))
  rw [←got,map_sub,map_sum,sub_sub_sub_cancel_left,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  change ‖cash depth g (embed (d j*pane j))-cash depth g (embed (d j))*cash depth g (embed (pane j))‖ ≤ _
  rw [map_mul,norm_sub_rev]
  have gap:=WilsonIndependentFittedNumericalProduct.signed depth small Finset.univ (![embed (d j),embed (pane j)]:Fin 2→PowerSeries ℂ)
  simpa [Fin.prod_univ_two] using gap

end YM.Integration.WilsonMovingForkSharpNumericalLedger
