import YM.Integration.WilsonMovingForkSharpAxisWindow

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpAxisCash
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
def mass {I:Type*}[Fintype I](c:I→PowerSeries ℝ)(q:ℕ):ℝ:=
  ∑i,∑j∈Finset.range (q+1),‖PowerSeries.coeff j (c i)‖

theorem weighted {I:Type*}[Fintype I](c x z:I→PowerSeries ℝ)(q:ℕ)(H':ℝ)
    (expense:∀a:I,∀j ≤ q,‖PowerSeries.coeff j (x a)-PowerSeries.coeff j (z a)‖ ≤ H'):
    ‖PowerSeries.coeff q (∑a,c a*x a)-PowerSeries.coeff q (∑a,c a*z a)‖ ≤ mass c q*H':=by
  classical
  rw [←map_sub,←Finset.sum_sub_distrib,map_sum]
  unfold mass
  rw [Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro l _
  rw [←mul_sub,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro i hi
  simp only [map_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (expense l _ (Nat.sub_le ..)) (norm_nonneg _)

def panel (Y:CutsP H T p v C C C C)(Q:SealR G)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(m older q:ℕ)(x:Verse F)(w:Fin 0→YForest G)(arm:Bool):ℝ:=
  PowerSeries.coeff q (∑l,clock Y.ax Y.tx Y.N Y.m older (atFar Y m x l)*
    reading (if arm then top Y Q φ ψ X y o older l else axisRow Y Q φ ψ X y o older l).2 w)

theorem original (p:h<D)(T:SectionData F)(Q:SealR G)(e u' target:ℕ):
    let toll:=Q.h+h+(u'+target+2)
    ∃C₁:Credit,∀{a u:ℕ}{v:Rails h k (u+a) e}(Y:CutsP H T p v C C C C),
      SpringD Y.vesselsC (h+Q.h) u' toll C → Dormitory Y.vesselsC (h+Q.h) u' C →
      PassportC H Y.vesselsC Q C C →
      ∀(m older:ℕ),Y.vesselsC.anchor ≤ older → older ≤ Y.m →
      ∀(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(o:CellR)(y gap r U V:ℝ),0<gap →
      Amplitude φ U → Amplitude ψ V → ClearDay φ ψ gap →
      φ.radius+|y|+1 ≤ r → ψ.radius+|y|+1 ≤ r → ∀(x:Verse F)(q:ℕ),q ≤ e → ∀w:Fin 0→YForest G,
        let amount:=mass (fun j=>clock Y.ax Y.tx Y.N Y.m older (atFar Y m x j)) q
        ‖panel Y Q φ ψ X y o m older q x w true-panel Y Q φ ψ X y o m older q x w false‖
          ≤ amount*(2*(wage (h:=h) Q X e u' target r gap U V*(paceT Y.ax.S Y.m Y.ceilC)^target)*
            C₁.buy (epoch Y.vesselsC older Y.ceilC)):=by
  intro toll
  obtain ⟨C₁,pay⟩:=WilsonMovingForkSharpAxisWindow.original (H:=H) (k:=k) p T Q e u' target
  refine ⟨C₁,?_⟩
  intro a u v Y spring dorm ticket m older gate age φ ψ X o y gap r U V pos inc far clear nr fr x q bound w amount
  unfold panel
  simp only [Bool.false_eq_true,if_false,if_true]
  apply weighted
  intro j l hl
  simpa only [WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk] using pay Y spring dorm ticket older gate age φ ψ X o y gap r U V
    pos inc far clear nr fr j l (hl.trans bound) w
end YM.Integration.WilsonMovingForkSharpAxisCash
