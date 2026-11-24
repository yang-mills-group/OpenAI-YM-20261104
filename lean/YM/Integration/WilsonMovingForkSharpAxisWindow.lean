import YM.Integration.WilsonMovingForkSharpProfile
import YM.Integration.WilsonMovingForkSharpFineGram

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpAxisWindow
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
def top (Y:CutsP H T p v C C C C)(Q:SealR G)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)
    (o:CellR)(older:ℕ)(j:Alma F):Era G ℝ:=
  pair Y.vesselsC (sectionSeal T p) Q φ ψ (axis j 0) X o y Y.m Y.N older Y.N

theorem one (j:Alma F)(e:ℕ):fee (sectionSeal T p) e (axis j 0)=1:=by
  classical
  change (∑b:Alma F,∑i:Fin (e+1),‖PowerSeries.coeff i.val (axis j 0 b)‖)=1
  have cell (b:Alma F)(i:Fin (e+1)):‖PowerSeries.coeff i.val (axis j 0 b)‖=
      if b=j then if i.val=0 then (1:ℝ) else 0 else 0:=by
    by_cases bj:b=j <;> by_cases q:i.val=0 <;> simp [axis,PowerSeries.coeff_mk,bj,q]
  simp_rw [cell]
  have zero (i:Fin (e+1)):i.val=0 ↔ i=0:=⟨fun ha=>Fin.ext ha,fun ha=>ha ▸ rfl⟩
  simp [zero]


def wage (Q:SealR G)(X:Q.Rider)(e u target:ℕ)(r gap U V:ℝ):ℝ:=
  let toll:=Q.h+h+(u+target+2)
  let fare:=fun b L=>(5*r)^4*(9^(u+toll)*(b*L))
  (16*r)^u*(gap⁻¹)^toll*fare U 1*(fare V (fee Q e X))

theorem original (p:h<D)(T:SectionData F)(Q:SealR G)(e u' target:ℕ):
    let toll:=Q.h+h+(u'+target+2)
    ∃C₁:Credit,∀{a u:ℕ}{v:Rails h k (u+a) e}(Y:CutsP H T p v C C C C),
      SpringD Y.vesselsC (h+Q.h) u' toll C → Dormitory Y.vesselsC (h+Q.h) u' C →
      PassportC H Y.vesselsC Q C C →
      ∀(older:ℕ),Y.vesselsC.anchor ≤ older → older ≤ Y.m →
      ∀(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(o:CellR)(y gap r U V:ℝ),0<gap →
      Amplitude φ U → Amplitude ψ V → ClearDay φ ψ gap →
      φ.radius+|y|+1 ≤ r → ψ.radius+|y|+1 ≤ r →
      ∀(j:Alma F)(q:ℕ),q ≤ e → ∀w:Fin 0→YForest G,
        ‖(top Y Q φ ψ X y o older j).2 q 0 w-(axisRow Y Q φ ψ X y o older j).2 q 0 w‖
          ≤ 2*(wage (h:=h) Q X e u' target r gap U V*(paceT Y.ax.S Y.m Y.ceilC)^target)*
            C₁.buy (epoch Y.vesselsC older Y.ceilC):=by
  intro toll
  obtain ⟨C₁,sold⟩:=WilsonMovingForkSharpFineGram.original H (sectionSeal T p) Q (h+Q.h) e u' target C C C C
  refine ⟨C₁,?_⟩
  intro a u v Y spring endP outside older gate ear φ ψ X o y gap r U V pos am bm clear left right j q hq w
  have price:=sold Y.vesselsC spring endP (passport Y) outside older Y.m Y.ceilC Y.N gate ear
    (Nat.le_add_right ..) (Y.hc.trans Y.hn) le_rfl φ ψ (axis j 0) X o y gap r U V pos am bm clear left right q hq w
  change ‖(top Y Q φ ψ X y o older j).2 q 0 w-(axisRow Y Q φ ψ X y o older j).2 q 0 w‖ ≤ _ at price
  exact price.trans_eq (by simp [invoice,WilsonSeparatedPrefixMovingWages.coupon,wage,one,show (sectionSeal T p).h=h from rfl])
end YM.Integration.WilsonMovingForkSharpAxisWindow
