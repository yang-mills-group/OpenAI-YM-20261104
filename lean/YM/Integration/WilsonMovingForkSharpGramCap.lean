import YM.Integration.WilsonMovingForkSharpGramOwnDate
import YM.Integration.WilsonMovingForkSharpAxisWindow

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramCap
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
open WilsonMovingForkSharpAxisWindow (top wage one)
open WilsonMovingForkSharpGramOwnDate (tariff)
def cap (H:Hol G)(A B:SealR G)(e u target:ℕ)(C₁ C₂:Credit)(X:B.Rider)(Z r gap:ℝ):ℝ:=
  2*wage (h:=A.h) B X e u target r gap 1 1*C₁.buy Z+
    C₂.buy Z*(coinMat (A.h+B.h) e*(hardCash e u C C C H A).buy (max Z r)*
      ((hardCash e u C C C H B).buy (max Z r)*fee B e X))
theorem original (p:h<D)(T:SectionData F)(Q:SealR G)(e u' target:ℕ):
    let toll:=Q.h+h+(u'+target+2)
    ∃ C₁ C₂:Credit,∀{a u:ℕ}{v:Rails h k (u+a) e}(Y:CutsP H T p v C C C C),
      SpringD Y.vesselsC (h+Q.h) u' toll C → Dormitory Y.vesselsC (h+Q.h) u' C →
      PassportC H Y.vesselsC Q C C → ∀older:ℕ,Y.vesselsC.anchor ≤ older → older ≤ Y.m →
      ∀(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(o:CellR)(y gap r U V:ℝ),0<gap →
      Amplitude φ U → Amplitude ψ V → ClearDay φ ψ gap →
      φ.radius+|y|+1 ≤ r → ψ.radius+|y|+1 ≤ r →
      ∀(j:Alma F)(q:ℕ),q ≤ e → ∀w:Fin 0→YForest G,
        ‖(top Y Q φ ψ X y o older j).2 q 0 w‖ ≤
          cap H (sectionSeal T p) Q e u' target C₁ C₂ X (epoch Y.vesselsC older Y.m) r gap*(U*V):=by
  intro toll
  obtain ⟨C₁,new⟩:=WilsonMovingForkSharpFineGram.original H (sectionSeal T p) Q (h+Q.h) e u' target C C C C
  obtain ⟨C₂,old⟩:=WilsonMovingForkSharpGramOwnDate.original H (sectionSeal T p) Q e u' C C C C
  refine ⟨C₁,C₂,?_⟩
  intro a u v Y spring dorm outer older gate ear φ ψ X o y gap r U V pos am bm clear left right j q hq w
  let Z:=epoch Y.vesselsC older Y.m
  have floor:Y.m ≤ Y.N:=(Nat.le_add_right ..).trans (Y.hc.trans Y.hn)
  let M:ℝ:=(top Y Q φ ψ X y o older j).2 q 0 w
  let oldM:ℝ:=(pair Y.vesselsC (sectionSeal T p) Q φ ψ (axis j 0) X o y Y.m Y.m older Y.N).2 q 0 w
  have fine:=new Y.vesselsC spring dorm (passport Y) outer older Y.m Y.m Y.N gate ear le_rfl floor
    le_rfl φ ψ (axis j 0) X o y gap r U V pos am bm clear left right q hq w
  have filed:‖M-oldM‖ ≤ 2*wage (h:=h) Q X e u' target r gap U V*C₁.buy Z:=by
    exact fine.trans_eq (by simp [invoice,WilsonSeparatedPrefixMovingWages.coupon,wage,one,
      show (sectionSeal T p).h=h from rfl,pace_self,Z])
  have raw:=old Y.vesselsC (passport Y) outer dorm older Y.m Y.N gate ear floor φ ψ (axis j 0) X y r U V o
    (by linarith [φ.markG]) (by linarith [abs_nonneg y]) (by linarith [abs_nonneg y]) am bm q hq w
  have bill:=add_le_add filed raw
  calc
    ‖M‖=‖(M-oldM)+oldM‖:=by rw [sub_add_cancel]
    _ ≤ ‖M-oldM‖+‖oldM‖:=norm_add_le _ _
    _ ≤ _:=bill.trans_eq (by
      simp only [cap,tariff,one,show (sectionSeal T p).h=h from rfl]
      unfold wage
      ring)
end YM.Integration.WilsonMovingForkSharpGramCap
