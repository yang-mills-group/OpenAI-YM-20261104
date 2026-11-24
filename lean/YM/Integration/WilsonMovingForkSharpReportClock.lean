import YM.Integration.WilsonMovingForkSharpRows
import YM.Integration.WilsonMovingForkSharpTested44

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpReportClock
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingLateLaw (whole far)
open WilsonIndependentMatchedFittedSeat (receiving dose)
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U V:Credit}

open WilsonMovingForkSharpProjected (amp)
open WilsonSeparatedPrefixMovingMomentCut (reported)

/-- Genuine transport of the complete independently reported output to the exterior home. -/
def atFar (Y:CutsP H T p v E W K U)(m:ℕ)(x:Verse F):Verse F:=
  ((paceT Y.ax.S m Y.m)^h)⁻¹ • street Y.ax Y.tx T p Y.N Y.m (m-Y.m) x

theorem homogeneous (A:Levels G)(Ñ:ChartRatio G)(N m j:ℕ)(x:ℝ)(b:Verse F):
    street A Ñ T p N m j (x • b)=x • street A Ñ T p N m j b:=by
  unfold street
  rw [show music (relativeF A Ñ N m j) (x • b)=x • music (relativeF A Ñ N m j) b from ?_,Matrix.mulVec_smul]
  funext i
  simp only [music,Pi.smul_apply]
  exact map_smul (PowerSeries.substAlgHom _) x _

theorem original (Y:CutsP H T p v E W K U)(m:ℕ)(span:Y.ceilC ≤ m)(cut:m ≤ Y.N)
    (x:Verse F)(observed:x=(paceT Y.ax.S m Y.ceilC)^h • steep Y.ax Y.tx T p Y.N Y.ceilC (m-Y.ceilC) Y.tileP):
    dose Y (amp Y)=atFar Y m x:=by
  have middle:Y.m+Y.i=Y.ceilC:=rfl
  have length:m-Y.m=Y.i+(m-Y.ceilC):=by omega
  have gate:Y.vesselsC.anchor ≤ Y.ceilC:=Y.ha.trans (Nat.le_add_right ..)
  have endDate:Y.ceilC+(m-Y.ceilC) ≤ Y.N:=by omega
  change street Y.ax Y.tx T p Y.N Y.m Y.i (amp Y • Y.tileP)=_
  rw [atFar,observed,homogeneous (T:=T) (p:=p),homogeneous (T:=T) (p:=p),smul_smul]
  rw [←WilsonMovingForkSharpRuler.ordinary Y m,length,←Street_plus,middle,Street_up Y.L.L _ gate endDate]
  rfl

end YM.Integration.WilsonMovingForkSharpReportClock
