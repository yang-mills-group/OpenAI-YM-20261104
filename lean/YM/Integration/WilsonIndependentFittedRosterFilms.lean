import YM.Integration.WilsonIndependentFittedPivotRoster
import YM.Integration.WilsonIndependentMatchedRosterSlots

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedRosterFilms
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedReportedFilm (funded weight)
open WilsonIndependentFittedMixedReturn (planted)
open WilsonIndependentMatchedPivotSeat (axis film)
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedRosterSlots (entry degree)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

def Vote (F:Labels.Frame G h):Bool→Type
  | true=>Unit
  | false=>Alma F
instance (b:Bool):Fintype (Vote F b):=by cases b <;> unfold Vote <;> infer_instance

def factor (d:Verse F):(b:Bool)→Vote F b→ Cost
  | true,_=>1
  | false,j=>d j

def piece (weighted:Bool)(X:CutsP H T p v E W K U)(a:ℝ)(d:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR):
    (flag:Bool)→Vote F flag→Era G ℝ
  | true,_=>seat X a φ y o X.i
  | false,j=>if weighted then planted X (weight (d j) (axis j 0)) φ y o else film X j 0 φ y o X.i

theorem entire (X:CutsP H T p v E W K U)(a:ℝ)(d:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR)(flag:Bool):
    entry flag X a d φ y o X.i=∑j,piece true X a d φ y o flag j:=by
  cases flag
  · exact WilsonIndependentFittedPivotRoster.sources X d φ y o
  · change seat X a φ y o X.i=∑_j:Unit,seat X a φ y o X.i
    simp

theorem authenticated (X:CutsP H T p v E W K U)(a:ℝ)(d:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR)
    (weighted flag:Bool)(j:Vote F flag):Auth (degree flag k h) (piece weighted X a d φ y o flag j):=by
  cases flag with
  | true=>exact (WilsonIndependentMatchedCoveredSeats.traced X a φ y o).1 X.i le_rfl
  | false=>cases weighted
           · exact WilsonIndependentFittedMixedReturn.paid X (axis j 0) φ y o
           · exact WilsonIndependentFittedMixedReturn.paid X (weight (d j) (axis j 0)) φ y o

theorem scaled (X:CutsP H T p v E W K U)(a:ℝ)(d:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR)
    (flag:Bool)(j:Vote F flag):
    piece true X a d φ y o flag j=funded (reel (relativeC X.ax X.tx X.N X.m X.i) (factor d flag j))
      (piece false X a d φ y o flag j):=by
  cases flag
  · exact WilsonIndependentFittedReportedFilm.original X φ y o j 0 (d j) X.i
  · simp only [piece,factor,map_one,funded,affix_plain]

end YM.Integration.WilsonIndependentFittedRosterFilms
