import YM.Integration.WilsonMovingForkSharpRows
import YM.Integration.WilsonIndependentFittedPivotCash

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpCash
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

open WilsonMovingForkSharpProjected (amp incoming paired axisRow)
open WilsonIndependentFittedPivotCash (measured)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)

/-- A single numerical evaluation of the entire filed coefficient, with its true pair. -/
def stated (Y:CutsP H T p v E W K U)(Q:SealR G)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(older depth:ℕ)(g:ℝ){r:ℕ}(legs:Fin r→YForest G):ℂ:=
  measured depth g (reading (paired Y Q ψ X y o older k (incoming Y φ y o)).2 legs)-
    ∑j,measured depth g (clock Y.ax Y.tx Y.N Y.m older (dose Y (amp Y) j))*
      measured depth g (reading (axisRow Y Q φ ψ X y o older j).2 legs)

def annulus (Y:CutsP H T p v E W K U)(Q:SealR G)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(older depth:ℕ){r:ℕ}(legs:Fin r→YForest G):ℝ:=
  ∑j,belt depth (embed (clock Y.ax Y.tx Y.N Y.m older (dose Y (amp Y) j)))*
    belt depth (embed (reading (axisRow Y Q φ ψ X y o older j).2 legs))

theorem original (Y:CutsP H T p v E W K U)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q W V)
    (room:Q.h≤k)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)(o:CellR)(older:ℕ)(before:older≤Y.m)
    (depth:ℕ)(g:ℝ)(small:|g|≤1){r:ℕ}(legs:Fin r→YForest G):
    ‖stated Y Q φ ψ X y o older depth g legs-measured depth g
        (reading (whole Y Q φ ψ X y o older Y.i).2 legs)‖ ≤
      2*|g|^(depth+1)*annulus Y Q φ ψ X y o older depth legs:=by
  let d:=fun j=>clock Y.ax Y.tx Y.N Y.m older (dose Y (amp Y) j)
  let pair:=fun j=>reading (axisRow Y Q φ ψ X y o older j).2 legs
  let raw:=reading (paired Y Q ψ X y o older k (incoming Y φ y o)).2 legs
  let ev:=measured depth g
  have got:raw-∑j,d j*pair j=reading (whole Y Q φ ψ X y o older Y.i).2 legs:=
    WilsonMovingForkSharpProjected.original Y Q ticket room φ ψ X y o older before legs
  change ‖(ev raw-∑j,ev (d j)*ev (pair j))-ev _‖≤2*|g|^(depth+1)*∑j,belt depth (embed (d j))*belt depth (embed (pair j))
  rw [←got,map_sub,map_sum,sub_sub_sub_cancel_left,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  change ‖cash depth g (embed (d j*pair j))-cash depth g (embed (d j))*cash depth g (embed (pair j))‖≤_
  rw [map_mul,norm_sub_rev]
  have gap:=WilsonIndependentFittedNumericalProduct.signed depth small Finset.univ
    (![embed (d j),embed (pair j)]:Fin 2→PowerSeries ℂ)
  simpa [Fin.prod_univ_two] using gap

end YM.Integration.WilsonMovingForkSharpCash
