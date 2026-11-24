import YM.Integration.WilsonSeparatedPrefixMovingNativeCut
import YM.Integration.WilsonSeparatedPrefixMovingUnjoined
import YM.Integration.WilsonSeparatedPrefixMovingNearReturn
import YM.Integration.WilsonSeparatedPrefixMovingOwnDate

/-! A first join after capture. The near source includes the old scalar
and is the complete propagated difference on its own nominated chart.
The reflected exterior enters as its literal own-date normalized column. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingLateLaw
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D a k k' e u extra:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {E W K U V V' L:Credit}

open WilsonSeparatedPrefixMovingPairSector (current)
open Finset

def near {v:Rails h k u e}(Y:CutsP H T p v E W K U)(φ:Rarity D)(y:ℝ)(o:CellR)(j:ℕ):Era G ℝ:=
  word ((paceT Y.ax.S Y.m Y.ceilC)^h • Y.springP j) φ (paceT Y.ax.S Y.m (Y.m+j)) y o h

def far {v:Rails h k u e}(Y:CutsP H T p v E W K U)(Q:SealR G)(ψ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(j:ℕ):Era G ℝ:=current Y.vesselsC Q ψ X Y.m (Y.m+j) Y.N y o

def whole {v:Rails h k u e}(Y:CutsP H T p v E W K U)(Q:SealR G)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(older j:ℕ):Era G ℝ:=cruises Y.ax Y.tx Y.N (k+Q.h) (Y.m+j) older
      (agateV (near Y φ y o j) (far Y Q ψ X y o j))

def birth {v:Rails h k u e}(Y:CutsP H T p v E W K U)(Q:SealR G)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(older j:ℕ):Era G ℝ:=cruises Y.ax Y.tx Y.N (k+Q.h) (Y.m+j) older
      (JoinGap Y.ax Y.tx (Y.m+j) Y.N k Q.h (near Y φ y o (j+1)) (far Y Q ψ X y o (j+1)))

theorem original {v:Rails h k u e}(Y:CutsP H T p v E W K U)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q W V)
    (φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)(o:CellR)(older:ℕ)(before:older ≤ Y.m):
    whole Y Q φ ψ X y o older Y.i=whole Y Q φ ψ X y o older 0+
      ∑j∈range Y.i,birth Y Q φ ψ X y o older j:=by
  have top:=Y.hc.trans Y.hn
  have cost (j:ℕ)(due:j ≤ Y.i):Auth k (near Y φ y o j):=by
    exact locale_val _ (placed h φ ((Y.onward due).μ _) _ _) _
  have peer (j:ℕ)(due:j ≤ Y.i):Auth Q.h (far Y Q ψ X y o j):=
    WilsonSeparatedPrefixMovingNativeCut.grades Y.vesselsC Q ticket ψ X o y Y.m (Y.m+j) Y.N
      (Y.ha.trans (Nat.le_add_right _ _)) (by omega)
  have stepNear (j:ℕ)(due:j<Y.i):
      verseI Y.ax Y.tx (Y.m+j) Y.N k (near Y φ y o (j+1))=near Y φ y o j:=by
    have edge:=WilsonIndependentMatchedCoverCarried.carried Y j due ((paceT Y.ax.S Y.m Y.ceilC)^h)
      φ (paceT Y.ax.S Y.m (Y.m+(j+1))) y o (pace_pos ..)
    rw [show Y.m+(j+1)=Y.m+j+1 by omega,pace_step] at edge
    exact edge
  have turn (j:ℕ)(due:j<Y.i):verseI Y.ax Y.tx (Y.m+j) Y.N Q.h (far Y Q ψ X y o (j+1))=far Y Q ψ X y o j:=
    WilsonSeparatedPrefixMovingNativeCut.step Y.vesselsC Q ticket ψ X o y Y.m (Y.m+j) Y.N Y.ha
      (Nat.le_add_right _ _) (by omega)
  simpa only [whole,birth,Nat.add_zero] using WilsonSeparatedPrefixMovingSignedChronology.split Y.vesselsC
    k Q.h older Y.m Y.N Y.i before top (near Y φ y o) (far Y Q ψ X y o) cost peer stepNear turn

end YM.Integration.WilsonSeparatedPrefixMovingLateLaw
