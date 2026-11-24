import YM.Integration.WilsonIndependentMatchedCoverCarried

/-! A stable column with a funded normalized peer, or two stable columns
from one common fitted horizon, on the actual cover mesh. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoveredSeats
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}
    {H H':Hol G}{T:SectionData F}{p:h<D}{v:Rails h k u e}{E W K U L V:Credit}

def seat (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR)(i:ℕ):Era G ℝ:=
  word (a • X.springP i) φ (paceT X.ax.S X.m (X.m+i)) y o h

def Posted (R:Realm G (e+1) E)(l r m N n:ℕ)(P Q:ℕ→Era G ℝ):Prop:=
  cruises R.draws R.paid N (l+r) (m+n) m (agateV (P n) (Q n))=
    agateV (P 0) (Q 0)+∑i∈Finset.range n,cruises R.draws R.paid N (l+r) (m+i) m
      (JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1)))

theorem traced (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):
    (∀i≤X.i, Auth k (seat X a φ y o i)) ∧
    ∀i<X.i, verseI X.ax X.tx (X.m+i) X.N k (seat X a φ y o (i+1))=seat X a φ y o i := by
  constructor
  · intro i hi
    exact locale_val _ (placed h φ ((X.onward hi).μ a) _ _) _
  · intro i hi
    have c:=WilsonIndependentMatchedCoverCarried.carried X i hi a φ
      (paceT X.ax.S X.m (X.m+i+1)) y o (pace_pos ..)
    rw [pace_step] at c
    exact c

end YM.Integration.WilsonIndependentMatchedCoveredSeats
