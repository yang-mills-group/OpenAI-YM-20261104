import YM.Integration.WilsonIndependentFittedReportedFilm
import YM.Integration.WilsonIndependentFittedThermalProduct

/-! The stopped signed mixed row with a fitted scalar on the true normalized
position peer, including the subsequent change of clock to its actual stop. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedMixedReturn
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (printed seat traced wired)
open WilsonIndependentMatchedReportedProxy (sectionSeal passport)
open WilsonIndependentMatchedPivotSeat (axis film)
open WilsonIndependentFittedReportedFilm (weight funded)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonOlderFreshSoftSocketKinetic (reading)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

def planted (X:CutsP H T p v E W K U)(q:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR):Era G ℝ:=
  printed X.vesselsC (sectionSeal T p) φ q X.m X.N y o X.i
def word (X:CutsP H T p v E W K U)(stop:ℕ)(P Q:Era G ℝ)(r:ℕ)(x:Fin r→YForest G):Cost:=
  reading (cruises X.ax X.tx X.N (k+k) (X.m+X.i) stop (agateV P Q)).2 x

theorem paid (X:CutsP H T p v E W K U)(q:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR):
    Auth h (planted X q φ y o):=
  (wired X.vesselsC (sectionSeal T p) (passport X) φ q X.m X.N X.i X.ha
    (X.hc.trans X.hn) y o).1 X.i le_rfl

theorem active (X:CutsP H T p v E W K U)(s:ℕ)(before:s≤X.m)(c:Cost){P Q:Era G ℝ}
    (prior:Auth (k+k) P)(unit:Auth (k+k) Q)
    (born:∀n,P.1 n=affix (reel (relativeC X.ax X.tx X.N X.m X.i) c) (Q.1 n))
    {r:ℕ}(x:Fin r→YForest G):
    reading (cruises X.ax X.tx X.N (k+k) (X.m+X.i) s P).2 x=
      clock X.ax X.tx X.N X.m s c*reading (cruises X.ax X.tx X.N (k+k) (X.m+X.i) s Q).2 x:=by
  have top:=X.hc.trans X.hn
  have stop:=before.trans (Nat.le_add_right X.m X.i)
  have eqn:=WilsonOlderFreshSoftSocketHistory.original X.ax X.tx X.vesselsC.hG X.vesselsC.green
    X.N (k+k) (X.m+X.i) s stop top P Q _ prior unit born
  rw [eqn,WilsonOlderFreshSoftSocketKinetic.valued,←WilsonOlderFreshSoftSocketKinetic.combine
    X.ax X.tx X.N (X.m+X.i) X.m s before (Nat.le_add_right ..),
    WilsonIndependentFittedRelativeClock.restored X.ax X.tx X.vesselsC.hG X.vesselsC.green X.N X.m X.i top]

theorem multiplied (X:CutsP H T p v E W K U)(stop:ℕ)(before:stop≤X.m)(P:Era G ℝ)(prior:Auth k P)
    (c:Cost)(d:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR)(r:ℕ)(x:Fin r→YForest G):
    let Q:=planted X d φ y o
    let M:=planted X (weight c d) φ y o
    let τ:=clock X.ax X.tx X.N X.m stop c
    word X stop P M r x=τ*word X stop P Q r x ∧ word X stop M P r x=τ*word X stop Q P r x:=by
  intro Q M τ
  have high:Auth k M:=(paid X (weight c d) φ y o).tall v.hk
  have low:Auth k Q:=(paid X d φ y o).tall v.hk
  have filed:M=funded (reel (relativeC X.ax X.tx X.N X.m X.i) c) Q:=
    WilsonIndependentFittedReportedFilm.drawn X φ y o d c X.i
  constructor
  · apply active X stop before c (prior.manor high) (prior.manor low) _ x
    intro n
    rw [filed]
    exact WilsonIndependentFittedThermalProduct.right _ (P.1 n) (Q.1 n)
  · apply active X stop before c (high.manor prior) (low.manor prior) _ x
    intro n
    rw [filed]
    exact WilsonIndependentFittedThermalProduct.left _ (Q.1 n) (P.1 n)

theorem original (X:CutsP H T p v E W K U)(stop:ℕ)(before:stop≤X.m)(a:ℝ)(c:Cost)
    (j:Alma F)(q:ℕ)(φ ψ:Rarity D)(y:ℝ)(o:CellR)(r:ℕ)(x:Fin r→YForest G):
    let P:=seat X a φ y o X.i
    let Q:=film X j q ψ y o X.i
    let M:=planted X (weight c (axis j q)) ψ y o
    let τ:=clock X.ax X.tx X.N X.m stop c
    word X stop P M r x=τ*word X stop P Q r x ∧ word X stop M P r x=τ*word X stop Q P r x:=
  multiplied X stop before (seat X a φ y o X.i) ((traced X a φ y o).1 X.i le_rfl)
    c (axis j q) ψ y o r x

end YM.Integration.WilsonIndependentFittedMixedReturn
