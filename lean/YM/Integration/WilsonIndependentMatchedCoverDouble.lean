import YM.Integration.WilsonIndependentMatchedCoveredSeats

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

/-- The signed double complement on the same real school dates. -/
theorem joined (X Y:CutsP H T p v E W K U)(school:Y.L=X.L)
    (home:Y.m=X.m)(ceiling:Y.N=X.N)(steps:Y.i=X.i)
    (a b:ℝ)(φ ψ:Rarity D)(y:ℝ)(o:CellR):
    Posted X.vesselsC k k X.m X.N X.i (seat X a φ y o) (seat Y b ψ y o):=by
  obtain ⟨px,sx⟩:=traced X a φ y o
  obtain ⟨py,sy⟩:=traced Y b ψ y o
  have paths:Y.ax=X.ax:=congrArg (fun L:Torch H T p v E W K=>L.L.V.draws) school
  have clock:Y.tx=X.tx:=congrArg (fun L:Torch H T p v E W K=>L.L.V.paid) school
  rw [steps] at py sy
  rw [paths,clock,home,ceiling] at sy
  exact WilsonIndependentMatchedCoverCarried.original X.vesselsC _ _ _ _ _ (X.hc.trans X.hn)
    _ _ px py sx sy

end YM.Integration.WilsonIndependentMatchedCoveredSeats
