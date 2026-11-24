import YM.Integration.WilsonIndependentMatchedCoverPeer

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

/-- A true filed normalized peer enters before the first covariance. -/
theorem mixed (X:CutsP H T p v E W K U)(Q:SealR G)(peer:PassportC H' X.vesselsC Q L V)
    (a:ℝ)(φ:Rarity D)(ψ:Rarity Q.D)(d:Q.Rider)(y:ℝ)(o:CellR):
    Posted X.vesselsC k Q.h X.m X.N X.i (seat X a φ y o) (printed X.vesselsC Q ψ d X.m X.N y o) ∧
    Posted X.vesselsC Q.h k X.m X.N X.i (printed X.vesselsC Q ψ d X.m X.N y o) (seat X a φ y o):=by
  have bound:X.m+X.i ≤ X.N:=X.hc.trans X.hn
  let P:=seat X a φ y o
  let Q':=printed X.vesselsC Q ψ d X.m X.N y o
  obtain ⟨auth,advance⟩:=traced X a φ y o
  obtain ⟨paid,story⟩:=wired X.vesselsC Q peer ψ d X.m X.N X.i X.ha bound y o
  constructor
  · exact WilsonIndependentMatchedCoverCarried.original X.vesselsC k Q.h X.m X.N X.i bound P Q'
      auth paid advance story
  · exact WilsonIndependentMatchedCoverCarried.original X.vesselsC Q.h k X.m X.N X.i bound Q' P
      paid auth story advance

end YM.Integration.WilsonIndependentMatchedCoveredSeats
