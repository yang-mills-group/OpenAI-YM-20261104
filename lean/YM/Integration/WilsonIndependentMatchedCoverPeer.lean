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

def printed (R:Realm G (e+1) E)(Q:SealR G)(φ:Rarity Q.D)(d:Q.Rider)(m N:ℕ)(y:ℝ)(o:CellR)(i:ℕ):Era G ℝ:=
  locale o (Q.spins R.draws R.paid φ m (m+i) N y d)

/-- The normalized fitted peer's own true printed path, at each named date. -/
theorem wired (R:Realm G (e+1) E)(Q:SealR G)(peer:PassportC H' R Q L V)
    (φ:Rarity Q.D)(d:Q.Rider)(m N n:ℕ)(home:R.anchor ≤ m)(bound:m+n ≤ N)(y:ℝ)(o:CellR):
    (∀i ≤ n, Auth Q.h (printed R Q φ d m N y o i)) ∧
    (∀i<n,verseI R.draws R.paid (m+i) N Q.h (printed R Q φ d m N y o (i+1))=
      printed R Q φ d m N y o i):=by
  constructor
  · intro i hi
    exact locale_val _ (passportHead (R:=R) (m:=m) (i:=m+i) (N:=N) peer φ d y
      (home.trans (Nat.le_add_right m i)) ((Nat.add_le_add_left hi m).trans bound)) o
  · intro i hi
    exact passportCarry (R:=R) (m:=m) (i:=m+i) (N:=N) (y:=y) peer φ d o home
      (Nat.le_add_right m i) ((Nat.add_lt_add_left hi m).trans_le bound)

end YM.Integration.WilsonIndependentMatchedCoveredSeats
