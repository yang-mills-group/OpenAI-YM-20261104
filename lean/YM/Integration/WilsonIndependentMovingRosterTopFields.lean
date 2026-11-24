import YM.Integration.WilsonIndependentMatchedTotalTop
import YM.Integration.WilsonIndependentMatchedRosterSigned

/-! Each actual cut keeps its own reporting home. All its scalar and angular
coordinates are carried to the same upper board before pairing with any peers. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterTopFields

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedCoveredSeats
open WilsonIndependentMatchedFittedSeat (receiving dose)
open WilsonIndependentMatchedReportedProxy (sectionSeal passport)
open scoped BigOperators Topology Classical

variable {I:Type}{G:Gauge}{H:Hol G}{e k:ℕ}{d D u:I→ℕ}
    {F:(s:I)→Labels.Frame G (d s)}{T:(s:I)→SectionData (F s)}
    {p:∀s,d s<D s}{v:(s:I)→Rails (d s) k (u s) e}{E W K U:Credit}
    (R:Realm G (e+1) E)(X:(s:I)→CutsP H (T s) (p s) (v s) E W K U)

def offered (a:I→ℝ)(φ:(i:I)→Rarity (D i))(y:I→ℝ)(o:I→CellR)(i:I):Era G ℝ:=
  word (a i • (X i).pt) (φ i) (paceT (X i).ax.S (X i).m ((X i).m+(X i).i)) (y i) (o i) (d i)

def stable (a:I→ℝ)(φ:(i:I)→Rarity (D i))(y:I→ℝ)(o:I→CellR)(i:I):Era G ℝ:=
  seat (X i) (a i) (φ i) (y i) (o i) (X i).i

def fitted (a:I→ℝ)(φ:(i:I)→Rarity (D i))(y:I→ℝ)(o:I→CellR)(N:ℕ)(i:I):Era G ℝ:=
  locale (o i) ((sectionSeal (T i) (p i)).spins R.draws R.paid (φ i) (X i).m N N (y i)
    (dose (X i) (a i)))

variable {N:ℕ}(same:∀i,(X i).vesselsC=R)(last:∀i,(X i).N=N)(upper:∀i,(X i).m+(X i).i=N)
    (a:I→ℝ)(φ:(i:I)→Rarity (D i))(y:I→ℝ)(o:I→CellR)

include same last upper

theorem figure (i:I):
    receiving (X i) (a i) (φ i) (y i) (o i) (X i).i=fitted R X a φ y o N i:=by
  unfold receiving printed fitted
  rw [same i, last i, upper i]

theorem original (i:I):
    offered X a φ y o i=stable X a φ y o i+fitted R X a φ y o N i:=by
  rw [←figure R X same last upper]
  exact WilsonIndependentMatchedTotalTop.placed (X i) (a i) (φ i) (y i) (o i)

theorem grades (i:I):Auth k (stable X a φ y o i) ∧ Auth (d i) (fitted R X a φ y o N i):=by
  rw [←figure R X same last upper]
  exact ⟨(traced (X i) (a i) (φ i) (y i) (o i)).1 _ le_rfl,
    (wired (X i).vesselsC _ (passport (X i)) (φ i) (dose (X i) (a i)) (X i).m (X i).N
      (X i).i (X i).ha ((X i).hc.trans (X i).hn) (y i) (o i)).1 _ le_rfl⟩

end YM.Integration.WilsonIndependentMovingRosterTopFields
