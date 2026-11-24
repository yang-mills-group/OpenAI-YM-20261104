import YM.Integration.WilsonIndependentMovingRosterStablePortfolio

/-! The complete compensated finite source with a prescribed normalized column at its own report. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedInputs

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


open WilsonIndependentMovingRosterTopFields (offered stable fitted)

def pupil (c:(i:I)→Verse (F i))(φ:(i:I)→Rarity (D i))(y:I→ℝ)(o:I→CellR)(N:ℕ)(i:I):Era G ℝ:=
  locale (o i) ((sectionSeal (T i) (p i)).spins R.draws R.paid (φ i) (X i).m N N (y i) (c i))

def submitted (a:I→ℝ)(c:(i:I)→Verse (F i))(φ:(i:I)→Rarity (D i))(y:I→ℝ)(o:I→CellR)(N:ℕ)(i:I):Era G ℝ:=
  offered X a φ y o i+(pupil R X c φ y o N i-fitted R X a φ y o N i)

variable {N:ℕ}(same:∀i,(X i).vesselsC=R)(last:∀i,(X i).N=N)(upper:∀i,(X i).m+(X i).i=N)
    (a:I→ℝ)(c:(i:I)→Verse (F i))(φ:(i:I)→Rarity (D i))(y:I→ℝ)(o:I→CellR)
include same last upper

theorem figure (i:I):
    printed (X i).vesselsC (sectionSeal (T i) (p i)) (φ i) (c i) (X i).m (X i).N
      (y i) (o i) (X i).i=pupil R X c φ y o N i:=by
  unfold printed pupil
  rw [same i,last i,upper i]

theorem grades (i:I):Auth k (stable X a φ y o i) ∧ Auth (d i) (pupil R X c φ y o N i):=by
  rw [←figure R X same last upper c φ y o]
  exact ⟨(traced (X i) (a i) (φ i) (y i) (o i)).1 _ le_rfl,
    (wired (X i).vesselsC _ (passport (X i)) (φ i) (c i) (X i).m (X i).N
      (X i).i (X i).ha ((X i).hc.trans (X i).hn) (y i) (o i)).1 _ le_rfl⟩

theorem exact_source (i:I):
    submitted R X a c φ y o N i=stable X a φ y o i+pupil R X c φ y o N i:=by
  unfold submitted
  rw [WilsonIndependentMovingRosterTopFields.original R X same last upper a φ y o i]
  abel

end YM.Integration.WilsonIndependentMovingRosterNormalizedInputs
