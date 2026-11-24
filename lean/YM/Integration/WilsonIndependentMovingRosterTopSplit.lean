import YM.Integration.WilsonIndependentMovingRosterTopFields

/-! The complete product of actual submitted top fields differs from the
product of their dated fitted fields by the original sum over occupied
stable masks. Every term is integrated on the same finite course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterTopSplit

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterMasks (choose quiet placed)
open WilsonIndependentMatchedRosterCuts (ranks)
open WilsonIndependentMovingRosterTopFields (offered stable fitted)
open scoped BigOperators Topology Classical

variable {G:Gauge}{H:Hol G}{n e k h:ℕ}{d D u:Fin (n+1)→ℕ}
    {F:(s:Fin (n+1))→Labels.Frame G (d s)}{T:(s:Fin (n+1))→SectionData (F s)}
    {p:∀s,d s<D s}{v:(s:Fin (n+1))→Rails (d s) k (u s) e}{E W K U:Credit}
    (R:Realm G (e+1) E)(X:(s:Fin (n+1))→CutsP H (T s) (p s) (v s) E W K U)

theorem original {older N:ℕ}(before:older≤N)(degrees:∀i,d i≤h)(room:h≤k)
    (same:∀i,(X i).vesselsC=R)(last:∀i,(X i).N=N)(upper:∀i,(X i).m+(X i).i=N)
    (a:Fin (n+1)→ℝ)(φ:(i:Fin (n+1))→Rarity (D i))(y:Fin (n+1)→ℝ)(o:Fin (n+1)→CellR):
    let read:=fun l=>cruises R.draws R.paid N l N older
    let P:=stable X a φ y o
    let B:=fitted R X a φ y o N
    read ((n+1)*k) (MassP G ℝ n (offered X a φ y o))-read ((n+1)*k) (MassP G ℝ n B)=
      ∑j∈Finset.univ.erase (quiet n),read (ranks (choose n j) k h) (placed P B j):=by
  intro read P B
  have all : offered X a φ y o=fun i=>P i+B i:=
    funext (WilsonIndependentMovingRosterTopFields.original R X same last upper a φ y o)
  have grade:=WilsonIndependentMovingRosterTopFields.grades R X same last upper a φ y o
  rw [all]
  exact WilsonIndependentMatchedRosterSigned.original (R:=R) before le_rfl room P B
    (fun i=>(grade i).1) (fun i=>(grade i).2.tall (degrees i))

end YM.Integration.WilsonIndependentMovingRosterTopSplit
