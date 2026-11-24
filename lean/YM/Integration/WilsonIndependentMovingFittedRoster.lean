import YM.Integration.WilsonIndependentMovingFittedClocks
import YM.Integration.WilsonIndependentFittedRosterFilms
import YM.Integration.WilsonIndependentMatchedRosterCuts
import YM.Integration.WilsonIndependentMatchedCensusReceipt

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedRoster
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedReportedFilm (funded)
open WilsonIndependentFittedRosterFilms (Vote factor piece)
open WilsonIndependentMatchedRosterSlots (entry degree)
open WilsonIndependentMatchedRosterCuts (ranks)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentEvenPassport (old)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}
local notation "slots" => Fin (n+1)

private lemma kept (X:CutsP H T p v E W K U)(a:ℝ)(d:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR)
    (flag:Bool)(b:Vote F flag):
    piece false X a d φ y o flag b=piece false X a 0 φ y o flag b :=by
  cases flag
  · simp only [WilsonIndependentFittedRosterFilms.piece,Bool.false_eq_true,if_false]
  · simp only [WilsonIndependentFittedRosterFilms.piece]

def row (X:slots → CutsP H T p v E W K U)(L:Torch H T p v E W K)(N top s:ℕ)(flag:slots → Bool)
    (a:slots → ℝ)(d:slots → Verse F)(φ:slots → Rarity D)(y:slots → ℝ)(o:slots → CellR){r:ℕ}(x:Fin r → YForest G):Cost:=
  let P:=MassP G ℝ n (fun j=>entry (flag j) (X j) (a j) (d j) (φ j) (y j) (o j) (X j).i)
  reading (cruises L.L.V.draws L.L.V.paid N (ranks flag k h) top s P).2 x

def unitRow (X:slots → CutsP H T p v E W K U)(L:Torch H T p v E W K)(N top s:ℕ)(flag:slots → Bool)
    (a:slots → ℝ)(φ:slots → Rarity D)(y:slots → ℝ)(o:slots → CellR)
    (sel:(j:slots) → Vote F (flag j)){r:ℕ}(x:Fin r → YForest G):Cost:=
  let P:=MassP G ℝ n (fun j=>piece false (X j) (a j) 0 (φ j) (y j) (o j) (flag j) (sel j))
  reading (cruises L.L.V.draws L.L.V.paid N (ranks flag k h) top s P).2 x

theorem original (X:slots → CutsP H T p v E W K U)(L:Torch H T p v E W K)(N top s:ℕ)(cap:top≤N)
    (school:∀j,(X j).L=L)(quiet:∀j,(X j).N=N)(dates:∀j,(X j).m+(X j).i=top)(before:∀j,s≤(X j).m)
    (flag:slots → Bool)(a:slots → ℝ)(d:slots → Verse F)(φ:slots → Rarity D)(y:slots → ℝ)(o:slots → CellR)
    {r:ℕ}(x:Fin r → YForest G):
    row X L N top s flag a d φ y o x=
      ∑sel:(j:slots) → Vote F (flag j),
        (∏j,clock L.L.V.draws L.L.V.paid N (X j).m s (factor (d j) (flag j) (sel j)))*
          unitRow X L N top s flag a φ y o sel x:=by
  let P:=fun j=>piece true (X j) (a j) (d j) (φ j) (y j) (o j) (flag j)
  let Q:=fun j=>piece false (X j) (a j) 0 (φ j) (y j) (o j) (flag j)
  have inlet:(fun j=>entry (flag j) (X j) (a j) (d j) (φ j) (y j) (o j) (X j).i)=(fun j=>∑t,P j t):=
    funext (fun j=>WilsonIndependentFittedRosterFilms.entire ..)
  have disclosed (j:slots)(b:Vote F (flag j)):P j b=funded
      (reel (relativeC L.L.V.draws L.L.V.paid N (X j).m (X j).i) (factor (d j) (flag j) b)) (Q j b):=by
    have share:(X j).vesselsC=L.L.V:=congrArg (fun Z=>Z.L.V) (school j)
    have sameA:(X j).ax=L.L.V.draws:=congrArg (fun R=>R.draws) share
    have sameO:(X j).tx=L.L.V.paid:=congrArg (fun R=>R.paid) share
    have same:=WilsonIndependentFittedRosterFilms.scaled (X j) (a j) (d j) (φ j) (y j) (o j) (flag j) b
    rw [kept,sameA,sameO,quiet j] at same
    exact same
  unfold row
  rw [inlet]
  exact WilsonIndependentMovingFittedClocks.original L.L.V.draws L.L.V.paid L.L.V.hG L.L.V.green N top s cap n
    (fun j=>degree (flag j) k h) (fun j=>(X j).m) (fun j=>(X j).i) (fun j=>Vote F (flag j))
    (fun j=>factor (d j) (flag j)) P Q dates before
    (fun j b=>WilsonIndependentFittedRosterFilms.authenticated (X j) (a j) (d j) (φ j) (y j) (o j) true (flag j) b)
    (fun j b=>WilsonIndependentFittedRosterFilms.authenticated (X j) (a j) 0 (φ j) (y j) (o j) false (flag j) b)
    disclosed r x

end YM.Integration.WilsonIndependentMovingFittedRoster
