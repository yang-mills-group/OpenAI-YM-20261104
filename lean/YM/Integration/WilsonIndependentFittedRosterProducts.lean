import YM.Integration.WilsonIndependentFittedProductCensus
import YM.Integration.WilsonIndependentFittedRosterFilms
import YM.Integration.WilsonIndependentMatchedRosterCuts
import YM.Integration.WilsonIndependentMatchedCensusReceipt

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedRosterProducts
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

def row (X:slots→CutsP H T p v E W K U)(flag:slots→Bool)(a:slots→ℝ)(d:slots→Verse F)
    (φ:slots→Rarity D)(y:ℝ)(o:CellR)(s:ℕ){r:ℕ}(x:Fin r→YForest G):Cost:=
  let P:=MassP G ℝ n (fun j=>entry (flag j) (X j) (a j) (d j) (φ j) y o (X 0).i)
  reading (cruises (X 0).ax (X 0).tx (X 0).N (ranks flag k h) ((X 0).m+(X 0).i) s P).2 x

def unitRow (X:slots→CutsP H T p v E W K U)(flag:slots→Bool)(a:slots→ℝ)
    (φ:slots→Rarity D)(y:ℝ)(o:CellR)(s:ℕ)(sel:(j:slots)→Vote F (flag j)){r:ℕ}(x:Fin r→YForest G):Cost:=
  let P:=MassP G ℝ n (fun j=>piece false (X j) (a j) 0 (φ j) y o (flag j) (sel j))
  reading (cruises (X 0).ax (X 0).tx (X 0).N (ranks flag k h) ((X 0).m+(X 0).i) s P).2 x

theorem original (X:slots→CutsP H T p v E W K U)(L:Torch H T p v E W K)(run:XSpace.Run)
    (base idx f:ℕ)(amp fee:slots→ℝ)(δ η:ℝ)(stem:slots→TowerS G D)
    (cofile:∀j,Filed (X j) L run base idx f (amp j) δ η (fee j) (stem j))
    (flag:slots→Bool)(a:slots→ℝ)(d:slots→Verse F)(φ:slots→Rarity D)(y:ℝ)(o:CellR)
    (stop:ℕ)(before:stop≤old run base idx){r:ℕ}(x:Fin r→YForest G):
    row X flag a d φ y o (f+stop) x=
      ∑sel:(j:slots)→Vote F (flag j),
        (∏j,clock (X 0).ax (X 0).tx (X 0).N (X 0).m (f+stop) (factor (d j) (flag j) (sel j)))*
        unitRow X flag a φ y o (f+stop) sel x:=by
  let P:=(fun j=>piece true (X j) (a j) (d j) (φ j) y o (flag j))
  let Q:=(fun j=>piece false (X j) (a j) 0 (φ j) y o (flag j))
  have steps (j:slots):(X j).i=(X 0).i:=(cofile j).gap.trans (cofile 0).gap.symm
  have top (j:slots):(X j).N=(X 0).N:=(cofile j).top.trans (cofile 0).top.symm
  have home (j:slots):(X j).m=(X 0).m:=(cofile j).report.trans (cofile 0).report.symm
  have course (j:slots):(X j).vesselsC=(X 0).vesselsC:=congrArg (fun Z=>Z.L.V) ((cofile j).school.trans (cofile 0).school.symm)
  have keep (j:slots)(b:Vote F (flag j)):piece false (X j) (a j) (d j) (φ j) y o (flag j) b=Q j b:=kept ..
  have inlet: (fun j=>entry (flag j) (X j) (a j) (d j) (φ j) y o (X 0).i)=(fun j=>∑t,P j t):=by
    funext j
    rw [←steps j]
    exact WilsonIndependentFittedRosterFilms.entire ..
  have disclosed (j:slots)(b:Vote F (flag j)):
      P j b=funded (reel (relativeC (X 0).ax (X 0).tx (X 0).N (X 0).m (X 0).i) (factor (d j) (flag j) b))
        (Q j b):=by
    have same:=WilsonIndependentFittedRosterFilms.scaled (X j) (a j) (d j) (φ j) y o (flag j) b
    rw [keep j b,top j,home j,steps j] at same
    have sameA:(X j).ax=(X 0).ax:=congrArg (fun r=>r.draws) (course j)
    have sameO:(X j).tx=(X 0).tx:=congrArg (fun r=>r.paid) (course j)
    rw [sameA,sameO] at same
    exact same
  unfold row
  rw [inlet]
  exact WilsonIndependentFittedProductCensus.stopped (X 0).ax (X 0).tx (X 0).vesselsC.hG (X 0).vesselsC.green
    (X 0).N (X 0).m (X 0).i (f+stop) ((cofile 0).report ▸ Nat.add_le_add_left before f)
    ((X 0).hc.trans (X 0).hn) n (fun j=>degree (flag j) k h) (fun j=>Vote F (flag j))
    (fun j=>factor (d j) (flag j)) P Q
    (fun j b=>WilsonIndependentFittedRosterFilms.authenticated (X j) (a j) (d j) (φ j) y o true (flag j) b)
    (fun j b=>WilsonIndependentFittedRosterFilms.authenticated (X j) (a j) 0 (φ j) y o false (flag j) b)
    disclosed r x

end YM.Integration.WilsonIndependentFittedRosterProducts
