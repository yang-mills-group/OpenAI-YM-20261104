import YM.Integration.WilsonIndependentFittedRosterProducts
import YM.Integration.WilsonIndependentFittedRosterCash
import YM.Integration.WilsonIndependentMatchedRosterAxes

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedRosterHearing
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedRosterFilms (Vote factor piece)
open WilsonIndependentFittedRosterProducts (row unitRow)
open WilsonIndependentFittedRosterCash (numerical reserve)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentMatchedRosterSlots (entry)
open WilsonIndependentMatchedRosterStop (Hearing)
open WilsonIndependentMatchedRosterCuts (ranks)
open WilsonIndependentMatchedPivotSeat (axis)
open WilsonIndependentMatchedRosterChronology (mass)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentEvenPassport (old)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}
local notation "slots" => Fin (n+1)

def name (fallback:Alma F):(b:Bool)→Vote F b→Alma F
  | true,_=>fallback
  | false,j=>j

theorem basis (X:CutsP H T p v E W K U)(flag:Bool)(fallback:Alma F)(j:Vote F flag)
    (a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):
    piece false X a 0 φ y o flag j=entry flag X a (axis (name fallback flag j) 0) φ y o X.i:=by
  cases flag <;> rfl

theorem original (X:slots→CutsP H T p v E W K U)(L:Torch H T p v E W K)(run:XSpace.Run)
    (base idx f:ℕ)(amp fee:slots→ℝ)(δ η:ℝ)(stem:slots→TowerS G D)
    (cofile:∀j,Filed (X j) L run base idx f (amp j) δ η (fee j) (stem j))
    (flag:slots→Bool)(a:slots→ℝ)(d:slots→Verse F)(φ:slots→Rarity D)(y:ℝ)(o:CellR)
    (stop:ℕ)(before:stop≤old run base idx)(u₀ Q:ℕ)(cap:Q≤e)(g:ℝ)(small:|g|≤1)(x:Fin 0→YForest G)
    (fallback:Alma F)(M:ℝ)
    (earned:∀dir:slots→Alma F,Hearing (X 0) (ranks flag k h) u₀ ((X 0).m+(X 0).i) (f+stop)
      (mass (fun j=>entry (flag j) (X j) (a j) (axis (dir j) 0) (φ j) y o) (X 0).i) M):
    let A:=(fun j=>fun w:Vote F (flag j)=>clock (X 0).ax (X 0).tx (X 0).N (X 0).m (f+stop) (factor (d j) (flag j) w))
    ‖cash Q g (embed (row X flag a d φ y o (f+stop) x))‖≤
      (numerical Q g A+(((n+1:ℕ):ℝ)+1)*|g|^(Q+1)*reserve Q A)*(((Q+1:ℕ):ℝ)*M):=by
  intro A
  let B:=fun sel=>(unitRow X flag a φ y o (f+stop) sel x)
  have total:=WilsonIndependentFittedRosterProducts.original X L run base idx f amp fee δ η stem cofile
    flag a d φ y o stop before x
  have equality:row X flag a d φ y o (f+stop) x=WilsonIndependentFittedRosterCash.roster A B:=by
    rw [total]
    unfold WilsonIndependentFittedRosterCash.roster
    exact sum_congr (by ext w;simp) fun w _=>rfl
  rw [equality]
  have purchased:=WilsonIndependentFittedRosterCash.original Q g small A B (((Q+1:ℕ):ℝ)*M)
  simp only [Fintype.card_fin] at purchased
  apply purchased 
  intro w
  let dir:=fun j=>name fallback (flag j) (w j)
  have pay:∀j≤e,∀z₀:Fin 0→YForest G,
      ‖(cruises (X 0).ax (X 0).tx (X 0).N (ranks flag k h) ((X 0).m+(X 0).i) (f+stop)
        (mass (fun j=>entry (flag j) (X j) (a j) (axis (dir j) 0) (φ j) y o) (X 0).i)).2 j 0 z₀‖≤M:=(earned dir).2
  have live (j:slots):(X j).i=(X 0).i:=(cofile j).gap.trans (cofile 0).gap.symm
  have eqn:(fun j=>piece false (X j) (a j) 0 (φ j) y o (flag j) (w j))=
      (fun j=>entry (flag j) (X j) (a j) (axis (dir j) 0) (φ j) y o (X 0).i):=by
    funext j
    rw [←live j]
    exact basis (X j) (flag j) fallback (w j) (a j) (φ j) y o
  calc
    _ ≤ ∑j∈range (Q+1),M:=by
      apply sum_le_sum
      intro j hj
      have tier:=pay j ((Nat.le_of_lt_succ (mem_range.mp hj)).trans cap) x
      simp only [B,WilsonIndependentFittedRosterProducts.unitRow,eqn,embed,coeff_map,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]
      simpa [mass] using tier
    _=_:=by simp

end YM.Integration.WilsonIndependentFittedRosterHearing
