import YM.Integration.WilsonIndependentMovingFittedRoster
import YM.Integration.WilsonIndependentFittedRosterHearing

/-! In one stopped native product each fitted home contributes its
own full finite numerical coefficient. The coefficientwise gross is
spent only on the terms thrown out by the common truncation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedCash
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedRosterFilms (Vote factor piece)
open WilsonIndependentMovingFittedRoster (row unitRow)
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

def factors (X:Fin (n+1) → CutsP H T p v E W K U)(L:Torch H T p v E W K)(N s:ℕ)(flag:Fin (n+1) → Bool)
    (d:Fin (n+1) → Verse F)(j:Fin (n+1))(w:Vote F (flag j)):Cost:=
  clock L.L.V.draws L.L.V.paid N (X j).m s (factor (d j) (flag j) w)

variable (X:Fin (n+1) → CutsP H T p v E W K U)(L:Torch H T p v E W K)(N top s:ℕ)
    (cap:top ≤ N)(school:∀j,(X j).L=L)(quiet:∀j,(X j).N=N)(dates:∀j,(X j).m+(X j).i=top)
    (before:∀j,s ≤ (X j).m)(flag:Fin (n+1) → Bool)(a:Fin (n+1) → ℝ)(d:Fin (n+1) → Verse F)
    (φ:Fin (n+1) → Rarity D)(y:Fin (n+1) → ℝ)(o:Fin (n+1) → CellR)

include cap school quiet dates before in
theorem recorded {r:ℕ}(x:Fin r → YForest G):
    row X L N top s flag a d φ y o x=WilsonIndependentFittedRosterCash.roster (factors X L N s flag d)
      (fun w=>unitRow X L N top s flag a φ y o w x):=by
  rw [WilsonIndependentMovingFittedRoster.original X L N top s cap school quiet dates before flag a d φ y o x]
  unfold WilsonIndependentFittedRosterCash.roster
  exact sum_congr (by ext w;simp) (fun _ _=>rfl)

include cap school quiet dates before in
theorem measured {r:ℕ}(x:Fin r → YForest G)(Q:ℕ)(g:ℝ)(small:|g| ≤ 1)(M:ℝ)
    (earned:∀w,belt Q (embed (unitRow X L N top s flag a φ y o w x)) ≤ M):
    ‖cash Q g (embed (row X L N top s flag a d φ y o x))-
      ∑w:(j:Fin (n+1)) → Vote F (flag j),(∏j,cash Q g (embed (factors X L N s flag d j (w j))))*
        cash Q g (embed (unitRow X L N top s flag a φ y o w x))‖ ≤
      (((n+1:ℕ):ℝ)+1)*|g|^(Q+1)*reserve Q (factors X L N s flag d)*M:=by
  rw [recorded X L N top s cap school quiet dates before flag a d φ y o x]
  have price:=WilsonIndependentFittedRosterCash.measured Q g small
    (factors X L N s flag d) (fun w=>unitRow X L N top s flag a φ y o w x) M earned
  simp only [Fintype.card_fin] at price
  refine le_trans (le_of_eq ?_) price
  congr 2
  exact sum_congr (by ext w;simp) (fun _ _=>rfl)

include cap school quiet dates before in
theorem original {r:ℕ}(x:Fin r → YForest G)(Q:ℕ)(g:ℝ)(small:|g| ≤ 1)(M:ℝ)
    (earned:∀w,belt Q (embed (unitRow X L N top s flag a φ y o w x)) ≤ M):
    ‖cash Q g (embed (row X L N top s flag a d φ y o x))‖ ≤
      (numerical Q g (factors X L N s flag d)+(((n+1:ℕ):ℝ)+1)*|g|^(Q+1)*reserve Q (factors X L N s flag d))*M:=by
  rw [recorded X L N top s cap school quiet dates before flag a d φ y o x]
  simpa only [Fintype.card_fin] using WilsonIndependentFittedRosterCash.original Q g small
    (factors X L N s flag d) (fun w=>unitRow X L N top s flag a φ y o w x) M earned

end YM.Integration.WilsonIndependentMovingFittedCash
