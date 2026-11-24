import YM.Integration.WilsonIndependentFittedRosterHearing
import YM.Integration.WilsonIndependentFittedBallotReserve

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedRosterLedger
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedRosterFilms (Vote factor)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentEvenPassport (old)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}
local notation "slots" => Fin (n+1)

private theorem embedded_one:embed (1:Cost)=1:=map_one _

theorem unit (q:ℕ)(g:ℝ):belt q (embed (1:Cost))=1 ∧ cash q g (embed (1:Cost))=1:=by
  rw [embedded_one]
  constructor
  · unfold WilsonPhysicalMarkedDefect.RawProduct.belt
    rw [sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [coeff_one,hj]
    · simp
  · unfold WilsonPhysicalMarkedDefect.RawBank.cash
    rw [sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [coeff_one,hj]
    · simp

def doseAt (X:CutsP H T p v E W K U)(a amp:ℝ):Verse F:=dose X (a/amp)

def deposit (X:CutsP H T p v E W K U)(s q:ℕ)(g:ℝ)(a amp:ℝ)(present:Bool):ℝ:=
  if present then 1 else WilsonIndependentFittedStoppedWage.numerical X s q g (doseAt X a amp)

def capital (q:ℕ)(δ η a fee:ℝ)(present:Bool):ℝ:=
  if present then 1 else (Fintype.card (Alma F):ℝ)*(q+1)*δ^(-(h:ℝ)-η)*|a| *fee

theorem ledger (X:CutsP H T p v E W K U)(s q:ℕ)(g δ η a amp fee:ℝ)(present:Bool)
    (here:s≤X.m)(bought:WilsonIndependentFittedBallotReserve.receipt X s q (doseAt X a amp) ≤ capital (F:=F) q δ η a fee false):
    let A:=fun j:Vote F present=>clock X.ax X.tx X.N X.m s (factor (doseAt X a amp) present j)
    (∑j,‖cash q g (embed (A j))‖)=deposit X s q g a amp present ∧
    (∑j,belt q (embed (A j)))≤capital (F:=F) q δ η a fee present:=by
  intro A
  cases present with
  | false =>exact ⟨rfl,bought⟩
  | true =>
    have folded:clock X.ax X.tx X.N X.m s 1=1:=by
      conv_lhs => enter [4];rw [show X.m=s+(X.m-s) by omega]
      rw [WilsonIndependentFittedRelativeClock.reported]
      exact map_one _
    have c:=unit q g
    constructor
    · change (∑_:Unit,‖cash q g (embed (clock X.ax X.tx X.N X.m s 1))‖)=1
      simp only [Fintype.sum_unique,folded,c.2,norm_one]
    · change (∑_:Unit,belt q (embed (clock X.ax X.tx X.N X.m s 1)))≤1
      simp only [Fintype.sum_unique,folded,c.1,le_refl]

end YM.Integration.WilsonIndependentFittedRosterLedger
