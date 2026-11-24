import YM.Integration.WilsonIndependentMovingFittedBasis
import YM.Integration.WilsonIndependentMovingRosterNormalizedMask

/-! The only unweighted detector in a fitted moving slot is its
actual unit thermal monomial. The other slots keep their signed fields
through the full normalized common-stop measurement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedMask
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
open WilsonIndependentFittedRosterHearing (name basis)
variable {G:Gauge}{h D k e u n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}
local notation "slots" => Fin (n+1)

open WilsonIndependentMatchedRosterMasks (Bits choose placed)
open WilsonIndependentMovingRosterTopFields (stable)
open WilsonIndependentMovingRosterNormalizedInputs (pupil)
open WilsonIndependentMovingFittedBasis (field)

variable (X:Fin (n+1) → CutsP H T p v E W K U)(L:Torch H T p v E W K)(N:ℕ)
    (same:∀i,(X i).vesselsC=L.L.V)(last:∀i,(X i).N=N)(upper:∀i,(X i).m+(X i).i=N)
    (mask:Bits n)(a:Fin (n+1) → ℝ)(φ:Fin (n+1) → Rarity D)(y:Fin (n+1) → ℝ)(o:Fin (n+1) → CellR)

include same last upper in
theorem mounted (dir:slots → Alma F):
    field X (choose n mask) a φ y o dir=
      placed (stable X a φ y o) (pupil L.L.V X (fun j=>axis (dir j) 0) φ y o N) mask:=by
  unfold field WilsonIndependentMatchedRosterMasks.placed
  congr 1
  funext j
  cases phase:choose n mask j with
  | false=>
    simp only [WilsonIndependentMatchedRosterSlots.entry,Bool.false_eq_true,↓reduceIte]
    exact WilsonIndependentMovingRosterNormalizedInputs.figure L.L.V X same last upper (fun j=>axis (dir j) 0) φ y o j
  | true=>rfl

include same last upper in
theorem purchased (s Q:ℕ)(x:Fin 0 → YForest G)(fallback:Alma F)(M:ℝ)
    (earned:∀dir:slots → Alma F,∀q ≤ Q,‖(cruises L.L.V.draws L.L.V.paid N (ranks (choose n mask) k h) N s
      (placed (stable X a φ y o) (pupil L.L.V X (fun j=>axis (dir j) 0) φ y o N) mask)).2 q 0 x‖ ≤ M):
    ∀w:(j:slots) → Vote F (choose n mask j),
      belt Q (embed (unitRow X L N N s (choose n mask) a φ y o w x)) ≤ ((Q+1:ℕ):ℝ)*M:=by
  apply WilsonIndependentMovingFittedBasis.purchased X L N N s (choose n mask) a φ y o Q x fallback M
  intro dir
  rw [mounted X L N same last upper mask a φ y o dir]
  exact earned dir

end YM.Integration.WilsonIndependentMovingFittedMask
