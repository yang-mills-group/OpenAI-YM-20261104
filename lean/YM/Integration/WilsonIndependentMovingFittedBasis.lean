import YM.Integration.WilsonIndependentMovingFittedCash

/-! The only unweighted detector in a fitted moving slot is its
actual unit thermal monomial. The other slots keep their signed fields
through the full normalized common-stop measurement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedBasis
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

def field (X:slots → CutsP H T p v E W K U)(flag:slots → Bool)(a:slots → ℝ)(φ:slots → Rarity D)
    (y:slots → ℝ)(o:slots → CellR)(dir:slots → Alma F):Era G ℝ:=
  MassP G ℝ n (fun j=>entry (flag j) (X j) (a j) (axis (dir j) 0) (φ j) (y j) (o j) (X j).i)

theorem purchased (X:slots → CutsP H T p v E W K U)(L:Torch H T p v E W K)(N top s:ℕ)
    (flag:slots → Bool)(a:slots → ℝ)(φ:slots → Rarity D)(y:slots → ℝ)(o:slots → CellR)
    (Q:ℕ)(x:Fin 0 → YForest G)(fallback:Alma F)(M:ℝ)
    (paid:∀dir:slots → Alma F,∀q ≤ Q,
      ‖(cruises L.L.V.draws L.L.V.paid N (ranks flag k h) top s (field X flag a φ y o dir)).2 q 0 x‖ ≤ M):
    ∀w:(j:slots) → Vote F (flag j),belt Q (embed (unitRow X L N top s flag a φ y o w x)) ≤ ((Q+1:ℕ):ℝ)*M:=by
  intro w
  let dir:=fun j=>name fallback (flag j) (w j)
  have eqn:(fun j=>piece false (X j) (a j) 0 (φ j) (y j) (o j) (flag j) (w j))=
        (fun j=>entry (flag j) (X j) (a j) (axis (dir j) 0) (φ j) (y j) (o j) (X j).i):=
    funext (fun j=>WilsonIndependentFittedRosterHearing.basis (X j) (flag j) fallback (w j) (a j) (φ j) (y j) (o j))
  calc
    _ ≤ ∑j∈range (Q+1),M:=by
      apply sum_le_sum
      intro j hj
      have tier:=paid dir j (Nat.le_of_lt_succ (mem_range.mp hj))
      simp only [WilsonIndependentMovingFittedRoster.unitRow,eqn,embed,coeff_map,
        WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]
      simpa [field] using tier
    _=_:=by simp

end YM.Integration.WilsonIndependentMovingFittedBasis
