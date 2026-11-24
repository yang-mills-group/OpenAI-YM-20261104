import YM.Integration.WilsonPositionThermometerDepositedFaces
import YM.Integration.WilsonPositionThermometerGradedReading
import YM.Integration.WilsonPositionThermometerStationUnit

/-! The seven regulated position readings as faces of one deposited Wilson table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCourseIntake
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Marker
open Extraction Table Spec Climb Trace.Pilot Next.UVStress Next.Rank RG12 RG17 PhysMS
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East FVA1 OriginalForcedAddresses
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
local notation "j" => fun i : Fin 3 => index A (grade i)
local notation "v" => vector A (Finset.univ : Badge)
local notation "C" => R.family

def incoming {N k per : ℕ} (upper : k ≤ N) (o : Positions (Fin 3) (R.family.side N per)) :=
  gust R.family.path N per N (WilsonPositionThermometerDepositedFaces.pages R simple N per
    A.station (j) (v) o) k upper

def placed (z : UVIndex) (s : Badge) (o : Fin 3 → Site (R.family.side z.1 z.2))
    (U : Config G (R.family.side z.1 z.2)) : ℂ :=
  ∏ i, R.family.O z.1 z.2 (A.station.wheel.atCut z (index A (grade i)) (vector A s i)) (o i) U

theorem subwords {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t) = (Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ (s : Badge) (o : Fin 3 → Site (R.family.side z.1 z.2))
      (U : Config G (R.family.side z.1 z.2)), placed R A z s o U =
        ∏ i ∈ s, R.family.O z.1 z.2 (A.station.wheel.atCut z (index A (grade i)) ((v) i)) (o i) U := by
  have all := Filter.eventually_all.mpr (fun i : Fin 3 =>
    WilsonPositionThermometerStationUnit.original A.station (index A (grade i)) R.makes checked)
  filter_upwards [all] with z paid s o U
  have slot (i : Fin 3) : R.family.O z.1 z.2 (A.station.wheel.atCut z (index A (grade i))
        (vector A s i)) (o i) U = if i ∈ s then
        R.family.O z.1 z.2 (A.station.wheel.atCut z (index A (grade i)) ((v) i)) (o i) U else 1 := by
    by_cases hi : i ∈ s
    · simp [vector,source,hi]
    · rw [if_neg hi]
      have zero : vector A s i = (Bel R.family.book).unit (grade i) :=
        (congrArg (A.change (grade i)) (WilsonPositionThermometerGradedSource.unit C s i hi)).trans (unit _)
      rw [zero]
      exact congrFun ((paid i).2 (o i)) U
  simp [placed,slot]

theorem original {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t) = (Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k ≤ z.1)
      (o : Positions (Fin 3) (R.family.side z.1 z.2)) (s : (Stock.census (Fin 3)).Mode)
      (U : Config G (R.family.side k z.2)),
      (incoming R A simple upper o U).part s =
        (R.family.path.rep z.1 z.2 k).eval U • actualTransport C (N:=z.1)
          (placed R A z s.val o.origin) upper U := by
  have refs := Filter.eventually_all.mpr (fun i : Fin 3 => large_mesh f (R.family.ref (grade i)))
  filter_upwards [subwords R A checked unit,refs] with z words ref k upper o s U
  have physical := WilsonPositionThermometerDepositedFaces.deposited R simple z.1 z.2
    A.station (j) (v) o ref upper s U
  rw [show placed R A z s.val o.origin =
    fun W => ∏ i ∈ s.val, R.family.O z.1 z.2 (A.station.wheel.atCut z (index A (grade i)) ((v) i))
      (o.origin i) W from funext (words s.val o.origin)]
  exact physical

theorem step {N i per : ℕ} (live : i<N) (o : Positions (Fin 3) (R.family.side N per)) :
    LocalComparison.actualPush C N per i (incoming R A simple live o) =
      incoming R A simple live.le o := (gust_step R.family.path N per N _ live).symm

end YM.Integration.WilsonThermometerCourseIntake
end

