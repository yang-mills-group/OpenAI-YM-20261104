import YM.Integration.WilsonThermometerFiniteConnectedRemainder
import YM.Integration.WilsonThermometerCenteredCredit

/-! The actual cutoff table contains all seven original graded reads. Pair
and singleton errors are measured with the absolute masses of the original
test at its independently placed fine sites. The local inverse and the
reference moments may vary with both regulators. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerFiniteConnectedCells
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Extraction Table Spec
open Climb Trace.Pilot RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East FVA1 OriginalForcedAddresses
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) (A : Group R.family 6)
local notation "J!" => Stock.census (Fin 3)
local notation "sites" z:max => Fin 3 → Site (R.family.side z.1 z.2)

def placement (z : UVIndex) (y : sites z) : Positions (Fin 3) (R.family.side z.1 z.2) where
  origin := y
  stub i := {y i}
  mem _ := mem_singleton_self _

abbrev measured (z : UVIndex) (y : sites z) : Poly J! :=
  WilsonThermometerCenteredCredit.table R A z (placement R z y)

local notation "χ" r:max z:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
local notation "W" φ:max r:max z:max => WilsonSeparatedOriginalThermometerCells.weight φ (χ r z)

def head (z : UVIndex) (r : ℝ) (φ : Test 3) (Q : sites z → Poly J!) : ℂ :=
  φ.applyTo fun x => ∑ s : (J!).Mode, weight (Q ((χ r z) x)) s *
    WilsonPositionThermometerGradedReading.row A z ((χ r z) x) s.val

def reference (z : UVIndex) (r : ℝ) (φ : Test 3) (Q : sites z → Poly J!) : ℂ :=
  φ.applyTo fun x => WilsonPositionThermometerConnected.value (read (Q ((χ r z) x)))

theorem original {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t) = (Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ r : ℝ, ∀ φ : Test 3, ∀ Q : sites z → Poly J!,
    (∀ y, (Q y).part (J!).quiet = 1) → ∀ E A₂ A₁ A₃ : ℝ, 0 ≤ A₂ → 0 ≤ A₁ →
    ‖head R A z r φ Q‖ ≤ E →
    let δ := fun (y : sites z) => read (total (measured R A z y) (Q y))
    (∀ s : Finset (Fin 3), s.card = 2 → ∑ y, ‖(W φ r z) y‖*‖δ y s‖^2 ≤ A₂^2) →
    (∀ t : Fin 3, ∑ y, ‖(W φ r z) y‖*‖δ y {t}‖^2 ≤ A₁^2) →
    (∀ t : Fin 3, ∑ y, ‖(W φ r z) y‖*‖δ y {t}‖^3 ≤ A₃^3) →
    ‖φ.applyTo (WilsonPositionThermometerGradedReading.full r A z) - reference R z r φ Q‖
      ≤ E + 3*(A₂*A₁) + 2*A₃^3 := by
  filter_upwards [WilsonThermometerCenteredCredit.unit_table R A checked unit] with z funded
  intro r φ Q qu E A₂ A₁ A₃ ha hb he
  dsimp only
  intro pair single cube
  let w := (W φ r z)
  let F := measured R A z
  have quiet (y : sites z) : (F y).part (J!).quiet = 1 := funded (placement R z y)
  have filed : head R A z r φ Q = ∑ y, w y*(total (F y) (Q y)).part full := by
    rw [head,WilsonSeparatedOriginalThermometerCells.tested φ (χ r z)
      (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
      (fun y => ∑ s : (J!).Mode, weight (Q y) s * WilsonPositionThermometerGradedReading.row A z y s.val)]
    apply sum_congr rfl
    intro y _
    rw [affine]
    rfl
  have all := WilsonThermometerFiniteConnectedRemainder.tested w F Q quiet qu E A₂ A₁ A₃
    ha hb (filed ▸ he) pair single cube
  let trueVal (y : sites z) := WilsonPositionThermometerConnected.value
    (WilsonPositionThermometerGradedReading.row A z y)
  let specVal (y : sites z) := WilsonPositionThermometerConnected.value (read (Q y))
  have actual (y : sites z) : read (Extra.Trajectories.connected (F y)) univ = trueVal y :=
    WilsonThermometerCenteredScalar.three _ (quiet y)
  have named (y : sites z) : read (Extra.Trajectories.connected (Q y)) univ = specVal y :=
    WilsonThermometerCenteredScalar.three _ (qu y)
  simp only [actual,named,mul_sub,Finset.sum_sub_distrib] at all
  have originalTest := WilsonSeparatedOriginalThermometerCells.tested φ (χ r z)
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
  change ‖φ.applyTo (fun x => trueVal ((χ r z) x)) -
    φ.applyTo (fun x => specVal ((χ r z) x))‖ ≤ _
  rw [originalTest trueVal,originalTest specVal]
  exact all

end YM.Integration.WilsonThermometerFiniteConnectedCells
