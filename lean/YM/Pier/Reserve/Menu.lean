import YM.Pier.Reserve.Tab
import YM.FullVolume.Mark.Hinge
/-! Reserve specifications on the native plate. These are discharged for
Boutique's ACTUAL `castT` by local producer proofs. The unprojected vertices
are indexed by their literal inputs; no gate promise for a different
organisation being transferred by mere equality of densities. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pier
open Finset Function Set Filter MeasureTheory Lattice Wilson RG Source Labels Bid
  Extra.Histories Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
  MergeProof MergeProof.Matric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} (H : History G) (N p j : ℕ)
    (Y : Hol G)
local notation "Out" => H.rep N p j
local notation "InSide" => H.S.side (j+1) p
local notation "L" => H.S.block j

/-- Independently strengthen the bought plate's `Prints` estimate, leaving
    operational inputs and charges (`u`, `rate`) the same, except with real
    *gain* on `ink` and strengthened simultaneous regular reserve. For dependent
    `duet` casts take general Inlet R and actual `gate` D (producer at
    `H.rep N p (j+1)`, the *only* connection at which this is used).*span*
    on ink retains the actual `fare`, combined with partners under Tale,
    and certifies this singleton-source output, not an all-source norm. `X`
    (and which labels are available on the plate) is selected by the upstream
    Cap when using the Menu. -/
structure Lathe (B : SectionData F) (R : Rep G (H.S.side (j+1) p))
    (A : Matric.Plate F (H.S.side (j+1) p) (H.S.side j p))
    (D : GaugeDoor (H.rep N p (j+1)) (H.rep N p j)) (u ζ : ℝ) : Prop where
  main i : let x := Size.axis F i
    Room (tell (A.main i)) 0 Out (kappa H j) (rotationBudget (Out).p)
      (u * F.coeffSize (vowel F L (F.core x)))
  regular i (f : Config G (H.S.side (j+1) p) → ℂ) a : let s := mapSeat (n:=InSide) i
    RegFit R 0 d Y s f → R.p.supBounds 0 s f a →
    Room (tell (A.tint i f)) 0 Out (kappa H j) (rotationBudget (Out).p)
      (ζ * R.p.mass s a)
  forced i (f : Config G (H.S.side (j+1) p) → ℂ) a (X : Wing → Prop) :
    let x := R.p.mass (R.activities.forced i).support a
    X (.gasKey i) → f ≠ 0 → SlotFit R 0 i f → (∀ V, ‖f V‖ ≤ a) →
    Room (tell (A.ink i f)) 0 Out (kappa H j) (rotationBudget (Out).p)
      (ζ * x) ∧
    Span B H N p j Y (tell (A.ink i f)) 0 (exactGas R.activities i f)
      0 D X (Extra.Histories.fare R i f) 0 (ζ*x) (ζ*x) (2*x)

end YM.Pier
