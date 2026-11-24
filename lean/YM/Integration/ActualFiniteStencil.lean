import YM.Integration.ActualStencilCylinder
import YM.Integration.ActualStencilOrb
import YM.Integration.RunLeadingSeries
import YM.WilsonComparison.Finite.Sources

/-! The recovered finite-MS interface instantiated with the retained Run's
original local section. All fields, including the full all-volume Reads
identity and low-order jet condition, are proved by the original section.
The native optional Dictionary.standard constructor is not used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualFiniteStencil
open Lattice Wilson Source
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G : Gauge}

def original (C : Family G) (hC : C.Makes) (d : ℕ)
    (hV : Bid.pop (C.localSection d)) (i : (C.labels.level d).Index) :
    WilsonComparison.Finite.Stencil G ((C.labels.level d).grades i).2 where
  F := ActualStencilCylinder.cylinder (C.localSection d) (Pi.single i 1)
  O := ActualStencilCylinder.observed (C.localSection d) (Pi.single i 1)
  continuous := ActualStencilCylinder.observed_continuous _ _
  reads := ActualStencilCylinder.reads _ _
  invariant := ActualStencilCylinder.invariant _ (hC.sections d) _
  low := ActualStencilCylinder.low _ hV i
  phase := ActualStencilCylinder.phase _ _

/-- One fixed stencil for every regulator, position, coupling order and
subsequent independent test. The original Run supplies the valuation. -/
def retained (R : Run G) (d : ℕ) (i : (R.family.labels.level d).Index) :
    WilsonComparison.Finite.Stencil G ((R.family.labels.level d).grades i).2 :=
  original R.family R.makes d (CoefficientBridge.run_valuation R d) i

theorem retained_cover (R : Run G) (d : ℕ)
    (i : (R.family.labels.level d).Index) :
    (retained R d i).F =
      ActualStencilCylinder.cylinder (R.family.localSection d) (Pi.single i 1) := rfl

theorem retained_observable (R : Run G) (d : ℕ)
    (i : (R.family.labels.level d).Index) (n : Side) (x : Site n)
    (U : Config G n) :
    ((retained R d i).O n x U : ℂ) =
      (R.family.localSection d).places (Pi.single i 1) x U :=
  ActualStencilCylinder.observed_complex _ (R.makes.sections d) i n x U

/-- Exact original calibration/engineering expansion in the fixed native
stencils. This does not identify a separately prescribed MS field conversion. -/
theorem retained_physical (R : Run G) (N p d : ℕ)
    (v : R.family.label d) (x : Site (R.family.side N p))
    (U : Config G (R.family.side N p)) :
    R.family.O N p v x U = Dict06.Actual.factor R.family N d *
      ∑ i, Dict06.Actual.matrix R.family N p d v i *
        ((retained R d i).O (R.family.side N p) x U : ℂ) :=
  ActualStencilCylinder.physical_expansion R.family R.makes N p d v x U

theorem retained_calibrated (R : Run G) (N p d : ℕ)
    (i : (R.family.labels.level d).Index) (x : Site (R.family.side N p))
    (U : Config G (R.family.side N p)) :
    R.family.O N p
        (Dict06.Actual.calibrate R.family N p d ((R.family.labels.level d).basis i)) x U =
      Dict06.Actual.factor R.family N d *
        ((retained R d i).O (R.family.side N p) x U : ℂ) := by
  rw [retained_physical, Dict06.Actual.meet, (R.family.labels.level d).coords_basis]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The original inversion observable has exactly its prescribed real
engineering factor; this does not identify that factor with an MS fee. -/
theorem retained_inversion (R : Run G) (N p d : ℕ)
    (i : (R.family.labels.level d).Index) (x : Site (R.family.side N p))
    (U : Config G (R.family.side N p)) :
    physicalInversionObservable R.family N p d x i U =
      ((R.family.S.a N) ^ d)⁻¹ * (retained R d i).O (R.family.side N p) x U :=
  ActualStencilOrb.calibrated R.family N p d i x U

end YM.Integration.ActualFiniteStencil
