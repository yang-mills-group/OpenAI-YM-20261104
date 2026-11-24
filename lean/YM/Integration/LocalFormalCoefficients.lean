import YM.Comparison.RG02.Bulk.Sequence
import YM.Comparison.RG02.Order.Eval
import YM.Comparison.RG02.Order.VacLog
import YM.Source.Construction

/-! The exact local formal coefficient object shared by the two external
inputs. This is the independently defined full Wick prescription `Bulk.Fk`,
on one fixed actual chain; it is not defined as a Taylor series of the actual
normalized output.

The datum is fixed before the requested order. `Order.observe` divides the
polarized coupling coefficient by `k!`, so these are ordinary power-series
coefficients, not repeated coupling derivatives. Marker normalization is
exactly the native `Census` convention. Every operation below keeps the same
conditional vacuum denominator.

These local coefficients are still functions of a coarse field through the
datum. They are not scalar terminal correlations. The iteration/readout and
its link to the concrete continuum MS theorem remain part of external item 2.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalFormal
open RG Lattice Wilson Exterior Tree Marker
open Comparison.RG02
open scoped Classical

variable {G : Gauge} (C : Family G) (Y : Bulk.Chain C.path)
    {V : Type} [DecidableEq V] (R : Census V)

/-- One actual local step, with its full marked input, chosen independently
of the perturbative demand. `Y` is the same chain retained by both inputs. -/
structure Datum where
  cutoff : ℕ
  period : ℕ
  level : ℕ
  below : level < cutoff
  forest : Forest (C.path.levels.clock.op level period).ratio
  tag : (C.path.levels.clock.op level period).Choices
  colors : Bulk.Colors R G (C.side (level + 1) period)
  field : fieldDir G (C.side level period) 1

namespace Datum
variable {C R} (D : Datum C R) [Fintype V]

abbrev kernel := Y.step D.cutoff D.level D.period D.below

/-- Full conditional numerator, after extracting only its stated leading
scalar, with the genuine base action, loop and Haar terms. -/
def raw (r : ℕ) : Order.Grade R r :=
  Bulk.Fk (D.kernel Y) D.forest D.tag D.colors D.field r

def denominator (r : ℕ) : Order.Grade R r := Order.denominator (D.raw Y r)
def ordinary (r : ℕ) : Order.Grade R r := Order.ratio (D.raw Y r)
def vacuumLog (r : ℕ) : Order.Grade R r := Order.logVac (D.raw Y r)
def markedLog (r : ℕ) : Order.Grade R r := Order.logMarked (D.raw Y r)

def rawCoefficient (r k : ℕ) (mode : R.Mode) : ℂ :=
  (Order.observe R r (D.raw Y r) k).part mode

def ordinaryCoefficient (r k : ℕ) (mode : R.Mode) : ℂ :=
  (Order.observe R r (D.ordinary Y r) k).part mode

def vacuumLogCoefficient (r k : ℕ) (mode : R.Mode) : ℂ :=
  (Order.observe R r (D.vacuumLog Y r) k).part mode

def markedLogCoefficient (r k : ℕ) (mode : R.Mode) : ℂ :=
  (Order.observe R r (D.markedLog Y r) k).part mode

theorem raw_unit (r : ℕ) : Order.UnitLeading (D.raw Y r) :=
  Bulk.fk_unit (D.kernel Y) D.forest D.tag D.colors D.field r

theorem reconstruct (r : ℕ) :
    D.denominator Y r * D.ordinary Y r = D.raw Y r :=
  Order.recovers (D.raw_unit Y r)

theorem ordinary_denominator (r : ℕ) :
    Order.denominator (D.ordinary Y r) = 1 :=
  Order.ratio_pure (D.raw_unit Y r)

theorem markedLog_denominator (r : ℕ) :
    Order.denominator (D.markedLog Y r) = 0 :=
  Order.log_marked (D.raw_unit Y r)

theorem logarithm_decomposition (r : ℕ) :
    Extra.Trajectories.connected (D.raw Y r) =
      D.vacuumLog Y r + D.markedLog Y r :=
  Order.log_full (D.raw_unit Y r)

/-- Choice independence is an exact property of the independently defined
formal germ. It does not assert equality of two numerical local integrals. -/
def retag (tag : (C.path.levels.clock.op D.level D.period).Choices) : Datum C R :=
  { D with tag := tag }

theorem raw_retag (tag : (C.path.levels.clock.op D.level D.period).Choices) (r : ℕ) :
    (D.retag tag).raw Y r = D.raw Y r := by
  exact (Bulk.fkChoice (D.kernel Y) D.forest D.tag D.colors D.field r tag).symm

theorem ordinaryCoefficient_retag
    (tag : (C.path.levels.clock.op D.level D.period).Choices)
    (r k : ℕ) (mode : R.Mode) :
    (D.retag tag).ordinaryCoefficient Y r k mode =
      D.ordinaryCoefficient Y r k mode := by
  simp only [ordinaryCoefficient, ordinary, raw_retag]

end Datum
end YM.Integration.LocalFormal
