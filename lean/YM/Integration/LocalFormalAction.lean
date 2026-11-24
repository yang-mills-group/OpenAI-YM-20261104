import YM.Integration.LocalFormalCoefficients
import YM.Comparison.RG02.Adjacent.Actual
import YM.Comparison.RG02.Adjacent.Attached

/-!
The complete local formal vacuum-action bank on the fixed Datum and Chain.
The canonical pre-reset bank is native `Orbit.ground`: the leading infrared
quadratic price plus the ordinary coefficients of logVac(Fk). The price is
present at order zero, so this bank is not bare logVac.

A reset bank always takes an explicit caller-supplied Caliber. None of these
identities identifies that Caliber with the actual beta ratio, identifies a
Plan predictor, or converts the input Colors.vac (inside g^-2 localClassic)
into an unscaled output action. Those remain separate physical bindings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalFormal
open RG Lattice Wilson Exterior Tree Marker
open Comparison.RG02
open scoped Classical

namespace Datum
variable {G : Gauge} {C : Family G}
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    (D : Datum C R) (Y : Bulk.Chain C.path)

/-- The complete independently prescribed local vacuum-action coefficients,
including the leading infrared quadratic contribution. -/
def vacuumAction (r : ℕ) : Adjacent.Display (fieldDir G (C.side D.level D.period) 1) :=
  Symmetry.Orbit.ground (D.kernel Y) D.forest D.tag D.colors r

/-- Re-expression in a specified formal output coupling. The Caliber is
explicit data; no equality with the actual trajectory is inferred. -/
def resetVacuumAction (cal : Adjacent.Caliber) (r : ℕ) :
    Adjacent.Display (fieldDir G (C.side D.level D.period) 1) :=
  Adjacent.born (D.vacuumAction Y r) (cal.back r) 0 r

theorem vacuumAction_coefficient (r k : ℕ)
    (A : fieldDir G (C.side D.level D.period) 1) :
    D.vacuumAction Y r k A =
      ({D with field := A} : Datum C R).vacuumLogCoefficient Y r k R.quiet +
        if k = 0 then Symmetry.price (D.kernel Y) D.forest D.tag A else 0 := rfl

theorem vacuumAction_zero (r : ℕ)
    (A : fieldDir G (C.side D.level D.period) 1) :
    D.vacuumAction Y r 0 A = Symmetry.price (D.kernel Y) D.forest D.tag A :=
  Adjacent.LocalScript.precedence (D.kernel Y) D.forest D.tag D.colors r A

theorem vacuumAction_nonzero (r k : ℕ) (hk : k ≠ 0)
    (A : fieldDir G (C.side D.level D.period) 1) :
    D.vacuumAction Y r k A =
      ({D with field := A} : Datum C R).vacuumLogCoefficient Y r k R.quiet := by
  rw [D.vacuumAction_coefficient Y r k A, if_neg hk, add_zero]

theorem vacuumAction_degree (r k : ℕ) (hk : k ≤ r) :
    Valence.Level ((k : ℤ) + 2) (D.vacuumAction Y r k) :=
  Adjacent.LocalScript.rank (D.kernel Y) D.forest D.tag D.colors r k hk

/-- The native scalar normalization removes precisely the leading price
already present in the full action bank. -/
theorem vacuumAction_cover (r : ℕ) (g : ℝ) :
    Order.exponentPrice (D.raw Y r) g =
      (Adjacent.cover (D.vacuumAction Y r) r g D.field).re -
        (Symmetry.price (D.kernel Y) D.forest D.tag D.field).re :=
  Adjacent.RealStep.price_cover (D.kernel Y) D.forest D.tag D.colors D.field g r

theorem resetVacuumAction_zero_eq (cal : Adjacent.Caliber) (r : ℕ) :
    D.resetVacuumAction Y cal r 0 = D.vacuumAction Y r 0 := by
  exact Adjacent.Attach.remains0
    (K := D.kernel Y) (F := D.forest) (w := D.tag) (W := D.colors) (C := cal) (r := r)

theorem resetVacuumAction_one_eq (cal : Adjacent.Caliber) (r : ℕ)
    (he : cal.EvenK r) (hr : 1 ≤ r) :
    D.resetVacuumAction Y cal r 1 = D.vacuumAction Y r 1 := by
  exact Adjacent.Attach.remains1
    (K := D.kernel Y) (F := D.forest) (w := D.tag) (W := D.colors) (C := cal) (r := r)
    he hr

/-- The explicit second-order reset subtracts the caller's kinetic readout
coefficient times the same leading action. -/
theorem resetVacuumAction_two_eq (cal : Adjacent.Caliber) (r : ℕ)
    (he : cal.EvenK r) (hr : 2 ≤ r) :
    D.resetVacuumAction Y cal r 2 =
      D.vacuumAction Y r 2 - (cal.measure 2 : ℂ) • D.vacuumAction Y r 0 := by
  exact Adjacent.Attach.ante
    (K := D.kernel Y) (F := D.forest) (w := D.tag) (W := D.colors) (C := cal) (r := r)
    he hr

/-- The zero-order term is the quadratic jet of this same actual output
path, independently of the caller's Caliber. -/
theorem resetVacuumAction_actual_quadratic (cal : Adjacent.Caliber) (r : ℕ)
    (A : fieldDir G (C.side D.level D.period) 1) :
    D.resetVacuumAction Y cal r 0 A =
      -Complex.ofReal (Assembly.jet
        (Extra.Iteration.Calibration.main
          (C.path.rep D.cutoff D.period D.level).path
          (C.path.rep D.cutoff D.period D.level).clip) 2 A) := by
  exact Adjacent.Attach.zero_kinetic
    (C := cal) (r := r) (K' := Y) (N := D.cutoff) (m := D.level) (q := D.period)
    (h := D.below) (F := D.forest) (t := D.tag) (W := D.colors) (x := A)

/-- For standard input colors and an even Caliber, the first coefficient
is the cubic jet of the same actual output path. -/
theorem resetVacuumAction_actual_cubic (cal : Adjacent.Caliber) (r : ℕ)
    (hr : 1 ≤ r) (he : cal.EvenK r) (hW : D.colors.Standard) (hG : G.Simple)
    (A : fieldDir G (C.side D.level D.period) 1) :
    D.resetVacuumAction Y cal r 1 A =
      -Complex.ofReal (Assembly.jet
        (Extra.Iteration.Calibration.main
          (C.path.rep D.cutoff D.period D.level).path
          (C.path.rep D.cutoff D.period D.level).clip) 3 A) := by
  exact Adjacent.Attach.first_kinetic
    (C := cal) (r := r) (K' := Y) (N := D.cutoff) (m := D.level) (q := D.period)
    (h := D.below) (F := D.forest) (t := D.tag) (W := D.colors) (x := A)
    (he := hW) hr he hG

end Datum
end YM.Integration.LocalFormal
