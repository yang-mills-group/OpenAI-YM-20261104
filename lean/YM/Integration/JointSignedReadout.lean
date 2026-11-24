import YM.Cells.Embedded
import YM.Integration.EngineeringWeightedReadout
import YM.Integration.EngineeringWholeHorizon

/-! Signed joint discrepancies are sufficient for the finite physical readout.

Reflection positivity turns a genuine replicated root estimate into a
signed moment estimate.  The original finite readout is then applied with
its exact column costs.  No field-space L1 or coincident residual-square
estimate is inferred from a signed first moment.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.JointSignedReadout
open Lattice Wilson RG Cells EngineeringWeightedReadout
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {β : ℝ}

/-- The native chessboard supplier controls the signed single-cell mean.
Locality in the actual cell is retained as an explicit geometric premise. -/
theorem moment_norm_le_rootTest (T : Tiling n) (hβ : 0 ≤ β)
    {F : Config G n → ℂ} (hF : Interior (T.chamber 0) F) :
    ‖moment β F‖ ≤ T.rootTest β F := by
  have h := T.planted (Cells.laws G n β hβ) (fun _ : Unit => 0)
    (Function.injective_of_subsingleton _) (fun _ : Unit => F) (fun _ => hF)
  simpa only [Fintype.prod_unique, Tiling.copy_zero] using h

variable {I Y : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Keep every actual readout column, including any engineering inverse.
The root estimates concern complete joint observables under one law. -/
theorem readout_norm_le_root_columns (L : (I → ℂ) →L[ℂ] Y)
    (T : I → Tiling n) (hβ : 0 ≤ β) (F : I → Config G n → ℂ)
    (hF : ∀ i, Interior ((T i).chamber 0) (F i)) :
    ‖L (fun i => moment β (F i))‖ ≤
      columnPrice L (fun i => (T i).rootTest β (F i)) :=
  column_bound L _ _ (fun i => moment_norm_le_rootTest (T i) hβ (hF i))

/-- Apply any paid native root bounds without taking field-space absolute
values before integration. This retains the cost of each original column. -/
theorem readout_norm_le_paid_columns (L : (I → ℂ) →L[ℂ] Y)
    (T : I → Tiling n) (hβ : 0 ≤ β) (F : I → Config G n → ℂ)
    (hF : ∀ i, Interior ((T i).chamber 0) (F i))
    (a : I → ℝ) (ha : ∀ i, (T i).rootTest β (F i) ≤ a i) :
    ‖L (fun i => moment β (F i))‖ ≤ columnPrice L a :=
  column_bound L _ _ (fun i => (moment_norm_le_rootTest (T i) hβ (hF i)).trans (ha i))

section Actual
open Spec OPE PhysMS
variable {C : Family G} {S : Table C.book} {D N p : ℕ}

/-- On the original Family, signed replicated bounds feed the exact
whole-horizon detector inverse. The displayed root-column price still
has to be paid; an unweighted scalar error is not promoted automatically. -/
theorem wholeReadout_signed_actual (hC : C.Makes)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (r : ℝ)
    (T : Fin U.size → Tiling (C.side N p))
    (F : Fin U.size → Config G (C.side N p) → ℂ)
    (hF : ∀ i, Interior ((T i).chamber 0) (F i)) :
    ‖wholeReadout U J r (fun i => moment (C.beta N p) (F i))‖ ≤
      columnPrice (wholeReadout U J r)
        (fun i => (T i).rootTest (C.beta N p) (F i)) := by
  have hβ : 0 ≤ C.beta N p := (Overlay.beta_positive hC.wilson le_rfl).le
  exact readout_norm_le_root_columns (wholeReadout U J r) T hβ F hF

end Actual
end YM.Integration.JointSignedReadout
