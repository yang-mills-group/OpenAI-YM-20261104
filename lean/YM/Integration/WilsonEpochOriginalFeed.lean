import YM.Integration.WilsonEpochBookedBatch
import YM.Integration.WilsonEpochCalibratedInsertion

/-! The separately defined RG10 terminal wake of the actual Wilson source,
at all orders, and the independently booked epoch at the same regulator.
The old vacuum is present in the native `FlatFeed.step`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochOriginalFeed

open Function Lattice Wilson XSpace FVA2 FVA2.Arrival FVA2.Register
open FormalOPE.RG10 FormalOPE.RG10.InversionTop PertExtension
open WilsonEpochCylinderDifference WilsonEpochPositionCoefficients
open scoped Classical BigOperators
variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G) (Y : Initialize G)

private theorem word_test (n : Side) (ev : Even n.val) (l : List (Folio G)) :
    Orb.PreTest (word (placed R Y n) l) := by
  induction l with
  | nil => exact Folio.matured Y n [] ev
  | cons s l ih => exact FVA2.Change.pre_pair (placed_valid R Y n s) ih

def row (n : Side) (ev : Even n.val) (l : List (Folio G)) : PowerSeries ℂ :=
  lower (Folio.asset l) ((feed ev).step (vertices G n)
    (raw (Orb.restrictedO (word (placed R Y n) l))))

/-- Equality of whole series; the exponent of each individual Wick term is
its own slot sum. This is the actual independent interaction, not a new
terminal definition by the booked array. -/
theorem identified (n : Side) (ev : Even n.val) (l : List (Folio G)) :
    row R Y n ev l = into (actual R Y n l) := by
  unfold row
  rw [tree_agreement ev (word_test R Y n ev l).curved]
  apply PowerSeries.ext
  intro k
  simp only [lower,actual,PowerSeries.coeff_mk,into_coeff]

private theorem real_scan (p : List (Birth G)) (f : List (Folio G) → PowerSeries ℝ) :
    Birth.scan p (fun l => into (f l)) = into (Birth.scan p f) := by
  induction p generalizing f with
  | nil => rfl
  | cons a p ih =>
    rw [Birth.scan,Birth.scan,map_sum]
    exact Finset.sum_congr rfl fun j _ => ih (fun l => f (a.chooses j :: l))

theorem priced (N : WilsonPrescription G) (i B : ℕ) (P : Handoff.Directory N i B)
    (p : List (Birth G)) (k : ℕ) (hk : Handoff.Directory.requested p + k ≤ B) :
    let n := (N.run.step i).p.side
    let ev : Even n.val := even_iff_two_dvd.mpr (N.run.step i).p.even
    PowerSeries.coeff k (Birth.scan p (row R N.scheme n ev)) -
      Complex.ofReal (PowerSeries.coeff k (P.product p)) =
      Complex.ofReal (PowerSeries.coeff k (Birth.scan p (residual R N.scheme n))) := by
  intro n ev
  rw [show row R N.scheme n ev = (fun l => into (actual R N.scheme n l)) from
    funext (identified R N.scheme n ev),real_scan,into_coeff]
  exact_mod_cast epoch R N i B P p k hk

end YM.Integration.WilsonEpochOriginalFeed
end

