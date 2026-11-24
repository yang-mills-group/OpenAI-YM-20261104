import YM.Integration.WilsonGraphAppointedNumeratorTranslation

/-! Centering the singleton near point preserves both physical sites and their original fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedOneNear

open Function Real Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YM.Answer.ContinuumLimit YM.OPE YM.OPE.Orbits
open scoped Topology BigOperators Classical

variable {G : Gauge} {R : Family G} {f : Extraction.Order} {P : Table R.book}
variable (U : Spec.Final R f P) (J : Physical.FramesH P)
variable {m : ℕ} {d : Fin 1 → ℕ} {e : Fin m → ℕ}

def exterior (s : ℝ) (x : Points 1) (y : Points m) : Points m :=
  WithLp.toLp 2 fun j => y j - Real.exp (-s) • x 0

/-- The far displacement cancels the change of center, at the actual coarse radius. -/
theorem sites (w : Window) (o : E4) (x : Points 1) (y : Points m) :
    Physical.atPos w.len o x = Physical.atPos w.len (o+w.len • x 0) (0 : Points 1) ∧
    Physical.atPos w.Coarse o y = Physical.atPos w.Coarse (o+w.len • x 0) (exterior w.sep x y) := by
  have factors : w.Coarse * Real.exp (-w.sep) = w.len := by
    change w.len * Real.exp w.sep * Real.exp (-w.sep) = w.len
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  constructor
  · funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    change o + w.len • x 0 = o + w.len • x 0 + w.len • (0:E4)
    simp
  · funext j
    change o + w.Coarse • y j = o + w.len • x 0 + w.Coarse • (y j - Real.exp (-w.sep) • x 0)
    rw [smul_sub,smul_smul,factors]
    abel

/-- Reanchor the singleton numerator with the same fields, birth radii and viewer. -/
theorem physical (w : Window) (phase : Viewers U) (o : E4) (x : Points 1)
    (y : Points m) (u : Inputs G d) (v : Inputs G e) :
    Physical.Y0 U J d e w (phase,o) x y u v =
      Physical.Y0 U J d e w (phase,o+w.len • x 0) 0 (exterior w.sep x y) u v := by
  rw [Physical.Y0_value,Physical.Y0_value]
  change whole (spectator U phase) (Physical.atPos w.len o x) (Physical.here J w.len u)
      (Physical.atPos w.Coarse o y) (Physical.here J w.len v) =
    whole (spectator U phase) (Physical.atPos w.len (o+w.len • x 0) (0 : Points 1))
      (Physical.here J w.len u) (Physical.atPos w.Coarse (o+w.len • x 0) (exterior w.sep x y))
      (Physical.here J w.len v)
  rw [(sites w o x y).1,(sites w o x y).2]

end YM.FVA2.GradedFar.AppointedOneNear
end

