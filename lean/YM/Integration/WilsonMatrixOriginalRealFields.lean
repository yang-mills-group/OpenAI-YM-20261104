import YM.Integration.WilsonInvariantActionIntegratedPair

/-! Real and imaginary field labels at the original finite-volume reporter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalRealFields
open Lattice Wilson RG PhysicalNext.Repeat.Legato
variable {G : Gauge} {R : Run G} {d N p : ℕ}

def realLabel (a : R.family.label d) : R.family.label d :=
  (2 : ℂ)⁻¹ • (a + star a)

def imagLabel (a : R.family.label d) : R.family.label d :=
  (2 * Complex.I)⁻¹ • (a - star a)

theorem real_at (a : R.family.label d) (h : R.family.ref d ≤ N)
    (x : Site (R.family.side N p)) (U : Config G (R.family.side N p)) :
    R.family.O N p (realLabel a) x U = ((R.family.O N p a x U).re : ℂ) := by
  rw [realLabel,(R.family.linearO N p d x).map_smul,(R.family.linearO N p d x).map_add]
  change (2 : ℂ)⁻¹ * (R.family.O N p a x U + R.family.O N p (star a) x U) = _
  rw [R.family.reality R.makes h, Complex.re_eq_add_conj]
  exact mul_comm _ _

theorem imag_at (a : R.family.label d) (h : R.family.ref d ≤ N)
    (x : Site (R.family.side N p)) (U : Config G (R.family.side N p)) :
    R.family.O N p (imagLabel a) x U = ((R.family.O N p a x U).im : ℂ) := by
  rw [imagLabel,(R.family.linearO N p d x).map_smul,(R.family.linearO N p d x).map_sub]
  change (2 * Complex.I)⁻¹ * (R.family.O N p a x U - R.family.O N p (star a) x U) = _
  rw [R.family.reality R.makes h, Complex.im_eq_sub_conj]
  exact mul_comm _ _

end YM.Integration.WilsonMatrixOriginalRealFields
