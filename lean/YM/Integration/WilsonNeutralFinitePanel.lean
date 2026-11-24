import YM.Integration.WilsonNeutralGradeFourTransport
import YM.Integration.ActualOriginalFiniteCoefficients
import YM.PertExtension.OrbParity

/-! Finite Wilson two-field sensors on the measured fourth-horizon columns.
We freeze their numerical coordinates before taking coefficients in the
independent bare Wilson program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralFinitePanel
open Function Lattice Wilson RG Source Cells PhysicalNext.Repeat.Legato
open Pert PertExtension FVAAlt2 WilsonNeutralGradeFourTransport WilsonPositionThermometerCapStation
open WilsonOriginalThermometerPalette WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p : ℕ}
local notation "n" => R.family.side N p
local notation "V" => R.family.label 4

def field {j : ℕ} (ref : R.family.ref 4 ≤ j) (top : j ≤ N) (x : V) (b : Site n) : Config G n → ℂ :=
  R.family.O N p ((atDate R (p:=p) j ref top).symm x) b

theorem filed {j : ℕ} (ref : R.family.ref 4 ≤ j) (top : j ≤ N) (b : Site n)
    (A : Group R.family 6) (leg : Fin 2) :
    field R ref top (coordinates R A j N p leg.succ) b =
      R.family.O N p (A.station.wheel.atCut (N,p) (index A (grade leg.succ)) (vector A Finset.univ leg.succ)) b := by
  unfold field
  change R.family.O N p ((atDate R (p:=p) j ref top).symm ((atDate R (p:=p) j ref top) _)) b = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Co-filing on the same cutoff is a pointwise change of the numerical
coordinates of the original observable, including its constant entry. -/
theorem common_top {m j : ℕ} (ref : R.family.ref 4 ≤ m) (mj : m ≤ j) (jt : j ≤ N)
    (x : V) (b : Site n) :
    field R ref (mj.trans jt) (transfer R (p:=p) ref mj jt x) b =
      field R (ref.trans mj) jt x b := by
  change R.family.O N p ((atDate R (p:=p) m ref (mj.trans jt)).symm
    ((atDate R (p:=p) m ref (mj.trans jt)) _)) b = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- A reflected detector on the same complete finite Wilson action. Its
two numerical columns may be filed at different dates and positions. -/
def panel {i j : ℕ} (ri : R.family.ref 4 ≤ i) (it : i ≤ N) (rj : R.family.ref 4 ≤ j)
    (jt : j ≤ N) (x y : V) (b c : Site n) (slotCount order : ℕ) : ℂ :=
  let F := fun U => star (field R ri it x b U) * field R rj jt y c U
  let part := fun (f : Config G n → ℝ) => Fixed.treeMom R.metals.O f slotCount order
  ⟨part (fun U => (F U).re), part (fun U => (F U).im)⟩

/-- Exact independent finite coefficients when a frozen true upper
operand is moved to the lower file. The other addressed column can
be any admitted measured fourth-horizon field on its own date. -/
theorem common_read {k m j : ℕ} (rk : R.family.ref 4 ≤ k) (kt : k ≤ N) (rm : R.family.ref 4 ≤ m)
    (mj : m ≤ j) (jt : j ≤ N) (x y : V) (b c : Site n) (r d : ℕ) :
    panel R rk kt rm (mj.trans jt) x (transfer R (p:=p) rm mj jt y) b c r d =
      panel R rk kt (rm.trans mj) jt x y b c r d := by
  unfold panel
  rw [common_top R rm mj jt y c]

/-- On each actual even period the linear bare-coupling coefficient of
every such row vanishes after any even total restoration of source slots.
Both ordinary columns retain their scalar terms. -/
theorem odd {i j : ℕ} (ri : R.family.ref 4 ≤ i) (it : i ≤ N) (rj : R.family.ref 4 ≤ j)
    (jt : j ≤ N) (x y : V) (b c : Site n) (rank order : ℕ)
    (hr : Even rank) (ho : Odd order) :
    panel R ri it rj jt x y b c rank order = 0 := by
  have evenSide := even_iff_two_dvd.mpr (ActualOriginalFiniteCoefficients.side_admissible R N p).2
  have h := ho.add_even hr
  exact Complex.ext (Orb.normalized_odd R.alloy.B.ratio evenSide _ h)
    (Orb.normalized_odd R.alloy.B.ratio evenSide _ h)

end YM.Integration.WilsonNeutralFinitePanel
