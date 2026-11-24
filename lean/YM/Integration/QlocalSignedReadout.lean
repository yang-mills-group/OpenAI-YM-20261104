import YM.Integration.QlocalOrientedTests
import YM.Integration.NativeCalibrationMoodReadout
import YM.Extra.SOURCE_HISTORIES.Motion

/-! Signed native test readers in the original independent test coordinates.
Conjugation occurs on both sides of the original complex-linear reader;
no reality property of its arbitrary coefficient basis is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QlocalSignedReadout
open Function Lattice Source ComparisonDensity.Address Extra.Histories
open QlocalOrientedTests NativeCalibrationMoodReadout RG05Readout.Native
open scoped Classical

private def conjugated (U : Orbit) (L : U.Mood →ₗ[ℂ] ℂ) : U.Mood →ₗ[ℂ] ℂ where
  toFun f := star (L (conjugateMood U f))
  map_add' f g := by rw [conjugateMood_add, map_add, star_add]
  map_smul' c f := by
    rw [conjugateMood_smul, map_smul]
    change star (star c * L (conjugateMood U f)) = c * star (L (conjugateMood U f))
    simp only [star_mul, star_star, mul_comm]

/-- The original orientation acts after the original reader and constant. -/
def linear (U : Orbit) (t : Motion) (c : ℂ) (L : U.Mood →ₗ[ℂ] ℂ) :
    U.Mood →ₗ[ℂ] ℂ :=
  if t.2 then star c • conjugated U L else c • L

theorem linear_apply (U : Orbit) (t : Motion) (c : ℂ)
    (L : U.Mood →ₗ[ℂ] ℂ) (f : U.Mood) :
    linear U t c L f = Motion.scalar t (c * L (orientedMood U t.2 f)) := by
  cases h : t.2 <;>
    simp [linear, Motion.scalar, orientedMood, h, conjugated, star_mul, mul_comm]

/-- Orienting the original test back recovers the literal signed amplitude. -/
theorem linear_recover (U : Orbit) (t : Motion) (c : ℂ)
    (L : U.Mood →ₗ[ℂ] ℂ) (f : U.Mood) :
    linear U t c L (orientedMood U t.2 f) = Motion.scalar t (c * L f) := by
  rw [linear_apply, orientedMood_involutive U t.2 f]

def native (U : Orbit) (t : Motion) (c : ℂ) {d : ℕ}
    (i : Letter d) (hi : depth i ≤ U.D) (δ : E4) (r : ℝ) :
    U.Mood →ₗ[ℂ] ℂ := linear U t c (readout U i hi δ r)

/-- Every independent test keeps its own original Bill, with the coordinate,
factorial, affine-scale and scalar factors displayed. -/
theorem native_bound (U : Orbit) (t : Motion) (c : ℂ) {d : ℕ}
    (i : Letter d) (hi : depth i ≤ U.D) (δ : E4) {r : ℝ} (hr : 0 ≤ r)
    (f : U.Mood) {b : ℝ} (hf : U.Bill f.val b)
    (hδ : ActualRunCalibrationTests.coordinates.symm δ ∈ U.scope) :
    ‖native U t c i hi δ r f‖ ≤
      ‖c‖ * (r ^ depth i * (coordinateCost (depth i) *
        (U.height (ActualRunCalibrationTests.coordinates.symm δ) * b))) := by
  have hOriented : U.Bill (orientedMood U t.2 f).val b := by
    cases t.2
    · exact hf
    · exact bill_conjugate hf
  change ‖linear U t c (readout U i hi δ r) f‖ ≤ _
  rw [linear_apply, Motion.norm_scalar, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (readout_bound U i hi δ hr (orientedMood U t.2 f) hOriented hδ) (norm_nonneg c)

theorem native_recover (U : Orbit) (t : Motion) (c : ℂ) {d : ℕ}
    (i : Letter d) (hi : depth i ≤ U.D) (δ : E4) (r : ℝ) (f : U.Mood) :
    native U t c i hi δ r (orientedMood U t.2 f) =
      Motion.scalar t (c * readout U i hi δ r f) :=
  linear_recover U t c (readout U i hi δ r) f

end YM.Integration.QlocalSignedReadout
