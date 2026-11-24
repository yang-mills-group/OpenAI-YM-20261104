import YM.Integration.QlocalNativeTests
import YM.Integration.NativeCalibrationMoodReadout
import YM.RG05Readout.Flatten.Joints

/-! Restriction of the existing finite-jet reader to every original native
smooth test. The full real coordinate pullback cancels exactly, and the
native feeR translation and inverse-count scale are kept literally.
No inverse from arbitrary finite-smooth Mood to smooth Body is asserted. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.QlocalNativeReadout
open Function Lattice Tensor RG05Readout.Native RG05Readout.Nuclear
open ComparisonDensity.Address
open scoped ContDiff Classical

/-- The two existing coordinate definitions are the same literal map. -/
theorem native_field (D w : ℕ) (f : Body) {c : ℝ}
    (h : Tall (E := E4) f D 1 c) :
    (QlocalNativeTests.nativeTest D w f h).val ∘
      ActualRunCalibrationTests.coordinates.symm = f.val := by
  funext x
  change f.val (QlocalNativeTests.coordinates
    (ActualRunCalibrationTests.coordinates.symm x)) = f.val x
  change f.val (ActualRunCalibrationTests.coordinates
    (ActualRunCalibrationTests.coordinates.symm x)) = f.val x
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The existing readout agrees with original readJ on an arbitrary native
test, including the exact affine derivative scale and original basis. -/
theorem readout_native (D w : ℕ) (f : Body) {c : ℝ}
    (h : Tall (E := E4) f D 1 c) {d : ℕ} (i : Letter d)
    (hi : depth i ≤ D) (δ : E4) (r : ℝ) :
    NativeCalibrationMoodReadout.readout (QlocalNativeTests.orbit D w)
      i hi δ r (QlocalNativeTests.nativeTest D w f h) =
        readJ i 0 (pull δ r f) := by
  rw [readJ, rate_consider]
  simp only [smul_zero, add_zero]
  change ((r ^ depth i : ℝ) : ℂ) • (_ : ℂ) = ((r ^ depth i : ℝ) : ℂ) • (_ : ℂ)
  apply congrArg (fun z : ℂ => ((r ^ depth i : ℝ) : ℂ) • z)
  change (writeC (depth i) _) i.2 = (writeC (depth i) _) i.2
  apply congrArg (fun T : Orb (depth i) => (writeC (depth i) T) i.2)
  apply Subtype.ext
  change Tensor.coeff
      ((QlocalNativeTests.nativeTest D w f h).val ∘
        ActualRunCalibrationTests.coordinates.symm) (depth i) δ =
    Tensor.coeff f.val (depth i) δ
  rw [native_field D w f h]

/-- The same restriction at the exact original feeR position and scale. -/
theorem readout_feeR {n m : Side} (q : Ratio n m) (y : Site q.count)
    (D w : ℕ) (f : Body) {c : ℝ} (h : Tall (E := E4) f D 1 c)
    {d : ℕ} (i : Letter d) (hi : depth i ≤ D) :
    NativeCalibrationMoodReadout.readout (QlocalNativeTests.orbit D w)
      i hi (RG05Readout.Flatten.placeR q y) ((q.count.val : ℝ)⁻¹)
      (QlocalNativeTests.nativeTest D w f h) =
        readJ i 0 (RG05Readout.Flatten.feeR q y f) :=
  readout_native D w f h i hi _ _

end YM.Integration.QlocalNativeReadout
