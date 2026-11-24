import YM.FVA2.MixedRates

/-! Rectangular engineering-horizon induction for the complete marked
two-point coefficients over a ring of controlled cutoff germs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSGradedReceiverRigidity

open Matrix
open scoped Classical Matrix

variable {S K : Type*} [CommRing S] [CommRing K]
variable {I J L : Type*} [Fintype I] [DecidableEq I] [Fintype J]

omit [Fintype I] [DecidableEq I] in
theorem same {a b : Matrix L I S} (f : S →+* K) (hf : Function.Injective f)
    (h : a.map f = b.map f) : a = b := by
  ext i j
  exact hf (congrFun (congrFun h i) j)

theorem low (u a b : Matrix I I S) (h : b = u * a * u.transpose) (hb : IsUnit b.det) :
    IsUnit u.det := by
  rw [h, Matrix.det_mul, Matrix.det_mul] at hb
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hb)

theorem inverse_right (f : S →+* K) (a : Matrix I I S) (ha : IsUnit a.det) :
    a.map f * (a⁻¹).map f = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ ha]
  exact map_one (f.mapMatrix (m := I))

/-- Use the actual two receiver tables. The high input and top canonical
port may be independently rectangular. No invariance of the changing
input field enters the solve. -/
theorem rectangle (f : S →+* K)
    (u a b : Matrix I I S) (h : b = u * a * u.transpose) (hb : IsUnit b.det)
    (ha : IsUnit a.det) (d : Matrix L J S) (k : Matrix J I S) (l : Matrix L I S)
    (x : Matrix L I K)
    (hm : l.map f = (x * a.map f + (d*k).map f) * u.transpose.map f) :
    ∃ y : Matrix L I S, x = y.map f := by
  have hu : IsUnit u.transpose.det := by
    rw [Matrix.det_transpose]
    exact low u a b h hb
  let v := (u.transpose)⁻¹
  have go : u.transpose.map f * v.map f = 1 := inverse_right f _ hu
  have ho : a.map f * (a⁻¹).map f = 1 := inverse_right f a ha
  let y := (l * v - d*k) * a⁻¹
  refine ⟨y, ?_⟩
  change x = ((l * v - d*k) * a⁻¹).map f
  rw [Matrix.map_mul, Matrix.map_sub f (map_sub f), Matrix.map_mul, hm,
    Matrix.mul_assoc, go, Matrix.mul_one, add_sub_cancel_right, Matrix.mul_assoc,
    ho, Matrix.mul_one]

/-- A genuine measured matrix whose formal head is a unit over the
controlled ring is a unit over its full series ring. -/
theorem formal (a : Matrix I I (PowerSeries S))
    (ha : IsUnit ((PowerSeries.constantCoeff (R := S)).mapMatrix a).det) :
    IsUnit a.det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, (PowerSeries.constantCoeff (R := S)).map_det]
  exact ha

end YM.Integration.MSGradedReceiverRigidity
