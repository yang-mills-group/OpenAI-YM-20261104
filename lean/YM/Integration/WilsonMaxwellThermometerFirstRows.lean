import YM.Integration.WilsonMaxwellThermometerRotations

/-! Exact angular average of a differentiated chiral curvature. Its off-shell
defect is one divergence or curl equation on each concrete component. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonMaxwellThermometerFirstRows
open Function XSpace.Chiral WilsonMaxwellThermometerRotations WilsonMaxwellThermometerJets
open scoped BigOperators

abbrev Array1 (R : Type*) := Axis → P → R

def read {R : Type*} [CommRing R] (k : Axis) (a : P) : Array1 R →ₗ[R] R where
  toFun X := X k a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evol {R : Type*} [CommRing R] (s : Bool) (a : P) : Array1 R →ₗ[R] R :=
  read 0 a - (phase s : R) • (read (shard (a+1)) (a+2) - read (shard (a+2)) (a+1))

def divg {R : Type*} [CommRing R] : Array1 R →ₗ[R] R := ∑ a : P, read (shard a) a

def residual {R : Type*} [CommRing R] (s : Bool) (a : P) (k : Axis) : Array1 R →ₗ[R] R :=
  if k=0 then evol s a
  else if k=shard a then divg
  else if k=shard (a+1) then (phase s : R) • evol s (a+2)
  else -(phase s : R) • evol s (a+1)

def entryBasis {R : Type*} [CommRing R] (l : Axis) (b : P) : Array1 R :=
  fun k a => if k=l ∧ a=b then 1 else 0

private lemma clock {R : Type*} [CommRing R] (F : Array1 R →ₗ[R] R) (X : Array1 R) :
    ∑ l : Axis, ∑ b : P, F (entryBasis l b) * X l b = F X := by
  have he : X = ∑ l : Axis, ∑ b : P, X l b • (entryBasis l b : Array1 R) := by
    ext k a
    simp [entryBasis, Finset.sum_apply, smul_eq_mul, ite_and, mul_ite]
  conv_rhs => rw [he]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

private lemma cast_evol (s : Bool) (a : P) (l : Axis) (b : P) :
    ((evol s a (entryBasis l b : Array1 ℤ) : ℤ) : ℝ) =
      evol s a (entryBasis l b : Array1 ℝ) := by
  simp [evol, read, entryBasis, smul_eq_mul, Int.cast_ite]

private lemma cast_residual (s : Bool) (a : P) (k l : Axis) (b : P) :
    ((residual s a k (entryBasis l b : Array1 ℤ) : ℤ) : ℝ) =
      residual s a k (entryBasis l b : Array1 ℝ) := by
  unfold residual
  split_ifs <;> simp [cast_evol, divg, read, entryBasis, smul_eq_mul]

private theorem booked :
    ∀ (s : Bool) (a : P) (k l : Axis) (b : P),
      ∑ n : Ticket, entry s n l k * spin s s n a b =
        16 * (residual s a k (entryBasis l b : Array1 ℤ) - entryBasis l b k a) := by decide

theorem charge (s : Bool) (a : P) (k l : Axis) (b : P) :
    (∑ n : Ticket, (entry s n l k : ℝ) * (spin s s n a b : ℝ)) =
      16 * (residual s a k (entryBasis l b : Array1 ℝ) - entryBasis l b k a) := by
  have h := congrArg (Int.cast : ℤ → ℝ) (booked s a k l b)
  push_cast [cast_residual, entryBasis] at h
  simpa only [entryBasis] using h

theorem discharged (s : Bool) (a : P) (k : Axis) (X : Array1 ℝ) (h : Equations s X) :
    residual s a k X = 0 := by
  have ev (b : P) : evol s b X = 0 := by
    change X 0 b - (phase s : ℝ)*(X (shard (b+1)) (b+2) - X (shard (b+2)) (b+1)) = 0
    rw [phase_cast, h.evolution, sub_self]
  have di : divg X = 0 := by simpa [divg, read] using h.divergence
  unfold residual
  split_ifs <;> simp [ev, di]

/-- In the doubled matrix convention each summand has denominator eight. -/
theorem measured (s : Bool) (a : P) (k : Axis) (X : Array1 ℝ) (h : Equations s X) :
    (∑ l : Axis, ∑ b : P, (∑ n : Ticket, (entry s n l k : ℝ) * (spin s s n a b : ℝ)) *
      X l b) = -16 * X k a := by
  simp_rw [charge, mul_assoc, sub_mul, ← Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib]
  rw [clock]
  have hh : ∑ l : Axis, ∑ b : P, entryBasis l b k a * X l b = X k a := by
    exact clock (read k a) X
  rw [hh, discharged s a k X h]
  ring

end YM.Integration.WilsonMaxwellThermometerFirstRows
