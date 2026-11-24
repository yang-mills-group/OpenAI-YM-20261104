import YM.Integration.WilsonMaxwellThermometerFirstRows

/-! The diagonal chiral curl contraction of a symmetric Hessian is its negative
trace; the two different polarizations have zero contraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerTrace
open Maxwell Maxwell.Free XSpace.Chiral WilsonMaxwellThermometerRotations
open scoped BigOperators

private abbrev Row (R : Type*) := Axis → Axis → R
private def read {R : Type*} [CommRing R] (i j : Axis) : Row R →ₗ[R] R where
  toFun X := X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def cellH {R : Type*} [CommRing R] (i j : Axis) : Row R →ₗ[R] R :=
  read (min i j) (max i j)
private def kronecker {R : Type*} [CommRing R] (i j : Axis) : R := if i=j then 1 else 0
private def term {R : Type*} [CommRing R] (a b k m : Axis) : Row R →ₗ[R] R :=
  (kronecker b k : R) • cellH a m - (kronecker b m : R) • cellH a k -
  ((kronecker a k : R) • cellH b m - (kronecker a m : R) • cellH b k)
private def price {R : Type*} [CommRing R] (s : Bool) (a b : P) : Row R →ₗ[R] R :=
  term 0 (shard a) 0 (shard b) + (phase s : R) • term 0 (shard a) (shard (b+1)) (shard (b+2)) +
  (phase s : R) • (term (shard (a+1)) (shard (a+2)) 0 (shard b) +
    (phase s : R) • term (shard (a+1)) (shard (a+2)) (shard (b+1)) (shard (b+2)))
private def due {R : Type*} [CommRing R] (a b : P) : Row R →ₗ[R] R :=
  (if a=b then (-1:R) else 0) • ∑ i : Axis, read i i
private def point {R : Type*} [CommRing R] (k l : Axis) : Row R :=
  fun i j => if k=i ∧ l=j then 1 else 0

private theorem sheet : ∀ (s : Bool) (a b : P) (k l : Axis),
    price s a b (point k l : Row ℤ) = due a b (point k l : Row ℤ) := by decide

private theorem term_apply {A : Type*} [CommRing A] (a b k m : Axis) (X : Row A) :
    term a b k m X =
    kronecker b k * X (min a m) (max a m) - kronecker b m * X (min a k) (max a k) -
    (kronecker a k * X (min b m) (max b m) - kronecker a m * X (min b k) (max b k)) := rfl

private theorem price_apply {A : Type*} [CommRing A] (s : Bool) (a b : P) (X : Row A) :
    price s a b X =
    term 0 (shard a) 0 (shard b) X + (phase s : A) * term 0 (shard a) (shard (b+1)) (shard (b+2)) X +
    (phase s : A) * (term (shard (a+1)) (shard (a+2)) 0 (shard b) X +
      (phase s : A) * term (shard (a+1)) (shard (a+2)) (shard (b+1)) (shard (b+2)) X) := rfl

private theorem due_apply {A : Type*} [CommRing A] (a b : P) (X : Row A) :
    due a b X = (if a=b then (-1:A) else 0) * ∑ i : Axis, X i i := by
  change _ * ((∑ i : Axis, read i i) X) = _
  rw [LinearMap.sum_apply]
  rfl

private theorem term_cast (a b k m u v : Axis) :
    ((term a b k m (point u v : Row ℤ) : ℤ) : ℝ) = term a b k m (point u v : Row ℝ) := by
  simp [term_apply, kronecker, point, Int.cast_ite]


private theorem paid (s : Bool) (a b : P) (k l : Axis) :
    price s a b (point k l : Row ℝ) = due a b (point k l : Row ℝ) := by
  have h:=congrArg ((↑) : ℤ → ℝ) (sheet s a b k l)
  simp only [price_apply, Int.cast_mul, Int.cast_add, term_cast, due_apply] at h ⊢
  simpa [Int.cast_ite, point] using h

private theorem entire (s : Bool) (a b : P) (X : Row ℝ) :
    price s a b X = due a b X := by
  have hx : X = ∑ i : Axis, ∑ j : Axis, X i j • point i j := by
    ext i j
    simp [point, Finset.sum_apply, smul_eq_mul, ite_and, mul_ite]
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, paid]

def curl (X : Axis → Axis → ℝ) (a b k m : Axis) :=
  (if b=k then X a m else 0) - (if b=m then X a k else 0) -
  ((if a=k then X b m else 0) - (if a=m then X b k else 0))

theorem balance (T : Axis → Axis → ℝ) (hs : ∀ i j, T i j=T j i)
    (ht : ∑ i, T i i = 0) (s : Bool) (a b : P) :
    curl T 0 (shard a) 0 (shard b) + sig s * curl T 0 (shard a) (shard (b+1)) (shard (b+2)) +
    sig s * (curl T (shard (a+1)) (shard (a+2)) 0 (shard b) +
      sig s * curl T (shard (a+1)) (shard (a+2)) (shard (b+1)) (shard (b+2))) = 0 := by
  have hs' (i j : Axis) : cellH i j T = T i j := by
    rcases le_total i j with e|e
    · simp [cellH,read,min_eq_left e,max_eq_right e]
    · simpa [cellH,read,min_eq_right e,max_eq_left e] using hs j i
  have ht' (i j k l : Axis) : term i j k l T = curl T i j k l := by
    change ∀ i j : Axis, T (min i j) (max i j) = T i j at hs'
    simp [term_apply, curl, kronecker, ite_mul, hs']
  simpa [price_apply, due_apply, ht', phase_cast, ht] using entire s a b T

end YM.Integration.WilsonMaxwellThermometerTrace
