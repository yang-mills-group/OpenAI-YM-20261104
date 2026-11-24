import YM.WilsonCoeffUV.Series.Covariance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The two finite forest charts have different quiet Taylor series.  This
change of integration coordinates uses both of them, the right-Haar
Jacobian, and the same external coarse field.  A common quiet term survives
in the unnormalized moment and cancels in every marked vacuum quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalTwoChartMarkedWick
open YM.WilsonCoeffUV.Blue Matrix PowerSeries
open scoped BigOperators

variable {U Y : Type*} [Fintype U] [DecidableEq U] [Fintype Y]

private lemma zero_after {A B : Type*} [CommRing A] [CommRing B]
    (f : PowerSeries A →+* PowerSeries B) (hx : f X = X)
    {x : PowerSeries A} (h : constantCoeff x = 0) : constantCoeff (f x) = 0 := by
  apply X_dvd_iff.mp
  rw [← hx]
  exact map_dvd f (X_dvd_iff.mpr h)

/-- The action arguments `Tₐ,Tₗ` use the positive action convention. `b`
is a common external change in their normalization. All density and area
identities are statements before integration. -/
theorem moment (K : Matrix U U ℝ) (hK : K.transpose = K) (hdet : IsUnit K.det)
    (θ : U → Ink (U ⊕ Y))
    (lead : ∀ i, constantCoeff (θ i) = constantCoeff (noiseLine (1 : Matrix U U ℝ) i))
    (Jₐ Jₗ Tₐ Tₗ Pₐ Pₗ : Ink (U ⊕ Y)) (b : Ink Y)
    (jₐ : constantCoeff Jₐ = 0) (jₗ : constantCoeff Jₗ = 0)
    (pₐ : constantCoeff Pₐ = 0) (pₗ : constantCoeff Pₗ = 0)
    (hb : constantCoeff b = 0)
    (left : Pₐ = Jₐ - Tₐ + bodyQ Y K) (right : Pₗ = Jₗ - Tₗ + bodyQ Y K)
    (action : Tₐ = reroll path θ Tₗ + holdUp U b)
    (area : (motionJ θ).det * raiseE (reroll path θ Jₗ) = raiseE Jₐ)
    (Aₐ Aₗ : Ink (U ⊕ Y)) (field : Aₐ = reroll path θ Aₗ) :
    Wick Y K⁻¹ (raiseE Pₗ * Aₗ) = raiseE b * Wick Y K⁻¹ (raiseE Pₐ * Aₐ) := by
  let φ := reroll (path (U := Y)) θ
  let F := bodyQ Y K - φ (bodyQ Y K)
  have hx : φ X = X := by simp [φ, reroll]
  have hu : holdUp U (X : Ink Y) = X := by simp [holdUp]
  have hb' : constantCoeff (holdUp U b) = 0 := zero_after _ hu hb
  have hp' : constantCoeff (φ Pₗ) = 0 := zero_after _ hx pₗ
  have hj' : constantCoeff (φ Jₗ) = 0 := zero_after _ hx jₗ
  have tri : K = (1 : Matrix U U ℝ).transpose * K * 1 := by simp
  have hF : constantCoeff F = 0 := local_zero_roll (1 : Matrix U U ℝ) path lead tri
  have balance : Jₐ + (F + φ Pₗ) = holdUp U b + Pₐ + φ Jₗ := by
    rw [left, right, action]
    simp only [F, map_add, map_sub]
    abel
  have ex : raiseE Jₐ * (raiseE F * raiseE (φ Pₗ)) =
      (raiseE (holdUp U b) * raiseE Pₐ) * raiseE (φ Jₗ) := by
    rw [← raise_add hF hp', ← raise_add jₐ (by simp [hF, hp']),
      ← raise_add hb' pₐ, ← raise_add (by simp [hb', pₐ]) hj', balance]
  have den : (motionJ θ).det * (raiseE F * raiseE (φ Pₗ)) =
      raiseE (holdUp U b) * raiseE Pₐ := by
    apply ((raise_unit hj').mul_left_inj).mp
    calc
      _ = ((motionJ θ).det * raiseE (φ Jₗ)) * (raiseE F * raiseE (φ Pₗ)) := by ring
      _ = _ := (congrArg (· * (raiseE F * raiseE (φ Pₗ))) area).trans ex
  have pull : (motionJ θ).det * (raiseE F * φ (raiseE Pₗ * Aₗ)) =
      (raiseE Pₐ * Aₐ) * holdUp U (raiseE b) := by
    rw [map_mul, raise_map φ (by simp [hx]) pₗ, ← mul_assoc (raiseE F),
      ← mul_assoc (motionJ θ).det, den, ← field, raise_map _ (by simp [hu]) hb]
    ring
  have symm : K⁻¹.transpose = K⁻¹ := by rw [transpose_nonsing_inv, hK]
  have change := W_covariance symm hK (Matrix.mul_nonsing_inv K hdet) symm
    (raiseE Pₗ * Aₗ) (1 : Matrix U U ℝ) (by simp) tri (by simp) θ path lead
  change Wick Y K⁻¹ ((motionJ θ).det * (raiseE F * φ (raiseE Pₗ * Aₗ))) = _ at change
  rw [pull, W_param] at change
  simpa [train_id, mul_comm] using change.symm

/-- The same unnormalized identity holds simultaneously for products of
independently named marked insertions. A name may itself represent an
incoming connected packet with several marks. -/
theorem marked {I : Type*} [DecidableEq I] (K : Matrix U U ℝ)
    (Pₐ Pₗ : Ink (U ⊕ Y)) (θ : U → Ink (U ⊕ Y)) (b : Ink Y)
    (law : ∀ a l : Ink (U ⊕ Y), a = reroll path θ l →
      Wick Y K⁻¹ (raiseE Pₗ * l) = raiseE b * Wick Y K⁻¹ (raiseE Pₐ * a))
    (Aₐ Aₗ : I → Ink (U ⊕ Y)) (field : ∀ i, Aₐ i = reroll path θ (Aₗ i))
    (S : Finset I) :
    Wick Y K⁻¹ (raiseE Pₗ * ∏ i ∈ S, Aₗ i) =
      raiseE b * Wick Y K⁻¹ (raiseE Pₐ * ∏ i ∈ S, Aₐ i) := by
  apply law
  simp only [map_prod, ← field]

/-- Unit division at the true empty source. -/
def normalized (p v : Ink Y) (hv : IsUnit v) : Ink Y := p * ↑(hv.unit⁻¹)

omit [Fintype Y] in
private lemma restore (p v : Ink Y) (hv : IsUnit v) : normalized p v hv * v = p := by
  unfold normalized
  conv_lhs => rhs; rw [← hv.unit_spec]
  simp [mul_assoc]

omit [Fintype Y] in
/-- Even a coarse-field dependent empty-source factor cancels. This statement
applies after summing all collections of original marked vertices in a mask. -/
theorem vacuum_quotient {I : Type*} (A L : I → Ink Y) (empty : I) (b : Ink Y)
    (law : ∀ i, L i = b * A i) (hA : IsUnit (A empty)) (hL : IsUnit (L empty)) (i : I) :
    normalized (L i) (L empty) hL = normalized (A i) (A empty) hA := by
  apply ((hL.mul hA).mul_left_inj).mp
  calc
    _ = (normalized (L i) (L empty) hL * L empty) * A empty := by ring
    _ = L i * A empty := by rw [restore]
    _ = A i * L empty := by rw [law i, law empty]; ring
    _ = (normalized (A i) (A empty) hA * A empty) * L empty := by rw [restore]
    _ = _ := by ring

end YM.Integration.OriginalTwoChartMarkedWick
