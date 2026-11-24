import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Formal calculations in the X-space prescription

Here and in files using FPS every equality, even of scale-dependent matrices, is understood
at each fixed finite order. Use the honest formal series ring to enforce compatibility;
it does NOT assert convergence of sums at positive coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.FPS
open PowerSeries
open scoped BigOperators

section extLinear
variable {S A B : Type*} [Semiring S] [Semiring A] [Semiring B] [Module S A] [Module S B]

def extending (L : A →ₗ[S] B) : PowerSeries A →ₗ[S] PowerSeries B where
  toFun f:= mk fun n => L (coeff n f)
  map_add' f g:= PowerSeries.ext fun n=> by simp
  map_smul' s f:=PowerSeries.ext fun n=>by simp [coeff_smul]

@[simp] lemma coeff_extending (L : A →ₗ[S] B) (f : PowerSeries A) (n : ℕ) : coeff n (extending L f)= L (coeff n f):= by simp [extending]
end extLinear

section algebra
variable {R S T : Type*} [CommSemiring R] [Semiring S] [Algebra R S] [Semiring T] [Algebra R T]

lemma extending_mul (L : S →ₗ[R] T) (a : PowerSeries R) (f : PowerSeries S) :
    extending L (PowerSeries.map (algebraMap R S) a * f)=PowerSeries.map (algebraMap R T) a*extending L f:=
  PowerSeries.ext fun n => by simp [coeff_mul,← Algebra.smul_def]

lemma extending_mul_self (L : S →ₗ[R] R) (a : PowerSeries R) (f : PowerSeries S) :
    extending L (PowerSeries.map (algebraMap R S) a * f)=a*extending L f:=by rw [extending_mul]; simp
end algebra

section subst
variable {R S : Type*} [CommRing R] [CommRing S]
variable [Algebra R S]

lemma coeff_substituted (f : PowerSeries R) {g : PowerSeries S} (hg : constantCoeff g=0) (n : ℕ) :
    coeff n (f.subst g)=∑ m∈Finset.range (n+1), coeff m f • coeff n (g^m) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  apply finsum_eq_sum_of_support_subset
  intro i hi; by_contra h
  change i∉ Finset.range (n+1) at h
  apply hi
  exact (congr_arg (coeff i f • ·) ((X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hg) i)) _ (by simp only [Finset.mem_range] at h; omega))).trans (smul_zero _)
end subst

lemma mapped_zero {R S : Type*} [Semiring R] [Semiring S] (L : R →+* S) {g : PowerSeries R} (hg : constantCoeff g=0):
    constantCoeff (PowerSeries.map L g) = 0 := by rw [← coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,hg,map_zero]

lemma substitute_ringHom {R S : Type*} [CommRing R] [CommRing S] (L : R →+* S) (f : PowerSeries R) {a : PowerSeries R} (ha : constantCoeff a=0) :
    PowerSeries.map L (f.subst a)=(PowerSeries.map L f).subst (PowerSeries.map L a) := PowerSeries.ext fun n=> by
  simp only [coeff_map, coeff_substituted f ha, coeff_substituted (PowerSeries.map L f) (mapped_zero L ha), smul_eq_mul, map_sum, map_mul]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← map_pow, coeff_map]

/-- Dilation in the formal *argument* applied **after** substitution. -/
lemma rescale_substitute {R : Type*} [CommRing R] (f g : PowerSeries R) (hg : constantCoeff g=0) (r : R) :
    rescale r (f.subst g) = f.subst (rescale r g) := PowerSeries.ext fun n=> by
  have hr : constantCoeff (rescale r g) = 0 := by rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,hg,mul_zero]
  rw [coeff_rescale,coeff_substituted f hg,coeff_substituted f hr,Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; rw [← map_pow,coeff_rescale]; simp only [smul_eq_mul]; ring
end YM.XSpace.FPS
