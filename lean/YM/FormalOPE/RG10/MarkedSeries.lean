import YM.FormalOPE.RG10.FlatFeed
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Next.MULTISOURCE.Formal

/-!
# `Word R` is perturbative Taylor series in the common census algebra
-/

set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open Marker Extra.Trajectories PowerSeries MeasureTheory Finset
open scoped BigOperators

variable {V I : Type} [DecidableEq V] [DecidableEq I] {R : Census V} {S : Census I}

abbrev Word (R : Census V) := PowerSeries (Poly R)

namespace Word

/-- Transpose: Taylor column associated to one allowed subset. -/
def see (s : R.Mode) (A : Word R) : Series := PowerSeries.mk fun i => (PowerSeries.coeff i A).part s

def package (f : R.Mode → Series) : Word R := PowerSeries.mk fun i => Poly.inject fun s =>
  PowerSeries.coeff i (f s)

lemma observe_ext {A B : Word R} (h : ∀ (s : R.Mode), see s A = see s B) : A = B := by
  apply PowerSeries.ext; intro k; ext s;
  have h := congr_arg (PowerSeries.coeff k) (h s)
  simpa [see] using h

@[simp] lemma unfold_see (s : R.Mode) (A : Word R) (n : ℕ) :
    PowerSeries.coeff n (see s A) = (PowerSeries.coeff n A).part s := by simp [see]

@[simp] lemma see_package (f : R.Mode → Series) (s : R.Mode) : see s (package f) = f s := by
  apply PowerSeries.ext; simp [package, Poly.part, Poly.inject]

@[simp] lemma package_see (A : Word R) : package (fun s => see s A) = A :=
  observe_ext fun _ => see_package ..

@[simp] lemma see_add (s : R.Mode) (A B : Word R) : see s (A+B) = see s A + see s B := by
  apply PowerSeries.ext; simp
@[simp] lemma see_sub (s : R.Mode) (A B : Word R) : see s (A-B) = see s A - see s B := by
  apply PowerSeries.ext; simp [part_sub]
@[simp] lemma see_zero (s : R.Mode) : see s (0 : Word R) = 0 := by
  apply PowerSeries.ext; simp
@[simp] lemma see_neg (s : R.Mode) (A : Word R) : see s (-A) = -see s A := by
  apply PowerSeries.ext; simp
@[simp] lemma see_smul (c : ℂ) (s : R.Mode) (A : Word R) : see s (c • A) = c • see s A := by
  apply PowerSeries.ext; intro i; simp

@[simp] lemma see_sum {L : Type*} (T : Finset L) (f : L → Word R) (s : R.Mode) :
    see s (∑ i ∈ T, f i) = ∑ i ∈ T, see s (f i) := by
  apply PowerSeries.ext; intro i; simp [Poly.part_sum]

@[simp] lemma see_one (s : R.Mode) : see s (1 : Word R) = if s = R.quiet then 1 else 0 := by
  apply PowerSeries.ext; intro k; by_cases h:s=R.quiet <;> by_cases hk:k=0 <;> simp [h,hk]

/-- Cauchy multiplication on coupling degree, disjoint-subset multiplication on markers. -/
lemma convolves (s : R.Mode) (A B : Word R) : see s (A*B) =
    ∑ i, ∑ j, if Poly.merges i j s then see i A * see j B else 0 := by
  apply PowerSeries.ext; intro k
  simp_rw [map_sum, unfold_see, PowerSeries.coeff_mul, Poly.part_sum, Poly.part_mul]
  -- need commute sums and extract if, coercions
  rw [Finset.sum_comm]; apply sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply sum_congr rfl; intro j _
  by_cases h : Poly.merges i j s <;> simp [h, PowerSeries.coeff_mul]

/-- Unmarked coefficients (already divided by a common denominator when `vac = 1`). -/
def vac (R : Census V) : Word R →ₐ[ℂ] Series where
  toFun := see R.quiet
  map_one' := by simp
  map_mul' a b := by rw [convolves]; simp [Poly.merge_vac, ite_and]
  map_add' _ _ := by simp
  map_zero' := see_zero R.quiet
  commutes' c := by rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]; simp

@[simp] lemma vac_eq (A : Word R) : vac R A = see R.quiet A := rfl

lemma mode_card_eq {s i j : R.Mode} (h : Poly.merges i j s) : s.val.card=i.val.card+j.val.card := by
  rw [← h.2, card_union_of_disjoint h.1]

lemma mark_order (A : Word R) (h : vac R A = 0) (j : ℕ) (s : R.Mode) (hs : s.val.card < j) :
    see s (A^j) = 0 := by
  induction j generalizing s with
  | zero => omega
  | succ j ih =>
    rw [pow_succ, convolves]; refine sum_eq_zero (fun i hi => sum_eq_zero fun k hk => ?_)
    by_cases hk : Poly.merges i k s
    · rw [if_pos hk]; obtain hz|hz := Nat.eq_zero_or_pos k.val.card
      · rw [show k=R.quiet from Subtype.ext (card_eq_zero.mp hz), ← vac_eq, h, mul_zero]
      have hh := mode_card_eq hk
      rw [ih i (by omega), zero_mul]
    rw [if_neg hk]

lemma marker_nil [Fintype V] {A : Word R} (h : vac R A = 0) {j : ℕ} (hj : Fintype.card V < j) :
    A ^ j = 0 := by
  apply observe_ext; intro s; rw [mark_order A h j s ((card_le_univ _).trans_lt hj), see_zero]

def eraseMarks (u : Names R S) : Word S →+* Word R := PowerSeries.map u.restriction

@[simp] lemma see_eraseMarks (u : Names R S) (s : R.Mode) (A : Word S) :
    see s (eraseMarks u A) = see (u.share s) A := by
  apply PowerSeries.ext; intro i; rw [unfold_see, unfold_see, eraseMarks, coeff_map]; rfl

/-- `sing` attaches a column to one allowed marker monomial. -/
def sing (s : R.Mode) (a : Series) : Word R := package fun i => if i = s then a else 0
@[simp] lemma see_sing (s i : R.Mode) (a : Series) : see s (sing i a)= if s=i then a else 0 := by
  rw [sing, see_package]

lemma spike_mul (A : Word R) (b : Series) (s : R.Mode) :
    see s (sing R.quiet b * A) = b * see s A := by
  rw [convolves, Finset.sum_eq_single R.quiet]
  · simp -- vacuum iff
  · intro j _ hj; simp [hj]
  simp

end Word
end YM.FormalOPE.RG10
