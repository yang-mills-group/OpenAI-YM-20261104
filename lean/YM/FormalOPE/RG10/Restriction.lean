import YM.FormalOPE.RG10.Reclosure
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Restrictions in order and marker demand commute

Inputs before field quotient/extractions. Compare genuine *same* coupling-germ convention. This
supports projective or finite truncated models (separate kernels needn't extend compatibly above
announced order/demand). Compatible **physical** field basis requires more than marker census
restriction: stencils and their identities and field frames need the same representatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open Marker Extra.Trajectories PowerSeries MeasureTheory Filter Finset Word Polar Function
open scoped BigOperators

variable {X : Type*}

def Through {α : Type*} [CommSemiring α] (r : ℕ) (A B : PowerSeries α) :=
  ∀ i ≤ r, PowerSeries.coeff i A = PowerSeries.coeff i B
namespace Through
variable {α : Type*} [CommSemiring α] {p r i : ℕ} {A B C D : PowerSeries α}
lemma refl (A : PowerSeries α) : Through r A A := fun _ _ => rfl
lemma symm (h : Through r A B) : Through r B A := fun _ i => (h _ i).symm
lemma trans (h : Through r A B) (k : Through r B C) : Through r A C := fun _ i => (h _ i).trans (k _ i)
lemma mono (h : Through r A B) (i : p ≤ r) : Through p A B := fun _ k => h _ (k.trans i)
lemma trunc (h : Through r A B) : trunc (r+1) A = trunc (r+1) B := by
  ext i; rw [coeff_trunc,coeff_trunc]; split
  · rename_i h'; exact h _ (by omega)
  rfl
lemma through_trunc : Through r ((PowerSeries.trunc (r+1) A : Polynomial α):PowerSeries α) A := by
  intro i hi; simp [coeff_trunc, hi]
lemma mul (h : Through r A B) (k : Through r C D) : Through r (A*C) (B*D) := by
  intro i hi; rw [coeff_mul, coeff_mul]; apply Finset.sum_congr rfl; intro j hj; have e:=Finset.mem_antidiagonal.mp hj
  rw [h _ (by omega), k _ (by omega)]
lemma pow (h : Through r A B) (i : ℕ) : Through r (A^i) (B^i) := by
  induction i with
  | zero => simp only [pow_zero]; apply Through.refl
  | succ i ih => rw [pow_succ, pow_succ]; exact ih.mul h
lemma add (h : Through r A B) (k : Through r C D) : Through r (A+C) (B+D) := by
  intro i hi; rw [map_add, map_add, h i hi, k i hi]
lemma invAlready (h : Through r A B) (he : A*C=1) (hg : B*D=1) : Through r C D := by
  have hv : C=C * B * D:= by rw [mul_assoc,hg,mul_one]
  rw [hv]; have hw : C * A * D = D:=by rw [mul_comm C,he,one_mul]
  nth_rw 2 [← hw]
  exact ((Through.refl C).mul h.symm).mul (Through.refl D)

variable {V I : Type} [DecidableEq V] [DecidableEq I] [Fintype V] [Fintype I]
    {R : Census V} {S : Census I}
omit [Fintype V] in
lemma views {A B : Word R} : Through r A B ↔ (∀ s : R.Mode, Through r (see s A) (see s B)) := by
  constructor
  · intro h s i hi; simp [h i hi]
  intro h i hi; ext s; rw [← unfold_see, ← unfold_see]; apply h s i hi

lemma coherent {A B : Word R} (hr : Fintype.card I ≤ r) (h : Through r A B) :
    certify I A = certify I B := by
  ext s; rw [← pay_sep s]; simp [h _ ((card_le_univ (tickets s)).trans hr), -pay_sep]

lemma logCongr {A B : Word R} (h : Through r A B) : Through r (logWord A) (logWord B) := by
  intro i hi; ext s; rw [log_grade, log_grade]; exact congr_arg
    (fun k : Poly (budget R (Fin i)) => (i.factorial:ℂ)⁻¹ * (connected k).part (pay s univ)) (coherent (by simpa using hi) h)

end Through

namespace FlatFeed
variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] (F : FlatFeed Θ E)
    {W W' : Vertices (Θ × E)}
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {R : Census V} {S : Census I}

/-- Preserve even marked history using the same input Wilson germ data through order `r`.
If Taylor bases, witnesses or physical outputs differ, not providing agreement implicitly. -/
structure AtOrder (A B : Vertices X) (r : ℕ) : Prop where
  J x : Through r (A.J x) (B.J x)
  V x : Through r (A.V x) (B.V x)

lemma AtOrder.weight {L L' : Vertices X} {r : ℕ} (h : AtOrder L L' r) (x : X) :
    Through r (L.weight x) (L'.weight x) := by
  apply Through.mul _ (h.J x); intro j hj
  simp only [expTaylor, PowerSeries.coeff_mk]
  exact Finset.sum_congr rfl fun i _ => by rw [(h.V x).pow i j hj]

variable {A : Θ × E → Word R} {B : Θ × E → Word S} {r : ℕ}

lemma average_compat {f q : Kernel (Θ × E)} (h : ∀ x, Through r (f x) (q x)) :
    Through r (F.average f) (F.average q) := by
  intro i hi
  simp_rw [average_coeff, show row i f = row i q from funext fun x => h x i hi]

lemma step_compat (hv : AtOrder W W' r) {f q : Kernel (Θ × E)} (h : ∀ x, Through r (f x) (q x)) :
    Through r (F.step W f) (F.step W' q) := by
  apply Through.mul (F.average_compat (fun x => (hv.weight x).mul (h x)))
    (Through.invAlready (F.average_compat hv.weight) (F.den_inv W) (F.den_inv W'))

omit [Fintype V] [Fintype I] in
lemma trim_through (hv : AtOrder W W' r) (u : Names R S)
    (h : ∀ x, Through r (A x) (eraseMarks u (B x))) :
    Through r (F.close W A) (eraseMarks u (F.close W' B)) := by
  apply Through.views.mpr; intro s
  rw [close_part, see_eraseMarks, close_part]
  apply step_compat F hv; intro x
  have h := Through.views.mp (h x) s; rw [see_eraseMarks] at h; exact h

lemma here_through (hv : AtOrder W W' r) (u : Names R S)
    (hB : read S.quiet B=1) (h : ∀ x, Through r (A x) (eraseMarks u (B x))) :
    Through r (F.contraction W A) (eraseMarks u (F.contraction W' B)) := by
  unfold contraction; rw [restrict_log]; apply Through.logCongr (F.trim_through hv u h); unfold boot
  rw [F.preserve_one _ hB]; simp

/-- Exported as simultaneous truncations (Mathlib `trunc (r+1)` includes row `r`). -/
theorem compatible (hv : AtOrder W W' r) (u : Names R S)
    (hA : read R.quiet A=1) (hB : read S.quiet B=1) (h : ∀ x, Through r (A x) (eraseMarks u (B x))) :
    let c := F.contraction W A
    let c' := F.contraction W' B
    trunc (r+1) c = trunc (r+1) (eraseMarks u c') ∧
    trunc (r+1) (expMark c) = trunc (r+1) (eraseMarks u (expMark c')) := by
  dsimp only
  rw [F.reclosure _ hA, F.reclosure _ hB]; exact ⟨(here_through F hv u hB h).trunc,
    (trim_through F hv u h).trunc⟩

lemma identical_input {f : V → Kernel X} {g : I → Kernel X} (u : Names R S) (h : ∀ i, f i = g (u.e i)) :
    ∀ x : X, Word.emit R (fun i => f i x) = eraseMarks u (Word.emit S (fun i => g i x)) := by
  intro x; apply observe_ext; intro s; rw [see_eraseMarks, emit_part, emit_part]
  unfold Names.share; rw [prod_image u.e.injective.injOn]
  exact prod_congr rfl fun i _ => congr_fun (h i) x

/-- Product inputs can also be supplied only through the requested order. -/
theorem finite_input {f : V → Kernel X} {g : I → Kernel X} (u : Names R S)
    (h : ∀ i x, Through r (f i x) (g (u.e i) x)) :
    ∀ x : X, Through r (Word.emit R (fun i => f i x)) (eraseMarks u (Word.emit S (fun i => g i x))) := by
  intro x; apply Through.views.mpr; intro s; rw [see_eraseMarks, emit_part, emit_part]; unfold Names.share
  rw [prod_image u.e.injective.injOn]
  generalize s.val = p
  induction p using Finset.induction with
  | empty => simp only [prod_empty]; apply Through.refl
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha]; apply Through.mul (h a x) ih
end FlatFeed
end YM.FormalOPE.RG10
