import YM.FormalOPE.RG10.Occupied
import YM.FormalOPE.RG10.Second

/-!
# RG10 multi-input kernels and output-to-log on the formal Wilson step

X-space formal adapter over the required given Gaussian data, per background derivatives handled
separately. Build a *single unmasked* marked polynomial, representing the full product. After
flat Gaussian integration (with the weight, any other vacuum common factors still tracked in
producer calculations if comparing to real output), divide by the zero-mark series with its full
field dependence. Only then take `contraction` (the logarithm). The unitarity and reconstruction
here are exact algebraic identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open Marker Extra.Trajectories PowerSeries MeasureTheory Filter Finset Word Function
open scoped BigOperators

variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] (F : FlatFeed Θ E)
    (W : Vertices (Θ × E))
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {R : Census V} {S : Census I} {X : Type*}

namespace Word

/-- Single-column generating input. Multi-marker logarithms can be inserted at later steps
via `expMark` prior to this same calculation. -/
def emit (R : Census V) (f : V → Series) := ∏ i : V, (1 + sing (R.fire i) (f i))

omit [Fintype V] in
private lemma only_product (f : V → Series) {s : Finset V} {t : R.Mode} (h : t.val=s) :
    ∏ i∈s, sing (R.fire i) (f i) = sing t (∏ i∈s, f i) := by
  induction s using Finset.induction generalizing t with
  | empty =>
    rw [prod_empty, prod_empty]; apply observe_ext; intro i
    simp [show t=R.quiet from Subtype.ext h]
  | insert i a hi ih =>
    rw [prod_insert hi, prod_insert hi]
    have hv : a ⊆ t.val := by rw [h]; exact subset_insert i _
    let j : R.Mode := ⟨a, R.down t.property _ hv⟩
    rw [ih (t:=j) rfl]; apply observe_ext; intro k
    have hz : Poly.merges (R.fire i) j t :=
      ⟨by simpa only [Census.fire, j, disjoint_singleton_left] using hi,(singleton_union ..).trans h.symm⟩
    rw [see_sing, convolves, Finset.sum_eq_single (R.fire i), Finset.sum_eq_single j]
    · by_cases hm : k=t
      · subst k; simp [hz]
      rw [if_neg hm, if_neg]; exact fun he => hm (Subtype.ext (he.2.symm.trans hz.2))
    · intro b h₁ h₂; simp [h₂]
    · simp
    · intro b h₁ h₂; simp [h₂]
    simp

omit [Fintype V] in
private lemma absent_product (f : V → Series) {s : Finset V} (h : s∉R.choices) :
    ∏ i∈s, sing (R.fire i) (f i)=0:= by
  induction s using Finset.induction with
  | empty => exact (h R.blank).elim
  | insert i a hi ih =>
    rw [prod_insert hi]
    by_cases he : a∈R.choices
    · let j : R.Mode := ⟨a,he⟩
      rw [only_product f (t:=j) rfl]; apply observe_ext; intro k
      rw [convolves, see_zero]; apply sum_eq_zero; intro b _; apply sum_eq_zero; intro c _
      by_cases hn : b=R.fire i ∧ c=j
      · rcases hn with ⟨rfl, ht⟩; rw [ht, if_neg]; intro hg; exact h ((show insert i a = k.val from (Finset.singleton_union ..).symm.trans hg.2) ▸ k.property)
      · by_cases hb : b=R.fire i
        · have hC : c≠j:= fun hh => hn ⟨hb,hh⟩; simp [hC]
        simp [hb]
    rw [ih he,mul_zero]

lemma emit_part (R : Census V) (f : V → Series) (k : R.Mode) : see k (emit R f) = ∏ i∈k.val,f i := by
  rw [emit, prod_one_add, see_sum, Finset.sum_eq_single k.val]
  · rw [only_product f rfl (t:=k)]; simp
  · intro b hb hB; by_cases h:b∈R.choices
    · let j : R.Mode := ⟨b,h⟩
      rw [only_product f (t:=j) rfl]; simp [show k≠j from fun he => hB (congr_arg Subtype.val he.symm)]
    rw [absent_product f h]; simp
  simp

@[simp] lemma emit_unit (f : V → Series) : vac R (emit R f) = 1 := by rw [vac_eq, emit_part]; rfl

/-- Evaluate one census, retaining the column labeling. -/
def read (s : R.Mode) (A : X → Word R) : Kernel X := see s ∘ A
lemma read_emitted (R : Census V) (f : V → Kernel X) (s : R.Mode) :
    read s (fun x => emit R (fun i => f i x)) = ∏ i∈s.val, f i := by
  funext x; unfold read; rw [Function.comp_apply, emit_part, Finset.prod_apply]
end Word
namespace FlatFeed

/-- Before any denominator operation. -/
def columns (A : Θ × E → Word R) : Word R := package fun s => F.average (read s A)

omit [Fintype V] in
@[simp] lemma column_eq (A : Θ × E → Word R) (s : R.Mode) : see s (F.columns A) = F.average (read s A) := by
  rw [columns, see_package]

/-- Kernel includes the weight as an operation on the **whole** unmasked marked polynomial.
All other necessary model factors must be included in `W` or the realization of the marked
polynomial. Integrability requirement is on these same outputs in every allowed subset. -/
def totalize (A : Θ × E → Word R) (x) := sing R.quiet (W.weight x) * A x

omit [Fintype Θ] [MeasurableSpace E] [Fintype V] in
lemma totalize_read (A : Θ × E → Word R) (s : R.Mode) :
    read s (totalize W A) = W.weight * read s A := by
  funext x; unfold Word.read totalize; rw [Function.comp_apply, spike_mul]; rfl

def markedFunded (A : Θ × E → Word R) := ∀ s : R.Mode, F.Funded (read s (totalize W A))

/-- Pre-log output expressed through the full marked numerator/denominator, not independent
substep approximations. -/
def close (A : Θ × E → Word R) :=
  sing R.quiet (F.den W)⁻¹ * F.columns (totalize W A)
omit [Fintype V] in
lemma close_part (A : Θ × E → Word R) (s : R.Mode) : see s (F.close W A) = F.step W (read s A) := by
  rw [close, spike_mul, column_eq, totalize_read, step, mul_comm]

omit [Fintype V] in
lemma preserve_one {A : Θ × E → Word R} (h : read R.quiet A = 1) : vac R (F.close W A) = 1 := by
  rw [vac_eq, close_part, h, step_one]

/-- Connected inclusion cumulants on finite demand. -/
def contraction (A : Θ × E → Word R) := logWord (F.close W A)

lemma reclosure {A : Θ × E → Word R} (h : read R.quiet A=1) :
    expMark (F.contraction W A) = F.close W A := exp_log _ (F.preserve_one W h)

lemma closing_emission (R : Census V) (f : V → Kernel (Θ × E)) (s : R.Mode) :
    see s (F.close W (fun x => emit R (fun i => f i x))) = F.ordinary W s.val f := by
  rw [close_part,read_emitted]; rfl

lemma contract_pair (R : Census V) {s : R.Mode} {i j} (hm : s.val={i,j}) (hn : i≠j)
    (f : V → Kernel (Θ × E)) : see s (F.contraction W (fun x => emit R (fun i => f i x))) =
      F.pairConnected W (f i) (f j) := by
  unfold contraction
  have e : vac R (F.close W (fun x => emit R (fun i => f i x)))=1 :=
    F.preserve_one W (funext (fun x => emit_unit ..))
  rw [crown _ e s hn hm, closing_emission, hm, F.ordinary_pair W hn f, closing_emission,
    closing_emission]
  simp only [Census.fire, ordinary, prod_singleton]; rfl

lemma ordinary_from_contract (R : Census V) (f : V → Kernel (Θ × E)) :
    let A := fun x => emit R (fun i => f i x)
    expMark (F.contraction W A) = package fun s : R.Mode => F.ordinary W s.val f := by
  intro A
  have hu : read R.quiet A = 1:= funext (fun x => emit_unit ..)
  apply observe_ext; intro s; rw [reclosure F W hu, see_package]; exact closing_emission ..

/-- Reproduces the positive-order calculation in `Second`, now from the general connected
scheme. -/
theorem projection_second (R : Census V) {s : R.Mode} {i j} (hm : s.val={i,j}) (hn : i≠j)
    (f : V → Kernel (Θ × E)) :
    PowerSeries.coeff 2 (see s (F.contraction W (fun x => emit R (fun i => f i x)))) =
      F.connectedSecond W (f i) (f j) := by rw [contract_pair F W R hm hn, connected_second]
end FlatFeed
end YM.FormalOPE.RG10
