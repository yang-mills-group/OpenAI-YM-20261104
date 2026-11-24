import YM.FormalOPE.RG10.MarkedSeries
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Polarization payment: coupling as extra distinct square-zero markers

This lets a connected-graph calculation use exactly the accepted Poly ring and cumulant and
connected-log bounds. It also detects order and truncation before any capture or one-tag projections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open Marker Extra.Trajectories PowerSeries MeasureTheory Filter Finset Word
open scoped BigOperators

variable {V I : Type} [DecidableEq V] [DecidableEq I] [Fintype V] [Fintype I]
    {R : Census V} {S : Census I}

namespace Polar
/-- The original finite census with an independent set of dummy coupling-degree slots. -/
def budget (R : Census V) (I : Type) [DecidableEq I] [Fintype I] : Census (V ⊕ I) where
  choices := Finset.univ.filter fun s : Finset (V⊕I) => s.toLeft ∈ R.choices
  blank := by simp [show (∅ : Finset (V⊕I)).toLeft = ∅ from rfl, R.blank]
  solo i := by
    rcases i with i|i
    · simp [show ({Sum.inl i} : Finset (V⊕I)).toLeft = {i} from Finset.ext (by simp), R.solo]
    simp [show ({Sum.inr i} : Finset (V⊕I)).toLeft = ∅ from Finset.ext (by simp), R.blank]
  down := fun h _ h' => mem_filter.mpr ⟨mem_univ _, R.down (mem_filter.mp h).2 _
    (toLeft_subset_toLeft h')⟩

def pay (s : R.Mode) (t : Finset I) : (budget R I).Mode :=
  ⟨s.val.disjSum t, by unfold budget; simp⟩

def mark (s : (budget R I).Mode) : R.Mode := ⟨s.val.toLeft, (mem_filter.mp s.property).2⟩
def tickets (s : (budget R I).Mode) : Finset I := s.val.toRight

@[simp] lemma mark_pay (s : R.Mode) (t : Finset I) : mark (pay s t) = s := Subtype.ext toLeft_disjSum
@[simp] lemma tickets_pay (s : R.Mode) (t : Finset I) : tickets (pay s t) = t := toRight_disjSum
@[simp] lemma pay_sep (s : (budget R I).Mode) : pay (mark s) (tickets s) = s := Subtype.ext toLeft_disjSum_toRight
lemma pay_inj (s a : R.Mode) (t b : Finset I) : pay s t = pay a b ↔ s=a ∧ t=b := by
  simp only [pay, Subtype.ext_iff, disjSum_inj]
lemma pay_quiet (R : Census V) (I : Type) [DecidableEq I] [Fintype I] :
    pay R.quiet (∅ : Finset I) = (budget R I).quiet := by simp [pay,Census.quiet]

/-- Multiplicativity is proved on the product of marker sets, not by treating the τ's as a
single square-zero coupling. -/
lemma pay_merge {s a b : R.Mode} {t x y : Finset I} :
    Poly.merges (pay a x) (pay b y) (pay s t) ↔ Poly.merges a b s ∧ (Disjoint x y ∧ x∪y=t) := by
  unfold Poly.merges pay
  have h : a.val.disjSum x ∪ b.val.disjSum y = (a.val∪b.val).disjSum (x∪y) :=
    Finset.ext (by rintro (p|p) <;> simp)
  simp only [h, disjSum_inj, Finset.disjoint_left]
  simp [Sum.forall]; tauto

private def splitUp : (budget R I).Mode ≃ R.Mode × Finset I where
  toFun s := (mark s, tickets s)
  invFun x := pay x.1 x.2
  right_inv x := by simp
  left_inv := pay_sep

lemma sum_pay {A : Type*} [AddCommMonoid A] (f : (budget R I).Mode → A) :
    ∑ i, f i = ∑ s : R.Mode, ∑ t : Finset I, f (pay s t) := by
  rw [← Fintype.sum_prod_type' (fun s t => f (pay s t))]
  exact Fintype.sum_equiv splitUp f _ (fun i => congr_arg f (pay_sep i).symm)

omit [Fintype I] in
private lemma sdiff_unique {x y t : Finset I} (h : Disjoint x y ∧ x ∪ y = t) : y = t \ x := by
  rw [← h.2]; apply Finset.ext; intro a; simp only [Finset.mem_sdiff, Finset.mem_union]
  have he : a∈x → a∈y → False := fun hx hy => disjoint_left.mp h.1 hx hy
  tauto

private lemma split_eval (t : Finset I) (A B : ℕ → ℂ) :
    ∑ x : Finset I, ∑ y : Finset I, (if Disjoint x y ∧ x∪y=t then A x.card * B y.card else 0) =
      ∑ j ∈ range (t.card+1), t.card.choose j • (A j * B (t.card-j)) := by
  rw [← sum_powerset_apply_card (x:=t) (fun j => A j * B (t.card-j)),
    ← sum_subset (s₁:=t.powerset) (Finset.subset_univ _) (fun x _ hx => ?_)]
  · refine sum_congr rfl fun x hx => ?_
    have he := mem_powerset.mp hx
    rw [Finset.sum_eq_single (t \ x)]
    · rw [if_pos (show Disjoint x (t \ x) ∧ x ∪ (t \ x) = t from
        ⟨disjoint_sdiff, union_sdiff_of_subset he⟩), card_sdiff_of_subset he]
    · intro y hy ht; rw [if_neg (fun h => ht (sdiff_unique h))]
    simp
  apply sum_eq_zero; intro y _
  exact if_neg (fun h : Disjoint x y ∧ x ∪ y = t => hx (mem_powerset.mpr (h.2 ▸ subset_union_left)))

/-- Detect a Taylor jet using genuine factorial multiplicity, no division by marker weights. -/
def present (I : Type) [DecidableEq I] [Fintype I] (A : Word R) : Poly (budget R I) :=
  Poly.inject fun s =>
    ↑(tickets s).card.factorial * (PowerSeries.coeff (tickets s).card A).part (mark s)

@[simp] lemma present_pay (A : Word R) (s : R.Mode) (t : Finset I) :
    (present I A).part (pay s t) = ↑t.card.factorial * (PowerSeries.coeff t.card A).part s := by
  change ↑(tickets (pay s t)).card.factorial * (coeff (tickets (pay s t)).card A).part (mark _) = _
  simp only [tickets_pay, mark_pay]

lemma present_quiet (A : Word R) :
    (present I A).part (budget R I).quiet = PowerSeries.coeff 0 (vac R A) := by
  rw [← pay_quiet]; simp

private lemma polarizedProduct (t : Finset I) (a b : R.Mode) (A B : Word R) :
    ∑ x : Finset I, ∑ y : Finset I,
      (if Disjoint x y ∧ x∪y=t then (present I A).part (pay a x) * (present I B).part (pay b y) else 0) =
    ↑t.card.factorial * (PowerSeries.coeff t.card (see a A * see b B)) := by
  simp_rw [present_pay]
  rw [split_eval t (fun k => ↑k.factorial * (coeff k A).part a) (fun k => ↑k.factorial * (coeff k B).part b),
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (see a A) * coeff j (see b B)), Finset.mul_sum]
  apply sum_congr rfl; intro j hj
  rw [nsmul_eq_mul, unfold_see, unfold_see]
  have hj : j ≤ t.card := Nat.le_of_lt_succ (mem_range.mp hj)
  conv_rhs => lhs; rw [← Nat.choose_mul_factorial_mul_factorial hj]; skip
  push_cast; ring

private lemma present_one : present I (1 : Word R) = 1 := by
  ext s; obtain ⟨⟨s,t⟩,rfl⟩ := (splitUp (R:=R)).symm.surjective s
  change (present I (1:Word R)).part (pay s t) = (1:Poly (budget R I)).part _
  rw [present_pay]; change _ = Poly.part (1:Poly (budget R I)) (pay s t); rw [Poly.one_part, ← pay_quiet]
  by_cases h:s=R.quiet <;> by_cases k:t=∅ <;> simp [pay_inj,h,k]

private lemma present_mul (A B : Word R) : present I (A*B) = present I A * present I B := by
  ext s; rw [← pay_sep s]
  generalize mark s = u
  generalize tickets s = t
  rw [Poly.part_mul, sum_pay, present_pay, ← unfold_see, convolves]
  simp_rw [map_sum, Finset.mul_sum]
  apply sum_congr rfl; intro a _
  simp_rw [sum_pay _]; rw [sum_comm (s:= (univ : Finset (Finset I)))] -- outer x before b ?
  apply sum_congr rfl; intro b _
  by_cases h : Poly.merges a b u
  · simp only [h, if_true, pay_merge, true_and]
    exact (polarizedProduct t a b A B).symm
  simp [pay_merge, h]

def certify (I : Type) [DecidableEq I] [Fintype I] : Word R →ₐ[ℂ] Poly (budget R I) where
  toFun := present I
  map_add' a b := by
    ext s; rw [← pay_sep s]
    simp only [present_pay, map_add, Poly.part_plus, mul_add]
  map_mul' a b := present_mul a b
  map_one' := present_one
  map_zero' := by ext s; rw [← pay_sep s]; simp [-pay_sep]
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    -- preserve ℂ scalars of our existing budgets
    change present I (z • (1:Word R)) = z • (1:Poly (budget R I))
    conv_rhs => rw [← present_one (R:=R)]
    ext s
    rw [← pay_sep s]; simp only [present_pay, coeff_smul, Poly.part_smul]; ring

@[simp] lemma certify_present (A : Word R) : certify I (R:=R) A = present I A := rfl
lemma detects {A B : Word R} (h : ∀ r : ℕ, certify (Fin r) A = certify (Fin r) B) : A=B := by
  apply PowerSeries.ext; intro k; ext s
  apply mul_left_cancel₀ (a:= (↑k.factorial:ℂ)) (by exact_mod_cast Nat.factorial_ne_zero k)
  simpa only [certify_present, present_pay, card_univ, Fintype.card_fin] using
    congr_arg (fun z => Poly.part z (pay s (Finset.univ (α:=Fin k)))) (h k)
end Polar
end YM.FormalOPE.RG10
