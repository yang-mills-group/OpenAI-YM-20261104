import YM.Integration.WilsonFiniteOrdinaryPartitions
import YM.IterationFour.Series.Tail

/-! The omitted coupling grades of the actual ordinary moment, with the wallet
of each disjoint marked block retained inside its product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteOrdinaryTail
open Finset Marker Multi Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open WilsonIndependentOrdinaryPairGrade WilsonFiniteOrdinaryPartitions
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

/-- All coupling monomials in this remainder have total grade at least r+1. -/
theorem omitted (p : Polynomial ℂ) (r : ℕ) (z : ℂ) :
    p.eval z-partialValue r z p = ∑ j ∈ p.support with r<j, z^j*p.coeff j := by
  classical
  have all : p.eval z = ∑ j ∈ p.support,z^j*p.coeff j := by
    rw [Polynomial.eval_eq_sum]
    exact sum_congr rfl (fun _ _ => mul_comm ..)
  have low : partialValue r z p=∑ j ∈ p.support with j≤r,z^j*p.coeff j := by
    symm
    apply sum_subset (fun j h => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp h).2))
    intro j hj h
    have absent : j∉p.support := fun hit =>
      h (mem_filter.mpr ⟨hit,Nat.le_of_lt_succ (mem_range.mp hj)⟩)
    rw [Polynomial.notMem_support_iff.mp absent,mul_zero]
  rw [all,low,sub_eq_iff_eq_add,add_comm]
  simpa only [not_le] using (sum_filter_add_sum_filter_not p.support (fun i => i≤r)
    (fun i => z^i*p.coeff i)).symm

private theorem tail (p : Polynomial ℂ) (r : ℕ) (z : ℂ) (small : ‖z‖≤1) :
    ‖p.eval z-partialValue r z p‖ ≤ ‖z‖^(r+1)*mass p := by
  rw [omitted]
  apply (norm_sum_le ..).trans
  rw [mass,mul_sum]
  calc
    _ ≤ ∑ j ∈ p.support with r<j, ‖z‖^(r+1)*‖p.coeff j‖ := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul,norm_pow]
      obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt (mem_filter.mp hj).2)
      rw [hd,pow_add]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) small)) (norm_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by positivity)

private theorem productMass {I : Type*} (S : Finset I) (p : I → Polynomial ℂ) :
    IterationFour.Series.mass (∏ i ∈ S, p i) ≤ ∏ i ∈ S, mass (p i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have one : (1:Polynomial ℂ).support={0} := by
      ext n
      cases n <;> simp [Polynomial.mem_support_iff,Polynomial.coeff_one]
    simp [IterationFour.Series.mass,one]
  | @insert i S hi h =>
    simp only [prod_insert hi]
    exact (IterationFour.Series.mass_mul ..).trans (mul_le_mul_of_nonneg_left h
      (IterationFour.Series.mass_nn _))

omit [Fintype V] in
theorem toll (w : V → ℝ) (s : R.Mode) (q : (parts R).Mode) (h : q ∈ shards R s) :
    Poly.toll w s=∏ t ∈ q.val, Poly.toll w t.val := by
  rw [← show unionOf q=s from (mem_filter.mp h).2]
  exact prod_biUnion (parts_wise q)

omit [Fintype V] in
theorem blocks (s : R.Mode) (q : (parts R).Mode) (h : q ∈ shards R s) :
    q.val.card ≤ s.val.card := by
  rw [← show unionOf q=s from (mem_filter.mp h).2]
  unfold unionOf
  dsimp only
  rw [card_biUnion (parts_wise q)]
  nth_rw 1 [← show ∑ _i∈q.val, 1=q.val.card by simp]
  exact sum_le_sum fun i _ => Finset.card_pos.mpr i.property

/-- Absolute remainder using the actual per-face connected coefficient masses.
The complete source weights multiply across the covering partition. -/
theorem priced (W : Grade R r) (unit : UnitLeading W) (sym : Symmetric W)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) (z : ℂ) (small : ‖z‖≤1) (s : R.Mode) :
    Poly.toll w s * ‖(Poly.pass (value z (logMarked W))).part s - (value z (ratio W)).part s‖ ≤
      ‖z‖^(r+1) * ∑ q ∈ shards R s, ∏ t ∈ q.val,
        (Poly.toll w t.val * mass (slot t.val (render (logMarked W)))) := by
  let C := render (logMarked W)
  have rich : mass (ordinary W s) ≤ ∑ q ∈ shards R s, ∏ t ∈ q.val, mass (slot t.val C) :=
    (IterationFour.Series.mass_sum _ _).trans (sum_le_sum (fun _ _ => productMass _ _))
  have factor : Poly.toll w s*(∑ q∈shards R s,∏ t∈q.val,mass (slot t.val C)) =
      ∑ q∈shards R s,∏ t∈q.val,(Poly.toll w t.val * mass (slot t.val C)) := by
    rw [mul_sum]
    refine sum_congr rfl fun q h => ?_
    rw [toll w s q h,prod_mul_distrib]
  rw [←evaluated W unit,normalized W unit sym]
  have bound := (tail (ordinary W s) r z small).trans (mul_le_mul_of_nonneg_left rich (by positivity))
  refine (mul_le_mul_of_nonneg_left bound (Poly.worth hw _).le).trans_eq ?_
  rw [mul_left_comm, factor]

end YM.Integration.WilsonFiniteOrdinaryTail
