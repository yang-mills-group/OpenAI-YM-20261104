import YM.Integration.WilsonReceivedOrdinaryPanel

/-! The independent ordinary coefficient sums the disjoint occupied partitions, retaining
the total coupling degree. The same operation on the finite Wick logarithm recovers its actual ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoveredOrdinaryPolynomial
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {J : Census V}

def row (r : ℕ) (f : ℕ → ℂ) : Polynomial ℂ :=
  ∑ i∈range (r+1), Polynomial.monomial i (f i)

theorem coefficient (r : ℕ) (f : ℕ → ℂ) (i : ℕ) :
    (row r f).coeff i = if i ≤ r then f i else 0 := by
  simp [row, Polynomial.coeff_monomial]

theorem distance (r : ℕ) (f h : ℕ → ℂ) :
    mass (row r f - row r h) ≤ ∑ i∈range (r+1), ‖f i-h i‖ := by
  have eqn : row r f-row r h = row r (fun i=>f i-h i) := by
    simp only [row,map_sub,sum_sub_distrib]
  rw [eqn]
  exact (IterationFour.Series.mass_sum ..).trans_eq
    (sum_congr rfl fun i _ => IterationFour.Series.prices_monomial (f i-h i) i)

def ordinary (r : ℕ) (K : ℕ → Poly J) (s : J.Mode) : Polynomial ℂ :=
  ∑ h∈shards J s, ∏ t∈h.val, row r (fun i=>(K i).part t.val)

def evaluated (r : ℕ) (K : ℕ → Poly J) (z : ℂ) (s : J.Mode) : ℂ :=
  partialValue r z (ordinary r K s)

theorem finite_row {r : ℕ} (P : Grade J r) (s : J.Mode) :
    row r (fun i=>(observe J r P i).part s) = slot s (render P) := by
  ext i
  rw [coefficient,coeff_slot,render_coeff]
  split
  · rfl
  · rename_i hi
    simp [observe,hi]

theorem finite {r : ℕ} (W : Grade J r) (unit : UnitLeading W) (sym : Symmetric W) (z : ℂ) (s : J.Mode) :
    evaluated r (observe J r (logMarked W)) z s = (value z (ratio W)).part s := by
  rw [WilsonFiniteOrdinaryPartitions.normalized W unit sym]
  simp only [evaluated,ordinary,WilsonFiniteOrdinaryPartitions.ordinary,finite_row]

theorem truncates (r : ℕ) (z : ℂ) (hz : ‖z‖≤1) (p : Polynomial ℂ) :
    ‖partialValue r z p‖ ≤ IterationFour.Series.mass p := by
  unfold partialValue
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ i∈range (r+1), ‖p.coeff i‖ := sum_le_sum fun i _ => by
      rw [norm_mul,norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
    _ = ∑ i∈p.support.filter (·≤r), ‖p.coeff i‖ := by
      symm
      apply sum_subset (fun i hi=>mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hi).2))
      intro i hi miss
      have outside : i∉p.support := fun hit=>miss (mem_filter.mpr ⟨hit,Nat.le_of_lt_succ (mem_range.mp hi)⟩)
      simp [Polynomial.notMem_support_iff.mp outside]
    _ ≤ IterationFour.Series.mass p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _=>norm_nonneg _)

end YM.Integration.WilsonCoveredOrdinaryPolynomial
