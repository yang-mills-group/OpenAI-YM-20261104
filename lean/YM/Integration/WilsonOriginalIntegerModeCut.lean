import YM.Integration.WilsonOriginalFourierLattice
import YM.Integration.WilsonOriginalHighModeExpense

/-! The frequency in the analytic tube and in the tested Fourier
coefficient is the same integer tuple, with the cutoff from the actual heater. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalIntegerModeCut
open Filter Finset
open scoped Topology BigOperators
open WilsonOriginalLowFourierJets (cube jet)
open WilsonOriginalFourierLattice (height)
variable {d j : ℕ}

def size (v : Fin d → ℤ) : ℝ := (height v : ℝ)^((12:ℝ)⁻¹)

lemma size_pow (v : Fin d → ℤ) : size v ^ 12 = (height v:ℝ) := by
  exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by decide : (12:ℕ) ≠ 0)

lemma nonnegative (v : Fin d → ℤ) : 0 ≤ size v :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma member (v : Fin d → ℤ) (N : ℕ) : v ∈ cube d N ↔ height v ≤ N := by
  change (_ ∈ Fintype.piFinset _) ↔ Finset.univ.sup _ ≤ N
  rw [Fintype.mem_piFinset]
  constructor
  · intro h
    apply Finset.sup_le
    intro i _
    rw [← Nat.cast_le (α:=ℤ),Int.natCast_natAbs]
    exact abs_le.mpr (mem_Icc.mp (h i))
  · intro h i
    apply mem_Icc.mpr
    apply abs_le.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast ((Finset.le_sup (f:=fun i => (v i).natAbs) (mem_univ i)).trans h)

theorem outside {u : ℝ} (hu : 0 < u) {v : Fin d → ℤ}
    (hv : v ∉ cube d ⌊(u⁻¹)^12⌋₊) : u⁻¹ < size v ∧ 1 ≤ size v*u := by
  have n : ⌊(u⁻¹)^12⌋₊ < height v := lt_of_not_ge fun nh => hv ((member _ _).2 nh)
  have hn : (u⁻¹)^12 < (height v:ℝ) := Nat.lt_of_floor_lt n
  have hs : u⁻¹ < size v := by
    by_contra! h
    have power := pow_le_pow_left₀ (nonnegative v) h 12
    rw [size_pow] at power;linarith
  exact ⟨hs, by simpa [hu.ne'] using mul_le_mul_of_nonneg_right hs.le hu.le⟩

/-- Every actual ordered derivative has its intrinsic salary on this very
frequency, including the zero-dimensional box and empty derivative. -/
theorem original (axis : Fin j → Fin d) (unit : Fin j → ℂ) (v : Fin d → ℤ) :
    ‖jet axis unit v‖ ≤ (∏ i, ‖unit i‖)*(size v^12)^j := by
  rw [size_pow,WilsonOriginalLowFourierJets.jet,norm_prod]
  calc
    _ ≤ ∏ i, (‖unit i‖*(height v:ℝ)) := prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => by
      have hi : (v (axis i)).natAbs ≤ height v :=
        Finset.le_sup (f:=fun i => (v i).natAbs) (mem_univ _)
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
      exact_mod_cast (show |v (axis i)| ≤ (height v:ℤ) by rw [← Int.natCast_natAbs];exact_mod_cast hi))
    _ = _ := by rw [prod_mul_distrib];simp

end YM.Integration.WilsonOriginalIntegerModeCut

