import YM.Integration.WilsonOriginalLowFourierJets
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! An absolute summation bill on the actual signed integer-mode bank in
a separated coordinate box, in any finite dimension. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFourierLattice
open Filter Finset
open scoped BigOperators

def height {d : ℕ} (v : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (v i).natAbs

private def line (z : ℤ) : ℝ := (1+(z.natAbs:ℝ))⁻¹ ^ 2

def weight {d : ℕ} (v : Fin d → ℤ) : ℝ := ∏ i, line (v i)

theorem nonnegative {d : ℕ} (v : Fin d → ℤ) : 0 ≤ weight v :=
  prod_nonneg fun _ _ => sq_nonneg _

private lemma oneDim : Summable line := by
  have pos := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
  have simple : Summable (fun n : ℕ => (1+(n:ℝ))⁻¹^2) := by
    apply pos.congr
    intro n
    rw [abs_of_nonneg (by positivity),Real.rpow_two,one_div,inv_pow,add_comm]
  rw [summable_int_iff_summable_nat_and_neg]
  constructor <;> simpa [line] using simple

theorem summable (d : ℕ) : Summable (@weight d) := by
  induction d with
  | zero =>
    letI : Fintype (Fin 0 → ℤ) :=
      ⟨{fun _ => 0},fun v => by simp only [mem_singleton];funext i;exact Fin.elim0 i⟩
    exact (hasSum_fintype _).summable
  | succ d ih =>
    let take : (Fin (d+1) → ℤ) → ℤ × (Fin d → ℤ) := fun v => (v 0, Fin.tail v)
    have inj : Function.Injective take := by
      intro v w eqv;funext i
      refine Fin.cases (congrArg Prod.fst eqv) (fun z => ?_) i
      exact congrFun (congrArg Prod.snd eqv) z
    have product := oneDim.mul_of_nonneg ih (fun z => sq_nonneg _) nonnegative
    apply (product.comp_injective inj).congr
    intro v
    exact (Fin.prod_univ_succ fun i => line (v i)).symm

theorem pays {d : ℕ} (v : Fin d → ℤ) :
    (1+(height v:ℝ))⁻¹ ^ (2*d) ≤ weight v := by
  let R : ℝ := 1+(height v:ℝ)
  have hr : 0 < R := by dsimp [R]; positivity
  have each (i : Fin d) : R⁻¹^2 ≤ line (v i) := by
    have h : (v i).natAbs ≤ height v := Finset.le_sup (f := fun i => (v i).natAbs) (mem_univ i)
    have h' : 1+((v i).natAbs:ℝ) ≤ R := by dsimp [R];exact_mod_cast Nat.add_le_add_left h 1
    apply pow_le_pow_left₀ (inv_nonneg.mpr hr.le)
    exact inv_le_inv₀ hr (by positivity : 0 < 1+((v i).natAbs:ℝ)) |>.mpr h'
  change R⁻¹^(2*d) ≤ ∏ i, line (v i)
  calc
    _ = ∏ _ : Fin d, R⁻¹^2 := by rw [pow_mul];simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun i _ => each i)

/-- The actual sum of absolute Fourier remainders costs one finite constant
depending only on the box dimension, uniformly over the physical read. -/
theorem original (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (_ : 0 ≤ A)
    (v : (Fin d → ℤ) → ℂ),
    (∀ p, ‖v p‖ ≤ A * (1+(height p:ℝ))⁻¹^(2*d)) →
    Summable (fun p => ‖v p‖) ∧ ∑' p, ‖v p‖ ≤ C*A := by
  refine ⟨∑' p : Fin d → ℤ, weight p, tsum_nonneg nonnegative,?_⟩
  intro A hA v income
  have each (p) : ‖v p‖ ≤ A*weight p :=
    (income p).trans (mul_le_mul_of_nonneg_left (pays p) hA)
  have hs := (summable d).mul_left A
  have available := Summable.of_nonneg_of_le (fun p => norm_nonneg _) each hs
  refine ⟨available,?_⟩
  calc
    _ ≤ ∑' p, A*weight p := available.tsum_le_tsum each hs
    _ = _ := by rw [tsum_mul_left,mul_comm]

end YM.Integration.WilsonOriginalFourierLattice

