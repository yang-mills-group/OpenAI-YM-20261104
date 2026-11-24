import YM.Integration.WilsonFiniteSignedResetProbes

/-! A single finite salary for all interpolation modes of the measured reset, on a true angular field. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramResetProbeWallet
open Finset Comparison.RG02.Adjacent WilsonFiniteSignedResetProbes
open scoped BigOperators Classical

def fee (K:UnitCost)(order d t:ℕ):ℝ :=
  ∑j∈range (order+1),∑b:Fin (d+1),∑l:Fin (d+1),‖weight K 0 d t j b l‖

def total (K:UnitCost)(order d:ℕ):ℝ:=∑t∈range (order+1),fee K order d t

theorem nonneg (K:UnitCost)(order d:ℕ):0≤ total K order d := by unfold total fee; positivity

theorem node_unit (d:ℕ)(l:Fin (d+1)): |node d l| ≤ 1 := by
  rw [node, abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast Nat.le_of_lt l.isLt

variable {E B:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]

theorem purchase (K:UnitCost)(order d t:ℕ)(ht:t≤order)(A:E→L[ℝ]B)(ε γ:ℝ)(hε:0≤ε)
    (h:ℕ)(bill:B→ℝ)(paid:∀x,γ*bill x≤ε*(2+‖x‖)^h)(u:E):
    γ*(∑j∈range (order+1),∑b:Fin (d+1),∑l:Fin (d+1),‖weight K 0 d t j b l‖*bill (node d l • A u)) ≤
      (ε*total K order d*(2+‖A‖)^h)*(1+‖u‖)^h := by
  have angle (l:Fin (d+1)):2+‖node d l • A u‖ ≤ (2+‖A‖)*(1+‖u‖) := by
    rw [norm_smul,Real.norm_eq_abs]
    have hu:=mul_le_mul_of_nonneg_right (node_unit d l) (norm_nonneg (A u))
    nlinarith only [hu,A.le_opNorm u,norm_nonneg u,norm_nonneg A]
  have each (j:ℕ)(b l:Fin (d+1)):
      γ*(‖weight K 0 d t j b l‖*bill (node d l • A u)) ≤
        ‖weight K 0 d t j b l‖*(ε*((2+‖A‖)^h*(1+‖u‖)^h)) := by
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (paid _).trans
    rw [←mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (angle l) _) hε
  calc
    _ ≤ fee K order d t*(ε*((2+‖A‖)^h*(1+‖u‖)^h)) := by
      unfold fee
      simp only [mul_sum,sum_mul]
      exact sum_le_sum fun j _=>sum_le_sum fun b _=>sum_le_sum fun l _=>each j b l
    _ ≤ _ := by
      have bound:fee K order d t≤total K order d :=
        single_le_sum (f:=fee K order d) (fun e _=>by unfold fee;positivity) (mem_range_succ_iff.mpr ht)
      apply (mul_le_mul_of_nonneg_right bound (by positivity)).trans_eq
      ring

end YM.Integration.WilsonPositionProgramResetProbeWallet
end
