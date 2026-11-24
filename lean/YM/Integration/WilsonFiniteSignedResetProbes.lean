import YM.Integration.FVA1Physical.Wilson.FiniteMarkDegrees
import YM.Comparison.RG02.Adjacent.Rank
import Mathlib.LinearAlgebra.Vandermonde

/-! The signed error of the finite Wilson marked row at the actual measured
reversion is a finite signed sum of errors on the original real field rays.
This retains the field-dependent dated invoice at every sampled node. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFiniteSignedResetProbes
open Finset Analysis Comparison.RG02 Comparison.RG02.Valence Comparison.RG02.Adjacent
open PertExtension.Series Comparison.RG02.Moving.Path
open scoped Classical BigOperators ContDiff
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def node (n:ℕ) (j:Fin (n+1)) : ℝ := (j.val:ℝ)/((n:ℝ)+1)
def nodeCoeff (n:ℕ) (i j:Fin (n+1)) : ℝ := (Matrix.vandermonde (node n))⁻¹ i j

-- The native finite Vandermonde calculation from FVA1Physical/Wilson/ResetGrid.
private theorem probe_jet {f:X→ℂ} {n:ℕ} (hf:Level (n:ℤ) f) (x:X) (i:Fin (n+1)) :
    Assembly.jet f i.val x = ∑ j, (nodeCoeff n i j:ℂ)*f (node n j • x) := by
  let M := Matrix.vandermonde (node n)
  have invert : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,Matrix.det_vandermonde_ne_zero_iff]
    intro j k e
    have eq : (j.val:ℝ)/((n:ℝ)+1) = (k.val:ℝ)/((n:ℝ)+1) := e
    apply Fin.ext
    exact_mod_cast (div_left_inj' (show (n:ℝ)+1≠0 by positivity)).mp eq
  let v (k:Fin (n+1)) := Assembly.jet f k.val x
  have nodes (j:Fin (n+1)) : f (node n j • x) = ∑ k, ((M j k:ℝ):ℂ)*v k := by
    rw [hf.posted]
    change _ = ∑ k:Fin (n+1), ((node n j ^ k.val:ℝ):ℂ)*Assembly.jet f k.val x
    rw [Fin.sum_univ_eq_sum_range (fun k:ℕ=> ((node n j ^ k:ℝ):ℂ)*Assembly.jet f k x) (n+1)]
    apply sum_congr rfl
    intro k _
    rw [Assembly.Clipper.weight,Complex.real_smul]
  simp_rw [nodes]
  change v i = ∑ j, ((M⁻¹ i j:ℝ):ℂ) * ∑ k, ((M j k:ℝ):ℂ)*v k
  simp only [mul_sum,←mul_assoc,←Complex.ofReal_mul]
  rw [sum_comm]
  simp only [←sum_mul,←Complex.ofReal_sum,←Matrix.mul_apply,Matrix.nonsing_inv_mul M invert]
  simp only [Matrix.one_apply]
  rw [sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp


def weight (κ:UnitCost) (d:ℤ) (n p j:ℕ) (k l:Fin (n+1)) : ℂ :=
  motion (money κ d j k.val) p * (nodeCoeff n k l:ℂ)

theorem signed {r n:ℕ} (U H:Display X) (κ:UnitCost) (d:ℤ)
    (hU:Charge r (fun _=>(n:ℤ)) U) (hH:Charge r (fun _=>(n:ℤ)) H)
    (p:ℕ) (x:X) :
    born U κ d r p x - born H κ d r p x =
      ∑ j∈range (r+1), ∑ k:Fin (n+1), ∑ l:Fin (n+1),
        weight κ d n p j k l * (U j (node n l • x)-H j (node n l • x)) := by
  have repr (A:Display X) (hA:Charge r (fun _=>(n:ℤ)) A) :
      born A κ d r p x = ∑ j∈range (r+1), ∑ k:Fin (n+1), ∑ l:Fin (n+1),
        weight κ d n p j k l * A j (node n l • x) := by
    rw [message κ d r hA]; simp only [Int.toNat_natCast]
    refine sum_congr rfl fun j hj=>?_
    rw [← Fin.sum_univ_eq_sum_range (fun k:ℕ=>motion (money κ d j k) p*Assembly.jet (A j) k x) (n+1)]
    refine sum_congr rfl fun k _=>?_
    rw [probe_jet (hA j (mem_range_succ_iff.mp hj)) x k, mul_sum]
    exact sum_congr rfl fun l _=>(mul_assoc _ _ _).symm
  rw [repr U hU,repr H hH,←sum_sub_distrib]
  simp_rw [←sum_sub_distrib,←mul_sub]

theorem measured {r n:ℕ} (U H:Display X) (κ:UnitCost) (d:ℤ)
    (hU:Charge r (fun _=>(n:ℤ)) U) (hH:Charge r (fun _=>(n:ℤ)) H)
    (p:ℕ) (x:X) (fee:ℝ) (hfee:0≤fee) (invoice:X→ℝ)
    (cap:∀ j≤r,∀ z,fee*‖U j z-H j z‖ ≤ invoice z) :
    fee*‖born U κ d r p x-born H κ d r p x‖ ≤
      ∑ j∈range (r+1), ∑ k:Fin (n+1), ∑ l:Fin (n+1),
        ‖weight κ d n p j k l‖*invoice (node n l • x) := by
  rw [signed U H κ d hU hH p x]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) hfee).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun j hj=>?_
  refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) hfee).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun k _=>?_
  refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) hfee).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun l _=>?_
  rw [norm_mul,mul_left_comm]
  exact mul_le_mul_of_nonneg_left (cap j (mem_range_succ_iff.mp hj) _) (norm_nonneg _)

end YM.Integration.WilsonFiniteSignedResetProbes
