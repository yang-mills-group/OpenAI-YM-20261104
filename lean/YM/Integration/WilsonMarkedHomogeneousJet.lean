import YM.Integration.WilsonMarkedCoupledAction

/-! The differential of a true homogeneous angular tensor at flat field,
with all factorials and a spatially uniform mixed-direction price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedHomogeneousJet
open Tensor Finset PertExtension.Series Planned.AtomRegular
open scoped Classical ContDiff
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {d:ℕ}

theorem ray (A:T E ℝ d)(x:E)(s:ℕ):
    iteratedFDeriv ℝ s (diagonal A) 0 (fun _=>x)=
      (if s=d then (d.factorial:ℝ) else 0)*diagonal A x:=by
  have curve:=Radial.radial_iteratedDeriv (f:=diagonal A) x (0:ℝ) s isOpen_univ (Set.mem_univ _)
    (diag_smooth A (s:WithTop ℕ∞)).contDiffOn
  have straight:(fun t:ℝ=>diagonal A (t • x))=fun t:ℝ=>t^d*diagonal A x:=
    funext fun t=>homogeneous A x t
  simp only [zero_smul] at curve
  rw [←curve,straight,iteratedDeriv_mul_const_field,iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp

theorem operator (A:T E ℝ d)(s:ℕ):
    ‖iteratedFDeriv ℝ s (diagonal A) 0‖ ≤ polarCost s*((s.factorial:ℝ)*‖A‖):=by
  apply op_polar (Analysis.sym_Jet (diag_smooth A (s:WithTop ℕ∞)).contDiffAt) (mul_nonneg (by positivity) (norm_nonneg _))
  intro x hx
  change ‖iteratedFDeriv ℝ s (diagonal A) 0 (fun _=>x)‖≤_
  rw [ray];split_ifs with eq
  · subst s
    rw [norm_mul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have diag:‖diagonal A x‖≤‖A‖:=by
      refine (A.le_opNorm (fun _=>x)).trans ?_
      simpa only [prod_const,card_univ,Fintype.card_fin,mul_one] using
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg x) hx (n:=d)) (norm_nonneg A)
    exact mul_le_mul_of_nonneg_left diag (Nat.cast_nonneg _)
  · rw [zero_mul,norm_zero];positivity

def allowance (p:ℕ):ℝ:=∑s∈range (p+1),polarCost s*(s.factorial:ℝ)

theorem nonnegative (p:ℕ):0≤allowance p:=sum_nonneg fun i _=>mul_nonneg
    (zero_le_one.trans (polar_one i)) (Nat.cast_nonneg _)

theorem paid (A:T E ℝ d){s p:ℕ}(h:s≤p):
    ‖iteratedFDeriv ℝ s (diagonal A) 0‖≤allowance p*‖A‖:=by
  have step:polarCost s*(s.factorial:ℝ)≤allowance p:=single_le_sum
    (f:=fun i=>polarCost i*(i.factorial:ℝ))
    (fun i _=>mul_nonneg (zero_le_one.trans (polar_one i)) (Nat.cast_nonneg _)) (by simpa using h)
  exact (operator A s).trans ((mul_assoc ..).symm.le.trans (mul_le_mul_of_nonneg_right step (norm_nonneg A)))

end YM.Integration.WilsonMarkedHomogeneousJet
end
