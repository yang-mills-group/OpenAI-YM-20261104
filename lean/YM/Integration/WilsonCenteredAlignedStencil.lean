import YM.OPE.Stencils
import Mathlib.Analysis.Calculus.Taylor

/-! A real Taylor estimate on the actual one-sided normalised position stencil.
The same bounded weights will be used on the physical and independent fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredAlignedStencil
open Function Filter Set OPE OPE.PolyDisk OPE.Stencils Finset
open scoped Classical BigOperators

private theorem leaves (n:ℕ) (a p:ℝ) (I:Set ℝ) (f:ℝ→ℂ) :
    (∑ j:Fin (n+1),lagWeight (angle a p) j*
        taylorWithinEval f n I 0 (displacement a (angle a p) j))=f 0 := by
  let u:=angle a p
  let D (k:ℕ):ℂ:=(k.factorial:ℂ)⁻¹*iteratedDerivWithin k f I 0
  have expand (y:ℝ):taylorWithinEval f n I 0 y=∑ k∈range (n+1),(y:ℂ)^k*D k:=by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro k _
    simp only [D,sub_zero,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,
      Complex.ofReal_natCast,Complex.ofReal_pow]
    ring
  rw [← taylorWithinEval_self f n I 0]
  simp_rw [expand,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  simp_rw [←mul_assoc]
  rw [←sum_mul,power_exact a u k (mem_range.mp hk)]
  rfl

theorem original (n:ℕ) : ∃ C:ℝ,1≤C ∧ ∀ (a p B:ℝ),0<a → 0≤B →
    let h:=a*((n+1:ℕ)+3)
    let I:=Icc (0:ℝ) h
    ∀ f:ℝ→ℂ,ContDiffOn ℝ (n+1) f I →
    (∀ y∈I,‖iteratedDerivWithin (n+1) f I y‖≤B) →
    ‖f 0-∑ j:Fin (n+1),lagWeight (angle a p) j*f (displacement a (angle a p) j)‖≤C*B*a^(n+1) := by
  obtain ⟨K,k1,wallet⟩:=lag_budget (n+1)
  let R:ℝ:=(n+1:ℕ)+3
  have room:1≤R:=by dsimp [R];exact_mod_cast (show 1≤n+1+3 by omega)
  refine ⟨K*R^(n+1),one_le_mul_of_one_le_of_one_le k1 (one_le_pow₀ room),?_⟩
  intro a p B ap bp h I f smooth cap
  let u:=angle a p
  have wall:0≤h:=mul_nonneg ap.le (zero_le_one.trans room)
  have nodes (j:Fin (n+1)):displacement a u j ∈ I:=by
    have near:=step_near (n+1) a ap (p:=p) j
    rw [step_affine (n+1) a ap j,add_comm p,add_sub_cancel_right] at near
    exact ⟨near.1.le,near.2⟩
  have tail (j:Fin (n+1)):
      ‖taylorWithinEval f n I 0 (displacement a u j)-f (displacement a u j)‖≤ B*h^(n+1):=by
    rw [norm_sub_rev]
    have paid:=taylor_mean_remainder_bound (n:=n) wall smooth (nodes j) cap
    rw [sub_zero] at paid
    refine paid.trans ((div_le_self (mul_nonneg bp (pow_nonneg (nodes j).1 _)) ?_).trans ?_)
    · exact_mod_cast Nat.factorial_pos n
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (nodes j).1 (nodes j).2 _) bp
  rw [←leaves n a p I f,←sum_sub_distrib]
  simp_rw [←mul_sub]
  calc
    _ ≤ _:=norm_sum_le _ _
    _ ≤ ∑ j:Fin (n+1),‖lagWeight u j‖*(B*h^(n+1)):=sum_le_sum (fun j _=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (tail j) (norm_nonneg _))
    _ ≤ K*(B*h^(n+1)):=by rw [←sum_mul];gcongr;exact wallet u (angle_law a)
    _ = _:=by dsimp only [h];rw [mul_pow];ring

end YM.Integration.WilsonCenteredAlignedStencil
