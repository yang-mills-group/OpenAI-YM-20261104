import YM.Integration.WilsonFirstReceivedRadialStencil
import Mathlib.Analysis.Calculus.Taylor

/-! Recovery on the original real radial sampling stencil. The derivative
order is fixed before the requested accuracy of the measurements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySamples
open Finset Polynomial Set WilsonFirstReceivedRadialStencil
open scoped Classical ContDiff

def weight (k : ℕ) : ℝ := ∑ j∈range (k+1),
  ‖(Lagrange.basis (range (k+1)) (fun i : ℕ => (node k i : ℂ)) j).coeff k‖

def price (k : ℕ) : ℝ := k.factorial * weight k

theorem price_nonneg (k : ℕ) : 0 ≤ price k := by
  unfold price weight
  positivity

/-- The one-order increase in the rough derivative pays the error as the
distance between measurements shrinks. All measured arguments are real. -/
theorem sampled (f : ℝ → ℂ) (k : ℕ) {t E M : ℝ} (ht : 0 < t) (hm : 0 ≤ M)
    (smooth : ∀ u ∈ Icc 0 t, ContDiffAt ℝ (k+1) f u)
    (rough : ∀ u ∈ Icc 0 t, ‖iteratedDeriv (k+1) f u‖ ≤ M)
    (values : ∀ j ≤ k, ‖f (t * node k j)‖ ≤ E) :
    ‖iteratedDeriv k f 0‖ ≤ price k * (E / t^k + M*t) := by
  let S := range (k+1)
  let v (i : ℕ) : ℂ := node k i
  let a (i : ℕ) : ℂ := (i.factorial : ℂ)⁻¹ * (t:ℂ)^i * iteratedDeriv i f 0
  let P : Polynomial ℂ := ∑ i∈S, monomial i (a i)
  have degree : P.natDegree ≤ k :=
    natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (natDegree_monomial_le ..).trans (Nat.le_of_lt_succ (mem_range.mp hi))
  have fine j (hj : j ≤ k) : ‖P.eval (v j)‖ ≤ E + M*t^(k+1) := by
    let x := t * node k j
    obtain ⟨hj₀,hj₁⟩ := node_mem hj
    have hx : x ∈ Icc 0 t := ⟨mul_nonneg ht.le hj₀,
      (mul_le_mul_of_nonneg_left hj₁ ht.le).trans_eq (mul_one _)⟩
    have hw i (hi : i ≤ k+1) u (hu : u∈Icc 0 t) :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
        ((smooth u hu).of_le (Nat.cast_le.mpr hi)) hu
    have tay := taylor_mean_remainder_bound (n:=k) (x:=x) ht.le
      (fun u hu => (smooth u hu).contDiffWithinAt) hx
      (fun u hu => by rw [hw (k+1) le_rfl u hu]; exact rough u hu)
    have eqn : taylorWithinEval f k (Icc 0 t) 0 x = P.eval (v j) := by
      rw [taylor_within_apply]
      unfold P
      simp only [eval_finsetSum,eval_monomial]
      apply sum_congr rfl
      intro i hi
      rw [hw i (le_of_lt (mem_range.mp hi)) 0 (left_mem_Icc.mpr ht.le)]
      simp [a,v,x,Complex.real_smul,mul_pow]
      ring
    rw [eqn,sub_zero] at tay
    have fac : (1:ℝ) ≤ k.factorial := by exact_mod_cast k.factorial_pos
    exact (norm_le_norm_add_norm_sub (f x) (P.eval (v j))).trans
      (add_le_add (values j hj) (tay.trans ((div_le_self
        (mul_nonneg hm (pow_nonneg hx.1 _)) fac).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 _) hm))))
  have inj : InjOn v S := by
    intro i _ j _ h
    have hij : node k i = node k j := Complex.ofReal_injective h
    exact_mod_cast (div_left_inj' (by positivity : (k+1:ℕ)≠(0:ℝ))).mp hij
  have deg : P.degree < (S.card : WithBot ℕ) := P.degree_le_natDegree.trans_lt (by
    simp only [S,card_range]; exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le degree))
  have top : ‖P.coeff k‖ ≤ (E + M*t^(k+1)) * weight k := by
    conv_lhs => rw [Lagrange.eq_interpolate (s:=S) (v:=v) (f:=P) inj deg,
      Lagrange.interpolate_apply,finsetSum_coeff]
    refine (norm_sum_le _ _).trans ?_
    rw [weight,Finset.mul_sum]
    apply sum_le_sum
    intro j hj
    rw [coeff_C_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right (fine j (Nat.le_of_lt_succ (mem_range.mp hj))) (norm_nonneg _)
  have hc : P.coeff k = a k := by simp [P,S,finsetSum_coeff,coeff_monomial]
  rw [hc] at top
  change ‖(k.factorial : ℂ)⁻¹ * (t:ℂ)^k * iteratedDeriv k f 0‖ ≤ _ at top
  simp only [norm_mul,norm_inv,norm_pow,Complex.norm_natCast,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos ht] at top
  have hf : (0:ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hh : ‖iteratedDeriv k f 0‖ * t^k ≤ k.factorial*((E + M*t^(k+1)) * weight k) := by
    calc
      _ = (k.factorial:ℝ) * ((k.factorial:ℝ)⁻¹ * t^k * ‖iteratedDeriv k f 0‖) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left top hf.le
  apply (le_div_iff₀ (pow_pos ht k)).2 at hh
  calc
    _ ≤ _ := hh
    _ = _ := by unfold price; rw [pow_succ]; field_simp

end YM.Integration.WilsonCapturedPrimarySamples
